// ==UserScript==
// @name         Torn Purchase Ledger
// @namespace    torn-purchase-ledger
// @version      8.6.7
// @description  Torn purchase, selling, trades, gifts and travel buys, FIFO P&L ledger and throttled Sync All
// @match        https://www.torn.com/*
// @grant        none
// ==/UserScript==

(function () {
    'use strict';

    const API_KEY = '###PDA-APIKEY###';
    const API = 'https://api.torn.com/v2';

    const STATE_KEY = 'TPL8_STATE';
    const CATALOG_KEY = 'TPL8_CATALOG_V2';
    const LAST_TMV_KEY = 'TPL8_LAST_TMV';
    const WIDTH_KEY = 'TPL8_WIDTH';

    const TIMEOUT = 10000;
    const PRICE_INTERVAL = 4 * 60 * 1000;
    const HISTORY_PAGE_DELAY = 800;
    const API_MIN_INTERVAL = 1200;
    const SYNC_ALL_COOLDOWN = 60 * 1000;
    const SYNC_ALL_LAST_KEY = 'TPL8_SYNC_ALL_LAST';

    const TRADE_PARSER_VERSION = 2;
    const TRADE_DETAIL_DELAY = 800;

    let state = {
        tracked: [],
        purchases: [],
        sells: [],
        trades: [],
        itemReceives: [],
        travelPurchases: [],
        parcelOpens: [],
        itemUses: [],
        itemSends: []
    };

    let catalog = [];
    let catalogMap = new Map();
    let prices = {};

    let drawer = null;
    let tab = null;

    let syncing = false;
    let pricing = false;
    let historySyncing = false;
    let sellingSyncing = false;
    let sellingHistorySyncing = false;
    let tradeSyncing = false;
    let tradeHistorySyncing = false;
    let tradeDetailAutoLoading = false;
    let receivingSyncing = false;
    let receivingHistorySyncing = false;
    let travelSyncing = false;
    let travelHistorySyncing = false;
    let parcelSyncing = false;
    let useSyncing = false;
    let syncAllRunning = false;
    let syncAllCooldownTimer = null;
    let apiQueue = Promise.resolve();
    let lastApiRequestAt = 0;

    let activePage = 'buying';
    let statusTimer = null;
    let uiObserver = null;
    let uiCheckTimer = null;

    const expandedItems = new Set();
    const expandedTrades = new Set();

    /* =====================================================
       BASIC HELPERS
    ===================================================== */

    function esc(v) {
        return String(v ?? '')
            .replace(/&/g, '&amp;')
            .replace(/</g, '&lt;')
            .replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;')
            .replace(/'/g, '&#039;');
    }

    function norm(v) {
        return String(v || '').trim().toLowerCase();
    }

    function money(v) {
        return Number.isFinite(Number(v))
            ? '$' + Math.round(Number(v)).toLocaleString('en-US')
            : 'Unavailable';
    }

    const GIFT_BASIS_KEY = 'TPL8_GIFT_BASIS'; // 'zero' (default) or 'tmv'
    const TRAVEL_DIAG_KEY = 'TPL8_TRAVEL_DIAG';
    const USE_MODE_KEY = 'TPL8_USE_MODE'; // 'separate' (default) or 'cost'
    const USE_DIAG_KEY = 'TPL8_USE_DIAG';
    const OD_DIAG_KEY = 'TPL8_OD_DIAG';
    const SEND_DIAG_KEY = 'TPL8_SEND_DIAG';
    const AUDIT_KEY = 'TPL8_AUDIT';
    let auditRunning = false;
    const OVERDOSE_LOG_DEFAULT = '2291';
    const OVERDOSE_LOG_KEY = 'TPL8_OVERDOSE_LOG'; // optional manual override

    function overdoseLogId() {
        try {
            const v = String(localStorage.getItem(OVERDOSE_LOG_KEY) || '').trim();
            return v || OVERDOSE_LOG_DEFAULT;
        } catch (_) {
            return OVERDOSE_LOG_DEFAULT;
        }
    }

    function useMode() {
        try {
            return localStorage.getItem(USE_MODE_KEY) === 'cost'
                ? 'cost'
                : 'separate';
        } catch (_) {
            return 'separate';
        }
    }

    function giftBasisMode() {
        try {
            return localStorage.getItem(GIFT_BASIS_KEY) === 'tmv'
                ? 'tmv'
                : 'zero';
        } catch (_) {
            return 'zero';
        }
    }

    function lastKnownTmv(itemId) {
        try {
            const map = JSON.parse(localStorage.getItem(LAST_TMV_KEY) || '{}') || {};
            return Number(map[Number(itemId)]) || 0;
        } catch (_) {
            return 0;
        }
    }

    function rememberTmv(itemId, tmv) {
        tmv = Number(tmv);
        if (!(tmv > 0)) return;
        try {
            const map = JSON.parse(localStorage.getItem(LAST_TMV_KEY) || '{}') || {};
            map[Number(itemId)] = tmv;
            localStorage.setItem(LAST_TMV_KEY, JSON.stringify(map));
        } catch (_) {}
    }

    function currentTmvFor(itemId) {
        const live = prices[Number(itemId)];
        const tmv = Number(live?.tmv);
        if (Number.isFinite(tmv) && tmv > 0) return tmv;
        return (
            Number(catalogMap.get(Number(itemId))?.market_value) ||
            lastKnownTmv(itemId) ||
            0
        );
    }

    function sleep(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }

    function formatDate(ts) {
        if (!ts) return '';

        const d = new Date(Number(ts) * 1000);
        const p = n => String(n).padStart(2, '0');

        return `${p(d.getHours())}:${p(d.getMinutes())}:${p(d.getSeconds())} - ${p(d.getDate())}/${p(d.getMonth() + 1)}/${String(d.getFullYear()).slice(-2)}`;
    }

    function timestampOf(v) {
        if (!v) return 0;
        if (typeof v === 'number') return Number(v) || 0;

        return Number(
            v.completed_at ??
            v.timestamp ??
            v.time ??
            v.created_at ??
            v.created ??
            v.date ??
            0
        ) || 0;
    }

    function getLogTimestamp(log) {
        const d = log?.data && typeof log.data === 'object'
            ? log.data
            : log;

        return Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );
    }

    function firstString(o, keys) {
        if (!o || typeof o !== 'object') return '';

        for (const k of keys) {
            if (o[k] != null && String(o[k]).trim()) {
                return String(o[k]);
            }
        }

        return '';
    }

    function setStatus(message) {
        if (!drawer) return;

        const el = drawer.querySelector('#tpl8-status');
        if (!el) return;

        el.textContent = message;

        clearTimeout(statusTimer);

        statusTimer = setTimeout(() => {
            if (el) {
                el.textContent =
                    `${state.tracked.length} tracked · ${state.trades.length} trades`;
            }
        }, 7000);
    }

    /* =====================================================
       STATE
    ===================================================== */

    function loadState() {
        try {
            const saved = JSON.parse(
                localStorage.getItem(STATE_KEY) || 'null'
            );

            if (!saved) return;

            state.tracked = Array.isArray(saved.tracked)
                ? saved.tracked
                : [];

            state.purchases = Array.isArray(saved.purchases)
                ? saved.purchases
                : [];

            state.sells = Array.isArray(saved.sells)
                ? saved.sells
                : [];

            state.trades = Array.isArray(saved.trades)
                ? saved.trades
                : [];

            state.itemReceives =
                Array.isArray(saved.itemReceives)
                    ? saved.itemReceives
                    : [];

            state.travelPurchases =
                Array.isArray(saved.travelPurchases)
                    ? saved.travelPurchases
                    : [];

            state.parcelOpens =
                Array.isArray(saved.parcelOpens)
                    ? saved.parcelOpens
                    : [];

            state.itemUses =
                Array.isArray(saved.itemUses)
                    ? saved.itemUses
                    : [];

            state.itemSends =
                Array.isArray(saved.itemSends)
                    ? saved.itemSends
                    : [];
        } catch (e) {
            console.error('[TPL8] State load error', e);
        }
    }

    function saveState() {
        try {
            localStorage.setItem(
                STATE_KEY,
                JSON.stringify(state)
            );
        } catch (e) {
            console.error('[TPL8] State save error', e);
            setStatus('Storage error — trade details may be too large');
        }
    }

    /* =====================================================
       API
    ===================================================== */

    function queueApiRequest(requestFn) {
        const run = apiQueue.then(async () => {
            const elapsed = Date.now() - lastApiRequestAt;
            const wait = Math.max(
                0,
                API_MIN_INTERVAL - elapsed
            );

            if (wait > 0) {
                await sleep(wait);
            }

            lastApiRequestAt = Date.now();
            return requestFn();
        });

        apiQueue = run.catch(() => {});
        return run;
    }

    async function api(path, params = {}, timeout = TIMEOUT) {
        return queueApiRequest(async () => {
            if (typeof PDA_httpGet !== 'function') {
                throw new Error('PDA_httpGet unavailable');
            }

            const query = new URLSearchParams();

            for (const [key, value] of Object.entries(params)) {
                if (
                    value !== undefined &&
                    value !== null &&
                    value !== ''
                ) {
                    query.set(key, value);
                }
            }

            const url =
                API +
                path +
                (query.toString() ? '?' + query.toString() : '');

            let timer;

            try {
                const request = PDA_httpGet(url, {
                    Authorization: `ApiKey ${API_KEY}`,
                    Accept: 'application/json'
                });

                const timeoutPromise = new Promise((_, reject) => {
                    timer = setTimeout(
                        () => reject(new Error('Request timed out')),
                        timeout
                    );
                });

                const response = await Promise.race([
                    request,
                    timeoutPromise
                ]);

                clearTimeout(timer);

                if (!response?.responseText) {
                    throw new Error('Empty Torn response');
                }

                const data = JSON.parse(response.responseText);

                if (data.error) {
                    throw new Error(
                        `${data.error.code || ''} ${data.error.error || 'API error'}`.trim()
                    );
                }

                return data;
            } catch (e) {
                clearTimeout(timer);
                throw e;
            }
        });
    }

    /* =====================================================
       CATALOGUE
    ===================================================== */

    async function loadCatalogue() {
        try {
            const cached = JSON.parse(
                localStorage.getItem(CATALOG_KEY) || 'null'
            );

            if (
                cached &&
                Array.isArray(cached.items) &&
                cached.items.length &&
                Date.now() - cached.time < 86400000
            ) {
                catalog = cached.items;
                buildCatalogMap();
                return;
            }
        } catch (_) {}

        setStatus('Loading item catalogue...');

        const data = await api(
            '/torn/items',
            {},
            15000
        );

        const raw = Array.isArray(data.items)
            ? data.items
            : (
                data.items &&
                typeof data.items === 'object'
                    ? Object.values(data.items)
                    : []
            );

        catalog = raw
            .filter(x => x && x.id && x.name)
            .map(x => ({
                id: Number(x.id),
                name: String(x.name),
                market_value:
                    Number(x.market_value) ||
                    Number(x.value?.market_price) ||
                    0
            }));

        buildCatalogMap();

        localStorage.setItem(
            CATALOG_KEY,
            JSON.stringify({
                time: Date.now(),
                items: catalog
            })
        );
    }

    function buildCatalogMap() {
        catalogMap = new Map(
            catalog.map(item => [
                Number(item.id),
                item
            ])
        );
    }

    /* =====================================================
       PURCHASE LOGS
    ===================================================== */

    function extractLogs(data) {
        const raw =
            data?.log ??
            data?.logs ??
            {};

        const output = [];

        if (Array.isArray(raw)) {
            for (const entry of raw) {
                output.push({
                    id: entry.id ?? entry.log_id ?? entry.timestamp,
                    data: entry
                });
            }

            return output;
        }

        if (raw && typeof raw === 'object') {
            for (const [id, entry] of Object.entries(raw)) {
                output.push({
                    id,
                    data: entry
                });
            }
        }

        return output;
    }

    async function getPurchaseLogs(to = null) {
        const params = {
            selections: 'log',
            log: '1112,1225'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    function parsePurchase(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        if (!Array.isArray(d?.items)) {
            return [];
        }

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        const seller =
            d?.seller_name ??
            d?.seller ??
            'Unknown';

        const total = Number(d?.cost_total ?? 0);
        const defaultUnit = Number(d?.cost_each ?? 0);

        if (!Number.isFinite(total) || total <= 0) {
            return [];
        }

        const output = [];

        for (const item of d.items) {
            const id = Number(item?.id);

            const quantity = Number(
                item?.qty ??
                item?.quantity ??
                item?.amount ??
                0
            );

            if (!id || quantity <= 0) continue;

            const catalogueItem = catalogMap.get(id);

            if (!catalogueItem) continue;

            let unit = Number(
                item?.cost_each ?? defaultUnit
            );

            if (!Number.isFinite(unit) || unit <= 0) {
                unit = total / quantity;
            }

            output.push({
                logId: String(logId),
                timestamp,
                dateText: formatDate(timestamp),
                itemId: id,
                itemName: catalogueItem.name,
                quantity,
                unitPrice: unit,
                total: unit * quantity,
                seller: String(seller)
            });
        }

        return output;
    }

    function purchaseKey(p) {
        return [
            p.logId,
            p.itemId,
            p.quantity,
            p.unitPrice,
            p.seller
        ].join('|');
    }

    function importPurchaseLogs(
        logs,
        wanted,
        existing
    ) {
        let matchedItems = 0;
        let imported = 0;

        for (const log of logs) {
            for (const purchase of parsePurchase(
                log.id,
                log.data
            )) {
                if (!wanted.has(norm(purchase.itemName))) {
                    continue;
                }

                matchedItems++;

                const key = purchaseKey(purchase);

                if (existing.has(key)) continue;

                existing.add(key);
                state.purchases.push(purchase);
                imported++;
            }
        }

        return {
            matchedItems,
            imported
        };
    }

    async function syncPurchases() {
        if (syncing || historySyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        syncing = true;

        try {
            setStatus('Getting purchase logs...');

            const logs = extractLogs(
                await getPurchaseLogs()
            );

            const wanted = new Set(
                state.tracked.map(x => norm(x.name))
            );

            const existing = new Set(
                state.purchases.map(purchaseKey)
            );

            const result = importPurchaseLogs(
                logs,
                wanted,
                existing
            );

            saveState();
            render();

            if (result.imported) {
                setStatus(
                    `Imported ${result.imported} purchase${result.imported === 1 ? '' : 's'}`
                );
            } else if (result.matchedItems) {
                setStatus(
                    `Found ${result.matchedItems} matching purchases — already saved`
                );
            } else {
                setStatus(
                    `Checked ${logs.length} logs — 0 tracked-item matches`
                );
            }
        } catch (e) {
            console.error('[TPL8] Purchase sync', e);
            setStatus('Sync error: ' + e.message);
        } finally {
            syncing = false;
        }
    }

    async function syncHistoricalPurchases() {
        if (historySyncing || syncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        historySyncing = true;

        try {
            setStatus('Starting unlimited purchase history...');

            const wanted = new Set(
                state.tracked.map(x => norm(x.name))
            );

            const existing = new Set(
                state.purchases.map(purchaseKey)
            );

            let data = await getPurchaseLogs();
            let previousOldest = null;
            let page = 0;
            let total = 0;

            while (true) {
                page++;

                const logs = extractLogs(data);

                if (!logs.length) break;

                total += importPurchaseLogs(
                    logs,
                    wanted,
                    existing
                ).imported;

                saveState();
                render();

                let oldest = null;

                for (const log of logs) {
                    const timestamp = getLogTimestamp(log);

                    if (
                        timestamp > 0 &&
                        (
                            oldest === null ||
                            timestamp < oldest
                        )
                    ) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (
                        previousOldest !== null &&
                        oldest >= previousOldest
                    )
                ) {
                    break;
                }

                previousOldest = oldest;

                setStatus(
                    `Purchase history: page ${page} — ${total} new`
                );

                await sleep(HISTORY_PAGE_DELAY);

                data = await getPurchaseLogs(oldest);
            }

            saveState();
            render();

            setStatus(
                `Purchase history finished — ${total} new purchases`
            );
        } catch (e) {
            console.error('[TPL8] Purchase history', e);
            setStatus('History error: ' + e.message);
        } finally {
            historySyncing = false;
        }
    }

    /* =====================================================
       SELL LOGS
    ===================================================== */

    async function getSellLogs(to = null) {
        const params = {
            selections: 'log',
            log: '1113,1226'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    function parseSell(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        if (!Array.isArray(d?.items)) {
            return [];
        }

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        const buyer =
            d?.buyer_name ??
            d?.buyer ??
            'Unknown';

        const total = Number(
            d?.cost_total ?? 0
        );

        const fee = Number(
            d?.fee ?? 0
        );

        const defaultUnit = Number(
            d?.cost_each ?? 0
        );

        if (!Number.isFinite(total) || total <= 0) {
            return [];
        }

        const output = [];

        for (const item of d.items) {
            const id = Number(item?.id);

            const quantity = Number(
                item?.qty ??
                item?.quantity ??
                item?.amount ??
                0
            );

            if (!id || quantity <= 0) continue;

            const catalogueItem = catalogMap.get(id);

            if (!catalogueItem) continue;

            let gross = Number(
                item?.cost_each ?? defaultUnit
            );

            if (!Number.isFinite(gross) || gross <= 0) {
                gross = total / quantity;
            }

            output.push({
                logId: String(logId),
                timestamp,
                dateText: formatDate(timestamp),
                itemId: id,
                itemName: catalogueItem.name,
                quantity,
                unitPrice: total / quantity,
                grossUnitPrice: gross,
                total,
                fee,
                buyer: String(buyer),
                market:
                    String(logId) === '1113'
                        ? 'Item Market'
                        : 'Bazaar'
            });
        }

        return output;
    }

    function sellKey(s) {
        return [
            s.logId,
            s.itemId,
            s.quantity,
            s.unitPrice,
            s.buyer,
            s.timestamp
        ].join('|');
    }

    function importSellLogs(
        logs,
        wanted,
        existing
    ) {
        let matchedItems = 0;
        let imported = 0;

        for (const log of logs) {
            for (const sale of parseSell(
                log.id,
                log.data
            )) {
                if (!wanted.has(norm(sale.itemName))) {
                    continue;
                }

                matchedItems++;

                const key = sellKey(sale);

                if (existing.has(key)) continue;

                existing.add(key);
                state.sells.push(sale);
                imported++;
            }
        }

        return {
            matchedItems,
            imported
        };
    }

    async function syncSells() {
        if (sellingSyncing || sellingHistorySyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        sellingSyncing = true;

        try {
            setStatus('Getting selling logs...');

            const logs = extractLogs(
                await getSellLogs()
            );

            const wanted = new Set(
                state.tracked.map(x => norm(x.name))
            );

            const existing = new Set(
                state.sells.map(sellKey)
            );

            const result = importSellLogs(
                logs,
                wanted,
                existing
            );

            saveState();
            render();

            if (result.imported) {
                setStatus(
                    `Imported ${result.imported} sale${result.imported === 1 ? '' : 's'}`
                );
            } else if (result.matchedItems) {
                setStatus(
                    `Found ${result.matchedItems} matching sales — already saved`
                );
            } else {
                setStatus(
                    `Checked ${logs.length} logs — 0 tracked-item sales`
                );
            }
        } catch (e) {
            console.error('[TPL8] Sell sync', e);
            setStatus(
                'Sell sync error: ' + e.message
            );
        } finally {
            sellingSyncing = false;
        }
    }

    async function syncHistoricalSells() {
        if (
            sellingHistorySyncing ||
            sellingSyncing
        ) {
            return;
        }

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        sellingHistorySyncing = true;

        try {
            setStatus(
                'Starting unlimited selling history...'
            );

            const wanted = new Set(
                state.tracked.map(x => norm(x.name))
            );

            const existing = new Set(
                state.sells.map(sellKey)
            );

            let data = await getSellLogs();
            let previousOldest = null;
            let page = 0;
            let total = 0;

            while (true) {
                page++;

                const logs = extractLogs(data);

                if (!logs.length) break;

                total += importSellLogs(
                    logs,
                    wanted,
                    existing
                ).imported;

                saveState();
                render();

                let oldest = null;

                for (const log of logs) {
                    const timestamp =
                        getLogTimestamp(log);

                    if (
                        timestamp > 0 &&
                        (
                            oldest === null ||
                            timestamp < oldest
                        )
                    ) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (
                        previousOldest !== null &&
                        oldest >= previousOldest
                    )
                ) {
                    break;
                }

                previousOldest = oldest;

                setStatus(
                    `Sell history: page ${page} — ${total} new`
                );

                await sleep(HISTORY_PAGE_DELAY);

                data = await getSellLogs(oldest);
            }

            saveState();
            render();

            setStatus(
                `Sell history finished — ${total} new sales`
            );
        } catch (e) {
            console.error('[TPL8] Sell history', e);
            setStatus(
                'Sell history error: ' + e.message
            );
        } finally {
            sellingHistorySyncing = false;
        }
    }

    /* =====================================================
       ITEM RECEIVE LOGS
    ===================================================== */

    async function getItemReceiveLogs(to = null) {
        const params = {
            selections: 'log',
            log: '4103'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    function parseItemReceive(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        let senderId = 0;
        let senderName = '';

        if (
            d?.sender &&
            typeof d.sender === 'object'
        ) {
            senderId =
                Number(
                    d.sender.id ??
                    d.sender.user_id ??
                    0
                ) || 0;

            senderName =
                firstString(
                    d.sender,
                    ['name', 'username']
                );
        } else {
            senderId =
                Number(
                    d?.sender_id ??
                    d?.sender ??
                    0
                ) || 0;

            senderName =
                firstString(
                    d,
                    [
                        'sender_name',
                        'sender_username'
                    ]
                );
        }

        const sender =
            senderName ||
            (
                senderId
                    ? `Player #${senderId}`
                    : 'Unknown'
            );

        const message =
            d?.message == null
                ? ''
                : String(d.message);

        const rawItems = d?.items;
        const output = [];

        const pushItem = (
            rawId,
            rawValue
        ) => {
            const id =
                Number(rawId) || 0;

            let quantity = 0;

            if (Array.isArray(rawValue)) {
                quantity =
                    Number(rawValue[0]) || 0;
            } else if (
                rawValue &&
                typeof rawValue === 'object'
            ) {
                quantity =
                    Number(
                        rawValue.quantity ??
                        rawValue.qty ??
                        rawValue.amount ??
                        rawValue.count ??
                        rawValue[0] ??
                        0
                    ) || 0;
            } else {
                quantity =
                    Number(rawValue) || 0;
            }

            if (!id || quantity <= 0) {
                return;
            }

            const catalogueItem =
                catalogMap.get(id);

            if (!catalogueItem) {
                return;
            }

            output.push({
                logId: String(logId),
                timestamp,
                dateText:
                    formatDate(timestamp),
                itemId: id,
                itemName:
                    catalogueItem.name,
                quantity,
                senderId,
                sender,
                message
            });
        };

        if (Array.isArray(rawItems)) {
            for (const item of rawItems) {
                if (
                    !item ||
                    typeof item !== 'object'
                ) {
                    continue;
                }

                pushItem(
                    item.id ??
                    item.item_id ??
                    item.itemId ??
                    item.details?.id,
                    item.quantity ??
                    item.qty ??
                    item.amount ??
                    item.count ??
                    item.details?.amount ??
                    item
                );
            }
        } else if (
            rawItems &&
            typeof rawItems === 'object'
        ) {
            for (
                const [rawId, rawValue]
                of Object.entries(rawItems)
            ) {
                pushItem(
                    rawId,
                    rawValue
                );
            }
        }

        return output;
    }

    function itemReceiveKey(receive) {
        return [
            receive.logId,
            receive.itemId,
            receive.quantity,
            receive.senderId || '',
            receive.timestamp,
            receive.message || ''
        ].join('|');
    }

    function importItemReceiveLogs(
        logs,
        wanted,
        existing
    ) {
        let matchedItems = 0;
        let imported = 0;

        for (const log of logs) {
            for (
                const receive
                of parseItemReceive(
                    log.id,
                    log.data
                )
            ) {
                if (
                    !wanted.has(
                        norm(receive.itemName)
                    )
                ) {
                    continue;
                }

                matchedItems++;

                const key =
                    itemReceiveKey(receive);

                if (existing.has(key)) {
                    continue;
                }

                existing.add(key);
                receive.tmvAtReceive =
                    currentTmvFor(receive.itemId);
                state.itemReceives.push(
                    receive
                );
                imported++;
            }
        }

        state.itemReceives.sort(
            (a, b) =>
                Number(a.timestamp || 0) -
                Number(b.timestamp || 0)
        );

        return {
            matchedItems,
            imported
        };
    }

    async function syncItemReceives() {
        if (
            receivingSyncing ||
            receivingHistorySyncing
        ) {
            return;
        }

        if (!state.tracked.length) {
            setStatus(
                'Track an item first'
            );
            return;
        }

        receivingSyncing = true;

        try {
            setStatus(
                'Getting Item Receive logs...'
            );

            const logs =
                extractLogs(
                    await getItemReceiveLogs()
                );

            const wanted =
                new Set(
                    state.tracked.map(
                        x => norm(x.name)
                    )
                );

            const existing =
                new Set(
                    state.itemReceives.map(
                        itemReceiveKey
                    )
                );

            const result =
                importItemReceiveLogs(
                    logs,
                    wanted,
                    existing
                );

            saveState();
            render();

            if (result.imported) {
                setStatus(
                    `Imported ${result.imported} Item Receive record${result.imported === 1 ? '' : 's'}`
                );
            } else if (
                result.matchedItems
            ) {
                setStatus(
                    `Found ${result.matchedItems} matching Item Receive records — already saved`
                );
            } else {
                setStatus(
                    `Checked ${logs.length} logs — 0 tracked-item receives`
                );
            }
        } catch (e) {
            console.error(
                '[TPL8] Item Receive sync',
                e
            );

            setStatus(
                'Item Receive sync error: ' +
                e.message
            );
        } finally {
            receivingSyncing = false;
        }
    }

    async function syncHistoricalItemReceives() {
        if (
            receivingHistorySyncing ||
            receivingSyncing
        ) {
            return;
        }

        if (!state.tracked.length) {
            setStatus(
                'Track an item first'
            );
            return;
        }

        receivingHistorySyncing = true;

        try {
            setStatus(
                'Starting unlimited Item Receive history...'
            );

            const wanted =
                new Set(
                    state.tracked.map(
                        x => norm(x.name)
                    )
                );

            const existing =
                new Set(
                    state.itemReceives.map(
                        itemReceiveKey
                    )
                );

            let data =
                await getItemReceiveLogs();

            let previousOldest = null;
            let page = 0;
            let total = 0;

            while (true) {
                page++;

                const logs =
                    extractLogs(data);

                if (!logs.length) {
                    break;
                }

                total +=
                    importItemReceiveLogs(
                        logs,
                        wanted,
                        existing
                    ).imported;

                saveState();
                render();

                let oldest = null;

                for (const log of logs) {
                    const timestamp =
                        getLogTimestamp(log);

                    if (
                        timestamp > 0 &&
                        (
                            oldest === null ||
                            timestamp < oldest
                        )
                    ) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (
                        previousOldest !== null &&
                        oldest >= previousOldest
                    )
                ) {
                    break;
                }

                previousOldest = oldest;

                setStatus(
                    `Item Receive history: page ${page} — ${total} new`
                );

                await sleep(
                    HISTORY_PAGE_DELAY
                );

                data =
                    await getItemReceiveLogs(
                        oldest
                    );
            }

            saveState();
            render();

            setStatus(
                `Item Receive history finished — ${total} new records`
            );
        } catch (e) {
            console.error(
                '[TPL8] Item Receive history',
                e
            );

            setStatus(
                'Item Receive history error: ' +
                e.message
            );
        } finally {
            receivingHistorySyncing = false;
        }
    }

    /* =====================================================
       TRAVEL PURCHASE LOGS (DIAGNOSTICS ONLY)
    ===================================================== */

    /*
     * Travel-buy diagnostics intentionally exclude restricted-item
     * tracking. The rest of the ledger remains unchanged and these
     * records are not included in FIFO/P&L.
     */
    const TRAVEL_DIAGNOSTIC_BLOCKED_NAMES = new Set([]);

    function isTravelDiagnosticAllowed(itemName) {
        return !TRAVEL_DIAGNOSTIC_BLOCKED_NAMES.has(
            norm(itemName)
        );
    }

    async function getTravelPurchaseLogs(to = null) {
        const params = {
            selections: 'log',
            log: '4201'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    /* =====================================================
       ITEM / DRUG USE (log 2290)
    ===================================================== */

    async function getItemUseLogs(to = null) {
        const params = {
            selections: 'log',
            log: '2290'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    function parseItemUse(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        const texts = collectStrings(log, []);

        /* "You used some Xanax from Natural Selection IV's armory gaining ..." */
        const hasArmoryKey = (o, depth = 0) => {
            if (!o || typeof o !== 'object' || depth > 3) return false;

            for (const [k, v] of Object.entries(o)) {
                if (/armou?ry/i.test(k) && v) return true;
                if (v && typeof v === 'object' && hasArmoryKey(v, depth + 1)) return true;
            }

            return false;
        };

        const armory =
            Number(d?.faction) > 0 ||
            texts.some(t => /\barmou?ry\b/i.test(t)) ||
            hasArmoryKey(log);

        let item = null;

        /* 1. item id in the payload */
        const id = pickNumber(d, ['drug', 'drug_id', 'item', 'item_id', 'itemId', 'id']);
        if (id && catalogMap.has(id)) item = catalogMap.get(id);

        /* 2. text: "You used some Xanax gaining 250 energy and 75 happiness" */
        if (!item) {
            for (const raw of texts) {
                const text = raw.replace(/\s+from\s+.+?['\u2019]s?\s+armory/i, '');

                const m = text.match(
                    /used\s+(?:some\s+|an?\s+|the\s+|\d+x\s+)?(.+?)(?:\s+gaining|\s+and\s|\s+which|\s*[,.]|$)/i
                );
                if (!m) continue;

                const name = norm(m[1]);
                const found = [...catalogMap.values()].find(
                    x => norm(x.name) === name
                );

                if (found) {
                    item = found;
                    break;
                }
            }
        }

        if (!item) return [];

        const qty =
            pickNumber(d, ['qty', 'quantity', 'amount', 'count']) || 1;

        const row = {
            logId: String(logId),
            timestamp,
            dateText: formatDate(timestamp),
            itemId: item.id,
            itemName: item.name,
            quantity: qty
        };

        if (armory) row.armory = true;

        return [row];
    }

    async function getOverdoseLogs(to = null) {
        const params = {
            selections: 'log',
            log: overdoseLogId()
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    /* "You overdosed on some Xanax going to the hospital for 83h 20m and losing ..." */
    function parseOverdose(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        let item = null;

        const id = pickNumber(d, ['drug', 'drug_id', 'item', 'item_id', 'itemId', 'id']);
        if (id && catalogMap.has(id)) item = catalogMap.get(id);

        if (!item) {
            for (const text of collectStrings(log, [])) {
                const m = text.match(
                    /overdosed\s+on\s+(?:some\s+|an?\s+|the\s+)?(.+?)(?:\s+going|\s+and\s|\s+which|\s*[,.]|$)/i
                );
                if (!m) continue;

                const name = norm(m[1]);
                const found = [...catalogMap.values()].find(
                    x => norm(x.name) === name
                );

                if (found) {
                    item = found;
                    break;
                }
            }
        }

        if (!item) return [];

        return [{
            logId: String(logId),
            timestamp,
            dateText: formatDate(timestamp),
            itemId: item.id,
            itemName: item.name,
            quantity: 1,
            kind: 'overdose'
        }];
    }

    async function getItemSendLogs(to = null) {
        const params = {
            selections: 'log',
            log: '4102'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    /* "You sent 6039x Permanent Marker to FAFFO with the message: ..." */
    function parseItemSend(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        const totals = new Map();

        const add = (id, qty) => {
            id = Number(id) || 0;
            qty = Number(qty) || 0;
            if (!id || qty <= 0 || !catalogMap.has(id)) return;
            totals.set(id, (totals.get(id) || 0) + qty);
        };

        const qtyOf = v => {
            if (Array.isArray(v)) return Number(v[0]) || 0;
            if (v && typeof v === 'object') {
                return (
                    Number(
                        v.quantity ?? v.qty ?? v.amount ?? v.count ?? v[0] ?? 0
                    ) || 0
                );
            }
            return Number(v) || 0;
        };

        const rawItems = d?.items;

        if (Array.isArray(rawItems)) {
            for (const item of rawItems) {
                if (!item || typeof item !== 'object') continue;
                add(
                    item.id ?? item.item_id ?? item.itemId ?? item.details?.id,
                    qtyOf(item)
                );
            }
        } else if (rawItems && typeof rawItems === 'object') {
            for (const [rawId, rawValue] of Object.entries(rawItems)) {
                add(rawId, qtyOf(rawValue));
            }
        }

        if (!totals.size) {
            for (const line of findItemLines(d, [])) {
                add(
                    pickNumber(line, ['id', 'item_id', 'itemId', 'item']),
                    pickNumber(line, ['qty', 'quantity', 'amount', 'count'])
                );
            }
        }

        let recipient = '';
        let message = '';

        for (const text of collectStrings(log, [])) {
            const head = text.match(
                /sent\s+(.+?)\s+to\s+(.+?)(?:\s+with\s+the\s+message:?\s*(.*))?\s*$/i
            );
            if (!head) continue;

            if (!recipient) recipient = head[2].trim();
            if (head[3]) message = head[3].trim();

            if (totals.size) continue;

            for (const part of head[1].split(/,\s*/)) {
                const m = part.trim().match(/^(?:(\d[\d,]*)\s*x\s+|an?\s+)?(.+?)$/i);
                if (!m) continue;

                const qty = m[1] ? Number(m[1].replace(/,/g, '')) : 1;
                const name = norm(m[2]);

                const found = [...catalogMap.values()].find(
                    item => norm(item.name) === name
                );

                if (found) add(found.id, qty);
            }
        }

        const output = [];

        for (const [id, quantity] of totals) {
            output.push({
                logId: String(logId),
                timestamp,
                dateText: formatDate(timestamp),
                itemId: id,
                itemName: catalogMap.get(id).name,
                quantity,
                recipient: recipient || 'Unknown',
                message: message.slice(0, 200)
            });
        }

        return output;
    }

    function itemSendKey(send) {
        return [
            send.logId,
            send.itemId,
            send.quantity,
            send.timestamp
        ].join('|');
    }

    /* Pages one log stream and imports it. Returns counts. */
    async function pageUseStream(label, fetchPage, parser, diagKey, wanted, existing, target, keyFn, save = true) {
        let data = await fetchPage(null);
        let previousOldest = null;
        let page = 0;
        let total = 0;
        let seen = 0;
        let unreadable = 0;

        while (true) {
            page++;
            const logs = extractLogs(data);
            if (!logs.length) break;

            const result = importItemUseLogs(logs, wanted, existing, parser, diagKey, target, keyFn);
            total += result.imported;
            seen += logs.length;
            unreadable += result.unreadable;

            if (save) saveState();
            render();

            let oldest = null;
            for (const log of logs) {
                const timestamp = getLogTimestamp(log);
                if (timestamp > 0 && (oldest === null || timestamp < oldest)) {
                    oldest = timestamp;
                }
            }

            if (
                oldest === null ||
                (previousOldest !== null && oldest >= previousOldest)
            ) {
                break;
            }

            previousOldest = oldest;
            setStatus(`${label} history: page ${page} — ${total} new`);
            await sleep(HISTORY_PAGE_DELAY);
            data = await fetchPage(oldest);
        }

        return { total, seen, unreadable };
    }

    function itemUseKey(use) {
        return [
            use.logId,
            use.itemId,
            use.quantity,
            use.timestamp
        ].join('|');
    }

    function importItemUseLogs(logs, wanted, existing, parser = parseItemUse, diagKey = USE_DIAG_KEY, target = state.itemUses, keyFn = itemUseKey) {
        let matched = 0;
        let imported = 0;
        let readable = 0;
        let unreadable = 0;
        let armoryRows = 0;

        let diag = {};
        try {
            diag = JSON.parse(localStorage.getItem(diagKey) || '{}') || {};
        } catch (_) {}

        if (!Array.isArray(diag.samples)) diag.samples = [];
        if (!Array.isArray(diag.sigs)) diag.sigs = [];

        for (const log of logs) {
            try {
                const entry = log.data && typeof log.data === 'object' ? log.data : {};
                const payload = entry.data && typeof entry.data === 'object' ? entry.data : entry;

                const sig =
                    Object.keys(payload).sort().map(k =>
                        k === 'faction'
                            ? (Number(payload.faction) > 0 ? 'faction=ID(armory)' : 'faction=0(own)')
                            : k
                    ).join(',') +
                    (
                        entry.params && typeof entry.params === 'object'
                            ? ' | params: ' + Object.keys(entry.params).sort().join(',')
                            : ''
                    );

                let group = diag.sigs.find(g => g.sig === sig);

                if (!group && diag.sigs.length < 8) {
                    group = {
                        sig,
                        count: 0,
                        sample: JSON.stringify(compactTradeObject(entry)).slice(0, 600)
                    };
                    diag.sigs.push(group);
                }

                if (group) group.count++;
            } catch (_) {}

            const rows = parser(log.id, log.data);

            if (!rows.length) {
                unreadable++;
                if (diag.samples.length < 3) {
                    try {
                        diag.samples.push(
                            JSON.stringify(compactTradeObject(log.data)).slice(0, 900)
                        );
                    } catch (_) {}
                }
                continue;
            }

            readable++;

            for (const use of rows) {
                if (use.armory) armoryRows++;

                if (!wanted.has(norm(use.itemName))) continue;

                matched++;
                const key = keyFn(use);
                if (existing.has(key)) continue;

                existing.add(key);
                target.push(use);
                imported++;
            }
        }

        diag.lastRaw = logs.length;
        diag.lastParsed = readable;
        diag.lastUnparsed = unreadable;
        diag.lastMatched = matched;
        diag.lastArmory = armoryRows;
        diag.time = Date.now();

        try {
            localStorage.setItem(diagKey, JSON.stringify(diag));
        } catch (_) {}

        target.sort(
            (a, b) => Number(a.timestamp || 0) - Number(b.timestamp || 0)
        );

        return { matched, imported, readable, unreadable };
    }

    async function syncItemUses() {
        if (useSyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        useSyncing = true;

        const backupUses = state.itemUses;
        const backupSends = state.itemSends;

        try {
            const wanted = new Set(
                state.tracked.map(item => norm(item.name))
            );

            /* Rebuild from scratch so records are always reclassified. */
            state.itemUses = [];
            state.itemSends = [];

            try {
                localStorage.removeItem(USE_DIAG_KEY);
                localStorage.removeItem(OD_DIAG_KEY);
                localStorage.removeItem(SEND_DIAG_KEY);
            } catch (_) {}

            const useExisting = new Set();
            const sendExisting = new Set();

            setStatus('Getting item use logs...');

            const uses = await pageUseStream(
                'Item use',
                to => getItemUseLogs(to),
                parseItemUse,
                USE_DIAG_KEY,
                wanted,
                useExisting,
                state.itemUses,
                itemUseKey,
                false
            );

            setStatus('Getting overdose logs...');

            const overdoses = await pageUseStream(
                'Overdose',
                to => getOverdoseLogs(to),
                parseOverdose,
                OD_DIAG_KEY,
                wanted,
                useExisting,
                state.itemUses,
                itemUseKey,
                false
            );

            setStatus('Getting item send logs...');

            const sends = await pageUseStream(
                'Item send',
                to => getItemSendLogs(to),
                parseItemSend,
                SEND_DIAG_KEY,
                wanted,
                sendExisting,
                state.itemSends,
                itemSendKey,
                false
            );

            saveState();
            render();

            const armoryCount = state.itemUses.filter(u => u.armory).length;
            const odCount = state.itemUses.filter(u => u.kind === 'overdose').length;
            const ownUses = state.itemUses.length - odCount - armoryCount;
            const unreadable = uses.unreadable + overdoses.unreadable + sends.unreadable;

            setStatus(
                `Use sync: ${ownUses} uses · ${armoryCount} faction armory (not counted) · ${odCount} overdoses · ${state.itemSends.length} sends` +
                (unreadable ? ` · ${unreadable} unreadable` : '')
            );
        } catch (e) {
            state.itemUses = backupUses;
            state.itemSends = backupSends;
            console.error('[TPL8] Item use sync', e);
            setStatus('Item use sync error: ' + e.message + ' (previous data kept)');
        } finally {
            useSyncing = false;
        }
    }

    /* =====================================================
       PARCEL / PRESENT OPENS (log 4001)
    ===================================================== */

    const PARCEL_DIAG_KEY = 'TPL8_PARCEL_DIAG';

    async function getParcelOpenLogs(to = null) {
        const params = {
            selections: 'log',
            log: '4001'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api('/user', params, 15000);
    }

    function parseParcelOpen(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        const totals = new Map();

        const add = (id, qty) => {
            id = Number(id) || 0;
            qty = Number(qty) || 0;
            if (!id || qty <= 0 || !catalogMap.has(id)) return;
            totals.set(id, (totals.get(id) || 0) + qty);
        };

        const qtyOf = v => {
            if (Array.isArray(v)) return Number(v[0]) || 0;
            if (v && typeof v === 'object') {
                return (
                    Number(
                        v.quantity ?? v.qty ?? v.amount ?? v.count ?? v[0] ?? 0
                    ) || 0
                );
            }
            return Number(v) || 0;
        };

        /* 1. data.items as an array or an id-keyed map */
        const rawItems = d?.items;

        if (Array.isArray(rawItems)) {
            for (const item of rawItems) {
                if (!item || typeof item !== 'object') continue;
                add(
                    item.id ?? item.item_id ?? item.itemId ?? item.details?.id,
                    qtyOf(item)
                );
            }
        } else if (rawItems && typeof rawItems === 'object') {
            for (const [rawId, rawValue] of Object.entries(rawItems)) {
                add(rawId, qtyOf(rawValue));
            }
        }

        /* 2. Item lines anywhere in the payload */
        if (!totals.size) {
            for (const line of findItemLines(d, [])) {
                add(
                    pickNumber(line, ['id', 'item_id', 'itemId', 'item']),
                    pickNumber(line, ['qty', 'quantity', 'amount', 'count'])
                );
            }
        }

        /* 3. Text: "You opened a Parcel containing 1x AK-47, 2x Axe, a Trench Coat" */
        let container = '';

        for (const text of collectStrings(log, [])) {
            const head = text.match(/opened\s+(?:an?\s+)?(.+?)\s+containing\s+/i);
            if (head && !container) container = head[1].trim();

            if (totals.size) continue;

            const list = text.match(/containing\s+(.+?)\.?$/i);
            if (!list) continue;

            for (const part of list[1].split(/,\s*/)) {
                const m = part.trim().match(/^(?:(\d[\d,]*)\s*x\s+|an?\s+)?(.+?)$/i);
                if (!m) continue;

                const qty = m[1] ? Number(m[1].replace(/,/g, '')) : 1;
                const name = norm(m[2]);

                const found = [...catalogMap.values()].find(
                    item => norm(item.name) === name
                );

                if (found) add(found.id, qty);
            }
        }

        if (!container) {
            container = firstString(
                d,
                ['parcel', 'present', 'gift', 'container', 'name']
            ) || 'Parcel';
        }

        const output = [];

        for (const [id, quantity] of totals) {
            output.push({
                logId: String(logId),
                timestamp,
                dateText: formatDate(timestamp),
                itemId: id,
                itemName: catalogMap.get(id).name,
                quantity,
                container
            });
        }

        return output;
    }

    function parcelOpenKey(open) {
        return [
            open.logId,
            open.itemId,
            open.quantity,
            open.timestamp
        ].join('|');
    }

    function importParcelOpenLogs(logs, wanted, existing) {
        let matched = 0;
        let imported = 0;
        let parsedLogs = 0;
        let unreadable = 0;

        let diag = {};
        try {
            diag = JSON.parse(localStorage.getItem(PARCEL_DIAG_KEY) || '{}') || {};
        } catch (_) {}

        if (!Array.isArray(diag.samples)) diag.samples = [];

        for (const log of logs) {
            const rows = parseParcelOpen(log.id, log.data);

            if (!rows.length) {
                unreadable++;
                if (diag.samples.length < 3) {
                    try {
                        diag.samples.push(
                            JSON.stringify(compactTradeObject(log.data)).slice(0, 900)
                        );
                    } catch (_) {}
                }
                continue;
            }

            parsedLogs++;

            for (const open of rows) {
                if (!wanted.has(norm(open.itemName))) continue;

                matched++;
                const key = parcelOpenKey(open);
                if (existing.has(key)) continue;

                existing.add(key);
                open.tmvAtReceive = currentTmvFor(open.itemId);
                state.parcelOpens.push(open);
                imported++;
            }
        }

        diag.lastRaw = logs.length;
        diag.lastParsed = parsedLogs;
        diag.lastUnparsed = unreadable;
        diag.lastMatched = matched;
        diag.time = Date.now();

        try {
            localStorage.setItem(PARCEL_DIAG_KEY, JSON.stringify(diag));
        } catch (_) {}

        state.parcelOpens.sort(
            (a, b) => Number(a.timestamp || 0) - Number(b.timestamp || 0)
        );

        return { matched, imported, parsedLogs, unreadable };
    }

    async function syncParcelOpens() {
        if (parcelSyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        parcelSyncing = true;

        try {
            setStatus('Getting parcel/present logs...');

            const wanted = new Set(
                state.tracked.map(item => norm(item.name))
            );

            const existing = new Set(
                state.parcelOpens.map(parcelOpenKey)
            );

            let data = await getParcelOpenLogs();
            let previousOldest = null;
            let page = 0;
            let total = 0;
            let seen = 0;
            let unreadable = 0;

            while (true) {
                page++;
                const logs = extractLogs(data);
                if (!logs.length) break;

                const result = importParcelOpenLogs(logs, wanted, existing);
                total += result.imported;
                seen += logs.length;
                unreadable += result.unreadable;

                saveState();
                render();

                let oldest = null;
                for (const log of logs) {
                    const timestamp = getLogTimestamp(log);
                    if (timestamp > 0 && (oldest === null || timestamp < oldest)) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (previousOldest !== null && oldest >= previousOldest)
                ) {
                    break;
                }

                previousOldest = oldest;
                setStatus(`Parcel history: page ${page} — ${total} new`);
                await sleep(HISTORY_PAGE_DELAY);
                data = await getParcelOpenLogs(oldest);
            }

            saveState();
            render();

            setStatus(
                total
                    ? `Parcels: ${total} new item record${total === 1 ? '' : 's'} (${seen} opens checked)`
                    : `Parcels: checked ${seen} opens — ${unreadable} unreadable, 0 new tracked items`
            );
        } catch (e) {
            console.error('[TPL8] Parcel sync', e);
            setStatus('Parcel sync error: ' + e.message);
        } finally {
            parcelSyncing = false;
        }
    }

    function collectStrings(v, out, depth = 0) {
        if (depth > 6 || v == null) return out;
        if (typeof v === 'string') {
            if (v.trim()) out.push(v);
        } else if (Array.isArray(v)) {
            for (const x of v) collectStrings(x, out, depth + 1);
        } else if (typeof v === 'object') {
            for (const x of Object.values(v)) collectStrings(x, out, depth + 1);
        }
        return out;
    }

    function pickNumber(o, keys) {
        if (!o || typeof o !== 'object') return 0;
        for (const k of keys) {
            const n = Number(o[k]);
            if (Number.isFinite(n) && n > 0) return n;
        }
        return 0;
    }

    /* Find every object in the payload that looks like an item line. */
    function findItemLines(v, out, depth = 0) {
        if (depth > 6 || v == null || typeof v !== 'object') return out;

        if (Array.isArray(v)) {
            for (const x of v) findItemLines(x, out, depth + 1);
            return out;
        }

        const id = pickNumber(v, ['id', 'item_id', 'itemId', 'item']);
        const qty = pickNumber(v, ['qty', 'quantity', 'amount', 'count']);

        if (id && qty && catalogMap.has(id)) {
            out.push(v);
            return out;
        }

        for (const x of Object.values(v)) {
            findItemLines(x, out, depth + 1);
        }
        return out;
    }

    function parseTravelPurchase(logId, log) {
        const d =
            log?.data && typeof log.data === 'object'
                ? log.data
                : log;

        const timestamp = Number(
            log?.timestamp ??
            d?.timestamp ??
            d?.time ??
            0
        );

        let destination = firstString(
            d,
            ['country', 'destination', 'location', 'city', 'shop', 'from']
        );

        const output = [];

        const addPurchase = (
            id,
            quantity,
            unitPrice,
            total,
            itemName = '',
            where = ''
        ) => {
            id = Number(id) || 0;
            quantity = Number(quantity) || 0;
            unitPrice = Number(unitPrice) || 0;
            total = Number(total) || 0;

            const catalogueItem = id
                ? catalogMap.get(id)
                : null;

            const resolvedName =
                catalogueItem?.name ||
                String(itemName || '').trim();

            if (!resolvedName) return;
            if (!isTravelDiagnosticAllowed(resolvedName)) return;

            if (!total && unitPrice && quantity) {
                total = unitPrice * quantity;
            }

            if (!unitPrice && total && quantity) {
                unitPrice = total / quantity;
            }

            output.push({
                logId: String(logId),
                timestamp,
                dateText: formatDate(timestamp),
                itemId: id,
                itemName: resolvedName,
                quantity: quantity || 1,
                unitPrice,
                total,
                destination: destination || String(where || '').trim()
            });
        };

        /* Payload-level price fallbacks (used when the item line has none). */
        const payloadUnit = pickNumber(d, ['cost_each', 'price_each', 'unit_price', 'price', 'cost']);
        const payloadTotal = pickNumber(d, ['cost_total', 'total', 'total_cost', 'amount_paid']);

        /* 1. Structured item lines (any depth). */
        const lines = findItemLines(d, []);

        if (lines.length) {
            for (const line of lines) {
                const id = pickNumber(line, ['id', 'item_id', 'itemId', 'item']);
                const qty = pickNumber(line, ['qty', 'quantity', 'amount', 'count']);

                let unit = pickNumber(line, ['cost_each', 'price_each', 'unit_price', 'price', 'cost']);
                let total = pickNumber(line, ['cost_total', 'total', 'amount_paid']);

                if (!unit && !total) {
                    if (payloadUnit) unit = payloadUnit;
                    else if (payloadTotal && lines.length === 1) total = payloadTotal;
                }

                addPurchase(id, qty, unit, total, catalogMap.get(id)?.name || '', destination);
            }

            if (output.length) return output;
        }

        /* 2. Flat payload: item id + quantity directly on the data object. */
        const flatId = pickNumber(d, ['item_id', 'itemId', 'item', 'id']);
        const flatQty = pickNumber(d, ['qty', 'quantity', 'amount', 'count']);

        if (flatId && flatQty && catalogMap.has(flatId)) {
            addPurchase(flatId, flatQty, payloadUnit, payloadTotal, '', destination);
            if (output.length) return output;
        }

        /* 3. Human-readable text, e.g.
              "You bought 56x Chamois Plushie at $400 each for a total of $22,400 from Switzerland" */
        const texts = collectStrings(log, []);

        for (const text of texts) {
            const match = text.match(
                /(\d[\d,]*)\s*x\s+(.+?)\s+at\s+\$([\d,]+)(?:\s+each)?(?:\s+for\s+a\s+total\s+of\s+\$([\d,]+))?(?:\s+from\s+([^.]+?))?(?:\.|$)/i
            );

            if (!match) continue;

            const [, rawQty, rawName, rawUnit, rawTotal, rawCountry] = match;

            if (rawCountry) destination = rawCountry.trim();

            const cleanName = rawName.trim().replace(/^(?:bought\s+)/i, '');

            const catalogueItem = [...catalogMap.values()].find(
                item => norm(item.name) === norm(cleanName)
            );

            addPurchase(
                catalogueItem?.id ?? 0,
                Number(rawQty.replace(/,/g, '')),
                Number(rawUnit.replace(/,/g, '')),
                rawTotal ? Number(rawTotal.replace(/,/g, '')) : 0,
                cleanName,
                destination
            );

            if (output.length) return output;
        }

        return output;
    }

    function travelPurchaseKey(purchase) {
        return [
            purchase.logId,
            purchase.itemId,
            purchase.quantity,
            purchase.unitPrice,
            purchase.timestamp,
            purchase.destination || ''
        ].join('|');
    }

    function importTravelPurchaseLogs(logs, wanted, existing) {
        let matchedItems = 0;
        let imported = 0;
        let parsed = 0;
        let unparsed = 0;
        const parsedNames = new Set();

        let diag = {};
        try {
            diag = JSON.parse(localStorage.getItem(TRAVEL_DIAG_KEY) || '{}') || {};
        } catch (_) {}

        if (!Array.isArray(diag.samples)) diag.samples = [];

        for (const log of logs) {
            const rows = parseTravelPurchase(log.id, log.data);

            if (!rows.length) {
                unparsed++;
                if (diag.samples.length < 3) {
                    try {
                        diag.samples.push(
                            JSON.stringify(compactTradeObject(log.data)).slice(0, 900)
                        );
                    } catch (_) {}
                }
                continue;
            }

            for (const purchase of rows) {
                parsed++;
                parsedNames.add(purchase.itemName);

                if (!wanted.has(norm(purchase.itemName))) continue;

                matchedItems++;
                const key = travelPurchaseKey(purchase);
                if (existing.has(key)) continue;

                existing.add(key);
                state.travelPurchases.push(purchase);
                imported++;
            }
        }

        diag.lastRaw = logs.length;
        diag.lastParsed = parsed;
        diag.lastUnparsed = unparsed;
        diag.lastMatched = matchedItems;
        diag.lastNames = [...parsedNames].slice(0, 12);
        diag.time = Date.now();

        try {
            localStorage.setItem(TRAVEL_DIAG_KEY, JSON.stringify(diag));
        } catch (_) {}

        state.travelPurchases.sort(
            (a, b) => Number(a.timestamp || 0) - Number(b.timestamp || 0)
        );

        return { matchedItems, imported, parsed, unparsed };
    }

    async function syncTravelPurchases() {
        if (travelSyncing || travelHistorySyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        travelSyncing = true;

        try {
            setStatus('Getting travel purchase logs...');

            const logs = extractLogs(
                await getTravelPurchaseLogs()
            );

            const wanted = new Set(
                state.tracked
                    .filter(item => isTravelDiagnosticAllowed(item.name))
                    .map(item => norm(item.name))
            );

            const existing = new Set(
                state.travelPurchases.map(travelPurchaseKey)
            );

            const result = importTravelPurchaseLogs(logs, wanted, existing);

            saveState();
            render();

            setStatus(
                result.imported
                    ? `Imported ${result.imported} travel purchase record${result.imported === 1 ? '' : 's'}`
                    : result.matchedItems
                        ? `Found ${result.matchedItems} matching travel purchases — already saved`
                        : `Checked ${logs.length} logs — ${result.parsed} parsed, ${result.unparsed} unreadable, 0 tracked-item matches`
            );
        } catch (e) {
            console.error('[TPL8] Travel purchase sync', e);
            setStatus('Travel purchase sync error: ' + e.message);
        } finally {
            travelSyncing = false;
        }
    }

    async function syncHistoricalTravelPurchases() {
        if (travelHistorySyncing || travelSyncing) return;

        if (!state.tracked.length) {
            setStatus('Track an item first');
            return;
        }

        travelHistorySyncing = true;

        try {
            setStatus('Starting unlimited travel purchase history...');

            const wanted = new Set(
                state.tracked
                    .filter(item => isTravelDiagnosticAllowed(item.name))
                    .map(item => norm(item.name))
            );

            const existing = new Set(
                state.travelPurchases.map(travelPurchaseKey)
            );

            let data = await getTravelPurchaseLogs();
            let previousOldest = null;
            let page = 0;
            let total = 0;

            while (true) {
                page++;
                const logs = extractLogs(data);
                if (!logs.length) break;

                total += importTravelPurchaseLogs(logs, wanted, existing).imported;

                saveState();
                render();

                let oldest = null;
                for (const log of logs) {
                    const timestamp = getLogTimestamp(log);
                    if (timestamp > 0 && (oldest === null || timestamp < oldest)) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (previousOldest !== null && oldest >= previousOldest)
                ) {
                    break;
                }

                previousOldest = oldest;
                setStatus(`Travel purchase history: page ${page} — ${total} new`);
                await sleep(HISTORY_PAGE_DELAY);
                data = await getTravelPurchaseLogs(oldest);
            }

            saveState();
            render();
            setStatus(`Travel purchase history finished — ${total} new records`);
        } catch (e) {
            console.error('[TPL8] Travel purchase history', e);
            setStatus('Travel purchase history error: ' + e.message);
        } finally {
            travelHistorySyncing = false;
        }
    }

    /* =====================================================
       TRADES
    ===================================================== */

    function extractTrades(data) {
        const raw =
            data?.trades ??
            data?.trade ??
            data?.data ??
            [];

        if (Array.isArray(raw)) {
            return raw;
        }

        if (raw && typeof raw === 'object') {
            return Object.entries(raw).map(
                ([id, value]) => ({
                    id,
                    ...(value || {})
                })
            );
        }

        return [];
    }

    async function getTrades(to = null) {
        const params = {
            cat: 'finished',
            limit: 100,
            sort: 'DESC'
        };

        if (to != null) {
            params.to = Number(to);
        }

        return api(
            '/user/trades',
            params,
            20000
        );
    }

    function tradeId(t) {
        return String(
            t?.id ??
            t?.trade_id ??
            t?.tradeId ??
            t?.uid ??
            t?.ID ??
            ''
        );
    }

    function tradeTimestamp(t) {
        return timestampOf(t);
    }

    function tradePlayer(t) {
        const trader = t?.trader;

        if (
            trader &&
            typeof trader === 'object' &&
            trader.name
        ) {
            return String(trader.name);
        }

        return (
            firstString(t, [
                'user_name',
                'username',
                'player_name',
                'player',
                'name',
                'partner_name',
                'other_user_name'
            ]) ||
            'Unknown player'
        );
    }

    function compactTradeObject(v, depth = 0) {
        if (depth > 5) return '[max depth]';

        if (
            v === null ||
            v === undefined
        ) {
            return v;
        }

        if (typeof v === 'string') {
            return v.length > 500
                ? v.slice(0, 500) + '…'
                : v;
        }

        if (
            typeof v === 'number' ||
            typeof v === 'boolean'
        ) {
            return v;
        }

        if (Array.isArray(v)) {
            return v
                .slice(0, 150)
                .map(x =>
                    compactTradeObject(
                        x,
                        depth + 1
                    )
                );
        }

        if (typeof v === 'object') {
            const output = {};

            for (
                const key of Object.keys(v).slice(0, 80)
            ) {
                output[key] =
                    compactTradeObject(
                        v[key],
                        depth + 1
                    );
            }

            return output;
        }

        return String(v);
    }

    function extractTradeDetailData(data) {
        if (!data) return null;

        if (data.trade) {
            return data.trade;
        }

        if (data.data) {
            return data.data;
        }

        return data;
    }

    function parseTradeItems(data) {
        const output = [];

        if (!data || !Array.isArray(data.items)) {
            return output;
        }

        for (const entry of data.items) {
            if (
                !entry ||
                entry.type !== 'Item' ||
                !entry.details
            ) {
                continue;
            }

            const id = Number(
                entry.details.id
            );

            const quantity = Number(
                entry.details.amount
            );

            if (
                !Number.isFinite(id) ||
                id <= 0 ||
                !Number.isFinite(quantity) ||
                quantity <= 0
            ) {
                continue;
            }

            output.push({
                id,
                uid: entry.details.uid ?? null,
                quantity,
                userId:
                    Number(entry.user_id) || 0,
                name:
                    catalogMap.get(id)?.name ||
                    `Item #${id}`
            });
        }

        return output;
    }

    function parseTradeMoney(data) {
        const output = [];

        if (!data || !Array.isArray(data.items)) {
            return output;
        }

        for (const entry of data.items) {
            if (
                !entry ||
                entry.type !== 'Money' ||
                !entry.details
            ) {
                continue;
            }

            const amount = Number(
                entry.details.amount
            );

            if (
                !Number.isFinite(amount) ||
                amount <= 0
            ) {
                continue;
            }

            output.push({
                amount,
                userId:
                    Number(entry.user_id) || 0
            });
        }

        return output;
    }

    function makeTradeRecord(summary) {
        const id = tradeId(summary);

        if (!id) return null;

        const timestamp =
            tradeTimestamp(summary);

        const trader = summary?.trader;

        return {
            id,
            timestamp,
            dateText: formatDate(timestamp),
            player: tradePlayer(summary),
            playerId:
                Number(trader?.id) || 0,
            selfUserId:
                Number(summary?.user?.id) || 0,
            status: 'summary',
            summary:
                compactTradeObject(summary),
            detail: null,
            items: [],
            money: [],
            loaded: false,
            parserVersion:
                TRADE_PARSER_VERSION
        };
    }

    function tradeKey(t) {
        return String(t.id);
    }

    function importTrades(
        trades,
        existing
    ) {
        let imported = 0;

        for (const raw of trades) {
            const trade =
                makeTradeRecord(raw);

            if (
                !trade ||
                existing.has(trade.id)
            ) {
                continue;
            }

            existing.add(trade.id);

            state.trades.push(trade);
            imported++;
        }

        state.trades.sort(
            (a, b) =>
                Number(b.timestamp || 0) -
                Number(a.timestamp || 0)
        );

        return imported;
    }

    function tradeNeedsDetail(trade) {
        return Boolean(
            trade &&
            (
                !trade.loaded ||
                Number(trade.parserVersion) !==
                    TRADE_PARSER_VERSION
            )
        );
    }

    function countTradesNeedingDetail() {
        return state.trades.filter(
            tradeNeedsDetail
        ).length;
    }

    async function syncTrades() {
        if (
            tradeSyncing ||
            tradeHistorySyncing
        ) {
            return;
        }

        tradeSyncing = true;

        try {
            setStatus(
                'Getting completed trades...'
            );

            const trades = extractTrades(
                await getTrades()
            );

            const imported = importTrades(
                trades,
                new Set(
                    state.trades.map(tradeKey)
                )
            );

            saveState();
            render();

            setStatus(
                imported
                    ? `Imported ${imported} trade${imported === 1 ? '' : 's'}`
                    : `Checked ${trades.length} trades — already saved`
            );

            setTimeout(
                autoLoadTradeDetails,
                250
            );
        } catch (e) {
            console.error(
                '[TPL8] Trade sync',
                e
            );

            setStatus(
                'Trade sync error: ' +
                e.message
            );
        } finally {
            tradeSyncing = false;
        }
    }

    async function syncHistoricalTrades() {
        if (
            tradeHistorySyncing ||
            tradeSyncing
        ) {
            return;
        }

        tradeHistorySyncing = true;

        try {
            setStatus(
                'Starting unlimited trade history...'
            );

            const existing = new Set(
                state.trades.map(tradeKey)
            );

            let data = await getTrades();
            let previousOldest = null;
            let page = 0;
            let total = 0;

            while (true) {
                page++;

                const trades =
                    extractTrades(data);

                if (!trades.length) break;

                total += importTrades(
                    trades,
                    existing
                );

                saveState();
                render();

                let oldest = null;

                for (const trade of trades) {
                    const timestamp =
                        tradeTimestamp(trade);

                    if (
                        timestamp > 0 &&
                        (
                            oldest === null ||
                            timestamp < oldest
                        )
                    ) {
                        oldest = timestamp;
                    }
                }

                if (
                    oldest === null ||
                    (
                        previousOldest !== null &&
                        oldest >= previousOldest
                    )
                ) {
                    break;
                }

                previousOldest = oldest;

                setStatus(
                    `Trade history: page ${page} — ${total} new`
                );

                await sleep(
                    HISTORY_PAGE_DELAY
                );

                data = await getTrades(oldest);
            }

            saveState();
            render();

            setStatus(
                `Trade history finished — ${total} new trades`
            );

            setTimeout(
                autoLoadTradeDetails,
                250
            );
        } catch (e) {
            console.error(
                '[TPL8] Trade history',
                e
            );

            setStatus(
                'Trade history error: ' +
                e.message
            );
        } finally {
            tradeHistorySyncing = false;
        }
    }

    async function autoLoadTradeDetails() {
        if (tradeDetailAutoLoading) {
            return;
        }

        const pending =
            state.trades
                .filter(tradeNeedsDetail)
                .map(t => String(t.id));

        if (!pending.length) {
            return;
        }

        tradeDetailAutoLoading = true;

        let loaded = 0;
        let failed = 0;

        try {
            setStatus(
                `Loading trade contents: 0 / ${pending.length}`
            );

            for (
                let i = 0;
                i < pending.length;
                i++
            ) {
                const id = pending[i];

                const trade =
                    state.trades.find(
                        t => String(t.id) === id
                    );

                if (
                    !trade ||
                    !tradeNeedsDetail(trade)
                ) {
                    continue;
                }

                setStatus(
                    `Loading trade contents: ${i + 1} / ${pending.length}`
                );

                if (
                    await loadTradeDetail(
                        id,
                        true
                    )
                ) {
                    loaded++;
                } else {
                    failed++;
                }

                if (
                    i < pending.length - 1
                ) {
                    await sleep(
                        TRADE_DETAIL_DELAY
                    );
                }
            }

            saveState();
            render();

            const remaining =
                countTradesNeedingDetail();

            setStatus(
                failed
                    ? `Trade detail loading finished — ${loaded} loaded, ${failed} failed, ${remaining} remaining`
                    : `Trade detail loading finished — ${loaded} loaded, ${remaining} remaining`
            );
        } finally {
            tradeDetailAutoLoading = false;

            if (
                countTradesNeedingDetail() > 0
            ) {
                setTimeout(
                    autoLoadTradeDetails,
                    1000
                );
            }
        }
    }

    async function loadTradeDetail(
        id,
        automatic = false
    ) {
        const trade =
            state.trades.find(
                t => String(t.id) === String(id)
            );

        if (!trade) return false;

        if (
            trade.loaded &&
            Number(trade.parserVersion) ===
                TRADE_PARSER_VERSION
        ) {
            return true;
        }

        if (!automatic) {
            setStatus(
                'Loading trade contents...'
            );
        }

        try {
            const data =
                extractTradeDetailData(
                    await api(
                        `/user/${encodeURIComponent(id)}/trade`,
                        {},
                        20000
                    )
                );

            if (
                !data ||
                typeof data !== 'object'
            ) {
                throw new Error(
                    'Trade detail returned no usable data'
                );
            }

            trade.detail =
                compactTradeObject(data);

            if (
                data.user &&
                typeof data.user === 'object'
            ) {
                trade.selfUserId =
                    Number(data.user.id) || 0;
            }

            if (
                data.trader &&
                typeof data.trader === 'object'
            ) {
                trade.playerId =
                    Number(data.trader.id) || 0;

                if (data.trader.name) {
                    trade.player =
                        String(data.trader.name);
                }
            }

            if (data.completed_at != null) {
                trade.timestamp =
                    Number(data.completed_at) ||
                    trade.timestamp;

                trade.dateText =
                    formatDate(
                        trade.timestamp
                    );
            }

            trade.items =
                parseTradeItems(data);

            trade.money =
                parseTradeMoney(data);

            trade.loaded = true;
            trade.parserVersion =
                TRADE_PARSER_VERSION;

            saveState();
            render();

            if (!automatic) {
                setStatus(
                    'Trade contents loaded'
                );
            }

            return true;
        } catch (e) {
            console.error(
                '[TPL8] Trade detail',
                e
            );

            if (!automatic) {
                setStatus(
                    'Trade detail error: ' +
                    e.message
                );
            }

            return false;
        }
    }

    /* =====================================================
       TRADE ACCOUNTING
    ===================================================== */

    function tradeSides(trade) {
        const items =
            Array.isArray(trade.items)
                ? trade.items
                : [];

        const moneyItems =
            Array.isArray(trade.money)
                ? trade.money
                : [];

        const self =
            Number(trade.selfUserId) || 0;

        if (!self) return null;

        const givenItems =
            items.filter(
                item =>
                    Number(item.userId) === self
            );

        const receivedItems =
            items.filter(
                item =>
                    Number(item.userId) !== self
            );

        const givenCash =
            moneyItems
                .filter(
                    item =>
                        Number(item.userId) === self
                )
                .reduce(
                    (sum, item) =>
                        sum +
                        Number(item.amount || 0),
                    0
                );

        const receivedCash =
            moneyItems
                .filter(
                    item =>
                        Number(item.userId) !== self
                )
                .reduce(
                    (sum, item) =>
                        sum +
                        Number(item.amount || 0),
                    0
                );

        return {
            givenItems,
            receivedItems,
            givenCash,
            receivedCash
        };
    }

    function tradeItemUnitValue(item) {
        const live =
            prices[Number(item.id)];

        const tmv =
            Number(live?.tmv);

        if (
            Number.isFinite(tmv) &&
            tmv > 0
        ) {
            return tmv;
        }

        return (
            Number(
                catalogMap.get(
                    Number(item.id)
                )?.market_value
            ) ||
            lastKnownTmv(item.id) ||
            0
        );
    }

    function tradeItemTotalValue(item) {
        return (
            Number(item.quantity) || 0
        ) * tradeItemUnitValue(item);
    }

    function sumTradeItemValue(items) {
        return items.reduce(
            (sum, item) =>
                sum +
                tradeItemTotalValue(item),
            0
        );
    }

    function tradeItemName(id) {
        return (
            catalogMap.get(Number(id))?.name ||
            `Item #${id}`
        );
    }

    function allocateTradeCost(
        items,
        totalCost
    ) {
        const output = [];

        if (
            !items.length ||
            !Number.isFinite(totalCost)
        ) {
            return output;
        }

        const values =
            items.map(tradeItemTotalValue);

        const totalValue =
            values.reduce(
                (sum, value) =>
                    sum + value,
                0
            );

        const totalQuantity =
            items.reduce(
                (sum, item) =>
                    sum +
                    Number(item.quantity || 0),
                0
            );

        for (
            let i = 0;
            i < items.length;
            i++
        ) {
            const item = items[i];

            const quantity =
                Number(item.quantity) || 0;

            if (quantity <= 0) continue;

            let allocated;

            if (totalValue > 0) {
                allocated =
                    totalCost *
                    (
                        values[i] /
                        totalValue
                    );
            } else if (totalQuantity > 0) {
                allocated =
                    totalCost *
                    (
                        quantity /
                        totalQuantity
                    );
            } else {
                allocated = 0;
            }

            output.push({
                item,
                totalCost: allocated,
                unitCost:
                    allocated / quantity
            });
        }

        return output;
    }

    function buildTradeAccounting() {
        const acquisitions = [];
        const dispositions = [];

        let loadedTrades = 0;
        let ignoredTrades = 0;

        for (const trade of state.trades) {
            if (
                !trade.loaded ||
                Number(trade.parserVersion) !==
                    TRADE_PARSER_VERSION
            ) {
                ignoredTrades++;
                continue;
            }

            const sides =
                tradeSides(trade);

            if (!sides) {
                ignoredTrades++;
                continue;
            }

            loadedTrades++;

            const {
                givenItems,
                receivedItems,
                givenCash,
                receivedCash
            } = sides;

            const givenValue =
                sumTradeItemValue(
                    givenItems
                );

            const receivedValue =
                sumTradeItemValue(
                    receivedItems
                );

            const outflow =
                givenCash +
                givenValue;

            const inflow =
                receivedCash +
                receivedValue;

            if (receivedItems.length) {
                for (
                    const allocation of
                    allocateTradeCost(
                        receivedItems,
                        Math.max(
                            0,
                            Number.isFinite(outflow)
                                ? outflow *
                                  (
                                      receivedCash > 0 &&
                                      receivedValue + receivedCash > 0
                                          ? receivedValue /
                                            (receivedValue + receivedCash)
                                          : 1
                                  )
                                : 0
                        )
                    )
                ) {
                    const item =
                        allocation.item;

                    const exact =
                        givenItems.length === 0 &&
                        receivedCash === 0 &&
                        givenCash > 0;

                    acquisitions.push({
                        tradeId:
                            String(trade.id),
                        timestamp:
                            Number(trade.timestamp) ||
                            0,
                        dateText:
                            trade.dateText ||
                            formatDate(
                                trade.timestamp
                            ),
                        itemId:
                            Number(item.id),
                        itemName:
                            tradeItemName(
                                item.id
                            ),
                        quantity:
                            Number(item.quantity),
                        unitPrice:
                            allocation.unitCost,
                        total:
                            allocation.totalCost,
                        player:
                            trade.player ||
                            'Unknown player',
                        exact,
                        estimated: !exact,
                        valuation:
                            exact
                                ? 'Exact cash purchase'
                                : 'Estimated from trade values'
                    });
                }
            }

            if (givenItems.length) {
                for (
                    const allocation of
                    allocateTradeCost(
                        givenItems,
                        Math.max(
                            0,
                            Number.isFinite(inflow)
                                ? inflow *
                                  (
                                      givenCash > 0 &&
                                      givenValue + givenCash > 0
                                          ? givenValue /
                                            (givenValue + givenCash)
                                          : 1
                                  )
                                : 0
                        )
                    )
                ) {
                    const item =
                        allocation.item;

                    const exact =
                        receivedItems.length === 0 &&
                        receivedCash > 0 &&
                        givenCash === 0;

                    dispositions.push({
                        tradeId:
                            String(trade.id),
                        timestamp:
                            Number(trade.timestamp) ||
                            0,
                        dateText:
                            trade.dateText ||
                            formatDate(
                                trade.timestamp
                            ),
                        itemId:
                            Number(item.id),
                        itemName:
                            tradeItemName(
                                item.id
                            ),
                        quantity:
                            Number(item.quantity),
                        total:
                            allocation.totalCost,
                        unitPrice:
                            allocation.unitCost,
                        player:
                            trade.player ||
                            'Unknown player',
                        exact,
                        estimated: !exact,
                        valuation:
                            exact
                                ? 'Exact cash sale'
                                : 'Estimated from trade values',
                        fee: 0,
                        buyer:
                            trade.player ||
                            'Unknown player',
                        market: 'Player Trade'
                    });
                }
            }
        }

        return {
            acquisitions,
            dispositions,
            loadedTrades,
            ignoredTrades
        };
    }

    /* =====================================================
       FIFO
    ===================================================== */

    function calculateFifoPnl(tracked) {
        const itemName =
            norm(tracked.name);

        const purchases =
            state.purchases
                .filter(
                    p =>
                        norm(p.itemName) ===
                        itemName
                )
                .map(p => ({
                    ...p,
                    source: 'Market/Bazaar',
                    exact: true,
                    estimated: false,
                    quantity:
                        Number(p.quantity),
                    unitPrice:
                        Number(p.unitPrice),
                    timestamp:
                        Number(p.timestamp)
                }))
                .filter(
                    p =>
                        p.quantity > 0 &&
                        Number.isFinite(p.unitPrice) &&
                        p.unitPrice >= 0
                );

        const tradeAccounting =
            buildTradeAccounting();

        const tradePurchases =
            tradeAccounting.acquisitions
                .filter(
                    p =>
                        norm(p.itemName) ===
                        itemName
                )
                .map(p => ({
                    ...p,
                    source: 'Player Trade',
                    quantity:
                        Number(p.quantity),
                    unitPrice:
                        Number(p.unitPrice),
                    timestamp:
                        Number(p.timestamp)
                }))
                .filter(
                    p =>
                        p.quantity > 0 &&
                        Number.isFinite(p.unitPrice) &&
                        p.unitPrice >= 0
                );

        const giftBasis = giftBasisMode();

        const giftPurchases =
            state.itemReceives
                .filter(
                    r =>
                        norm(r.itemName) ===
                        itemName
                )
                .map(r => {
                    const frozen = Number(r.tmvAtReceive);
                    const unit =
                        giftBasis === 'zero'
                            ? 0
                            : (
                                Number.isFinite(frozen) && frozen > 0
                                    ? frozen
                                    : currentTmvFor(r.itemId)
                            );

                    return {
                        logId: r.logId,
                        giftKey: itemReceiveKey(r),
                        timestamp: Number(r.timestamp),
                        dateText: r.dateText,
                        itemId: r.itemId,
                        itemName: r.itemName,
                        quantity: Number(r.quantity),
                        unitPrice: unit,
                        seller: r.sender || 'Gift',
                        source: 'Gift',
                        exact: false,
                        estimated: giftBasis !== 'zero',
                        valuation:
                            giftBasis === 'zero'
                                ? 'Gift at $0 basis'
                                : 'Gift at TMV when received'
                    };
                })
                .filter(
                    p =>
                        p.quantity > 0 &&
                        Number.isFinite(p.unitPrice) &&
                        p.unitPrice >= 0
                );

        const parcelLots =
            state.parcelOpens
                .filter(
                    o =>
                        norm(o.itemName) ===
                        itemName
                )
                .map(o => {
                    const frozen = Number(o.tmvAtReceive);
                    const unit =
                        giftBasis === 'zero'
                            ? 0
                            : (
                                Number.isFinite(frozen) && frozen > 0
                                    ? frozen
                                    : currentTmvFor(o.itemId)
                            );

                    return {
                        logId: o.logId,
                        timestamp: Number(o.timestamp),
                        dateText: o.dateText,
                        itemId: o.itemId,
                        itemName: o.itemName,
                        quantity: Number(o.quantity),
                        unitPrice: unit,
                        seller: o.container || 'Parcel',
                        source: 'Parcel',
                        exact: false,
                        estimated: giftBasis !== 'zero',
                        valuation:
                            giftBasis === 'zero'
                                ? 'Opened parcel at $0 basis'
                                : 'Opened parcel at TMV when received'
                    };
                })
                .filter(
                    p =>
                        p.quantity > 0 &&
                        Number.isFinite(p.unitPrice) &&
                        p.unitPrice >= 0
                );

        const travelLots =
            state.travelPurchases
                .filter(
                    t =>
                        norm(t.itemName) ===
                        itemName
                )
                .map(t => ({
                    logId: t.logId,
                    timestamp: Number(t.timestamp),
                    dateText: t.dateText,
                    itemId: t.itemId,
                    itemName: t.itemName,
                    quantity: Number(t.quantity),
                    unitPrice: Number(t.unitPrice),
                    seller: t.destination || 'Travel',
                    source: 'Travel',
                    exact: true,
                    estimated: false,
                    valuation: 'Exact travel purchase'
                }))
                .filter(
                    p =>
                        p.quantity > 0 &&
                        Number.isFinite(p.unitPrice) &&
                        p.unitPrice > 0
                );

        const sells =
            state.sells
                .filter(
                    s =>
                        norm(s.itemName) ===
                        itemName
                )
                .map(s => ({
                    ...s,
                    source: 'Market/Bazaar',
                    exact: true,
                    estimated: false,
                    quantity:
                        Number(s.quantity),
                    total:
                        Number(s.total),
                    fee:
                        Number(s.fee) || 0,
                    timestamp:
                        Number(s.timestamp)
                }))
                .filter(
                    s =>
                        s.quantity > 0 &&
                        Number.isFinite(s.total) &&
                        s.total >= 0
                );

        const tradeSells =
            tradeAccounting.dispositions
                .filter(
                    s =>
                        norm(s.itemName) ===
                        itemName
                )
                .map(s => ({
                    ...s,
                    source: 'Player Trade',
                    quantity:
                        Number(s.quantity),
                    total:
                        Number(s.total),
                    fee: 0,
                    timestamp:
                        Number(s.timestamp)
                }))
                .filter(
                    s =>
                        s.quantity > 0 &&
                        Number.isFinite(s.total) &&
                        s.total >= 0
                );

        const events = [];

        for (const purchase of purchases) {
            events.push({
                type: 'purchase',
                timestamp:
                    purchase.timestamp || 0,
                id:
                    'market-' +
                    String(purchase.logId),
                data: purchase
            });
        }

        for (const purchase of tradePurchases) {
            events.push({
                type: 'purchase',
                timestamp:
                    purchase.timestamp || 0,
                id:
                    'trade-buy-' +
                    String(purchase.tradeId) +
                    '-' +
                    String(purchase.itemId),
                data: purchase
            });
        }

        for (const gift of giftPurchases) {
            events.push({
                type: 'purchase',
                timestamp: gift.timestamp || 0,
                id:
                    'gift-' +
                    String(gift.giftKey),
                data: gift
            });
        }

        for (const parcel of parcelLots) {
            events.push({
                type: 'purchase',
                timestamp: parcel.timestamp || 0,
                id:
                    'parcel-' +
                    String(parcel.logId) +
                    '-' +
                    String(parcel.itemId) +
                    '-' +
                    String(parcel.quantity) +
                    '-' +
                    String(parcel.timestamp),
                data: parcel
            });
        }

        for (const travel of travelLots) {
            events.push({
                type: 'purchase',
                timestamp: travel.timestamp || 0,
                id:
                    'travel-' +
                    String(travel.logId) +
                    '-' +
                    String(travel.itemId) +
                    '-' +
                    String(travel.timestamp),
                data: travel
            });
        }

        for (const send of state.itemSends) {
            if (norm(send.itemName) !== itemName) continue;

            events.push({
                type: 'use',
                timestamp: send.timestamp || 0,
                id:
                    'send-' +
                    String(send.logId) +
                    '-' +
                    String(send.itemId) +
                    '-' +
                    String(send.timestamp),
                data: { ...send, kind: 'send' }
            });
        }

        for (const use of state.itemUses) {
            if (norm(use.itemName) !== itemName) continue;

            events.push({
                type: 'use',
                timestamp: use.timestamp || 0,
                id:
                    'use-' +
                    String(use.logId) +
                    '-' +
                    String(use.timestamp),
                data: use
            });
        }

        for (const sale of sells) {
            events.push({
                type: 'sell',
                timestamp:
                    sale.timestamp || 0,
                id:
                    'market-' +
                    String(sale.logId),
                data: sale
            });
        }

        for (const sale of tradeSells) {
            events.push({
                type: 'sell',
                timestamp:
                    sale.timestamp || 0,
                id:
                    'trade-sell-' +
                    String(sale.tradeId) +
                    '-' +
                    String(sale.itemId),
                data: sale
            });
        }

        events.sort((a, b) => {
            const difference =
                a.timestamp - b.timestamp;

            if (difference !== 0) {
                return difference;
            }

            if (a.type === b.type) {
                return a.id.localeCompare(b.id);
            }

            return a.type === 'purchase'
                ? -1
                : 1;
        });

        const lots = [];

        let totalPurchased = 0;
        let totalPurchaseCost = 0;
        let marketPurchased = 0;
        let tradePurchased = 0;
        let tradePurchaseCost = 0;
        let estimatedTradePurchases = 0;
        let giftPurchased = 0;
        let giftValue = 0;
        let travelPurchased = 0;
        let travelPurchaseCost = 0;
        let parcelPurchased = 0;
        let parcelValue = 0;

        let totalSold = 0;
        let totalSaleRevenue = 0;
        let totalFees = 0;
        let marketSold = 0;
        let tradeSold = 0;
        let tradeSaleRevenue = 0;
        let estimatedTradeSales = 0;

        let matchedSold = 0;
        let matchedRevenue = 0;
        let fifoCost = 0;

        let unmatchedSold = 0;
        let unmatchedRevenue = 0;
        let consumedQty = 0;
        let consumedCost = 0;
        let unmatchedUse = 0;
        let consumedOverdose = 0;
        let armoryQty = 0;
        let sentQty = 0;
        let sentCost = 0;

        const saleMatches = [];

        for (const event of events) {
            if (event.type === 'purchase') {
                const purchase =
                    event.data;

                lots.push({
                    quantity:
                        purchase.quantity,
                    unitPrice:
                        purchase.unitPrice,
                    timestamp:
                        purchase.timestamp,
                    dateText:
                        purchase.dateText,
                    logId:
                        purchase.logId ||
                        purchase.tradeId,
                    seller:
                        purchase.seller ||
                        purchase.player ||
                        'Player Trade',
                    source:
                        purchase.source,
                    estimated:
                        Boolean(
                            purchase.estimated
                        ),
                    valuation:
                        purchase.valuation || ''
                });

                totalPurchased +=
                    purchase.quantity;

                totalPurchaseCost +=
                    purchase.quantity *
                    purchase.unitPrice;

                if (
                    purchase.source ===
                    'Player Trade'
                ) {
                    tradePurchased +=
                        purchase.quantity;

                    tradePurchaseCost +=
                        purchase.quantity *
                        purchase.unitPrice;

                    if (purchase.estimated) {
                        estimatedTradePurchases +=
                            purchase.quantity;
                    }
                } else if (purchase.source === 'Gift') {
                    giftPurchased +=
                        purchase.quantity;

                    giftValue +=
                        purchase.quantity *
                        purchase.unitPrice;
                } else if (purchase.source === 'Parcel') {
                    parcelPurchased +=
                        purchase.quantity;

                    parcelValue +=
                        purchase.quantity *
                        purchase.unitPrice;
                } else if (purchase.source === 'Travel') {
                    travelPurchased +=
                        purchase.quantity;

                    travelPurchaseCost +=
                        purchase.quantity *
                        purchase.unitPrice;
                } else {
                    marketPurchased +=
                        purchase.quantity;
                }

                continue;
            }

            if (event.type === 'use') {
                const kind = event.data.kind || 'use';
                let need = Number(event.data.quantity) || 0;
                const qtyTotal = need;

                /* Used straight from a faction armory: never in personal stock. */
                if (event.data.armory) {
                    armoryQty += qtyTotal;
                    continue;
                }

                let cost = 0;

                while (need > 0 && lots.length > 0) {
                    const lot = lots[0];
                    const used = Math.min(need, lot.quantity);

                    cost += used * lot.unitPrice;

                    lot.quantity -= used;
                    need -= used;

                    if (lot.quantity <= 0) {
                        lots.shift();
                    }
                }

                if (kind === 'send') {
                    sentQty += qtyTotal;
                    sentCost += cost;
                } else {
                    consumedQty += qtyTotal;
                    consumedCost += cost;

                    if (kind === 'overdose') {
                        consumedOverdose += qtyTotal;
                    }
                }

                unmatchedUse += Math.max(0, need);
                continue;
            }

            const sale = event.data;

            let remaining =
                sale.quantity;

            const saleRevenue =
                Number(sale.total) || 0;

            totalSold += sale.quantity;
            totalSaleRevenue +=
                saleRevenue;

            totalFees +=
                Number(sale.fee) || 0;

            if (
                sale.source ===
                'Player Trade'
            ) {
                tradeSold +=
                    sale.quantity;

                tradeSaleRevenue +=
                    saleRevenue;

                if (sale.estimated) {
                    estimatedTradeSales +=
                        sale.quantity;
                }
            } else {
                marketSold +=
                    sale.quantity;
            }

            const inventoryBeforeSale =
                lots.reduce(
                    (sum, lot) =>
                        sum +
                        Number(
                            lot.quantity || 0
                        ),
                    0
                );

            let matchedQuantity = 0;
            let saleCost = 0;

            const matchedLots = [];

            while (
                remaining > 0 &&
                lots.length > 0
            ) {
                const lot = lots[0];

                const used =
                    Math.min(
                        remaining,
                        lot.quantity
                    );

                saleCost +=
                    used *
                    lot.unitPrice;

                matchedQuantity += used;

                matchedLots.push({
                    quantity: used,
                    unitPrice:
                        lot.unitPrice,
                    source:
                        lot.source,
                    estimated:
                        lot.estimated
                });

                lot.quantity -= used;
                remaining -= used;

                if (lot.quantity <= 0) {
                    lots.shift();
                }
            }

            const inventoryAfterSale =
                lots.reduce(
                    (sum, lot) =>
                        sum +
                        Number(
                            lot.quantity || 0
                        ),
                    0
                );

            const netUnitRevenue =
                sale.quantity > 0
                    ? saleRevenue /
                      sale.quantity
                    : 0;

            const saleMatchedRevenue =
                matchedQuantity *
                netUnitRevenue;

            const saleUnmatchedQuantity =
                Math.max(
                    0,
                    remaining
                );

            const saleUnmatchedRevenue =
                saleUnmatchedQuantity *
                netUnitRevenue;

            matchedSold +=
                matchedQuantity;

            matchedRevenue +=
                saleMatchedRevenue;

            fifoCost += saleCost;

            unmatchedSold +=
                saleUnmatchedQuantity;

            unmatchedRevenue +=
                saleUnmatchedRevenue;

            saleMatches.push({
                sell: sale,
                matchedQuantity,
                unmatchedQuantity:
                    saleUnmatchedQuantity,
                revenue:
                    saleMatchedRevenue,
                unmatchedRevenue:
                    saleUnmatchedRevenue,
                fifoCost:
                    saleCost,
                pnl:
                    saleMatchedRevenue -
                    saleCost,
                matchedLots,
                inventoryBeforeSale,
                inventoryAfterSale
            });
        }

        let remainingQuantity = 0;
        let remainingCost = 0;
        let remainingMarketQuantity = 0;
        let remainingTradeQuantity = 0;
        let remainingTradeCost = 0;

        for (const lot of lots) {
            remainingQuantity +=
                lot.quantity;

            remainingCost +=
                lot.quantity *
                lot.unitPrice;

            if (
                lot.source ===
                'Player Trade'
            ) {
                remainingTradeQuantity +=
                    lot.quantity;

                remainingTradeCost +=
                    lot.quantity *
                    lot.unitPrice;
            } else {
                remainingMarketQuantity +=
                    lot.quantity;
            }
        }

        const realizedPnl =
            matchedRevenue -
            fifoCost -
            (useMode() === 'cost' ? consumedCost + sentCost : 0);

        const item =
            catalogMap.get(
                Number(tracked.id)
            );

        const price =
            prices[tracked.id];

        const tmv =
            Number(price?.tmv) ||
            Number(item?.market_value) ||
            lastKnownTmv(tracked.id) ||
            0;

        const tmvMissing =
            !(tmv > 0) && remainingQuantity > 0;

        const currentValue =
            remainingQuantity *
            tmv;

        const unrealizedPnl =
            currentValue -
            remainingCost;

        const totalPnl =
            realizedPnl +
            unrealizedPnl;

        return {
            itemName: tracked.name,

            totalPurchased,
            totalPurchaseCost,
            marketPurchased,
            tradePurchased,
            tradePurchaseCost,
            estimatedTradePurchases,
            giftPurchased,
            giftValue,
            travelPurchased,
            travelPurchaseCost,
            parcelPurchased,
            parcelValue,
            consumedQty,
            consumedCost,
            unmatchedUse,
            consumedOverdose,
            armoryQty,
            sentQty,
            sentCost,

            totalSold,
            totalSaleRevenue,
            totalFees,
            marketSold,
            tradeSold,
            tradeSaleRevenue,
            estimatedTradeSales,

            matchedSold,
            matchedRevenue,
            fifoCost,

            unmatchedSold,
            unmatchedRevenue,

            remainingQuantity,
            remainingCost,
            remainingMarketQuantity,
            remainingTradeQuantity,
            remainingTradeCost,

            tmv,
            currentValue,
            tmvMissing,

            realizedPnl,
            unrealizedPnl,
            totalPnl,

            complete:
                unmatchedSold <= 0,

            saleMatches,

            loadedTrades:
                tradeAccounting.loadedTrades,

            ignoredTrades:
                tradeAccounting.ignoredTrades
        };
    }

    /* =====================================================
       DIAGNOSTICS
    ===================================================== */

    function buildDiagnosticTimeline(
        tracked
    ) {
        const itemName =
            norm(tracked.name);

        const accounting =
            buildTradeAccounting();

        const events = [];

        for (
            const purchase of
            state.purchases.filter(
                x =>
                    norm(x.itemName) ===
                    itemName
            )
        ) {
            events.push({
                type: 'purchase',
                timestamp:
                    Number(
                        purchase.timestamp
                    ) || 0,
                quantity:
                    Number(
                        purchase.quantity
                    ) || 0,
                unitPrice:
                    Number(
                        purchase.unitPrice
                    ) || 0,
                source:
                    'Market/Bazaar',
                id:
                    purchase.logId || '?',
                seller:
                    purchase.seller ||
                    'Unknown'
            });
        }

        for (
            const purchase of
            accounting.acquisitions.filter(
                x =>
                    norm(x.itemName) ===
                    itemName
            )
        ) {
            events.push({
                type: 'purchase',
                timestamp:
                    Number(
                        purchase.timestamp
                    ) || 0,
                quantity:
                    Number(
                        purchase.quantity
                    ) || 0,
                unitPrice:
                    Number(
                        purchase.unitPrice
                    ) || 0,
                source:
                    'Player Trade',
                id:
                    purchase.tradeId || '?',
                seller:
                    purchase.player ||
                    'Unknown',
                estimated:
                    Boolean(
                        purchase.estimated
                    )
            });
        }

        for (
            const sale of
            state.sells.filter(
                x =>
                    norm(x.itemName) ===
                    itemName
            )
        ) {
            events.push({
                type: 'sell',
                timestamp:
                    Number(
                        sale.timestamp
                    ) || 0,
                quantity:
                    Number(
                        sale.quantity
                    ) || 0,
                total:
                    Number(
                        sale.total
                    ) || 0,
                source:
                    sale.market ||
                    'Market/Bazaar',
                id:
                    sale.logId || '?',
                buyer:
                    sale.buyer ||
                    'Unknown',
                fee:
                    Number(sale.fee) || 0
            });
        }

        for (
            const sale of
            accounting.dispositions.filter(
                x =>
                    norm(x.itemName) ===
                    itemName
            )
        ) {
            events.push({
                type: 'sell',
                timestamp:
                    Number(
                        sale.timestamp
                    ) || 0,
                quantity:
                    Number(
                        sale.quantity
                    ) || 0,
                total:
                    Number(
                        sale.total
                    ) || 0,
                source:
                    'Player Trade',
                id:
                    sale.tradeId || '?',
                buyer:
                    sale.player ||
                    'Unknown',
                fee: 0,
                estimated:
                    Boolean(
                        sale.estimated
                    )
            });
        }

        for (const r of state.itemReceives) {
            if (norm(r.itemName) !== itemName) continue;

            events.push({
                type: 'purchase',
                timestamp: Number(r.timestamp) || 0,
                quantity: Number(r.quantity) || 0,
                unitPrice: Number(r.tmvAtReceive) || 0,
                source: 'Gift',
                id: r.logId || '?',
                seller: r.sender || 'Gift'
            });
        }

        for (const o of state.parcelOpens) {
            if (norm(o.itemName) !== itemName) continue;

            events.push({
                type: 'purchase',
                timestamp: Number(o.timestamp) || 0,
                quantity: Number(o.quantity) || 0,
                unitPrice: Number(o.tmvAtReceive) || 0,
                source: 'Parcel',
                id: o.logId || '?',
                seller: o.container || 'Parcel'
            });
        }

        for (const t of state.travelPurchases) {
            if (norm(t.itemName) !== itemName) continue;

            events.push({
                type: 'purchase',
                timestamp: Number(t.timestamp) || 0,
                quantity: Number(t.quantity) || 0,
                unitPrice: Number(t.unitPrice) || 0,
                source: 'Travel',
                id: t.logId || '?',
                seller: t.destination || 'Travel'
            });
        }

        for (const sd of state.itemSends) {
            if (norm(sd.itemName) !== itemName) continue;

            events.push({
                type: 'sell',
                timestamp: Number(sd.timestamp) || 0,
                quantity: Number(sd.quantity) || 0,
                total: 0,
                source: 'Item send',
                id: sd.logId || '?',
                buyer: sd.recipient || 'Unknown',
                fee: 0
            });
        }

        for (const u of state.itemUses) {
            if (norm(u.itemName) !== itemName || u.armory) continue;

            events.push({
                type: 'sell',
                timestamp: Number(u.timestamp) || 0,
                quantity: Number(u.quantity) || 0,
                total: 0,
                source: u.kind === 'overdose' ? 'Overdose' : 'Item use',
                id: u.logId || '?',
                buyer: 'Used',
                fee: 0
            });
        }

        events.sort((a, b) => {
            const difference =
                a.timestamp -
                b.timestamp;

            if (difference !== 0) {
                return difference;
            }

            if (a.type === b.type) {
                return 0;
            }

            return a.type === 'purchase'
                ? -1
                : 1;
        });

        let inventory = 0;
        let inventoryCost = 0;

        let firstDeficit = null;
        const unmatched = [];

        for (const event of events) {
            if (event.type === 'purchase') {
                inventory +=
                    event.quantity;

                inventoryCost +=
                    event.quantity *
                    event.unitPrice;

                continue;
            }

            const beforeInventory =
                inventory;

            const unitRevenue =
                event.quantity > 0
                    ? event.total /
                      event.quantity
                    : 0;

            const matched =
                Math.min(
                    Math.max(
                        inventory,
                        0
                    ),
                    event.quantity
                );

            const unmatchedQuantity =
                event.quantity -
                matched;

            if (
                unmatchedQuantity > 0 &&
                !firstDeficit
            ) {
                firstDeficit = {
                    ...event,
                    beforeInventory,
                    matched,
                    unmatched:
                        unmatchedQuantity,
                    unmatchedRevenue:
                        unmatchedQuantity *
                        unitRevenue
                };
            }

            unmatched.push({
                event,
                beforeInventory,
                matched,
                unmatched:
                    unmatchedQuantity,
                unmatchedRevenue:
                    unmatchedQuantity *
                    unitRevenue
            });

            inventory -=
                event.quantity;

            if (inventory < 0) {
                inventory = 0;
            }
        }

        return {
            events,
            firstDeficit,
            unmatched,
            finalInventory:
                inventory,
            finalInventoryCost:
                inventoryCost
        };
    }

    function renderDiagnosticsPage(body) {
        if (!state.tracked.length) {
            body.innerHTML = `
                <div class="tpl8-empty">
                    🔎<br><br>
                    Track an item first.
                </div>
            `;
            return;
        }

        const results =
            state.tracked.map(tracked => ({
                tracked,
                pnl:
                    calculateFifoPnl(
                        tracked
                    ),
                diagnostics:
                    buildDiagnosticTimeline(
                        tracked
                    )
            }));

        const loaded =
            state.trades.filter(
                trade =>
                    trade.loaded &&
                    Number(
                        trade.parserVersion
                    ) ===
                        TRADE_PARSER_VERSION
            ).length;

        const pending =
            countTradesNeedingDetail();

        const totalUnmatchedRecords =
            results.reduce(
                (sum, result) =>
                    sum +
                    result.diagnostics.unmatched.filter(
                        x =>
                            x.unmatched > 0
                    ).length,
                0
            );

        const totalUnmatchedUnits =
            results.reduce(
                (sum, result) =>
                    sum +
                    result.pnl.unmatchedSold,
                0
            );

        const totalUnmatchedRevenue =
            results.reduce(
                (sum, result) =>
                    sum +
                    result.pnl.unmatchedRevenue,
                0
            );

        const totalReceiveRecords =
            state.itemReceives.length;

        const totalReceiveUnits =
            state.itemReceives.reduce(
                (sum, receive) =>
                    sum +
                    Number(
                        receive.quantity || 0
                    ),
                0
            );

        const totalTravelRecords =
            state.travelPurchases.length;

        const totalTravelUnits =
            state.travelPurchases.reduce(
                (sum, purchase) =>
                    sum + Number(purchase.quantity || 0),
                0
            );

        body.innerHTML = `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>🔎 Ledger Diagnostics</span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Tracked items
                    </span>
                    <span class="tpl8-value">
                        ${state.tracked.length}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Purchase records
                    </span>
                    <span class="tpl8-value">
                        ${state.purchases.length.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Sale records
                    </span>
                    <span class="tpl8-value">
                        ${state.sells.length.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Stored trades
                    </span>
                    <span class="tpl8-value">
                        ${state.trades.length.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Loaded trades
                    </span>
                    <span class="tpl8-value">
                        ${loaded.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Pending trade details
                    </span>
                    <span class="tpl8-value">
                        ${pending.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Item Receive records (tracked items)
                    </span>
                    <span class="tpl8-value">
                        ${totalReceiveRecords.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Item Receive units (tracked items)
                    </span>
                    <span class="tpl8-value">
                        ${totalReceiveUnits.toLocaleString()}
                    </span>
                </div>


                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Travel purchase records (allowed items)
                    </span>
                    <span class="tpl8-value">
                        ${totalTravelRecords.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Travel purchase units (allowed items)
                    </span>
                    <span class="tpl8-value">
                        ${totalTravelUnits.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Unmatched sale records
                    </span>
                    <span class="tpl8-value">
                        ${totalUnmatchedRecords.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Unmatched units
                    </span>
                    <span class="tpl8-value">
                        ${totalUnmatchedUnits.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Unmatched revenue
                    </span>
                    <span class="tpl8-value">
                        ${money(totalUnmatchedRevenue)}
                    </span>
                </div>

                <div class="tpl8-muted"
                     style="margin-top:8px;font-size:11px">
                    Diagnostics reconstruct the chronological
                    inventory separately. They do not change
                    FIFO accounting.
                </div>
            </div>

            ${results.map(result =>
                renderDiagnosticItem(
                    result.tracked,
                    result.pnl,
                    result.diagnostics
                )
            ).join('')}

            ${state.tracked.map(renderTradeAuditBox).join('')}
            ${renderTravelDebugBox()}
            ${renderParcelDebugBox()}
            ${renderUseDebugBox()}
            ${renderOverdoseDebugBox()}
            ${renderSendDebugBox()}
            ${renderAuditBox()}
        `;

        bindAuditControls(body);
    }

    const KNOWN_LOG_IDS = new Set(['1112','1113','1225','1226','4103','4201','4001','2290','2291','4102']);

    function auditMonthOptions() {
        const out = [];
        const now = new Date();
        let y = now.getFullYear();
        let m = now.getMonth() + 1;
        for (let i = 0; i < 26; i++) {
            out.push(y + '-' + String(m).padStart(2, '0'));
            m--;
            if (m === 0) { m = 12; y--; }
        }
        return out;
    }

    function renderAuditBox() {
        let diag = null;
        try { diag = JSON.parse(localStorage.getItem(AUDIT_KEY) || 'null'); } catch (_) {}

        const options = auditMonthOptions()
            .map(m => `<option value="${m}" ${diag && diag.month === m ? 'selected' : ''}>${m}</option>`)
            .join('');

        let result = '<div class="tpl8-muted">Pick a month and scan every log type that mentions a tracked item.</div>';

        if (diag) {
            const rows = (diag.rows || []).map(r => `
                <div class="tpl8-stat">
                    <span class="tpl8-label">${KNOWN_LOG_IDS.has(String(r.id)) ? '' : '\u2757 '}${esc(r.id)} ${esc(r.title)}</span>
                    <span class="tpl8-value">${Number(r.count).toLocaleString()}${r.units ? ' \u00b7 ' + Number(r.units).toLocaleString() + ' units' : ''}</span>
                </div>
                ${KNOWN_LOG_IDS.has(String(r.id)) ? '' : `<div class="tpl8-muted" style="word-break:break-all;font-size:11px">${esc(r.sample)}</div>`}
            `).join('');

            result = `
                <div class="tpl8-muted">${esc(diag.month)}: ${Number(diag.scanned || 0).toLocaleString()} logs scanned in ${Number(diag.pages || 0)} pages${diag.error ? ' \u00b7 stopped: ' + esc(diag.error) : ''}. \u2757 = log types the ledger does not read.</div>
                ${rows || '<div class="tpl8-muted">No log entries mention a tracked item.</div>'}
                <div class="tpl8-muted">Trades in these logs: ${Number(diag.tradesSeen || 0)} \u00b7 not in ledger: ${(diag.missingTrades || []).length ? esc((diag.missingTrades || []).join(', ')) : 'none'}</div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title"><span>\ud83d\udd75 Log audit (all log types)</span></div>
                <div style="display:flex;gap:8px;margin:8px 0">
                    <select id="tpl8-audit-month" class="tpl8-input" style="flex:1">${options}</select>
                    <button id="tpl8-audit-run" class="tpl8-btn">Scan</button>
                </div>
                ${result}
            </div>
        `;
    }

    function bindAuditControls(body) {
        const btn = body.querySelector('#tpl8-audit-run');
        const sel = body.querySelector('#tpl8-audit-month');
        if (!btn || !sel) return;
        btn.addEventListener('click', () => runLogAudit(sel.value));
    }

    async function runLogAudit(month) {
        if (auditRunning) return;
        auditRunning = true;

        const [yy, mm] = month.split('-').map(Number);
        const from = Math.floor(new Date(yy, mm - 1, 1).getTime() / 1000);
        const to = Math.floor(new Date(yy, mm, 1).getTime() / 1000) - 1;

        const ids = new Set();
        const names = state.tracked.map(t => norm(t.name));
        for (const [id, item] of catalogMap.entries()) {
            if (names.includes(norm(item?.name))) ids.add(String(id));
        }

        const idRe = ids.size
            ? new RegExp('"(?:item|item_id|itemId|drug|drug_id|id|items)":"?(?:' + [...ids].join('|') + ')"?[,}\\]]')
            : null;
        const nameRe = names.length
            ? new RegExp(names.map(n => n.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')).join('|'), 'i')
            : null;

        const tally = {};
        const tradeIdsSeen = {};
        let scanned = 0;
        let pages = 0;
        let error = '';
        let cursor = to;

        try {
            while (pages < 300) {
                pages++;
                setStatus(`Log audit ${month}: page ${pages}, ${scanned} logs`);
                const data = await api('/user', { selections: 'log', from, to: cursor }, 15000);
                const logs = extractLogs(data);
                if (!logs.length) break;

                let oldest = null;
                for (const log of logs) {
                    const e = log.data && typeof log.data === 'object' ? log.data : {};
                    const ts = Number(e.timestamp || 0);
                    if (ts > 0 && (oldest === null || ts < oldest)) oldest = ts;
                    if (ts && ts < from) continue;
                    scanned++;

                    const text = JSON.stringify({ d: e.data, p: e.params, t: e.details?.title });
                    if (!((idRe && idRe.test(text)) || (nameRe && nameRe.test(text)))) continue;

                    const lid = String(e.details?.id ?? '?');
                    const title = String(e.details?.title ?? '');
                    const key = lid + '|' + title;
                    const o = tally[key] || (tally[key] = { id: lid, title, count: 0, units: 0, sample: text.slice(0, 260) });
                    o.count++;

                    const walk = (v, depth) => {
                        if (!v || typeof v !== 'object' || depth > 5) return;
                        if (Array.isArray(v)) { v.forEach(x => walk(x, depth + 1)); return; }
                        if (ids.has(String(v.id)) && (v.qty != null || v.amount != null || v.quantity != null)) {
                            o.units += Number(v.qty ?? v.amount ?? v.quantity) || 0;
                        }
                        Object.values(v).forEach(x => walk(x, depth + 1));
                    };
                    walk(e.data, 0);

                    const tm = /trade\.php[^"]*?ID=(\d+)/i.exec(text) || /"trade_id":"?(\d+)/i.exec(text);
                    if (tm) tradeIdsSeen[tm[1]] = (tradeIdsSeen[tm[1]] || 0) + 1;
                }

                if (oldest === null || oldest <= from || oldest >= cursor) break;
                cursor = oldest;
                await sleep(HISTORY_PAGE_DELAY);
            }
        } catch (err) {
            error = String(err?.message || err).slice(0, 80);
        }

        const rows = Object.values(tally).sort((a, b) => {
            const ka = KNOWN_LOG_IDS.has(a.id) ? 1 : 0;
            const kb = KNOWN_LOG_IDS.has(b.id) ? 1 : 0;
            return ka - kb || b.count - a.count;
        });

        const known = new Set(state.trades.map(t => String(t.id)));
        const missingTrades = Object.keys(tradeIdsSeen).filter(id => !known.has(id));
        const tradesSeen = Object.keys(tradeIdsSeen).length;

        try {
            localStorage.setItem(AUDIT_KEY, JSON.stringify({ month, scanned, pages, error, rows, tradesSeen, missingTrades }));
        } catch (_) {}

        auditRunning = false;
        setStatus(`Log audit ${month} done: ${scanned} logs`);
        render();
    }

    function renderTradeAuditBox(tracked) {
        const name = norm(tracked.name);
        const accounting = buildTradeAccounting();

        const acquisitions = accounting.acquisitions
            .filter(a => norm(a.itemName) === name)
            .sort((a, b) => Number(b.total) - Number(a.total));

        const dispositions = accounting.dispositions
            .filter(d => norm(d.itemName) === name);

        const dispUnits = dispositions.reduce(
            (sum, d) => sum + Number(d.quantity || 0), 0
        );
        const dispRevenue = dispositions.reduce(
            (sum, d) => sum + Number(d.total || 0), 0
        );

        const fmtItems = items =>
            items.length
                ? items
                    .map(i => `${Number(i.quantity).toLocaleString()}× ${tradeItemName(i.id)}`)
                    .join(', ')
                : 'nothing';

        const describe = tradeIdValue => {
            const trade = state.trades.find(
                t => String(t.id) === String(tradeIdValue)
            );
            const sides = trade ? tradeSides(trade) : null;
            if (!sides) return '';

            const gave =
                (sides.givenCash ? money(sides.givenCash) + ' + ' : '') +
                fmtItems(sides.givenItems);
            const got =
                (sides.receivedCash ? money(sides.receivedCash) + ' + ' : '') +
                fmtItems(sides.receivedItems);

            return `Gave: ${gave} · Got: ${got}`;
        };

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>🤝 Trade audit: ${esc(tracked.name)}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Acquired by trade</span>
                    <span class="tpl8-value">${acquisitions.reduce((n, a) => n + Number(a.quantity || 0), 0).toLocaleString()} units (${acquisitions.length})</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Disposed by trade</span>
                    <span class="tpl8-value">${dispUnits.toLocaleString()} units (${dispositions.length})</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Trade sale revenue</span>
                    <span class="tpl8-value">${money(dispRevenue)}</span>
                </div>
                ${
                    acquisitions.slice(0, 10).map(a => `
                        <div class="tpl8-record" style="margin-top:8px">
                            <strong>${esc(a.dateText)} · trade #${esc(a.tradeId)} · ${esc(a.player)}</strong><br>
                            ${Number(a.quantity).toLocaleString()} units at ${money(a.unitPrice)} = ${money(a.total)}
                            (${a.exact ? 'exact' : 'estimated'})<br>
                            <span class="tpl8-muted" style="font-size:11px">${esc(describe(a.tradeId))}</span>
                        </div>
                    `).join('')
                }
            </div>
        `;
    }

    function renderSendDebugBox() {
        let diag = null;

        try {
            diag = JSON.parse(localStorage.getItem(SEND_DIAG_KEY) || 'null');
        } catch (_) {}

        let armoryNote = '';
        try {
            const u = JSON.parse(localStorage.getItem(USE_DIAG_KEY) || 'null');
            if (u) armoryNote = `Faction armory rows in last use batch: ${Number(u.lastArmory || 0).toLocaleString()}`;
        } catch (_) {}

        if (!diag) {
            return `
                <div class="tpl8-card">
                    <div class="tpl8-diagnostic-title">
                        <span>📤 Item send log debug (log 4102)</span>
                    </div>
                    <div class="tpl8-muted">
                        Run a Use Sync to populate this.
                    </div>
                </div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>📤 Item send log debug (log 4102)</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Last batch: raw logs</span>
                    <span class="tpl8-value">${Number(diag.lastRaw || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Readable sends</span>
                    <span class="tpl8-value">${Number(diag.lastParsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Unreadable logs</span>
                    <span class="tpl8-value">${Number(diag.lastUnparsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Tracked-item matches</span>
                    <span class="tpl8-value">${Number(diag.lastMatched || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-muted" style="font-size:11px;margin-top:6px">${esc(armoryNote)}</div>
                ${
                    (diag.samples || []).length
                        ? `<div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            Unreadable sample:<br>${esc(diag.samples[0])}
                           </div>`
                        : ''
                }
            </div>
        `;
    }

    function renderOverdoseDebugBox() {
        let diag = null;

        try {
            diag = JSON.parse(localStorage.getItem(OD_DIAG_KEY) || 'null');
        } catch (_) {}

        if (!diag) {
            return `
                <div class="tpl8-card">
                    <div class="tpl8-diagnostic-title">
                        <span>☠️ Overdose log debug (log ${esc(overdoseLogId())})</span>
                    </div>
                    <div class="tpl8-muted">
                        Run a Use Sync to populate this.
                    </div>
                </div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>☠️ Overdose log debug (log ${esc(overdoseLogId())})</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Last batch: raw logs</span>
                    <span class="tpl8-value">${Number(diag.lastRaw || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Readable overdoses</span>
                    <span class="tpl8-value">${Number(diag.lastParsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Unreadable logs</span>
                    <span class="tpl8-value">${Number(diag.lastUnparsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Tracked-item matches</span>
                    <span class="tpl8-value">${Number(diag.lastMatched || 0).toLocaleString()}</span>
                </div>
                ${
                    (diag.samples || []).length
                        ? `<div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            Unreadable sample:<br>${esc(diag.samples[0])}
                           </div>`
                        : ''
                }
            </div>
        `;
    }

    function renderUseDebugBox() {
        let diag = null;

        try {
            diag = JSON.parse(localStorage.getItem(USE_DIAG_KEY) || 'null');
        } catch (_) {}

        if (!diag) {
            return `
                <div class="tpl8-card">
                    <div class="tpl8-diagnostic-title">
                        <span>💊 Item use log debug</span>
                    </div>
                    <div class="tpl8-muted">
                        Run a Use Sync to populate this.
                    </div>
                </div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>💊 Item use log debug</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Last batch: raw logs</span>
                    <span class="tpl8-value">${Number(diag.lastRaw || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Readable uses</span>
                    <span class="tpl8-value">${Number(diag.lastParsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Unreadable logs</span>
                    <span class="tpl8-value">${Number(diag.lastUnparsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Tracked-item matches</span>
                    <span class="tpl8-value">${Number(diag.lastMatched || 0).toLocaleString()}</span>
                </div>
                ${
                    (diag.sigs || []).map(g => `
                        <div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            <strong>${Number(g.count).toLocaleString()}× data keys:</strong> ${esc(g.sig)}<br>
                            ${esc(g.sample)}
                        </div>
                    `).join('')
                }
                ${
                    (diag.samples || []).length
                        ? `<div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            Unreadable sample:<br>${esc(diag.samples[0])}
                           </div>`
                        : ''
                }
            </div>
        `;
    }

    function renderParcelDebugBox() {
        let diag = null;

        try {
            diag = JSON.parse(localStorage.getItem(PARCEL_DIAG_KEY) || 'null');
        } catch (_) {}

        if (!diag) {
            return `
                <div class="tpl8-card">
                    <div class="tpl8-diagnostic-title">
                        <span>🎁 Parcel log debug</span>
                    </div>
                    <div class="tpl8-muted">
                        Run a Parcel Sync to populate this.
                    </div>
                </div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>🎁 Parcel log debug</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Last batch: raw logs</span>
                    <span class="tpl8-value">${Number(diag.lastRaw || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Readable opens</span>
                    <span class="tpl8-value">${Number(diag.lastParsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Unreadable logs</span>
                    <span class="tpl8-value">${Number(diag.lastUnparsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Tracked-item matches</span>
                    <span class="tpl8-value">${Number(diag.lastMatched || 0).toLocaleString()}</span>
                </div>
                ${
                    (diag.samples || []).length
                        ? `<div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            Unreadable sample:<br>${esc(diag.samples[0])}
                           </div>`
                        : ''
                }
            </div>
        `;
    }

    function renderTravelDebugBox() {
        let diag = null;

        try {
            diag = JSON.parse(localStorage.getItem(TRAVEL_DIAG_KEY) || 'null');
        } catch (_) {}

        if (!diag) {
            return `
                <div class="tpl8-card">
                    <div class="tpl8-diagnostic-title">
                        <span>✈️ Travel log debug</span>
                    </div>
                    <div class="tpl8-muted">
                        Run a travel sync to populate this.
                    </div>
                </div>
            `;
        }

        return `
            <div class="tpl8-card">
                <div class="tpl8-diagnostic-title">
                    <span>✈️ Travel log debug</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Last batch: raw logs</span>
                    <span class="tpl8-value">${Number(diag.lastRaw || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Parsed lines</span>
                    <span class="tpl8-value">${Number(diag.lastParsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Unreadable logs</span>
                    <span class="tpl8-value">${Number(diag.lastUnparsed || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-stat">
                    <span class="tpl8-label">Matched tracked items</span>
                    <span class="tpl8-value">${Number(diag.lastMatched || 0).toLocaleString()}</span>
                </div>
                <div class="tpl8-muted" style="font-size:11px;margin-top:6px">
                    Items seen: ${esc((diag.lastNames || []).join(', ') || 'none')}
                </div>
                ${
                    (diag.samples || []).length
                        ? `<div class="tpl8-muted" style="font-size:10px;margin-top:6px;word-break:break-all">
                            Unreadable sample:<br>${esc(diag.samples[0])}
                           </div>`
                        : ''
                }
            </div>
        `;
    }

    function renderDiagnosticItem(
        tracked,
        pnl,
        diagnostics
    ) {
        const first =
            diagnostics.firstDeficit;

        const unmatched =
            diagnostics.unmatched.filter(
                x =>
                    x.unmatched > 0
            );

        const deficitByMonth = {};
        for (const x of unmatched) {
            const dt = new Date(
                (Number(x.event.timestamp) || 0) * 1000
            );
            const k = dt.getFullYear() + '-' +
                String(dt.getMonth() + 1).padStart(2, '0');
            const src = String(x.event.source || '?');
            const o = deficitByMonth[k] ||
                (deficitByMonth[k] = { qty: 0, bySrc: {} });
            o.qty += x.unmatched;
            o.bySrc[src] = (o.bySrc[src] || 0) + x.unmatched;
        }
        const flow = {};
        for (const ev of (diagnostics.events || [])) {
            const dt = new Date((Number(ev.timestamp) || 0) * 1000);
            const k = dt.getFullYear() + '-' +
                String(dt.getMonth() + 1).padStart(2, '0');
            const o = flow[k] || (flow[k] = { inn: 0, out: 0 });
            if (ev.type === 'purchase') o.inn += Number(ev.quantity) || 0;
            else o.out += Number(ev.quantity) || 0;
        }
        let runInv = 0;
        const flowHtml = Object.keys(flow).sort().map(k => {
            const o = flow[k];
            runInv += o.inn - o.out;
            return `${k}: +${o.inn.toLocaleString()} / -${o.out.toLocaleString()} = ${runInv.toLocaleString()}` +
                (runInv < 0 ? ' \u26a0' : '');
        }).join('<br>');

        const deficitMonthsHtml = Object.keys(deficitByMonth)
            .sort()
            .map(k => `${k}: ${deficitByMonth[k].qty.toLocaleString()} (` +
                Object.entries(deficitByMonth[k].bySrc)
                    .map(([a, b]) => `${a} ${b.toLocaleString()}`)
                    .join(', ') + ')')
            .join('<br>');

        const key =
            'diag-' +
            String(tracked.id);

        const expanded =
            expandedItems.has(key);

        const receives =
            state.itemReceives
                .filter(
                    receive =>
                        norm(receive.itemName) ===
                        norm(tracked.name)
                )
                .sort(
                    (a, b) =>
                        Number(a.timestamp || 0) -
                        Number(b.timestamp || 0)
                );

        const receivedUnits =
            receives.reduce(
                (sum, receive) =>
                    sum +
                    Number(
                        receive.quantity || 0
                    ),
                0
            );

        const firstReceive =
            receives.length
                ? receives[0]
                : null;

        const lastReceive =
            receives.length
                ? receives[receives.length - 1]
                : null;

        const potentialCoverage =
            Math.min(
                receivedUnits,
                Number(pnl.unmatchedSold || 0)
            );

        return `
            <div class="tpl8-card"
                 data-item-id="${esc(
                     String(tracked.id)
                 )}">

                <div class="tpl8-diagnostic-title">
                    <span>
                        ${esc(tracked.name)}
                    </span>

                    <span>
                        ${pnl.complete
                            ? '✓'
                            : '⚠️'}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Bought
                    </span>
                    <span class="tpl8-value">
                        ${pnl.totalPurchased.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Sold
                    </span>
                    <span class="tpl8-value">
                        ${pnl.totalSold.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        FIFO matched
                    </span>
                    <span class="tpl8-value">
                        ${pnl.matchedSold.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        FIFO unmatched
                    </span>
                    <span class="tpl8-value">
                        ${pnl.unmatchedSold.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Unmatched revenue
                    </span>
                    <span class="tpl8-value">
                        ${money(
                            pnl.unmatchedRevenue
                        )}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Received from players
                    </span>
                    <span class="tpl8-value">
                        ${receivedUnits.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Receive records
                    </span>
                    <span class="tpl8-value">
                        ${receives.length.toLocaleString()}
                    </span>
                </div>


                ${
                    isTravelDiagnosticAllowed(tracked.name)
                        ? (() => {
                            const travel = state.travelPurchases.filter(
                                purchase => norm(purchase.itemName) === norm(tracked.name)
                            );
                            const travelUnits = travel.reduce(
                                (sum, purchase) => sum + Number(purchase.quantity || 0),
                                0
                            );
                            return `
                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Travel purchases
                                    </span>
                                    <span class="tpl8-value">
                                        ${travelUnits.toLocaleString()} (${travel.length.toLocaleString()} records)
                                    </span>
                                </div>
                            `;
                        })()
                        : ''
                }

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Potential deficit coverage
                    </span>
                    <span class="tpl8-value">
                        ${potentialCoverage.toLocaleString()}
                    </span>
                </div>

                ${
                    first
                        ? `
                            <div class="tpl8-pnl-warning">
                                <strong>
                                    First FIFO deficit
                                </strong>

                                <br>

                                ${esc(
                                    formatDate(
                                        first.timestamp
                                    )
                                )}

                                <br>

                                ${esc(first.source)}
                                · ID ${esc(first.id)}

                                <br>

                                Sold:
                                ${first.quantity.toLocaleString()}

                                · Inventory before:
                                ${first.beforeInventory.toLocaleString()}

                                <br>

                                Matched:
                                ${first.matched.toLocaleString()}

                                · Unmatched:
                                ${first.unmatched.toLocaleString()}

                                <br>

                                Unmatched revenue:
                                ${money(
                                    first.unmatchedRevenue
                                )}

                                <br>

                                <span class="tpl8-muted">
                                    This is the first chronological
                                    point where recorded sales exceed
                                    recorded inventory.
                                </span>
                            </div>
                        `
                        : `
                            <div class="tpl8-pnl-complete">
                                ✓ No chronological FIFO deficit detected.
                            </div>
                        `
                }

                ${
                    flowHtml
                        ? `<div class="tpl8-history">
                            <div class="tpl8-history-count">Monthly flow: +in / -out = running balance (unfloored)</div>
                            <div class="tpl8-muted">${flowHtml}</div>
                           </div>`
                        : ''
                }

                ${
                    deficitMonthsHtml
                        ? `<div class="tpl8-history">
                            <div class="tpl8-history-count">Unmatched (over-disposed) by month</div>
                            <div class="tpl8-muted">${deficitMonthsHtml}</div>
                           </div>`
                        : ''
                }

                ${
                    receives.length
                        ? `
                            <div class="tpl8-history">
                                <div class="tpl8-history-count">
                                    Player Item Receives
                                </div>

                                ${
                                    firstReceive
                                        ? `
                                            <div class="tpl8-record">
                                                <strong>First:</strong>
                                                ${esc(
                                                    formatDate(
                                                        firstReceive.timestamp
                                                    )
                                                )}
                                                · ${esc(
                                                    firstReceive.sender
                                                )}
                                                · ${Number(
                                                    firstReceive.quantity || 0
                                                ).toLocaleString()}
                                            </div>
                                        `
                                        : ''
                                }

                                ${
                                    lastReceive &&
                                    lastReceive !== firstReceive
                                        ? `
                                            <div class="tpl8-record">
                                                <strong>Last:</strong>
                                                ${esc(
                                                    formatDate(
                                                        lastReceive.timestamp
                                                    )
                                                )}
                                                · ${esc(
                                                    lastReceive.sender
                                                )}
                                                · ${Number(
                                                    lastReceive.quantity || 0
                                                ).toLocaleString()}
                                            </div>
                                        `
                                        : ''
                                }

                                <div class="tpl8-muted"
                                     style="margin-top:6px;font-size:11px">
                                    Receive quantity is shown for diagnosis only.
                                    It is not included in FIFO accounting yet.
                                </div>

                                ${
                                    expanded
                                        ? receives
                                            .slice(0, 100)
                                            .map(receive => `
                                                <div class="tpl8-record">
                                                    <strong>
                                                        ${esc(
                                                            formatDate(
                                                                receive.timestamp
                                                            )
                                                        )}
                                                    </strong>

                                                    <br>

                                                    Received:
                                                    ${Number(
                                                        receive.quantity || 0
                                                    ).toLocaleString()}
                                                    · From:
                                                    ${esc(
                                                        receive.sender
                                                    )}

                                                    ${
                                                        receive.message
                                                            ? `
                                                                <br>
                                                                Message:
                                                                ${esc(
                                                                    receive.message
                                                                )}
                                                            `
                                                            : ''
                                                    }

                                                    ${
                                                        receive.senderId
                                                            ? `
                                                                <br>
                                                                Sender ID:
                                                                ${esc(
                                                                    receive.senderId
                                                                )}
                                                            `
                                                            : ''
                                                    }
                                                </div>
                                            `)
                                            .join('')
                                        : ''
                                }

                                ${
                                    expanded &&
                                    receives.length > 100
                                        ? `
                                            <div class="tpl8-muted"
                                                 style="margin-top:6px;font-size:11px">
                                                Showing the first 100 receive records.
                                            </div>
                                        `
                                        : ''
                                }
                            </div>
                        `
                        : `
                            <div class="tpl8-muted"
                                 style="margin-top:8px;font-size:11px">
                                No Item Receive records found for this tracked item.
                            </div>
                        `
                }

                ${
                    expanded
                        ? `
                            <div class="tpl8-history">
                                <div class="tpl8-history-count">
                                    ${unmatched.length.toLocaleString()}
                                    unmatched/partial sale events
                                </div>

                                ${
                                    unmatched
                                        .slice(0, 100)
                                        .map(entry => `
                                            <div class="tpl8-record">
                                                <strong>
                                                    ${esc(
                                                        formatDate(
                                                            entry.event.timestamp
                                                        )
                                                    )}
                                                </strong>

                                                <br>

                                                ${esc(
                                                    entry.event.source
                                                )}
                                                · ID
                                                ${esc(
                                                    entry.event.id
                                                )}

                                                <br>

                                                Sold:
                                                ${entry.event.quantity.toLocaleString()}

                                                <br>

                                                Inventory before:
                                                ${entry.beforeInventory.toLocaleString()}

                                                <br>

                                                FIFO matched:
                                                ${entry.matched.toLocaleString()}

                                                <br>

                                                FIFO unmatched:
                                                ${entry.unmatched.toLocaleString()}

                                                <br>

                                                Total revenue:
                                                ${money(
                                                    entry.event.total
                                                )}

                                                <br>

                                                Unmatched revenue:
                                                ${money(
                                                    entry.unmatchedRevenue
                                                )}

                                                <br>

                                                Unit revenue:
                                                ${money(
                                                    entry.event.quantity
                                                        ? entry.event.total /
                                                          entry.event.quantity
                                                        : 0
                                                )}

                                                <br>

                                                Counterparty:
                                                ${esc(
                                                    entry.event.buyer ||
                                                    'Unknown'
                                                )}
                                            </div>
                                        `)
                                        .join('')
                                }
                            </div>
                        `
                        : ''
                }

                <div class="tpl8-muted"
                     style="margin-top:10px;font-size:11px">
                    Tap this card to
                    ${expanded
                        ? 'collapse'
                        : 'expand'}
                    diagnostic sale details.
                </div>
            </div>
        `;
    }

    /* =====================================================
       PRICES
    ===================================================== */

    async function refreshPrice(item) {
        const id = Number(item.id);

        prices[id] = {
            status: 'loading',
            tmv:
                Number(item.market_value) ||
                lastKnownTmv(id) ||
                0,
            lowest: null
        };

        render();

        try {
            const market =
                (
                    await api(
                        `/market/${id}/itemmarket`,
                        {},
                        10000
                    )
                )?.itemmarket || {};

            const listings =
                Array.isArray(
                    market.listings
                )
                    ? market.listings
                    : [];

            let lowest = null;

            for (const listing of listings) {
                const price =
                    Number(listing?.price);

                if (
                    Number.isFinite(price) &&
                    price > 0 &&
                    (
                        lowest === null ||
                        price < lowest
                    )
                ) {
                    lowest = price;
                }
            }

            const goodTmv =
                Number(
                    market?.item?.average_price
                ) ||
                Number(item.market_value) ||
                lastKnownTmv(id) ||
                0;

            rememberTmv(id, goodTmv);

            prices[id] = {
                status: 'ok',
                tmv: goodTmv,
                lowest
            };
        } catch (_) {
            prices[id] = {
                status: 'unavailable',
                tmv:
                    Number(item.market_value) ||
                    lastKnownTmv(id) ||
                    0,
                lowest: null
            };
        }

        render();
    }

    async function refreshPrices() {
        if (pricing) return;

        pricing = true;

        setStatus('Refreshing prices...');

        try {
            for (const tracked of state.tracked) {
                const item =
                    catalogMap.get(
                        Number(tracked.id)
                    );

                if (item) {
                    await refreshPrice(item);
                }

                await sleep(200);
            }

            setStatus(
                'Prices refreshed'
            );
        } finally {
            pricing = false;
        }
    }

    /* =====================================================
       UI
    ===================================================== */

    function addCSS() {
        if (
            document.getElementById(
                'tpl8-css'
            )
        ) {
            return;
        }

        const style =
            document.createElement('style');

        style.id = 'tpl8-css';

        style.textContent = `
            #tpl8-tab {
                position: fixed !important;
                right: 0 !important;
                top: 42% !important;
                width: 48px !important;
                height: 60px !important;
                border: 0 !important;
                border-radius: 14px 0 0 14px !important;
                background: #202226 !important;
                color: white !important;
                font-size: 23px !important;
                z-index: 2147483647 !important;
                padding: 0 !important;
                margin: 0 !important;
                display: block !important;
                pointer-events: auto !important;
                touch-action: manipulation !important;
                transition: right .15s ease !important;
            }

            #tpl8-drawer {
                position: fixed !important;
                top: 0 !important;
                right: 0 !important;
                bottom: 0 !important;
                width: 390px;
                max-width: calc(100vw - 10px) !important;
                min-width: 280px !important;
                background: #101114 !important;
                color: #eee !important;
                z-index: 2147483646 !important;
                display: none !important;
                flex-direction: column !important;
                box-shadow: -5px 0 25px rgba(0,0,0,.55) !important;
                font-family: Arial, sans-serif !important;
            }

            #tpl8-drawer.open {
                display: flex !important;
            }

            #tpl8-head {
                flex-shrink: 0 !important;
                padding: 12px !important;
                background: #181a1e !important;
                border-bottom: 1px solid #30333a !important;
            }

            #tpl8-title-row {
                display: flex !important;
                justify-content: space-between !important;
                align-items: center !important;
            }

            #tpl8-title {
                font-size: 18px !important;
                font-weight: bold !important;
            }

            .tpl8-btn {
                border: 0 !important;
                border-radius: 8px !important;
                background: #292c32 !important;
                color: #eee !important;
                padding: 8px 10px !important;
                font-size: 13px !important;
                touch-action: manipulation !important;
            }

            #tpl8-status {
                margin-top: 7px !important;
                min-height: 16px !important;
                color: #999 !important;
                font-size: 12px !important;
            }

            #tpl8-pages {
                display: flex !important;
                gap: 5px !important;
                margin-top: 9px !important;
                width: 100% !important;
            }

            .tpl8-page-btn {
                flex: 1 !important;
                border: 0 !important;
                border-radius: 8px !important;
                background: #22252a !important;
                color: #999 !important;
                padding: 9px 3px !important;
                font-size: 11px !important;
                font-weight: bold !important;
                touch-action: manipulation !important;
            }

            .tpl8-page-btn.active {
                background: #3a3e46 !important;
                color: #fff !important;
            }

            #tpl8-controls {
                display: flex !important;
                flex-wrap: wrap !important;
                gap: 6px !important;
                margin-top: 8px !important;
            }

            #tpl8-search {
                width: 100% !important;
                box-sizing: border-box !important;
                margin-top: 9px !important;
                padding: 10px !important;
                border: 1px solid #3a3d44 !important;
                border-radius: 8px !important;
                background: #22252a !important;
                color: white !important;
                font-size: 14px !important;
            }

            #tpl8-results {
                position: absolute !important;
                left: 0 !important;
                right: 0 !important;
                max-height: 230px !important;
                overflow-y: auto !important;
                background: #202329 !important;
                border: 1px solid #3a3d44 !important;
                border-radius: 8px !important;
                z-index: 100 !important;
            }

            .tpl8-result {
                padding: 11px !important;
                border-bottom: 1px solid #34373d !important;
                font-size: 13px !important;
                touch-action: manipulation !important;
            }

            #tpl8-body {
                flex: 1 !important;
                overflow-y: auto !important;
                padding: 10px !important;
                -webkit-overflow-scrolling: touch !important;
            }

            .tpl8-card {
                margin-bottom: 10px !important;
                padding: 11px !important;
                border: 1px solid #30333a !important;
                border-radius: 10px !important;
                background: #191b20 !important;
            }

            .tpl8-remove-tracked {
                margin-left: auto !important;
                margin-right: 8px !important;
                border: 1px solid rgba(255,255,255,.18) !important;
                background: transparent !important;
                color: inherit !important;
                border-radius: 4px !important;
                padding: 3px 7px !important;
                font-size: 10px !important;
                cursor: pointer !important;
                opacity: .75 !important;
                touch-action: manipulation !important;
            }

            .tpl8-remove-tracked:hover {
                opacity: 1 !important;
            }

            .tpl8-title {
                display: flex !important;
                align-items: center !important;
                justify-content: space-between !important;
                width: 100% !important;
                box-sizing: border-box !important;
                font-size: 16px !important;
                font-weight: bold !important;
                margin-bottom: 8px !important;
                cursor: pointer !important;
                touch-action: manipulation !important;
            }

            .tpl8-title-name {
                flex: 1 !important;
            }

            .tpl8-arrow {
                width: 24px !important;
                text-align: center !important;
                color: #aaa !important;
            }

            .tpl8-diagnostic-title {
                display: flex !important;
                justify-content: space-between !important;
                align-items: center !important;
                font-size: 16px !important;
                font-weight: bold !important;
                margin-bottom: 8px !important;
            }

            .tpl8-stat {
                display: flex !important;
                justify-content: space-between !important;
                gap: 10px !important;
                padding: 3px 0 !important;
                font-size: 13px !important;
            }

            .tpl8-label {
                color: #999 !important;
            }

            .tpl8-value {
                text-align: right !important;
            }

            .tpl8-price,
            .tpl8-history,
            .tpl8-pnl-section,
            .tpl8-trade-section {
                margin-top: 10px !important;
                padding-top: 9px !important;
                border-top: 1px solid #30333a !important;
            }

            .tpl8-history-count {
                margin-bottom: 7px !important;
                color: #999 !important;
                font-size: 11px !important;
            }

            .tpl8-record {
                margin-top: 6px !important;
                padding: 8px !important;
                border-radius: 7px !important;
                background: #121318 !important;
                font-size: 12px !important;
                line-height: 1.45 !important;
            }

            .tpl8-muted {
                color: #888 !important;
            }

            .tpl8-empty {
                padding: 35px 15px !important;
                text-align: center !important;
                color: #888 !important;
            }

            .tpl8-pnl-positive {
                color: #70d890 !important;
                font-weight: bold !important;
            }

            .tpl8-pnl-negative {
                color: #ff7777 !important;
                font-weight: bold !important;
            }

            .tpl8-pnl-neutral {
                color: #ddd !important;
                font-weight: bold !important;
            }

            .tpl8-pnl-warning {
                margin-bottom: 10px !important;
                padding: 10px !important;
                border-radius: 8px !important;
                background: #29241b !important;
                border: 1px solid #554827 !important;
                color: #d8c99a !important;
                font-size: 12px !important;
                line-height: 1.45 !important;
            }

            .tpl8-pnl-complete {
                margin-bottom: 10px !important;
                padding: 9px !important;
                border-radius: 8px !important;
                background: #19231d !important;
                border: 1px solid #294332 !important;
                color: #9bc6a7 !important;
                font-size: 12px !important;
            }

            .tpl8-trade-player {
                font-size: 15px !important;
                font-weight: bold !important;
            }

            .tpl8-trade-button {
                margin-top: 8px !important;
                width: 100% !important;
            }

            .tpl8-trade-item {
                display: flex !important;
                justify-content: space-between !important;
                gap: 10px !important;
                padding: 3px 0 !important;
            }

            .tpl8-trade-side {
                margin-top: 8px !important;
                padding: 8px !important;
                border-radius: 8px !important;
                background: #121318 !important;
            }

            .tpl8-trade-side-title {
                margin-bottom: 6px !important;
                font-size: 11px !important;
                font-weight: bold !important;
                color: #aaa !important;
                text-transform: uppercase !important;
            }

            .tpl8-trade-money {
                display: flex !important;
                justify-content: space-between !important;
                gap: 10px !important;
                padding: 3px 0 !important;
            }

            .tpl8-estimated {
                color: #d8c99a !important;
                font-size: 11px !important;
            }

            .tpl8-trade-loading {
                margin-bottom: 10px !important;
                padding: 10px !important;
                border-radius: 8px !important;
                background: #20242a !important;
                border: 1px solid #343a43 !important;
                color: #bbb !important;
                font-size: 12px !important;
                line-height: 1.45 !important;
            }
        `;

        document.head.appendChild(style);
    }

    /* =====================================================
       PERSISTENT UI
    ===================================================== */

    function positionLedgerButton() {
        if (!tab || !drawer) return;

        /*
         * IMPORTANT:
         * The button is NEVER hidden.
         *
         * When the drawer is open, move the button to
         * immediately beside the drawer instead.
         */

        if (
            drawer.classList.contains('open')
        ) {
            const width =
                drawer.getBoundingClientRect()
                    .width;

            tab.style.right =
                Math.max(
                    0,
                    Math.round(width)
                ) + 'px';
        } else {
            tab.style.right = '0px';
        }

        tab.style.display = 'block';
        tab.style.visibility = 'visible';
        tab.style.opacity = '1';
    }

    function createUI() {
        addCSS();

        if (
            document.getElementById(
                'tpl8-tab'
            )
        ) {
            tab =
                document.getElementById(
                    'tpl8-tab'
                );
        } else {
            tab =
                document.createElement(
                    'button'
                );

            tab.id = 'tpl8-tab';
            tab.type = 'button';
            tab.textContent = '🧾';

            document.body.appendChild(tab);
        }

        if (
            document.getElementById(
                'tpl8-drawer'
            )
        ) {
            drawer =
                document.getElementById(
                    'tpl8-drawer'
                );

            /*
             * If Torn replaced the drawer contents,
             * rebuild it.
             */
            if (
                !drawer.querySelector(
                    '#tpl8-body'
                )
            ) {
                drawer.remove();
                drawer = null;
            }
        }

        if (!drawer) {
            drawer =
                document.createElement(
                    'div'
                );

            drawer.id = 'tpl8-drawer';

            drawer.innerHTML = `
                <div id="tpl8-head">

                    <div id="tpl8-title-row">
                        <div id="tpl8-title">
                            🧾 Purchase Ledger
                        </div>

                        <button
                            id="tpl8-close"
                            class="tpl8-btn"
                        >
                            ✕
                        </button>
                    </div>

                    <div id="tpl8-status">
                        Ready
                    </div>

                    <div id="tpl8-pages">

                        <button
                            id="tpl8-page-buying"
                            class="tpl8-page-btn active"
                        >
                            Buying
                        </button>

                        <button
                            id="tpl8-page-selling"
                            class="tpl8-page-btn"
                        >
                            Selling
                        </button>

                        <button
                            id="tpl8-page-trades"
                            class="tpl8-page-btn"
                        >
                            🤝 Trades
                        </button>

                        <button
                            id="tpl8-page-pnl"
                            class="tpl8-page-btn"
                        >
                            P&amp;L
                        </button>

                        <button
                            id="tpl8-page-diagnostics"
                            class="tpl8-page-btn"
                        >
                            🔎
                        </button>

                    </div>

                    <div id="tpl8-controls">

                        <button
                            id="tpl8-sync"
                            class="tpl8-btn"
                        >
                            ↻ Sync
                        </button>

                        <button
                            id="tpl8-history"
                            class="tpl8-btn"
                        >
                            ⏪ History
                        </button>

                        <button
                            id="tpl8-sell-sync"
                            class="tpl8-btn"
                        >
                            ↻ Sell Sync
                        </button>

                        <button
                            id="tpl8-sell-history"
                            class="tpl8-btn"
                        >
                            ⏪ Sell History
                        </button>

                        <button
                            id="tpl8-trade-sync"
                            class="tpl8-btn"
                        >
                            ↻ Trade Sync
                        </button>

                        <button
                            id="tpl8-trade-history"
                            class="tpl8-btn"
                        >
                            ⏪ Trade History
                        </button>

                        <button
                            id="tpl8-receive-sync"
                            class="tpl8-btn"
                        >
                            📥 Receive Sync
                        </button>

                        <button
                            id="tpl8-receive-history"
                            class="tpl8-btn"
                        >
                            ⏪ Receive History
                        </button>

                        <button
                            id="tpl8-travel-sync"
                            class="tpl8-btn"
                        >
                            ✈️ Travel Sync
                        </button>

                        <button
                            id="tpl8-travel-history"
                            class="tpl8-btn"
                        >
                            ⏪ Travel History
                        </button>

                        <button
                            id="tpl8-parcel-sync"
                            class="tpl8-btn"
                        >
                            🎁 Parcel Sync
                        </button>

                        <button
                            id="tpl8-use-sync"
                            class="tpl8-btn"
                        >
                            💊 Use Sync
                        </button>

                        <button
                            id="tpl8-sync-all"
                            class="tpl8-btn"
                        >
                            🔄 Sync All
                        </button>

                        <button
                            id="tpl8-price"
                            class="tpl8-btn"
                        >
                            💰 Prices
                        </button>

                        <button
                            id="tpl8-copy"
                            class="tpl8-btn"
                        >
                            Copy
                        </button>

                        <button
                            id="tpl8-minus"
                            class="tpl8-btn"
                        >
                            W−
                        </button>

                        <button
                            id="tpl8-plus"
                            class="tpl8-btn"
                        >
                            W+
                        </button>

                    </div>

                    <div
                        id="tpl8-search-wrap"
                        style="position:relative"
                    >
                        <input
                            id="tpl8-search"
                            placeholder="Add item to track..."
                            autocomplete="off"
                        >

                        <div
                            id="tpl8-results"
                            style="display:none"
                        ></div>
                    </div>

                </div>

                <div id="tpl8-body"></div>
            `;

            document.body.appendChild(
                drawer
            );
        }

        drawer.style.width =
            (
                Number(
                    localStorage.getItem(
                        WIDTH_KEY
                    )
                ) || 390
            ) + 'px';

        setupEvents();

        positionLedgerButton();

        if (getSyncAllRemaining() > 0) {
            startSyncAllCooldown();
        }

        render();
    }

    function ensureUI() {
        if (!document.body) return;

        const existingTab =
            document.getElementById(
                'tpl8-tab'
            );

        const existingDrawer =
            document.getElementById(
                'tpl8-drawer'
            );

        /*
         * Torn can replace page content while
         * navigating between sections.
         *
         * If either element disappears,
         * recreate the UI.
         */

        if (
            !existingTab ||
            !document.body.contains(
                existingTab
            ) ||
            !existingDrawer ||
            !document.body.contains(
                existingDrawer
            )
        ) {
            const wasOpen =
                drawer &&
                drawer.classList.contains(
                    'open'
                );

            createUI();

            if (wasOpen && drawer) {
                drawer.classList.add(
                    'open'
                );

                positionLedgerButton();
            }

            return;
        }

        tab = existingTab;
        drawer = existingDrawer;

        /*
         * Torn may alter inline styles/classes.
         * Reassert our critical button properties.
         */
        tab.style.display = 'block';
        tab.style.visibility = 'visible';
        tab.style.opacity = '1';

        positionLedgerButton();
    }

    function startUIWatchdog() {
        if (uiObserver) return;

        uiObserver =
            new MutationObserver(() => {
                clearTimeout(
                    uiCheckTimer
                );

                uiCheckTimer =
                    setTimeout(
                        ensureUI,
                        50
                    );
            });

        uiObserver.observe(
            document.body,
            {
                childList: true,
                subtree: true
            }
        );

        /*
         * Extra periodic check.
         * This catches aggressive SPA navigation
         * that replaces nodes in unusual ways.
         */
        setInterval(
            ensureUI,
            1000
        );
    }

    function setupEvents() {
        if (!tab || !drawer) return;

        /*
         * Prevent duplicate listeners if the watchdog
         * verifies an existing UI.
         */
        if (
            tab.dataset.tpl8Bound === '1'
        ) {
            return;
        }

        tab.dataset.tpl8Bound = '1';

        const openLedger = event => {
            event.preventDefault();
            event.stopPropagation();

            if (!drawer) return;

            drawer.classList.add(
                'open'
            );

            /*
             * DO NOT hide the button.
             * Move it beside the drawer.
             */
            positionLedgerButton();
        };

        tab.addEventListener(
            'click',
            openLedger,
            true
        );

        tab.addEventListener(
            'touchend',
            openLedger,
            {
                passive: false,
                capture: true
            }
        );

        drawer
            .querySelector(
                '#tpl8-close'
            )
            .addEventListener(
                'click',
                () => {
                    drawer.classList.remove(
                        'open'
                    );

                    /*
                     * Restore the button to the
                     * right edge.
                     */
                    positionLedgerButton();
                }
            );

        const pages = {
            buying:
                'tpl8-page-buying',

            selling:
                'tpl8-page-selling',

            trades:
                'tpl8-page-trades',

            pnl:
                'tpl8-page-pnl',

            diagnostics:
                'tpl8-page-diagnostics'
        };

        for (
            const [page, id]
            of Object.entries(pages)
        ) {
            const button =
                drawer.querySelector(
                    '#' + id
                );

            if (button) {
                button.addEventListener(
                    'click',
                    () =>
                        switchPage(page)
                );
            }
        }

        drawer
            .querySelector('#tpl8-sync')
            .addEventListener(
                'click',
                syncPurchases
            );

        drawer
            .querySelector('#tpl8-history')
            .addEventListener(
                'click',
                syncHistoricalPurchases
            );

        drawer
            .querySelector('#tpl8-sell-sync')
            .addEventListener(
                'click',
                syncSells
            );

        drawer
            .querySelector('#tpl8-sell-history')
            .addEventListener(
                'click',
                syncHistoricalSells
            );

        drawer
            .querySelector('#tpl8-trade-sync')
            .addEventListener(
                'click',
                syncTrades
            );

        drawer
            .querySelector('#tpl8-trade-history')
            .addEventListener(
                'click',
                syncHistoricalTrades
            );

        drawer
            .querySelector('#tpl8-receive-sync')
            .addEventListener(
                'click',
                syncItemReceives
            );

        drawer
            .querySelector('#tpl8-receive-history')
            .addEventListener(
                'click',
                syncHistoricalItemReceives
            );

        drawer
            .querySelector('#tpl8-travel-sync')
            .addEventListener(
                'click',
                syncTravelPurchases
            );

        drawer
            .querySelector('#tpl8-travel-history')
            .addEventListener(
                'click',
                syncHistoricalTravelPurchases
            );

        drawer
            .querySelector('#tpl8-parcel-sync')
            .addEventListener(
                'click',
                syncParcelOpens
            );

        drawer
            .querySelector('#tpl8-use-sync')
            .addEventListener(
                'click',
                syncItemUses
            );

        drawer
            .querySelector('#tpl8-sync-all')
            .addEventListener(
                'click',
                syncAll
            );

        drawer
            .querySelector('#tpl8-price')
            .addEventListener(
                'click',
                refreshPrices
            );

        drawer
            .querySelector('#tpl8-copy')
            .addEventListener(
                'click',
                copyLedger
            );

        drawer
            .querySelector('#tpl8-minus')
            .addEventListener(
                'click',
                () =>
                    resizeDrawer(-40)
            );

        drawer
            .querySelector('#tpl8-plus')
            .addEventListener(
                'click',
                () =>
                    resizeDrawer(40)
            );

        drawer
            .querySelector('#tpl8-search')
            .addEventListener(
                'input',
                event =>
                    searchItems(
                        event.target.value
                    )
            );

        drawer
            .querySelector('#tpl8-body')
            .addEventListener(
                'click',
                event => {

                    const tradeButton =
                        event.target.closest(
                            '[data-load-trade]'
                        );

                    if (tradeButton) {
                        loadTradeDetail(
                            tradeButton.dataset
                                .loadTrade
                        );

                        return;
                    }

                    const removeButton =
                        event.target.closest(
                            '[data-remove-tracked]'
                        );

                    if (removeButton) {
                        event.stopPropagation();

                        removeTracked(
                            removeButton.dataset.removeTracked
                        );

                        return;
                    }

                    const title =
                        event.target.closest(
                            '.tpl8-title'
                        );

                    if (!title) return;

                    const card =
                        title.closest(
                            '.tpl8-card'
                        );

                    if (!card) return;

                    if (
                        card.dataset.tradeId
                    ) {
                        const key =
                            'trade-' +
                            card.dataset.tradeId;

                        if (
                            expandedTrades.has(
                                key
                            )
                        ) {
                            expandedTrades.delete(
                                key
                            );
                        } else {
                            expandedTrades.add(
                                key
                            );
                        }
                    } else {
                        const id =
                            card.dataset.itemId;

                        let key;

                        if (
                            activePage ===
                            'selling'
                        ) {
                            key =
                                'sell-' +
                                id;
                        } else if (
                            activePage ===
                            'pnl'
                        ) {
                            key =
                                'pnl-' +
                                id;
                        } else if (
                            activePage ===
                            'diagnostics'
                        ) {
                            key =
                                'diag-' +
                                id;
                        } else {
                            key = id;
                        }

                        if (
                            expandedItems.has(
                                key
                            )
                        ) {
                            expandedItems.delete(
                                key
                            );
                        } else {
                            expandedItems.add(
                                key
                            );
                        }
                    }

                    render();
                }
            );
    }

    function switchPage(page) {
        if (
            ![
                'buying',
                'selling',
                'trades',
                'pnl',
                'diagnostics'
            ].includes(page)
        ) {
            return;
        }

        activePage = page;

        render();
    }

    function resizeDrawer(amount) {
        let width =
            (
                parseInt(
                    drawer.style.width,
                    10
                ) || 390
            ) + amount;

        width = Math.max(
            280,
            Math.min(
                window.innerWidth - 10,
                width
            )
        );

        drawer.style.width =
            width + 'px';

        localStorage.setItem(
            WIDTH_KEY,
            String(width)
        );

        positionLedgerButton();
    }

    function searchItems(value) {
        const results =
            drawer.querySelector(
                '#tpl8-results'
            );

        const query =
            norm(value);

        if (!query) {
            results.style.display =
                'none';

            return;
        }

        const matches =
            catalog
                .filter(
                    item =>
                        norm(item.name)
                            .includes(query)
                )
                .filter(
                    item =>
                        !state.tracked.some(
                            tracked =>
                                norm(
                                    tracked.name
                                ) ===
                                norm(
                                    item.name
                                )
                        )
                )
                .slice(0, 20);

        results.innerHTML =
            matches
                .map(
                    item => `
                        <div
                            class="tpl8-result"
                            data-id="${item.id}"
                        >
                            ${esc(item.name)}
                        </div>
                    `
                )
                .join('');

        results.style.display =
            'block';

        results
            .querySelectorAll(
                '[data-id]'
            )
            .forEach(result => {
                result.addEventListener(
                    'click',
                    () =>
                        addTracked(
                            Number(
                                result.dataset.id
                            )
                        )
                );
            });
    }

    async function addTracked(id) {
        const item =
            catalogMap.get(id);

        if (!item) return;

        state.tracked.push({
            id,
            name: item.name
        });

        saveState();

        drawer.querySelector(
            '#tpl8-search'
        ).value = '';

        drawer.querySelector(
            '#tpl8-results'
        ).style.display = 'none';

        render();

        await syncPurchases();

        refreshPrice(item);
    }

    function removeTracked(id) {
        const numericId = Number(id);

        const index = state.tracked.findIndex(
            tracked => Number(tracked.id) === numericId
        );

        if (index === -1) return;

        const removed = state.tracked[index];

        state.tracked.splice(index, 1);

        saveState();

        expandedItems.delete(String(numericId));
        expandedItems.delete('sell-' + String(numericId));
        expandedItems.delete('pnl-' + String(numericId));
        expandedItems.delete('diag-' + String(numericId));

        render();

        setStatus(
            `Stopped tracking ${removed.name}`
        );
    }

    function updatePageButtons() {
        const ids = {
            buying:
                'tpl8-page-buying',
            selling:
                'tpl8-page-selling',
            trades:
                'tpl8-page-trades',
            pnl:
                'tpl8-page-pnl',
            diagnostics:
                'tpl8-page-diagnostics'
        };

        for (
            const [page, id]
            of Object.entries(ids)
        ) {
            const button =
                drawer.querySelector(
                    '#' + id
                );

            if (button) {
                button.classList.toggle(
                    'active',
                    activePage === page
                );
            }
        }
    }

    function updatePageControls() {
        const buying =
            activePage === 'buying';

        const selling =
            activePage === 'selling';

        const trades =
            activePage === 'trades';

        const diagnostics =
            activePage === 'diagnostics';

        const show = (
            selector,
            visible
        ) => {
            const element =
                drawer.querySelector(
                    selector
                );

            if (element) {
                element.style.display =
                    visible
                        ? ''
                        : 'none';
            }
        };

        show(
            '#tpl8-sync',
            buying
        );

        show(
            '#tpl8-history',
            buying
        );

        show(
            '#tpl8-sell-sync',
            selling
        );

        show(
            '#tpl8-sell-history',
            selling
        );

        show(
            '#tpl8-trade-sync',
            trades
        );

        show(
            '#tpl8-trade-history',
            trades
        );

        show(
            '#tpl8-receive-sync',
            diagnostics
        );

        show(
            '#tpl8-receive-history',
            diagnostics
        );

        show(
            '#tpl8-price',
            buying
        );

        show(
            '#tpl8-copy',
            buying
        );

        const search =
            drawer.querySelector(
                '#tpl8-search-wrap'
            );

        if (search) {
            search.style.display =
                buying
                    ? ''
                    : 'none';
        }
    }

    function render() {
        if (!drawer) return;

        updatePageButtons();
        updatePageControls();

        const body =
            drawer.querySelector(
                '#tpl8-body'
            );

        if (!body) return;

        if (
            activePage ===
            'buying'
        ) {
            renderBuyingPage(body);
            return;
        }

        if (
            activePage ===
            'selling'
        ) {
            renderSellingPage(body);
            return;
        }

        if (
            activePage ===
            'trades'
        ) {
            renderTradesPage(body);
            return;
        }

        if (
            activePage ===
            'diagnostics'
        ) {
            renderDiagnosticsPage(body);
            return;
        }

        renderPnlPage(body);
    }

    /* =====================================================
       BUYING PAGE
    ===================================================== */

    function renderBuyingPage(body) {
        if (!state.tracked.length) {
            body.innerHTML = `
                <div class="tpl8-empty">
                    🧾<br><br>
                    Search for an item above.
                </div>
            `;

            return;
        }

        body.innerHTML =
            state.tracked
                .map(renderPurchaseCard)
                .join('');
    }

    function renderPurchaseCard(tracked) {
        const purchases =
            state.purchases.filter(
                purchase =>
                    norm(
                        purchase.itemName
                    ) ===
                    norm(tracked.name)
            );

        const quantity =
            purchases.reduce(
                (sum, purchase) =>
                    sum +
                    Number(
                        purchase.quantity
                    ),
                0
            );

        const spent =
            purchases.reduce(
                (sum, purchase) =>
                    sum +
                    Number(
                        purchase.total
                    ),
                0
            );

        const average =
            quantity
                ? spent / quantity
                : 0;

        const item =
            catalogMap.get(
                Number(tracked.id)
            );

        const price =
            prices[tracked.id];

        const tmv =
            price?.tmv ||
            item?.market_value ||
            0;

        const lowest =
            price?.status === 'loading'
                ? 'Checking...'
                : price?.status ===
                  'unavailable'
                    ? 'Unavailable'
                    : price?.lowest != null
                        ? money(
                              price.lowest
                          )
                        : 'Not checked';

        const expanded =
            expandedItems.has(
                String(tracked.id)
            );

        return `
            <div
                class="tpl8-card"
                data-item-id="${tracked.id}"
            >

                <div class="tpl8-title">
                    <span class="tpl8-title-name">
                        ${esc(tracked.name)}
                    </span>

                    <button
                        type="button"
                        class="tpl8-remove-tracked"
                        data-remove-tracked="${tracked.id}"
                        title="Stop tracking this item"
                    >
                        Remove
                    </button>

                    <span class="tpl8-arrow">
                        ${expanded
                            ? '▼'
                            : '▶'}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Quantity
                    </span>

                    <span class="tpl8-value">
                        ${quantity.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Total spent
                    </span>

                    <span class="tpl8-value">
                        ${money(spent)}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Average buy
                    </span>

                    <span class="tpl8-value">
                        ${money(average)}
                    </span>
                </div>

                <div class="tpl8-price">

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            TMV
                        </span>

                        <span class="tpl8-value">
                            ${
                                tmv
                                    ? money(tmv)
                                    : 'Unavailable'
                            }
                        </span>
                    </div>

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            Lowest Item Market
                        </span>

                        <span class="tpl8-value">
                            ${lowest}
                        </span>
                    </div>

                </div>

                ${
                    expanded
                        ? `
                            <div class="tpl8-history">

                                <div class="tpl8-history-count">
                                    ${purchases.length.toLocaleString()}
                                    purchase records
                                </div>

                                ${
                                    purchases
                                        .slice(0, 100)
                                        .map(
                                            purchase => `
                                                <div class="tpl8-record">
                                                    <strong>
                                                        ${esc(
                                                            purchase.dateText
                                                        )}
                                                    </strong>

                                                    <br>

                                                    ${purchase.quantity}
                                                    ×
                                                    ${money(
                                                        purchase.unitPrice
                                                    )}

                                                    =
                                                    <strong>
                                                        ${money(
                                                            purchase.total
                                                        )}
                                                    </strong>

                                                    <br>

                                                    <span class="tpl8-muted">
                                                        Seller:
                                                        ${esc(
                                                            purchase.seller
                                                        )}
                                                    </span>
                                                </div>
                                            `
                                        )
                                        .join('')
                                }

                            </div>
                        `
                        : ''
                }

            </div>
        `;
    }

    /* =====================================================
       SELLING PAGE
    ===================================================== */

    function renderSellingPage(body) {
        if (!state.tracked.length) {
            body.innerHTML = `
                <div class="tpl8-empty">
                    💰<br><br>
                    Track an item first.
                </div>
            `;

            return;
        }

        body.innerHTML =
            state.tracked
                .map(renderSellCard)
                .join('');
    }

    function renderSellCard(tracked) {
        const sales =
            state.sells.filter(
                sale =>
                    norm(
                        sale.itemName
                    ) ===
                    norm(tracked.name)
            );

        const quantity =
            sales.reduce(
                (sum, sale) =>
                    sum +
                    Number(
                        sale.quantity
                    ),
                0
            );

        const revenue =
            sales.reduce(
                (sum, sale) =>
                    sum +
                    Number(
                        sale.total
                    ),
                0
            );

        const fees =
            sales.reduce(
                (sum, sale) =>
                    sum +
                    Number(
                        sale.fee
                    ),
                0
            );

        const average =
            quantity
                ? revenue / quantity
                : 0;

        const expanded =
            expandedItems.has(
                'sell-' +
                String(tracked.id)
            );

        return `
            <div
                class="tpl8-card"
                data-item-id="${tracked.id}"
            >

                <div class="tpl8-title">

                    <span class="tpl8-title-name">
                        ${esc(tracked.name)}
                    </span>

                    <span class="tpl8-arrow">
                        ${expanded
                            ? '▼'
                            : '▶'}
                    </span>

                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Quantity sold
                    </span>

                    <span class="tpl8-value">
                        ${quantity.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Net received
                    </span>

                    <span class="tpl8-value">
                        ${money(revenue)}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Total fees
                    </span>

                    <span class="tpl8-value">
                        ${money(fees)}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Average net sale
                    </span>

                    <span class="tpl8-value">
                        ${money(average)}
                    </span>
                </div>

                ${
                    expanded
                        ? `
                            <div class="tpl8-history">

                                <div class="tpl8-history-count">
                                    ${sales.length.toLocaleString()}
                                    sale records
                                </div>

                                ${
                                    sales
                                        .slice(0, 100)
                                        .map(
                                            sale => `
                                                <div class="tpl8-record">

                                                    <strong>
                                                        ${esc(
                                                            sale.dateText
                                                        )}
                                                    </strong>

                                                    <br>

                                                    ${sale.quantity}
                                                    ×
                                                    ${money(
                                                        sale.grossUnitPrice
                                                    )}

                                                    <br>

                                                    Net received:
                                                    <strong>
                                                        ${money(
                                                            sale.total
                                                        )}
                                                    </strong>

                                                    ${
                                                        Number(
                                                            sale.fee
                                                        ) > 0
                                                            ? `
                                                                <br>
                                                                <span class="tpl8-muted">
                                                                    Fee:
                                                                    ${money(
                                                                        sale.fee
                                                                    )}
                                                                </span>
                                                            `
                                                            : ''
                                                    }

                                                    <br>

                                                    <span class="tpl8-muted">
                                                        ${esc(
                                                            sale.market
                                                        )}
                                                        · Buyer:
                                                        ${esc(
                                                            sale.buyer
                                                        )}
                                                    </span>

                                                </div>
                                            `
                                        )
                                        .join('')
                                }

                            </div>
                        `
                        : ''
                }

            </div>
        `;
    }

    /* =====================================================
       TRADES PAGE
    ===================================================== */

    function renderTradesPage(body) {
        if (!state.trades.length) {
            body.innerHTML = `
                <div class="tpl8-empty">
                    🤝<br><br>
                    No completed trades imported yet.
                    <br><br>
                    Tap <strong>Trade Sync</strong>.
                </div>
            `;

            return;
        }

        const pending =
            countTradesNeedingDetail();

        body.innerHTML = `
            ${
                tradeDetailAutoLoading
                    ? `
                        <div class="tpl8-trade-loading">
                            🤝
                            <strong>
                                Automatically loading trade contents...
                            </strong>

                            <br><br>

                            The ledger is processing
                            trades one at a time.
                        </div>
                    `
                    : ''
            }

            <div class="tpl8-card">

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Stored trades
                    </span>

                    <span class="tpl8-value">
                        ${state.trades.length.toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Loaded trade contents
                    </span>

                    <span class="tpl8-value">
                        ${(
                            state.trades.length -
                            pending
                        ).toLocaleString()}
                    </span>
                </div>

                <div class="tpl8-stat">
                    <span class="tpl8-label">
                        Waiting to load
                    </span>

                    <span class="tpl8-value">
                        ${pending.toLocaleString()}
                    </span>
                </div>

            </div>

            ${
                state.trades
                    .map(renderTradeCard)
                    .join('')
            }
        `;
    }

    function renderTradeCard(trade) {
        const expanded =
            expandedTrades.has(
                'trade-' +
                trade.id
            );

        const needsDetail =
            tradeNeedsDetail(trade);

        return `
            <div
                class="tpl8-card"
                data-trade-id="${esc(
                    trade.id
                )}"
            >

                <div class="tpl8-title">

                    <span class="tpl8-title-name">

                        <span class="tpl8-trade-player">
                            🤝
                            ${esc(
                                trade.player ||
                                'Unknown player'
                            )}
                        </span>

                        <br>

                        <span
                            class="tpl8-muted"
                            style="font-size:11px"
                        >
                            ${esc(
                                trade.dateText ||
                                formatDate(
                                    trade.timestamp
                                )
                            )}
                        </span>

                    </span>

                    <span class="tpl8-arrow">
                        ${expanded
                            ? '▼'
                            : '▶'}
                    </span>

                </div>

                <div class="tpl8-stat">

                    <span class="tpl8-label">
                        Trade ID
                    </span>

                    <span class="tpl8-value">
                        ${esc(trade.id)}
                    </span>

                </div>

                ${
                    needsDetail
                        ? `
                            <button
                                class="tpl8-btn tpl8-trade-button"
                                data-load-trade="${esc(
                                    trade.id
                                )}"
                            >
                                ${
                                    trade.loaded
                                        ? 'Reload trade contents'
                                        : 'Load trade contents'
                                }
                            </button>
                        `
                        : `
                            <div class="tpl8-trade-section">
                                <div
                                    class="tpl8-muted"
                                    style="font-size:11px"
                                >
                                    ✓ Loaded trade contents
                                </div>
                            </div>
                        `
                }

                ${
                    expanded
                        ? `
                            <div class="tpl8-trade-section">
                                ${
                                    needsDetail
                                        ? `
                                            <span class="tpl8-muted">
                                                Waiting for trade detail loading.
                                            </span>
                                        `
                                        : renderTradeContents(
                                            trade
                                        )
                                }
                            </div>
                        `
                        : ''
                }

            </div>
        `;
    }

    function renderTradeContents(trade) {
        const items =
            trade.items || [];

        const moneyItems =
            trade.money || [];

        const self =
            Number(
                trade.selfUserId
            ) || 0;

        const givenItems =
            self
                ? items.filter(
                      item =>
                          Number(
                              item.userId
                          ) === self
                  )
                : [];

        const receivedItems =
            self
                ? items.filter(
                      item =>
                          Number(
                              item.userId
                          ) !== self
                  )
                : items;

        const givenMoney =
            self
                ? moneyItems.filter(
                      item =>
                          Number(
                              item.userId
                          ) === self
                  )
                : [];

        const receivedMoney =
            self
                ? moneyItems.filter(
                      item =>
                          Number(
                              item.userId
                          ) !== self
                  )
                : moneyItems;

        let html = '';

        if (self) {
            html += `
                <div class="tpl8-trade-side">

                    <div class="tpl8-trade-side-title">
                        YOU GAVE
                    </div>

                    ${
                        givenItems
                            .map(
                                item => `
                                    <div class="tpl8-trade-item">
                                        <span>
                                            ${esc(
                                                item.name
                                            )}
                                        </span>

                                        <strong>
                                            ×
                                            ${Number(
                                                item.quantity
                                            ).toLocaleString()}
                                        </strong>
                                    </div>
                                `
                            )
                            .join('')
                    }

                    ${
                        givenMoney
                            .map(
                                item => `
                                    <div class="tpl8-trade-money">
                                        <span>
                                            Cash
                                        </span>

                                        <strong>
                                            ${money(
                                                item.amount
                                            )}
                                        </strong>
                                    </div>
                                `
                            )
                            .join('')
                    }

                    ${
                        !givenItems.length &&
                        !givenMoney.length
                            ? `
                                <div class="tpl8-muted">
                                    Nothing detected.
                                </div>
                            `
                            : ''
                    }

                </div>

                <div class="tpl8-trade-side">

                    <div class="tpl8-trade-side-title">
                        RECEIVED FROM
                        ${esc(
                            trade.player ||
                            'PLAYER'
                        )}
                    </div>

                    ${
                        receivedItems
                            .map(
                                item => `
                                    <div class="tpl8-trade-item">
                                        <span>
                                            ${esc(
                                                item.name
                                            )}
                                        </span>

                                        <strong>
                                            ×
                                            ${Number(
                                                item.quantity
                                            ).toLocaleString()}
                                        </strong>
                                    </div>
                                `
                            )
                            .join('')
                    }

                    ${
                        receivedMoney
                            .map(
                                item => `
                                    <div class="tpl8-trade-money">
                                        <span>
                                            Cash
                                        </span>

                                        <strong>
                                            ${money(
                                                item.amount
                                            )}
                                        </strong>
                                    </div>
                                `
                            )
                            .join('')
                    }

                    ${
                        !receivedItems.length &&
                        !receivedMoney.length
                            ? `
                                <div class="tpl8-muted">
                                    Nothing detected.
                                </div>
                            `
                            : ''
                    }

                </div>
            `;
        } else {
            html +=
                items.length
                    ? items
                          .map(
                              item => `
                                  <div class="tpl8-trade-item">
                                      <span>
                                          ${esc(
                                              item.name
                                          )}
                                      </span>

                                      <strong>
                                          ×
                                          ${Number(
                                              item.quantity
                                          ).toLocaleString()}
                                      </strong>
                                  </div>
                              `
                          )
                          .join('')
                    : `
                        <div class="tpl8-muted">
                            No item records detected.
                        </div>
                    `;

            html += moneyItems
                .map(
                    item => `
                        <div class="tpl8-stat">

                            <span class="tpl8-label">
                                Money
                            </span>

                            <span class="tpl8-value">
                                ${money(
                                    item.amount
                                )}
                            </span>

                        </div>
                    `
                )
                .join('');
        }

        html += `
            <div
                class="tpl8-muted"
                style="margin-top:12px;font-size:11px"
            >
                Loaded trades participate in FIFO P&amp;L.
            </div>
        `;

        return html;
    }

    /* =====================================================
       P&L PAGE
    ===================================================== */

    function pnlClass(value) {
        return Number(value) > 0
            ? 'tpl8-pnl-positive'
            : Number(value) < 0
                ? 'tpl8-pnl-negative'
                : 'tpl8-pnl-neutral';
    }

    function pnlValue(value) {
        const number =
            Number(value) || 0;

        return (
            (number > 0 ? '+' : '') +
            money(number)
        );
    }

    function renderPnlPage(body) {
        if (!state.tracked.length) {
            body.innerHTML = `
                <div class="tpl8-empty">
                    📊<br><br>
                    Track an item first.
                </div>
            `;

            return;
        }

        const results =
            state.tracked.map(
                calculateFifoPnl
            );

        const incomplete =
            results.filter(
                result =>
                    !result.complete
            );

        const ignoredTrades =
            results.some(
                result =>
                    result.ignoredTrades > 0
            );

        body.innerHTML = `
            ${
                incomplete.length
                    ? `
                        <div class="tpl8-pnl-warning">
                            ⚠️
                            <strong>
                                Incomplete cost basis
                            </strong>

                            <br><br>

                            ${
                                incomplete.length
                            }
                            tracked item${
                                incomplete.length === 1
                                    ? ''
                                    : 's'
                            }
                            still has sales that cannot
                            be matched to recorded purchases
                            or loaded trade acquisitions.
                        </div>
                    `
                    : `
                        <div class="tpl8-pnl-complete">
                            ✓ FIFO cost basis matched all
                            recorded sales against available
                            acquisitions.
                        </div>
                    `
            }

            ${
                ignoredTrades
                    ? `
                        <div class="tpl8-pnl-warning">
                            🤝
                            <strong>
                                Some trades are not included yet
                            </strong>

                            <br><br>

                            Trade records without loaded
                            contents are ignored by FIFO
                            until loaded.
                        </div>
                    `
                    : ''
            }

            ${
                results
                    .map(renderPnlCard)
                    .join('')
            }
        `;
    }

    function renderPnlCard(result) {
        const tracked =
            state.tracked.find(
                item =>
                    norm(item.name) ===
                    norm(result.itemName)
            );

        const id =
            tracked?.id;

        const expanded =
            expandedItems.has(
                'pnl-' +
                String(id)
            );

        const quantities = [
            [
                'Quantity bought',
                result.totalPurchased
            ],
            [
                'Market/Bazaar bought',
                result.marketPurchased
            ],
            [
                'Trade acquired',
                result.tradePurchased
            ],
            [
                'Gifted',
                result.giftPurchased
            ],
            [
                'Parcels opened',
                result.parcelPurchased
            ],
            [
                'Travel bought',
                result.travelPurchased
            ],
            [
                'Quantity sold',
                result.totalSold
            ],
            [
                'Market/Bazaar sold',
                result.marketSold
            ],
            [
                'Trade disposed',
                result.tradeSold
            ],
            [
                'Used / consumed',
                result.consumedQty
            ]
        ].concat(
            result.consumedOverdose
                ? [['of which overdoses', result.consumedOverdose]]
                : [],
            result.armoryQty
                ? [['Used from faction armory (not counted)', result.armoryQty]]
                : [],
            result.sentQty
                ? [['Sent to players', result.sentQty]]
                : []
        );

        return `
            <div
                class="tpl8-card"
                data-item-id="${esc(
                    String(id)
                )}"
            >

                <div class="tpl8-title">

                    <span class="tpl8-title-name">
                        ${esc(
                            result.itemName
                        )}
                    </span>

                    <span class="tpl8-arrow">
                        ${expanded
                            ? '▼'
                            : '▶'}
                    </span>

                </div>

                ${
                    [
                        [
                            'Realized P&L',
                            result.realizedPnl
                        ],
                        [
                            'Unrealized P&L',
                            result.tmvMissing ? null : result.unrealizedPnl
                        ],
                        [
                            'Total P&L',
                            result.tmvMissing ? null : result.totalPnl
                        ]
                    ]
                        .map(
                            ([label, value]) => `
                                <div class="tpl8-stat">

                                    <span class="tpl8-label">
                                        ${label}
                                    </span>

                                    <span
                                        class="tpl8-value ${value === null ? '' : pnlClass(
                                            value
                                        )}"
                                    >
                                        ${value === null ? 'TMV unavailable' : pnlValue(
                                            value
                                        )}
                                    </span>

                                </div>
                            `
                        )
                        .join('')
                }

                <div class="tpl8-pnl-section">

                    ${
                        quantities
                            .map(
                                ([label, value]) => `
                                    <div class="tpl8-stat">

                                        <span class="tpl8-label">
                                            ${label}
                                        </span>

                                        <span class="tpl8-value">
                                            ${Number(
                                                value
                                            ).toLocaleString()}
                                        </span>

                                    </div>
                                `
                            )
                            .join('')
                    }

                </div>

                ${
                    result.tradePurchased
                        ? `
                            <div class="tpl8-pnl-section">

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Trade acquisition cost
                                    </span>

                                    <span class="tpl8-value">
                                        ${money(
                                            result.tradePurchaseCost
                                        )}
                                    </span>
                                </div>

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Estimated trade acquisition
                                    </span>

                                    <span class="tpl8-value tpl8-estimated">
                                        ${result.estimatedTradePurchases.toLocaleString()}
                                        units
                                    </span>
                                </div>

                            </div>
                        `
                        : ''
                }

                ${
                    result.tradeSold
                        ? `
                            <div class="tpl8-pnl-section">

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Trade revenue
                                    </span>

                                    <span class="tpl8-value">
                                        ${money(
                                            result.tradeSaleRevenue
                                        )}
                                    </span>
                                </div>

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Estimated trade revenue
                                    </span>

                                    <span class="tpl8-value tpl8-estimated">
                                        ${result.estimatedTradeSales.toLocaleString()}
                                        units
                                    </span>
                                </div>

                            </div>
                        `
                        : ''
                }

                <div class="tpl8-pnl-section">

                    ${
                        [
                            [
                                'FIFO cost of sales',
                                result.fifoCost
                            ],
                            [
                                'Net sale revenue',
                                result.matchedRevenue
                            ],
                            [
                                'Fees paid',
                                result.totalFees
                            ],
                            [
                                useMode() === 'cost'
                                    ? 'Consumed cost (in P&L)'
                                    : 'Consumed cost (not in P&L)',
                                result.consumedCost
                            ]
                        ].concat(
                            result.sentQty
                                ? [[
                                    useMode() === 'cost'
                                        ? 'Sent cost (in P&L)'
                                        : 'Sent cost (not in P&L)',
                                    result.sentCost
                                ]]
                                : []
                        )
                            .map(
                                ([label, value]) => `
                                    <div class="tpl8-stat">

                                        <span class="tpl8-label">
                                            ${label}
                                        </span>

                                        <span class="tpl8-value">
                                            ${money(
                                                value
                                            )}
                                        </span>

                                    </div>
                                `
                            )
                            .join('')
                    }

                </div>

                <div class="tpl8-pnl-section">

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            Remaining quantity
                        </span>

                        <span class="tpl8-value">
                            ${result.remainingQuantity.toLocaleString()}
                        </span>
                    </div>

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            Remaining FIFO cost
                        </span>

                        <span class="tpl8-value">
                            ${money(
                                result.remainingCost
                            )}
                        </span>
                    </div>

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            From player trades
                        </span>

                        <span class="tpl8-value">
                            ${result.remainingTradeQuantity.toLocaleString()}
                        </span>
                    </div>

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            Current TMV
                        </span>

                        <span class="tpl8-value">
                            ${result.tmvMissing ? 'N/A' : money(
                                result.tmv
                            )}
                        </span>
                    </div>

                    <div class="tpl8-stat">
                        <span class="tpl8-label">
                            Current inventory value
                        </span>

                        <span class="tpl8-value">
                            ${result.tmvMissing ? 'N/A' : money(
                                result.currentValue
                            )}
                        </span>
                    </div>

                </div>

                ${
                    result.unmatchedSold
                        ? `
                            <div class="tpl8-pnl-section">

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Unmatched sold
                                    </span>

                                    <span class="tpl8-value">
                                        ${result.unmatchedSold.toLocaleString()}
                                    </span>
                                </div>

                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Unmatched revenue
                                    </span>

                                    <span class="tpl8-value">
                                        ${money(
                                            result.unmatchedRevenue
                                        )}
                                    </span>
                                </div>

                            </div>
                        `
                        : ''
                }

                ${
                    result.unmatchedUse
                        ? `
                            <div class="tpl8-pnl-section">
                                <div class="tpl8-stat">
                                    <span class="tpl8-label">
                                        Unmatched used
                                    </span>

                                    <span class="tpl8-value">
                                        ${result.unmatchedUse.toLocaleString()}
                                    </span>
                                </div>
                            </div>
                        `
                        : ''
                }

                ${
                    expanded
                        ? `
                            <div class="tpl8-history">

                                <div class="tpl8-history-count">
                                    FIFO sale matching
                                </div>

                                ${
                                    result.saleMatches
                                        .slice(0, 100)
                                        .map(
                                            match => `
                                                <div class="tpl8-record">

                                                    <strong>
                                                        ${esc(
                                                            match.sell.dateText
                                                        )}
                                                    </strong>

                                                    <br>

                                                    Sold:
                                                    ${match.sell.quantity}

                                                    <br>

                                                    FIFO matched:
                                                    ${match.matchedQuantity}

                                                    <br>

                                                    FIFO cost:
                                                    ${money(
                                                        match.fifoCost
                                                    )}

                                                    <br>

                                                    Net revenue:
                                                    ${money(
                                                        match.revenue
                                                    )}

                                                    <br>

                                                    <strong>
                                                        P&amp;L:
                                                        ${pnlValue(
                                                            match.pnl
                                                        )}
                                                    </strong>

                                                </div>
                                            `
                                        )
                                        .join('')
                                }

                            </div>
                        `
                        : ''
                }

                <div
                    class="tpl8-muted"
                    style="margin-top:10px;font-size:11px"
                >
                    Loaded trades:
                    ${result.loadedTrades}
                    ·
                    Unloaded/ignored trades:
                    ${result.ignoredTrades}
                </div>

            </div>
        `;
    }

    /* =====================================================
       SYNC ALL / API SAFETY
    ===================================================== */

    function getSyncAllRemaining() {
        const last = Number(
            localStorage.getItem(SYNC_ALL_LAST_KEY) || 0
        );

        if (!last) return 0;

        return Math.max(
            0,
            SYNC_ALL_COOLDOWN - (Date.now() - last)
        );
    }

    function setSyncAllButtonState(disabled, label = null) {
        if (!drawer) return;

        const button = drawer.querySelector('#tpl8-sync-all');
        if (!button) return;

        button.disabled = Boolean(disabled);
        button.style.opacity = disabled ? '0.55' : '1';

        if (label !== null) {
            button.textContent = label;
        }
    }

    function setSyncControlsDisabled(disabled) {
        if (!drawer) return;

        const ids = [
            '#tpl8-sync',
            '#tpl8-history',
            '#tpl8-sell-sync',
            '#tpl8-sell-history',
            '#tpl8-trade-sync',
            '#tpl8-trade-history',
            '#tpl8-receive-sync',
            '#tpl8-receive-history',
            '#tpl8-travel-sync',
            '#tpl8-travel-history',
            '#tpl8-parcel-sync',
            '#tpl8-use-sync'
        ];

        for (const id of ids) {
            const button = drawer.querySelector(id);
            if (!button) continue;
            button.disabled = Boolean(disabled);
            button.style.opacity = disabled ? '0.55' : '1';
        }
    }

    function startSyncAllCooldown() {
        clearInterval(syncAllCooldownTimer);

        const tick = () => {
            const remaining = getSyncAllRemaining();

            if (remaining <= 0) {
                clearInterval(syncAllCooldownTimer);
                syncAllCooldownTimer = null;
                setSyncAllButtonState(false, '🔄 Sync All');
                return;
            }

            const seconds = Math.ceil(remaining / 1000);
            setSyncAllButtonState(
                true,
                `⏳ Sync All (${seconds}s)`
            );
        };

        tick();
        syncAllCooldownTimer = setInterval(tick, 1000);
    }

    async function syncAll() {
        if (syncAllRunning) return;

        const remaining = getSyncAllRemaining();

        if (remaining > 0) {
            setStatus(
                `Sync All cooldown: ${Math.ceil(remaining / 1000)}s remaining`
            );
            startSyncAllCooldown();
            return;
        }

        if (!state.tracked.length) {
            setStatus('Track at least one item first');
            return;
        }

        syncAllRunning = true;
        localStorage.setItem(
            SYNC_ALL_LAST_KEY,
            String(Date.now())
        );
        setSyncControlsDisabled(true);
        setSyncAllButtonState(true, '⏳ Sync All');
        startSyncAllCooldown();

        const before = {
            purchases: state.purchases.length,
            sells: state.sells.length,
            trades: state.trades.length,
            receives: state.itemReceives.length,
            travelPurchases: state.travelPurchases.length,
            parcelOpens: state.parcelOpens.length,
            itemUses: state.itemUses.length
        };

        const steps = [
            ['Purchases', syncPurchases],
            ['Purchase history', syncHistoricalPurchases],
            ['Sales', syncSells],
            ['Sale history', syncHistoricalSells],
            ['Trades', syncTrades],
            ['Trade history', syncHistoricalTrades],
            ['Item receives', syncItemReceives],
            ['Item receive history', syncHistoricalItemReceives],
            ['Travel purchases', syncTravelPurchases],
            ['Travel purchase history', syncHistoricalTravelPurchases],
            ['Parcel opens', syncParcelOpens],
            ['Item uses', syncItemUses]
        ];

        try {
            for (let i = 0; i < steps.length; i++) {
                const [label, fn] = steps[i];
                setStatus(
                    `Sync All ${i + 1}/${steps.length}: ${label}...`
                );
                await fn();
            }

            setStatus('Sync All: loading trade details...');
            await autoLoadTradeDetails();

            saveState();
            render();

            const added = {
                purchases: Math.max(0, state.purchases.length - before.purchases),
                sells: Math.max(0, state.sells.length - before.sells),
                trades: Math.max(0, state.trades.length - before.trades),
                receives: Math.max(0, state.itemReceives.length - before.receives),
                travelPurchases: Math.max(0, state.travelPurchases.length - before.travelPurchases),
                parcelOpens: Math.max(0, state.parcelOpens.length - before.parcelOpens),
                itemUses: Math.max(0, state.itemUses.length - before.itemUses)
            };

            setStatus(
                `Sync All complete — +${added.purchases} purchases · +${added.sells} sales · +${added.trades} trades · +${added.receives} receives · +${added.travelPurchases} travel · +${added.parcelOpens} parcel items · +${added.itemUses} uses`
            );
        } catch (e) {
            console.error('[TPL8] Sync All', e);
            setStatus('Sync All stopped: ' + e.message);
        } finally {
            syncAllRunning = false;
            setSyncControlsDisabled(false);
            startSyncAllCooldown();
        }
    }

    /* =====================================================
       COPY
    ===================================================== */

    async function copyLedger() {
        let text =
            'TORN PURCHASE LEDGER\n\n';

        for (const tracked of state.tracked) {
            const purchases =
                state.purchases.filter(
                    purchase =>
                        norm(
                            purchase.itemName
                        ) ===
                        norm(
                            tracked.name
                        )
                );

            text +=
                `${tracked.name}\n`;

            text +=
                `Quantity: ${purchases.reduce(
                    (sum, purchase) =>
                        sum +
                        Number(
                            purchase.quantity
                        ),
                    0
                )}\n`;

            text +=
                `Total: ${money(
                    purchases.reduce(
                        (sum, purchase) =>
                            sum +
                            Number(
                                purchase.total
                            ),
                        0
                    )
                )}\n\n`;
        }

        try {
            await navigator.clipboard.writeText(
                text
            );
        } catch (_) {
            const textarea =
                document.createElement(
                    'textarea'
                );

            textarea.value = text;

            document.body.appendChild(
                textarea
            );

            textarea.select();

            document.execCommand(
                'copy'
            );

            textarea.remove();
        }

        setStatus(
            'Ledger copied'
        );
    }

    /* =====================================================
       INIT
    ===================================================== */

    async function init() {
        loadState();

        if (
            !Array.isArray(
                state.trades
            )
        ) {
            state.trades = [];
        }

        let migrate = false;

        for (
            const trade of
            state.trades
        ) {
            if (
                trade &&
                trade.loaded &&
                Number(
                    trade.parserVersion
                ) !==
                    TRADE_PARSER_VERSION
            ) {
                trade.loaded = false;
                migrate = true;
            }
        }

        if (migrate) {
            saveState();
        }

        createUI();

        /*
         * Start the persistent UI watchdog.
         * This is the important v8.2.3 fix.
         */
        startUIWatchdog();

        try {
            await loadCatalogue();

            let frozen = false;
            for (const receive of [...state.itemReceives, ...state.parcelOpens]) {
                if (!(Number(receive.tmvAtReceive) > 0)) {
                    const tmv = currentTmvFor(receive.itemId);
                    if (tmv > 0) {
                        receive.tmvAtReceive = tmv;
                        frozen = true;
                    }
                }
            }
            if (frozen) saveState();

            setStatus(
                `${state.tracked.length} tracked · ${state.trades.length} trades`
            );

            setTimeout(
                autoLoadTradeDetails,
                500
            );
        } catch (e) {
            console.error(
                '[TPL8] Catalogue',
                e
            );

            setStatus(
                'Catalogue error: ' +
                e.message
            );
        }

        setInterval(
            () => {
                if (
                    state.tracked.length &&
                    !pricing
                ) {
                    refreshPrices();
                }
            },
            PRICE_INTERVAL
        );
    }

    if (document.body) {
        init();
    } else {
        window.addEventListener(
            'DOMContentLoaded',
            init,
            { once: true }
        );
    }

})();