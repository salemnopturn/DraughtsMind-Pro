const m = { from: 1, to: 2, path: [3, 4], captured: [5, 6], capKings: 1, promo: true, score: 0 };
function cloneMv(m) {
    if (!m) return null;
    return {
        from: m.from, to: m.to,
        path: m.path ? m.path.slice() : [],
        captured: m.captured ? m.captured.slice() : [],
        capKings: m.capKings || 0,
        promo: m.promo || false,
        score: m.score || 0
    };
}
console.log(cloneMv(m));
