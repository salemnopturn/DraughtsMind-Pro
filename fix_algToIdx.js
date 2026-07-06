const fs = require('fs');
let code = fs.readFileSync('renderer/scripts/app.js', 'utf8');

const oldAlgToIdx = `    function algToIdx(sq) {
        if (!sq || sq.length < 2) return -1;
        const c = sq.charCodeAt(0) - 97, r = parseInt(sq[1]) - 1;
        if (c < 0 || c > 7 || r < 0 || r > 7) return -1;
        return r * 8 + c;
    }`;

const newAlgToIdx = `    function algToIdx(sq) {
        if (!sq || sq.length < 2) return -1;
        const charCode = sq.toLowerCase().charCodeAt(0);
        const c = charCode - 97, r = parseInt(sq[1]) - 1;
        if (c < 0 || c > 7 || r < 0 || r > 7) return -1;
        return r * 8 + c;
    }`;

if (code.includes(oldAlgToIdx)) {
    code = code.replace(oldAlgToIdx, newAlgToIdx);
    fs.writeFileSync('renderer/scripts/app.js', code);
    console.log("algToIdx updated successfully!");
} else {
    console.log("Could not find old algToIdx!");
}
