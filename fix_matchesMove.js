const fs = require('fs');
let code = fs.readFileSync('renderer/scripts/app.js', 'utf8');

const oldMatchesMove = `        // Helper to check if a sequence of squares matches a move
        function matchesMove(m, tkSqs) {
            if (tkSqs.length < 2) return false;
            const M = m.captured.length > 0 ? [m.from, ...m.path] : [m.from, m.to];
            if (tkSqs[0] !== M[0]) return false;
            
            // Check if tkSqs is a subsequence of M
            let i = 0, j = 0;
            while (i < tkSqs.length && j < M.length) {
                if (tkSqs[i] === M[j]) i++;
                j++;
            }
            return i === tkSqs.length;
        }`;

const newMatchesMove = `        // Helper to check if a sequence of squares matches a move
        function matchesMove(m, tkSqs) {
            if (tkSqs.length < 2) return false;
            if (tkSqs[0] !== m.from) return false;
            
            if (m.captured.length > 0) {
                // The notation might specify landing squares OR captured pieces.
                // As long as the last square is either m.to OR the last captured piece,
                // and all intermediate squares are part of the capture path or captured pieces, we consider it a match.
                
                // Also, sometimes notations just use from-to even for captures (e.g. c3-e5 instead of c3xe5)
                if (tkSqs.length === 2 && tkSqs[1] === m.to) return true;
                
                // If it specifies the captured piece instead of landing square (e.g. c5-d4 instead of c5-e3)
                if (tkSqs.length === 2 && m.captured.length === 1 && tkSqs[1] === m.captured[0]) return true;

                // Validate sequence
                const validSqs = [...m.path, ...m.captured, m.to];
                for (let i = 1; i < tkSqs.length; i++) {
                    if (!validSqs.includes(tkSqs[i])) return false;
                }
                return true;
            } else {
                return tkSqs[tkSqs.length - 1] === m.to;
            }
        }`;

if (code.includes(oldMatchesMove)) {
    code = code.replace(oldMatchesMove, newMatchesMove);
    fs.writeFileSync('renderer/scripts/app.js', code);
    console.log("matchesMove updated successfully!");
} else {
    console.log("Could not find old matchesMove!");
}
