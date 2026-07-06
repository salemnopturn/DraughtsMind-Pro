const fs = require('fs');
let code = fs.readFileSync('renderer/scripts/app.js', 'utf8');

// 1. Add cloneMv
code = code.replace(
    /function allocMv\([\s\S]*?return m;\n    }/,
    `$&

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
    }`
);

// 2. Fix generatePDN to use moveStr
code = code.replace(
    /out \+= move2PDN\(main\.move\) \+ ' ';\n            for \(let i = 1; i < curr\.children\.length; i\+\+\) \{\n                const v = curr\.children\[i\];\n                out \+= \`\( \$\{moveNum\}\$\{isWhite \? '\.' : '\.\.\.'\} \$\{move2PDN\(v\.move\)\} \$\{generatePDN\(v, ply \+ 1\)\}\) \`;/g,
    `out += main.moveStr + ' ';\n            for (let i = 1; i < curr.children.length; i++) {\n                const v = curr.children[i];\n                out += \`( \${moveNum}\${isWhite ? '.' : '...'} \${v.moveStr} \${generatePDN(v, ply + 1)}) \`;`
);

// 3. Fix addNodeAndApply
code = code.replace(
    /const n=\{ id:nextNodeId\+\+, parent:currentNode, moveStr:move2Str\(m\), state:newState, children:\[\], move:m \};/,
    `const n={ id:nextNodeId++, parent:currentNode, moveStr:move2Str(m), state:newState, children:[], move: cloneMv(m) };`
);

// 4. Fix autoSelectTablita & Tablita parsing
code = code.replace(
    /state: ns2, children: \[\], move: found \};\n                curr\.children\.push\(nd\); allNodes\[nd\.id\] = nd; curr = nd;/g,
    `state: ns2, children: [], move: cloneMv(found) };\n                curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;`
);
code = code.replace(
    /state: ns2, children: \[\], move: found \};\n            curr\.children\.push\(nd\); allNodes\[nd\.id\] = nd; curr = nd;/g,
    `state: ns2, children: [], move: cloneMv(found) };\n            curr.children.push(nd); allNodes[nd.id] = nd; curr = nd;`
);

// 5. Fix parsePDNTokens
code = code.replace(
    /state: ns2, children: \[\], move: found,\n                                 _var: varDepth > 0 \};/g,
    `state: ns2, children: [], move: cloneMv(found),\n                                 _var: varDepth > 0 };`
);

// 6. Fix search return
code = code.replace(
    /return \{\n            move: bestMove,\n            score: bestScore,\n            depth: reachedDepth,\n            nodes,\n            pv,\n            isBook: false,\n        \};/g,
    `return {\n            move: cloneMv(bestMove),\n            score: bestScore,\n            depth: reachedDepth,\n            nodes,\n            pv: pv.map(cloneMv),\n            isBook: false,\n        };`
);
code = code.replace(
    /return \{ move: bookMove, score: 0, depth: 0, nodes: 0, pv: \[bookMove\], isBook: true \};/g,
    `return { move: cloneMv(bookMove), score: 0, depth: 0, nodes: 0, pv: [cloneMv(bookMove)], isBook: true };`
);
code = code.replace(
    /const res = \{ move: moves\[0\], score: state\.eval\(\), depth: 1, nodes: 1, pv: \[moves\[0\]\], isBook: false \};/g,
    `const res = { move: cloneMv(moves[0]), score: state.eval(), depth: 1, nodes: 1, pv: [cloneMv(moves[0])], isBook: false };`
);
code = code.replace(
    /return \{ move: null, score: -10000, depth: 0, nodes: 0, pv: \[\], isBook: false \};/g,
    `return { move: null, score: -10000, depth: 0, nodes: 0, pv: [], isBook: false };`
);

fs.writeFileSync('renderer/scripts/app.js', code);
console.log('Replacements done!');
