const fs = require('fs');
let code = fs.readFileSync('renderer/scripts/app.js', 'utf8');

// We need to find the `function renderTree()` block.
const regex = /function renderTree\(\) \{[\s\S]*?container\.scrollTop = container\.scrollHeight;\n    \}/;
const match = code.match(regex);
if (match) {
    console.log("Found renderTree!");
} else {
    console.log("Not found!");
}
