const fs = require('fs');
let code = fs.readFileSync('renderer/scripts/app.js', 'utf8');

// We comment out the block `if (isCPU&&cfgMode!==MODE_SAND&&!isAnalysisOn) return;`
code = code.replace(
    /if \(isCPU&&cfgMode!==MODE_SAND&&!isAnalysisOn\) return;/g,
    `// [ENG-V32-FLEX] Allow user to create variations freely even during CPU's turn, overriding it\n        // if (isCPU&&cfgMode!==MODE_SAND&&!isAnalysisOn) return;`
);

fs.writeFileSync('renderer/scripts/app.js', code);
console.log('Fixed click blocking!');
