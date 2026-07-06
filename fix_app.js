const fs = require('fs');
const book = fs.readFileSync('engine/book.js', 'utf8');
const app = fs.readFileSync('renderer/scripts/app.js', 'utf8');

const parsePDNLineMatch = book.match(/function parsePDNLine\([\s\S]*?(?=function bookAddLine)/);
const bookAddLineMatch = book.match(/function bookAddLine\([\s\S]*?(?=function buildOpeningBook)/);

if (!parsePDNLineMatch || !bookAddLineMatch) {
    console.error("Functions not found in book.js");
    process.exit(1);
}

const injectedCode = parsePDNLineMatch[0] + "\n    " + bookAddLineMatch[0] + "\n";

// Inject right before buildOpeningBook
const appFixed = app.replace('    function buildOpeningBook() {', injectedCode + '    function buildOpeningBook() {');

fs.writeFileSync('renderer/scripts/app.js', appFixed, 'utf8');
console.log("Functions injected into app.js successfully.");
