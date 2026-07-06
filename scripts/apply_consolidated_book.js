"use strict";

const fs = require('fs');
const path = require('path');

function updateFile(filePath, bookData, bookDataExt) {
    let content = fs.readFileSync(filePath, 'utf8');

    // Regex to match: const BOOK_DATA = ...; (allowing optional spaces around =)
    const bookDataRegex = /const BOOK_DATA\s*=\s*[\s\S]*?;/;
    if (!bookDataRegex.test(content)) {
        throw new Error(`Could not find const BOOK_DATA in ${filePath}`);
    }
    content = content.replace(bookDataRegex, `const BOOK_DATA =\n        "${bookData}";`);

    // Regex to match: const BOOK_DATA_EXT = ...; (allowing optional spaces around =)
    const bookDataExtRegex = /const BOOK_DATA_EXT\s*=\s*[\s\S]*?;/;
    if (!bookDataExtRegex.test(content)) {
        throw new Error(`Could not find const BOOK_DATA_EXT in ${filePath}`);
    }
    content = content.replace(bookDataExtRegex, `const BOOK_DATA_EXT =\n        "${bookDataExt}";`);

    fs.writeFileSync(filePath, content, 'utf8');
    console.log(`Successfully updated ${filePath}`);
}

function main() {
    const jsonPath = path.join(__dirname, '..', 'consolidated_book.json');
    if (!fs.existsSync(jsonPath)) {
        console.error("consolidated_book.json not found!");
        process.exit(1);
    }
    const bookDataJson = JSON.parse(fs.readFileSync(jsonPath, 'utf8'));
    
    const engineBookPath = path.join(__dirname, '..', 'engine', 'book.js');
    const rendererAppPath = path.join(__dirname, '..', 'renderer', 'scripts', 'app.js');
    
    updateFile(engineBookPath, bookDataJson.BOOK_DATA, bookDataJson.BOOK_DATA_EXT);
    updateFile(rendererAppPath, bookDataJson.BOOK_DATA, bookDataJson.BOOK_DATA_EXT);
    
    console.log("All opening book updates completed successfully!");
}

main();
