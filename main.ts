// Driver for markdown-render-speed-02: reads every case from the input
// directory, renders each one with parse() from parse.js, and writes the
// HTML strings in order to html.json in the output directory.
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8')) as { id: string; markdown: string }[];
const html: string[] = [];
for (const c of cases) html.push(parse(c.markdown));
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
