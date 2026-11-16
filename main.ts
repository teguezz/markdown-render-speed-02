// main.ts — the harness driver for the fast marked drop-in.
//
// Reads every case from <INPUT>/cases.json (a JSON array of
// {"id", "markdown"}), renders each case on its own with parse(), and
// writes the HTML strings, in case order, as a JSON array to
// <OUTPUT>/html.json. INPUT and OUTPUT come from the MAKEFUN_INPUT_DIR
// and MAKEFUN_OUTPUT_DIR environment variables, defaulting to /input
// and /output.

import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

interface CaseInput {
  id: string;
  markdown: string;
}

const inputDir: string = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir: string = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const raw = readFileSync(join(inputDir, 'cases.json'), 'utf8');
const cases = JSON.parse(raw) as CaseInput[];

const html: string[] = new Array(cases.length);
for (let i = 0; i < cases.length; i++) {
  html[i] = parse(cases[i].markdown);
}

mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
