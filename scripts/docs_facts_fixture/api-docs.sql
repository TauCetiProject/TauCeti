CREATE TABLE modules (
  name TEXT PRIMARY KEY,
  source_url TEXT
);
CREATE TABLE name_info (
  module_name TEXT NOT NULL,
  position INTEGER NOT NULL,
  kind TEXT,
  name TEXT NOT NULL,
  type BLOB NOT NULL,
  sorried INTEGER NOT NULL,
  render INTEGER NOT NULL,
  PRIMARY KEY (module_name, position),
  FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE
);
CREATE TABLE declaration_markdown_docstrings (
  module_name TEXT NOT NULL,
  position INTEGER NOT NULL,
  text TEXT NOT NULL,
  PRIMARY KEY (module_name, position),
  FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE
);
CREATE TABLE declaration_ranges (
  module_name TEXT NOT NULL,
  position INTEGER NOT NULL,
  start_line INTEGER NOT NULL,
  start_column INTEGER NOT NULL,
  start_utf16 INTEGER NOT NULL,
  end_line INTEGER NOT NULL,
  end_column INTEGER NOT NULL,
  end_utf16 INTEGER NOT NULL,
  PRIMARY KEY (module_name, position),
  FOREIGN KEY (module_name) REFERENCES modules(name) ON DELETE CASCADE
);
INSERT INTO modules (name, source_url) VALUES ('Demo.A', 'https://github.com/TauCetiProject/TauCeti/blob/937b7d87c3dec2f992a6791337a04a2cafd0d243/Demo/A.lean');
INSERT INTO modules (name, source_url) VALUES ('Demo.Empty', 'https://github.com/TauCetiProject/TauCeti/blob/937b7d87c3dec2f992a6791337a04a2cafd0d243/Demo/Empty.lean');
INSERT INTO modules (name, source_url) VALUES ('Demo.Sub.B', 'https://github.com/TauCetiProject/TauCeti/blob/937b7d87c3dec2f992a6791337a04a2cafd0d243/Demo/Sub/B.lean');
INSERT INTO modules (name, source_url) VALUES ('DemoDocs', NULL);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 1, 'theorem', 'Demo.alpha', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 2, 'structure', 'Demo.Point', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 4, 'constructor', 'Demo.Point.mk', X'', 0, 0);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 8, 'definition', 'Demo.Point.x', X'', 0, 0);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 9, 'definition', 'Demo.Point.y', X'', 0, 0);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 10, 'definition', 'Demo.instReprPoint.repr', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 11, 'instance', 'Demo.instReprPoint', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 12, 'definition', 'Demo.instDecidableEqPoint.decEq', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 13, 'instance', 'Demo.instDecidableEqPoint', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 14, 'inductive', 'Demo.Colour', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 15, 'constructor', 'Demo.Colour.red', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 16, 'constructor', 'Demo.Colour.green', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 19, 'instance', 'Demo.instInhabitedColour', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 20, 'instance', 'Demo.instInhabitedPoint', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 21, 'definition', 'Demo.undocumented', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 22, 'class', 'Demo.Shiny', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 24, 'constructor', 'Demo.Shiny.mk', X'', 0, 0);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 27, 'definition', 'Demo.Shiny.shine', X'', 0, 0);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 28, 'definition', 'Demo.Short', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 29, 'opaque', 'Demo.secret', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.A', 30, 'axiom', 'Demo.demoAxiom', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.Sub.B', 0, 'theorem', 'Demo.Sub.beta', X'', 0, 1);
INSERT INTO name_info (module_name, position, kind, name, type, sorried, render) VALUES ('Demo.Sub.B', 1, 'theorem', 'Demo.Sub.gamma', X'', 0, 1);
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.A', 1, '**Alpha''s theorem.** It states `True`.

A second paragraph.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.A', 2, 'A point.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.A', 8, 'The x coordinate.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.A', 14, 'A colour.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.A', 22, 'A class.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.Sub.B', 0, 'Uses alpha.');
INSERT INTO declaration_markdown_docstrings (module_name, position, text) VALUES ('Demo.Sub.B', 1, 'Proved by `simp`.');
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 0, 3, 0, 0, 7, 2, 2);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 1, 13, 0, 0, 16, 31, 31);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 2, 18, 0, 0, 23, 28, 28);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 4, 18, 0, 0, 23, 28, 28);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 8, 21, 2, 2, 21, 3, 3);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 9, 22, 2, 2, 22, 3, 3);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 10, 23, 11, 11, 23, 15, 15);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 11, 23, 11, 11, 23, 15, 15);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 12, 23, 17, 17, 23, 28, 28);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 13, 23, 17, 17, 23, 28, 28);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 14, 25, 0, 0, 29, 20, 20);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 15, 27, 2, 2, 27, 7, 7);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 16, 28, 2, 2, 28, 9, 9);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 19, 29, 11, 11, 29, 20, 20);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 20, 31, 0, 0, 31, 38, 38);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 21, 33, 0, 0, 34, 7, 7);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 22, 36, 0, 0, 38, 17, 17);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 24, 36, 0, 0, 38, 17, 17);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 27, 38, 2, 2, 38, 7, 7);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 28, 40, 0, 0, 40, 19, 19);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 29, 42, 0, 0, 42, 19, 19);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.A', 30, 44, 0, 0, 44, 23, 23);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.Empty', 0, 3, 0, 0, 7, 2, 2);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.Sub.B', 0, 9, 0, 0, 10, 33, 33);
INSERT INTO declaration_ranges (module_name, position, start_line, start_column, start_utf16, end_line, end_column, end_utf16) VALUES ('Demo.Sub.B', 1, 13, 0, 0, 14, 50, 50);
