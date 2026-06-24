import pypdf
import os

pdf_path = r"C:\Users\harsh\.gemini\antigravity\brain\f41a5221-4837-4acf-b148-a39c0d0af995\media__1782330907118.pdf"
output_path = "paper_text.txt"

print(f"Extracting {pdf_path} to {output_path}...")
if not os.path.exists(pdf_path):
    print("Error: PDF file does not exist at path:", pdf_path)
    exit(1)

reader = pypdf.PdfReader(pdf_path)
print(f"Number of pages: {len(reader.pages)}")

with open(output_path, "w", encoding="utf-8") as f:
    for idx, page in enumerate(reader.pages):
        f.write(f"\n--- PAGE {idx+1} ---\n")
        f.write(page.extract_text())

print("Extraction complete.")
