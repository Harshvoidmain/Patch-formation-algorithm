import sys

# Configure stdout to print UTF-8 correctly
sys.stdout.reconfigure(encoding='utf-8')

query = sys.argv[1].lower() if len(sys.argv) > 1 else "corner"

with open("paper_text.txt", "r", encoding="utf-8") as f:
    lines = f.readlines()

print(f"Searching for '{query}'...")
for i, line in enumerate(lines):
    if query in line.lower():
        print(f"Line {i+1}: {line.strip()}")
        # print context
        start = max(0, i - 2)
        end = min(len(lines), i + 3)
        for j in range(start, end):
            if j != i:
                print(f"  [{j+1}] {lines[j].strip()}")
        print("-" * 40)
