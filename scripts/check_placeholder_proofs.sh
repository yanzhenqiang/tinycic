#!/bin/bash
# 检查假证明模式脚本
# 用于检测使用无关占位符的"假证明"

echo "=== 检查假证明模式 ==="

# 检查用 CauchySeq.equiv_refl 证明非 Cauchy 目标
echo ""
echo "检查 1: CauchySeq.equiv_refl 滥用（用于非 Cauchy 序列目标）"
if grep -B5 "CauchySeq.equiv_refl" lib/real.x | grep -E "(le\s|lt\s|hasUpperBound|isLub)" > /dev/null; then
    echo "❌ 发现滥用：CauchySeq.equiv_refl 用于非 Cauchy 序列目标"
    grep -B10 "CauchySeq.equiv_refl" lib/real.x | grep -E "def|lemma|theorem" | tail -1
else
    echo "✓ 未发现滥用"
fi

# 检查归纳步骤的 exact ih
echo ""
echo "检查 2: 归纳步骤无进展（exact ih 直接返回归纳假设）"
if grep -A20 "induction.*with" lib/real.x | grep -B2 "exact ih" > /dev/null; then
    echo "❌ 发现无进展的归纳步骤："
    grep -B5 -A2 "exact ih" lib/real.x | head -10
else
    echo "✓ 未发现无进展的归纳步骤"
fi

# 检查 limit_le_of_seq_le 的证明结构
echo ""
echo "检查 3: limit_le_of_seq_le 的证明结构"
if grep -A50 "def limit_le_of_seq_le" lib/real.x | grep "CauchySeq.equiv_refl" > /dev/null; then
    echo "❌ limit_le_of_seq_le 使用了无关的 equiv_refl 占位符"
else
    echo "✓ limit_le_of_seq_le 未使用明显占位符"
fi

# 检查 limit_preserves_le_upper 的证明结构
echo ""
echo "检查 4: limit_preserves_le_upper 的证明结构"
if grep -A50 "def limit_preserves_le_upper" lib/real.x | grep "CauchySeq.equiv_refl" > /dev/null; then
    echo "❌ limit_preserves_le_upper 使用了无关的 equiv_refl 占位符"
else
    echo "✓ limit_preserves_le_upper 未使用明显占位符"
fi

# 检查 limit_preserves_le_least 的证明结构
echo ""
echo "检查 5: limit_preserves_le_least 的归纳步骤"
if grep -A100 "def limit_preserves_le_least" lib/real.x | grep -A30 "| succ n ih =>" | grep "exact ih" > /dev/null; then
    echo "❌ limit_preserves_le_least 的归纳步骤直接返回 ih，未处理 mid 情况"
else
    echo "✓ limit_preserves_le_least 归纳步骤有实质内容"
fi

echo ""
echo "=== 检查完成 ==="
