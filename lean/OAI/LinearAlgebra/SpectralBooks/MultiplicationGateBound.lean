import OAI.LinearAlgebra.SpectralBooks.CircuitRankSpecialization
import OAI.LinearAlgebra.SpectralBooks.SquareExponent
import OAI.LinearAlgebra.SpectralBooks.ExactExponent

/-! # A finite-size lower bound on multiplication and division gates

Every formal circuit with division that multiplies two `n × n` matrices over a field,
for `n ≥ 2`, uses at least `⌈n ^ (9/4) / 2⌉` multiplication and division gates.
Additions and subtractions are free. Multiplication by a field constant is still
counted, because the gate model has no separate scalar multiplication.

The proof combines three existing results: the exact square exponent over the
algebraic closure, the bound of asymptotic rank by rank, and the bound of rank over
the algebraic closure by twice the number of multiplications and divisions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

/-- Over every field, the `n × n` matrix multiplication tensor has rank at least
`n ^ (9/4)` for `n ≥ 2`. -/
theorem rpow_nine_fourths_le_tensorRank (F : Type*) [Field F] {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ ((9 : ℝ) / 4) ≤ tensorRank (matrixTensor F n n n) := by
  have h := rpow_formalOmega_le_asymptoticRank F hn
  rw [square_exponent F] at h
  exact h.trans (asymptoticRank_le_tensorRank _)

variable {F : Type*} [Field F] {n : ℕ} {P : RationalMatrixAlgorithm F n n n}

/-- Twice the number of multiplication and division gates is at least `n ^ (9/4)`. -/
theorem rpow_nine_fourths_le_twice_productQuotientCount (hn : 2 ≤ n) (h : P.Correct) :
    (n : ℝ) ^ ((9 : ℝ) / 4) ≤ 2 * (P.program.productQuotientCount : ℝ) := by
  have h₁ := rpow_nine_fourths_le_tensorRank (AlgebraicClosure F) hn
  have h₂ : (tensorRank (matrixTensor (AlgebraicClosure F) n n n) : ℝ) ≤
      ((2 * P.program.productQuotientCount : ℕ) : ℝ) := by
    exact_mod_cast algebraicClosure_rank_le_twice_productQuotientCount h
  push_cast at h₂
  exact h₁.trans h₂

/-- Corollary 1.2 of the November 24 preprint, with multiplications by constants
counted: at least `⌈n ^ (9/4) / 2⌉` multiplication and division gates. -/
theorem productQuotientCount_ceil_lower (hn : 2 ≤ n) (h : P.Correct) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ P.program.productQuotientCount := by
  rw [Nat.ceil_le]
  have := rpow_nine_fourths_le_twice_productQuotientCount hn h
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
