import OAI.LinearAlgebra.SpectralBooks.NonscalarGateBound
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Consequences
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Surplus

/-! # Rectangular nonscalar gate lower bounds

For an `a × b` by `b × c` product over a field, every formal circuit with division has
at least `⌈exp (U (log a) (log c) (log b)) / 2⌉` nonscalar gates, and hence at least
`⌈(a b c) ^ (3/4) / 2⌉`. Here `U` is the exact rectangular exponent benchmark of
`MatrixExponent.Rectangle`.

The rank bound transfers a rank decomposition of the cyclic tensor `matrixTensor F b c a`
of this file's development to a weighted decomposition of `ordinary F a c b`, whose
asymptotic rank is `exp (U (log a) (log c) (log b))` by `Rectangle.Consequences.minimum`.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication
open MatrixExponent.Rectangle

variable {F : Type*} [Field F] {a b c : ℕ}

/-- A rank decomposition of the cyclic tensor is a weighted decomposition of the
all-ones `(a, c, b)` weight after swapping the output coordinate. -/
theorem weightedRankLE_of_rankAtMost {r : ℕ}
    (h : Foundation.Tensor.RankAtMost (matrixTensor F b c a) r) :
    WeightedRankLE (ordinary F a c b) r := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨A, B, fun l z => C l z.swap, ?_⟩
  intro x y z
  simpa [ordinary, matrixTensor, Foundation.Tensor.matrixCoefficients, Foundation.Tensor.rankOne,
    and_comm, and_left_comm, eq_comm] using (congrFun (congrFun (congrFun h x) y) z.swap).symm

/-- The rank of the `a × b` by `b × c` matrix multiplication tensor is at least
`exp (U (log a) (log c) (log b))`. -/
theorem exp_U_le_tensorRank (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Real.exp (U (Real.log a) (Real.log c) (Real.log b)) ≤ tensorRank (matrixTensor F b c a) := by
  have hw := weightedRankLE_of_rankAtMost (rankAtMost_tensorRank (matrixTensor F b c a))
  have h := hw.border.asymptotic ha hc hb
  rwa [(Consequences.minimum F ha hc hb).1] at h

/-- The benchmark is at least the volume bound: `exp U ≥ (a b c) ^ (3/4)`. -/
theorem volume_le_exp_U (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ((a * b * c : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤ Real.exp (U (Real.log a) (Real.log c) (Real.log b)) := by
  classical
  have hne : (Sparse.support (ordinary F a c b)).Nonempty :=
    ⟨(⟨0, ha⟩, ⟨0, hc⟩, ⟨0, hb⟩), by simp [Sparse.support, ordinary]⟩
  have hs : supportSize (ordinary F a c b) = a * b * c := by
    simp [supportSize, ordinary, Finset.card_univ]
    ring
  have h := Consequences.support_lower (F := F) hne
  rw [hs, (Consequences.minimum F ha hc hb).1] at h
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ (Sparse.premium (Sparse.support (ordinary F a c b)) / 4) :=
    Real.one_le_rpow (by norm_num) (by linarith [Sparse.premium_nonneg _ hne])
  have hv : (0 : ℝ) ≤ ((a * b * c : ℕ) : ℝ) ^ (3 / 4 : ℝ) := by positivity
  nlinarith

variable {P : RationalMatrixAlgorithm F a b c}

/-- Rectangular Corollary 1.2: at least `⌈exp (U (log a) (log c) (log b)) / 2⌉`
nonscalar gates for an `a × b` by `b × c` product. -/
theorem nonscalarCount_benchmark_ceil_lower (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : P.Correct) :
    ⌈Real.exp (U (Real.log a) (Real.log c) (Real.log b)) / 2⌉₊ ≤ P.program.nonscalarCount := by
  rw [Nat.ceil_le]
  have h₁ := exp_U_le_tensorRank (AlgebraicClosure F) ha hb hc
  have h₂ : (tensorRank (matrixTensor (AlgebraicClosure F) b c a) : ℝ) ≤
      ((2 * P.program.nonscalarCount : ℕ) : ℝ) := by
    exact_mod_cast algebraicClosure_rank_le_twice_nonscalarCount h
  push_cast at h₂
  linarith

/-- Volume form: at least `⌈(a b c) ^ (3/4) / 2⌉` nonscalar gates. -/
theorem nonscalarCount_volume_ceil_lower (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : P.Correct) :
    ⌈((a * b * c : ℕ) : ℝ) ^ (3 / 4 : ℝ) / 2⌉₊ ≤ P.program.nonscalarCount := by
  refine le_trans (Nat.ceil_mono ?_) (nonscalarCount_benchmark_ceil_lower ha hb hc h)
  have := volume_le_exp_U F ha hb hc
  linarith

end SpectralBooks
end LinearAlgebra
end OAI
