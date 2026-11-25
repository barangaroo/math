import OAI.LinearAlgebra.SpectralBooks.QuotientCircuit
import OAI.LinearAlgebra.SpectralBooks.MultiplicationGateBound

/-! # Nonscalar gate lower bound (Corollary 1.2)

A multiplication is *scalar* when one of its two inputs is a field constant, and a
division is scalar when its divisor is a nonzero field constant. Scalar operations,
additions and subtractions are free. Every remaining gate is *nonscalar*.

For a scalar operation the mixed second derivative of the result is a constant
multiple of the mixed second derivative of the other input, so it needs no new
products of first derivatives. The rank bound of `QuotientCircuit` therefore holds
with the nonscalar count in place of the count of all products and quotients.

Consequently every formal circuit with division over a field `F` that multiplies two
`n × n` matrices, for `n ≥ 2`, has at least `⌈n ^ (9/4) / 2⌉` nonscalar gates.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic Foundation MvPolynomial
open scoped BigOperators

noncomputable section

variable {F : Type*} [Field F]

/-- A rational function in the inputs that is a constant of the ground field. -/
def IsFieldConstant {I : Type*} (x : FractionRing (MvPolynomial I F)) : Prop :=
  ∃ c : F, algebraMap (MvPolynomial I F) (FractionRing (MvPolynomial I F)) (C c) = x

namespace RationalProgram

variable {I : Type*}

open Classical in
/-- Number of nonscalar multiplications and divisions. A product with a constant
factor and a quotient by a constant are free. -/
def nonscalarCount : {r : ℕ} → RationalProgram F I r → ℕ
  | _, .nil => 0
  | _, .step p (.mul i j) =>
      if IsFieldConstant (p.value i) ∨ IsFieldConstant (p.value j) then p.nonscalarCount
      else p.nonscalarCount + 1
  | _, .step p _ => p.nonscalarCount
  | _, .quot p _ j =>
      if IsFieldConstant (p.value j) then p.nonscalarCount else p.nonscalarCount + 1

theorem nonscalarCount_le_productQuotientCount {r : ℕ} (p : RationalProgram F I r) :
    p.nonscalarCount ≤ p.productQuotientCount := by
  induction p with
  | nil => exact le_rfl
  | step p g ih =>
    cases g <;> simp only [nonscalarCount, productQuotientCount] <;> try exact ih
    split_ifs <;> omega
  | quot p i j ih =>
    simp only [nonscalarCount, productQuotientCount]
    split_ifs <;> omega

end RationalProgram

variable {K A B : Type*} [Field K]

/-- Local copy of the expansion predicate of `QuotientCircuit`, which is private there. -/
private def Expands {n : ℕ} (u : Fin n → A → K) (v : Fin n → B → K) (H : A → B → K) : Prop :=
  ∃ c : Fin n → K, ∀ x y, H x y = ∑ t, u t x * v t y * c t

private theorem expands_zero {n : ℕ} (u : Fin n → A → K) (v : Fin n → B → K) :
    Expands u v 0 :=
  ⟨0, by simp⟩

private theorem expands_add {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G : A → B → K} (hH : Expands u v H) (hG : Expands u v G) : Expands u v (H + G) := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  exact ⟨c + d, by simp [Pi.add_apply, mul_add, Finset.sum_add_distrib, hc, hd]⟩

private theorem expands_sub {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G : A → B → K} (hH : Expands u v H) (hG : Expands u v G) : Expands u v (H - G) := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  exact ⟨c - d, by simp [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, hc, hd]⟩

private theorem expands_smul {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H : A → B → K} (hH : Expands u v H) (s : K) : Expands u v (fun x y => s * H x y) := by
  obtain ⟨c, hc⟩ := hH
  refine ⟨fun t => s * c t, fun x y => ?_⟩
  simp only [hc, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

private theorem expands_insert {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H : A → B → K} (hH : Expands u v H) (a : A → K) (b : B → K) :
    Expands (Fin.cons a u) (Fin.cons b v) H := by
  obtain ⟨c, hc⟩ := hH
  exact ⟨Fin.cons 0 c, by simp [Fin.sum_univ_succ, hc]⟩

private theorem expands_twoProducts {n : ℕ} {u : Fin n → A → K} {v : Fin n → B → K}
    {H G T : A → B → K} (hH : Expands u v H) (hG : Expands u v G)
    (a a' : A → K) (b b' : B → K) (s t w : K)
    (h : ∀ x y, T x y = s * H x y + t * G x y + w * (a x * b y + a' x * b' y)) :
    Expands (Fin.cons a (Fin.cons a' u)) (Fin.cons b (Fin.cons b' v)) T := by
  obtain ⟨c, hc⟩ := hH
  obtain ⟨d, hd⟩ := hG
  refine ⟨Fin.cons w (Fin.cons w (fun j => s * c j + t * d j)), fun x y => ?_⟩
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, h, hc, hd, mul_add,
    Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

local notation "RI" F:max A:max B:max => FractionRing (MvPolynomial (A ⊕ B) F)

private def leftD (p : RI F A B) (x : A) := ratPartial (.inl x) p

private def rightD (p : RI F A B) (y : B) := ratPartial (.inr y) p

private theorem ratPartial_const (s : A ⊕ B) (c : F) :
    ratPartial s (algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c)) = 0 := by
  simp

private theorem ratMixed_const_mul (c : F) (q : RI F A B) :
    ratMixed (algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c) * q) =
      fun x y => algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c) * ratMixed q x y := by
  funext x y
  rw [ratMixed_mul, ratMixed_C, ratPartial_const, ratPartial_const]
  ring

private theorem ratMixed_mul_const (c : F) (p : RI F A B) :
    ratMixed (p * algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c)) =
      fun x y => algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c) * ratMixed p x y := by
  rw [mul_comm]
  exact ratMixed_const_mul c p

private theorem ratMixed_div_const (c : F) (p : RI F A B)
    (hk : algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c) ≠ 0) :
    ratMixed (p / algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c)) =
      fun x y => (algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c))⁻¹ * ratMixed p x y := by
  funext x y
  have h := ratMixed_mul (p / algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c))
    (algebraMap (MvPolynomial (A ⊕ B) F) (RI F A B) (C c)) x y
  rw [div_mul_cancel₀ _ hk, ratMixed_C, ratPartial_const, ratPartial_const] at h
  simp only [mul_zero, zero_mul, add_zero] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ hk, one_mul]

private theorem expansion_mul {n : ℕ} {u : Fin n → A → RI F A B}
    {v : Fin n → B → RI F A B} {p q : RI F A B}
    (hp : Expands u v (ratMixed p)) (hq : Expands u v (ratMixed q)) :
    Expands (Fin.cons (leftD p) (Fin.cons (leftD q) u))
      (Fin.cons (rightD q) (Fin.cons (rightD p) v)) (ratMixed (p * q)) := by
  apply expands_twoProducts hp hq _ _ _ _ q p 1
  intro x y
  rw [ratMixed_mul]
  simp only [leftD, rightD, one_mul]
  abel

private theorem expansion_quot {n : ℕ} {u : Fin n → A → RI F A B}
    {v : Fin n → B → RI F A B} {p q : RI F A B}
    (hp : Expands u v (ratMixed p)) (hq : Expands u v (ratMixed q)) (hne : q ≠ 0) :
    Expands (Fin.cons (leftD (p / q)) (Fin.cons (leftD q) u))
      (Fin.cons (rightD q) (Fin.cons (rightD (p / q)) v)) (ratMixed (p / q)) := by
  apply expands_twoProducts hp hq _ _ _ _ q⁻¹ (-(q⁻¹ * (p / q))) (-q⁻¹)
  intro x y
  have h := ratMixed_mul (p / q) q x y
  rw [div_mul_cancel₀ _ hne] at h
  rw [h]
  simp only [leftD, rightD]
  field_simp
  ring

/-- A scalar product: one factor is a field constant. -/
private theorem expansion_scalar_mul {n : ℕ} {u : Fin n → A → RI F A B}
    {v : Fin n → B → RI F A B} {p q : RI F A B}
    (hp : Expands u v (ratMixed p)) (hq : Expands u v (ratMixed q))
    (hc : IsFieldConstant p ∨ IsFieldConstant q) : Expands u v (ratMixed (p * q)) := by
  rcases hc with ⟨c, rfl⟩ | ⟨c, rfl⟩
  · rw [ratMixed_const_mul]
    exact expands_smul hq _
  · rw [ratMixed_mul_const]
    exact expands_smul hp _

/-- A scalar quotient: the divisor is a nonzero field constant. -/
private theorem expansion_scalar_quot {n : ℕ} {u : Fin n → A → RI F A B}
    {v : Fin n → B → RI F A B} {p q : RI F A B}
    (hp : Expands u v (ratMixed p)) (hne : q ≠ 0) (hc : IsFieldConstant q) :
    Expands u v (ratMixed (p / q)) := by
  obtain ⟨c, rfl⟩ := hc
  rw [ratMixed_div_const c p hne]
  exact expands_smul hp _

private theorem nonscalarRegisterProducts {r : ℕ} (p : RationalProgram F (A ⊕ B) r)
    (h : p.Valid) :
    ∃ (u : Fin (2 * p.nonscalarCount) → A → RI F A B)
      (v : Fin (2 * p.nonscalarCount) → B → RI F A B),
      ∀ i, Expands u v (ratMixed (p.value i)) := by
  induction p with
  | nil => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0⟩
  | step p g ih =>
    obtain ⟨u, v, huv⟩ := ih h
    cases g with
    | constant z =>
      simp only [RationalProgram.nonscalarCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [Expands, RationalProgram.value, RationalProgram.gateValue] using expands_zero u v
    | input i =>
      simp only [RationalProgram.nonscalarCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [Expands, RationalProgram.value, RationalProgram.gateValue] using expands_zero u v
    | add i j =>
      simp only [RationalProgram.nonscalarCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [Expands, RationalProgram.value, RationalProgram.gateValue] using
        expands_add (huv i) (huv j)
    | sub i j =>
      simp only [RationalProgram.nonscalarCount]
      refine ⟨u, v, Fin.cases ?_ huv⟩
      simpa [Expands, RationalProgram.value, RationalProgram.gateValue] using
        expands_sub (huv i) (huv j)
    | mul i j =>
      by_cases hc : IsFieldConstant (p.value i) ∨ IsFieldConstant (p.value j)
      · have e : (RationalProgram.step p (.mul i j)).nonscalarCount = p.nonscalarCount := by
          simp [RationalProgram.nonscalarCount, hc]
        rw [e]
        refine ⟨u, v, Fin.cases ?_ huv⟩
        simpa [Expands, RationalProgram.value, RationalProgram.gateValue] using
          expansion_scalar_mul (huv i) (huv j) hc
      · have e : (RationalProgram.step p (.mul i j)).nonscalarCount = p.nonscalarCount + 1 := by
          simp [RationalProgram.nonscalarCount, hc]
        rw [e]
        refine ⟨_, _, Fin.cases (expansion_mul (huv i) (huv j)) (fun k => ?_)⟩
        exact expands_insert (expands_insert (huv k) _ _) _ _
  | quot p i j ih =>
    obtain ⟨u, v, huv⟩ := ih h.1
    by_cases hc : IsFieldConstant (p.value j)
    · have e : (RationalProgram.quot p i j).nonscalarCount = p.nonscalarCount := by
        simp [RationalProgram.nonscalarCount, hc]
      rw [e]
      exact ⟨u, v, Fin.cases (expansion_scalar_quot (huv i) h.2 hc) huv⟩
    · have e : (RationalProgram.quot p i j).nonscalarCount = p.nonscalarCount + 1 := by
        simp [RationalProgram.nonscalarCount, hc]
      rw [e]
      refine ⟨_, _, Fin.cases (expansion_quot (huv i) (huv j) h.2) (fun k => ?_)⟩
      exact expands_insert (expands_insert (huv k) _ _) _ _

variable {a b c : ℕ} {P : RationalMatrixAlgorithm F a b c}

/-- The generic-input rank is at most twice the number of nonscalar gates. -/
theorem matrixTensor_rank_le_twice_nonscalarCount (h : P.Correct) :
    tensorRank (matrixTensor (FractionRing (MvPolynomial (MatrixInput a b c) F)) b c a) ≤
      2 * P.program.nonscalarCount := by
  classical
  obtain ⟨u, v, huv⟩ := nonscalarRegisterProducts P.program h.1
  choose w hw using huv
  apply tensorRank_le_of_rankAtMost
  refine ⟨u, v, fun t z => w (P.output z.2 z.1) t, ?_⟩
  funext x y z
  have hout := hw (P.output z.2 z.1) x y
  rw [h.2, map_sum] at hout
  simp only [map_mul, ratMixed_matrixEntry] at hout
  exact hout

/-- Rank over the algebraic closure is at most twice the number of nonscalar gates. -/
theorem algebraicClosure_rank_le_twice_nonscalarCount (h : P.Correct) :
    tensorRank (matrixTensor (AlgebraicClosure F) b c a) ≤ 2 * P.program.nonscalarCount :=
  (matrix_tensorRank_algebraicClosure_le_fractionRing F (MatrixInput a b c) b c a).trans
    (matrixTensor_rank_le_twice_nonscalarCount h)

variable {n : ℕ} {Q : RationalMatrixAlgorithm F n n n}

/-- **Corollary 1.2.** Every formal circuit with division over a field that multiplies
two `n × n` matrices, `n ≥ 2`, has at least `⌈n ^ (9/4) / 2⌉` nonscalar multiplication
or division gates. Additions, subtractions, products with a constant factor and
quotients by a nonzero constant are free. -/
theorem nonscalarCount_ceil_lower (hn : 2 ≤ n) (h : Q.Correct) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ Q.program.nonscalarCount := by
  rw [Nat.ceil_le]
  have h₁ := rpow_nine_fourths_le_tensorRank (AlgebraicClosure F) hn
  have h₂ : (tensorRank (matrixTensor (AlgebraicClosure F) n n n) : ℝ) ≤
      ((2 * Q.program.nonscalarCount : ℕ) : ℝ) := by
    exact_mod_cast algebraicClosure_rank_le_twice_nonscalarCount h
  push_cast at h₂
  linarith

end

end SpectralBooks
end LinearAlgebra
end OAI
