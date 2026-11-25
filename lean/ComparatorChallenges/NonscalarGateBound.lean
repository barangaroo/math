import Mathlib

/-! # Nonscalar gate lower bounds for matrix multiplication over every field

Corollary 1.2 of "The matrix multiplication exponent is nine fourths" (Family 379):
every formal circuit with division over a field that multiplies two `n × n` matrices,
`n ≥ 2`, has at least `⌈n ^ (9/4) / 2⌉` nonscalar multiplication or division gates.
A multiplication with a field-constant input and a division by a nonzero field
constant are scalar and free; additions and subtractions are free.
Also the rectangular forms `⌈exp (U (log a) (log c) (log b)) / 2⌉` and
`⌈(a b c) ^ (3/4) / 2⌉` for an `a × b` by `b × c` product.
-/

namespace OAI

noncomputable section

open scoped BigOperators

namespace MatrixMultiplication.Arithmetic

inductive Gate (F Input Register : Type*) where
  | constant : F → Gate F Input Register
  | input : Input → Gate F Input Register
  | add : Register → Register → Gate F Input Register
  | sub : Register → Register → Gate F Input Register
  | mul : Register → Register → Gate F Input Register

namespace Gate

variable {F Input Register : Type*}

def cost : Gate F Input Register → ℕ
  | .constant _ => 0
  | .input _ => 0
  | .add _ _ => 1
  | .sub _ _ => 1
  | .mul _ _ => 1

end Gate

abbrev MatrixInput (a b c : ℕ) := (Fin a × Fin b) ⊕ (Fin b × Fin c)

end MatrixMultiplication.Arithmetic

end

end OAI

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

/-- The benchmark on the cone where the last coordinate is smallest. -/
def benchmark (a b c : ℝ) : ℝ :=
  a + b + (max ((a + b) * c - a * b) 0) ^ 2 / (4 * a * b * c)

/-- Evaluate the benchmark with a smallest side placed last. Division by
zero in the real-valued formula returns zero on a coordinate plane. -/
def U (a b c : ℝ) : ℝ :=
  if c ≤ min a b then benchmark a b c
  else if a ≤ b then benchmark b c a
  else benchmark c a b

end OAI.LinearAlgebra.MatrixExponent.Rectangle

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Arithmetic MvPolynomial
open scoped BigOperators

/-- Straight-line programs over the field of rational functions in the inputs. -/
inductive RationalProgram (F I : Type*) : ℕ → Type _ where
  | nil : RationalProgram F I 0
  | step {r : ℕ} (p : RationalProgram F I r) (g : Gate F I (Fin r)) :
      RationalProgram F I (r + 1)
  | quot {r : ℕ} (p : RationalProgram F I r) (i j : Fin r) : RationalProgram F I (r + 1)

namespace RationalProgram

variable {F I R : Type*} {r : ℕ}

/-- Total number of scalar arithmetic operations. -/
def cost : {r : ℕ} → RationalProgram F I r → ℕ
  | _, .nil => 0
  | _, .step p g => p.cost + g.cost
  | _, .quot p _ _ => p.cost + 1

noncomputable section

variable [Field F]

/-- Interpret the ordinary gates in the rational function field. -/
def gateValue (g : Gate F I R) (v : R → FractionRing (MvPolynomial I F)) :
    FractionRing (MvPolynomial I F) :=
  g.casesOn (fun c => algebraMap _ _ (C c : MvPolynomial I F)) (fun i => algebraMap _ _ (X i : MvPolynomial I F))
    (fun i j => v i + v j) (fun i j => v i - v j) (fun i j => v i * v j)

/-- The rational function recorded at a register. Register zero holds the latest gate. -/
def value : {r : ℕ} → RationalProgram F I r → Fin r → FractionRing (MvPolynomial I F)
  | _, .nil => Fin.elim0
  | _, .step p g => Fin.cases (gateValue g p.value) p.value
  | _, .quot p i j => Fin.cases (p.value i / p.value j) p.value

/-- Every denominator occurring during the computation is generically nonzero. -/
def Valid : {r : ℕ} → RationalProgram F I r → Prop
  | _, .nil => True
  | _, .step p _ => p.Valid
  | _, .quot p _ j => p.Valid ∧ p.value j ≠ 0

end
end RationalProgram

/-- A rectangular matrix multiplication algorithm with division gates. -/
structure RationalMatrixAlgorithm (F : Type*) (a b c : ℕ) where
  registers : ℕ
  program : RationalProgram F (MatrixInput a b c) registers
  output : Fin a → Fin c → Fin registers

namespace RationalMatrixAlgorithm

variable {F : Type*} {a b c : ℕ}

variable [Field F]

/-- Validity of the divisions and the formal identities for all output coordinates. -/
def Correct (P : RationalMatrixAlgorithm F a b c) : Prop :=
  P.program.Valid ∧ ∀ i k, P.program.value (P.output i k) = algebraMap _ _
    (∑ j : Fin b, X (Sum.inl (i, j)) * X (Sum.inr (j, k)) : MvPolynomial (MatrixInput a b c) F)

end RationalMatrixAlgorithm

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

end RationalProgram

/-- Corollary 1.2: at least `⌈n ^ (9/4) / 2⌉` nonscalar gates for `n × n` matrices. -/
theorem nonscalarCount_ceil_lower {n : ℕ} {Q : RationalMatrixAlgorithm F n n n}
    (hn : 2 ≤ n) (h : Q.Correct) :
    ⌈(n : ℝ) ^ ((9 : ℝ) / 4) / 2⌉₊ ≤ Q.program.nonscalarCount := by
  sorry

open MatrixExponent.Rectangle in
/-- Rectangular benchmark form, for an `a × b` by `b × c` product. -/
theorem nonscalarCount_benchmark_ceil_lower {a b c : ℕ} {P : RationalMatrixAlgorithm F a b c}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : P.Correct) :
    ⌈Real.exp (U (Real.log a) (Real.log c) (Real.log b)) / 2⌉₊ ≤ P.program.nonscalarCount := by
  sorry

/-- Volume form, for an `a × b` by `b × c` product. -/
theorem nonscalarCount_volume_ceil_lower {a b c : ℕ} {P : RationalMatrixAlgorithm F a b c}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : P.Correct) :
    ⌈((a * b * c : ℕ) : ℝ) ^ (3 / 4 : ℝ) / 2⌉₊ ≤ P.program.nonscalarCount := by
  sorry

end

end SpectralBooks
end LinearAlgebra
end OAI
