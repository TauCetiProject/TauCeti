/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import TauCeti.Topology.Algebra.InfiniteSum.DiscreteConvolution
import Mathlib.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Group.Pi

/-!
# Rings of two-sided coefficient families under convolution

A two-sided coefficient family `a : ℤ → R` stands for the formal Laurent series `∑_{n ∈ ℤ} aₙ tⁿ`.
The product of two such series has coefficients `(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ`, the discrete
convolution `a ⋆ᵣ₊ b`, but these sums are infinite and need not converge. Over a topological
ring that is a `T3Space`, a class of families on which they do, closed under convolution, is a ring.

`TauCeti.IsConvolutionRing S` collects the convergence and closure hypotheses for the convolution
product on the submodule `S` of `ℤ → R`: `S` contains every monomial `Pi.single n c` and is closed
under convolution, the convolution sums of its members converge, and the triple products of three
members are summable, so that the two bracketings of a triple product agree. Under it, this file
equips `S` with the convolution product, and the monomials multiply by adding degrees. When `R` is
moreover a ring with `IsTopologicalRing R` and `T3Space R`, `S` is a ring (`instRing`); when `R`
is in addition commutative, `S` is a commutative `R`-algebra (`instCommRing`, `instAlgebra`). The
families with coefficients in the closed unit ball of an ultrametric normed ring form a subring.

## Main definitions

* `TauCeti.IsConvolutionRing`: the convergence and closure hypotheses for the convolution product
  on a submodule of `ℤ → R`.
* `TauCeti.IsConvolutionRing.instRing`, `TauCeti.IsConvolutionRing.instCommRing`,
  `TauCeti.IsConvolutionRing.instAlgebra`: the ring and algebra structures.
* `TauCeti.IsConvolutionRing.monomial`: the Laurent monomial `c tⁿ`.
* `TauCeti.IsConvolutionRing.integral`: the subring of families with coefficients in the closed
  unit ball.

## Main results

* `TauCeti.IsConvolutionRing.hasSum_coeff_mul`: the coefficients of a product are the convergent
  convolution sums.
* `TauCeti.IsConvolutionRing.monomial_mul_monomial`: `(a tᵐ)(b tⁿ) = ab tᵐ⁺ⁿ`.
* `TauCeti.IsConvolutionRing.isUnit_monomial`: a monomial with a unit coefficient is a unit; in
  particular `t` is a unit.
-/

public section

open scoped DiscreteConvolution

namespace TauCeti

open DiscreteConvolution

variable {R : Type*}

/-- The convergence and closure hypotheses for the convolution product
`(ab)ₙ = ∑_{i ∈ ℤ} aᵢ bₙ₋ᵢ` on the submodule `S` of two-sided coefficient families `ℤ → R`: `S`
contains every monomial `Pi.single n c` and is closed under convolution, the convolution sums of
two members converge, and the triple products `a i * b j * c k` over the triples with
`i + j + k = n` of three members are summable, indexed as in
`DiscreteConvolution.addRingConvolution_assoc`. The ring structure `instRing` on `S` further needs
`R` to be a ring with `IsTopologicalRing R` and `T3Space R`; `instCommRing` and `instAlgebra` also
need `R` to be commutative. -/
class IsConvolutionRing [Semiring R] [TopologicalSpace R] (S : Submodule R (ℤ → R)) : Prop where
  single_mem (n : ℤ) (c : R) : Pi.single n c ∈ S
  addRingConvolution_mem {a b : ℤ → R} : a ∈ S → b ∈ S → a ⋆ᵣ₊ b ∈ S
  addConvolutionExists {a b : ℤ → R} : a ∈ S → b ∈ S → AddConvolutionExists (.mul ℕ R) a b
  summable_sigma_addFiber_mul_mul {a b c : ℤ → R} : a ∈ S → b ∈ S → c ∈ S → ∀ n : ℤ,
    Summable fun σ : Σ p : addFiber n, addFiber p.val.1 ↦ a σ.2.val.1 * b σ.2.val.2 * c σ.1.val.2

namespace IsConvolutionRing

/-- **Coefficientwise extensionality**: two members of a submodule of `ℤ → R` that agree in every
degree are equal. -/
@[ext]
theorem ext [Semiring R] {S : Submodule R (ℤ → R)} {f g : S}
    (h : ∀ n, (f : ℤ → R) n = (g : ℤ → R) n) : f = g :=
  Subtype.ext <| funext h

section Semiring

variable [Semiring R] [TopologicalSpace R] {S : Submodule R (ℤ → R)} [IsConvolutionRing S]

instance instOne : One S where
  one := ⟨Pi.single 0 1, single_mem 0 1⟩

@[simp, norm_cast]
theorem coe_one : ((1 : S) : ℤ → R) = Pi.single 0 1 :=
  (rfl)

/-- **The Laurent monomial `c tⁿ`**: the family supported in degree `n` with value `c`. The
variable `t` is `monomial 1 1`. -/
def monomial (n : ℤ) (c : R) : S :=
  ⟨Pi.single n c, single_mem n c⟩

@[simp, norm_cast]
theorem coe_monomial (n : ℤ) (c : R) : ((monomial n c : S) : ℤ → R) = Pi.single n c :=
  (rfl)

@[simp]
theorem monomial_zero_one : (monomial 0 1 : S) = 1 :=
  (rfl)

@[simp]
theorem monomial_zero_right (n : ℤ) : (monomial n 0 : S) = 0 :=
  Subtype.ext <| by simp

@[simp]
theorem monomial_add (n : ℤ) (c d : R) :
    (monomial n (c + d) : S) = monomial n c + monomial n d :=
  Subtype.ext <| by simp [Pi.single_add]

/-- `c (a tⁿ) = (ca) tⁿ`. -/
@[simp]
theorem smul_monomial (c : R) (n : ℤ) (a : R) : c • (monomial n a : S) = monomial n (c * a) :=
  Subtype.ext <| by simp [← smul_eq_mul, Pi.single_smul']

noncomputable instance instMul : Mul S where
  mul f g := ⟨f ⋆ᵣ₊ g, addRingConvolution_mem f.property g.property⟩

/-- The coefficient family of a product is the convolution of the coefficient families. -/
@[simp, norm_cast]
theorem coe_mul (f g : S) : ((f * g : S) : ℤ → R) = ↑f ⋆ᵣ₊ ↑g :=
  (rfl)

/-- **Laurent monomials multiply by adding degrees**: `(a tᵐ)(b tⁿ) = ab tᵐ⁺ⁿ`. In particular
`t t⁻¹ = 1`. -/
@[simp]
theorem monomial_mul_monomial (m n : ℤ) (a b : R) :
    (monomial m a * monomial n b : S) = monomial (m + n) (a * b) :=
  Subtype.ext <| single_addRingConvolution_single m n a b

/-- **The coefficients of a product are convergent convolution sums**: the `n`-th coefficient of
`f g` is the sum of the convergent series `∑_{y ∈ ℤ} fₙ₋ᵧ gᵧ`. -/
theorem hasSum_coeff_mul (f g : S) (n : ℤ) :
    HasSum (fun y ↦ (f : ℤ → R) (n - y) * (g : ℤ → R) y) (((f * g : S) : ℤ → R) n) :=
  (addConvolutionExists f.property g.property n).hasSum_sub

end Semiring

/-- The monomial `a tⁿ` commutes with negating its coefficient. -/
@[simp]
theorem monomial_neg [Ring R] [TopologicalSpace R] {S : Submodule R (ℤ → R)}
    [IsConvolutionRing S] (n : ℤ) (a : R) : (monomial n (-a) : S) = -monomial n a :=
  Subtype.ext <| by simp [Pi.single_neg]

section Ring

variable [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T3Space R]
  {S : Submodule R (ℤ → R)} [IsConvolutionRing S]

/-- **A convolution ring is a ring.** -/
noncomputable instance instRing : Ring S where
  mul_assoc f g h := Subtype.ext <|
    addRingConvolution_assoc (addConvolutionExists f.property g.property)
      (addConvolutionExists g.property h.property)
      (summable_sigma_addFiber_mul_mul f.property g.property h.property)
  one_mul f := Subtype.ext <| by rw [coe_mul, coe_one, single_addRingConvolution]
  mul_one f := Subtype.ext <| by rw [coe_mul, coe_one, addRingConvolution_single]
  zero_mul f := Subtype.ext <| by rw [coe_mul, Submodule.coe_zero, zero_addRingConvolution]
  mul_zero f := Subtype.ext <| by rw [coe_mul, Submodule.coe_zero, addRingConvolution_zero]
  left_distrib f g h := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_add, Submodule.coe_add, coe_mul, coe_mul]
    exact addRingConvolution_add _ _ _ (addConvolutionExists f.property g.property)
      (addConvolutionExists f.property h.property)
  right_distrib f g h := Subtype.ext <| by
    rw [coe_mul, Submodule.coe_add, Submodule.coe_add, coe_mul, coe_mul]
    exact add_addRingConvolution _ _ _ (addConvolutionExists f.property h.property)
      (addConvolutionExists g.property h.property)

/-- **A monomial with a unit coefficient is a unit**: the inverse of `a tⁿ` is `a⁻¹ t⁻ⁿ`. In
particular the variable `t = monomial 1 1` is a unit. -/
theorem isUnit_monomial (n : ℤ) {a : R} (ha : IsUnit a) : IsUnit (monomial n a : S) := by
  obtain ⟨u, rfl⟩ := ha
  exact isUnit_iff_exists.2 ⟨monomial (-n) ↑u⁻¹, by simp, by simp⟩

end Ring

section CommRing

variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T3Space R]
  {S : Submodule R (ℤ → R)} [IsConvolutionRing S]

/-- **A convolution ring over a commutative ring is commutative.** -/
noncomputable instance instCommRing : CommRing S where
  mul_comm f g := Subtype.ext <| by rw [coe_mul, coe_mul, addRingConvolution_comm]

/-- **A convolution ring is an `R`-algebra**, with the coefficientwise scalar action. -/
noncomputable instance instAlgebra : Algebra R S :=
  .ofModule
    (fun c f g ↦ Subtype.ext <| by
      rw [Submodule.coe_smul, coe_mul, coe_mul, Submodule.coe_smul]
      exact smul_addRingConvolution c _ _ (addConvolutionExists f.property g.property))
    (fun c f g ↦ Subtype.ext <| by
      rw [Submodule.coe_smul, coe_mul, coe_mul, Submodule.coe_smul]
      exact addRingConvolution_smul c _ _ (addConvolutionExists f.property g.property))

/-- The structure map sends `c` to the constant series `c = c t⁰`. -/
@[simp, norm_cast]
theorem coe_algebraMap (c : R) : (algebraMap R S c : ℤ → R) = Pi.single 0 c := by
  simp [Algebra.algebraMap_eq_smul_one, ← Pi.single_smul]

@[simp]
theorem monomial_zero_left (c : R) : (monomial 0 c : S) = algebraMap R S c :=
  Subtype.ext <| by simp

/-- Multiplying by a constant series multiplies the coefficient: `a (b tⁿ) = ab tⁿ`. -/
@[simp]
theorem algebraMap_mul_monomial (a : R) (n : ℤ) (b : R) :
    algebraMap R S a * monomial n b = monomial n (a * b) := by
  rw [← monomial_zero_left, monomial_mul_monomial, zero_add]

/-- Multiplying by a constant series multiplies the coefficient: `(a tⁿ) b = ab tⁿ`. -/
@[simp]
theorem monomial_mul_algebraMap (n : ℤ) (a b : R) :
    monomial n a * algebraMap R S b = monomial n (a * b) := by
  rw [← monomial_zero_left, monomial_mul_monomial, add_zero]

end CommRing

section Integral

variable [NormedRing R] [IsUltrametricDist R] [NormOneClass R] {S : Submodule R (ℤ → R)}
  [IsConvolutionRing S]

variable (S) in
/-- **The integral subring**: the families in `S` whose coefficients lie in the closed unit
ball. -/
def integral : Subring S where
  carrier := {f | ∀ n, ‖(f : ℤ → R) n‖ ≤ 1}
  mul_mem' hf hg n := (norm_addRingConvolution_apply_le hf hg n).trans_eq (one_mul 1)
  one_mem' n := (Pi.norm_single_apply_le (E := fun _ ↦ R) 0 n 1).trans_eq norm_one
  add_mem' hf hg n := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))
  zero_mem' n := by simp
  neg_mem' hf n := by simpa using hf n

@[simp]
theorem mem_integral {f : S} : f ∈ integral S ↔ ∀ n, ‖(f : ℤ → R) n‖ ≤ 1 :=
  (Iff.rfl)

/-- A monomial `c tⁿ` with `‖c‖ ≤ 1` is integral. -/
theorem monomial_mem_integral (n : ℤ) {c : R} (hc : ‖c‖ ≤ 1) : monomial n c ∈ integral S :=
  fun m ↦ (Pi.norm_single_apply_le (E := fun _ ↦ R) n m c).trans hc

end Integral

end IsConvolutionRing

end TauCeti
