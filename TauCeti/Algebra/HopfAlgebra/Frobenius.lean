/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.HopfAlgebra.RightHopfModule.Dual
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Module.Injective.Frobenius
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The Larson–Sweedler Frobenius theorem, integrals, and bijectivity of the antipode

A nonzero right invariant functional on a finite-dimensional Hopf algebra is a
Frobenius functional. Here right invariance means `(φ ⊗ id) Δ(x) = φ(x) 1`,
so this is the right-cointegral convention (`TauCeti.IsRightCointegral`). Left invariant
functionals (`TauCeti.IsLeftCointegral`) give Frobenius functionals as well.

A Frobenius functional on a finite-dimensional bialgebra pairs nontrivially with
both integral spaces: each has a unique element on which the functional is one, so both
`TauCeti.leftIntegral` and `TauCeti.rightIntegral` have dimension one. For a right invariant
functional, strong invariance gives a reconstruction formula from the coproduct of its
normalized left integral, showing that the antipode is bijective.

Combining these conditional statements with the Larson–Sweedler dual decomposition
`TauCeti.leftCointegralsTensorEquiv` (`leftCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H`) yields
the unconditional **Larson–Sweedler theorems** for every finite-dimensional Hopf algebra `H` over a
field `k`:

* `TauCeti.finrank_leftCointegrals` and `TauCeti.finrank_rightCointegrals`: the spaces of left and
  right cointegrals are one-dimensional;
* `TauCeti.exists_isFrobeniusFunctional`: `H` is a Frobenius algebra;
* `TauCeti.finrank_leftIntegral` and `TauCeti.finrank_rightIntegral`: the spaces of left and right
  integrals are one-dimensional;
* `TauCeti.antipode_bijective`, `TauCeti.antipodeLinearEquiv`, and `TauCeti.antipodeAlgEquivOp`:
  the antipode of a finite-dimensional Hopf algebra is bijective;
* `TauCeti.HopfAlgebra.moduleProjective_iff_moduleInjective`,
  `TauCeti.HopfAlgebra.moduleInjective_self`, and `TauCeti.HopfAlgebra.moduleInjective_op_self`:
  projective and injective `H`-modules coincide, and `H` is self-injective on both sides.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorems 2.1.3 and 2.1.4.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.
-/

public section

open Coalgebra HopfAlgebra TauCeti
open scoped Coalgebra TensorProduct

namespace LinearMap

variable {k H : Type*} [Field k] [Ring H]

section Bialgebra

variable [Bialgebra k H] [FiniteDimensional k H] {φ : H →ₗ[k] k}

/-- The left integral pairing to one against a Frobenius functional exists uniquely.
No normalization of its counit is required. -/
theorem IsFrobeniusFunctional.existsUnique_leftIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : leftIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.isPerfPair.bijective_right.surjective (counit (R := k))
  have ht' (x : H) : φ (x * t) = counit (R := k) x :=
    DFunLike.congr_fun ht x
  have hmem : t ∈ leftIntegral k H := by
    rw [mem_leftIntegral_iff]
    intro x
    apply hφ.eq_of_forall_apply_mul_eq
    intro y
    simp [← mul_assoc, ht', mul_comm]
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp u.property) x, hu, ht']

/-- The right integral pairing to one against a Frobenius functional exists uniquely. -/
theorem IsFrobeniusFunctional.existsUnique_rightIntegral_apply_eq_one
    (hφ : φ.IsFrobeniusFunctional) :
    ∃! t : rightIntegral k H, φ t = 1 := by
  obtain ⟨t, ht⟩ := hφ.toDualEquiv.surjective (counit (R := k))
  have ht' (x : H) : φ (t * x) = counit (R := k) x := by
    simpa using DFunLike.congr_fun ht x
  have hmem : t ∈ rightIntegral k H := by
    rw [mem_rightIntegral_iff]
    intro x
    apply sub_eq_zero.mp
    apply hφ.eq_zero_of_forall_left
    intro y
    simp [sub_mul, mul_assoc, ht']
  have hone : φ t = 1 := by simpa using ht' 1
  refine ⟨⟨t, hmem⟩, hone, ?_⟩
  intro u hu
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp u.property) x, hu, ht']

/-- A Frobenius functional identifies the left integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_leftIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_leftIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply hφ.eq_of_forall_apply_mul_eq
  intro x
  simp [(mem_leftIntegral_iff.mp t.property) x,
    (mem_leftIntegral_iff.mp u.property) x, ht, mul_comm]

/-- A Frobenius functional identifies the right integral space with a line. -/
theorem IsFrobeniusFunctional.finrank_rightIntegral
    (hφ : φ.IsFrobeniusFunctional) : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨t, ht, _⟩ := hφ.existsUnique_rightIntegral_apply_eq_one
  have ht0 : t ≠ 0 := by
    intro h
    simp [h] at ht
  apply (finrank_eq_one_iff_of_ne_zero' t ht0).mpr
  intro u
  refine ⟨φ u, ?_⟩
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply hφ.eq_zero_of_forall_left
  intro x
  simp [sub_mul, (mem_rightIntegral_iff.mp t.property) x,
    (mem_rightIntegral_iff.mp u.property) x, ht, mul_comm]

end Bialgebra

section Hopf

variable [HopfAlgebra k H] {φ : H →ₗ[k] k}

/-- A nonzero right invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsRightInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_left fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero left invariant functional on a finite-dimensional Hopf algebra
is a Frobenius functional. -/
theorem IsLeftInvariantIntegral.isFrobeniusFunctional [FiniteDimensional k H]
    (hφ : φ.IsLeftInvariantIntegral) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  .of_right fun _ hx => hφ.eq_zero_of_forall_mul_eq_zero h0 hx

/-- A nonzero right invariant functional makes the antipode surjective in finite
dimension, via the normalized left integral's reconstruction formula. -/
theorem IsRightInvariantIntegral.antipode_surjective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Surjective (antipode k : H → H) := by
  classical
  obtain ⟨t, ht, _⟩ :=
    (hφ.isFrobeniusFunctional h0).existsUnique_leftIntegral_apply_eq_one
  let r := ℛ k (t : H)
  intro x
  refine ⟨∑ i ∈ r.index, φ (x * r.left i) • r.right i, ?_⟩
  simpa only [map_sum, map_smul] using
    hφ.sum_apply_mul_smul_antipode t.property ht r x

/-- The antipode is bijective whenever a finite-dimensional Hopf algebra admits
a nonzero right invariant functional. -/
theorem IsRightInvariantIntegral.antipode_bijective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Bijective (antipode k : H → H) :=
  ⟨LinearMap.injective_iff_surjective.mpr (hφ.antipode_surjective h0),
    hφ.antipode_surjective h0⟩

end Hopf

end LinearMap

namespace TauCeti

universe u v w

section CointegralBridge

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- Over a bialgebra, `IsRightCointegral` agrees with `LinearMap.IsRightInvariantIntegral`. -/
theorem isRightCointegral_iff_isRightInvariantIntegral (φ : Module.Dual R H) :
    IsRightCointegral φ ↔ φ.IsRightInvariantIntegral := by
  rw [isRightCointegral_def, LinearMap.isRightInvariantIntegral_iff]

/-- Over a bialgebra, `IsLeftCointegral` agrees with `LinearMap.IsLeftInvariantIntegral`. -/
theorem isLeftCointegral_iff_isLeftInvariantIntegral (φ : Module.Dual R H) :
    IsLeftCointegral φ ↔ φ.IsLeftInvariantIntegral := by
  rw [isLeftCointegral_def, LinearMap.isLeftInvariantIntegral_iff]

end CointegralBridge

section FiniteDimensional

variable {k : Type u} {H : Type v} [Field k] [Ring H] [_root_.HopfAlgebra k H]
  [FiniteDimensional k H]

/-- A nonzero right cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsRightCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  ((isRightCointegral_iff_isRightInvariantIntegral φ).mp hφ).isFrobeniusFunctional h0

/-- A nonzero left cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  ((isLeftCointegral_iff_isLeftInvariantIntegral φ).mp hφ).isFrobeniusFunctional h0

variable (k H) in
/-- **Larson–Sweedler theorem on left cointegrals**: the space of left cointegrals on a
finite-dimensional Hopf algebra over a field has dimension one. -/
@[simp]
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 := by
  have : Module.Free k ↥(leftCointegrals k H) := .of_divisionRing k ↥(leftCointegrals k H)
  have : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  have hpos : 0 < Module.finrank k H := Module.finrank_pos
  have heq := (leftCointegralsTensorEquiv k H).finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq] at heq
  exact Nat.eq_of_mul_eq_mul_right hpos (heq.trans (one_mul _).symm)

/-- The space of left cointegrals on a finite-dimensional Hopf algebra over a field is nontrivial.
-/
theorem leftCointegrals_ne_bot : leftCointegrals k H ≠ ⊥ := by
  intro h
  have hrank := finrank_leftCointegrals k H
  rw [h, finrank_bot] at hrank
  exact zero_ne_one hrank

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  simpa using Submodule.exists_mem_ne_zero_of_ne_bot (leftCointegrals_ne_bot (k := k) (H := H))

variable (k H) in
/-- **Larson–Sweedler Frobenius theorem**: every finite-dimensional Hopf algebra over a field
admits a Frobenius functional. -/
theorem exists_isFrobeniusFunctional :
    ∃ φ : Module.Dual k H, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isLeftCointegral_ne_zero (k := k) (H := H)
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

variable (k H) in
/-- **Larson–Sweedler theorem on left integrals**: the space of left integrals in a
finite-dimensional Hopf algebra over a field has dimension one. -/
@[simp]
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.finrank_leftIntegral

/-- The submodule of left integrals in a finite-dimensional Hopf algebra over a field is
nontrivial. -/
theorem leftIntegral_ne_bot : leftIntegral k H ≠ ⊥ := by
  intro h
  have hrank := finrank_leftIntegral k H
  rw [h, finrank_bot] at hrank
  exact zero_ne_one hrank

/-- Every finite-dimensional Hopf algebra over a field contains a nonzero left integral. -/
theorem exists_mem_leftIntegral_ne_zero :
    ∃ t : H, t ∈ leftIntegral k H ∧ t ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot leftIntegral_ne_bot

variable (k H) in
/-- **Larson–Sweedler theorem on right integrals**: the space of right integrals in a
finite-dimensional Hopf algebra over a field has dimension one. -/
@[simp]
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.finrank_rightIntegral

/-- The submodule of right integrals in a finite-dimensional Hopf algebra over a field is
nontrivial. -/
theorem rightIntegral_ne_bot : rightIntegral k H ≠ ⊥ := by
  intro h
  have hrank := finrank_rightIntegral k H
  rw [h, finrank_bot] at hrank
  exact zero_ne_one hrank

/-- Every finite-dimensional Hopf algebra over a field contains a nonzero right integral. -/
theorem exists_mem_rightIntegral_ne_zero :
    ∃ t : H, t ∈ rightIntegral k H ∧ t ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot rightIntegral_ne_bot

variable (k H) in
/-- **Larson–Sweedler theorem on right cointegrals**: the space of right cointegrals on a
finite-dimensional Hopf algebra over a field has dimension one. -/
@[simp]
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  rw [(rightCointegralsEquivRightIntegral k H).finrank_eq]
  exact finrank_rightIntegral k (ConvolutionDual k H)

/-- The space of right cointegrals on a finite-dimensional Hopf algebra over a field is nontrivial.
-/
theorem rightCointegrals_ne_bot : rightCointegrals k H ≠ ⊥ := by
  intro h
  have hrank := finrank_rightCointegrals k H
  rw [h, finrank_bot] at hrank
  exact zero_ne_one hrank

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right cointegral. -/
theorem exists_isRightCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsRightCointegral φ ∧ φ ≠ 0 := by
  simpa using Submodule.exists_mem_ne_zero_of_ne_bot (rightCointegrals_ne_bot (k := k) (H := H))

variable (k H) in
/-- **Larson–Sweedler antipode theorem**: the antipode of a finite-dimensional Hopf algebra over a
field is bijective. -/
theorem antipode_bijective :
    Function.Bijective (antipode k : H → H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact ((isRightCointegral_iff_isRightInvariantIntegral φ).mp hφ).antipode_bijective h0

variable (k H) in
/-- The antipode of a finite-dimensional Hopf algebra over a field, bundled as a `k`-linear
equivalence `H ≃ₗ[k] H`. -/
noncomputable def antipodeLinearEquiv : H ≃ₗ[k] H :=
  LinearEquiv.ofBijective (antipode k) (antipode_bijective k H)

/-- `antipodeLinearEquiv` evaluates to the antipode. -/
@[simp]
theorem antipodeLinearEquiv_apply (h : H) :
    antipodeLinearEquiv k H h = antipode k h :=
  (rfl)

/-- Applying the antipode to `(antipodeLinearEquiv k H).symm h` recovers `h`. -/
@[simp]
theorem antipode_antipodeLinearEquiv_symm_apply (h : H) :
    antipode k ((antipodeLinearEquiv k H).symm h) = h :=
  (antipodeLinearEquiv k H).apply_symm_apply h

variable (k H) in
/-- The antipode of a finite-dimensional Hopf algebra over a field, bundled as a `k`-algebra
equivalence `H ≃ₐ[k] Hᵐᵒᵖ`. -/
noncomputable def antipodeAlgEquivOp : H ≃ₐ[k] Hᵐᵒᵖ :=
  AlgEquiv.ofBijective (antipodeAlgHomOp k H)
    (MulOpposite.opEquiv.bijective.comp (antipode_bijective k H))

/-- `antipodeAlgEquivOp` evaluates to `MulOpposite.op` applied to the antipode. -/
@[simp]
theorem antipodeAlgEquivOp_apply (h : H) :
    antipodeAlgEquivOp k H h = MulOpposite.op (antipode k h) :=
  (rfl)

variable (k H) in
/-- Over a finite-dimensional Hopf algebra over a field, the antipode restricts to a `k`-linear
equivalence between the left-integral and right-integral submodules. -/
noncomputable def leftIntegralEquivRightIntegral :
    leftIntegral k H ≃ₗ[k] rightIntegral k H :=
  integralAntipodeEquiv (antipode_bijective k H)

/-- `leftIntegralEquivRightIntegral` acts on underlying elements by the antipode. -/
@[simp]
theorem coe_leftIntegralEquivRightIntegral_apply (t : leftIntegral k H) :
    (leftIntegralEquivRightIntegral k H t : H) = antipode k (t : H) :=
  integralAntipodeEquiv_apply (antipode_bijective k H) t

namespace HopfAlgebra

include k

variable (k H) in
/-- Every projective left module over a finite-dimensional Hopf algebra is injective, with no
finiteness assumption on the module. -/
theorem moduleInjective_of_projective (P : Type w) [AddCommGroup P] [Module H P]
    [Module.Projective H P] : Module.Injective H P := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_of_projective P

variable (k H) in
/-- Projective and injective left modules over a finite-dimensional Hopf algebra coincide, with no
finiteness assumption on the module. -/
theorem moduleProjective_iff_moduleInjective [Small.{w} H] (M : Type w) [AddCommGroup M]
    [Module H M] : Module.Projective H M ↔ Module.Injective H M := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.moduleProjective_iff_moduleInjective M

variable (k H) in
/-- A finite-dimensional Hopf algebra over a field is left self-injective. -/
theorem moduleInjective_self : Module.Injective H H :=
  moduleInjective_of_projective k H H

variable (k H) in
/-- A finite-dimensional Hopf algebra over a field is right self-injective. -/
theorem moduleInjective_op_self : Module.Injective Hᵐᵒᵖ H := by
  obtain ⟨φ, hφ⟩ := exists_isFrobeniusFunctional k H
  have : Module.Projective Hᵐᵒᵖ H :=
    Module.Projective.of_equiv (MulOpposite.opLinearEquiv Hᵐᵒᵖ).symm
  exact hφ.op.moduleInjective_of_projective H

end HopfAlgebra

end FiniteDimensional

end TauCeti
