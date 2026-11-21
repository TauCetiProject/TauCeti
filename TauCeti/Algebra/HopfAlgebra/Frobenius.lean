/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi, The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.Algebra.Frobenius.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.Algebra.HopfAlgebra.Cointegral.DualBasis
import TauCeti.Algebra.HopfAlgebra.HopfModule.Dual
import TauCeti.Algebra.Module.Injective.Frobenius

/-!
# Frobenius structure, integrals, and cointegrals of finite-dimensional Hopf algebras

A nonzero right invariant functional on a finite-dimensional Hopf algebra is a Frobenius functional.
Here right invariance means `(φ ⊗ id) Δ(x) = φ(x) 1`, agreeing with `TauCeti.IsRightCointegral`
(`LinearMap.isRightInvariantIntegral_iff_isRightCointegral`). Left invariant functionals give
Frobenius functionals as well.

A Frobenius functional on a finite-dimensional bialgebra pairs nontrivially with both integral
spaces: each has a unique element on which the functional is one, so both integral spaces have
dimension `1`. For a right invariant functional on a Hopf algebra, strong invariance gives a
reconstruction formula from the coproduct of its normalized left integral, forcing the antipode to
be bijective.

Combining these consequences with the Larson–Sweedler cointegral decomposition
`rightCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H` from
`TauCeti.Algebra.HopfAlgebra.HopfModule.Dual` yields the unconditional **Larson–Sweedler theorems**
for any finite-dimensional Hopf algebra `H` over a field `k`:

* `TauCeti.finrank_rightCointegrals` and `TauCeti.finrank_leftCointegrals`: the spaces of right and
  left cointegrals on `H` are one-dimensional;
* `TauCeti.exists_isFrobeniusFunctional_of_hopfAlgebra`: `H` admits a Frobenius functional;
* `TauCeti.finrank_leftIntegral` and `TauCeti.finrank_rightIntegral`: the spaces of left and right
  integrals in `H` are one-dimensional;
* `TauCeti.antipode_bijective`: the antipode of `H` is bijective;
* `TauCeti.moduleInjective_self_of_hopfAlgebra` and
  `TauCeti.moduleInjective_op_self_of_hopfAlgebra`: `H` is left and right self-injective.
* `TauCeti.moduleProjective_iff_moduleInjective_of_hopfAlgebra`: projective and injective left
  `H`-modules coincide.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2, Theorem 2.1.3.
-/

public section

open Coalgebra HopfAlgebra TauCeti
open scoped Coalgebra

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
    (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mp hφ).sum_apply_mul_smul_antipode
      t.property ht r x

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

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- A nonzero right cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsRightCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).isFrobeniusFunctional h0

/-- A nonzero left cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  (LinearMap.isLeftInvariantIntegral_iff_isLeftCointegral.mpr hφ).isFrobeniusFunctional h0

variable (k H)

/-- **Larson–Sweedler Cointegral Theorem (right)**: the space of right cointegrals on a
finite-dimensional Hopf algebra is one-dimensional. -/
@[simp]
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  have : Module.Free k (rightCointegrals k H) :=
    @Module.Free.of_divisionRing k _ _ (Submodule.addCommGroup (rightCointegrals k H)) _
  have hpos : 0 < Module.finrank k H := by
    have := Bialgebra.nontrivial (R := k) (A := H)
    exact Module.finrank_pos
  have heq : Module.finrank k (rightCointegrals k H) * Module.finrank k H =
      1 * Module.finrank k H := by
    rw [one_mul, ← Module.finrank_tensorProduct,
      (rightCointegralsTensorEquivDual k H).finrank_eq, Subspace.dual_finrank_eq]
  exact Nat.eq_of_mul_eq_mul_right hpos heq

/-- Every finite-dimensional Hopf algebra over a field has a nontrivial space of right
cointegrals. -/
theorem rightCointegrals_ne_bot : rightCointegrals k H ≠ ⊥ :=
  Submodule.one_le_finrank_iff.mp (finrank_rightCointegrals k H).ge

/-- **Larson–Sweedler Frobenius Theorem**: every finite-dimensional Hopf algebra over a field
admits a Frobenius functional. -/
theorem exists_isFrobeniusFunctional_of_hopfAlgebra :
    ∃ φ : H →ₗ[k] k, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

/-- **Larson–Sweedler Integral Theorem (left)**: the space of left integrals in a
finite-dimensional Hopf algebra is one-dimensional. -/
@[simp]
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact hφ.finrank_leftIntegral

/-- **Larson–Sweedler Integral Theorem (right)**: the space of right integrals in a
finite-dimensional Hopf algebra is one-dimensional. -/
@[simp]
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact hφ.finrank_rightIntegral

/-- Every finite-dimensional Hopf algebra over a field has a nontrivial space of left
integrals. -/
theorem leftIntegral_ne_bot : leftIntegral k H ≠ ⊥ :=
  Submodule.one_le_finrank_iff.mp (finrank_leftIntegral k H).ge

/-- Every finite-dimensional Hopf algebra over a field has a nontrivial space of right
integrals. -/
theorem rightIntegral_ne_bot : rightIntegral k H ≠ ⊥ :=
  Submodule.one_le_finrank_iff.mp (finrank_rightIntegral k H).ge

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left integral. -/
theorem exists_leftIntegral_ne_zero : ∃ t : H, t ∈ leftIntegral k H ∧ t ≠ 0 := by
  simpa [Submodule.ne_bot_iff] using leftIntegral_ne_bot k H

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right integral. -/
theorem exists_rightIntegral_ne_zero : ∃ t : H, t ∈ rightIntegral k H ∧ t ≠ 0 := by
  simpa [Submodule.ne_bot_iff] using rightIntegral_ne_bot k H

/-- **Larson–Sweedler Cointegral Theorem (left)**: the space of left cointegrals on a
finite-dimensional Hopf algebra is one-dimensional. -/
@[simp]
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 :=
  (leftCointegralsConvEquiv k H).finrank_eq.trans
    (finrank_leftIntegral k (ConvolutionDual k H))

/-- Every finite-dimensional Hopf algebra over a field has a nontrivial space of left
cointegrals. -/
theorem leftCointegrals_ne_bot : leftCointegrals k H ≠ ⊥ :=
  Submodule.one_le_finrank_iff.mp (finrank_leftCointegrals k H).ge

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  simpa [Submodule.ne_bot_iff] using leftCointegrals_ne_bot k H

/-- **Larson–Sweedler Antipode Bijectivity Theorem**: the antipode of any finite-dimensional Hopf
algebra over a field is bijective. -/
theorem antipode_bijective : Function.Bijective (antipode k : H →ₗ[k] H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact (LinearMap.isRightInvariantIntegral_iff_isRightCointegral.mpr hφ).antipode_bijective h0

include k in
/-- Every finite-dimensional Hopf algebra over a field is left self-injective. -/
theorem moduleInjective_self_of_hopfAlgebra : Module.Injective H H := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact hφ.moduleInjective_self

include k in
/-- Every finite-dimensional Hopf algebra over a field is right self-injective. -/
theorem moduleInjective_op_self_of_hopfAlgebra : Module.Injective Hᵐᵒᵖ H := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact hφ.moduleInjective_op_self

section ProjectiveIffInjective

universe w

include k in
/-- Over a finite-dimensional Hopf algebra, a left module (not necessarily finitely generated) is
projective if and only if it is injective. -/
theorem moduleProjective_iff_moduleInjective_of_hopfAlgebra [Small.{w} H] (M : Type w)
    [AddCommGroup M] [Module H M] :
    Module.Projective H M ↔ Module.Injective H M := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional_of_hopfAlgebra k H
  exact hφ.moduleProjective_iff_moduleInjective M

end ProjectiveIffInjective

end TauCeti
