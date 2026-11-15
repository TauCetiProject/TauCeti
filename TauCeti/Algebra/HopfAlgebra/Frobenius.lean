/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfModule.Dual
public import TauCeti.Algebra.HopfAlgebra.Integral
public import TauCeti.Algebra.Module.Injective.Frobenius
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Frobenius structure, integrals, and antipode bijectivity for finite-dimensional Hopf algebras

Every finite-dimensional Hopf algebra `H` over a field `k` is a Frobenius algebra whose left and
right integral and cointegral spaces are one-dimensional, whose antipode is bijective, and over
which projective and injective modules coincide (Larson–Sweedler, Khovanov).

First, any nonzero right or left invariant functional on `H` is a Frobenius functional. Here right
invariance means `(φ ⊗ id) Δ(x) = φ(x) 1`, matching `TauCeti.IsRightCointegral`. A Frobenius
functional on a finite-dimensional bialgebra pairs to `1` against a unique left integral and a
unique right integral, identifying both `leftIntegral k H` and `rightIntegral k H` with lines.
Strong invariance yields dual-basis reconstruction formulas from the coproduct of the normalized
integral, making the antipode surjective and hence bijective.

Second, the Larson–Sweedler Hopf-module isomorphism
`leftCointegralsTensorEquiv : leftCointegrals k H ⊗[k] H ≃ₗ[k] Module.Dual k H` unconditionally
forces `Module.finrank k (leftCointegrals k H) = 1`. Consequently `H` admits a nonzero left
cointegral, hence a Frobenius functional, so `leftIntegral k H` and `rightIntegral k H` have
dimension `1`; applying `finrank_rightIntegral` to `ConvolutionDual k H` via
`rightCointegralsEquivRightIntegral` gives `Module.finrank k (rightCointegrals k H) = 1`, which in
turn yields unconditional bijectivity of `HopfAlgebra.antipode k`, left/right self-injectivity of
`H`, and equality of projective and injective `H`-modules.

## Main results

* `TauCeti.finrank_leftCointegrals`, `TauCeti.finrank_rightCointegrals`,
  `TauCeti.finrank_leftIntegral`, `TauCeti.finrank_rightIntegral`: all four integral and
  cointegral subspaces of a finite-dimensional Hopf algebra have dimension `1`.
* `TauCeti.HopfAlgebra.exists_isFrobeniusFunctional`: every finite-dimensional Hopf algebra over a
  field admits a Frobenius functional.
* `TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`: the antipode of a
  finite-dimensional Hopf algebra over a field is bijective.
* `TauCeti.HopfAlgebra.moduleInjective_self`, `TauCeti.HopfAlgebra.moduleInjective_op_self`,
  `TauCeti.HopfAlgebra.moduleProjective_iff_moduleInjective`: self-injectivity and coincidence of
  projective and injective modules over a finite-dimensional Hopf algebra.

## References

* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Chapter 2.
* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for
  Hopf algebras*, Amer. J. Math. 91 (1969), 75–94.
* M. Khovanov, *Hopfological algebra and categorification at a root of unity: the first steps*,
  J. Knot Theory Ramifications 25 (2016), Proposition 1.

The nondegeneracy input is the algebraic faithfulness theorem in
`TauCeti.Algebra.HopfAlgebra.Integral`.
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
    hφ.sum_apply_mul_smul_antipode t.property ht r x

/-- The antipode is bijective whenever a finite-dimensional Hopf algebra admits
a nonzero right invariant functional. -/
theorem IsRightInvariantIntegral.antipode_bijective [FiniteDimensional k H]
    (hφ : φ.IsRightInvariantIntegral) (h0 : φ ≠ 0) :
    Function.Bijective (antipode k : H → H) :=
  ⟨LinearMap.injective_iff_surjective.mpr (hφ.antipode_surjective h0),
    hφ.antipode_surjective h0⟩

end Hopf

section SemiringReconstruction

variable {R A : Type*} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Reconstruction from the coproduct of a normalized right integral against a left invariant
functional, dual to `IsRightInvariantIntegral.sum_apply_mul_smul_antipode`. -/
theorem IsLeftInvariantIntegral.sum_apply_mul_smul_antipode {φ : A →ₗ[R] R}
    (hφ : φ.IsLeftInvariantIntegral) {t : A} (ht : t ∈ rightIntegral R A)
    (htφ : φ t = 1) {ι : Type*} (r : Coalgebra.Repr R t ι) (x : A) :
    ∑ i ∈ r.index, φ (r.right i * x) • antipode R (r.left i) = x := by
  classical
  have htx (y : A) : φ (t * y) = counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [← hφ.strong_invariance (ℛ R x) r]
  simpa only [htx] using sum_smul_counit (ℛ R x)

end SemiringReconstruction

end LinearMap

namespace TauCeti

section Bridge

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- `IsRightCointegral` coincides with `LinearMap.IsRightInvariantIntegral`. -/
theorem isRightCointegral_iff_isRightInvariantIntegral (φ : Module.Dual R H) :
    IsRightCointegral φ ↔ φ.IsRightInvariantIntegral := by
  rw [isRightCointegral_def, LinearMap.isRightInvariantIntegral_iff]

/-- `IsLeftCointegral` coincides with `LinearMap.IsLeftInvariantIntegral`. -/
theorem isLeftCointegral_iff_isLeftInvariantIntegral (φ : Module.Dual R H) :
    IsLeftCointegral φ ↔ φ.IsLeftInvariantIntegral := by
  rw [isLeftCointegral_def, LinearMap.isLeftInvariantIntegral_iff]

end Bridge

section LarsonSweedler

variable {k H : Type*} [Field k] [Ring H] [_root_.HopfAlgebra k H] [FiniteDimensional k H]

/-- A nonzero right cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsRightCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  ((isRightCointegral_iff_isRightInvariantIntegral φ).mp hφ).isFrobeniusFunctional h0

/-- A nonzero left cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  ((isLeftCointegral_iff_isLeftInvariantIntegral φ).mp hφ).isFrobeniusFunctional h0

/-- **Larson–Sweedler Theorem (left cointegrals).** The space of left cointegrals on a
finite-dimensional Hopf algebra over a field is one-dimensional. -/
@[simp]
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 := by
  have : Nontrivial H := Bialgebra.nontrivial k
  have h := (leftCointegralsTensorEquiv k H).finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq] at h
  exact Nat.eq_of_mul_eq_mul_right (Module.finrank_pos (R := k) (M := H)) (by simpa using h)

variable (k H) in
/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  have hpos : 0 < Module.finrank k (leftCointegrals k H) := by simp
  obtain ⟨φ, hφ0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := leftCointegrals k H)).mp hpos
  exact ⟨φ.1, (mem_leftCointegrals φ.1).mp φ.2, fun h ↦ hφ0 (Subtype.ext h)⟩

/-- The left-cointegral subspace of a finite-dimensional Hopf algebra over a field is nontrivial. -/
theorem leftCointegrals_ne_bot : leftCointegrals k H ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := exists_isLeftCointegral_ne_zero k H
  exact (leftCointegrals k H).ne_bot_iff.mpr ⟨φ, (mem_leftCointegrals φ).mpr hφ, h0⟩

variable (k H) in
/-- **Every finite-dimensional Hopf algebra over a field is a Frobenius algebra.** -/
theorem HopfAlgebra.exists_isFrobeniusFunctional :
    ∃ φ : Module.Dual k H, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isLeftCointegral_ne_zero k H
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

/-- **Larson–Sweedler Theorem (left integrals).** The space of left integrals in a
finite-dimensional Hopf algebra over a field is one-dimensional. -/
@[simp]
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.finrank_leftIntegral

/-- **Larson–Sweedler Theorem (right integrals).** The space of right integrals in a
finite-dimensional Hopf algebra over a field is one-dimensional. -/
@[simp]
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.finrank_rightIntegral

variable (k H) in
/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left integral. -/
theorem exists_mem_leftIntegral_ne_zero : ∃ t ∈ leftIntegral k H, t ≠ 0 := by
  have hpos : 0 < Module.finrank k (leftIntegral k H) := by simp
  obtain ⟨t, ht0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := leftIntegral k H)).mp hpos
  exact ⟨t.1, t.2, fun h ↦ ht0 (Subtype.ext h)⟩

variable (k H) in
/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right integral. -/
theorem exists_mem_rightIntegral_ne_zero : ∃ t ∈ rightIntegral k H, t ≠ 0 := by
  have hpos : 0 < Module.finrank k (rightIntegral k H) := by simp
  obtain ⟨t, ht0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := rightIntegral k H)).mp hpos
  exact ⟨t.1, t.2, fun h ↦ ht0 (Subtype.ext h)⟩

/-- The left-integral subspace of a finite-dimensional Hopf algebra over a field is nontrivial. -/
theorem leftIntegral_ne_bot : leftIntegral k H ≠ ⊥ := by
  obtain ⟨t, ht, h0⟩ := exists_mem_leftIntegral_ne_zero k H
  exact (leftIntegral k H).ne_bot_iff.mpr ⟨t, ht, h0⟩

/-- The right-integral subspace of a finite-dimensional Hopf algebra over a field is nontrivial. -/
theorem rightIntegral_ne_bot : rightIntegral k H ≠ ⊥ := by
  obtain ⟨t, ht, h0⟩ := exists_mem_rightIntegral_ne_zero k H
  exact (rightIntegral k H).ne_bot_iff.mpr ⟨t, ht, h0⟩

/-- **Larson–Sweedler Theorem (right cointegrals).** The space of right cointegrals on a
finite-dimensional Hopf algebra over a field is one-dimensional. -/
@[simp]
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  rw [(rightCointegralsEquivRightIntegral k H).finrank_eq]
  exact finrank_rightIntegral (k := k) (H := ConvolutionDual k H)

variable (k H) in
/-- Every finite-dimensional Hopf algebra over a field admits a nonzero right cointegral. -/
theorem exists_isRightCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsRightCointegral φ ∧ φ ≠ 0 := by
  have hpos : 0 < Module.finrank k (rightCointegrals k H) := by simp
  obtain ⟨φ, hφ0⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := rightCointegrals k H)).mp hpos
  exact ⟨φ.1, (mem_rightCointegrals φ.1).mp φ.2, fun h ↦ hφ0 (Subtype.ext h)⟩

/-- The right-cointegral subspace of a finite-dimensional Hopf algebra over a field is
nontrivial. -/
theorem rightCointegrals_ne_bot : rightCointegrals k H ≠ ⊥ := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact (rightCointegrals k H).ne_bot_iff.mpr ⟨φ, (mem_rightCointegrals φ).mpr hφ, h0⟩

/-- **Radford–Larson–Sweedler Antipode Bijectivity.** The antipode of any finite-dimensional Hopf
algebra over a field is bijective. -/
theorem HopfAlgebra.antipode_bijective_of_finiteDimensional :
    Function.Bijective (antipode k : H →ₗ[k] H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact ((isRightCointegral_iff_isRightInvariantIntegral φ).mp hφ).antipode_bijective h0

/-- **A finite-dimensional Hopf algebra over a field is left self-injective.** -/
theorem HopfAlgebra.moduleInjective_self (k H : Type*) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] : Module.Injective H H := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_self

/-- **A finite-dimensional Hopf algebra over a field is right self-injective.** -/
theorem HopfAlgebra.moduleInjective_op_self (k H : Type*) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] : Module.Injective Hᵐᵒᵖ H := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_op_self

universe w in
/-- **Projective modules over a finite-dimensional Hopf algebra are injective.** No finiteness is
assumed on the module. -/
theorem HopfAlgebra.moduleInjective_of_projective (k H : Type*) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] (P : Type w) [AddCommGroup P] [Module H P]
    [Module.Projective H P] : Module.Injective H P := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_of_projective P

universe w in
/-- **Injective modules over a finite-dimensional Hopf algebra are projective.** No finiteness is
assumed on the module. -/
theorem HopfAlgebra.moduleProjective_of_injective (k H : Type*) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] [Small.{w} H] (M : Type w) [AddCommGroup M]
    [Module H M] [Module.Injective H M] : Module.Projective H M := by
  obtain ⟨φ, hφ⟩ := HopfAlgebra.exists_isFrobeniusFunctional k H
  exact hφ.moduleProjective_of_injective M

universe w in
/-- **Projective and injective modules over a finite-dimensional Hopf algebra coincide**
(Khovanov, Proposition 1): an arbitrary left `H`-module, not necessarily finitely generated, is
projective if and only if it is injective. -/
theorem HopfAlgebra.moduleProjective_iff_moduleInjective (k H : Type*) [Field k] [Ring H]
    [_root_.HopfAlgebra k H] [FiniteDimensional k H] [Small.{w} H] (M : Type w) [AddCommGroup M]
    [Module H M] : Module.Projective H M ↔ Module.Injective H M :=
  ⟨fun _ ↦ HopfAlgebra.moduleInjective_of_projective k H M,
    fun _ ↦ HopfAlgebra.moduleProjective_of_injective k H M⟩

end LarsonSweedler

end TauCeti
