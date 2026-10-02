/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Flat.Localization

/-!
# The rank of a module tensored with a localization

Localizing a module at a submonoid of non-zero-divisors does not change its rank over the base
ring (`IsLocalizedModule.finrank_eq`), and tensoring with the localization `A` of `R` is such a
localization (`IsLocalization.tensorProduct_isLocalizedModule`). Mathlib states this for
`A ⊗[R] M`; this file records the same formula for `M ⊗[R] A`, the form in which a
rationalization `M ⊗[ℤ_p] ℚ_p` of a `ℤ_p`-module is written. Since `M ⊗[R] A` is an `A`-module
on which `R` acts through `A`, its `R`-rank is also its `A`-rank; for `A` a field this is the
dimension of the vector space `M ⊗[R] A`.

Conversely, over a domain the rank detects isomorphisms after passing to the field of fractions:
an injective linear map between finite modules of the same rank has torsion cokernel, so it
becomes an isomorphism after tensoring with the field of fractions. This is how an integral
lattice of full rank in a module computes its rationalization. The map may be linear over any
`R`-algebra `A`, and its rationalization is then `A`-linear for the module structure of
`TensorProduct.AlgebraTensorModule` on the left factor.

## Main results

* `TauCeti.IsLocalization.finrank_tensorProduct`: `finrank R (M ⊗[R] A) = finrank R M` for a
  localization `A` of `R` at a submonoid of non-zero-divisors.
* `TauCeti.IsFractionRing.rTensor_bijective_of_injective_of_finrank_eq`: an injective linear map
  `f : M → N` with `N` finite and `finrank R M = finrank R N` over a domain `R` becomes bijective
  after tensoring with the field of fractions of `R`.
-/

public section

namespace TauCeti.IsLocalization

open scoped TensorProduct

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] (hS : S ≤ nonZeroDivisors R) (M : Type*) [AddCommGroup M] [Module R M]

include hS in
/-- Tensoring with a localization at a submonoid of non-zero-divisors does not change the rank
over the base ring. -/
theorem finrank_tensorProduct : Module.finrank R (M ⊗[R] A) = Module.finrank R M :=
  (TensorProduct.comm R M A).finrank_eq.trans
    (IsLocalizedModule.finrank_eq S (TensorProduct.mk R A M 1) hS)

end TauCeti.IsLocalization

namespace TauCeti.IsFractionRing

open scoped TensorProduct

variable {R : Type*} [CommRing R] [IsDomain R] (Q : Type*) [CommRing Q] [Algebra R Q]
  [IsFractionRing R Q] {A : Type*} [Ring A] [Algebra R A]
  {M N : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N] [Module.Finite R N]

/-- **Full-rank injections become isomorphisms over the field of fractions.** Let `R` be a domain
with field of fractions `Q`, and `f : M → N` an injective `A`-linear map, for an `R`-algebra `A`,
where `N` is finite over `R` and `M` has the same rank as `N`. Then `f ⊗ 𝟙 Q` is bijective: it is
injective because `Q` is flat over `R`, and surjective because the cokernel of `f` has rank zero,
so it is torsion, and the nonzero elements of `R` are invertible in `Q`. -/
theorem rTensor_bijective_of_injective_of_finrank_eq (f : M →ₗ[A] N)
    (hf : Function.Injective f) (h : Module.finrank R M = Module.finrank R N) :
    Function.Bijective (TensorProduct.AlgebraTensorModule.rTensor R Q f) := by
  have := _root_.IsLocalization.flat Q (nonZeroDivisors R)
  refine ⟨Module.Flat.rTensor_preserves_injective_linearMap (M := Q) (f.restrictScalars R) hf,
    fun x ↦ ?_⟩
  -- The cokernel of `f` has rank zero, hence every element of `N` has a nonzero multiple in the
  -- range of `f`.
  let g := f.restrictScalars R
  have hrank : Module.finrank R (N ⧸ LinearMap.range g) = 0 := by
    have := Submodule.finrank_quotient_add_finrank (LinearMap.range g)
    rw [LinearMap.finrank_range_of_inj (f := g) hf, h] at this
    omega
  have htors (n : N) : ∃ a : R, a ≠ 0 ∧ a • n ∈ LinearMap.range g := by
    obtain ⟨a, ha, han⟩ := Module.finrank_eq_zero_iff.mp hrank (Submodule.Quotient.mk n)
    exact ⟨a, ha, (Submodule.Quotient.mk_eq_zero _).mp (by rwa [Submodule.Quotient.mk_smul])⟩
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩
  | tmul n q =>
    -- With `a • n = f m`, the element `n ⊗ q` is the image of `m ⊗ (a⁻¹ q)`.
    obtain ⟨a, ha, m, hm⟩ := htors n
    obtain ⟨u, hu⟩ := _root_.IsLocalization.map_units Q
      (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ : nonZeroDivisors R)
    refine ⟨m ⊗ₜ (↑u⁻¹ * q), ?_⟩
    rw [TensorProduct.AlgebraTensorModule.rTensor_tmul, ← LinearMap.restrictScalars_apply (R := R),
      hm, TensorProduct.smul_tmul, Algebra.smul_def, ← mul_assoc, ← hu]
    simp

end TauCeti.IsFractionRing
