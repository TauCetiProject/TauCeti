/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.Defs

import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Lifting maps into a localization when the localization map is injective

Let `g : N →ₗ[R] N'` exhibit `N'` as the localization of `N` at a submonoid `S`. A linear map
`l : M →ₗ[R] N'` from a finitely generated module `M` takes values with denominators, but
finitely many generators of `M` have a common denominator `s ∈ S`, so `s • l` takes values in the
image of `g`. When `g` is injective, which happens exactly when every element of `S` acts
injectively on `N` (`IsLocalizedModule.injective_iff_isRegular`), this gives an `R`-linear map
`h : M →ₗ[R] N` with `g ∘ₗ h = s • l`. More generally, if `g` and `l` are linear over an
`R`-algebra `A` and `M` is finitely generated over `A`, the lift `h` can be chosen `A`-linear.

Mathlib's `Module.FinitePresentation.exists_lift_of_isLocalizedModule` proves the same
conclusion for a finitely presented `M` and an arbitrary localization map. The version here
trades the finite presentation of `M` for injectivity of `g`: the lift is then read off from the
image of `g` rather than built from a presentation. It is the form used to clear denominators
between lattices, which are torsion-free but need not be finitely presented over a
non-Noetherian base.

Applying this to `Finsupp.mapRange.linearMap (Algebra.linearMap R A)` clears denominators in the
coordinates of any `R`-linear map `M →ₗ[R] E` with respect to an `A`-basis of `E`, producing an
`R`-linear map `M →ₗ[R] (ι → R)` that is injective whenever `M →ₗ[R] E` is.

## Main results

* `Module.Finite.exists_lift_of_isLocalizedModule_of_injective`: a linear map from a finitely
  generated module into an injective localization lifts after multiplication by an element of
  the submonoid, linearly over any algebra acting compatibly.
* `Module.Finite.exists_lift_pi_of_basis` and `Module.Finite.exists_injective_lift_pi_of_basis`:
  clearing denominators of coordinates with respect to a basis over an injective localization.
-/

public section

namespace Module.Finite

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {A : Type*} [Semiring A] [Algebra R A]
  {M N N' : Type*} [AddCommMonoid M] [Module A M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]
  [AddCommMonoid N'] [Module R N'] [Module A N'] [IsScalarTower R A N']
  {g : N →ₗ[A] N'} [IsLocalizedModule S (g.restrictScalars R)]

/-- An `A`-linear map from a finitely generated `A`-module into the localization `N'` of `N` lifts
to an `A`-linear map into `N` after multiplication by an element of `S`, provided the localization
map `g` is injective. Taking `A = R` gives the statement for plain `R`-linear maps. -/
theorem exists_lift_of_isLocalizedModule_of_injective [Module.Finite A M]
    (hg : Function.Injective g) (l : M →ₗ[A] N') :
    ∃ (h : M →ₗ[A] N) (s : S), g ∘ₗ h = s • l := by
  obtain ⟨T, hT⟩ := ‹Module.Finite A M›
  obtain ⟨s, hs⟩ := IsLocalizedModule.exist_integer_multiples S (g.restrictScalars R) T l
  -- The elements whose image under `s • l` comes from `N` form a submodule containing `T`.
  have hrange : LinearMap.range (s • l) ≤ LinearMap.range g := by
    rw [LinearMap.range_le_iff_comap, eq_top_iff, ← hT, Submodule.span_le]
    exact fun x hx ↦ by simpa [IsLocalizedModule.IsInteger, Submonoid.smul_def] using hs x hx
  refine ⟨(LinearEquiv.ofInjective g hg).symm.toLinearMap ∘ₗ
    (s • l).codRestrict _ fun m ↦ hrange (LinearMap.mem_range_self _ m), s, ?_⟩
  ext m
  simp [LinearEquiv.ofInjective_symm_apply]

/-- Clearing denominators of coordinates with respect to a basis over an injective localization.
Given an `R`-linear map `f : M →ₗ[R] E` from a finite `R`-module into an `A`-module with basis
`b : Module.Basis ι A E`, where `A` is an injective localization of `R` at `S`, there exist
`Ψ : M →ₗ[R] (ι → R)` and `s : S` such that
`algebraMap R A (Ψ m i) = algebraMap R A s * b.repr (f m) i` for all `m` and `i`. -/
theorem exists_lift_pi_of_basis {R : Type*} [CommSemiring R] (S : Submonoid R)
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    (ha : Function.Injective (algebraMap R A))
    {M E ι : Type*} [AddCommMonoid M] [Module R M] [Module.Finite R M]
    [AddCommMonoid E] [Module R E] [Module A E] [IsScalarTower R A E]
    (b : Module.Basis ι A E) (f : M →ₗ[R] E) :
    ∃ (Ψ : M →ₗ[R] (ι → R)) (s : S),
      ∀ m i, algebraMap R A (Ψ m i) = algebraMap R A (s : R) * b.repr (f m) i := by
  let g : (ι →₀ R) →ₗ[R] (ι →₀ A) := Finsupp.mapRange.linearMap (Algebra.linearMap R A)
  have hg : Function.Injective g :=
    fun x y hxy ↦ Finsupp.ext fun i ↦ ha (DFunLike.congr_fun hxy i)
  have : IsLocalizedModule S (g.restrictScalars R) := by
    rw [LinearMap.restrictScalars_self]
    infer_instance
  let l : M →ₗ[R] (ι →₀ A) := (b.repr.toLinearMap.restrictScalars R).comp f
  obtain ⟨h, s, hs⟩ := exists_lift_of_isLocalizedModule_of_injective S (A := R) hg l
  refine ⟨LinearMap.pi fun i ↦ (Finsupp.lapply i).comp h, s, fun m i ↦ ?_⟩
  have hm := DFunLike.congr_fun (LinearMap.congr_fun hs m) i
  simpa [g, l, Submonoid.smul_def, Algebra.smul_def] using hm

/-- If moreover `f : M →ₗ[R] E` is injective in `exists_lift_pi_of_basis`, then the cleared
coordinate map `Ψ : M →ₗ[R] (ι → R)` is injective. -/
theorem exists_injective_lift_pi_of_basis {R : Type*} [CommSemiring R] (S : Submonoid R)
    {A : Type*} [CommSemiring A] [Algebra R A] [IsLocalization S A]
    (ha : Function.Injective (algebraMap R A))
    {M E ι : Type*} [AddCommMonoid M] [Module R M] [Module.Finite R M]
    [AddCommMonoid E] [Module R E] [Module A E] [IsScalarTower R A E]
    (b : Module.Basis ι A E) {f : M →ₗ[R] E} (hf : Function.Injective f) :
    ∃ (Ψ : M →ₗ[R] (ι → R)) (s : S), Function.Injective Ψ ∧
      ∀ m i, algebraMap R A (Ψ m i) = algebraMap R A (s : R) * b.repr (f m) i := by
  obtain ⟨Ψ, s, hΨ⟩ := exists_lift_pi_of_basis S ha b f
  refine ⟨Ψ, s, fun m₁ m₂ hm ↦ hf <| b.repr.injective <| Finsupp.ext fun i ↦ ?_, hΨ⟩
  have hmul : algebraMap R A (s : R) * b.repr (f m₁) i =
      algebraMap R A (s : R) * b.repr (f m₂) i := by
    rw [← hΨ, ← hΨ, hm]
  exact (IsLocalization.map_units A s).mul_left_cancel hmul

end Module.Finite
