/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Int
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Lifting maps and eigenvectors into a localization when the localization map is injective

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

The same clearing of denominators applies to a single vector. If the operators `T' i` on `N'`
extend operators `T i` on `N`, and a nonzero `v : N'` is a common eigenvector of the `T' i` whose
eigenvalues lie in `R`, then a multiple `s • v` with `s ∈ S` is the image of a nonzero common
eigenvector of the `T i` with the same eigenvalues, for an arbitrary family of operators. This is
how an eigenvector found over the fraction field of a domain gives an integral eigenvector of a
lattice. The integral eigenvector represents the same line, but nothing is claimed about its
reduction modulo an ideal.

## Main results

* `Module.Finite.exists_lift_of_isLocalizedModule_of_injective`: a linear map from a finitely
  generated module into an injective localization lifts after multiplication by an element of
  the submonoid, linearly over any algebra acting compatibly.
* `IsLocalizedModule.exists_ne_zero_forall_apply_eq_smul_of_injective`: a common eigenvector in an
  injective localization, with eigenvalues in the base ring, has a nonzero multiple coming from a
  common eigenvector with the same eigenvalues.

## References

* P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ENS 7 (1974),
  Lemme 6.11 and its proof, for integral eigenvectors of Hecke operators.
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

end Module.Finite

namespace IsLocalizedModule

variable {R : Type*} [CommSemiring R] (S : Submonoid R) {N N' : Type*} [AddCommMonoid N]
  [Module R N] [AddCommMonoid N'] [Module R N'] {g : N →ₗ[R] N'} [IsLocalizedModule S g]

/-- **Integral representatives of common eigenvectors.** Let `g : N → N'` be an injective
localization map at `S`, and let the operators `T' i` on `N'` extend the operators `T i` on `N`.
If a nonzero `v : N'` satisfies `T' i v = b i • v` for all `i`, with eigenvalues `b i` in `R`, then
some nonzero `n : N` with `g n = s • v` for an `s ∈ S` satisfies `T i n = b i • n` for all `i`.
The family of operators may be infinite. -/
theorem exists_ne_zero_forall_apply_eq_smul_of_injective {ι : Type*} (hg : Function.Injective g)
    {T : ι → Module.End R N} {T' : ι → Module.End R N'} (hT : ∀ i, T' i ∘ₗ g = g ∘ₗ T i)
    {b : ι → R} {v : N'} (hv : v ≠ 0) (hTv : ∀ i, T' i v = b i • v) :
    ∃ n : N, n ≠ 0 ∧ (∀ i, T i n = b i • n) ∧ ∃ s : S, g n = s • v := by
  obtain ⟨⟨n, s⟩, hs⟩ := IsLocalizedModule.surj S g v
  refine ⟨n, ?_, fun i ↦ hg ?_, s, hs.symm⟩
  · rintro rfl
    exact hv (IsLocalizedModule.smul_injective g s (by simpa using hs))
  · rw [map_smul, ← LinearMap.comp_apply, ← hT i, LinearMap.comp_apply, ← hs,
      LinearMap.map_smul_of_tower, hTv, smul_comm]

end IsLocalizedModule
