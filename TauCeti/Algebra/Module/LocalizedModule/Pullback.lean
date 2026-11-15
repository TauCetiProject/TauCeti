/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# Localization of compatible pairs

For maps `f : M → P` and `g : N → P`, the module of compatible pairs is
`ker (f.coprod (-g))`, a submodule of `M × N`. If localization makes `g` an
isomorphism, projection from this module to `M` becomes an isomorphism after the
same localization. Thus compatible pairs recover the prescribed module on any
principal open where the second map is an isomorphism.

This is the principal-open comparison in the construction of a module by formal
gluing: `N` is the module on the formal neighbourhood, `M` is the module of sections
on the complementary open, and `P` is the module on their overlap. The comparison
requires neither finite generation nor any assumption on a completion map.

The proof uses Mathlib's `LinearMap.toKerLocalized_isLocalizedModule` (localization
commutes with kernels) and `IsLocalizedModule.prodMap` (localization commutes with
binary products).

## References

* The Stacks Project, Proposition 15.91.16 (05ER), formal gluing of modules;
  the localization comparison proved here is a step in its proof.
-/

public section

open Function

namespace LinearMap

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- **Localization of compatible pairs.** If localization at `S` makes `g : N → P`
bijective, then the map from pairs `(x, y)` satisfying `f x = g y` to a localization
of `M`, given by `(x, y) ↦ m x`, is a localization map. In particular, its target
is canonically the localization of the module of compatible pairs. -/
theorem isLocalizedModule_fst_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[R] P)
    (S : Submonoid R) {M' N' P' : Type*}
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    [AddCommGroup P'] [Module R P']
    (m : M →ₗ[R] M') (n : N →ₗ[R] N') (p : P →ₗ[R] P')
    [IsLocalizedModule S m] [IsLocalizedModule S n] [IsLocalizedModule S p]
    (hg : Bijective (IsLocalizedModule.map S n p g)) :
    IsLocalizedModule S (m ∘ₗ fst R M N ∘ₗ (ker (f.coprod (-g))).subtype) := by
  let F := m.prodMap n
  let d := f.coprod (-g)
  let f' := IsLocalizedModule.map S m p f
  let g' := IsLocalizedModule.map S n p g
  let d' := IsLocalizedModule.map S F p d
  have hg' : Bijective g' := hg
  have hd' : d' = f'.coprod (-g') := by
    apply IsLocalizedModule.linearMap_ext S F p
    rw [IsLocalizedModule.map_comp]
    apply LinearMap.ext
    intro x
    simp [f', g', F, d, IsLocalizedModule.map_apply]
  let π : ker d' →ₗ[R] M' :=
    fst R _ _ ∘ₗ (ker d').subtype
  have hpair (x : ker d') : f' x.val.1 = g' x.val.2 := by
    have hx := x.property
    simpa only [mem_ker, hd', coprod_apply, LinearMap.neg_apply, add_neg_eq_zero] using hx
  have hπ : Bijective π := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      refine Prod.ext hxy (hg'.1 ?_)
      exact (hpair x).symm.trans ((congrArg f' hxy).trans (hpair y))
    · intro x
      obtain ⟨y, hy⟩ := hg'.2 (f' x)
      refine ⟨⟨(x, y), ?_⟩, rfl⟩
      simp [mem_ker, hd', hy]
  let := IsLocalizedModule.module (A := Localization S) S F
  let := IsLocalizedModule.isScalarTower_module (A := Localization S) S F
  let := IsLocalizedModule.module (A := Localization S) S p
  let := IsLocalizedModule.isScalarTower_module (A := Localization S) S p
  have hker := toKerLocalized_isLocalizedModule (S := Localization S) S F p d
  have hcomp : π ∘ₗ toKerIsLocalized S F p d =
      m ∘ₗ fst R M N ∘ₗ (ker d).subtype := by
    ext x
    simp [π, toKerIsLocalized, F]
  rw [← hcomp]
  exact (IsLocalizedModule.comp_iff_of_bijective_left S π hπ).mpr hker

end LinearMap
