/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Localization of compatible pairs

For maps `f : M → P` and `g : N → P`, the module of compatible pairs is
`ker (f.coprod (-g))`, a submodule of `M × N`. If localization makes `g` an
isomorphism, projection from this module to `M` becomes an isomorphism after the
same localization (`LinearMap.isLocalizedModule_fst_ker_coprod`,
`LinearMap.bijective_localizedModuleMap_fst_ker_coprod`). When `N` and `P` are `S`-modules over an
`R`-algebra `S` and `f.liftBaseChange S` also becomes surjective after localization, the comparison
map `S ⊗[R] ker (f.coprod (-g)) → N` induced by the second projection becomes surjective after
localization (`LinearMap.surjective_localizedModuleMap_liftBaseChange_snd_ker_coprod`). Thus
compatible pairs recover the prescribed module on any localization where the overlap comparison is
an isomorphism.

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

section Algebra

open scoped TensorProduct

variable {S : Type*} [CommSemiring S] [Algebra R S]
  [Module S N] [IsScalarTower R S N] [Module S P] [IsScalarTower R S P]

/-- If `g : N →ₗ[S] P` becomes bijective after localizing at the image of `T : Submonoid R` in
`S`, then the first projection from the `R`-module of compatible pairs `ker (f.coprod (-g))` to
`M` becomes bijective after localizing at `T`. -/
theorem bijective_localizedModuleMap_fst_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[S] P)
    (T : Submonoid R) (hg : Bijective (LocalizedModule.map (T.map (algebraMap R S)) g)) :
    Bijective (LocalizedModule.map T
      ((LinearMap.fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker)) := by
  -- `Algebra.algebraMapSubmonoid S T` is `T.map (algebraMap R S)` by definition.
  let T' : Submonoid S := Algebra.algebraMapSubmonoid S T
  let m := LocalizedModule.mkLinearMap T M
  let n := (LocalizedModule.mkLinearMap T' N).restrictScalars R
  let p := (LocalizedModule.mkLinearMap T' P).restrictScalars R
  have : IsLocalizedModule T n := IsLocalizedModule.restrictScalars T _
  have : IsLocalizedModule T p := IsLocalizedModule.restrictScalars T _
  have hmap_eq :
      IsLocalizedModule.map T n p (g.restrictScalars R) =
        (LocalizedModule.map T' g).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext T n p
    refine LinearMap.ext fun x ↦ ?_
    exact (IsLocalizedModule.map_apply T n p (g.restrictScalars R) x).trans
      (LocalizedModule.map_mk T' g x 1).symm
  have hg_map : Bijective (IsLocalizedModule.map T n p (g.restrictScalars R)) := by
    rw [hmap_eq]
    exact hg
  let fstK := (fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker
  let g₁ := m ∘ₗ fst R M N ∘ₗ (ker (f.coprod (-g.restrictScalars R))).subtype
  have : IsLocalizedModule T g₁ :=
    isLocalizedModule_fst_ker_coprod f (g.restrictScalars R) T m n p hg_map
  have hid : IsLocalizedModule.map T g₁ m fstK = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext T g₁ m
    refine LinearMap.ext fun x ↦ ?_
    exact IsLocalizedModule.map_apply T g₁ m fstK x
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective g₁ m).mp
    (hid ▸ Function.bijective_id)

/-- If `g : N →ₗ[S] P` becomes bijective after inverting `algebraMap R S r`, then the first
projection from the `R`-module of compatible pairs `ker (f.coprod (-g))` to `M` becomes bijective
after inverting `r`. -/
theorem bijective_localizedModuleMap_powers_fst_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[S] P)
    (r : R) (hg : Bijective (LocalizedModule.map (.powers (algebraMap R S r)) g)) :
    Bijective (LocalizedModule.map (.powers r)
      ((LinearMap.fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker)) :=
  bijective_localizedModuleMap_fst_ker_coprod f g (.powers r) (by rwa [Submonoid.map_powers])

/-- If `f.liftBaseChange S : S ⊗[R] M →ₗ[S] P` becomes surjective and `g : N →ₗ[S] P` becomes
bijective after localizing at `T.map (algebraMap R S)`, then the map
`S ⊗[R] ker (f.coprod (-g)) →ₗ[S] N` induced by the second projection also becomes surjective
after localizing at `T.map (algebraMap R S)`. -/
theorem surjective_localizedModuleMap_liftBaseChange_snd_ker_coprod (f : M →ₗ[R] P)
    (g : N →ₗ[S] P) (T : Submonoid R)
    (hf : Surjective (LocalizedModule.map (T.map (algebraMap R S)) (f.liftBaseChange S)))
    (hg : Bijective (LocalizedModule.map (T.map (algebraMap R S)) g)) :
    Surjective (LocalizedModule.map (T.map (algebraMap R S))
      (((LinearMap.snd R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker).liftBaseChange
        S)) := by
  let K := (f.coprod (-g.restrictScalars R)).ker
  let fstK : K →ₗ[R] M := (LinearMap.fst R M N).domRestrict K
  let sndK : K →ₗ[R] N := (LinearMap.snd R M N).domRestrict K
  have hcomm : f.comp fstK = (g.restrictScalars R).comp sndK :=
    LinearMap.ext fun k ↦ add_neg_eq_zero.mp k.2
  have hcomm_bc : (f.liftBaseChange S).comp (fstK.baseChange S) = g.comp (sndK.liftBaseChange S) :=
    LinearMap.liftBaseChange_comp_baseChange S hcomm
  have hfst : Bijective (LocalizedModule.map T fstK) :=
    bijective_localizedModuleMap_fst_ker_coprod f g T hg
  have hsurj_comp : Surjective (LocalizedModule.map (T.map (algebraMap R S))
      ((f.liftBaseChange S).comp (fstK.baseChange S))) := by
    rw [LocalizedModule.map_comp]
    exact hf.comp (fstK.surjective_localizedModuleMap_map_baseChange hfst.2)
  rw [hcomm_bc, LocalizedModule.map_comp, LinearMap.coe_comp] at hsurj_comp
  exact hsurj_comp.of_comp_left hg.1

/-- If `f.liftBaseChange S` becomes surjective and `g` becomes bijective after inverting
`algebraMap R S r`, then the map `S ⊗[R] ker (f.coprod (-g)) →ₗ[S] N` induced by the second
projection becomes surjective after inverting `algebraMap R S r`. -/
theorem surjective_localizedModuleMap_powers_liftBaseChange_snd_ker_coprod (f : M →ₗ[R] P)
    (g : N →ₗ[S] P) (r : R)
    (hf : Surjective (LocalizedModule.map (.powers (algebraMap R S r)) (f.liftBaseChange S)))
    (hg : Bijective (LocalizedModule.map (.powers (algebraMap R S r)) g)) :
    Surjective (LocalizedModule.map (.powers (algebraMap R S r))
      (((LinearMap.snd R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker).liftBaseChange
        S)) := by
  rw [← Submonoid.map_powers] at hf hg ⊢
  exact surjective_localizedModuleMap_liftBaseChange_snd_ker_coprod f g (.powers r) hf hg

end Algebra

end LinearMap
