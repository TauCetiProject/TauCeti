/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import TauCeti.Algebra.Module.LocalizedModule.BaseChange
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.TensorProduct.IsBaseChange

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

When `N` and `P` are `S`-modules over `R → S` and `g : N →ₗ[S] P` becomes bijective at
`Algebra.algebraMapSubmonoid S T`, `LinearMap.bijective_localizedMap_fst_ker_coprod` packages the
resulting bijectivity of `LocalizedModule.map T` on the first projection, and
`LinearMap.surjective_localizedMap_liftBaseChange_snd_ker_coprod` deduces surjectivity of the
scalar-extension comparison `S ⊗[R] K →ₗ[S] N` at `Algebra.algebraMapSubmonoid S T` whenever
`f.liftBaseChange S` is surjective there.

The proof uses Mathlib's `LinearMap.toKerLocalized_isLocalizedModule` (localization
commutes with kernels) and `IsLocalizedModule.prodMap` (localization commutes with
binary products).

In formal gluing, `N` and `P` are modules over an `R`-algebra `S` and `g` is `S`-linear;
`LinearMap.isLocalizedModule_fst_ker_coprod_restrictScalars` states the comparison when `g`
becomes bijective after inverting the image of `r : R` in `S`.

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

section BaseChange

variable {S : Type*} [CommSemiring S] [Algebra R S]
  [Module S N] [IsScalarTower R S N] [Module S P] [IsScalarTower R S P]

/-- Elements `(m, n)` in `ker (f.coprod (-g.restrictScalars R))` satisfy `f m = g n`. -/
theorem apply_fst_ker_coprod_eq (f : M →ₗ[R] P) (g : N →ₗ[S] P)
    (k : (f.coprod (-g.restrictScalars R)).ker) :
    f (((LinearMap.fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker) k) =
      g (((LinearMap.snd R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker) k) := by
  simpa only [mem_ker, coprod_apply, LinearMap.neg_apply, coe_restrictScalars, add_neg_eq_zero,
    domRestrict_apply, fst_apply, snd_apply] using k.property

/-- If `g : N →ₗ[S] P` becomes bijective after localizing at `Algebra.algebraMapSubmonoid S T`,
then the first projection from compatible pairs `ker (f.coprod (-g)) → M` becomes bijective after
localizing at `T`. -/
theorem bijective_localizedMap_fst_ker_coprod (f : M →ₗ[R] P) (g : N →ₗ[S] P) (T : Submonoid R)
    (hg : Bijective (LocalizedModule.map (Algebra.algebraMapSubmonoid S T) g)) :
    Bijective (LocalizedModule.map T
      ((LinearMap.fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker)) := by
  let b := (LinearMap.fst R M N).domRestrict (f.coprod (-g.restrictScalars R)).ker
  have hgR : Bijective (LocalizedModule.map T (g.restrictScalars R)) :=
    (LocalizedModule.map_algebraMapSubmonoid_bijective_iff g).mp hg
  have hb_loc : IsLocalizedModule T (LocalizedModule.mkLinearMap T M ∘ₗ b) :=
    isLocalizedModule_fst_ker_coprod f (g.restrictScalars R) T
      (LocalizedModule.mkLinearMap T M)
      (LocalizedModule.mkLinearMap T N)
      (LocalizedModule.mkLinearMap T P)
      ((IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
        (LocalizedModule.mkLinearMap T N) (LocalizedModule.mkLinearMap T P)).mpr hgR)
  have hid : IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M ∘ₗ b)
      (LocalizedModule.mkLinearMap T M) b = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext T
      (LocalizedModule.mkLinearMap T M ∘ₗ b) (LocalizedModule.mkLinearMap T M)
    rw [IsLocalizedModule.map_comp]
    rfl
  refine (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (LocalizedModule.mkLinearMap T M ∘ₗ b) (LocalizedModule.mkLinearMap T M)).mp ?_
  rw [hid]
  exact bijective_id

/-- If `f.liftBaseChange S` becomes surjective and `g` becomes bijective at
`Algebra.algebraMapSubmonoid S T`, then the scalar-extension comparison `S ⊗[R] K →ₗ[S] N` from
compatible pairs becomes surjective at `Algebra.algebraMapSubmonoid S T`. -/
theorem surjective_localizedMap_liftBaseChange_snd_ker_coprod
    (f : M →ₗ[R] P) (g : N →ₗ[S] P) (T : Submonoid R)
    (hf : Surjective (LocalizedModule.map (Algebra.algebraMapSubmonoid S T) (f.liftBaseChange S)))
    (hg : Bijective (LocalizedModule.map (Algebra.algebraMapSubmonoid S T) g)) :
    Surjective (LocalizedModule.map (Algebra.algebraMapSubmonoid S T)
      (((LinearMap.snd R M N).domRestrict
        (f.coprod (-g.restrictScalars R)).ker).liftBaseChange S)) := by
  let U := Algebra.algebraMapSubmonoid S T
  let K := (f.coprod (-g.restrictScalars R)).ker
  let b := (LinearMap.fst R M N).domRestrict K
  let c := (LinearMap.snd R M N).domRestrict K
  have hb_bij : Bijective (LocalizedModule.map U (b.baseChange S)) :=
    LocalizedModule.map_baseChange_bijective b (bijective_localizedMap_fst_ker_coprod f g T hg)
  have hsq : LocalizedModule.map U g ∘ₗ LocalizedModule.map U (c.liftBaseChange S) =
      LocalizedModule.map U (f.liftBaseChange S) ∘ₗ LocalizedModule.map U (b.baseChange S) := by
    rw [← LocalizedModule.map_comp, ← LocalizedModule.map_comp,
      (LinearMap.liftBaseChange_comp_baseChange S
        (LinearMap.ext (apply_fst_ker_coprod_eq f g))).symm]
  have hsurj : Surjective (⇑(LocalizedModule.map U g) ∘
      ⇑(LocalizedModule.map U (c.liftBaseChange S))) := by
    rw [← LinearMap.coe_comp, hsq]
    exact hf.comp hb_bij.2
  exact (Surjective.of_comp_iff' hg _).mp hsurj

/-- **Localization of compatible pairs, for a map of modules over an algebra.** If `g : N → P`
is `S`-linear and becomes bijective after inverting the image of `r : R` in `S`, then the map
from pairs `(x, y)` satisfying `f x = g y` to the localization of `M` at `r` is a localization
map. -/
theorem isLocalizedModule_fst_ker_coprod_restrictScalars (f : M →ₗ[R] P) (g : N →ₗ[S] P) (r : R)
    (hg : Bijective (LocalizedModule.map (.powers (algebraMap R S r)) g)) :
    IsLocalizedModule (.powers r) (LocalizedModule.mkLinearMap (.powers r) M ∘ₗ
      fst R M N ∘ₗ (ker (f.coprod (-g.restrictScalars R))).subtype) := by
  let n := (LocalizedModule.mkLinearMap (.powers (algebraMap R S r)) N).restrictScalars R
  let p := (LocalizedModule.mkLinearMap (.powers (algebraMap R S r)) P).restrictScalars R
  have : IsLocalizedModule (.powers r) n := IsLocalizedModule.restrictScalars_powers r _
  have : IsLocalizedModule (.powers r) p := IsLocalizedModule.restrictScalars_powers r _
  refine isLocalizedModule_fst_ker_coprod f (g.restrictScalars R) _ _ n p ?_
  have heq : IsLocalizedModule.map (.powers r) n p (g.restrictScalars R) =
      (LocalizedModule.map (.powers (algebraMap R S r)) g).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (.powers r) n p
    ext x
    simp [n, p, IsLocalizedModule.map_comp]
  rw [heq]
  exact hg

end BaseChange

end LinearMap
