/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.RingTheory.GradedAlgebra.Connected
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Head coordinates and shift invariance for graded free modules

For a connected nonnegatively `ℤ`-graded `k`-algebra `A` (`𝒜 : ℤ → Submodule k A`,
`∀ i < 0, 𝒜 i = ⊥`, `𝒜 0` in the image of `algebraMap k A` with `FaithfulSMul k A`), the
canonical augmentation `GradedAlgebra.connectedAugmentation : A →ₐ[k] k` induces a `k`-linear
head-coordinate map `TauCeti.GradedModuleCat.freeHeadCoord` on each degree-`q` piece of a shifted
free graded module `free 𝒜 s`.

This file establishes the basic properties of `freeHeadCoord` and deduces shift-multiset and rank
invariance of finite shifted free graded modules up to graded isomorphism, without requiring any
PID or retract hypotheses:

* `TauCeti.GradedModuleCat.map_mem_positive_smul_top`: graded morphisms preserve `A₊ M`.
* `TauCeti.GradedModuleCat.freeHeadCoord`, `TauCeti.GradedModuleCat.freeHeadCoord_eq_zero_iff`,
  `TauCeti.GradedModuleCat.freeHeadCoord_surjective`: the degree-`q` head-coordinate map on
  `free 𝒜 s`, whose kernel is `A₊ (free 𝒜 s) ∩ (free 𝒜 s) q` and which is surjective whenever the
  shift-`q` fiber is finite.
* `TauCeti.GradedModuleCat.card_fiber_eq_of_iso_free`,
  `TauCeti.GradedModuleCat.multiset_map_eq_of_iso_free`,
  `TauCeti.GradedModuleCat.card_eq_of_iso_free`: over a nontrivial commutative base ring `k`,
  isomorphic finite shifted free graded modules have the same shift multiplicities, shift
  multiset, and rank.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4.
-/

public section

noncomputable section

open CategoryTheory _root_.DirectSum
open scoped DirectSum

universe uk uA uI v

namespace TauCeti.GradedModuleCat

open _root_.TauCeti.GradedAlgebra

section General

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Every morphism of graded modules preserves the positive-degree action `A₊ M`. -/
theorem map_mem_positive_smul_top {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun _ _ hx hy ↦ by
    simpa only [map_add] using Submodule.add_mem _ hx hy)
  rw [map_smul]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

variable [GradedAlgebra 𝒜]

/-- Every element of `free 𝒜 s` is the sum over its support of its coordinates times the
corresponding free generators. -/
private theorem eq_sum_support_smul_freeGenerator {I : Type uI} [DecidableEq I] [DecidableEq A]
    (s : I → ℤ) (x : free 𝒜 s) :
    x = ∑ j ∈ x.support, x j • freeGenerator (𝒜 := 𝒜) (d := s) j := by
  conv_lhs => rw [← DirectSum.sum_support_of x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [freeGenerator_eq_lof, ← LinearMap.map_smul, smul_eq_mul, mul_one, DirectSum.lof_eq_of]

end General

section HeadCoordinates

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Reading the augmented coordinates at summands of shift `q` defines a `k`-linear head map on
the degree-`q` piece of `free 𝒜 s`. -/
def freeHeadCoord (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) :
    (free 𝒜 s).grading.piece q →ₗ[k] ({j : I // s j = q} → k) where
  toFun x j := connectedAugmentation hneg hzero (x.val j.val)
  map_add' x y := funext fun j ↦ by
    rw [Submodule.coe_add, DirectSum.add_apply, map_add, Pi.add_apply]
  map_smul' c x := funext fun j ↦ by
    rw [Submodule.coe_smul_of_tower, ← algebraMap_smul A c x.val, DirectSum.smul_apply, smul_eq_mul,
      map_mul, connectedAugmentation_algebraMap, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- `freeHeadCoord` evaluates `connectedAugmentation` on each shift-`q` coordinate. -/
@[simp]
theorem freeHeadCoord_apply (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) (x : (free 𝒜 s).grading.piece q)
    (j : {j : I // s j = q}) :
    freeHeadCoord hneg hzero s q x j = connectedAugmentation hneg hzero (x.val j.val) :=
  (rfl)

omit [FaithfulSMul k A] in
/-- An element of `A₊ (free 𝒜 s)` has every coordinate in the positive-degree ideal `A₊`. -/
private theorem coord_mem_positive_of_mem_positive_smul_top (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {I : Type uI} (s : I → ℤ) {x : free 𝒜 s}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s))) (j : I) :
    x j ∈ ⨆ (i : ℤ) (_ : 0 < i), 𝒜 i := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun u v hu hv ↦ by
    simpa using Submodule.add_mem _ hu hv)
  simpa only [DirectSum.smul_apply, smul_eq_mul] using mul_mem_positive_of_left hneg ha (y j)

/-- A degree-`q` element of `free 𝒜 s` has vanishing head coordinates in degree `q` if and only if
it lies in `A₊ (free 𝒜 s)`. -/
theorem freeHeadCoord_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) (x : (free 𝒜 s).grading.piece q) :
    freeHeadCoord hneg hzero s q x = 0 ↔
      (x : free 𝒜 s) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s)) := by
  constructor
  · intro hx0
    classical
    rw [eq_sum_support_smul_freeGenerator s x.val]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hxj : x.val j ∈ 𝒜 (q - s j) := (mem_free_piece_iff 𝒜 s q x.val).mp x.property j
    rcases lt_trichotomy (s j) q with hlt | hsq | hgt
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (q - s j) (Submodule.mem_iSup_of_mem (by omega) hxj))
        Submodule.mem_top
    · have hxj0 : x.val j ∈ 𝒜 0 := by simpa [hsq] using hxj
      have haug : connectedAugmentation hneg hzero (x.val j) = 0 := congrFun hx0 ⟨j, hsq⟩
      have hzero_coord : x.val j = 0 := by
        rw [← algebraMap_connectedAugmentation_of_mem_zero hneg hzero hxj0, haug, map_zero]
      simp [hzero_coord]
    · have hzero_coord : x.val j = 0 := by simpa [hneg (q - s j) (by omega)] using hxj
      simp [hzero_coord]
  · intro hx
    ext j
    exact (connectedAugmentation_eq_zero_iff hneg hzero).mpr
      (coord_mem_positive_of_mem_positive_smul_top hneg s hx j.val)

omit [FaithfulSMul k A] in
/-- Canonical `k`-linear section of `freeHeadCoord` when the shift-`q` fiber is finite. -/
private def freeHeadLift {I : Type uI} (s : I → ℤ) (q : ℤ) [Fintype {j : I // s j = q}] :
    ({j : I // s j = q} → k) →ₗ[k] (free 𝒜 s).grading.piece q where
  toFun c :=
    ⟨∑ j : {j : I // s j = q}, c j • freeGenerator (𝒜 := 𝒜) (d := s) j.val, by
      refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ (c j) ?_
      simpa [j.property] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) j.val⟩
  map_add' c₁ c₂ := Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
  map_smul' r c := Subtype.ext (by simp [Finset.smul_sum, mul_smul])

private theorem freeHeadCoord_freeHeadLift (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) [Fintype {j : I // s j = q}]
    (c : {j : I // s j = q} → k) :
    freeHeadCoord hneg hzero s q (freeHeadLift s q c) = c := by
  classical
  ext i
  rw [freeHeadCoord_apply]
  have hcoord : (freeHeadLift (𝒜 := 𝒜) s q c).val i.val = algebraMap k A (c i) := by
    dsimp only [freeHeadLift, LinearMap.coe_mk, AddHom.coe_mk]
    rw [DFinsupp.finsetSum_apply]
    simp_rw [← algebraMap_smul A, DirectSum.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [freeGenerator_apply]
    · intro j _ hji
      have hij : j.val ≠ i.val := fun h ↦ hji (Subtype.ext h)
      simp [freeGenerator_apply, hij]
    · exact fun hi ↦ absurd (Finset.mem_univ i) hi
  simp [hcoord]

/-- When the shift-`q` fiber `{j : I // s j = q}` is finite (in particular, for any finite index
type `I`), the head-coordinate map `freeHeadCoord` is surjective. -/
theorem freeHeadCoord_surjective (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) [Finite {j : I // s j = q}] :
    Function.Surjective (freeHeadCoord hneg hzero s q) := by
  cases nonempty_fintype {j : I // s j = q}
  exact fun c ↦ ⟨freeHeadLift s q c, freeHeadCoord_freeHeadLift hneg hzero s q c⟩

/-- Functorial action of a graded morphism between finite shifted free modules on their degree-`q`
head coordinates. -/
private def freeHeadHom (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I J : Type uI} [Fintype I] {s : I → ℤ} {t : J → ℤ}
    (f : free 𝒜 s ⟶ free 𝒜 t) (q : ℤ) :
    ({i : I // s i = q} → k) →ₗ[k] ({j : J // t j = q} → k) :=
  (freeHeadCoord hneg hzero t q).comp
    (LinearMap.codRestrict ((free 𝒜 t).grading.piece q)
      ((f.hom.restrictScalars k).comp (((free 𝒜 s).grading.piece q).subtype.comp
        (freeHeadLift s q)))
      fun c ↦ map_mem f (freeHeadLift s q c).property)

private theorem freeHeadHom_id (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] (s : I → ℤ) (q : ℤ) :
    freeHeadHom hneg hzero (𝟙 (free 𝒜 s)) q = LinearMap.id := by
  ext c j
  dsimp [freeHeadHom]
  exact congrFun (freeHeadCoord_freeHeadLift hneg hzero s q c) j

private theorem freeHeadHom_comp (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I₁ I₂ I₃ : Type uI} [Fintype I₁] [Fintype I₂]
    {d₁ : I₁ → ℤ} {d₂ : I₂ → ℤ} {d₃ : I₃ → ℤ}
    (f : free 𝒜 d₁ ⟶ free 𝒜 d₂) (g : free 𝒜 d₂ ⟶ free 𝒜 d₃) (q : ℤ) :
    freeHeadHom hneg hzero (f ≫ g) q =
      (freeHeadHom hneg hzero g q).comp (freeHeadHom hneg hzero f q) := by
  ext c j
  set y : (free 𝒜 d₂).grading.piece q :=
    ⟨f.hom (freeHeadLift d₁ q c).val, map_mem f (freeHeadLift d₁ q c).property⟩
  set y' : (free 𝒜 d₂).grading.piece q :=
    freeHeadLift d₂ q (freeHeadCoord hneg hzero d₂ q y)
  have hdiff : ((y - y' : (free 𝒜 d₂).grading.piece q) : free 𝒜 d₂) ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d₂)) := by
    rw [← freeHeadCoord_eq_zero_iff hneg hzero d₂ q (y - y'), map_sub,
      freeHeadCoord_freeHeadLift, sub_self]
  have hgdiff : freeHeadCoord hneg hzero d₃ q
      ⟨g.hom (y - y').val, map_mem g (y - y').property⟩ = 0 :=
    (freeHeadCoord_eq_zero_iff hneg hzero d₃ q _).mpr (map_mem_positive_smul_top g hdiff)
  have hg_sub : (⟨g.hom (y - y').val, map_mem g (y - y').property⟩ : (free 𝒜 d₃).grading.piece q) =
      ⟨g.hom y.val, map_mem g y.property⟩ - ⟨g.hom y'.val, map_mem g y'.property⟩ :=
    Subtype.ext (map_sub g.hom y.val y'.val)
  rw [hg_sub, map_sub] at hgdiff
  dsimp [freeHeadHom]
  exact congrFun (sub_eq_zero.mp hgdiff) j

/-- Over a nontrivial commutative ring `k`, isomorphic finite shifted free graded modules over a
connected nonnegatively graded `k`-algebra have the same number of generators in every degree `q`.
-/
theorem card_fiber_eq_of_iso_free [Nontrivial k] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I₁ I₂ : Type uI} [Fintype I₁] [Fintype I₂] {d₁ : I₁ → ℤ} {d₂ : I₂ → ℤ}
    (Φ : free 𝒜 d₁ ≅ free 𝒜 d₂) (q : ℤ) :
    Fintype.card {i : I₁ // d₁ i = q} = Fintype.card {i : I₂ // d₂ i = q} := by
  let e : ({i : I₁ // d₁ i = q} → k) ≃ₗ[k] ({i : I₂ // d₂ i = q} → k) :=
    LinearEquiv.ofLinearMap (freeHeadHom hneg hzero Φ.hom q) (freeHeadHom hneg hzero Φ.inv q)
      (by rw [← freeHeadHom_comp, Φ.inv_hom_id, freeHeadHom_id])
      (by rw [← freeHeadHom_comp, Φ.hom_inv_id, freeHeadHom_id])
  exact card_eq_of_linearEquiv k e

/-- Over a nontrivial commutative ring `k`, isomorphic finite shifted free graded modules over a
connected nonnegatively graded `k`-algebra have the same multiset of basis shifts. -/
theorem multiset_map_eq_of_iso_free [Nontrivial k] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I₁ I₂ : Type uI} [Fintype I₁] [Fintype I₂] {d₁ : I₁ → ℤ} {d₂ : I₂ → ℤ}
    (Φ : free 𝒜 d₁ ≅ free 𝒜 d₂) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val := by
  classical
  refine Multiset.ext.mpr fun q ↦ ?_
  have hcount : ∀ {I : Type uI} [Fintype I] (d : I → ℤ),
      Multiset.count q (Multiset.map d Finset.univ.val) = Fintype.card {i : I // d i = q} := by
    intro I _ d
    rw [Multiset.count_map, ← Finset.filter_val, ← Finset.card_def, Fintype.card_subtype]
    simp_rw [eq_comm]
  rw [hcount d₁, hcount d₂]
  exact card_fiber_eq_of_iso_free hneg hzero Φ q

/-- Over a nontrivial commutative ring `k`, isomorphic finite shifted free graded modules over a
connected nonnegatively graded `k`-algebra have the same rank. -/
theorem card_eq_of_iso_free [Nontrivial k] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I₁ I₂ : Type uI} [Fintype I₁] [Fintype I₂] {d₁ : I₁ → ℤ} {d₂ : I₂ → ℤ}
    (Φ : free 𝒜 d₁ ≅ free 𝒜 d₂) : Fintype.card I₁ = Fintype.card I₂ := by
  have h := congrArg Multiset.card (multiset_map_eq_of_iso_free hneg hzero Φ)
  simpa using h

end HeadCoordinates

end TauCeti.GradedModuleCat
