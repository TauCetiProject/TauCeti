/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.RingTheory.GradedAlgebra.Connected
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded retracts and projective modules over connected algebras over a PID

Let `A` be a `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`) that is nonnegatively graded
(`∀ i < 0, 𝒜 i = ⊥`) and connected (`𝒜 0` lies in the image of `algebraMap k A`, with
`FaithfulSMul k A`), with canonical augmentation `GradedAlgebra.connectedAugmentation : A →ₐ[k] k`
annihilating `A₊ = ⨆ i > 0, 𝒜 i`.

Over a principal ideal domain `k`, every graded retract of a finitely generated shifted free
graded `A`-module `free 𝒜 s` — and hence every finitely generated projective object in
`GradedModuleCat 𝒜` — is isomorphic in `GradedModuleCat 𝒜` to a finite shifted free module and
admits a finite `A`-basis of homogeneous elements:

1. Reading the augmented coordinates at summands of shift `q` defines a `k`-linear head map
   `freeHeadCoord` on each degree-`q` piece whose kernel is the degree-`q` part of `A₊ M`.
2. In each of the finitely many shifts appearing in `s`, the image of `M_q` under this head map is
   a `k`-submodule of a finite free `k`-module, so `Submodule.basisOfPid` supplies a finite
   `k`-basis that lifts homogeneously to `M_q`.
3. Bounded-below graded Nakayama (`eq_top_of_piece_le_sup_positive_smul_top`) shows that the
   induced morphism `Φ` from the finite shifted free module on these lifts is surjective.
4. Projectivity splits `Φ`, making its kernel a bounded-below retract whose head coordinates vanish
   by `k`-linear independence of the lifted bases, so graded Nakayama
   (`subsingleton_of_positive_smul_top_eq_top`) forces the kernel to vanish.

Moreover, over any nontrivial commutative base ring `k`, reducing modulo `A₊` recovers the fiber
cardinalities `{i // d i = q}` via `InvariantBasisNumber k`, so the rank and the multiset of basis
degrees of a finite shifted free graded module are uniquely determined by its graded isomorphism
class.

## Main definitions

* `TauCeti.GradedModuleCat.isoFreeOfHomogeneousBasis`,
  `TauCeti.GradedModuleCat.homogeneousBasisOfIsoFree`: equivalence between homogeneous `A`-bases of
  `M` and isomorphisms `free 𝒜 d ≅ M` in `GradedModuleCat 𝒜`.
* `TauCeti.GradedModuleCat.freeHeadCoord`: the `k`-linear head-coordinate map on
  `(free 𝒜 s).grading.piece q`.

## Main results

* `TauCeti.GradedModuleCat.exists_iso_free_of_retract`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`: a graded retract of a finite
  shifted free module over a connected nonnegatively graded algebra over a PID is graded free.
* `TauCeti.GradedModuleCat.exists_iso_free_of_projective`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_projective`: every finitely generated
  projective object of `GradedModuleCat 𝒜` is graded free.
* `TauCeti.GradedModuleCat.multiset_map_eq_of_iso_free`,
  `TauCeti.GradedModuleCat.card_eq_of_iso_free`: invariance of the multiset of shifts and rank of
  finite shifted free graded modules.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4, for graded projective
  modules over connected positively graded rings.
-/

public section

noncomputable section

open CategoryTheory _root_.DirectSum
open scoped DirectSum

namespace TauCeti

universe uk uA v uI

namespace GradedModuleCat

open _root_.TauCeti.GradedAlgebra

section General

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- An `A`-basis of `M` consisting of homogeneous elements of degrees `d` induces an isomorphism
`free 𝒜 d ≅ M` in `GradedModuleCat 𝒜`. -/
def isoFreeOfHomogeneousBasis {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) : free 𝒜 d ≅ M := by
  classical
  let x : ∀ i, M.grading.piece (d i) := fun i ↦ ⟨b i, hb i⟩
  have hcomp : ∀ v : I →₀ A,
      (freeLift x).hom (finsuppLequivDFinsupp A v) = b.repr.symm v := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => rw [map_zero, map_zero, map_zero]
    | add u w hu hw => rw [map_add, map_add, map_add, hu, hw]
    | single i a =>
      simp only [finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single,
        DirectSum.single_eq_lof A, Module.Basis.repr_symm_apply, Finsupp.linearCombination_single]
      exact freeLift_lof x i a
  have hbij : Function.Bijective (freeLift x).hom := by
    rw [← (finsuppLequivDFinsupp A).bijective.of_comp_iff]
    have hfun : ((freeLift x).hom ∘ ⇑(finsuppLequivDFinsupp A)) = ⇑b.repr.symm := funext hcomp
    rw [hfun]
    exact b.repr.symm.bijective
  have : IsIso (freeLift x) := (isIso_iff_bijective (freeLift x)).mpr hbij
  exact asIso (freeLift x)

/-- `isoFreeOfHomogeneousBasis b hb` sends the `i`th free generator to `b i`. -/
@[simp]
theorem isoFreeOfHomogeneousBasis_hom_generator {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (b : Module.Basis I A M)
    (hb : ∀ i, b i ∈ M.grading.piece (d i)) (i : I) :
    (isoFreeOfHomogeneousBasis b hb).hom.hom (freeGenerator i) = b i := by
  simp [isoFreeOfHomogeneousBasis]

/-- Conversely, an isomorphism `free 𝒜 d ≅ M` in `GradedModuleCat 𝒜` equips `M` with an `A`-basis
whose `i`th vector is the image of `freeGenerator i` in degree `d i`. -/
def homogeneousBasisOfIsoFree {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (Φ : free 𝒜 d ≅ M) : Module.Basis I A M := by
  classical
  have hbij : Function.Bijective Φ.hom.hom := (isIso_iff_bijective Φ.hom).mp inferInstance
  exact (Finsupp.basisSingleOne (ι := I) (R := A)).map
    ((finsuppLequivDFinsupp A).trans (LinearEquiv.ofBijective Φ.hom.hom hbij))

/-- The `i`th basis vector of `homogeneousBasisOfIsoFree Φ` is `Φ.hom.hom (freeGenerator i)`. -/
@[simp]
theorem homogeneousBasisOfIsoFree_apply {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (Φ : free 𝒜 d ≅ M) (i : I) :
    homogeneousBasisOfIsoFree Φ i = Φ.hom.hom (freeGenerator i) := by
  classical
  unfold homogeneousBasisOfIsoFree
  rw [Module.Basis.map_apply, Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply,
    LinearEquiv.ofBijective_apply, finsuppLequivDFinsupp_apply_apply,
    Finsupp.toDFinsupp_single, DirectSum.single_eq_lof A, ← freeGenerator_eq_lof (𝒜 := 𝒜) (d := d)]

/-- The `i`th vector of `homogeneousBasisOfIsoFree Φ` is homogeneous of degree `d i`. -/
theorem homogeneousBasisOfIsoFree_mem_piece {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (Φ : free 𝒜 d ≅ M) (i : I) :
    homogeneousBasisOfIsoFree Φ i ∈ M.grading.piece (d i) := by
  rw [homogeneousBasisOfIsoFree_apply]
  exact map_mem Φ.hom (freeGenerator_mem_free_piece i)

omit [GradedAlgebra 𝒜] in
/-- Every morphism of graded modules preserves the positive-degree action `A₊ M`. -/
theorem map_mem_positive_smul_top {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ ↦ ?_) (fun _ _ hx hy ↦ by
    simpa only [map_add] using Submodule.add_mem _ hx hy)
  rw [map_smul]
  exact Submodule.smul_mem_smul ha Submodule.mem_top

omit [GradedAlgebra 𝒜] in
/-- Along a graded retract, membership in the positive-degree action is preserved and reflected. -/
theorem retract_mem_positive_smul_top_iff {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {x : M} :
    r.i.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) ↔
      x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  refine ⟨fun hx ↦ ?_, map_mem_positive_smul_top r.i⟩
  have h := map_mem_positive_smul_top r.r hx
  have hri : r.r.hom (r.i.hom x) = x :=
    LinearMap.congr_fun (congrArg Hom.hom r.retract) x
  rwa [hri] at h

omit [GradedAlgebra 𝒜] in
/-- Vanishing of a homogeneous piece passes to graded retracts. -/
theorem piece_eq_bot_of_retract {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {p : ℤ}
    (hp : N.grading.piece p = ⊥) : M.grading.piece p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  have hix : r.i.hom x = 0 := by simpa [hp] using map_mem r.i hx
  have hri : r.r.hom (r.i.hom x) = x :=
    LinearMap.congr_fun (congrArg Hom.hom r.retract) x
  simpa [hix] using hri.symm

/-- Over a nonnegatively graded algebra, a finitely generated shifted free graded module is
bounded below. -/
theorem exists_piece_eq_bot_of_lt_free {I : Type uI} [Finite I] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (s : I → ℤ) : ∃ b : ℤ, ∀ p < b, (free 𝒜 s).grading.piece p = ⊥ := by
  cases nonempty_fintype I
  obtain ⟨b, hb⟩ := (Finset.univ.image s).bddBelow
  refine ⟨b, fun p hp ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  ext j
  have hsb : b ≤ s j := hb (Finset.mem_image_of_mem s (Finset.mem_univ j))
  have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
  rw [hneg (p - s j) (by omega), Submodule.mem_bot] at hxj
  simpa using hxj

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
  toFun x j := connectedAugmentation hneg hzero (x.1 j.1)
  map_add' x y := funext fun j ↦ by
    rw [Submodule.coe_add, DirectSum.add_apply, map_add, Pi.add_apply]
  map_smul' c x := funext fun j ↦ by
    rw [Submodule.coe_smul_of_tower, ← algebraMap_smul A c x.1, DirectSum.smul_apply, smul_eq_mul,
      map_mul, connectedAugmentation_algebraMap, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

/-- `freeHeadCoord` evaluates `connectedAugmentation` on each shift-`q` coordinate. -/
@[simp]
theorem freeHeadCoord_apply (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) (x : (free 𝒜 s).grading.piece q)
    (j : {j : I // s j = q}) :
    freeHeadCoord hneg hzero s q x j = connectedAugmentation hneg hzero (x.1 j.1) :=
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
    rw [eq_sum_support_smul_freeGenerator s x.1]
    refine Submodule.sum_mem _ fun j _ ↦ ?_
    have hxj : x.1 j ∈ 𝒜 (q - s j) := (mem_free_piece_iff 𝒜 s q x.1).mp x.2 j
    rcases lt_trichotomy (s j) q with hlt | hsq | hgt
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (q - s j) (Submodule.mem_iSup_of_mem (by omega) hxj))
        Submodule.mem_top
    · have hxj0 : x.1 j ∈ 𝒜 0 := by simpa [hsq] using hxj
      have haug : connectedAugmentation hneg hzero (x.1 j) = 0 := congrFun hx0 ⟨j, hsq⟩
      have hzero_coord : x.1 j = 0 := by
        rw [← algebraMap_connectedAugmentation_of_mem_zero hneg hzero hxj0, haug, map_zero]
      simp [hzero_coord]
    · have hzero_coord : x.1 j = 0 := by simpa [hneg (q - s j) (by omega)] using hxj
      simp [hzero_coord]
  · intro hx
    ext j
    exact (connectedAugmentation_eq_zero_iff hneg hzero).mpr
      (coord_mem_positive_of_mem_positive_smul_top hneg s hx j.1)

omit [FaithfulSMul k A] in
/-- Canonical `k`-linear section of `freeHeadCoord` on a finite index type `I`. -/
private def freeHeadLift {I : Type uI} [Fintype I] (s : I → ℤ) (q : ℤ) :
    ({j : I // s j = q} → k) →ₗ[k] (free 𝒜 s).grading.piece q where
  toFun c :=
    ⟨∑ j : {j : I // s j = q}, c j • freeGenerator (𝒜 := 𝒜) (d := s) j.1, by
      refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ (c j) ?_
      simpa [j.2] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) j.1⟩
  map_add' c₁ c₂ := Subtype.ext (by simp [add_smul, Finset.sum_add_distrib])
  map_smul' r c := Subtype.ext (by simp [Finset.smul_sum, mul_smul])

private theorem freeHeadCoord_freeHeadLift (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] (s : I → ℤ) (q : ℤ) (c : {j : I // s j = q} → k) :
    freeHeadCoord hneg hzero s q (freeHeadLift s q c) = c := by
  classical
  ext i
  rw [freeHeadCoord_apply]
  have hcoord : (freeHeadLift (𝒜 := 𝒜) s q c).1 i.1 = algebraMap k A (c i) := by
    dsimp only [freeHeadLift, LinearMap.coe_mk, AddHom.coe_mk]
    rw [DFinsupp.finsetSum_apply]
    simp_rw [← algebraMap_smul A, DirectSum.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp [freeGenerator_apply]
    · intro j _ hji
      have hij : j.1 ≠ i.1 := fun h ↦ hji (Subtype.ext h)
      simp [freeGenerator_apply, hij]
    · exact fun hi ↦ absurd (Finset.mem_univ i) hi
  simp [hcoord]

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
      fun c ↦ map_mem f (freeHeadLift s q c).2)

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
    ⟨f.hom (freeHeadLift d₁ q c).1, map_mem f (freeHeadLift d₁ q c).2⟩
  set y' : (free 𝒜 d₂).grading.piece q :=
    freeHeadLift d₂ q (freeHeadCoord hneg hzero d₂ q y)
  have hdiff : ((y - y' : (free 𝒜 d₂).grading.piece q) : free 𝒜 d₂) ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d₂)) := by
    rw [← freeHeadCoord_eq_zero_iff hneg hzero d₂ q (y - y'), map_sub,
      freeHeadCoord_freeHeadLift, sub_self]
  have hgdiff : freeHeadCoord hneg hzero d₃ q
      ⟨g.hom (y - y').1, map_mem g (y - y').2⟩ = 0 :=
    (freeHeadCoord_eq_zero_iff hneg hzero d₃ q _).mpr (map_mem_positive_smul_top g hdiff)
  have hg_sub : (⟨g.hom (y - y').1, map_mem g (y - y').2⟩ : (free 𝒜 d₃).grading.piece q) =
      ⟨g.hom y.1, map_mem g y.2⟩ - ⟨g.hom y'.1, map_mem g y'.2⟩ :=
    Subtype.ext (map_sub g.hom y.1 y'.1)
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

section RetractHead

variable {k : Type uk} [CommRing k]
  {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The degree-`q` head coordinate map induced on a retract `r : Retract M (free 𝒜 s)`. -/
private def retractHeadMap (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) :
    M.grading.piece q →ₗ[k] ({j : I // s j = q} → k) :=
  (freeHeadCoord hneg hzero s q).comp
    (LinearMap.codRestrict ((free 𝒜 s).grading.piece q)
      ((r.i.hom.restrictScalars k).comp (M.grading.piece q).subtype)
      fun m ↦ map_mem r.i m.2)

private theorem retractHeadMap_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) (m : M.grading.piece q) :
    retractHeadMap hneg hzero r q m = 0 ↔
      (m : M) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  dsimp [retractHeadMap]
  exact (freeHeadCoord_eq_zero_iff hneg hzero s q ⟨r.i.hom m.1, map_mem r.i m.2⟩).trans
    (retract_mem_positive_smul_top_iff r)

/-- Degree-zero scalars act on `retractHeadMap` via `connectedAugmentation`. -/
private theorem retractHeadMap_smul_eq_of_eq (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) {q p : ℤ} (hpq : p = q) (a : A) (ha : a ∈ 𝒜 (q - p))
    (g : M.grading.piece p) {v : {j : I // s j = q} → k}
    (hg : retractHeadMap hneg hzero r q ⟨g.1, hpq ▸ g.2⟩ = v) :
    retractHeadMap hneg hzero r q
      ⟨a • g.1, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.2⟩ =
      connectedAugmentation hneg hzero a • v := by
  subst hpq
  have ha0 : a ∈ 𝒜 0 := by simpa using ha
  have hsmul : a • g.1 = (connectedAugmentation hneg hzero a) • g.1 := by
    conv_lhs => rw [← algebraMap_connectedAugmentation_of_mem_zero hneg hzero ha0]
    exact algebraMap_smul A (connectedAugmentation hneg hzero a) g.1
  have hsub : (⟨a • g.1, by simpa using SetLike.GradedSMul.smul_mem ha g.2⟩ :
      M.grading.piece p) = (connectedAugmentation hneg hzero a) • g :=
    Subtype.ext hsmul
  rw [hsub, map_smul, ← hg]

/-- Off-degree scalars act by zero on `retractHeadMap`: positive degrees land in `A₊ M`, while
negative-degree scalars vanish. -/
private theorem retractHeadMap_smul_eq_zero_of_ne (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) {q p : ℤ} (hpq : p ≠ q) (a : A) (ha : a ∈ 𝒜 (q - p))
    (g : M.grading.piece p) :
    retractHeadMap hneg hzero r q
      ⟨a • g.1, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.2⟩ = 0 := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact (retractHeadMap_eq_zero_iff hneg hzero r q _).mpr <|
      Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (q - p) (Submodule.mem_iSup_of_mem (by omega) ha))
        Submodule.mem_top
  · have ha0 : a = 0 := by simpa [hneg (q - p) (by omega)] using ha
    have hsub : (⟨a • g.1, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.2⟩ :
        M.grading.piece q) = 0 := Subtype.ext (by simp [ha0])
    rw [hsub, map_zero]

/-- If `liftGen q` lifts a `k`-basis of `LinearMap.range (retractHeadMap hneg hzero r q.1)` for
every shift `q` in the image of `s`, then the induced morphism `freeLift` onto `M` is surjective. -/
private theorem surjective_freeLift_of_retractHeadBasis (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s))
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s,
      Module.Basis (Fin (nq q)) k (LinearMap.range (retractHeadMap hneg hzero r q.1)))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.1)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.1 (liftGen q t) = (bq q t).1)
    {n : ℕ} (ev : Fin n ≃ Σ q : Finset.univ.image s, Fin (nq q)) :
    Function.Surjective
      (freeLift (d := (fun u ↦ (ev u).1.1) ∘ ULift.down)
        (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).1 (ev u.down).2)).hom := by
  let d' : ULift.{uI} (Fin n) → ℤ := (fun u ↦ (ev u).1.1) ∘ ULift.down
  let g' : ∀ u : ULift.{uI} (Fin n), M.grading.piece (d' u) :=
    fun u ↦ liftGen (ev u.down).1 (ev u.down).2
  let Φ : free 𝒜 d' ⟶ M := freeLift g'
  obtain ⟨bM, hbM⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg s
  have hbelowM : ∀ p < bM, M.grading.piece p = ⊥ := fun p hp ↦ piece_eq_bot_of_retract r (hbM p hp)
  refine LinearMap.range_eq_top.mp
    (InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (LinearMap.range Φ.hom) Φ.isHomogeneous.isHomogeneous_range bM hbelowM fun q m hm ↦ ?_)
  by_cases hqS : q ∈ Finset.univ.image s
  · let q' : Finset.univ.image s := ⟨q, hqS⟩
    have hmem : retractHeadMap hneg hzero r q'.1 ⟨m, hm⟩ ∈
        LinearMap.range (retractHeadMap hneg hzero r q'.1) := ⟨⟨m, hm⟩, rfl⟩
    let c := (bq q').repr ⟨retractHeadMap hneg hzero r q'.1 ⟨m, hm⟩, hmem⟩
    let y : M.grading.piece q := ∑ t : Fin (nq q'), c t • liftGen q' t
    have hy_range : (y : M) ∈ LinearMap.range Φ.hom := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Submodule.sum_mem (LinearMap.range Φ.hom) fun t _ ↦ ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul A]
      refine Submodule.smul_mem (LinearMap.range Φ.hom) (algebraMap k A (c t))
        ⟨freeGenerator (ULift.up (ev.symm ⟨q', t⟩)),
          (freeLift_generator g' (ULift.up (ev.symm ⟨q', t⟩))).trans <|
            congrArg (fun idx : Σ q : Finset.univ.image s, Fin (nq q) ↦ (liftGen idx.1 idx.2 : M))
              (ev.apply_symm_apply ⟨q', t⟩)⟩
    have hdiff_pos : m - (y : M) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
      refine (retractHeadMap_eq_zero_iff hneg hzero r q'.1 (⟨m, hm⟩ - y)).mp ?_
      simp only [map_sub, y, map_sum, map_smul, hliftGen]
      have hsum := congrArg Subtype.val ((bq q').sum_repr ⟨_, hmem⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hsum
      exact sub_eq_zero.mpr hsum.symm
    rw [← add_sub_cancel (y : M) m]
    exact Submodule.add_mem_sup hy_range hdiff_pos
  · have : IsEmpty {j : I // s j = q} :=
      ⟨fun j ↦ hqS (j.2 ▸ Finset.mem_image_of_mem s (Finset.mem_univ j.1))⟩
    exact Submodule.mem_sup_right
      ((retractHeadMap_eq_zero_iff hneg hzero r q ⟨m, hm⟩).mp (Subsingleton.elim _ _))

/-- Evaluating `retractHeadMap q` on `Φ.hom z = 0` isolates the fiber of basis lifts of degree `q`
and shows that every shift-`q` head coordinate of `z` vanishes. -/
private theorem freeHeadCoord_eq_zero_of_mem_ker_freeLift (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s))
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s,
      Module.Basis (Fin (nq q)) k (LinearMap.range (retractHeadMap hneg hzero r q.1)))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.1)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.1 (liftGen q t) = (bq q t).1)
    {n : ℕ} (ev : Fin n ≃ Σ q : Finset.univ.image s, Fin (nq q)) (q : ℤ)
    {z : free 𝒜 ((fun u ↦ (ev u).1.1) ∘ ULift.down)}
    (hz_piece : z ∈ (free 𝒜 ((fun u ↦ (ev u).1.1) ∘ ULift.down)).grading.piece q)
    (hz_ker : (freeLift (d := (fun u ↦ (ev u).1.1) ∘ ULift.down)
      (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).1 (ev u.down).2)).hom z = 0) :
    freeHeadCoord hneg hzero ((fun u ↦ (ev u).1.1) ∘ ULift.down) q ⟨z, hz_piece⟩ = 0 := by
  classical
  let S : Finset ℤ := Finset.univ.image s
  let J := ULift.{uI} (Fin n)
  let d' : J → ℤ := (fun u ↦ (ev u).1.1) ∘ ULift.down
  let g' : ∀ u : J, M.grading.piece (d' u) := fun u ↦ liftGen (ev u.down).1 (ev u.down).2
  let eqv : J ≃ Σ q : S, Fin (nq q) := Equiv.ulift.trans ev
  ext ⟨u, hu⟩
  let q' : S := ⟨q, hu ▸ (ev u.down).1.2⟩
  -- Expand `Φ z = 0` as a finite sum in the degree-`q` piece of `M`.
  let term : J → M.grading.piece q := fun v ↦
    ⟨z v • (g' v).1, by
      simpa [sub_add_cancel] using
        SetLike.GradedSMul.smul_mem ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece v) (g' v).2⟩
  have hsum_term : ∑ v : J, term v = 0 := Subtype.ext <| by
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hz_ker]
    conv_rhs => rw [← DirectSum.sum_univ_of z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← DirectSum.lof_eq_of A J (fun _ ↦ A), freeLift_lof]
  -- Apply `retractHeadMap q`: only the degree-`q` fiber `q'` survives.
  have hμ_idx :
      ∑ idx : Σ q : S, Fin (nq q), retractHeadMap hneg hzero r q (term (eqv.symm idx)) = 0 := by
    rw [eqv.symm.sum_comp (fun v ↦ retractHeadMap hneg hzero r q (term v)),
      ← map_sum, hsum_term, map_zero]
  have hμ_fiber : ∑ t : Fin (nq q'),
      connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)) • (bq q' t).1 = 0 := by
    rw [Fintype.sum_sigma] at hμ_idx
    rw [← hμ_idx, Finset.sum_eq_single q']
    · refine Finset.sum_congr rfl fun t _ ↦ ?_
      have hd_eq : d' (eqv.symm ⟨q', t⟩) = q :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.1.1) (ev.apply_symm_apply ⟨q', t⟩)
      have hg_val : (g' (eqv.symm ⟨q', t⟩)).1 = (liftGen q' t).1 :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ (liftGen idx.1 idx.2 : M))
          (ev.apply_symm_apply ⟨q', t⟩)
      have hg_map : retractHeadMap hneg hzero r q
          ⟨(g' (eqv.symm ⟨q', t⟩)).1, hd_eq ▸ (g' (eqv.symm ⟨q', t⟩)).2⟩ = (bq q' t).1 :=
        (congrArg (retractHeadMap hneg hzero r q) (Subtype.ext hg_val)).trans (hliftGen q' t)
      exact (retractHeadMap_smul_eq_of_eq hneg hzero r hd_eq (z (eqv.symm ⟨q', t⟩))
        ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece _) (g' (eqv.symm ⟨q', t⟩)) hg_map).symm
    · intro q₁ _ hq₁
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      have hd_eq₁ : d' (eqv.symm ⟨q₁, t⟩) = q₁.1 :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.1.1) (ev.apply_symm_apply ⟨q₁, t⟩)
      exact retractHeadMap_smul_eq_zero_of_ne hneg hzero r
        (fun h ↦ hq₁ (Subtype.ext (hd_eq₁.symm.trans h))) (z (eqv.symm ⟨q₁, t⟩))
        ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece _) (g' (eqv.symm ⟨q₁, t⟩))
    · exact fun h ↦ absurd (Finset.mem_univ q') h
  -- Conclude by `k`-linear independence of the lifted head basis `bq q'`.
  have hlin := Fintype.linearIndependent_iff.mp (bq q').linearIndependent
    (fun t ↦ connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)))
    (Subtype.ext (by simpa [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using hμ_fiber))
  rcases hp : ev u.down with ⟨q₀, t₀⟩
  have hq₀ : q₀ = q' := Subtype.ext (by
    have hu' : (ev u.down).1.1 = q := hu
    rwa [hp] at hu')
  subst hq₀
  rw [freeHeadCoord_apply, Pi.zero_apply]
  dsimp only
  have hu_eq : u = eqv.symm ⟨q', t₀⟩ := eqv.injective (by rw [Equiv.apply_symm_apply]; exact hp)
  rw [hu_eq]
  exact hlin t₀

omit [FaithfulSMul k A] [GradedAlgebra 𝒜] in
/-- A split epimorphism in `GradedModuleCat 𝒜` makes its kernel a graded retract of the domain. -/
private def retractKernelOfSection {M N : GradedModuleCat.{v} 𝒜} (Φ : N ⟶ M) (ψ : M ⟶ N)
    (hψΦ : ψ ≫ Φ = 𝟙 M) : Retract (kernelObj Φ) N where
  i := kernelι Φ
  r := ofHom (LinearMap.codRestrict (LinearMap.ker Φ.hom) (𝟙 N - Φ ≫ ψ).hom fun x ↦ by
      have h := LinearMap.congr_fun (congrArg Hom.hom hψΦ) (Φ.hom x)
      simpa using sub_eq_zero.mpr h.symm)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hx ↦ by
      simpa [kernelObj] using map_mem (𝟙 N - Φ ≫ ψ) hx)
  retract := hom_ext <| LinearMap.ext fun z ↦ Subtype.ext <| by
    dsimp [kernelι]
    simp

end RetractHead

section PIDRetract

variable {k : Type uk} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
  {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- **Graded freeness of retracts.** Over a connected nonnegatively graded algebra `A` over a
principal ideal domain `k`, every graded retract `M` of a finite shifted free module `free 𝒜 s`
is isomorphic in `GradedModuleCat 𝒜` to a finite shifted free module. -/
theorem exists_iso_free_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 (d ∘ ULift.down) ≅ M) := by
  classical
  cases nonempty_fintype I
  -- Lift `k`-bases of the head-coordinate images in each shift of `s`.
  let S : Finset ℤ := Finset.univ.image s
  let pidPkg : ∀ q : S,
      Σ n : ℕ, Module.Basis (Fin n) k (LinearMap.range (retractHeadMap hneg hzero r q.1)) :=
    fun q ↦ Submodule.basisOfPid (Pi.basisFun k {j : I // s j = q.1}) _
  let nq : S → ℕ := fun q ↦ (pidPkg q).1
  let bq : ∀ q : S, Module.Basis (Fin (nq q)) k _ := fun q ↦ (pidPkg q).2
  let liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.1 := fun q t ↦ (bq q t).2.choose
  have hliftGen : ∀ (q : S) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.1 (liftGen q t) = (bq q t).1 :=
    fun q t ↦ (bq q t).2.choose_spec
  let n : ℕ := Fintype.card (Σ q : S, Fin (nq q))
  let ev : Fin n ≃ Σ q : S, Fin (nq q) := (Fintype.equivFin _).symm
  let d : Fin n → ℤ := fun u ↦ (ev u).1.1
  let d' : ULift.{uI} (Fin n) → ℤ := d ∘ ULift.down
  let Φ : free 𝒜 d' ⟶ M := freeLift fun u ↦ liftGen (ev u.down).1 (ev u.down).2
  -- Surjectivity of `Φ` splits it by projectivity of `M`.
  have hsurjΦ : Function.Surjective Φ.hom :=
    surjective_freeLift_of_retractHeadBasis hneg hzero r nq bq liftGen hliftGen ev
  have : Epi Φ := (epi_iff_surjective Φ).mpr hsurjΦ
  have : Projective M := r.projective
  let rK := retractKernelOfSection Φ (Projective.factorThru (𝟙 M) Φ)
    (Projective.factorThru_comp (𝟙 M) Φ)
  -- The split kernel is bounded below with vanishing head coordinates, hence `0`.
  let _ := (kernelObj Φ).gradedSMul
  obtain ⟨bK, hbK⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg d'
  have hbelowK : ∀ p < bK, (kernelObj Φ).grading.piece p = ⊥ := fun p hp ↦
    piece_eq_bot_of_retract rK (hbK p hp)
  have hker_pos : ∀ q : ℤ, (kernelObj Φ).grading.piece q ≤
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj Φ)) := fun q z hz ↦
    (retract_mem_positive_smul_top_iff rK).mp
      ((freeHeadCoord_eq_zero_iff hneg hzero d' q ⟨z.1, map_mem (kernelι Φ) hz⟩).mp
        (freeHeadCoord_eq_zero_of_mem_ker_freeLift hneg hzero r nq bq liftGen hliftGen ev q
          (map_mem (kernelι Φ) hz) z.2))
  have htopK : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj Φ)) = ⊤ :=
    top_unique fun z _ ↦ by
      rw [← sum_support_decompose (kernelObj Φ).grading.piece z]
      exact Submodule.sum_mem _ fun q _ ↦
        hker_pos q (decompose (kernelObj Φ).grading.piece z q).2
  have : Subsingleton (kernelObj Φ) :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 bK hbelowK htopK
  have hinjΦ : Function.Injective Φ.hom :=
    LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr fun x hx ↦
      congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : kernelObj Φ) 0))
  have : IsIso Φ := (isIso_iff_bijective Φ).mpr ⟨hinjΦ, hsurjΦ⟩
  exact ⟨n, d, ⟨asIso Φ⟩⟩

/-- **Homogeneous basis of a graded retract.** Over a connected nonnegatively graded algebra `A`
over a PID `k`, every graded retract `M` of a finite shifted free module `free 𝒜 s` admits a
finite `A`-basis of homogeneous elements. -/
theorem exists_homogeneous_basis_of_retract (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A M) (d : Fin n → ℤ),
      ∀ i, b i ∈ M.grading.piece (d i) := by
  obtain ⟨n, d, ⟨Φ⟩⟩ := exists_iso_free_of_retract hneg hzero r
  refine ⟨n, (homogeneousBasisOfIsoFree Φ).reindex Equiv.ulift, d, fun i ↦ ?_⟩
  simpa using homogeneousBasisOfIsoFree_mem_piece Φ (ULift.up i)

/-- Every finitely generated projective object of `GradedModuleCat 𝒜` over a connected
nonnegatively graded algebra over a PID admits a finite `A`-basis of homogeneous elements. -/
theorem exists_homogeneous_basis_of_projective (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    (M : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A M] [Projective M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A M) (d : Fin n → ℤ),
      ∀ i, b i ∈ M.grading.piece (d i) := by
  obtain ⟨I, hI, s, f, hf⟩ := exists_finite_free_surjection M
  let _ : Finite I := hI
  have : Epi f := (epi_iff_surjective f).mpr hf
  let r : Retract M (free 𝒜 s) :=
    { i := Projective.factorThru (𝟙 M) f
      r := f
      retract := Projective.factorThru_comp (𝟙 M) f }
  exact exists_homogeneous_basis_of_retract (I := I) (M := M) hneg hzero r

/-- **Finitely generated graded projective modules are graded free.** Over a connected
nonnegatively graded algebra `A` over a PID `k`, every finitely generated projective object of
`GradedModuleCat 𝒜` is isomorphic to a finite shifted free module. -/
theorem exists_iso_free_of_projective (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    (M : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A M] [Projective M] :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 (d ∘ ULift.down) ≅ M) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_of_projective hneg hzero M
  exact ⟨n, d, ⟨isoFreeOfHomogeneousBasis (b.reindex Equiv.ulift.symm) fun i ↦ by
    simpa using hb i.down⟩⟩

end PIDRetract

end GradedModuleCat

end TauCeti
