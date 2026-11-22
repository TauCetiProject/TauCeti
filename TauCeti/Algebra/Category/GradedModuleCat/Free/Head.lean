/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Free.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.PieceQuotient
public import TauCeti.RingTheory.GradedAlgebra.Connected
import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Head coordinates and shift invariance for graded free modules

For a connected nonnegatively `ℤ`-graded `k`-algebra `A` (`𝒜 : ℤ → Submodule k A`,
`∀ i < 0, 𝒜 i = ⊥`, `𝒜 0` in the image of `algebraMap k A` with `FaithfulSMul k A`), the
canonical augmentation `GradedAlgebra.connectedAugmentation : A →ₐ[k] k` induces a `k`-linear
head-coordinate map `TauCeti.GradedModuleCat.freeHeadCoord` on each degree-`q` piece of a shifted
free graded module `free 𝒜 s`.

This file identifies `PieceQuotient (free 𝒜 s) q` with the shift-`q` coordinate space
`{j : I // s j = q} → k` via `TauCeti.GradedModuleCat.freePieceQuotientEquiv`, and deduces
shift-multiset and rank invariance of finite shifted free graded modules up to graded isomorphism
without requiring any PID or retract hypotheses:

* `TauCeti.GradedModuleCat.freeHeadCoord`, `TauCeti.GradedModuleCat.freeHeadCoord_eq_zero_iff`,
  `TauCeti.GradedModuleCat.freeHeadCoord_surjective`: the degree-`q` head-coordinate map on
  `free 𝒜 s`, whose kernel is `A₊ (free 𝒜 s) ∩ (free 𝒜 s) q` and which is surjective whenever the
  shift-`q` fiber is finite.
* `TauCeti.GradedModuleCat.freePieceQuotientEquiv`: `k`-linear identification of
  `PieceQuotient (free 𝒜 s) q` with `{j : I // s j = q} → k`.
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

section HeadCoordinates

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

omit [FaithfulSMul k A] in
/-- Every element of `free 𝒜 s` is the sum over its support of its coordinates times the
corresponding free generators. -/
private theorem eq_sum_support_smul_freeGenerator {I : Type uI} [DecidableEq I] [DecidableEq A]
    (s : I → ℤ) (x : free 𝒜 s) :
    x = ∑ j ∈ x.support, x j • freeGenerator (𝒜 := 𝒜) (d := s) j := by
  conv_lhs => rw [← DirectSum.sum_support_of x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [freeGenerator_eq_lof, ← LinearMap.map_smul, smul_eq_mul, mul_one, DirectSum.lof_eq_of]

/-- Reading the augmented coordinates at summands of shift `q` defines a `k`-linear head map on
the degree-`q` piece of `free 𝒜 s`. -/
def freeHeadCoord (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) :
    (free 𝒜 s).grading.piece q →ₗ[k] ({j : I // s j = q} → k) :=
  (LinearMap.pi fun j : {j : I // s j = q} ↦
    (connectedAugmentation hneg hzero).toLinearMap.comp
      (DirectSum.component k I (fun _ ↦ A) j.val)).comp
    ((free 𝒜 s).grading.piece q).subtype

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
    ({j : I // s j = q} → k) →ₗ[k] (free 𝒜 s).grading.piece q :=
  Fintype.linearCombination k fun j : {j : I // s j = q} ↦
    ⟨freeGenerator (𝒜 := 𝒜) (d := s) j.val, by
      simpa [j.property] using freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := s) j.val⟩

private theorem freeHeadCoord_freeHeadLift (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) [Fintype {j : I // s j = q}]
    (c : {j : I // s j = q} → k) :
    freeHeadCoord hneg hzero s q (freeHeadLift s q c) = c := by
  classical
  ext i
  rw [freeHeadCoord_apply]
  have hcoord : (freeHeadLift (𝒜 := 𝒜) s q c).val i.val = algebraMap k A (c i) := by
    rw [freeHeadLift, Fintype.linearCombination_apply, AddSubmonoidClass.coe_finsetSum,
      DFinsupp.finsetSum_apply]
    simp_rw [SetLike.val_smul, ← algebraMap_smul A, DirectSum.smul_apply, smul_eq_mul]
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

/-- Descending `freeHeadCoord` identifies `PieceQuotient (free 𝒜 s) q` with the shift-`q`
coordinate space `{j : I // s j = q} → k`. -/
def freePieceQuotientEquiv (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) [Finite {j : I // s j = q}] :
    PieceQuotient (free 𝒜 s) q ≃ₗ[k] ({j : I // s j = q} → k) :=
  let P := (positiveSubmodule (free 𝒜 s)).comap (pieceSubmodule (free 𝒜 s) q).subtype
  let ePiece : pieceSubmodule (free 𝒜 s) q ≃ₗ[k] (free 𝒜 s).grading.piece q :=
    { toFun := fun x ↦ ⟨x.val, x.property⟩
      invFun := fun x ↦ ⟨x.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let f : pieceSubmodule (free 𝒜 s) q →ₗ[k] ({j : I // s j = q} → k) :=
    (freeHeadCoord hneg hzero s q).comp ePiece.toLinearMap
  have hker : P.restrictScalars k = LinearMap.ker f :=
    Submodule.ext fun x ↦ (freeHeadCoord_eq_zero_iff hneg hzero s q ⟨x.val, x.property⟩).symm
  have hsurj : Function.Surjective f :=
    (freeHeadCoord_surjective hneg hzero s q).comp ePiece.surjective
  (Submodule.Quotient.restrictScalarsEquiv k P).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj))

/-- Applying `freePieceQuotientEquiv` to the class of `x` evaluates `freeHeadCoord`. -/
@[simp]
theorem freePieceQuotientEquiv_mk (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} (s : I → ℤ) (q : ℤ) [Finite {j : I // s j = q}]
    (x : pieceSubmodule (free 𝒜 s) q) :
    freePieceQuotientEquiv hneg hzero s q (Submodule.Quotient.mk x) =
      freeHeadCoord hneg hzero s q ⟨x.val, x.property⟩ := by
  simp [freePieceQuotientEquiv]
  rfl

/-- Over a nontrivial commutative ring `k`, isomorphic finite shifted free graded modules over a
connected nonnegatively graded `k`-algebra have the same number of generators in every degree `q`.
-/
theorem card_fiber_eq_of_iso_free [Nontrivial k] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I₁ I₂ : Type uI} [Fintype I₁] [Fintype I₂] {d₁ : I₁ → ℤ} {d₂ : I₂ → ℤ}
    (Φ : free 𝒜 d₁ ≅ free 𝒜 d₂) (q : ℤ) :
    Fintype.card {i : I₁ // d₁ i = q} = Fintype.card {i : I₂ // d₂ i = q} := by
  let ePQ : PieceQuotient (free 𝒜 d₁) q ≃ₗ[k] PieceQuotient (free 𝒜 d₂) q :=
    LinearEquiv.ofLinearMap
      ((pieceQuotientHom Φ.hom q).restrictScalars k)
      ((pieceQuotientHom Φ.inv q).restrictScalars k)
      (by
        rw [← LinearMap.restrictScalars_comp, ← pieceQuotientHom_comp, Φ.inv_hom_id,
          pieceQuotientHom_id, LinearMap.restrictScalars_id])
      (by
        rw [← LinearMap.restrictScalars_comp, ← pieceQuotientHom_comp, Φ.hom_inv_id,
          pieceQuotientHom_id, LinearMap.restrictScalars_id])
  let e : ({i : I₁ // d₁ i = q} → k) ≃ₗ[k] ({i : I₂ // d₂ i = q} → k) :=
    (freePieceQuotientEquiv hneg hzero d₁ q).symm.trans
      (ePQ.trans (freePieceQuotientEquiv hneg hzero d₂ q))
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
