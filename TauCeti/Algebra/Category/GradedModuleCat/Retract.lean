/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Category.GradedModuleCat.Free.Head
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded retracts and projective modules over connected algebras over a PID

Let `A` be a `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`) that is nonnegatively graded
(`∀ i < 0, 𝒜 i = ⊥`) and connected (`𝒜 0` lies in the image of `algebraMap k A`, with
`FaithfulSMul k A`).

This file provides:

* Basic stability of positive-degree multiples and vanishing homogeneous pieces along graded
  retracts (`CategoryTheory.Retract.mem_positive_smul_top_iff`,
  `CategoryTheory.Retract.piece_eq_bot`).
* Over a principal ideal domain `k`, graded freeness of every graded retract of a finite shifted
  free graded `A`-module — and hence of every finitely generated projective object in
  `GradedModuleCat 𝒜` — both categorically (`free 𝒜 (d ∘ ULift.down) ≅ M`) and as a finite
  homogeneous `A`-basis (`TauCeti.GradedModuleCat.exists_iso_free_of_retract`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`,
  `TauCeti.GradedModuleCat.exists_iso_free_of_projective`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_projective`).

## Main results

* `TauCeti.GradedModuleCat.exists_iso_free_of_retract`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`: a graded retract of a finite
  shifted free module over a connected nonnegatively graded algebra over a PID is graded free.
* `TauCeti.GradedModuleCat.exists_iso_free_of_projective`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_projective`: every finitely generated
  projective object of `GradedModuleCat 𝒜` is graded free.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Chapter II, §4, for graded projective
  modules over connected positively graded rings.
-/

public section

noncomputable section

open CategoryTheory _root_.DirectSum
open scoped DirectSum

universe uk uA v uI

namespace CategoryTheory.Retract

open TauCeti TauCeti.GradedModuleCat

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- Along a graded retract, membership in the positive-degree action is preserved and reflected. -/
theorem mem_positive_smul_top_iff {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {x : M} :
    r.i.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) ↔
      x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  refine ⟨fun hx ↦ ?_, map_mem_positive_smul_top r.i⟩
  have h := map_mem_positive_smul_top r.r hx
  have hri : r.r.hom (r.i.hom x) = x :=
    LinearMap.congr_fun (congrArg Hom.hom r.retract) x
  rwa [hri] at h

/-- Vanishing of a homogeneous piece passes to graded retracts. -/
theorem piece_eq_bot {M N : GradedModuleCat.{v} 𝒜} (r : Retract M N) {p : ℤ}
    (hp : N.grading.piece p = ⊥) : M.grading.piece p = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  have hix : r.i.hom x = 0 := by simpa [hp] using map_mem r.i hx
  have hri : r.r.hom (r.i.hom x) = x :=
    LinearMap.congr_fun (congrArg Hom.hom r.retract) x
  simpa [hix] using hri.symm

end CategoryTheory.Retract

namespace TauCeti

namespace GradedModuleCat

open _root_.TauCeti.GradedAlgebra

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
    ((r.i.hom.restrictScalars k).restrict fun _ hm ↦ map_mem r.i hm)

private theorem retractHeadMap_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) (m : M.grading.piece q) :
    retractHeadMap hneg hzero r q m = 0 ↔
      (m : M) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  dsimp [retractHeadMap]
  exact (freeHeadCoord_eq_zero_iff hneg hzero s q ⟨r.i.hom m.val, map_mem r.i m.property⟩).trans
    r.mem_positive_smul_top_iff

/-- Degree-zero scalars act on `retractHeadMap` via `connectedAugmentation`. -/
private theorem retractHeadMap_smul_eq_of_eq (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) {q p : ℤ} (hpq : p = q) (a : A) (ha : a ∈ 𝒜 (q - p))
    (g : M.grading.piece p) {v : {j : I // s j = q} → k}
    (hg : retractHeadMap hneg hzero r q ⟨g.val, hpq ▸ g.property⟩ = v) :
    retractHeadMap hneg hzero r q
      ⟨a • g.val, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.property⟩ =
      connectedAugmentation hneg hzero a • v := by
  subst hpq
  have ha0 : a ∈ 𝒜 0 := by simpa using ha
  have hsmul : a • g.val = (connectedAugmentation hneg hzero a) • g.val := by
    conv_lhs => rw [← algebraMap_connectedAugmentation_of_mem_zero hneg hzero ha0]
    exact algebraMap_smul A (connectedAugmentation hneg hzero a) g.val
  have hsub : (⟨a • g.val, by simpa using SetLike.GradedSMul.smul_mem ha g.property⟩ :
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
      ⟨a • g.val, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.property⟩ =
      0 := by
  rcases lt_or_gt_of_ne hpq with hlt | hgt
  · exact (retractHeadMap_eq_zero_iff hneg hzero r q _).mpr <|
      Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (q - p) (Submodule.mem_iSup_of_mem (by omega) ha))
        Submodule.mem_top
  · have ha0 : a = 0 := by simpa [hneg (q - p) (by omega)] using ha
    have hsub :
        (⟨a • g.val, by simpa [sub_add_cancel] using SetLike.GradedSMul.smul_mem ha g.property⟩ :
          M.grading.piece q) = 0 := Subtype.ext (by simp [ha0])
    rw [hsub, map_zero]

/-- If `liftGen q` lifts a `k`-basis of `LinearMap.range (retractHeadMap hneg hzero r q.val)` for
every shift `q` in the image of `s`, then the induced morphism `freeLift` onto `M` is surjective. -/
private theorem surjective_freeLift_of_retractHeadBasis (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s))
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s,
      Module.Basis (Fin (nq q)) k (LinearMap.range (retractHeadMap hneg hzero r q.val)))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.val (liftGen q t) = (bq q t).val)
    {n : ℕ} (ev : Fin n ≃ Σ q : Finset.univ.image s, Fin (nq q)) :
    Function.Surjective
      (freeLift (d := (fun u ↦ (ev u).fst.val) ∘ ULift.down)
        (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).fst (ev u.down).snd)).hom := by
  let d' : ULift.{uI} (Fin n) → ℤ := (fun u ↦ (ev u).fst.val) ∘ ULift.down
  let g' : ∀ u : ULift.{uI} (Fin n), M.grading.piece (d' u) :=
    fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  let Φ : free 𝒜 d' ⟶ M := freeLift g'
  obtain ⟨bM, hbM⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg s
  have hbelowM : ∀ p < bM, M.grading.piece p = ⊥ := fun p hp ↦ r.piece_eq_bot (hbM p hp)
  refine LinearMap.range_eq_top.mp
    (InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
      (LinearMap.range Φ.hom) Φ.isHomogeneous.isHomogeneous_range bM hbelowM fun q m hm ↦ ?_)
  by_cases hqS : q ∈ Finset.univ.image s
  · let q' : Finset.univ.image s := ⟨q, hqS⟩
    have hmem : retractHeadMap hneg hzero r q'.val ⟨m, hm⟩ ∈
        LinearMap.range (retractHeadMap hneg hzero r q'.val) := ⟨⟨m, hm⟩, rfl⟩
    let c := (bq q').repr ⟨retractHeadMap hneg hzero r q'.val ⟨m, hm⟩, hmem⟩
    let y : M.grading.piece q := ∑ t : Fin (nq q'), c t • liftGen q' t
    have hy_range : (y : M) ∈ LinearMap.range Φ.hom := by
      rw [AddSubmonoidClass.coe_finsetSum]
      refine Submodule.sum_mem (LinearMap.range Φ.hom) fun t _ ↦ ?_
      rw [Submodule.coe_smul_of_tower, ← algebraMap_smul A]
      refine Submodule.smul_mem (LinearMap.range Φ.hom) (algebraMap k A (c t))
        ⟨freeGenerator (ULift.up (ev.symm ⟨q', t⟩)),
          (freeLift_generator g' (ULift.up (ev.symm ⟨q', t⟩))).trans <|
            congrArg (fun idx : Σ q : Finset.univ.image s, Fin (nq q) ↦
                (liftGen idx.fst idx.snd : M))
              (ev.apply_symm_apply ⟨q', t⟩)⟩
    have hdiff_pos : m - (y : M) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
      refine (retractHeadMap_eq_zero_iff hneg hzero r q'.val (⟨m, hm⟩ - y)).mp ?_
      simp only [map_sub, y, map_sum, map_smul, hliftGen]
      have hsum := congrArg Subtype.val ((bq q').sum_repr ⟨_, hmem⟩)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hsum
      exact sub_eq_zero.mpr hsum.symm
    rw [← add_sub_cancel (y : M) m]
    exact Submodule.add_mem_sup hy_range hdiff_pos
  · have : IsEmpty {j : I // s j = q} :=
      ⟨fun j ↦ hqS (j.property ▸ Finset.mem_image_of_mem s (Finset.mem_univ j.val))⟩
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
      Module.Basis (Fin (nq q)) k (LinearMap.range (retractHeadMap hneg hzero r q.val)))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.val (liftGen q t) = (bq q t).val)
    {n : ℕ} (ev : Fin n ≃ Σ q : Finset.univ.image s, Fin (nq q)) (q : ℤ)
    {z : free 𝒜 ((fun u ↦ (ev u).fst.val) ∘ ULift.down)}
    (hz_piece : z ∈ (free 𝒜 ((fun u ↦ (ev u).fst.val) ∘ ULift.down)).grading.piece q)
    (hz_ker : (freeLift (d := (fun u ↦ (ev u).fst.val) ∘ ULift.down)
      (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).fst (ev u.down).snd)).hom z = 0) :
    freeHeadCoord hneg hzero ((fun u ↦ (ev u).fst.val) ∘ ULift.down) q ⟨z, hz_piece⟩ = 0 := by
  classical
  let S : Finset ℤ := Finset.univ.image s
  let J := ULift.{uI} (Fin n)
  let d' : J → ℤ := (fun u ↦ (ev u).fst.val) ∘ ULift.down
  let g' : ∀ u : J, M.grading.piece (d' u) := fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  let eqv : J ≃ Σ q : S, Fin (nq q) := Equiv.ulift.trans ev
  ext ⟨u, hu⟩
  let q' : S := ⟨q, hu ▸ (ev u.down).fst.property⟩
  -- Expand `Φ z = 0` as a finite sum in the degree-`q` piece of `M`.
  let term : J → M.grading.piece q := fun v ↦
    ⟨z v • (g' v).val, by
      simpa [sub_add_cancel] using
        SetLike.GradedSMul.smul_mem ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece v) (g' v).property⟩
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
      connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)) • (bq q' t).val = 0 := by
    rw [Fintype.sum_sigma] at hμ_idx
    rw [← hμ_idx, Finset.sum_eq_single q']
    · refine Finset.sum_congr rfl fun t _ ↦ ?_
      have hd_eq : d' (eqv.symm ⟨q', t⟩) = q :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.fst.val) (ev.apply_symm_apply ⟨q', t⟩)
      have hg_val : (g' (eqv.symm ⟨q', t⟩)).val = (liftGen q' t).val :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ (liftGen idx.fst idx.snd : M))
          (ev.apply_symm_apply ⟨q', t⟩)
      have hg_map : retractHeadMap hneg hzero r q
          ⟨(g' (eqv.symm ⟨q', t⟩)).val, hd_eq ▸ (g' (eqv.symm ⟨q', t⟩)).property⟩ =
          (bq q' t).val :=
        (congrArg (retractHeadMap hneg hzero r q) (Subtype.ext hg_val)).trans (hliftGen q' t)
      exact (retractHeadMap_smul_eq_of_eq hneg hzero r hd_eq (z (eqv.symm ⟨q', t⟩))
        ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece _) (g' (eqv.symm ⟨q', t⟩)) hg_map).symm
    · intro q₁ _ hq₁
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      have hd_eq₁ : d' (eqv.symm ⟨q₁, t⟩) = q₁.val :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.fst.val) (ev.apply_symm_apply ⟨q₁, t⟩)
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
    have hu' : (ev u.down).fst.val = q := hu
    rwa [hp] at hu')
  subst hq₀
  rw [freeHeadCoord_apply, Pi.zero_apply]
  dsimp only
  have hu_eq : u = eqv.symm ⟨q', t₀⟩ := eqv.injective (by rw [Equiv.apply_symm_apply]; exact hp)
  rw [hu_eq]
  exact hlin t₀

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
      Σ n : ℕ, Module.Basis (Fin n) k (LinearMap.range (retractHeadMap hneg hzero r q.val)) :=
    fun q ↦ Submodule.basisOfPid (Pi.basisFun k {j : I // s j = q.val}) _
  let nq : S → ℕ := fun q ↦ (pidPkg q).fst
  let bq : ∀ q : S, Module.Basis (Fin (nq q)) k _ := fun q ↦ (pidPkg q).snd
  let liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.val :=
    fun q t ↦ (bq q t).property.choose
  have hliftGen : ∀ (q : S) (t : Fin (nq q)),
      retractHeadMap hneg hzero r q.val (liftGen q t) = (bq q t).val :=
    fun q t ↦ (bq q t).property.choose_spec
  let n : ℕ := Fintype.card (Σ q : S, Fin (nq q))
  let ev : Fin n ≃ Σ q : S, Fin (nq q) := (Fintype.equivFin _).symm
  let d : Fin n → ℤ := fun u ↦ (ev u).fst.val
  let d' : ULift.{uI} (Fin n) → ℤ := d ∘ ULift.down
  let Φ : free 𝒜 d' ⟶ M := freeLift fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  -- Surjectivity of `Φ` splits it by projectivity of `M`.
  have hsurjΦ : Function.Surjective Φ.hom :=
    surjective_freeLift_of_retractHeadBasis hneg hzero r nq bq liftGen hliftGen ev
  have : Epi Φ := (epi_iff_surjective Φ).mpr hsurjΦ
  have : Projective M := r.projective
  let sp := (shortExact_kernelι Φ).splittingOfProjective
  let rK : Retract (kernelObj Φ) (free 𝒜 d') := ⟨kernelι Φ, sp.r, sp.f_r⟩
  -- The split kernel is bounded below with vanishing head coordinates, hence `0`.
  let _ := (kernelObj Φ).gradedSMul
  obtain ⟨bK, hbK⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg d'
  have hbelowK : ∀ p < bK, (kernelObj Φ).grading.piece p = ⊥ := fun p hp ↦
    rK.piece_eq_bot (hbK p hp)
  have hker_pos : ∀ q : ℤ, (kernelObj Φ).grading.piece q ≤
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj Φ)) := fun q z hz ↦
    rK.mem_positive_smul_top_iff.mp
      ((freeHeadCoord_eq_zero_iff hneg hzero d' q ⟨z.val, map_mem (kernelι Φ) hz⟩).mp
        (freeHeadCoord_eq_zero_of_mem_ker_freeLift hneg hzero r nq bq liftGen hliftGen ev q
          (map_mem (kernelι Φ) hz) z.property))
  have htopK : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (kernelObj Φ)) = ⊤ := by
    have hle := iSup_le hker_pos
    rw [(DirectSum.Decomposition.isInternal (kernelObj Φ).grading.piece).submodule_iSup_eq_top]
      at hle
    exact top_unique hle
  have : Subsingleton (kernelObj Φ) :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 bK hbelowK htopK
  have hinjΦ : Function.Injective Φ.hom :=
    LinearMap.ker_eq_bot.mp (Submodule.subsingleton_iff_eq_bot.mp this)
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
  refine ⟨n, Φ.homogeneousBasis.reindex Equiv.ulift, d, fun i ↦ ?_⟩
  simpa using Φ.homogeneousBasis_mem_piece (ULift.up i)

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
  exact ⟨n, d, ⟨(b.reindex Equiv.ulift.symm).isoGradedFree fun i ↦ by
    simpa using hb i.down⟩⟩

end PIDRetract

end GradedModuleCat

end TauCeti
