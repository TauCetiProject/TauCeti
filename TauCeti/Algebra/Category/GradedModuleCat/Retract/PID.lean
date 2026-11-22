/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import TauCeti.Algebra.Category.GradedModuleCat.Free.Head
public import TauCeti.Algebra.Category.GradedModuleCat.Retract.Basic
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded retracts and projective modules over connected algebras over a PID

Let `A` be a `ℤ`-graded `k`-algebra (`𝒜 : ℤ → Submodule k A`) over a principal ideal domain `k`
that is nonnegatively graded (`∀ i < 0, 𝒜 i = ⊥`) and connected (`𝒜 0` lies in the image of
`algebraMap k A`, with `FaithfulSMul k A`).

This file proves that every graded retract of a finite shifted free graded `A`-module — and hence
every finitely generated projective object in `GradedModuleCat 𝒜` — is graded free:

* `TauCeti.GradedModuleCat.exists_iso_free_of_retract`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`: a graded retract of a finite
  shifted free module admits a finite homogeneous `A`-basis and is isomorphic in
  `GradedModuleCat 𝒜` to a finite shifted free module.
* `TauCeti.GradedModuleCat.exists_iso_free_of_projective`,
  `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_projective`: every finitely generated
  projective object of `GradedModuleCat 𝒜` admits a finite homogeneous `A`-basis and is
  isomorphic in `GradedModuleCat 𝒜` to a finite shifted free module.

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

namespace TauCeti.GradedModuleCat

open _root_.TauCeti.GradedAlgebra

section RetractHead

variable {k : Type uk} [CommRing k]
  {A : Type uA} [Ring A] [Algebra k A] [FaithfulSMul k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- The `k`-linear inclusion `PieceQuotient M q →ₗ[k] ({j : I // s j = q} → k)` induced by a
graded retract `r : Retract M (free 𝒜 s)`. -/
private def retractPieceQuotientHom (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) :
    PieceQuotient M q →ₗ[k] ({j : I // s j = q} → k) :=
  (freePieceQuotientEquiv hneg hzero s q).toLinearMap.comp
    ((pieceQuotientHom r.i q).restrictScalars k)

private theorem injective_retractPieceQuotientHom (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) :
    Function.Injective (retractPieceQuotientHom hneg hzero r q) := by
  let ρ : ({j : I // s j = q} → k) →ₗ[k] PieceQuotient M q :=
    ((pieceQuotientHom r.r q).restrictScalars k).comp
      (freePieceQuotientEquiv hneg hzero s q).symm.toLinearMap
  refine Function.LeftInverse.injective (g := ρ) fun x ↦ ?_
  dsimp [ρ, retractPieceQuotientHom]
  rw [LinearEquiv.symm_apply_apply]
  have hcomp : ((pieceQuotientHom r.r q).restrictScalars k).comp
      ((pieceQuotientHom r.i q).restrictScalars k) = LinearMap.id := by
    rw [← LinearMap.restrictScalars_comp, ← pieceQuotientHom_comp, r.retract,
      pieceQuotientHom_id, LinearMap.restrictScalars_id]
  exact LinearMap.congr_fun hcomp x

/-- If `liftGen q` lifts a `k`-basis `bq q` of `PieceQuotient M q.val` for every shift `q` in the
image of `s`, then the induced morphism `freeLift` onto `M` is surjective. -/
private theorem surjective_freeLift_of_retractHeadBasis (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s))
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s, Module.Basis (Fin (nq q)) k (PieceQuotient M q.val))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, (liftGen q t).property⟩ :
        PieceQuotient M q.val) = bq q t)
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
    let xm : pieceSubmodule M q' := ⟨m, mem_pieceSubmodule.mpr hm⟩
    let c := (bq q').repr (Submodule.Quotient.mk xm)
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
      let ym : pieceSubmodule M q' := ⟨y.val, mem_pieceSubmodule.mpr y.property⟩
      have hmk : (Submodule.Quotient.mk (xm - ym) : PieceQuotient M q') = 0 := by
        rw [Submodule.Quotient.mk_sub, sub_eq_zero]
        have hsum : (Submodule.Quotient.mk ym : PieceQuotient M q') = ∑ t, c t • bq q' t := by
          have hym : ym = ∑ t : Fin (nq q'),
              c t • (⟨(liftGen q' t).val, (liftGen q' t).property⟩ : pieceSubmodule M q') := by
            ext
            simp [ym, y, AddSubmonoidClass.coe_finsetSum]
          rw [hym]
          change ((positiveSubmodule M).comap (pieceSubmodule M q'.val).subtype).mkQ _ = _
          rw [map_sum]
          refine Finset.sum_congr rfl fun t _ ↦ ?_
          change Submodule.Quotient.mk (c t • _) = c t • bq q' t
          rw [← hliftGen]
          rfl
        rw [hsum]
        exact ((bq q').sum_repr (Submodule.Quotient.mk xm)).symm
      exact Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hmk)
    rw [← add_sub_cancel (y : M) m]
    exact Submodule.add_mem_sup hy_range hdiff_pos
  · have : IsEmpty {j : I // s j = q} :=
      ⟨fun j ↦ hqS (j.property ▸ Finset.mem_image_of_mem s (Finset.mem_univ j.val))⟩
    have : Subsingleton (PieceQuotient M q) :=
      (injective_retractPieceQuotientHom hneg hzero r q).subsingleton
    have hmk0 : (Submodule.Quotient.mk
        (⟨m, mem_pieceSubmodule.mpr hm⟩ : pieceSubmodule M q) : PieceQuotient M q) = 0 :=
      Subsingleton.elim _ _
    exact Submodule.mem_sup_right <| Submodule.mem_comap.mp <|
      (Submodule.Quotient.mk_eq_zero
        ((positiveSubmodule M).comap (pieceSubmodule M q).subtype)).mp hmk0

/-- Evaluating in `PieceQuotient M q` on `Φ.hom z = 0` isolates the fiber of basis lifts of
degree `q` and shows that every shift-`q` head coordinate of `z` vanishes. -/
private theorem freeHeadCoord_eq_zero_of_mem_ker_freeLift (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s, Module.Basis (Fin (nq q)) k (PieceQuotient M q.val))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, (liftGen q t).property⟩ :
        PieceQuotient M q.val) = bq q t)
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
  -- Expand `Φ z = 0` as a finite sum in `pieceSubmodule M q`.
  let term : J → pieceSubmodule M q := fun v ↦
    ⟨z v • (g' v).val, mem_pieceSubmodule.mpr <| by
      simpa [sub_add_cancel] using
        SetLike.GradedSMul.smul_mem ((mem_free_piece_iff 𝒜 d' q z).mp hz_piece v) (g' v).property⟩
  have hsum_term : ∑ v : J, term v = 0 := Subtype.ext <| by
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero, ← hz_ker]
    conv_rhs => rw [← DirectSum.sum_univ_of z]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [← DirectSum.lof_eq_of A J (fun _ ↦ A), freeLift_lof]
  -- Project to `PieceQuotient M q`: only the degree-`q` fiber `q'` survives.
  have hq_idx : ∑ idx : Σ q : S, Fin (nq q),
      (Submodule.Quotient.mk (term (eqv.symm idx)) : PieceQuotient M q) = 0 := by
    rw [eqv.symm.sum_comp (fun v ↦ (Submodule.Quotient.mk (term v) : PieceQuotient M q))]
    change ∑ v : J, ((positiveSubmodule M).comap (pieceSubmodule M q).subtype).mkQ (term v) = 0
    rw [← map_sum, hsum_term, map_zero]
  have hq_fiber : ∑ t : Fin (nq q'),
      connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)) • bq q' t = 0 := by
    rw [Fintype.sum_sigma] at hq_idx
    rw [← hq_idx, Finset.sum_eq_single q']
    · refine Finset.sum_congr rfl fun t _ ↦ ?_
      have hd_eq : d' (eqv.symm ⟨q', t⟩) = q :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.fst.val) (ev.apply_symm_apply ⟨q', t⟩)
      have hg_val : (g' (eqv.symm ⟨q', t⟩)).val = (liftGen q' t).val :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ (liftGen idx.fst idx.snd : M))
          (ev.apply_symm_apply ⟨q', t⟩)
      have hz0 : z (eqv.symm ⟨q', t⟩) ∈ 𝒜 0 := by
        simpa [hd_eq] using (mem_free_piece_iff 𝒜 d' q z).mp hz_piece (eqv.symm ⟨q', t⟩)
      have hterm_eq : term (eqv.symm ⟨q', t⟩) =
          connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)) •
            (⟨(liftGen q' t).val, (liftGen q' t).property⟩ : pieceSubmodule M q) := by
        ext
        change z (eqv.symm ⟨q', t⟩) • (g' (eqv.symm ⟨q', t⟩)).val =
          connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩)) • (liftGen q' t).val
        rw [hg_val]
        conv_lhs => rw [← algebraMap_connectedAugmentation_of_mem_zero hneg hzero hz0]
        exact algebraMap_smul A _ _
      rw [hterm_eq, ← hliftGen]
      rfl
    · intro q₁ _ hq₁
      refine Finset.sum_eq_zero fun t _ ↦ ?_
      let v := eqv.symm ⟨q₁, t⟩
      have hd_eq₁ : d' v = q₁.val :=
        congrArg (fun idx : Σ q : S, Fin (nq q) ↦ idx.fst.val) (ev.apply_symm_apply ⟨q₁, t⟩)
      have hne : q₁.val ≠ q := fun h ↦ hq₁ (Subtype.ext h)
      have hz_mem : z v ∈ 𝒜 (q - q₁.val) := by
        simpa [hd_eq₁] using (mem_free_piece_iff 𝒜 d' q z).mp hz_piece v
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · refine (Submodule.Quotient.mk_eq_zero
          ((positiveSubmodule M).comap (pieceSubmodule M q).subtype)).mpr
          (Submodule.mem_comap.mpr ?_)
        change z v • (g' v).val ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)
        exact Submodule.smul_mem_smul
          (Submodule.mem_iSup_of_mem (q - q₁.val) (Submodule.mem_iSup_of_mem (by omega) hz_mem))
          Submodule.mem_top
      · have hz0 : z v = 0 := by simpa [hneg (q - q₁.val) (by omega)] using hz_mem
        have hterm0 : term v = 0 := Subtype.ext (by
          change z v • (g' v).val = 0
          rw [hz0, zero_smul])
        change Submodule.Quotient.mk (term v) = 0
        rw [hterm0, Submodule.Quotient.mk_zero]
    · exact fun h ↦ absurd (Finset.mem_univ q') h
  -- Conclude by `k`-linear independence of the lifted head basis `bq q'`.
  have hlin := Fintype.linearIndependent_iff.mp (bq q').linearIndependent
    (fun t ↦ connectedAugmentation hneg hzero (z (eqv.symm ⟨q', t⟩))) hq_fiber
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
  -- Lift `k`-bases of `PieceQuotient M q` via its retract embedding into `{j // s j = q} → k`.
  let S : Finset ℤ := Finset.univ.image s
  let pidPkg : ∀ q : S,
      Σ n : ℕ, Module.Basis (Fin n) k
        (LinearMap.range (retractPieceQuotientHom hneg hzero r q.val)) :=
    fun q ↦ Submodule.basisOfPid (Pi.basisFun k {j : I // s j = q.val}) _
  let nq : S → ℕ := fun q ↦ (pidPkg q).fst
  let bq : ∀ q : S, Module.Basis (Fin (nq q)) k (PieceQuotient M q.val) := fun q ↦
    (pidPkg q).snd.map
      (LinearEquiv.ofInjective (retractPieceQuotientHom hneg hzero r q.val)
        (injective_retractPieceQuotientHom hneg hzero r q.val)).symm
  let liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.val := fun q t ↦
    let y := (Submodule.Quotient.mk_surjective _ (bq q t)).choose
    ⟨y.val, mem_pieceSubmodule.mp y.property⟩
  have hliftGen : ∀ (q : S) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, (liftGen q t).property⟩ :
        PieceQuotient M q.val) = bq q t :=
    fun q t ↦ (Submodule.Quotient.mk_surjective _ (bq q t)).choose_spec
  let n : ℕ := Fintype.card (Σ q : S, Fin (nq q))
  let ev : Fin n ≃ Σ q : S, Fin (nq q) := (Fintype.equivFin _).symm
  let d : Fin n → ℤ := fun u ↦ (ev u).fst.val
  let d' : ULift.{uI} (Fin n) → ℤ := d ∘ ULift.down
  let Φ : free 𝒜 d' ⟶ M := freeLift fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  -- Surjectivity of `Φ` splits its kernel sequence by projectivity of `M`.
  have hsurjΦ : Function.Surjective Φ.hom :=
    surjective_freeLift_of_retractHeadBasis hneg hzero r nq bq liftGen hliftGen ev
  have : Epi Φ := (epi_iff_surjective Φ).mpr hsurjΦ
  have : Projective M := r.projective
  have : Epi (ShortComplex.kernelSequence Φ).g := ‹Epi Φ›
  have : Projective (ShortComplex.kernelSequence Φ).X₃ := ‹Projective M›
  let sp := (ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact Φ)
    inferInstance inferInstance).splittingOfProjective
  let K : GradedModuleCat.{max uA uI} 𝒜 := Limits.kernel Φ
  let rK : Retract K (free 𝒜 d') := ⟨Limits.kernel.ι Φ, sp.r, sp.f_r⟩
  -- The split kernel is bounded below with vanishing head coordinates, hence `0`.
  let _ := K.gradedSMul
  obtain ⟨bK, hbK⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg d'
  have hbelowK : ∀ p < bK, K.grading.piece p = ⊥ := fun p hp ↦
    rK.piece_eq_bot (hbK p hp)
  have hker_pos : ∀ q : ℤ, K.grading.piece q ≤
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k K) := fun q z hz ↦ by
    have hz_ker : Φ.hom ((Limits.kernel.ι Φ).hom z) = 0 :=
      LinearMap.congr_fun (congrArg Hom.hom (Limits.kernel.condition Φ)) z
    exact rK.mem_positive_smul_top_iff.mp
      ((freeHeadCoord_eq_zero_iff hneg hzero d' q ⟨(Limits.kernel.ι Φ).hom z,
        map_mem (Limits.kernel.ι Φ) hz⟩).mp
        (freeHeadCoord_eq_zero_of_mem_ker_freeLift hneg hzero nq bq liftGen hliftGen ev q
          (map_mem (Limits.kernel.ι Φ) hz) hz_ker))
  have htopK : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k K) = ⊤ := by
    have hle := iSup_le hker_pos
    rw [(DirectSum.Decomposition.isInternal K.grading.piece).submodule_iSup_eq_top]
      at hle
    exact top_unique hle
  have : Subsingleton K :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 bK hbelowK htopK
  have : Mono Φ := Abelian.mono_of_kernel_ι_eq_zero Φ
    (hom_ext <| LinearMap.ext fun (z : K) ↦ by simp [Subsingleton.elim z 0])
  have : IsIso Φ := isIso_of_mono_of_epi Φ
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

end TauCeti.GradedModuleCat
