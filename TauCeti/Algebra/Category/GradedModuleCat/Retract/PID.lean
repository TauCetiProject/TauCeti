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
import TauCeti.LinearAlgebra.Pi

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
    M.grading.PieceQuotient 𝒜 q →ₗ[k] ({j : I // s j = q} → k) :=
  (freePieceQuotientEquiv hneg hzero s q).toLinearMap.comp
    ((pieceQuotientHom r.i q).restrictScalars k)

private theorem injective_retractPieceQuotientHom (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s)) (q : ℤ) :
    Function.Injective (retractPieceQuotientHom hneg hzero r q) := by
  let rPQ := r.map (pieceQuotientFunctor (𝒜 := 𝒜) q)
  have hleft : Function.LeftInverse rPQ.r.hom rPQ.i.hom := fun x ↦
    LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp rPQ.retract) x
  exact (freePieceQuotientEquiv hneg hzero s q).injective.comp hleft.injective

omit [FaithfulSMul k A] in
/-- Subtracting the `bq`-coordinate combination of chosen lifts from `m ∈ M.grading.piece q`
leaves an element of `A₊ M`. -/
private theorem sub_sum_repr_smul_mem_positive_smul_top
    {M : GradedModuleCat.{v} 𝒜} {q : ℤ} {n : ℕ}
    (bq : Module.Basis (Fin n) k (M.grading.PieceQuotient 𝒜 q))
    (lift : Fin n → M.grading.piece q)
    (hlift : ∀ t : Fin n,
      (Submodule.Quotient.mk ⟨(lift t).val, InternalGrading.mem_pieceSubmodule.mpr
        (lift t).property⟩ : M.grading.PieceQuotient 𝒜 q) = bq t)
    {m : M} (hm : m ∈ M.grading.piece q) :
    m - ∑ t : Fin n,
      bq.repr (Submodule.Quotient.mk ⟨m, InternalGrading.mem_pieceSubmodule.mpr hm⟩) t •
        (lift t : M) ∈
        (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  let P : Submodule (SetLike.GradeZero.subalgebra 𝒜) (M.grading.pieceSubmodule 𝒜 q) :=
    (InternalGrading.positiveSubmodule M 𝒜).comap (M.grading.pieceSubmodule 𝒜 q).subtype
  let xm : M.grading.pieceSubmodule 𝒜 q := ⟨m, InternalGrading.mem_pieceSubmodule.mpr hm⟩
  let c : Fin n → k := bq.repr (Submodule.Quotient.mk xm)
  let ym : M.grading.pieceSubmodule 𝒜 q :=
    ∑ t : Fin n, c t • ⟨(lift t).val, InternalGrading.mem_pieceSubmodule.mpr (lift t).property⟩
  have hmk : (Submodule.Quotient.mk (xm - ym) : M.grading.PieceQuotient 𝒜 q) = 0 := by
    rw [← Submodule.mkQ_apply P (xm - ym), ← LinearMap.restrictScalars_apply k P.mkQ, map_sub,
      sub_eq_zero, map_sum]
    simp_rw [map_smul, LinearMap.restrictScalars_apply, Submodule.mkQ_apply, hlift]
    exact (bq.sum_repr (Submodule.Quotient.mk xm)).symm
  have hmem : (xm - ym : M.grading.pieceSubmodule 𝒜 q).val ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) :=
    (InternalGrading.mem_positiveSubmodule.mp <| Submodule.mem_comap.mp <|
      (Submodule.Quotient.mk_eq_zero P).mp hmk)
  have hcoe : (xm - ym : M.grading.pieceSubmodule 𝒜 q).val =
      m - ∑ t : Fin n, c t • (lift t : M) := by
    simp [xm, ym, AddSubmonoidClass.coe_finsetSum]
  exact hcoe ▸ hmem

/-- If `liftGen q` lifts a `k`-basis `bq q` of `M.grading.PieceQuotient 𝒜 q.val` for every shift
`q` in the image of `s`, then the induced morphism `freeLift` onto `M` is surjective. -/
private theorem surjective_freeLift_of_retractHeadBasis (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {I : Type uI} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (r : Retract M (free 𝒜 s))
    (nq : (Finset.univ.image s) → ℕ)
    (bq : ∀ q : Finset.univ.image s, Module.Basis (Fin (nq q)) k (M.grading.PieceQuotient 𝒜 q.val))
    (liftGen : ∀ q : Finset.univ.image s, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : Finset.univ.image s) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, InternalGrading.mem_pieceSubmodule.mpr
        (liftGen q t).property⟩ : M.grading.PieceQuotient 𝒜 q.val) = bq q t)
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
    let c := (bq q').repr (Submodule.Quotient.mk ⟨m, InternalGrading.mem_pieceSubmodule.mpr hm⟩)
    let y : M := ∑ t : Fin (nq q'), c t • (liftGen q' t : M)
    have hy_range : y ∈ LinearMap.range Φ.hom := by
      refine Submodule.sum_mem (LinearMap.range Φ.hom) fun t _ ↦ ?_
      rw [← algebraMap_smul A]
      refine Submodule.smul_mem (LinearMap.range Φ.hom) (algebraMap k A (c t))
        ⟨freeGenerator (ULift.up (ev.symm ⟨q', t⟩)),
          (freeLift_generator g' (ULift.up (ev.symm ⟨q', t⟩))).trans <|
            congrArg (fun idx : Σ q : Finset.univ.image s, Fin (nq q) ↦
                (liftGen idx.fst idx.snd : M))
              (ev.apply_symm_apply ⟨q', t⟩)⟩
    have hdiff_pos : m - y ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) :=
      sub_sum_repr_smul_mem_positive_smul_top (bq q') (liftGen q') (hliftGen q') hm
    rw [← add_sub_cancel y m]
    exact Submodule.add_mem_sup hy_range hdiff_pos
  · have : IsEmpty {j : I // s j = q} :=
      ⟨fun j ↦ hqS (j.property ▸ Finset.mem_image_of_mem s (Finset.mem_univ j.val))⟩
    have : Subsingleton (M.grading.PieceQuotient 𝒜 q) :=
      (injective_retractPieceQuotientHom hneg hzero r q).subsingleton
    have hmk0 : (Submodule.Quotient.mk
        (⟨m, InternalGrading.mem_pieceSubmodule.mpr hm⟩ : M.grading.pieceSubmodule 𝒜 q) :
        M.grading.PieceQuotient 𝒜 q) = 0 :=
      Subsingleton.elim _ _
    exact Submodule.mem_sup_right <| InternalGrading.mem_positiveSubmodule.mp <|
      Submodule.mem_comap.mp <|
      (Submodule.Quotient.mk_eq_zero ((InternalGrading.positiveSubmodule M 𝒜).comap
        (M.grading.pieceSubmodule 𝒜 q).subtype)).mp hmk0

/-- Equivalence between the shift-`q'` fiber of `ULift (Fin n)` along `ev` and `Fin (nq q')`. -/
private def retractHeadFiberEquiv {S : Finset ℤ} {nq : S → ℕ} {n : ℕ}
    (ev : Fin n ≃ Σ q : S, Fin (nq q)) (q' : S) :
    {u : ULift.{uI} (Fin n) // ((fun u ↦ (ev u).fst.val) ∘ ULift.down) u = q'.val} ≃ Fin (nq q') :=
  (Equiv.subtypeEquiv (p := fun u : ULift.{uI} (Fin n) ↦
      ((fun u ↦ (ev u).fst.val) ∘ ULift.down) u = q'.val)
    (Equiv.ulift.trans ev) fun _ ↦
    ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩).trans
    (Equiv.sigmaSubtype q')

/-- On head coordinates in degree `q'`, the map induced by `freeLift` from a basis lift equals
coordinate reindexing along the fiber equivalence `retractHeadFiberEquiv ev q'`. -/
private theorem freeLift_pieceQuotient_comp_equivFun
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {S : Finset ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (nq : S → ℕ)
    (bq : ∀ q : S, Module.Basis (Fin (nq q)) k (M.grading.PieceQuotient 𝒜 q.val))
    (liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : S) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, InternalGrading.mem_pieceSubmodule.mpr
        (liftGen q t).property⟩ : M.grading.PieceQuotient 𝒜 q.val) = bq q t)
    {n : ℕ} (ev : Fin n ≃ Σ q : S, Fin (nq q)) (q' : S) :
    (bq q').equivFun.toLinearMap.comp
      (((pieceQuotientHom
          (freeLift (d := (fun u ↦ (ev u).fst.val) ∘ ULift.down)
            (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).fst (ev u.down).snd))
          q'.val).restrictScalars k).comp
        (freePieceQuotientEquiv hneg hzero
          ((fun u ↦ (ev u).fst.val) ∘ ULift.down) q'.val).symm.toLinearMap) =
      (LinearEquiv.piCongrLeft k (fun _ ↦ k) (retractHeadFiberEquiv ev q')).toLinearMap := by
  let d' : ULift.{uI} (Fin n) → ℤ := (fun u ↦ (ev u).fst.val) ∘ ULift.down
  let g' : ∀ u : ULift.{uI} (Fin n), M.grading.piece (d' u) :=
    fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  let Φ : free 𝒜 d' ⟶ M := freeLift g'
  let e_q := retractHeadFiberEquiv ev q'
  refine LinearMap.pi_ext fun u c ↦ ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [freePieceQuotientEquiv_symm_single, map_smul, map_smul, LinearMap.restrictScalars_apply,
    pieceQuotientHom_apply]
  have hev : ev u.val.down = ⟨q', e_q u⟩ :=
    (Equiv.ulift.trans ev).eq_symm_apply.mp (congrArg Subtype.val (e_q.symm_apply_apply u).symm)
  have hgen : Φ.hom (freeGenerator u.val) = (liftGen q' (e_q u)).val := by
    have h1 : Φ.hom (freeGenerator u.val) = (g' u.val).val := freeLift_generator g' u.val
    -- `hev` aligns the dependent sigma pair `(ev u.val.down).fst, (ev u.val.down).snd` with
    -- `⟨q', e_q u⟩` so `liftGen` evaluates in the same degree piece.
    have h2 : (g' u.val).val = (liftGen q' (e_q u)).val :=
      congrArg (fun idx : Σ p : S, Fin (nq p) ↦ (liftGen idx.fst idx.snd).val) hev
    exact h1.trans h2
  have hsub : (⟨Φ.hom (freeGenerator u.val),
      InternalGrading.mem_pieceSubmodule.mpr
        (map_mem Φ (freeGenerator_mem_free_piece_of_eq u.property))⟩ :
      M.grading.pieceSubmodule 𝒜 q'.val) =
      ⟨(liftGen q' (e_q u)).val,
        InternalGrading.mem_pieceSubmodule.mpr (liftGen q' (e_q u)).property⟩ :=
    Subtype.ext hgen
  rw [hsub, hliftGen, LinearEquiv.piCongrLeft_single]
  ext t
  simp [e_q, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- For every degree `q`, `freeLift` from a basis lift of `M.grading.PieceQuotient 𝒜` induces
an injective map on `PieceQuotient` in degree `q`. -/
private theorem injective_pieceQuotientHom_freeLift
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (hzero : ∀ a ∈ 𝒜 0, a ∈ LinearMap.range (Algebra.linearMap k A))
    {S : Finset ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (nq : S → ℕ)
    (bq : ∀ q : S, Module.Basis (Fin (nq q)) k (M.grading.PieceQuotient 𝒜 q.val))
    (liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.val)
    (hliftGen : ∀ (q : S) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, InternalGrading.mem_pieceSubmodule.mpr
        (liftGen q t).property⟩ : M.grading.PieceQuotient 𝒜 q.val) = bq q t)
    {n : ℕ} (ev : Fin n ≃ Σ q : S, Fin (nq q)) (q : ℤ) :
    Function.Injective
      (pieceQuotientHom
        (freeLift (d := (fun u ↦ (ev u).fst.val) ∘ ULift.down)
          (fun u : ULift.{uI} (Fin n) ↦ liftGen (ev u.down).fst (ev u.down).snd))
        q) := by
  let d' : ULift.{uI} (Fin n) → ℤ := (fun u ↦ (ev u).fst.val) ∘ ULift.down
  let g' : ∀ u : ULift.{uI} (Fin n), M.grading.piece (d' u) :=
    fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  let Φ : free 𝒜 d' ⟶ M := freeLift g'
  by_cases hq : q ∈ S
  · let q' : S := ⟨q, hq⟩
    have hcomp := freeLift_pieceQuotient_comp_equivFun hneg hzero nq bq liftGen hliftGen ev q'
    have hinj : Function.Injective
        ((bq q').equivFun.toLinearMap.comp
          (((pieceQuotientHom Φ q).restrictScalars k).comp
            (freePieceQuotientEquiv hneg hzero d' q).symm.toLinearMap)) := by
      rw [hcomp]
      exact (LinearEquiv.piCongrLeft k (fun _ ↦ k) (retractHeadFiberEquiv ev q')).injective
    intro x y hxy
    obtain ⟨x', rfl⟩ := (freePieceQuotientEquiv hneg hzero d' q).symm.surjective x
    obtain ⟨y', rfl⟩ := (freePieceQuotientEquiv hneg hzero d' q).symm.surjective y
    exact congrArg _ (hinj (by simp [Φ, d', g', hxy]))
  · have : IsEmpty {u : ULift.{uI} (Fin n) // d' u = q} :=
      ⟨fun u ↦ hq (u.property ▸ (ev u.val.down).fst.property)⟩
    have : Subsingleton ((free 𝒜 d').grading.PieceQuotient 𝒜 q) :=
      (freePieceQuotientEquiv hneg hzero d' q).injective.subsingleton
    exact Function.injective_of_subsingleton _

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
  -- Lift `k`-bases of `M.grading.PieceQuotient 𝒜 q` via its retract embedding.
  let S : Finset ℤ := Finset.univ.image s
  let pidPkg : ∀ q : S,
      Σ n : ℕ, Module.Basis (Fin n) k
        (LinearMap.range (retractPieceQuotientHom hneg hzero r q.val)) :=
    fun q ↦ Submodule.basisOfPid (Pi.basisFun k {j : I // s j = q.val}) _
  let nq : S → ℕ := fun q ↦ (pidPkg q).fst
  let bq : ∀ q : S, Module.Basis (Fin (nq q)) k (M.grading.PieceQuotient 𝒜 q.val) := fun q ↦
    (pidPkg q).snd.map
      (LinearEquiv.ofInjective (retractPieceQuotientHom hneg hzero r q.val)
        (injective_retractPieceQuotientHom hneg hzero r q.val)).symm
  let liftGen : ∀ q : S, Fin (nq q) → M.grading.piece q.val := fun q t ↦
    let y := (Submodule.Quotient.mk_surjective _ (bq q t)).choose
    ⟨y.val, InternalGrading.mem_pieceSubmodule.mp y.property⟩
  have hliftGen : ∀ (q : S) (t : Fin (nq q)),
      (Submodule.Quotient.mk ⟨(liftGen q t).val, InternalGrading.mem_pieceSubmodule.mpr
        (liftGen q t).property⟩ : M.grading.PieceQuotient 𝒜 q.val) = bq q t :=
    fun q t ↦ (Submodule.Quotient.mk_surjective _ (bq q t)).choose_spec
  let n : ℕ := Fintype.card (Σ q : S, Fin (nq q))
  let ev : Fin n ≃ Σ q : S, Fin (nq q) := (Fintype.equivFin _).symm
  let d : Fin n → ℤ := fun u ↦ (ev u).fst.val
  let d' : ULift.{uI} (Fin n) → ℤ := d ∘ ULift.down
  let Φ : free 𝒜 d' ⟶ M := freeLift fun u ↦ liftGen (ev u.down).fst (ev u.down).snd
  -- Split-kernel Nakayama applies: `Φ` is epi onto projective `M` and injective on `PieceQuotient`.
  have : Epi Φ := (epi_iff_surjective Φ).mpr
    (surjective_freeLift_of_retractHeadBasis hneg hzero r nq bq liftGen hliftGen ev)
  have : Projective M := r.projective
  obtain ⟨b, hb⟩ := exists_piece_eq_bot_of_lt_free (𝒜 := 𝒜) hneg d'
  have : IsIso Φ := isIso_of_epi_of_ker_le_positive_smul_top hb Φ fun _ hz ↦
    mem_positive_smul_top_of_injective_pieceQuotientHom Φ
      (injective_pieceQuotientHom_freeLift hneg hzero nq bq liftGen hliftGen ev) hz
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
