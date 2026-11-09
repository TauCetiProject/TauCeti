/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Joint regularity of all spatial derivatives

Products, smooth composition, differentiation and inversion of invertible continuous
linear maps preserve fixed finite joint regularity of every spatial derivative of a
parameter-dependent family. The parameter set is arbitrary and the spatial set is open.
These operations support the coordinate jet bootstrap for smooth Ricci-flow restart
(Morgan–Tian, Proposition 3.12).

Public formalization references:
[lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set
open scoped ContDiff Topology
universe u v

variable {T : Type v} [NormedAddCommGroup T] [NormedSpace ℝ T]
namespace TauCeti

section FiniteSpatialJets

/-- Fixed finite joint regularity of all spatial derivatives is preserved when the spatial
derivative is taken once more. -/
theorem contDiffOn_spatial_jets_fderiv
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {J : Set T} {U : Set E} (k : ℕ) (f : T → E → F)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦ iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦
        iteratedFDeriv ℝ q (fun x ↦ fderiv ℝ (f p.1) x) p.2) (J ×ˢ U) := by
  intro q
  let L : (E [×(q + 1)]→L[ℝ] F) →L[ℝ] (E [×q]→L[ℝ] (E →L[ℝ] F)) :=
    (continuousMultilinearCurryRightEquiv' ℝ q E F)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContDiff ℝ (k : ℕ∞ω) L :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := E [×(q + 1)]→L[ℝ] F)
      (F := E [×q]→L[ℝ] (E →L[ℝ] F)) L
  have h := hL.comp_contDiffOn (hjets (q + 1))
  apply h.congr
  intro p _
  change _ = L (iteratedFDeriv ℝ (q + 1) (f p.1) p.2)
  rw [iteratedFDeriv_succ_eq_comp_right]
  exact ((continuousMultilinearCurryRightEquiv' ℝ q E F).apply_symm_apply _).symm

/-- Two families with smooth spatial slices and fixed finite joint regularity of every spatial
jet have the same regularity after pairing. -/
theorem contDiffOn_spatial_jets_prodMk
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set T} {U : Set E} (hU : IsOpen U) (k : ℕ)
    (f : T → E → F) (g : T → E → G)
    (hf : ∀ t ∈ J, ContDiffOn ℝ ∞ (f t) U)
    (hg : ∀ t ∈ J, ContDiffOn ℝ ∞ (g t) U)
    (hfj : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦ iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U))
    (hgj : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦ iteratedFDeriv ℝ q (g p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦
        iteratedFDeriv ℝ q (fun x ↦ (f p.1 x, g p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  let L : ((E [×q]→L[ℝ] F) × (E [×q]→L[ℝ] G)) →L[ℝ]
      (E [×q]→L[ℝ] (F × G)) :=
    (ContinuousMultilinearMap.prodL ℝ (fun _ : Fin q ↦ E) F G)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.contDiff.comp_contDiffOn ((hfj q).prodMk (hgj q))
  apply h.congr
  intro p hp
  exact iteratedFDeriv_prodMk
    ((hf p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    ((hg p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    (show (q : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)

/-- Smooth composition preserves fixed finite joint regularity of every spatial jet on the
stated mapped domain. -/
theorem contDiffOn_spatial_jets_comp
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {J : Set T} {U : Set E} {W : Set F}
    (hU : IsOpen U) (hW : IsOpen W) (k : ℕ)
    (f : T → E → F) (Phi : F → G)
    (hf : ∀ t ∈ J, ContDiffOn ℝ ∞ (f t) U)
    (hPhi : ContDiffOn ℝ ∞ Phi W)
    (hmap : ∀ t ∈ J, MapsTo (f t) U W)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦ iteratedFDeriv ℝ q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦
        iteratedFDeriv ℝ q (fun x ↦ Phi (f p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  induction q generalizing F G with
  | zero =>
    let L : (E [×0]→L[ℝ] F) →L[ℝ] F :=
      (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.toContinuousLinearMap
    have h0 : ContDiffOn ℝ k (fun p : T × E ↦ f p.1 p.2) (J ×ˢ U) :=
      L.contDiff.comp_contDiffOn (hjets 0)
    have hc : ContDiffOn ℝ k (fun p : T × E ↦ Phi (f p.1 p.2)) (J ×ˢ U) :=
      (hPhi.of_le (show (k : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp h0
        (fun p hp ↦ hmap p.1 hp.1 hp.2)
    let L' : G →L[ℝ] (E [×0]→L[ℝ] G) :=
      (continuousMultilinearCurryFin0 ℝ E G).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L'.contDiff.comp_contDiffOn hc
  | succ q ih =>
    let H : T → E → F × (E →L[ℝ] F) := fun t x ↦ (f t x, fderiv ℝ (f t) x)
    let Psi : F × (E →L[ℝ] F) → E →L[ℝ] G :=
      fun p ↦ (fderiv ℝ Phi p.1).comp p.2
    have hd (t : T) (ht : t ∈ J) : ContDiffOn ℝ ∞ (fderiv ℝ (f t)) U :=
      (hf t ht).fderiv_of_isOpen hU (by simp)
    have hH (t : T) (ht : t ∈ J) : ContDiffOn ℝ ∞ (H t) U :=
      (hf t ht).prodMk (hd t ht)
    have hHj : ∀ r : ℕ, ContDiffOn ℝ k
        (fun p : T × E ↦ iteratedFDeriv ℝ r (H p.1) p.2) (J ×ˢ U) :=
      contDiffOn_spatial_jets_prodMk hU k f (fun t ↦ fderiv ℝ (f t)) hf hd hjets
        (contDiffOn_spatial_jets_fderiv k f hjets)
    have hPsi : ContDiffOn ℝ ∞ Psi (W ×ˢ (univ : Set (E →L[ℝ] F))) :=
      ((hPhi.fderiv_of_isOpen hW (by simp)).comp contDiffOn_fst
        (fun p (hp : p ∈ W ×ˢ (univ : Set (E →L[ℝ] F))) ↦ hp.1)).clm_comp contDiffOn_snd
    have hQ := ih (F := F × (E →L[ℝ] F)) (G := E →L[ℝ] G)
      (W := W ×ˢ (univ : Set (E →L[ℝ] F))) (hW := hW.prod isOpen_univ)
      (f := H) (Phi := Psi) hH hPsi (fun t ht x hx ↦ ⟨hmap t ht hx, mem_univ _⟩) hHj
    let L : (E [×q]→L[ℝ] (E →L[ℝ] G)) →L[ℝ] (E [×(q + 1)]→L[ℝ] G) :=
      (continuousMultilinearCurryRightEquiv' ℝ q E G).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap
    have h := L.contDiff.comp_contDiffOn hQ
    apply h.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right]
    change L (iteratedFDeriv ℝ q (fderiv ℝ (fun x ↦ Phi (f p.1 x))) p.2) =
      L (iteratedFDeriv ℝ q (fun x ↦ Psi (H p.1 x)) p.2)
    apply congrArg L
    have heq : fderiv ℝ (fun x ↦ Phi (f p.1 x)) =ᶠ[𝓝 p.2] fun x ↦ Psi (H p.1 x) := by
      filter_upwards [hU.mem_nhds hp.2] with x hx
      exact (((hPhi.contDiffAt (hW.mem_nhds (hmap p.1 hp.1 hx))).differentiableAt
        (by simp)).hasFDerivAt.comp x
          (((hf p.1 hp.1).contDiffAt (hU.mem_nhds hx)).differentiableAt
            (by simp)).hasFDerivAt).fderiv
    exact (heq.iteratedFDeriv ℝ q).eq_of_nhds

/-- Actual invertibility at every point lets the inverse operator family retain fixed finite
joint regularity of every spatial jet. -/
theorem contDiffOn_spatial_jets_inverse
    {E P Q : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {J : Set T} {U : Set E} (hU : IsOpen U) (k : ℕ)
    (A : T → E → P →L[ℝ] Q)
    (hA : ∀ t ∈ J, ContDiffOn ℝ ∞ (A t) U)
    (hInv : ∀ t ∈ J, ∀ x ∈ U, (A t x).IsInvertible)
    (hjets : ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦ iteratedFDeriv ℝ q (A p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn ℝ k
      (fun p : T × E ↦
        iteratedFDeriv ℝ q (fun x ↦ (A p.1 x).inverse) p.2) (J ×ˢ U) := by
  let W : Set (P →L[ℝ] Q) := range (fun e : P ≃L[ℝ] Q ↦ (e : P →L[ℝ] Q))
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen
  have hinv : ContDiffOn ℝ ∞ (ContinuousLinearMap.inverse :
      (P →L[ℝ] Q) → (Q →L[ℝ] P)) W := by
    intro B hB
    exact (show B.IsInvertible from hB).contDiffAt_map_inverse.contDiffWithinAt
  exact contDiffOn_spatial_jets_comp hU hW k A ContinuousLinearMap.inverse hA hinv
    (fun t ht x hx ↦ hInv t ht x hx) hjets

end FiniteSpatialJets

end TauCeti
