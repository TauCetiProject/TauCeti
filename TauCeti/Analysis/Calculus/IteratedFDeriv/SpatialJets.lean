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
linear maps preserve fixed joint regularity of every spatial derivative of a
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

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {T : Type v} [NormedAddCommGroup T] [NormedSpace 𝕜 T]
namespace TauCeti

section SpatialJets

/-- Fixed joint regularity of all spatial derivatives is preserved when the spatial
derivative is taken once more. -/
theorem contDiffOn_spatial_jets_fderiv
    {E F : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {J : Set T} {U : Set E} (k : ℕ∞) (f : T → E → F)
    (hjets : ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦ iteratedFDeriv 𝕜 q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦
        iteratedFDeriv 𝕜 q (fun x ↦ fderiv 𝕜 (f p.1) x) p.2) (J ×ˢ U) := by
  intro q
  let L : (E [×(q + 1)]→L[𝕜] F) →L[𝕜] (E [×q]→L[𝕜] (E →L[𝕜] F)) :=
    (continuousMultilinearCurryRightEquiv' 𝕜 q E F)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ContDiff 𝕜 (k : ℕ∞ω) L :=
    ContinuousLinearMap.contDiff (𝕜 := 𝕜) (E := E [×(q + 1)]→L[𝕜] F)
      (F := E [×q]→L[𝕜] (E →L[𝕜] F)) L
  have h := hL.comp_contDiffOn (hjets (q + 1))
  apply h.congr
  intro p _
  -- The right-curry equivalence identifies a multilinear derivative with a linear-map-valued one.
  change _ = L (iteratedFDeriv 𝕜 (q + 1) (f p.1) p.2)
  rw [iteratedFDeriv_succ_eq_comp_right]
  exact ((continuousMultilinearCurryRightEquiv' 𝕜 q E F).apply_symm_apply _).symm

/-- Two families with smooth spatial slices and fixed joint regularity of every spatial
jet have the same regularity after pairing. -/
theorem contDiffOn_spatial_jets_prodMk
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {J : Set T} {U : Set E} (hU : IsOpen U) (k : ℕ∞)
    (f : T → E → F) (g : T → E → G)
    (hf : ∀ t ∈ J, ContDiffOn 𝕜 ∞ (f t) U)
    (hg : ∀ t ∈ J, ContDiffOn 𝕜 ∞ (g t) U)
    (hfj : ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦ iteratedFDeriv 𝕜 q (f p.1) p.2) (J ×ˢ U))
    (hgj : ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦ iteratedFDeriv 𝕜 q (g p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦
        iteratedFDeriv 𝕜 q (fun x ↦ (f p.1 x, g p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  let L : ((E [×q]→L[𝕜] F) × (E [×q]→L[𝕜] G)) →L[𝕜]
      (E [×q]→L[𝕜] (F × G)) :=
    (ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin q ↦ E) F G)
      |>.toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.contDiff.comp_contDiffOn ((hfj q).prodMk (hgj q))
  apply h.congr
  intro p hp
  have hq : (q : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  exact iteratedFDeriv_prodMk
    ((hf p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    ((hg p.1 hp.1).contDiffAt (hU.mem_nhds hp.2))
    hq

/-- Smooth composition preserves fixed joint regularity of every spatial jet on the
stated mapped domain. -/
theorem contDiffOn_spatial_jets_comp
    {E F G : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {J : Set T} {U : Set E} {W : Set F}
    (hU : IsOpen U) (hW : IsOpen W) (k : ℕ∞)
    (f : T → E → F) (Phi : F → G)
    (hf : ∀ t ∈ J, ContDiffOn 𝕜 ∞ (f t) U)
    (hPhi : ContDiffOn 𝕜 ∞ Phi W)
    (hmap : ∀ t ∈ J, MapsTo (f t) U W)
    (hjets : ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦ iteratedFDeriv 𝕜 q (f p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦
        iteratedFDeriv 𝕜 q (fun x ↦ Phi (f p.1 x)) p.2) (J ×ˢ U) := by
  intro q
  induction q generalizing F G with
  | zero =>
    let L : (E [×0]→L[𝕜] F) →L[𝕜] F :=
      (continuousMultilinearCurryFin0 𝕜 E F).toContinuousLinearEquiv.toContinuousLinearMap
    have h0 : ContDiffOn 𝕜 k (fun p : T × E ↦ f p.1 p.2) (J ×ˢ U) :=
      L.contDiff.comp_contDiffOn (hjets 0)
    have hk : (k : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hc : ContDiffOn 𝕜 k (fun p : T × E ↦ Phi (f p.1 p.2)) (J ×ˢ U) :=
      (hPhi.of_le hk).comp h0
        (fun p hp ↦ hmap p.1 hp.1 hp.2)
    let L' : G →L[𝕜] (E [×0]→L[𝕜] G) :=
      (continuousMultilinearCurryFin0 𝕜 E G).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact L'.contDiff.comp_contDiffOn hc
  | succ q ih =>
    let H : T → E → F × (E →L[𝕜] F) := fun t x ↦ (f t x, fderiv 𝕜 (f t) x)
    let Psi : F × (E →L[𝕜] F) → E →L[𝕜] G :=
      fun p ↦ (fderiv 𝕜 Phi p.1).comp p.2
    have hd (t : T) (ht : t ∈ J) : ContDiffOn 𝕜 ∞ (fderiv 𝕜 (f t)) U :=
      (hf t ht).fderiv_of_isOpen hU (by simp)
    have hH (t : T) (ht : t ∈ J) : ContDiffOn 𝕜 ∞ (H t) U :=
      (hf t ht).prodMk (hd t ht)
    have hHj : ∀ r : ℕ, ContDiffOn 𝕜 k
        (fun p : T × E ↦ iteratedFDeriv 𝕜 r (H p.1) p.2) (J ×ˢ U) :=
      contDiffOn_spatial_jets_prodMk hU k f (fun t ↦ fderiv 𝕜 (f t)) hf hd hjets
        (contDiffOn_spatial_jets_fderiv k f hjets)
    have hPsi : ContDiffOn 𝕜 ∞ Psi (W ×ˢ (univ : Set (E →L[𝕜] F))) :=
      ((hPhi.fderiv_of_isOpen hW (by simp)).comp contDiffOn_fst
        (fun p (hp : p ∈ W ×ˢ (univ : Set (E →L[𝕜] F))) ↦ hp.1)).clm_comp contDiffOn_snd
    have hQ := ih (F := F × (E →L[𝕜] F)) (G := E →L[𝕜] G)
      (W := W ×ˢ (univ : Set (E →L[𝕜] F))) (hW := hW.prod isOpen_univ)
      (f := H) (Phi := Psi) hH hPsi (fun t ht x hx ↦ ⟨hmap t ht hx, mem_univ _⟩) hHj
    let L : (E [×q]→L[𝕜] (E →L[𝕜] G)) →L[𝕜] (E [×(q + 1)]→L[𝕜] G) :=
      (continuousMultilinearCurryRightEquiv' 𝕜 q E G).symm
        |>.toContinuousLinearEquiv.toContinuousLinearMap
    have h := L.contDiff.comp_contDiffOn hQ
    apply h.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right]
    -- Apply the inverse currying map to both representations of the next derivative.
    change L (iteratedFDeriv 𝕜 q (fderiv 𝕜 (fun x ↦ Phi (f p.1 x))) p.2) =
      L (iteratedFDeriv 𝕜 q (fun x ↦ Psi (H p.1 x)) p.2)
    apply congrArg L
    have heq : fderiv 𝕜 (fun x ↦ Phi (f p.1 x)) =ᶠ[𝓝 p.2] fun x ↦ Psi (H p.1 x) := by
      filter_upwards [hU.mem_nhds hp.2] with x hx
      exact (((hPhi.contDiffAt (hW.mem_nhds (hmap p.1 hp.1 hx))).differentiableAt
        (by simp)).hasFDerivAt.comp x
          (((hf p.1 hp.1).contDiffAt (hU.mem_nhds hx)).differentiableAt
            (by simp)).hasFDerivAt).fderiv
    exact (heq.iteratedFDeriv 𝕜 q).eq_of_nhds

/-- Actual invertibility at every point lets the inverse operator family retain fixed
joint regularity of every spatial jet. -/
theorem contDiffOn_spatial_jets_inverse
    {E P Q : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
    [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
    {J : Set T} {U : Set E} (hU : IsOpen U) (k : ℕ∞)
    (A : T → E → P →L[𝕜] Q)
    (hA : ∀ t ∈ J, ContDiffOn 𝕜 ∞ (A t) U)
    (hInv : ∀ t ∈ J, ∀ x ∈ U, (A t x).IsInvertible)
    (hjets : ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦ iteratedFDeriv 𝕜 q (A p.1) p.2) (J ×ˢ U)) :
    ∀ q : ℕ, ContDiffOn 𝕜 k
      (fun p : T × E ↦
        iteratedFDeriv 𝕜 q (fun x ↦ (A p.1 x).inverse) p.2) (J ×ˢ U) := by
  let W : Set (P →L[𝕜] Q) := range (fun e : P ≃L[𝕜] Q ↦ (e : P →L[𝕜] Q))
  have hW : IsOpen W := ContinuousLinearEquiv.isOpen
  have hinv : ContDiffOn 𝕜 ∞ (ContinuousLinearMap.inverse :
      (P →L[𝕜] Q) → (Q →L[𝕜] P)) W := by
    intro B hB
    -- IsInvertible is membership in the range of continuous linear equivalences.
    have hBinv : B.IsInvertible := hB
    exact hBinv.contDiffAt_map_inverse.contDiffWithinAt
  exact contDiffOn_spatial_jets_comp hU hW k A ContinuousLinearMap.inverse hA hinv
    (fun t ht x hx ↦ hInv t ht x hx) hjets

end SpatialJets

end TauCeti
