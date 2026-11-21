/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Joint regularity of all spatial derivatives

Products, smooth composition, differentiation and inversion of invertible continuous
linear maps preserve fixed joint regularity of every spatial derivative of a
parameter-dependent family. The parameter set is arbitrary and the spatial set is open.
These operations support the coordinate jet bootstrap for smooth Ricci-flow restart
(Morgan–Tian, Proposition 3.12).

For a merely topological parameter space, joint continuity of every spatial derivative survives
multiplication by a fixed smooth scalar function (`TauCeti.continuousOn_spatial_jets_smul`). This
is the form of joint regularity in which integrals over compact parameter spaces may be
differentiated under the integral sign (`TauCeti.contDiffOn_integral_of_continuous_jets`), for
instance for cut-off homogeneous terms of symbols.

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

section ContinuousSpatialJets

open Filter

variable {Y E F : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {𝕜' : Type*} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Multiplying a family by a fixed smooth scalar function preserves joint continuity of every
spatial derivative, in the parameter and the point. The parameter space need only be a
topological space; the spatial set is open. -/
theorem continuousOn_spatial_jets_smul {U : Set E} (hU : IsOpen U) {c : E → 𝕜'}
    (hc : ContDiffOn 𝕜 ∞ c U) {f : Y → E → F} (hf : ∀ y, ContDiffOn 𝕜 ∞ (f y) U)
    (hjets : ∀ q : ℕ,
      ContinuousOn (fun p : Y × E ↦ iteratedFDeriv 𝕜 q (f p.1) p.2) (univ ×ˢ U)) (k : ℕ) :
    ContinuousOn (fun p : Y × E ↦ iteratedFDeriv 𝕜 k (fun x ↦ c x • f p.1 x) p.2)
      (univ ×ˢ U) := by
  rintro ⟨y₀, x₀⟩ ⟨-, hx₀⟩
  have hat {g : E → F} (hg : ContDiffOn 𝕜 ∞ g U) {x : E} (hx : x ∈ U) (i : ℕ) :
      ContDiffAt 𝕜 i g x :=
    ((hg x hx).contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast le_top)
  let g : Y → E → F := fun y x ↦ c x • f y x
  have hg (y : Y) : ContDiffOn 𝕜 ∞ (g y) U := hc.smul (hf y)
  -- Since `g y - g y₀ = c • (f y - f y₀)`, the Leibniz rule bounds the change of the jets of `g`.
  have hbound : ∀ p ∈ (univ : Set Y) ×ˢ U,
      ‖iteratedFDeriv 𝕜 k (g p.1) p.2 - iteratedFDeriv 𝕜 k (g y₀) x₀‖ ≤
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i c p.2‖ *
          ‖iteratedFDeriv 𝕜 (k - i) (f p.1) p.2 - iteratedFDeriv 𝕜 (k - i) (f y₀) p.2‖) +
        ‖iteratedFDeriv 𝕜 k (g y₀) p.2 - iteratedFDeriv 𝕜 k (g y₀) x₀‖ := by
    rintro ⟨y, x⟩ ⟨-, hx⟩
    replace hx : x ∈ U := hx
    have hsub : iteratedFDeriv 𝕜 k (g y) x - iteratedFDeriv 𝕜 k (g y₀) x =
        iteratedFDeriv 𝕜 k (fun z ↦ c z • (f y - f y₀) z) x := by
      rw [← iteratedFDeriv_sub_apply (hat (hg y) hx k) (hat (hg y₀) hx k)]
      congr 1
      funext z
      simp [g, smul_sub]
    have hleib := norm_iteratedFDeriv_smul_le_of_isOpen hU hc (f := f y - f y₀)
      ((hf y).sub (hf y₀)) hx
      (k := k) (by exact_mod_cast le_top)
    refine (norm_sub_le_norm_sub_add_norm_sub _ (iteratedFDeriv 𝕜 k (g y₀) x) _).trans
      (add_le_add_left (hsub ▸ hleib.trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)) _)
    rw [iteratedFDeriv_sub_apply (hat (hf y) hx _) (hat (hf y₀) hx _)]
  have hsnd : Tendsto Prod.snd (𝓝[(univ : Set Y) ×ˢ U] (y₀, x₀)) (𝓝 x₀) :=
    continuous_snd.continuousWithinAt.tendsto
  -- Every term of the bound tends to zero.
  have hlim : Tendsto (fun p : Y × E ↦
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv 𝕜 i c p.2‖ *
          ‖iteratedFDeriv 𝕜 (k - i) (f p.1) p.2 - iteratedFDeriv 𝕜 (k - i) (f y₀) p.2‖) +
        ‖iteratedFDeriv 𝕜 k (g y₀) p.2 - iteratedFDeriv 𝕜 k (g y₀) x₀‖)
      (𝓝[(univ : Set Y) ×ˢ U] (y₀, x₀)) (𝓝 0) := by
    have hc' (i : ℕ) := ((hc x₀ hx₀).contDiffAt (hU.mem_nhds hx₀)).of_le
      (by exact_mod_cast le_top) |>.continuousAt_iteratedFDeriv (k := i) le_rfl
    simpa using (tendsto_finsetSum (Finset.range (k + 1)) fun i _ ↦
      ((tendsto_const_nhds (x := (k.choose i : ℝ))).mul ((hc' i).tendsto.comp hsnd).norm).mul
        (((hjets (k - i)) (y₀, x₀) ⟨mem_univ _, hx₀⟩).tendsto.sub
          (((hat (hf y₀) hx₀ (k - i)).continuousAt_iteratedFDeriv le_rfl).tendsto.comp
            hsnd)).norm).add
      ((((hat (hg y₀) hx₀ k).continuousAt_iteratedFDeriv le_rfl).tendsto.comp hsnd).sub
        (tendsto_const_nhds (x := iteratedFDeriv 𝕜 k (g y₀) x₀))).norm
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (eventually_mem_nhdsWithin.mono hbound) hlim

end ContinuousSpatialJets

end TauCeti
