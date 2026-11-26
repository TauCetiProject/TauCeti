/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet.Basic
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Holder.Leibniz
import TauCeti.Analysis.Holder.FaaDiBruno
import TauCeti.Analysis.Holder.IsBigO
import TauCeti.Analysis.Normed.Operator.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hölder regularity of local inverses

Inversion preserves local `C^{n,α}` regularity for every finite order `n` and `α ≤ 1`.
Operator families may take values in maps over a normed real algebra, for example complex-linear
maps differentiated over the reals. Invertibility is required only at the base point.

At positive order, the lower inverse jets are locally Lipschitz by ordinary `C^n` inverse calculus.
Two bilinear Leibniz estimates applied to `D(H⁻¹) = -H⁻¹ (DH) H⁻¹` control the top inverse jet.
For an open partial homeomorphism, the inverse function theorem and composition with its inverse
then give the Hölder bound for the inverse chart.

## Main results

* `ContDiffOn.exists_holderOnWith_iteratedFDeriv_clm_inverse`: inverse-family estimates on a ball.
* `ContDiffOn.exists_ckHolderSpaceOn_clm_inverse`: the inverse family in `CkHolderSpaceOn`.
* `OpenPartialHomeomorph.exists_holderOnWith_iteratedFDeriv_symm`: the inverse-chart estimate.
* `OpenPartialHomeomorph.exists_restr_holderOnWith_iteratedFDeriv_symm`: a restriction whose
  inverse is `C^{m+1,α}` on its whole target.
* `OpenPartialHomeomorph.exists_ckHolderSpaceOn_symm`: the inverse chart in `CkHolderSpaceOn`.
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace
open scoped NNReal Topology ContDiff

universe uP uV uW u𝕜 uE uF

/-- An invertible family that is `α`-Hölder with constant `C`, with inverse norms bounded by
`M`, has inverse `α`-Hölder constant `M * C * M`. No completeness is needed. -/
theorem HolderOnWith.clm_inverse_of_norm_le
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] {P : Type uP} [PseudoMetricSpace P]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    {H : P → V →L[𝕜] W} {s : Set P} {C α M : ℝ≥0}
    (hH : HolderOnWith C α H s) (hinv : ∀ x ∈ s, (H x).IsInvertible)
    (hb : ∀ x ∈ s, ‖(H x).inverse‖ ≤ M) :
    HolderOnWith (M * C * M) α (fun x ↦ (H x).inverse) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  rw [dist_eq_norm]
  have hd : ‖H y - H x‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [← dist_eq_norm, dist_comm y x] using hH.dist_le hy hx
  calc
    ‖(H x).inverse - (H y).inverse‖ ≤ ‖(H x).inverse‖ * ‖H y - H x‖ * ‖(H y).inverse‖ :=
      (hinv x hx).norm_inverse_sub_inverse_le (hinv y hy)
    _ ≤ (M : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ)) * M := by
      gcongr
      exacts [hb x hx, hb y hy]
    _ = (M * C * M : ℝ≥0) * dist x y ^ (α : ℝ) := by push_cast; ring

section OperatorFamily

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
  [IsScalarTower ℝ 𝕜 V] [CompleteSpace V]
  {W : Type uW} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
  [IsScalarTower ℝ 𝕜 W]


-- These curried composition maps put the inverse derivative formula in the bilinear form used
-- by the Hölder Leibniz estimate.
omit [CompleteSpace V] in
private def inverseDerivativeLeft :
    (P →L[ℝ] V →L[𝕜] W) →L[ℝ] (W →L[𝕜] V) →L[ℝ] P →L[ℝ] W →L[𝕜] W :=
  ((ContinuousLinearMap.compL 𝕜 W V W).bilinearRestrictScalars ℝ).precompL P

omit [CompleteSpace V] in
private def inverseDerivativeRight :
    (W →L[𝕜] V) →L[ℝ] (P →L[ℝ] W →L[𝕜] W) →L[ℝ] P →L[ℝ] W →L[𝕜] V :=
  ((ContinuousLinearMap.compL 𝕜 W W V).bilinearRestrictScalars ℝ).precompR P

private theorem fderiv_clm_inverse_precomp {H : P → V →L[𝕜] W} {x : P}
    (hH : DifferentiableAt ℝ H x) (hinv : (H x).IsInvertible) :
    fderiv ℝ (fun y ↦ (H y).inverse) x =
      -inverseDerivativeRight (P := P) (H x).inverse
        (inverseDerivativeLeft (fderiv ℝ H x) (H x).inverse) := by
  rw [(hH.hasFDerivAt.clm_inverse_of_completeSpace hinv).fderiv]
  ext v
  simp only [inverseDerivativeLeft, inverseDerivativeRight,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
    neg_apply, ContinuousLinearMap.flip_apply]

private theorem exists_ball_holder_fderiv_clm_inverse
    {H : P → V →L[𝕜] W} {s : Set P} {a : P} {k : ℕ} {α C D : ℝ≥0}
    (hs : IsOpen s) (ha : a ∈ s) (hα : α ≤ 1) (hH : ContDiffOn ℝ (k + 1) H s)
    (hinv : ∀ x ∈ s, (H x).IsInvertible)
    (hD : HolderOnWith C α (iteratedFDeriv ℝ k (fderiv ℝ H)) s)
    (hI : HolderOnWith D α (iteratedFDeriv ℝ k (fun x ↦ (H x).inverse)) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ k (fderiv ℝ (fun x ↦ (H x).inverse)))
        (ball a r) := by
  let B := inverseDerivativeLeft (𝕜 := 𝕜) (P := P) (V := V) (W := W)
  let A := inverseDerivativeRight (𝕜 := 𝕜) (P := P) (V := V) (W := W)
  let I : P → W →L[𝕜] V := fun x ↦ (H x).inverse
  let G := fun x ↦ B (fderiv ℝ H x) (I x)
  let Q := fun x ↦ A (I x) (G x)
  have hInv : ContDiffOn ℝ (k + 1) I s := hH.clm_inverse hinv
  have hInvk : ContDiffOn ℝ k I s := hInv.of_le (by simp)
  have hDH : ContDiffOn ℝ k (fderiv ℝ H) s := hH.fderiv_of_isOpen hs (by simp)
  -- Control `DH ∘ H⁻¹` first, then compose on the left by `H⁻¹`.
  obtain ⟨r, hr, hrs, hG, C₁, h₁⟩ :=
    ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂
      (P := P) (A := P →L[ℝ] V →L[𝕜] W) (B := W →L[𝕜] V)
      (G := P →L[ℝ] W →L[𝕜] W) B (hs.mem_nhds ha) hα hDH hInvk hD hI
  obtain ⟨t, ht, htr, _, C₂, h₂⟩ :=
    ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂
      (P := P) (A := W →L[𝕜] V) (B := P →L[ℝ] W →L[𝕜] W)
      (G := P →L[ℝ] W →L[𝕜] V) A (ball_mem_nhds a hr) hα
        (hInvk.mono hrs) hG (hI.mono hrs) h₁
  have hts := htr.trans hrs
  have heq (x : P) (hx : x ∈ s) : fderiv ℝ I x = -Q x := by
    exact fderiv_clm_inverse_precomp
      ((hH.differentiableOn (by simp) x hx).differentiableAt (hs.mem_nhds hx)) (hinv x hx)
  have hneg := isometry_neg.comp_holderOnWith h₂
  refine ⟨t, ht, hts, C₂, hneg.congr fun x hx ↦ ?_⟩
  have hx' := hts hx
  have hev : fderiv ℝ I =ᶠ[𝓝 x] -Q :=
    Filter.Eventually.mono (hs.mem_nhds hx') fun y hy ↦ heq y hy
  simpa only [Function.comp_apply, Pi.neg_apply] using
    ((hev.iteratedFDeriv ℝ k).eq_of_nhds.trans iteratedFDeriv_neg_apply).symm

private theorem exists_ball_holder_clm_inverse_on
    {H : P → V →L[𝕜] W} {s : Set P} {a : P} {n : ℕ} {α C : ℝ≥0}
    (hs : IsOpen s) (ha : a ∈ s) (hα : α ≤ 1) (hH : ContDiffOn ℝ n H s)
    (hinv : ∀ x ∈ s, (H x).IsInvertible)
    (hD : HolderOnWith C α (iteratedFDeriv ℝ n H) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ n (fun x ↦ (H x).inverse)) (ball a r) := by
  have hI := hH.clm_inverse hinv
  rcases n with _ | k
  · obtain ⟨r, hr, M, hb⟩ := (hI.contDiffAt (hs.mem_nhds ha)).exists_ball_bound_iteratedFDeriv
    obtain ⟨ρ, hρ, hρrs⟩ := Metric.eventually_nhds_iff_ball.mp
      (Filter.Eventually.and (ball_mem_nhds a hr) (hs.mem_nhds ha))
    have hρs : ball a ρ ⊆ s := fun x hx ↦ (hρrs x hx).2
    have hb' : ∀ x ∈ ball a ρ, ‖(H x).inverse‖ ≤ M.toNNReal := by
      intro x hx
      simpa using (hb 0 le_rfl x (hρrs x hx).1).trans
        (Real.le_coe_toNNReal M)
    have hD' := (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp hD).mono hρs
    exact ⟨ρ, hρ, hρs, _, TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mpr
      (hD'.clm_inverse_of_norm_le (fun x hx ↦ hinv x (hρs hx)) hb')⟩
  · have hLower : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k (fun x ↦ (H x).inverse)) a :=
      (hI.contDiffAt (hs.mem_nhds ha)).iteratedFDeriv_right (by simp [add_comm])
    obtain ⟨r, hr, D, hIr⟩ :=
      (hLower.isBigO_sub_dist_rpow one_ne_zero hα).exists_holderOnWith_ball
    obtain ⟨ρ, hρ, hρrs⟩ := Metric.eventually_nhds_iff_ball.mp
      (Filter.Eventually.and (ball_mem_nhds a hr) (hs.mem_nhds ha))
    have hρr : ball a ρ ⊆ ball a r := fun x hx ↦ (hρrs x hx).1
    have hρs : ball a ρ ⊆ s := fun x hx ↦ (hρrs x hx).2
    obtain ⟨u, hu, hus, K, hK⟩ := exists_ball_holder_fderiv_clm_inverse isOpen_ball
      (mem_ball_self hρ) hα (hH.mono hρs) (fun x hx ↦ hinv x (hρs hx))
      ((TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp hD).mono hρs) (hIr.mono hρr)
    exact ⟨u, hu, hus.trans hρs, K, TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mpr hK⟩

/-- Inversion preserves finite-order Hölder regularity near an invertible member of a family. -/
theorem ContDiffOn.exists_holderOnWith_iteratedFDeriv_clm_inverse
    {H : P → V →L[𝕜] W} {s : Set P} {a : P} {n : ℕ} {α C : ℝ≥0}
    (hH : ContDiffOn ℝ n H s) (hs : s ∈ 𝓝 a) (hα : α ≤ 1)
    (hD : HolderOnWith C α (iteratedFDeriv ℝ n H) s) (hinv : (H a).IsInvertible) :
    ∃ r > 0, ball a r ⊆ s ∧ (∀ x ∈ ball a r, (H x).IsInvertible) ∧
      ContDiffOn ℝ n (fun x ↦ (H x).inverse) (ball a r) ∧ ∃ K : ℝ≥0,
        HolderOnWith K α (iteratedFDeriv ℝ n (fun x ↦ (H x).inverse)) (ball a r) := by
  have hcont : ContinuousAt H a := (hH.contDiffAt hs).continuousAt
  have hev : ∀ᶠ x in 𝓝 a, x ∈ s ∧ (H x).IsInvertible :=
    Filter.Eventually.and hs (hcont.tendsto.eventually hinv.eventually_nhds)
  obtain ⟨t, ht, hgood⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hts : ball a t ⊆ s := fun x hx ↦ (hgood x hx).1
  have htinv : ∀ x ∈ ball a t, (H x).IsInvertible := fun x hx ↦ (hgood x hx).2
  obtain ⟨r, hr, hrt, K, hK⟩ := exists_ball_holder_clm_inverse_on isOpen_ball (mem_ball_self ht)
    hα (hH.mono hts) htinv (hD.mono hts)
  exact ⟨r, hr, hrt.trans hts, fun x hx ↦ htinv x (hrt hx),
    ((hH.mono hts).clm_inverse htinv).mono hrt, K, hK⟩

end OperatorFamily

/-- The inverse family lies in `CkHolderSpaceOn n α` on a ball about the base point, with
values `(H x).inverse`. -/
theorem ContDiffOn.exists_ckHolderSpaceOn_clm_inverse
    {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {V : Type uV} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedSpace ℝ V]
    [IsScalarTower ℝ 𝕜 V] [CompleteSpace V]
    {W : Type uW} [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedSpace ℝ W]
    [IsScalarTower ℝ 𝕜 W]
    {H : P → V →L[𝕜] W} {s : Set P} {a : P} {n : ℕ} {α C : ℝ≥0}
    (hH : ContDiffOn ℝ n H s) (hs : s ∈ 𝓝 a) (hα : α ≤ 1)
    (hD : HolderOnWith C α (iteratedFDeriv ℝ n H) s) (hinv : (H a).IsInvertible) :
    ∃ r > 0, ball a r ⊆ s ∧ (∀ x ∈ ball a r, (H x).IsInvertible) ∧
      ∃ g : TauCeti.CkHolderSpaceOn n α ⟨ball a r, isOpen_ball⟩ (W →L[𝕜] V),
        ∀ x, g x = (H x).inverse := by
  obtain ⟨r, hr, hrs, hInv, hC, K, hK⟩ :=
    hH.exists_holderOnWith_iteratedFDeriv_clm_inverse hs hα hD hinv
  obtain ⟨t, ht, htr, g, hg⟩ := hC.exists_ckHolderSpaceOn_ball (ball_mem_nhds _ hr) hα hK
  exact ⟨t, ht, htr.trans hrs, fun x hx ↦ hInv x (htr hx), g, hg⟩

/-- The actual inverse of a finite-order Hölder local diffeomorphism is locally Hölder of
that same order. -/
theorem OpenPartialHomeomorph.exists_holderOnWith_iteratedFDeriv_symm
    {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {m : ℕ} {α C : ℝ≥0} (e : OpenPartialHomeomorph E F) {a : E} (ha : a ∈ e.source)
    {s : Set E} (he : ContDiffOn ℝ (m + 1) e s) (hα : α ≤ 1) (hs : s ∈ 𝓝 a)
    (hH : HolderOnWith C α (iteratedFDeriv ℝ (m + 1) e) s)
    (hinv : (fderiv ℝ e a).IsInvertible) :
    ∃ r > 0, ball (e a) r ⊆ e.target ∧ ContDiffOn ℝ (m + 1) e.symm (ball (e a) r) ∧
      ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ (m + 1) e.symm) (ball (e a) r) := by
  let S := e.source ∩ interior s
  have hS : IsOpen S := e.open_source.inter isOpen_interior
  have haS : a ∈ S := ⟨ha, mem_interior_iff_mem_nhds.mpr hs⟩
  have heS : ContDiffOn ℝ (m + 1) e S := he.mono (inter_subset_right.trans interior_subset)
  have hDf : ContDiffOn ℝ m (fderiv ℝ e) S := heS.fderiv_of_isOpen hS (by simp)
  have hDH := (TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp hH).mono
    (inter_subset_right.trans interior_subset : S ⊆ s)
  obtain ⟨r, hr, hrs, hrinv, hFI, K, hK⟩ :=
    hDf.exists_holderOnWith_iteratedFDeriv_clm_inverse (hS.mem_nhds haS) hα hDH hinv
  let U := e.target ∩ e.symm ⁻¹' ball a r
  have hU : IsOpen U := e.isOpen_inter_preimage_symm isOpen_ball
  have haU : e a ∈ U := by
    refine ⟨e.map_source ha, ?_⟩
    simpa only [mem_preimage, e.left_inv ha] using (mem_ball_self hr : a ∈ ball a r)
  have hg : ContDiffOn ℝ (m + 1) e.symm U :=
    e.contDiffOn_symm_inter_preimage isOpen_ball ((heS.mono hrs).mono inter_subset_right)
      (fun x hx ↦ hrinv x hx.2)
  let H : E → F →L[ℝ] E := fun x ↦ (fderiv ℝ e x).inverse
  have hKw : HolderOnWith K α (iteratedFDerivWithin ℝ m H (ball a r)) (ball a r) :=
    hK.congr fun x hx ↦ (iteratedFDerivWithin_of_isOpen m isOpen_ball hx).symm
  obtain ⟨t, ht, N, hN⟩ := TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp
    hα (hU.mem_nhds haU) isOpen_ball.uniqueDiffOn hg hFI (fun _ hy ↦ hy.2)
    self_mem_nhdsWithin hKw
  obtain ⟨ρ, hρ, hρtU⟩ := Metric.eventually_nhds_iff_ball.mp
    (Filter.Eventually.and (ball_mem_nhds (e a) ht) (hU.mem_nhds haU))
  have hρt : ball (e a) ρ ⊆ ball (e a) t := fun y hy ↦ (hρtU y hy).1
  have hρU : ball (e a) ρ ⊆ U := fun y hy ↦ (hρtU y hy).2
  have heq (y : F) (hy : y ∈ U) : H (e.symm y) = fderiv ℝ e.symm y := by
    have hd := (heS.mono hrs).contDiffAt (isOpen_ball.mem_nhds hy.2)
    have hds := hg.contDiffAt (hU.mem_nhds hy)
    exact ((hrinv _ hy.2).eq_inverse_of_comp_eq_id_left
      (e.fderiv_symm_comp_fderiv hy.1 (hd.differentiableAt (by simp))
        (hds.differentiableAt (by simp)))).symm
  have htop : HolderOnWith N α (iteratedFDeriv ℝ m (fderiv ℝ e.symm)) (ball (e a) ρ) := by
    refine (hN.mono hρt).congr fun y hy ↦ ?_
    rw [iteratedFDerivWithin_of_isOpen m hU (hρU hy)]
    have hev : H ∘ e.symm =ᶠ[𝓝 y] fderiv ℝ e.symm :=
      Filter.Eventually.mono (hU.mem_nhds (hρU hy)) fun z hz ↦ heq z hz
    exact (hev.iteratedFDeriv ℝ m).eq_of_nhds
  exact ⟨ρ, hρ, fun y hy ↦ (hρU hy).1, hg.mono hρU, N,
    TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mpr htop⟩

/-- An open partial homeomorphism that is `C^{m+1}` on a neighbourhood `s` of `a`, with
`α`-Hölder `(m+1)`-th derivative there and invertible derivative at `a`, restricts around `a` to an
open partial homeomorphism with the same values whose inverse is `C^{m+1}` on its target, with
`α`-Hölder `(m+1)`-th derivative there. -/
theorem OpenPartialHomeomorph.exists_restr_holderOnWith_iteratedFDeriv_symm
    {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {m : ℕ} {α C : ℝ≥0} (e : OpenPartialHomeomorph E F) {a : E} (ha : a ∈ e.source)
    {s : Set E} (he : ContDiffOn ℝ (m + 1) e s) (hα : α ≤ 1) (hs : s ∈ 𝓝 a)
    (hH : HolderOnWith C α (iteratedFDeriv ℝ (m + 1) e) s)
    (hinv : (fderiv ℝ e a).IsInvertible) :
    ∃ e' : OpenPartialHomeomorph E F, ⇑e' = ⇑e ∧ a ∈ e'.source ∧ e'.source ⊆ e.source ∧
      ContDiffOn ℝ (m + 1) e'.symm e'.target ∧
      ∃ K : ℝ≥0, HolderOnWith K α (iteratedFDeriv ℝ (m + 1) e'.symm) e'.target := by
  obtain ⟨r, hr, -, hsymm, K, hK⟩ := e.exists_holderOnWith_iteratedFDeriv_symm ha he hα hs hH
    hinv
  set e' := e.restrOpen (e.source ∩ e ⁻¹' ball (e a) r) (e.isOpen_inter_preimage isOpen_ball)
  -- The target of `e'` lies in the ball, since `e'` maps its source there.
  have ht : e'.target ⊆ ball (e a) r := fun w hw ↦ by
    have h : e (e'.symm w) ∈ ball (e a) r := (e'.map_target hw).2.2
    rwa [show e (e'.symm w) = w from e'.right_inv hw] at h
  exact ⟨e', rfl, ⟨ha, ha, mem_ball_self hr⟩, fun z hz ↦ hz.1, hsymm.mono ht, K, hK.mono ht⟩

/-- The inverse chart lies in `CkHolderSpaceOn (m + 1) α` on a ball about the image point,
with values `e.symm x`. -/
theorem OpenPartialHomeomorph.exists_ckHolderSpaceOn_symm
    {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {m : ℕ} {α C : ℝ≥0} (e : OpenPartialHomeomorph E F) {a : E} (ha : a ∈ e.source)
    {s : Set E} (he : ContDiffOn ℝ (m + 1) e s) (hα : α ≤ 1) (hs : s ∈ 𝓝 a)
    (hH : HolderOnWith C α (iteratedFDeriv ℝ (m + 1) e) s)
    (hinv : (fderiv ℝ e a).IsInvertible) :
    ∃ r > 0, ball (e a) r ⊆ e.target ∧
      ∃ g : TauCeti.CkHolderSpaceOn (m + 1) α ⟨ball (e a) r, isOpen_ball⟩ E,
        ∀ x, g x = e.symm x := by
  obtain ⟨r, hr, hrt, hC, K, hK⟩ :=
    e.exists_holderOnWith_iteratedFDeriv_symm ha he hα hs hH hinv
  obtain ⟨t, ht, htr, g, hg⟩ := hC.exists_ckHolderSpaceOn_ball (ball_mem_nhds _ hr) hα hK
  exact ⟨t, ht, htr.trans hrt, g, hg⟩
