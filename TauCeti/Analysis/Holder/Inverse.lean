/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.OpenSet
public import TauCeti.Analysis.Calculus.InverseFunctionTheorem
import TauCeti.Analysis.Holder.Leibniz
import TauCeti.Analysis.Holder.FaaDiBruno
import TauCeti.Analysis.Holder.IsBigO
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
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
* `OpenPartialHomeomorph.exists_ckHolderSpaceOn_symm`: the inverse chart in `CkHolderSpaceOn`.
-/

public section

noncomputable section

open Set Filter Metric TopologicalSpace
open scoped NNReal Topology ContDiff

universe uP uV uW u𝕜 uE uF

private theorem exists_ball_jet_bounds_holder
    {P : Type uP} {V : Type uV} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : P → V} {s : Set P} {a : P}
    {n : ℕ} {α C : ℝ≥0} (hf : ContDiffOn ℝ n f s) (hs : IsOpen s) (ha : a ∈ s)
    (hα : α ≤ 1) (hH : HolderOnWith C α (iteratedFDeriv ℝ n f) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ M H : ℝ≥0,
      (∀ j ≤ n, ∀ x ∈ ball a r, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
      ∀ j ≤ n, HolderOnWith H α (iteratedFDeriv ℝ j f) (ball a r) := by
  obtain ⟨r, hr, A, hA⟩ := (hf.contDiffAt (hs.mem_nhds ha)).exists_ball_bound_iteratedFDeriv
  obtain ⟨t, ht, hts⟩ := Metric.isOpen_iff.mp hs a ha
  let ρ := min r t
  have hρ : 0 < ρ := lt_min hr ht
  have hrs : ball a ρ ⊆ s := (ball_subset_ball (min_le_right r t)).trans hts
  have hbound : ∀ j ≤ n, ∀ x ∈ ball a ρ, ‖iteratedFDeriv ℝ j f x‖ ≤ A.toNNReal := by
    intro j hj x hx
    exact (hA j hj x (ball_subset_ball (min_le_left r t) hx)).trans (Real.le_coe_toNNReal A)
  refine ⟨ρ, hρ, hrs, A.toNNReal, max C (3 * A.toNNReal), hbound, fun j hj ↦ ?_⟩
  rcases hj.lt_or_eq with hj | rfl
  · have h := (hf.mono hrs).holderOnWith_iteratedFDeriv_of_lt isOpen_ball (convex_ball a ρ)
      hj hα (hbound j hj.le) (hbound (j + 1) hj)
    apply h.mono_const
    calc A.toNNReal + 2 * A.toNNReal = 3 * A.toNNReal := by ring
         _ ≤ max C (3 * A.toNNReal) := le_max_right _ _
  · exact (hH.mono hrs).mono_const (le_max_left _ _)

private theorem exists_ball_holder_iteratedFDeriv_bilinear
    {P A B G : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {n : ℕ} {α C D : ℝ≥0} {f : P → A} {g : P → B}
    {s : Set P} {a : P} (hs : IsOpen s) (ha : a ∈ s) (hα : α ≤ 1)
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hfH : HolderOnWith C α (iteratedFDeriv ℝ n f) s)
    (hgH : HolderOnWith D α (iteratedFDeriv ℝ n g) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ K : ℝ≥0,
      HolderOnWith K α (iteratedFDeriv ℝ n (fun x ↦ L (f x) (g x))) (ball a r) := by
  obtain ⟨r, hr, hrs, M, H, hfb, hfH'⟩ := exists_ball_jet_bounds_holder hf hs ha hα hfH
  obtain ⟨t, ht, _, N, K, hgb, hgH'⟩ := exists_ball_jet_bounds_holder hg hs ha hα hgH
  let ρ := min r t
  have hρr : ball a ρ ⊆ ball a r := ball_subset_ball (min_le_left r t)
  have hρt : ball a ρ ⊆ ball a t := ball_subset_ball (min_le_right r t)
  have hρs := hρr.trans hrs
  exact ⟨ρ, lt_min hr ht, hρs, _, L.holderOnWith_iteratedFDeriv_comp₂
    (hf.mono hρs) (hg.mono hρs) isOpen_ball
    (fun j hj x hx ↦ hfb j hj x (hρr hx)) (fun j hj x hx ↦ hgb j hj x (hρt hx))
    (fun j hj ↦ (hfH' j hj).mono hρr) (fun j hj ↦ (hgH' j hj).mono hρt)⟩

private theorem exists_ball_holder_lower_jet
    {P : Type uP} {V : Type uV} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : P → V} {a : P} {n : ℕ} {α : ℝ≥0}
    (hf : ContDiffAt ℝ (n + 1) f a) (hα : α ≤ 1) :
    ∃ r > 0, ∃ C : ℝ≥0, HolderOnWith C α (iteratedFDeriv ℝ n f) (ball a r) := by
  have h : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) a :=
    hf.iteratedFDeriv_right (by simp [add_comm])
  exact (h.isBigO_sub_dist_rpow one_ne_zero hα).exists_holderOnWith_ball

private theorem exists_ball_holder_nested_bilinear
    {P A B G D : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup D] [NormedSpace ℝ D]
    (L₁ : A →L[ℝ] B →L[ℝ] G) (L₂ : B →L[ℝ] G →L[ℝ] D)
    {n : ℕ} {α C K : ℝ≥0} {f : P → A} {g : P → B} {s : Set P} {a : P}
    (hs : IsOpen s) (ha : a ∈ s) (hα : α ≤ 1)
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hfH : HolderOnWith C α (iteratedFDeriv ℝ n f) s)
    (hgH : HolderOnWith K α (iteratedFDeriv ℝ n g) s) :
    ∃ r > 0, ball a r ⊆ s ∧ ∃ N : ℝ≥0,
      HolderOnWith N α (iteratedFDeriv ℝ n (fun x ↦ L₂ (g x) (L₁ (f x) (g x))))
        (ball a r) := by
  have hG : ContDiffOn ℝ n (fun x ↦ L₁ (f x) (g x)) s :=
    L₁.isBoundedBilinearMap.contDiff.comp_contDiffOn (hf.prodMk hg)
  obtain ⟨r, hr, hrs, C₁, h₁⟩ := exists_ball_holder_iteratedFDeriv_bilinear L₁ hs ha hα
    hf hg hfH hgH
  obtain ⟨t, ht, htr, C₂, h₂⟩ := exists_ball_holder_iteratedFDeriv_bilinear L₂ isOpen_ball
    (mem_ball_self hr) hα (hg.mono hrs) (hG.mono hrs) (hgH.mono hrs) h₁
  exact ⟨t, ht, htr.trans hrs, C₂, h₂⟩

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
  rw [dist_eq_norm, (hinv x hx).inverse_sub_inverse (hinv y hy)]
  have hd : ‖H y - H x‖ ≤ (C : ℝ) * dist x y ^ (α : ℝ) := by
    simpa only [← dist_eq_norm, dist_comm y x] using hH.dist_le hy hx
  have hp := mul_le_mul hd (hb y hy) (norm_nonneg _) (by positivity :
    0 ≤ (C : ℝ) * dist x y ^ (α : ℝ))
  calc
    ‖(H x).inverse ∘L (H y - H x) ∘L (H y).inverse‖
        ≤ ‖(H x).inverse‖ * (‖H y - H x‖ * ‖(H y).inverse‖) :=
          (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (M : ℝ) * ((C : ℝ) * dist x y ^ (α : ℝ) * M) :=
      mul_le_mul (hb x hx) hp (mul_nonneg (norm_nonneg _) (norm_nonneg _)) M.coe_nonneg
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
  obtain ⟨t, ht, hts, C₂, h₂⟩ := exists_ball_holder_nested_bilinear
    (P := P) (A := P →L[ℝ] V →L[𝕜] W) (B := W →L[𝕜] V)
    (G := P →L[ℝ] W →L[𝕜] W) (D := P →L[ℝ] W →L[𝕜] V)
    B A (f := fderiv ℝ H) (g := I) hs ha hα hDH hInvk hD hI
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
    obtain ⟨t, ht, hts⟩ := Metric.isOpen_iff.mp hs a ha
    let ρ := min r t
    have hρs : ball a ρ ⊆ s := (ball_subset_ball (min_le_right r t)).trans hts
    have hb' : ∀ x ∈ ball a ρ, ‖(H x).inverse‖ ≤ M.toNNReal := by
      intro x hx
      simpa using (hb 0 le_rfl x (ball_subset_ball (min_le_left r t) hx)).trans
        (Real.le_coe_toNNReal M)
    have hD' := (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp hD).mono hρs
    exact ⟨ρ, lt_min hr ht, hρs, _, TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mpr
      (hD'.clm_inverse_of_norm_le (fun x hx ↦ hinv x (hρs hx)) hb')⟩
  · obtain ⟨r, hr, D, hIr⟩ := exists_ball_holder_lower_jet (hI.contDiffAt (hs.mem_nhds ha)) hα
    obtain ⟨t, ht, hts⟩ := Metric.isOpen_iff.mp hs a ha
    let ρ := min r t
    have hρr : ball a ρ ⊆ ball a r := ball_subset_ball (min_le_left r t)
    have hρs : ball a ρ ⊆ s := (ball_subset_ball (min_le_right r t)).trans hts
    obtain ⟨u, hu, hus, K, hK⟩ := exists_ball_holder_fderiv_clm_inverse isOpen_ball
      (mem_ball_self (lt_min hr ht)) hα (hH.mono hρs) (fun x hx ↦ hinv x (hρs hx))
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

private theorem exists_ckHolderSpaceOn_ball
    {P : Type uP} {V : Type uV} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {φ : P → V} {s : Set P} {a : P}
    {n : ℕ} {α C : ℝ≥0} (hf : ContDiffOn ℝ n φ s) (hs : IsOpen s) (ha : a ∈ s)
    (hα : α ≤ 1) (hH : HolderOnWith C α (iteratedFDeriv ℝ n φ) s) :
    ∃ r > 0, ball a r ⊆ s ∧
      ∃ g : TauCeti.CkHolderSpaceOn n α ⟨ball a r, isOpen_ball⟩ V,
        ∀ x, g x = φ x := by
  obtain ⟨ρ, hρ, hρs, M, _, hb, _⟩ := exists_ball_jet_bounds_holder hf hs ha hα hH
  let Ω : Opens P := ⟨ball a ρ, isOpen_ball⟩
  have hbound : ∀ j ≤ n, ∃ A, ∀ x : Ω, ‖iteratedFDeriv ℝ j φ x‖ ≤ A :=
    fun j hj ↦ ⟨(M : ℝ), fun x ↦ hb j hj x x.property⟩
  have hholder : MemHolder α (fun x : Ω ↦ iteratedFDeriv ℝ n φ x) :=
    ⟨C, fun x y ↦ hH x (hρs x.property) y (hρs y.property)⟩
  exact ⟨ρ, hρ, hρs, TauCeti.CkHolderSpaceOn.ofContDiffOn φ (hf.mono hρs) hbound hholder,
    fun x ↦ TauCeti.CkHolderSpaceOn.ofContDiffOn_apply φ (hf.mono hρs) hbound hholder x⟩

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
  obtain ⟨t, ht, htr, g, hg⟩ := exists_ckHolderSpaceOn_ball hC isOpen_ball (mem_ball_self hr) hα hK
  exact ⟨t, ht, htr.trans hrs, fun x hx ↦ hInv x (htr hx), g, hg⟩

private theorem contDiffOn_symm_on_preimage
    {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace E]
    {m : ℕ} (e : OpenPartialHomeomorph E F) {s : Set E}
    (he : ContDiffOn ℝ (m + 1) e s) (hs : IsOpen s)
    (hinv : ∀ x ∈ s, (fderiv ℝ e x).IsInvertible) :
    ContDiffOn ℝ (m + 1) e.symm (e.target ∩ e.symm ⁻¹' s) := by
  intro y hy
  have hc := he.contDiffAt (hs.mem_nhds hy.2)
  obtain ⟨L, hL⟩ := hinv (e.symm y) hy.2
  refine (e.contDiffAt_symm hy.1 (f₀' := L) ?_ hc).contDiffWithinAt
  simpa only [hL] using (hc.differentiableAt (by simp)).hasFDerivAt

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
    contDiffOn_symm_on_preimage e (heS.mono hrs) isOpen_ball hrinv
  let H : E → F →L[ℝ] E := fun x ↦ (fderiv ℝ e x).inverse
  have hKw : HolderOnWith K α (iteratedFDerivWithin ℝ m H (ball a r)) (ball a r) :=
    hK.congr fun x hx ↦ (iteratedFDerivWithin_of_isOpen m isOpen_ball hx).symm
  obtain ⟨t, ht, N, hN⟩ := TauCeti.exists_holderOnWith_iteratedFDerivWithin_comp
    hα (hU.mem_nhds haU) isOpen_ball.uniqueDiffOn hg hFI (fun _ hy ↦ hy.2)
    self_mem_nhdsWithin hKw
  obtain ⟨u, hu, huU⟩ := Metric.isOpen_iff.mp hU (e a) haU
  let ρ := min t u
  have hρt : ball (e a) ρ ⊆ ball (e a) t := ball_subset_ball (min_le_left t u)
  have hρU : ball (e a) ρ ⊆ U := (ball_subset_ball (min_le_right t u)).trans huU
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
  exact ⟨ρ, lt_min ht hu, fun y hy ↦ (hρU hy).1, hg.mono hρU, N,
    TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mpr htop⟩

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
  obtain ⟨t, ht, htr, g, hg⟩ := exists_ckHolderSpaceOn_ball hC isOpen_ball (mem_ball_self hr) hα hK
  exact ⟨t, ht, htr.trans hrt, g, hg⟩
