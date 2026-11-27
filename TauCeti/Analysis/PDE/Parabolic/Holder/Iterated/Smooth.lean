/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CauchyProblem
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.CompLeft
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.OfDeriv
public import TauCeti.Analysis.PDE.Parabolic.Holder.Iterated.LowOrder
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Prod
import TauCeti.Analysis.Holder.Iterated
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Holder

/-!
# Smooth maps with bounded derivatives in the parabolic Hölder spaces

Let `f : E × ℝ → F` be a map on ordinary space-time of class `C^{k+1}` whose derivatives of
orders `0, …, k + 1` are bounded. This file proves that the restriction of `f` to every closed
slab `E × [a, b]` lies in the bounded parabolic Hölder space `C_{par,b}^{k+α}`, for every `α ≤ 1`
(`TauCeti.ParabolicCkHolderSpace.exists_coe_eq_of_contDiff`). A field `D_t^r D_x^m f` of parabolic
order `2 r + m ≤ k` involves only `r + m ≤ k` ordinary derivatives, and one more bounded
derivative makes it Lipschitz, hence Hölder for the parabolic distance and in time.

As a consequence, data with bounded derivatives give regular solutions of the parabolic Cauchy
problem. On `ℝⁿ × [0, T]` let `P u = ∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u` have coefficients in
`C_b^{α,α/2}`, `0 < α < 1`, with `a` uniformly elliptic, and let `u` be the solution in
`C_b^{2+α,1+α/2}` of `P u = f`, `u(·, 0) = g`. If the coefficients and the forcing are
restrictions of maps of class `C^{k+1}` on `ℝⁿ × ℝ`, and the initial datum is of class `C^{k+3}`
on `ℝⁿ`, all with bounded derivatives through these orders, then `u` lies in `C_{par,b}^{k+2+α}`
(`TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply_of_contDiff`).
The initial datum lies in `C_b^{k+2,α}` by `TauCeti.CkHolderSpace.exists_coe_eq_of_contDiff`, and
the higher regularity theorem
`TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply` applies. In
particular, smooth coefficients, forcing and initial datum with bounded derivatives of every order
give a solution in every finite-order space `C_{par,b}^{k+2+α}`.

## Main declarations

* `TauCeti.ParabolicCkHolderSpace.exists_coe_eq_of_contDiff`: a `C^{k+1}` map on `E × ℝ` with
  bounded derivatives through order `k + 1` restricts to an element of `C_{par,b}^{k+α}` on every
  slab.
* `TauCeti.ParabolicC2HolderSpace.exists_coe_eq_euclideanInitialDataCLE_symm_apply_of_contDiff`:
  the solution of the Cauchy problem with such data lies in `C_{par,b}^{k+2+α}`.

## The argument

The proof is by induction on `k` in steps of two, for all maps with values in the spaces of
continuous multilinear maps `E [×m]→L[ℝ] F` at once, since differentiating in space adds one
argument. At orders `0` and `1` the fields are built directly: a map with bounded first
derivative is Lipschitz, hence parabolically `α`-Hölder
(`TauCeti.ParabolicSpaceTime.exists_holderWith_comp_coords`) and `(1 + α) / 2`-Hölder in time
(`TauCeti.holderWith_of_norm_le_of_norm_fderiv_le`). For the step from `k` to `k + 2`, the
spatial derivative `D_x f` and the time derivative `∂ₜf` are again bounded maps with bounded
derivatives, of one order less. By induction they lie in `C_{par,b}^{(k+1)+α}` and
`C_{par,b}^{k+α}`, and a map whose spatial and time derivatives lie there lies in
`C_{par,b}^{(k+2)+α}` (`TauCeti.ParabolicCkHolderSpace.ofSpatialFDerivTimeDeriv`).

## References

* A. Lunardi, *Linear and nonlinear diffusion problems*, Cortona lecture notes, 2004, Chapter 3.
* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996,
  Chapter 8.
-/

public section
noncomputable section

namespace TauCeti

open Set ParabolicSpaceTime
open scoped NNReal BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ}

namespace ParabolicCkHolderSpace

variable {α : ℝ≥0} {hab : a < b}

/-! ### Derivative fields of maps with bounded derivatives -/

/-- The restriction to a slab of a continuous map on `E × ℝ` bounded by `M`, as a bounded continuous
map. -/
private def restrictSlab {V : Type*} [NormedAddCommGroup V] (f : E × ℝ → V) (hf : Continuous f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) : slab (E := E) a b →ᵇ V :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p ↦ f ((p : ParabolicSpaceTime E).space, (p : ParabolicSpaceTime E).time))
    (hf.comp (by fun_prop)) M fun _ ↦ hM _

omit [NormedSpace ℝ E] in
private theorem restrictSlab_apply {V : Type*} [NormedAddCommGroup V] {f : E × ℝ → V}
    (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (p : slab (E := E) a b) :
    restrictSlab f hf hM p =
      f ((p : ParabolicSpaceTime E).space, (p : ParabolicSpaceTime E).time) :=
  (rfl)

/-- A `C¹` map on `E × ℝ` with bounded value and derivative restricts to every slab as an
element of the parabolic Hölder space `C_b^{α,α/2}`, for `α ≤ 1`. -/
private theorem exists_holderSpace_coe_eq_of_contDiff {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (hα : α ≤ 1) {f : E × ℝ → V} (hf : ContDiff ℝ 1 f)
    (hbdd : ∀ i ≤ 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ C) :
    ∃ g : HolderSpace α (slab (E := E) a b) V,
      ⇑g = fun p : slab (E := E) a b ↦
        f ((p : ParabolicSpaceTime E).space, (p : ParabolicSpaceTime E).time) := by
  obtain ⟨M, hM⟩ := hbdd 0 zero_le_one
  obtain ⟨K, hK⟩ := hbdd 1 le_rfl
  simp only [norm_iteratedFDeriv_zero] at hM
  simp only [norm_iteratedFDeriv_one] at hK
  have hL : LipschitzWith K.toNNReal f :=
    lipschitzWith_of_nnNorm_fderiv_le (hf.differentiable one_ne_zero) fun z ↦ by
      rw [← NNReal.coe_le_coe, coe_nnNorm]
      exact (hK z).trans (Real.le_coe_toNNReal K)
  obtain ⟨C, hC⟩ := exists_holderWith_comp_coords hα hL hM
  have hH : HolderWith C α (restrictSlab (a := a) (b := b) f hf.continuous hM) := fun p q ↦ by
    have h := hC 0 p q
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero] at h
    rwa [restrictSlab_apply, restrictSlab_apply, Subtype.edist_eq]
  exact ⟨HolderSpace.ofBoundedContinuousFunction _ hH.memHolder,
    funext (HolderSpace.ofBoundedContinuousFunction_apply _ _)⟩

variable (α hab E F) in
/-- The statement proved by induction on the order `k`, for maps with values in the spaces of
continuous multilinear maps `E [×m]→L[ℝ] F` for all `m` at once. -/
private def ContDiffMotive (k : ℕ) : Prop :=
  ∀ (m : ℕ) (f : E × ℝ → E [×m]→L[ℝ] F), ContDiff ℝ (k + 1 : ℕ) f →
    (∀ i ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ C) →
    ∃ u : ParabolicCkHolderSpace k α E (E [×m]→L[ℝ] F) hab,
      ⇑u = fun p : slab (E := E) a b ↦
        f ((p : ParabolicSpaceTime E).space, (p : ParabolicSpaceTime E).time)

private theorem contDiffMotive_zero (hα : α ≤ 1) : ContDiffMotive E F α hab 0 :=
  fun _ _ hf hbdd ↦ by
  obtain ⟨g, hg⟩ := exists_holderSpace_coe_eq_of_contDiff hα (by exact_mod_cast hf) hbdd
  exact ⟨equivHolderSpace.symm g, by rw [coe_equivHolderSpace_symm, hg]⟩

private theorem contDiffMotive_one (hα : α ≤ 1) : ContDiffMotive E F α hab 1 :=
  fun m f hf hbdd ↦ by
  let R : (E × ℝ →L[ℝ] E [×m]→L[ℝ] F) →L[ℝ] E →L[ℝ] E [×m]→L[ℝ] F :=
    (ContinuousLinearMap.inl ℝ E ℝ).precomp _
  obtain ⟨hfx, hbfx⟩ :=
    hf.continuousLinearMap_comp_fderiv_and_exists_bound_iteratedFDeriv (n := 1)
      (G := E →L[ℝ] E [×m]→L[ℝ] F) hbdd R
  obtain ⟨ux, hux⟩ :=
    exists_holderSpace_coe_eq_of_contDiff (a := a) (b := b) hα (by exact_mod_cast hfx) hbfx
  obtain ⟨M, hM⟩ := hbdd 0 (by omega)
  simp only [norm_iteratedFDeriv_zero] at hM
  obtain ⟨K, hK⟩ := hbdd 1 (by omega)
  simp only [norm_iteratedFDeriv_one] at hK
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  -- `f` is `(1 + α) / 2`-Hölder, hence so is each time slice `t ↦ f (x, t)`.
  have hγ : (1 + α) / 2 ≤ 1 := by
    rw [div_le_one (by norm_num)]
    calc 1 + α ≤ 1 + 1 := by gcongr
      _ = 2 := one_add_one_eq_two
  have hfH := holderWith_of_norm_le_of_norm_fderiv_le hγ (hf1.differentiable one_ne_zero)
    (fun z ↦ (hM z).trans (Real.le_coe_toNNReal M))
    (fun z ↦ (hK z).trans (Real.le_coe_toNNReal K))
  have hC (x : E) := hfH.comp_lipschitzWith_one (f := fun t : Icc a b ↦ (x, (t : ℝ)))
    (by
      have h := (LipschitzWith.prodMk_left x).comp (LipschitzWith.subtypeVal (Icc a b))
      rw [mul_one] at h
      exact h)
  let u := restrictSlab (a := a) (b := b) f hf.continuous hM
  have hx (t : Icc a b) (x : E) : HasFDerivAt (fun y ↦ u (slabMk y t)) (ux (slabMk x t)) x := by
    simp only [u, restrictSlab_apply, hux, space_slabMk, time_slabMk]
    exact (hf1.differentiable one_ne_zero (x, (t : ℝ))).hasFDerivAt_slice_fst
  have ht : timeEHolderNorm ((1 + α) / 2) (u : slab (E := E) a b → E [×m]→L[ℝ] F) < ⊤ :=
    (timeEHolderNorm_le_iff.2 fun x t s ↦ by
      simpa only [u, restrictSlab_apply, space_slabMk, time_slabMk, Function.comp_apply] using
        hC x t s).trans_lt
      ENNReal.coe_lt_top
  exact ⟨equivParabolicC1HolderSpace.symm (ParabolicC1HolderSpace.mk u ux hx ht), by
    rw [coe_equivParabolicC1HolderSpace_symm]
    exact funext (ParabolicC1HolderSpace.mk_apply u ux hx ht)⟩

private theorem contDiffMotive_add_two {k : ℕ} (hk : ContDiffMotive E F α hab k)
    (hk₁ : ContDiffMotive E F α hab (k + 1)) : ContDiffMotive E F α hab (k + 2) :=
  fun m f hf hbdd ↦ by
  -- The spatial derivative, with its first argument joined to the others.
  let e : (E [×(m + 1)]→L[ℝ] F) ≃L[ℝ] E →L[ℝ] E [×m]→L[ℝ] F :=
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).toContinuousLinearEquiv
  let R : (E × ℝ →L[ℝ] E [×m]→L[ℝ] F) →L[ℝ] E →L[ℝ] E [×m]→L[ℝ] F :=
    (ContinuousLinearMap.inl ℝ E ℝ).precomp _
  obtain ⟨hfx, hbfx⟩ :=
    hf.continuousLinearMap_comp_fderiv_and_exists_bound_iteratedFDeriv (n := k + 2)
      (G := E [×(m + 1)]→L[ℝ] F) hbdd
      ((e.symm : (E →L[ℝ] E [×m]→L[ℝ] F) →L[ℝ] E [×(m + 1)]→L[ℝ] F).comp R)
  obtain ⟨Gm, hGm⟩ := hk₁ (m + 1) _ hfx hbfx
  let G : ParabolicCkHolderSpace (k + 1) α E (E →L[ℝ] E [×m]→L[ℝ] F) hab :=
    compLeftL (e : _ →L[ℝ] _) Gm
  -- The time derivative.
  obtain ⟨hft, hbft⟩ :=
    hf.continuousLinearMap_comp_fderiv_and_exists_bound_iteratedFDeriv (n := k + 2)
      (G := E [×m]→L[ℝ] F) hbdd
      (ContinuousLinearMap.apply ℝ _ ((0, 1) : E × ℝ) :
        (E × ℝ →L[ℝ] E [×m]→L[ℝ] F) →L[ℝ] E [×m]→L[ℝ] F)
  obtain ⟨H, hH⟩ := hk m _ (hft.of_le (by norm_cast; omega))
    fun i hi ↦ hbft i (by omega)
  obtain ⟨M, hM⟩ := hbdd 0 (by omega)
  simp only [norm_iteratedFDeriv_zero] at hM
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_cast; omega)
  let u := restrictSlab (a := a) (b := b) f hf.continuous hM
  have hG (t : Icc a b) (x : E) : HasFDerivAt (fun y ↦ u (slabMk y t)) (G (slabMk x t)) x := by
    simp only [u, G, R, restrictSlab_apply, compLeftL_apply, hGm, space_slabMk, time_slabMk,
      Function.comp_apply, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.precomp_apply]
    exact (hf1.differentiable one_ne_zero (x, (t : ℝ))).hasFDerivAt_slice_fst
  have hHd (x : E) (t : Icc a b) : HasDerivWithinAt
      (ParabolicC2HolderSpace.timeExtension hab.le u x) (H (slabMk x t)) (Icc a b) t := by
    have hd : HasDerivAt (fun s : ℝ ↦ f (x, s)) (fderiv ℝ f (x, (t : ℝ)) (0, 1)) t := by
      simpa using
        ((hf1.differentiable one_ne_zero (x, (t : ℝ))).hasFDerivAt_slice_snd).hasDerivAt
    rw [hH]
    simp only [Function.comp_apply, space_slabMk, time_slabMk, ContinuousLinearMap.apply_apply]
    refine hd.hasDerivWithinAt.congr_of_mem (fun s hs ↦ ?_) t.property
    rw [ParabolicC2HolderSpace.timeExtension_def]
    dsimp only
    rw [projIcc_of_mem hab.le hs]
    simp only [u, restrictSlab_apply, space_slabMk, time_slabMk]
  exact ⟨ofSpatialFDerivTimeDeriv u G H hG hHd,
    funext fun p ↦ by rw [ofSpatialFDerivTimeDeriv_apply, restrictSlab_apply]⟩

/-- **Smooth maps with bounded derivatives are parabolically Hölder of every order.** Let
`f : E × ℝ → F` be of class `C^{k+1}` with bounded derivatives of orders `0, …, k + 1`. Then for
`α ≤ 1` its restriction to every closed slab `E × [a, b]` lies in the bounded parabolic Hölder
space `C_{par,b}^{k+α}`. -/
theorem exists_coe_eq_of_contDiff (hα : α ≤ 1) (k : ℕ) {f : E × ℝ → F}
    (hf : ContDiff ℝ (k + 1 : ℕ) f) (hbdd : ∀ i ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ C) :
    ∃ u : ParabolicCkHolderSpace k α E F hab,
      ⇑u = fun p : slab (E := E) a b ↦
        f ((p : ParabolicSpaceTime E).space, (p : ParabolicSpaceTime E).time) := by
  have hmot : ContDiffMotive E F α hab k :=
    Nat.twoStepInduction (contDiffMotive_zero hα) (contDiffMotive_one hα)
      (fun _ h h₁ ↦ contDiffMotive_add_two h h₁) k
  -- Values in `F` are read as `0`-multilinear maps.
  let e : (E [×0]→L[ℝ] F) ≃ₗᵢ[ℝ] F := continuousMultilinearCurryFin0 ℝ E F
  obtain ⟨u, hu⟩ := hmot 0 (e.symm ∘ f)
    ((e.symm.toContinuousLinearEquiv : F →L[ℝ] E [×0]→L[ℝ] F).contDiff.comp hf) fun i hi ↦ by
      obtain ⟨C, hC⟩ := hbdd i hi
      refine ⟨C, fun z ↦ ?_⟩
      rw [e.symm.norm_iteratedFDeriv_comp_left]
      exact hC z
  refine ⟨compLeftL (e.toContinuousLinearEquiv : (E [×0]→L[ℝ] F) →L[ℝ] F) u, ?_⟩
  rw [coe_compLeftL, hu]
  ext p
  simp

end ParabolicCkHolderSpace

namespace ParabolicC2HolderSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℝ≥0} {hT : (0 : ℝ) < T} {α : ℝ≥0}
  {a : ι → ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {b : ι → HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {c : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
  {ha : ∃ lam : ℝ, 0 < lam ∧ ∀ p (ξ : EuclideanSpace ℝ ι),
    lam * ‖ξ‖ ^ 2 ≤ (Matrix.of fun i j ↦ a i j p).toQuadraticForm' ξ}

/-- **Data with bounded derivatives give solutions of every finite order.** Let `0 < α < 1`, let
`aⁱʲ`, `bⁱ`, `c` be coefficients in `C_b^{α,α/2}(ℝⁿ × [0, T])` with `a` uniformly elliptic, and
let `u` be the solution in `C_b^{2+α,1+α/2}` of `∂ₜu - aⁱʲ ∂ᵢ∂ⱼu - bⁱ ∂ᵢu - c u = f`,
`u(·, 0) = g`. If the coefficients and the forcing are restrictions to the slab of `C^{k+1}` maps
on `ℝⁿ × ℝ` with bounded derivatives through order `k + 1`, and the initial datum is a `C^{k+3}`
map with bounded derivatives through order `k + 3`, then `u` lies in `C_{par,b}^{k+2+α}`.
Smooth data with bounded derivatives of every order satisfy these hypotheses for every `k`, so
their solution lies in every space `C_{par,b}^{k+2+α}`. -/
theorem exists_coe_eq_euclideanInitialDataCLE_symm_apply_of_contDiff (hα₀ : 0 < α)
    (hα₁ : α < 1) (k : ℕ)
    (hak : ∀ i j, ∃ A : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ (k + 1 : ℕ) A ∧
      (∀ n ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n A z‖ ≤ C) ∧
      ∀ p, a i j p = A (p.val.space, p.val.time))
    (hbk : ∀ i, ∃ B : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ (k + 1 : ℕ) B ∧
      (∀ n ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n B z‖ ≤ C) ∧
      ∀ p, b i p = B (p.val.space, p.val.time))
    (hck : ∃ C₀ : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ (k + 1 : ℕ) C₀ ∧
      (∀ n ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n C₀ z‖ ≤ C) ∧
      ∀ p, c p = C₀ (p.val.space, p.val.time))
    {f : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
    (hfk : ∃ F₀ : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ (k + 1 : ℕ) F₀ ∧
      (∀ n ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n F₀ z‖ ≤ C) ∧
      ∀ p, f p = F₀ (p.val.space, p.val.time))
    {g : CkHolderSpace 2 α (EuclideanSpace ℝ ι) ℝ}
    (hgk : ∃ G₀ : EuclideanSpace ℝ ι → ℝ, ContDiff ℝ (k + 3 : ℕ) G₀ ∧
      (∀ n ≤ k + 3, ∃ C, ∀ x, ‖iteratedFDeriv ℝ n G₀ x‖ ≤ C) ∧ ⇑g = G₀) :
    ∃ U : ParabolicCkHolderSpace (k + 2) α (EuclideanSpace ℝ ι) ℝ hT,
      ⇑U = ⇑((euclideanInitialDataCLE hα₀ hα₁ hT a b c ha).symm (f, g)) := by
  -- Each restriction of a map with bounded derivatives lies in `C_{par,b}^{k+α}`.
  have hpar {v : HolderSpace α (slab (E := EuclideanSpace ℝ ι) 0 T) ℝ}
      (hv : ∃ V : EuclideanSpace ℝ ι × ℝ → ℝ, ContDiff ℝ (k + 1 : ℕ) V ∧
        (∀ n ≤ k + 1, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n V z‖ ≤ C) ∧
        ∀ p, v p = V (p.val.space, p.val.time)) :
      ∃ W : ParabolicCkHolderSpace k α (EuclideanSpace ℝ ι) ℝ hT, ⇑W = ⇑v := by
    obtain ⟨V, hV, hVb, hvV⟩ := hv
    obtain ⟨W, hW⟩ := ParabolicCkHolderSpace.exists_coe_eq_of_contDiff hα₁.le k hV hVb
    exact ⟨W, hW.trans (funext fun p ↦ (hvV p).symm)⟩
  obtain ⟨G₀, hG₀, hG₀b, hgG₀⟩ := hgk
  obtain ⟨G, hG⟩ := CkHolderSpace.exists_coe_eq_of_contDiff hα₁.le (k + 2) hG₀ hG₀b
  exact exists_coe_eq_euclideanInitialDataCLE_symm_apply hα₀ hα₁ k (fun i j ↦ hpar (hak i j))
    (fun i ↦ hpar (hbk i)) (hpar hck) (hpar hfk) ⟨G, hG.trans hgG₀.symm⟩

end ParabolicC2HolderSpace

end TauCeti
