/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Holder.JetBounds
public import TauCeti.Analysis.Normed.Operator.Holder
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Higher Hölder bounds for bilinear products

Leibniz differentiation preserves Hölder bounds at every finite order. If all derivative fields
of two maps up to order `k` are bounded and `α`-Hölder on an open set `s`, then the `k`-th
derivative of their pointwise bilinear product is `α`-Hölder on `s`, with constant
`2 ^ k ‖L‖ (M K + N H)` (`ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂`). Only local
bounds on the first factor are needed for a global bound when the second factor has topological
support inside that open set
(`ContinuousLinearMap.holderWith_iteratedFDeriv_of_tsupport_subset_right`).

For two local `C^{n,α}` maps, `ContinuousLinearMap.exists_holderOnWith_iteratedFDeriv_comp₂`
gives a common positive ball on which their bilinear product is `C^n` and its top derivative is
`α`-Hölder, deriving the required lower-jet bounds locally.
-/

public section

open Set Metric Filter
open scoped NNReal Topology

namespace ContinuousLinearMap

/-- The order-zero case of `holderWith_iteratedFDeriv_bilinear_aux`: a bilinear product whose
second factor is supported inside `s` is Hölder with constant `‖L‖ * (M * K + N * H)`. -/
private theorem holderWith_iteratedFDeriv_zero_bilinear {E A B G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {f : E → A} {g : E → B} {s : Set E} {M N H K α : ℝ≥0}
    (hgs : tsupport g ⊆ s)
    (hfb : ∀ x ∈ s, ‖iteratedFDeriv ℝ 0 f x‖ ≤ M) (hgb : ∀ x, ‖iteratedFDeriv ℝ 0 g x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ 0 f) s)
    (hgH : HolderWith K α (iteratedFDeriv ℝ 0 g)) :
    HolderWith (‖L‖₊ * (M * K + N * H)) α (iteratedFDeriv ℝ 0 (fun x => L (f x) (g x))) := by
  apply holderOnWith_univ.mp
  rw [TauCeti.holderOnWith_iteratedFDeriv_zero_iff]
  apply holderOnWith_univ.mpr
  simpa using L.holderWith_comp₂_of_eq_zero
    (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp hfH)
    (holderOnWith_univ.mp (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp
      (hgH.holderOnWith univ)))
    (by simpa only [norm_iteratedFDeriv_zero] using hfb)
    (by simpa only [norm_iteratedFDeriv_zero] using fun x _ => hgb x)
    (fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hgs h))

private theorem holderWith_iteratedFDeriv_bilinear_aux {E A B G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (L : A →L[ℝ] B →L[ℝ] G) {f : E → A} {g : E → B} {s : Set E}
    {M N H K α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hg : ContDiff ℝ k g) (hs : IsOpen s)
    (hgs : tsupport g ⊆ s)
    (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hgb : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ N)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s)
    (hgH : ∀ j ≤ k, HolderWith K α (iteratedFDeriv ℝ j g)) :
    HolderWith ((2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) := by
  induction k generalizing A B G with
  | zero =>
    simpa using holderWith_iteratedFDeriv_zero_bilinear L hgs (hfb 0 le_rfl) (hgb 0 le_rfl)
      (hfH 0 le_rfl) (hgH 0 le_rfl)
  | succ k ih =>
    have hf' : ContDiffOn ℝ k (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
    have hg' : ContDiff ℝ k (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hf₀ : ContDiffOn ℝ k f s := hf.of_le (by simp)
    have hg₀ : ContDiff ℝ k g := hg.of_le (by simp)
    have hgb' : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fderiv ℝ g) x‖ ≤ N := by
      intro j hj x
      rw [norm_iteratedFDeriv_fderiv]
      exact hgb (j + 1) (by omega) x
    have hfb' : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ ≤ M := by
      intro j hj x hx
      rw [norm_iteratedFDeriv_fderiv]
      exact hfb (j + 1) (by omega) x hx
    have hfH' : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j (fderiv ℝ f)) s :=
      fun j hj => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hfH (j + 1) (by omega))
    have hgH' : ∀ j ≤ k, HolderWith K α (iteratedFDeriv ℝ j (fderiv ℝ g)) := by
      intro j hj
      exact holderOnWith_univ.mp (TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp
        ((hgH (j + 1) (by omega)).holderOnWith univ))
    have hR := ih (L.precompR E) hf₀ hg' ((tsupport_fderiv_subset ℝ).trans hgs)
      (fun j hj => hfb j (by omega)) hgb' (fun j hj => hfH j (by omega)) hgH'
    have hL := ih (L.precompL E) hf' hg₀ hgs hfb'
      (fun j hj => hgb j (by omega)) hfH' (fun j hj => hgH j (by omega))
    have hRdiff := (L.precompR E).contDiff_of_tsupport_subset_right hf₀ hg'.contDiffOn hs
      ((tsupport_fderiv_subset ℝ).trans hgs)
    have hLdiff := (L.precompL E).contDiff_of_tsupport_subset_right hf' hg₀.contDiffOn hs hgs
    have hd : fderiv ℝ (fun x => L (f x) (g x)) =
        (fun x => L.precompR E (f x) (fderiv ℝ g x)) +
          (fun x => L.precompL E (fderiv ℝ f x) (g x)) := by
      funext x
      exact L.fderiv_of_tsupport_subset_right (hf.differentiableOn (by simp))
        (hg.differentiable (by simp)) hs hgs x
    apply holderOnWith_univ.mp
    rw [TauCeti.holderOnWith_iteratedFDeriv_succ_iff, hd,
      iteratedFDeriv_add hRdiff hLdiff]
    apply holderOnWith_univ.mpr
    apply (hR.add hL).mono
    calc
      _ ≤ (2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H) +
          (2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H) := by
        gcongr
        · exact_mod_cast L.norm_precompR_le E
        · exact_mod_cast L.norm_precompL_le E
      _ = _ := by ring

/-- Composing a factor with linear isometry equivalences on both sides transfers smoothness on `s`,
bounds on the derivative fields through order `k` and their Hölder bounds on `s` to the preimage
of `s`. This is the per-factor step of the universe reduction for Leibniz Hölder bounds. -/
private theorem contDiffOn_bounds_comp_linearIsometryEquiv
    {E E' A A' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup A']
    [NormedSpace ℝ A'] (e : E' ≃ₗᵢ[ℝ] E) (a : A' ≃ₗᵢ[ℝ] A) {k : ℕ} {f : E → A} {s : Set E}
    {M H α : ℝ≥0} (hf : ContDiffOn ℝ k f s)
    (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s) :
    ContDiffOn ℝ k (a.symm ∘ f ∘ e) (e ⁻¹' s) ∧
      (∀ j ≤ k, ∀ x ∈ e ⁻¹' s, ‖iteratedFDeriv ℝ j (a.symm ∘ f ∘ e) x‖ ≤ M) ∧
      ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j (a.symm ∘ f ∘ e)) (e ⁻¹' s) :=
  ⟨a.symm.contDiff.comp_contDiffOn (hf.comp_continuousLinearMap (e : E' →L[ℝ] E)),
    fun j hj x hx => by
      rw [a.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hfb j hj (e x) hx,
    fun j hj => e.holderOnWith_iteratedFDeriv_comp a.symm f j (hfH j hj)⟩

/-- Transfers a Hölder bound for the `k`-th derivative of a bilinear product from `ULift` copies
of the spaces in a common universe back to the original spaces. The lifted bound is required for
every bilinear map between the lifted spaces of norm at most `‖L‖`. -/
private theorem holderOnWith_iteratedFDeriv_comp₂_of_uLift
    {E : Type uE} {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {k : ℕ} {f : E → A} {g : E → B} {s : Set E} {C α : ℝ≥0}
    (h : ∀ Lu : ULift.{max uE uB uG, uA} A →L[ℝ] ULift.{max uE uA uG, uB} B →L[ℝ]
        ULift.{max uE uA uB, uG} G, ‖Lu‖₊ ≤ ‖L‖₊ →
      HolderOnWith C α (iteratedFDeriv ℝ k fun x : ULift.{max uA uB uG, uE} E =>
        Lu ((LinearIsometryEquiv.ulift ℝ A).symm (f (LinearIsometryEquiv.ulift ℝ E x)))
          ((LinearIsometryEquiv.ulift ℝ B).symm (g (LinearIsometryEquiv.ulift ℝ E x))))
        (LinearIsometryEquiv.ulift ℝ E ⁻¹' s)) :
    HolderOnWith C α (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) s := by
  let Eu : Type max uE uA uB uG := ULift.{max uA uB uG, uE} E
  let Au : Type max uE uA uB uG := ULift.{max uE uB uG, uA} A
  let Bu : Type max uE uA uB uG := ULift.{max uE uA uG, uB} B
  let Gu : Type max uE uA uB uG := ULift.{max uE uA uB, uG} G
  let e : Eu ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let a : Au ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let b : Bu ≃ₗᵢ[ℝ] B := LinearIsometryEquiv.ulift ℝ B
  let c : Gu ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let Lu₀ := ((L.comp (a : Au →L[ℝ] A)).flip.comp (b : Bu →L[ℝ] B)).flip
  let Lu : Au →L[ℝ] Bu →L[ℝ] Gu :=
    compL ℝ Au (Bu →L[ℝ] G) (Bu →L[ℝ] Gu)
      (compL ℝ Bu G Gu (c.symm : G →L[ℝ] Gu)) Lu₀
  have hLu : (fun x => Lu (a.symm (f (e x))) (b.symm (g (e x)))) =
      c.symm ∘ (fun x => L (f x) (g x)) ∘ e := by
    ext x
    simp [Lu, Lu₀]
  have hnormReal : ‖Lu‖ ≤ ‖L‖ := by
    refine opNorm_le_bound _ (norm_nonneg L) fun v => ?_
    refine opNorm_le_bound _ (by positivity) fun w => ?_
    simpa [Lu, Lu₀] using L.le_opNorm₂ (a v) (b w)
  have hbound : HolderOnWith C α
      (iteratedFDeriv ℝ k fun x => Lu (a.symm (f (e x))) (b.symm (g (e x)))) (e ⁻¹' s) :=
    h Lu (by exact_mod_cast hnormReal)
  rw [holderOnWith_iff_dist_le] at hbound ⊢
  intro x hx y hy
  have hxy := hbound (e.symm x) (by simpa using hx) (e.symm y) (by simpa using hy)
  rw [hLu, dist_eq_norm, LinearIsometryEquiv.norm_iteratedFDeriv_sub_comp, e.symm.dist_map] at hxy
  simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.dist_map,
    dist_eq_norm] using hxy

/-- A supported bilinear product has a global Hölder bound for its order-`k` derivative from
uniform local bounds on all source jets and global bounds on all supported-factor jets. -/
theorem holderWith_iteratedFDeriv_of_tsupport_subset_right
    {E : Type uE} {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {k : ℕ} {f : E → A} {g : E → B} {s : Set E}
    {M N H K α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hg : ContDiff ℝ k g) (hs : IsOpen s)
    (hgs : tsupport g ⊆ s)
    (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hgb : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ N)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s)
    (hgH : ∀ j ≤ k, HolderWith K α (iteratedFDeriv ℝ j g)) :
    HolderWith ((2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) := by
  -- A common universe permits induction through continuous-linear-map-valued derivatives.
  refine holderOnWith_univ.mp (holderOnWith_iteratedFDeriv_comp₂_of_uLift L fun Lu hnorm => ?_)
  let e : ULift.{max uA uB uG, uE} E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let a : ULift.{max uE uB uG, uA} A ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let b : ULift.{max uE uA uG, uB} B ≃ₗᵢ[ℝ] B := LinearIsometryEquiv.ulift ℝ B
  obtain ⟨hfu, hfub, hfuH⟩ := contDiffOn_bounds_comp_linearIsometryEquiv e a hf hfb hfH
  have hgu : ContDiff ℝ k (b.symm ∘ g ∘ e) := b.symm.contDiff.comp (hg.comp e.contDiff)
  have hsupport : tsupport (b.symm ∘ g ∘ e) ⊆ e ⁻¹' s := by
    apply (tsupport_comp_subset (map_zero b.symm) (g ∘ e)).trans
    exact (tsupport_comp_subset_preimage g e.continuous).trans (preimage_mono hgs)
  have h := holderWith_iteratedFDeriv_bilinear_aux k Lu hfu hgu (hs.preimage e.continuous)
    hsupport hfub
    (fun j hj x => by
      rw [b.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hgb j hj (e x))
    hfuH
    (fun j hj => holderOnWith_univ.mp (by
      simpa using e.holderOnWith_iteratedFDeriv_comp b.symm g j ((hgH j hj).holderOnWith univ)))
  exact (h.mono (by gcongr)).holderOnWith _

/-- Single-universe form of `holderOnWith_iteratedFDeriv_comp₂`, proved by induction on the
order: the derivative of `x ↦ L (f x) (g x)` is the sum of two bilinear products of the same
kind, with one factor differentiated. -/
private theorem holderOnWith_iteratedFDeriv_comp₂_aux {E A B G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (k : ℕ) (L : A →L[ℝ] B →L[ℝ] G) {f : E → A} {g : E → B} {s : Set E}
    {M N H K α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) (hs : IsOpen s)
    (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hgb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g x‖ ≤ N)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s)
    (hgH : ∀ j ≤ k, HolderOnWith K α (iteratedFDeriv ℝ j g) s) :
    HolderOnWith ((2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) s := by
  induction k generalizing A B G with
  | zero =>
    rw [pow_zero, one_mul, TauCeti.holderOnWith_iteratedFDeriv_zero_iff]
    exact L.holderOnWith_comp₂ (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp (hfH 0 le_rfl))
      (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp (hgH 0 le_rfl))
      (by simpa only [norm_iteratedFDeriv_zero] using hfb 0 le_rfl)
      (by simpa only [norm_iteratedFDeriv_zero] using hgb 0 le_rfl)
  | succ k ih =>
    have hf' : ContDiffOn ℝ k (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
    have hg' : ContDiffOn ℝ k (fderiv ℝ g) s := hg.fderiv_of_isOpen hs (by simp)
    have hf₀ : ContDiffOn ℝ k f s := hf.of_le (by simp)
    have hg₀ : ContDiffOn ℝ k g s := hg.of_le (by simp)
    -- The induction hypothesis for the two terms of the Leibniz rule for the derivative.
    have hR := ih (L.precompR E) hf₀ hg' (fun j hj => hfb j (by omega))
      (fun j hj x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hgb (j + 1) (by omega) x hx)
      (fun j hj => hfH j (by omega))
      (fun j hj => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hgH (j + 1) (by omega)))
    have hL := ih (L.precompL E) hf' hg₀
      (fun j hj x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hfb (j + 1) (by omega) x hx)
      (fun j hj => hgb j (by omega))
      (fun j hj => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hfH (j + 1) (by omega)))
      (fun j hj => hgH j (by omega))
    have hRdiff : ContDiffOn ℝ k (fun x => L.precompR E (f x) (fderiv ℝ g x)) s :=
      (L.precompR E).isBoundedBilinearMap.contDiff.comp_contDiffOn (hf₀.prodMk hg')
    have hLdiff : ContDiffOn ℝ k (fun x => L.precompL E (fderiv ℝ f x) (g x)) s :=
      (L.precompL E).isBoundedBilinearMap.contDiff.comp_contDiffOn (hf'.prodMk hg₀)
    -- On the open set `s`, the derivative of the product is given by the Leibniz rule, so the
    -- iterated derivatives of both sides agree there.
    have hd : ∀ x ∈ s, iteratedFDeriv ℝ k (fderiv ℝ (fun x => L (f x) (g x))) x =
        iteratedFDeriv ℝ k (fun x => L.precompR E (f x) (fderiv ℝ g x)) x +
          iteratedFDeriv ℝ k (fun x => L.precompL E (fderiv ℝ f x) (g x)) x := fun x hx => by
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact L.fderiv_of_bilinear ((hf.differentiableOn (by simp) y hy).differentiableAt
          (hs.mem_nhds hy)) ((hg.differentiableOn (by simp) y hy).differentiableAt
          (hs.mem_nhds hy))) k).eq_of_nhds]
      exact iteratedFDeriv_add_apply (hRdiff.contDiffAt (hs.mem_nhds hx))
        (hLdiff.contDiffAt (hs.mem_nhds hx))
    have hsum := (hR.add hL).mono_const (show _ ≤ (2 : ℝ≥0)^(k + 1) * ‖L‖₊ * (M * K + N * H) by
      calc
        _ ≤ (2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H) + (2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H) := by
          gcongr
          · exact_mod_cast L.norm_precompR_le E
          · exact_mod_cast L.norm_precompL_le E
        _ = _ := by ring)
    rw [TauCeti.holderOnWith_iteratedFDeriv_succ_iff]
    intro x hx y hy
    rw [hd x hx, hd y hy]
    exact hsum x hx y hy

/-- **Leibniz's rule preserves Hölder bounds on an open set.** If `f` and `g` are `C^k` on an open
set `s`, with all derivative fields through order `k` bounded by `M` and `N` and `α`-Hölder with
constants `H` and `K` on `s`, then the `k`-th derivative of `x ↦ L (f x) (g x)` is `α`-Hölder on
`s` with constant `2 ^ k * ‖L‖ * (M * K + N * H)`. -/
theorem holderOnWith_iteratedFDeriv_comp₂
    {E : Type uE} {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {k : ℕ} {f : E → A} {g : E → B} {s : Set E}
    {M N H K α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hg : ContDiffOn ℝ k g s) (hs : IsOpen s)
    (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hgb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j g x‖ ≤ N)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s)
    (hgH : ∀ j ≤ k, HolderOnWith K α (iteratedFDeriv ℝ j g) s) :
    HolderOnWith ((2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) s := by
  -- A common universe permits induction through continuous-linear-map-valued derivatives.
  refine holderOnWith_iteratedFDeriv_comp₂_of_uLift L fun Lu hnorm => ?_
  let e : ULift.{max uA uB uG, uE} E ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let a : ULift.{max uE uB uG, uA} A ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let b : ULift.{max uE uA uG, uB} B ≃ₗᵢ[ℝ] B := LinearIsometryEquiv.ulift ℝ B
  obtain ⟨hfu, hfub, hfuH⟩ := contDiffOn_bounds_comp_linearIsometryEquiv e a hf hfb hfH
  obtain ⟨hgu, hgub, hguH⟩ := contDiffOn_bounds_comp_linearIsometryEquiv e b hg hgb hgH
  have h := holderOnWith_iteratedFDeriv_comp₂_aux k Lu hfu hgu (hs.preimage e.continuous)
    hfub hgub hfuH hguH
  exact h.mono_const (by gcongr)

/-- Two local `C^{n,α}` maps have a local `C^{n,α}` bilinear product, without an extra
derivative or finite-dimensional parameter assumption. -/
theorem exists_holderOnWith_iteratedFDeriv_comp₂
    {P : Type uP} {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {n : ℕ} {α C D : ℝ≥0} {f : P → A} {g : P → B}
    {s : Set P} {a : P} (hs : s ∈ 𝓝 a) (hα : α ≤ 1)
    (hf : ContDiffOn ℝ n f s) (hg : ContDiffOn ℝ n g s)
    (hfH : HolderOnWith C α (iteratedFDeriv ℝ n f) s)
    (hgH : HolderOnWith D α (iteratedFDeriv ℝ n g) s) :
    ∃ r > 0, ball a r ⊆ s ∧
      ContDiffOn ℝ n (fun x ↦ L (f x) (g x)) (ball a r) ∧ ∃ K : ℝ≥0,
        HolderOnWith K α (iteratedFDeriv ℝ n (fun x ↦ L (f x) (g x))) (ball a r) := by
  obtain ⟨r, hr, hrs, M, H, hfb, hfH'⟩ :=
    hf.exists_ball_bounds_and_holderOnWith_iteratedFDeriv hs hα hfH
  obtain ⟨t, ht, _, N, K, hgb, hgH'⟩ :=
    hg.exists_ball_bounds_and_holderOnWith_iteratedFDeriv hs hα hgH
  obtain ⟨ρ, hρ, hρrt⟩ := Metric.eventually_nhds_iff_ball.mp
    (Filter.Eventually.and (ball_mem_nhds a hr) (ball_mem_nhds a ht))
  have hρr : ball a ρ ⊆ ball a r := fun x hx ↦ (hρrt x hx).1
  have hρt : ball a ρ ⊆ ball a t := fun x hx ↦ (hρrt x hx).2
  have hρs := hρr.trans hrs
  have hC : ContDiffOn ℝ n (fun x ↦ L (f x) (g x)) s :=
    L.isBoundedBilinearMap.contDiff.comp_contDiffOn (hf.prodMk hg)
  exact ⟨ρ, hρ, hρs, hC.mono hρs, _, L.holderOnWith_iteratedFDeriv_comp₂
    (hf.mono hρs) (hg.mono hρs) isOpen_ball
    (fun j hj x hx ↦ hfb j hj x (hρr hx)) (fun j hj x hx ↦ hgb j hj x (hρt hx))
    (fun j hj ↦ (hfH' j hj).mono hρr) (fun j hj ↦ (hgH' j hj).mono hρt)⟩

end ContinuousLinearMap
