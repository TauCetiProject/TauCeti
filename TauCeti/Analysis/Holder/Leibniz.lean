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

Leibniz differentiation preserves Hölder bounds at every finite order. Only local bounds on the
first factor are needed when the second factor has topological support inside that open set
(`ContinuousLinearMap.holderWith_iteratedFDeriv_of_tsupport_subset_right`). When both factors are
only given on an open set, Hölder bounds on that set for all their derivatives through order `k`
give a Hölder bound on that set for the `k`-th derivative of the product
(`ContinuousLinearMap.holderOnWith_iteratedFDeriv_comp₂`).
-/

public section

open Set
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

/-- A continuous bilinear map transported to `ULift`s of its spaces. The Leibniz inductions in
this file run with all spaces in a common universe, and this brings a bilinear map there. -/
private noncomputable def uliftBilinear {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] B →L[ℝ] G) :
    ULift.{wA} A →L[ℝ] ULift.{wB} B →L[ℝ] ULift.{wG} G :=
  compL ℝ (ULift.{wA} A) (ULift.{wB} B →L[ℝ] G) (ULift.{wB} B →L[ℝ] ULift.{wG} G)
    (compL ℝ (ULift.{wB} B) G (ULift.{wG} G)
      ((LinearIsometryEquiv.ulift ℝ G).symm : G →L[ℝ] ULift.{wG} G))
    ((L.comp (LinearIsometryEquiv.ulift ℝ A : ULift.{wA} A →L[ℝ] A)).flip.comp
      (LinearIsometryEquiv.ulift ℝ B : ULift.{wB} B →L[ℝ] B)).flip

private theorem uliftBilinear_apply {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] B →L[ℝ] G) (a : ULift.{wA} A)
    (b : ULift.{wB} B) :
    (uliftBilinear L : ULift.{wA} A →L[ℝ] ULift.{wB} B →L[ℝ] ULift.{wG} G) a b =
      (LinearIsometryEquiv.ulift ℝ G).symm
        (L (LinearIsometryEquiv.ulift ℝ A a) (LinearIsometryEquiv.ulift ℝ B b)) := by
  simp [uliftBilinear]

private theorem nnnorm_uliftBilinear_le {A : Type uA} {B : Type uB} {G : Type uG}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] B →L[ℝ] G) :
    ‖(uliftBilinear L : ULift.{wA} A →L[ℝ] ULift.{wB} B →L[ℝ] ULift.{wG} G)‖₊ ≤ ‖L‖₊ := by
  have h : ‖(uliftBilinear L : ULift.{wA} A →L[ℝ] ULift.{wB} B →L[ℝ] ULift.{wG} G)‖ ≤ ‖L‖ := by
    refine opNorm_le_bound _ (norm_nonneg L) fun v => ?_
    refine opNorm_le_bound _ (by positivity) fun w => ?_
    rw [uliftBilinear_apply, LinearIsometryEquiv.norm_map]
    exact L.le_opNorm₂ _ _
  exact_mod_cast h

/-- A bilinear product read through `uliftBilinear` and linear isometries of the source is the
lifted product. -/
private theorem uliftBilinear_comp {E' : Type*} {E : Type*} {A : Type uA} {B : Type uB}
    {G : Type uG} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup G] [NormedSpace ℝ G] (L : A →L[ℝ] B →L[ℝ] G)
    (f : E → A) (g : E → B) (e : E' ≃ₗᵢ[ℝ] E) :
    (fun x => (uliftBilinear L : ULift.{wA} A →L[ℝ] ULift.{wB} B →L[ℝ] ULift.{wG} G)
        (((LinearIsometryEquiv.ulift ℝ A).symm ∘ f ∘ e) x)
        (((LinearIsometryEquiv.ulift ℝ B).symm ∘ g ∘ e) x)) =
      (LinearIsometryEquiv.ulift ℝ G).symm ∘ (fun x => L (f x) (g x)) ∘ e := by
  funext x
  simp only [Function.comp_apply, uliftBilinear_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The hypotheses on one factor of a bilinear product transport along linear isometries of the
source and target: `C^k` regularity on `s`, bounds on `s` for all derivatives through order `k`,
and `α`-Hölder bounds on `s` for them pass to `a ∘ f ∘ e` on `e ⁻¹' s`. -/
private theorem comp_linearIsometryEquiv_of_holderOnWith {E' E A A' : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup A'] [NormedSpace ℝ A']
    (e : E' ≃ₗᵢ[ℝ] E) (a : A ≃ₗᵢ[ℝ] A') {k : ℕ} {f : E → A} {s : Set E} {M H α : ℝ≥0}
    (hf : ContDiffOn ℝ k f s) (hfb : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j f x‖ ≤ M)
    (hfH : ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j f) s) :
    ContDiffOn ℝ k (a ∘ f ∘ e) (e ⁻¹' s) ∧
      (∀ j ≤ k, ∀ x ∈ e ⁻¹' s, ‖iteratedFDeriv ℝ j (a ∘ f ∘ e) x‖ ≤ M) ∧
      ∀ j ≤ k, HolderOnWith H α (iteratedFDeriv ℝ j (a ∘ f ∘ e)) (e ⁻¹' s) :=
  ⟨a.contDiff.comp_contDiffOn (hf.comp_continuousLinearMap (e : E' →L[ℝ] E)),
    fun j hj x hx => by
      rw [a.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hfb j hj (e x) hx,
    fun j hj => e.holderOnWith_iteratedFDeriv_comp a f j (hfH j hj)⟩

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
  let Eu : Type max uE uA uB uG := ULift.{max uA uB uG, uE} E
  let Au : Type max uE uA uB uG := ULift.{max uE uB uG, uA} A
  let Bu : Type max uE uA uB uG := ULift.{max uE uA uG, uB} B
  let Gu : Type max uE uA uB uG := ULift.{max uE uA uB, uG} G
  let e : Eu ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let a : Au ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let b : Bu ≃ₗᵢ[ℝ] B := LinearIsometryEquiv.ulift ℝ B
  let c : Gu ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let fu : Eu → Au := a.symm ∘ f ∘ e
  let gu : Eu → Bu := b.symm ∘ g ∘ e
  let Lu : Au →L[ℝ] Bu →L[ℝ] Gu := uliftBilinear L
  have hLu : (fun x => Lu (fu x) (gu x)) = c.symm ∘ (fun x => L (f x) (g x)) ∘ e :=
    uliftBilinear_comp L f g e
  have hnorm : ‖Lu‖₊ ≤ ‖L‖₊ := nnnorm_uliftBilinear_le L
  obtain ⟨hfu, hfub, hfuH⟩ := comp_linearIsometryEquiv_of_holderOnWith e a.symm hf hfb hfH
  have hgu : ContDiff ℝ k gu := b.symm.contDiff.comp (hg.comp e.contDiff)
  have hsupport : tsupport gu ⊆ e ⁻¹' s := by
    apply (tsupport_comp_subset (map_zero b.symm) (g ∘ e)).trans
    exact (tsupport_comp_subset_preimage g e.continuous).trans (preimage_mono hgs)
  have h := holderWith_iteratedFDeriv_bilinear_aux k Lu hfu hgu (hs.preimage e.continuous)
    hsupport hfub
    (fun j hj x => by
      rw [b.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hgb j hj (e x))
    hfuH (fun j hj => holderOnWith_univ.mp (by
      simpa using e.holderOnWith_iteratedFDeriv_comp b.symm g j ((hgH j hj).holderOnWith univ)))
  have h' : HolderWith ((2 : ℝ≥0)^k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => Lu (fu x) (gu x))) :=
    h.mono (by gcongr)
  have hbound := h'.holderOnWith univ
  apply holderOnWith_univ.mp
  rw [holderOnWith_iff_dist_le] at hbound ⊢
  intro x _ y _
  have hxy := hbound (e.symm x) (mem_univ _) (e.symm y) (mem_univ _)
  rw [hLu, dist_eq_norm, LinearIsometryEquiv.norm_iteratedFDeriv_sub_comp, e.symm.dist_map] at hxy
  simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.dist_map,
    dist_eq_norm] using hxy

/-- On an open set, the iterated derivatives of the derivative of a bilinear product are the sums
of those of the two Leibniz terms. -/
private theorem iteratedFDeriv_fderiv_comp₂_eq_add {E A B G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {k : ℕ} {f : E → A} {g : E → B} {s : Set E}
    (hf : ContDiffOn ℝ (k + 1) f s) (hg : ContDiffOn ℝ (k + 1) g s) (hs : IsOpen s) {x : E}
    (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fderiv ℝ (fun y => L (f y) (g y))) x =
      iteratedFDeriv ℝ k (fun y => L.precompR E (f y) (fderiv ℝ g y)) x +
        iteratedFDeriv ℝ k (fun y => L.precompL E (fderiv ℝ f y) (g y)) x := by
  have hloc : fderiv ℝ (fun y => L (f y) (g y)) =ᶠ[𝓝 x]
      (fun y => L.precompR E (f y) (fderiv ℝ g y)) +
        (fun y => L.precompL E (fderiv ℝ f y) (g y)) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact L.fderiv_of_bilinear
      ((hf.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hy))
      ((hg.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hy))
  rw [(hloc.iteratedFDeriv ℝ k).eq_of_nhds]
  exact iteratedFDeriv_add_apply
    (((L.precompR E).isBoundedBilinearMap.contDiff.comp_contDiffOn
      ((hf.of_le (by simp)).prodMk (hg.fderiv_of_isOpen hs (by simp)))).contDiffAt
        (hs.mem_nhds hx))
    (((L.precompL E).isBoundedBilinearMap.contDiff.comp_contDiffOn
      ((hf.fderiv_of_isOpen hs (by simp)).prodMk (hg.of_le (by simp)))).contDiffAt
        (hs.mem_nhds hx))

/-- The common-universe case of `holderOnWith_iteratedFDeriv_comp₂`, proved by induction on the
order through the Leibniz rule for the first derivative. -/
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
    HolderOnWith ((2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) s := by
  induction k generalizing A B G with
  | zero =>
    rw [pow_zero, one_mul, TauCeti.holderOnWith_iteratedFDeriv_zero_iff]
    refine L.holderOnWith_comp₂ (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp (hfH 0 le_rfl))
      (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp (hgH 0 le_rfl)) (fun x hx => ?_)
      (fun x hx => ?_)
    · simpa only [norm_iteratedFDeriv_zero] using hfb 0 le_rfl x hx
    · simpa only [norm_iteratedFDeriv_zero] using hgb 0 le_rfl x hx
  | succ k ih =>
    have hfb' : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖ ≤ M := by
      intro j hj x hx
      rw [norm_iteratedFDeriv_fderiv]
      exact hfb (j + 1) (by omega) x hx
    have hgb' : ∀ j ≤ k, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (fderiv ℝ g) x‖ ≤ N := by
      intro j hj x hx
      rw [norm_iteratedFDeriv_fderiv]
      exact hgb (j + 1) (by omega) x hx
    -- The two Leibniz terms of the first derivative satisfy the hypotheses at order `k`.
    have hR := ih (L.precompR E) (hf.of_le (by simp)) (hg.fderiv_of_isOpen hs (by simp))
      (fun j hj => hfb j (by omega)) hgb' (fun j hj => hfH j (by omega))
      (fun j hj => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hgH (j + 1) (by omega)))
    have hL := ih (L.precompL E) (hf.fderiv_of_isOpen hs (by simp)) (hg.of_le (by simp)) hfb'
      (fun j hj => hgb j (by omega))
      (fun j hj => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hfH (j + 1) (by omega)))
      (fun j hj => hgH j (by omega))
    rw [TauCeti.holderOnWith_iteratedFDeriv_succ_iff]
    refine ((hR.add hL).mono_const ?_).congr fun x hx =>
      (iteratedFDeriv_fderiv_comp₂_eq_add L hf hg hs hx).symm
    calc
      _ ≤ (2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H) +
          (2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H) := by
        gcongr
        · exact_mod_cast L.norm_precompR_le E
        · exact_mod_cast L.norm_precompL_le E
      _ = _ := by ring

/-- Leibniz differentiation preserves Hölder bounds on an open set: if `f` and `g` are `C^k` on
the open set `s`, with all derivatives through order `k` bounded on `s` by `M` and `N` and
`α`-Hölder on `s` with constants `H` and `K`, then the `k`-th derivative of the product
`x ↦ L (f x) (g x)` is `α`-Hölder on `s` with constant `2 ^ k * ‖L‖ * (M * K + N * H)`.
Hölder bounds on all lower derivatives are assumed, since on a non-convex set they do not follow
from the bounds on the next derivative. -/
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
    HolderOnWith ((2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ k (fun x => L (f x) (g x))) s := by
  -- A common universe permits induction through continuous-linear-map-valued derivatives.
  let Eu : Type max uE uA uB uG := ULift.{max uA uB uG, uE} E
  let Au : Type max uE uA uB uG := ULift.{max uE uB uG, uA} A
  let Bu : Type max uE uA uB uG := ULift.{max uE uA uG, uB} B
  let Gu : Type max uE uA uB uG := ULift.{max uE uA uB, uG} G
  let e : Eu ≃ₗᵢ[ℝ] E := LinearIsometryEquiv.ulift ℝ E
  let a : Au ≃ₗᵢ[ℝ] A := LinearIsometryEquiv.ulift ℝ A
  let b : Bu ≃ₗᵢ[ℝ] B := LinearIsometryEquiv.ulift ℝ B
  let c : Gu ≃ₗᵢ[ℝ] G := LinearIsometryEquiv.ulift ℝ G
  let fu : Eu → Au := a.symm ∘ f ∘ e
  let gu : Eu → Bu := b.symm ∘ g ∘ e
  let Lu : Au →L[ℝ] Bu →L[ℝ] Gu := uliftBilinear L
  have hLu : (fun x => Lu (fu x) (gu x)) = c.symm ∘ (fun x => L (f x) (g x)) ∘ e :=
    uliftBilinear_comp L f g e
  obtain ⟨hfu, hfub, hfuH⟩ := comp_linearIsometryEquiv_of_holderOnWith e a.symm hf hfb hfH
  obtain ⟨hgu, hgub, hguH⟩ := comp_linearIsometryEquiv_of_holderOnWith e b.symm hg hgb hgH
  have h := holderOnWith_iteratedFDeriv_comp₂_aux k Lu hfu hgu (hs.preimage e.continuous)
    hfub hgub hfuH hguH
  rw [hLu] at h
  -- Transport back along the inverse isometries.
  have h' := e.symm.holderOnWith_iteratedFDeriv_comp c _ k h
  have hfun : c ∘ (c.symm ∘ (fun x => L (f x) (g x)) ∘ e) ∘ e.symm =
      fun x => L (f x) (g x) := by
    ext x
    simp
  have hset : e.symm ⁻¹' (e ⁻¹' s) = s := by
    ext x
    simp
  rw [hfun, hset] at h'
  exact h'.mono_const (by gcongr; exact nnnorm_uliftBilinear_le L)

end ContinuousLinearMap
