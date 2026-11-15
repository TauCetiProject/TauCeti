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

Leibniz differentiation preserves Hölder bounds at every finite order, both on an open set when
both factors satisfy local derivative and Hölder bounds there, and globally when the second factor
has topological support inside an open set where the first factor is controlled.
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
  let Lu₀ := ((L.comp (a : Au →L[ℝ] A)).flip.comp (b : Bu →L[ℝ] B)).flip
  let Lu : Au →L[ℝ] Bu →L[ℝ] Gu :=
    compL ℝ Au (Bu →L[ℝ] G) (Bu →L[ℝ] Gu)
      (compL ℝ Bu G Gu (c.symm : G →L[ℝ] Gu)) Lu₀
  have hLu : (fun x => Lu (fu x) (gu x)) = c.symm ∘ (fun x => L (f x) (g x)) ∘ e := by
    ext x
    simp [Lu, Lu₀, fu, gu]
  have hnormReal : ‖Lu‖ ≤ ‖L‖ := by
    refine opNorm_le_bound _ (norm_nonneg L) fun v => ?_
    refine opNorm_le_bound _ (by positivity) fun w => ?_
    simpa [Lu, Lu₀] using L.le_opNorm₂ (a v) (b w)
  have hnorm : ‖Lu‖₊ ≤ ‖L‖₊ := by exact_mod_cast hnormReal
  have hfu : ContDiffOn ℝ k fu (e ⁻¹' s) :=
    a.symm.contDiff.comp_contDiffOn (hf.comp_continuousLinearMap (e : Eu →L[ℝ] E))
  have hgu : ContDiff ℝ k gu := b.symm.contDiff.comp (hg.comp e.contDiff)
  have hsupport : tsupport gu ⊆ e ⁻¹' s := by
    apply (tsupport_comp_subset (map_zero b.symm) (g ∘ e)).trans
    exact (tsupport_comp_subset_preimage g e.continuous).trans (preimage_mono hgs)
  have h := holderWith_iteratedFDeriv_bilinear_aux k Lu hfu hgu (hs.preimage e.continuous)
    hsupport (fun j hj x hx => by
      rw [a.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hfb j hj (e x) hx)
    (fun j hj x => by
      rw [b.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hgb j hj (e x))
    (fun j hj => e.holderOnWith_iteratedFDeriv_comp a.symm f j (hfH j hj))
    (fun j hj => holderOnWith_univ.mp (by
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

private theorem holderOnWith_iteratedFDeriv_zero_bilinear {E A B G : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : A →L[ℝ] B →L[ℝ] G) {f : E → A} {g : E → B} {s : Set E} {M N H K α : ℝ≥0}
    (hfb : ∀ x ∈ s, ‖iteratedFDeriv ℝ 0 f x‖ ≤ M) (hgb : ∀ x ∈ s, ‖iteratedFDeriv ℝ 0 g x‖ ≤ N)
    (hfH : HolderOnWith H α (iteratedFDeriv ℝ 0 f) s)
    (hgH : HolderOnWith K α (iteratedFDeriv ℝ 0 g) s) :
    HolderOnWith (‖L‖₊ * (M * K + N * H)) α
      (iteratedFDeriv ℝ 0 (fun x => L (f x) (g x))) s := by
  rw [TauCeti.holderOnWith_iteratedFDeriv_zero_iff]
  exact L.holderOnWith_comp₂ (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp hfH)
    (TauCeti.holderOnWith_iteratedFDeriv_zero_iff.mp hgH)
    (by simpa only [norm_iteratedFDeriv_zero] using hfb)
    (by simpa only [norm_iteratedFDeriv_zero] using hgb)

private theorem holderOnWith_iteratedFDeriv_bilinear_aux {E A B G : Type u}
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
    simpa using holderOnWith_iteratedFDeriv_zero_bilinear L (hfb 0 le_rfl) (hgb 0 le_rfl)
      (hfH 0 le_rfl) (hgH 0 le_rfl)
  | succ k ih =>
    have hf' : ContDiffOn ℝ k (fderiv ℝ f) s := hf.fderiv_of_isOpen hs (by simp)
    have hg' : ContDiffOn ℝ k (fderiv ℝ g) s := hg.fderiv_of_isOpen hs (by simp)
    have hR := ih (L.precompR E) (hf.of_le (by simp)) hg' (fun j hj => hfb j (by omega))
      (fun j _ x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hgb (j + 1) (by omega) x hx)
      (fun j hj => hfH j (by omega))
      (fun j _ => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hgH (j + 1) (by omega)))
    have hL := ih (L.precompL E) hf' (hg.of_le (by simp))
      (fun j _ x hx => by rw [norm_iteratedFDeriv_fderiv]; exact hfb (j + 1) (by omega) x hx)
      (fun j hj => hgb j (by omega))
      (fun j _ => TauCeti.holderOnWith_iteratedFDeriv_succ_iff.mp (hfH (j + 1) (by omega)))
      (fun j hj => hgH j (by omega))
    let uR : E → E →L[ℝ] G := fun x => L.precompR E (f x) (fderiv ℝ g x)
    let uL : E → E →L[ℝ] G := fun x => L.precompL E (fderiv ℝ f x) (g x)
    have huR : ContDiffOn ℝ k uR s :=
      (L.precompR E).isBoundedBilinearMap.contDiff.comp_contDiffOn ((hf.of_le (by simp)).prodMk hg')
    have huL : ContDiffOn ℝ k uL s :=
      (L.precompL E).isBoundedBilinearMap.contDiff.comp_contDiffOn (hf'.prodMk (hg.of_le (by simp)))
    have hsum : HolderOnWith ((2 : ℝ≥0) ^ (k + 1) * ‖L‖₊ * (M * K + N * H)) α
        (iteratedFDeriv ℝ k uR + iteratedFDeriv ℝ k uL) s :=
      (hR.add hL).mono_const (calc
        _ ≤ (2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H) +
            (2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H) := by
          gcongr
          · exact_mod_cast L.norm_precompR_le E
          · exact_mod_cast L.norm_precompL_le E
        _ = _ := by ring)
    have heq : ∀ x ∈ s, iteratedFDeriv ℝ k (fderiv ℝ (fun y => L (f y) (g y))) x =
        (iteratedFDeriv ℝ k uR + iteratedFDeriv ℝ k uL) x := fun x hx => by
      have hd : fderiv ℝ (fun y => L (f y) (g y)) =ᶠ[𝓝 x] uR + uL := by
        filter_upwards [hs.mem_nhds hx] with y hy
        exact L.fderiv_of_bilinear
          ((hf.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hy))
          ((hg.differentiableOn (by simp)).differentiableAt (hs.mem_nhds hy))
      rw [(hd.iteratedFDeriv ℝ k).eq_of_nhds,
        iteratedFDeriv_add_apply (huR.contDiffAt (hs.mem_nhds hx))
          (huL.contDiffAt (hs.mem_nhds hx)), Pi.add_apply]
    rw [TauCeti.holderOnWith_iteratedFDeriv_succ_iff]
    intro x hx y hy
    rw [heq x hx, heq y hy]
    exact hsum x hx y hy

/-- A bilinear product on an open set `s` has a local Hölder bound for its order-`k` derivative
from uniform bounds and Hölder bounds on all iterated derivatives of both factors up to order `k`
on `s`, adapting `holderWith_iteratedFDeriv_of_tsupport_subset_right` to open domains without a
support condition. -/
theorem holderOnWith_iteratedFDeriv
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
  let Lu₀ := ((L.comp (a : Au →L[ℝ] A)).flip.comp (b : Bu →L[ℝ] B)).flip
  let Lu : Au →L[ℝ] Bu →L[ℝ] Gu :=
    compL ℝ Au (Bu →L[ℝ] G) (Bu →L[ℝ] Gu)
      (compL ℝ Bu G Gu (c.symm : G →L[ℝ] Gu)) Lu₀
  have hLu : (fun x => Lu (fu x) (gu x)) = c.symm ∘ (fun x => L (f x) (g x)) ∘ e := by
    ext x
    simp [Lu, Lu₀, fu, gu]
  have hnorm : ‖Lu‖₊ ≤ ‖L‖₊ := by
    exact_mod_cast (opNorm_le_bound _ (norm_nonneg L) fun v =>
      opNorm_le_bound _ (by positivity) fun w => by simpa [Lu, Lu₀] using L.le_opNorm₂ (a v) (b w))
  have hfu : ContDiffOn ℝ k fu (e ⁻¹' s) :=
    a.symm.contDiff.comp_contDiffOn (hf.comp_continuousLinearMap (e : Eu →L[ℝ] E))
  have hgu : ContDiffOn ℝ k gu (e ⁻¹' s) :=
    b.symm.contDiff.comp_contDiffOn (hg.comp_continuousLinearMap (e : Eu →L[ℝ] E))
  have h := (holderOnWith_iteratedFDeriv_bilinear_aux k Lu hfu hgu (hs.preimage e.continuous)
    (fun j hj x hx => by
      rw [a.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hfb j hj (e x) hx)
    (fun j hj x hx => by
      rw [b.symm.norm_iteratedFDeriv_comp_left, e.norm_iteratedFDeriv_comp_right]
      exact hgb j hj (e x) hx)
    (fun j hj => e.holderOnWith_iteratedFDeriv_comp a.symm f j (hfH j hj))
    (fun j hj => e.holderOnWith_iteratedFDeriv_comp b.symm g j (hgH j hj))).mono_const
    (C₂ := (2 : ℝ≥0) ^ k * ‖L‖₊ * (M * K + N * H)) (by gcongr)
  rw [holderOnWith_iff_dist_le] at h ⊢
  intro x hx y hy
  have hxy := h (e.symm x) (by simpa using hx) (e.symm y) (by simpa using hy)
  rw [hLu, dist_eq_norm, LinearIsometryEquiv.norm_iteratedFDeriv_sub_comp, e.symm.dist_map] at hxy
  simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.dist_map,
    dist_eq_norm] using hxy

end ContinuousLinearMap
