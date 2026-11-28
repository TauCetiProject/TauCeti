/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.AnalyticSubmanifold.Transport
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.RegularValue.Level
import TauCeti.Geometry.Manifold.SmoothEmbedding.DefiningEquation

/-!
# Regular defining equations for analytic submanifolds

`IsOpen.isMAnalyticSubmanifold_inter_preimage_singleton` identifies a nonempty regular level
on an open set as an analytic submanifold of the ambient manifold. It uses
`TauCeti.isSmoothEmbedding_coe_regularLevel` to embed the level and
`Manifold.IsSmoothEmbedding.isMAnalyticSubmanifold_range` to recognize its image.

`TauCeti.isMAnalyticSubmanifold_iff_locally_eq_zero` characterizes analytic submanifolds by local
regular equations with as many components as the codimension. The forward direction uses
`TauCeti.IsMAnalyticSubmanifold.exists_isSmoothEmbedding` and
`TauCeti.SmoothEmbedding.exists_contMDiffOn_eq_zero`. Over `ℂ` these are holomorphic equations.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.1.
-/

public section

open Module Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H M : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ω M]
  {n d : ℕ} {e : E ≃L[𝕜] Fin n → 𝕜}

/-- The nonempty level `f = c` on an open set of a boundaryless analytic manifold is an analytic
submanifold of codimension `finrank 𝕜 F` if `f` is analytic and its differential is surjective at
each point of the level. Surjectivity at any point of the level makes the codomain
finite-dimensional. -/
theorem _root_.IsOpen.isMAnalyticSubmanifold_inter_preimage_singleton
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {c : F} {U : Set M}
    (hU : IsOpen U) (hne : (U ∩ f ⁻¹' {c}).Nonempty)
    (hf : ∀ x ∈ U, f x = c → ContMDiffAt I 𝓘(𝕜, F) ω f x)
    (hreg : ∀ x ∈ U, f x = c → IsRegularPoint I 𝓘(𝕜, F) f x) :
    IsMAnalyticSubmanifold I e (n - finrank 𝕜 F) (U ∩ f ⁻¹' {c}) := by
  have : FiniteDimensional 𝕜 E := e.symm.toLinearEquiv.finiteDimensional
  obtain ⟨x, hxU, hxc⟩ := hne
  have hsurj := isRegularPoint_iff.1 (hreg x hxU hxc)
  have : FiniteDimensional 𝕜 F :=
    FiniteDimensional.of_surjective (mfderiv I 𝓘(𝕜, F) f x).toLinearMap hsurj
  let V : TopologicalSpace.Opens M := ⟨U, hU⟩
  let g : V → F := f ∘ Subtype.val
  have hg (y : V) (hy : g y = c) : ContMDiffAt I 𝓘(𝕜, F) ω g y :=
    (hf y y.property hy).comp y contMDiff_subtypeVal.contMDiffAt
  have hregular : IsRegularValue I 𝓘(𝕜, F) g c := by
    rw [isRegularValue_iff]
    intro y hy
    exact (hreg y y.property hy).comp (isRegularPoint_subtype_val y)
  have hdim : finrank 𝕜 E - finrank 𝕜 F = n - finrank 𝕜 F := by
    rw [e.toLinearEquiv.finrank_eq, finrank_fin_fun]
  have hone : 1 ≤ (ω : ℕ∞ω) := by simp
  let := regularLevelChartedSpace (fun y hy ↦ (hg y hy).of_le hone) hregular hdim
  let := isManifold_regularLevel hone hg hregular hdim
  have : Nonempty {y : V // g y = c} := ⟨⟨⟨x, hxU⟩, hxc⟩⟩
  have hemb := isSmoothEmbedding_coe_regularLevel hone hg hregular hdim
  have hlevel : {y : V | g y = c} = (Subtype.val : V → M) ⁻¹' (f ⁻¹' {c}) := rfl
  have hrange : range ((Subtype.val : V → M) ∘ (Subtype.val : {y : V // g y = c} → V)) =
      U ∩ f ⁻¹' {c} := by
    rw [range_comp, Subtype.range_val_subtype, hlevel, image_preimage_eq_inter_range,
      Subtype.range_val_subtype, inter_comm]
    simp only [V, TopologicalSpace.Opens.mem_mk, ofPred_mem_eq]
  rw [← hrange]
  exact ((isSmoothEmbedding_subtypeVal_comp_iff).2 hemb).isMAnalyticSubmanifold_range
    (ContinuousLinearEquiv.refl 𝕜 _) e

/-- A subset of an `n`-dimensional boundaryless analytic manifold is a `d`-dimensional analytic
submanifold precisely when it is nonempty, `d ≤ n`, and locally the zero set of `n - d` analytic
equations with surjective differential along the zero set. -/
theorem isMAnalyticSubmanifold_iff_locally_eq_zero {s : Set M} :
    IsMAnalyticSubmanifold I e d s ↔ s.Nonempty ∧ d ≤ n ∧
      ∀ x ∈ s, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ g : M → Fin (n - d) → 𝕜,
        ContMDiffOn I 𝓘(𝕜, Fin (n - d) → 𝕜) ω g U ∧
        (∀ y ∈ U, y ∈ s ↔ g y = 0) ∧
        ∀ y ∈ U, g y = 0 → IsRegularPoint I 𝓘(𝕜, Fin (n - d) → 𝕜) g y := by
  constructor
  · intro hs
    have : FiniteDimensional 𝕜 E := e.symm.toLinearEquiv.finiteDimensional
    obtain ⟨charts, -, hemb⟩ := hs.exists_isSmoothEmbedding
    let := charts
    let i := SmoothEmbedding.ofIsSmoothEmbedding Subtype.val hemb
    have hdim : finrank 𝕜 (Fin (n - d) → 𝕜) = finrank 𝕜 E - finrank 𝕜 (Fin d → 𝕜) := by
      rw [e.toLinearEquiv.finrank_eq]
      simp only [finrank_fin_fun]
    refine ⟨hs.nonempty, hs.le, fun x hx ↦ ?_⟩
    obtain ⟨U, hU, hxU, g, hg, hzero, hreg⟩ := i.exists_contMDiffOn_eq_zero (by simp) hdim ⟨x, hx⟩
    simp only [i, SmoothEmbedding.coe_ofIsSmoothEmbedding, Subtype.range_val] at hxU hzero
    exact ⟨U, hU, hxU, g, hg, hzero, fun y hy _ ↦ hreg y hy⟩
  · rintro ⟨hne, hd, hloc⟩
    refine isMAnalyticSubmanifold_of_locally_isMAnalyticSubmanifold hne fun x hx ↦ ?_
    obtain ⟨U, hU, hxU, g, hg, hzero, hreg⟩ := hloc x hx
    refine ⟨U, hU, hxU, ?_⟩
    have heq : U ∩ g ⁻¹' {0} = s ∩ U := by
      ext y
      exact ⟨fun ⟨hyU, hy0⟩ ↦ ⟨(hzero y hyU).2 hy0, hyU⟩,
        fun ⟨hys, hyU⟩ ↦ ⟨hyU, (hzero y hyU).1 hys⟩⟩
    have hne : (s ∩ U).Nonempty := ⟨x, hx, hxU⟩
    have hlevel := hU.isMAnalyticSubmanifold_inter_preimage_singleton (e := e)
      (heq ▸ hne) (fun y hy _ ↦ hg.contMDiffAt (hU.mem_nhds hy)) hreg
    simpa only [heq, finrank_fin_fun, Nat.sub_sub_self hd] using hlevel

end TauCeti
