/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Submersion
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Half-space charts from local defining functions

Let `ρ : M → ℝ` be `C^n`, `1 ≤ n`, on an open subset `U` of a boundaryless manifold modelled on a
finite-dimensional real space `E`, and let `p ∈ U` be a regular point of `ρ`. Then `ρ` is affine in
a `C^n` partial diffeomorphism `e` from a neighbourhood of `p` inside `U` onto an open subset of
`E`, centred at `p`: `ρ (e.symm z) = ℓ z + ρ p` for a nonzero continuous linear functional `ℓ`.
Consequently, if a set `D` agrees on `U` with the superlevel set `{ρ ≥ 0}` and `ρ p = 0`, then `D`
reads in `e` as the closed half-space `{z | 0 ≤ ℓ z}`.

No regularity of `ρ` outside `U` is needed. The chart is the scalar submersion chart
`TauCeti.scalarSubmersionChartAt` of the restriction of `ρ` to `U`, which is smooth on all of `U`
and therefore lies in the maximal atlas of `U`, carried to `M` by the inclusion of `U`.

## Main results

* `TauCeti.IsRegularPoint.exists_partialDiffeomorph_normalForm`: a function that is `C^n` on an
  open set and regular at `p` is affine in a `C^n` partial diffeomorphism centred at `p`.
* `TauCeti.IsRegularPoint.exists_partialDiffeomorph_halfSpace`: a set with a local defining
  function regular at a zero `p` is a half-space in a `C^n` partial diffeomorphism centred at `p`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 4 (the rank theorem) and Proposition 5.47 (regular domains).
-/

public section

open Function Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω} [IsManifold I n M]
  {ρ : M → ℝ} {U : Set M} {p : M}

/-- **The submersion normal form in a partial diffeomorphism.** If `ρ` is `C^n`, `1 ≤ n`, on an
open set `U` and regular at `p ∈ U`, then there are a `C^n` partial diffeomorphism `e` from a
neighbourhood of `p` inside `U` onto an open subset of the model space, with `e p = 0`, and a
nonzero continuous linear functional `ℓ` such that `ρ (e.symm z) = ℓ z + ρ p` on the target
of `e`. -/
theorem IsRegularPoint.exists_partialDiffeomorph_normalForm (hreg : IsRegularPoint I 𝓘(ℝ) ρ p)
    (hn : 1 ≤ n) (hU : IsOpen U) (hρ : ContMDiffOn I 𝓘(ℝ) n ρ U) (hp : p ∈ U) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, E) M E n, p ∈ e.source ∧ e.source ⊆ U ∧ e p = 0 ∧
      ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ z ∈ e.target, ρ (e.symm z) = ℓ z + ρ p := by
  let V : Opens M := ⟨U, hU⟩
  let f : V → ℝ := ρ ∘ Subtype.val
  let q : V := ⟨p, hp⟩
  have hf : ContMDiff I 𝓘(ℝ) n f := hρ.comp_contMDiff contMDiff_subtype_val fun x ↦ x.2
  have hf1 : ContMDiffAt I 𝓘(ℝ) 1 f q := (hf q).of_le hn
  have hregf : IsRegularPoint I 𝓘(ℝ) f q := hreg.comp <| isRegularPoint_iff.2
    ((isLocalDiffeomorph_subtype_val (I := I) (n := 1) (U := V) q).isInvertible_mfderiv
      one_ne_zero).surjective
  let Φ := (scalarSubmersionChartAt hf1 hregf).toPartialDiffeomorphOfMemMaximalAtlas
    (scalarSubmersionChartAt_mem_maximalAtlas hf1 hregf fun x _ ↦ hf x)
  have hi := isLocalDiffeomorph_subtype_val (I := I) (n := n) (U := V) q
  let Ψ := hi.localInverse
  have hval {w : V} (hw : w ∈ Ψ.target) : Ψ.symm w = w := by
    have h := hi.localInverse_right_inv (Ψ.map_target hw)
    rw [Ψ.right_inv hw] at h
    exact h.symm
  have hΨp : Ψ p = q := hi.localInverse_left_inv hi.localInverse_mem_target
  have hqΦ : q ∈ Φ.source := by
    rw [OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_source]
    exact mem_scalarSubmersionChartAt_source hf1 hregf
  refine ⟨Ψ.trans Φ, ⟨hi.localInverse_mem_source, show Ψ p ∈ Φ.source from hΨp ▸ hqΦ⟩,
    fun x hx ↦ ?_, ?_, fderiv ℝ (f ∘ (extChartAt I q).symm) (extChartAt I q q), fun h ↦ ?_,
    fun z hz ↦ ?_⟩
  · rw [← hi.localInverse_right_inv hx.1]
    exact (Ψ x).2
  · change Φ (Ψ p) = 0
    rw [hΨp, OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_apply]
    exact scalarSubmersionChartAt_extend_self hf1 hregf
  · obtain ⟨v, hv⟩ := hregf.surjective_fderiv_comp_extChartAt_symm 1
    rw [h, zero_apply] at hv
    exact zero_ne_one hv
  · have hw : Φ.symm z ∈ Ψ.target := hz.2
    have hzΦ : z ∈ ((scalarSubmersionChartAt hf1 hregf).extend I).target := by
      have h : z ∈ Φ.target := hz.1
      rw [OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_target] at h
      rwa [OpenPartialHomeomorph.extend_target, I.range_eq_univ, inter_univ]
    change ρ (Ψ.symm (Φ.symm z)) = _
    rw [hval hw, PartialDiffeomorph.symm_toPartialEquiv,
      OpenPartialHomeomorph.toPartialDiffeomorphOfMemMaximalAtlas_symm_apply,
      ← comp_apply (f := (scalarSubmersionChartAt hf1 hregf).symm),
      ← OpenPartialHomeomorph.extend_coe_symm]
    exact apply_scalarSubmersionChartAt_extend_symm hf1 hregf hzΦ

/-- **Half-space charts from a local defining function.** Let `ρ` be `C^n`, `1 ≤ n`, on an open set
`U`, on which a set `D` is the superlevel set `{ρ ≥ 0}`, and let `p ∈ U` be a regular zero of
`ρ`. Then there are a `C^n` partial diffeomorphism `e` from a neighbourhood of `p` inside `U` onto
an open subset of the model space, with `e p = 0`, and a nonzero continuous linear functional `ℓ`
such that `D` reads in `e` as the half-space `{z | 0 ≤ ℓ z}`. -/
theorem IsRegularPoint.exists_partialDiffeomorph_halfSpace (hreg : IsRegularPoint I 𝓘(ℝ) ρ p)
    (hn : 1 ≤ n) (hU : IsOpen U) (hρ : ContMDiffOn I 𝓘(ℝ) n ρ U) (hp : p ∈ U) (hρp : ρ p = 0)
    {D : Set M} (hD : ∀ x ∈ U, x ∈ D ↔ 0 ≤ ρ x) :
    ∃ e : PartialDiffeomorph I 𝓘(ℝ, E) M E n, p ∈ e.source ∧ e.source ⊆ U ∧ e p = 0 ∧
      ∃ ℓ : E →L[ℝ] ℝ, ℓ ≠ 0 ∧ ∀ z ∈ e.target, e.symm z ∈ D ↔ 0 ≤ ℓ z := by
  obtain ⟨e, hpe, heU, hep, ℓ, hℓ, he⟩ := hreg.exists_partialDiffeomorph_normalForm hn hU hρ hp
  refine ⟨e, hpe, heU, hep, ℓ, hℓ, fun z hz ↦ ?_⟩
  rw [hD _ (heU (e.symm.map_source hz)), he z hz, hρp, add_zero]

end TauCeti
