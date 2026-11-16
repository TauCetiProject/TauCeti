/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Parametric
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Analysis.Calculus.Morse.LocalNormalForm
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Ball
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The parametric Morse lemma along the whole zero section

The canonical parametric Morse coordinate `TauCeti.parametricMorseCoord F (b, v) = R (b, v) v` of
`TauCeti.Analysis.Calculus.Morse.Parametric`, where `R (b, v)` is Palais's operator square root
comparing the averaged vertical Hessian with the vertical Hessian at `(b, 0)`, is determined by the
family `F` alone, with no choices. It also only depends on `F` along the segment from `(b, 0)` to
`(b, v)` (`TauCeti.parametricMorseCoord_congr_of_eqOn`). So the local normal forms it gives near the
points of the zero section glue: over an open set `U` of the base on which the zero section is
critical and nondegenerate, `(b, v) ↦ (b, parametricMorseCoord F (b, v))` is a single `C^n` chart on
a neighbourhood of the whole zero section over `U`, in which `F` is its vertical Hessian quadratic
form (`TauCeti.exists_parametricMorseCoord_chart`). The family need only be `C^{n+2}` on an open set
containing the zero section over `U`. The source of the chart is a union of products of open sets of
the base with balls about `0`; over each base point these balls are nested, so the chart is
injective (`TauCeti.exists_partialDiffeomorph_source_eq_biUnion_prod_ball`).

## Main declarations

* `TauCeti.exists_parametricMorseCoord_partialDiffeomorph_prod_ball`: near a point of the zero
  section, the canonical map is a partial diffeomorphism on a product of an open set with a ball.
* `TauCeti.exists_parametricMorseCoord_chart`: the parametric Morse lemma along the whole zero
  section over an open set of the base, in a single chart given by the canonical coordinate.

## References

* R. S. Palais, *Morse theory on Hilbert manifolds*, Topology **2** (1963), 299--340, Section 2,
  for the operator square root.
* R. S. Palais, *The Morse lemma for Banach spaces*, Bull. Amer. Math. Soc. **75** (1969),
  968--971.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

section Chart

variable [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] {F : P × E → ℝ} {W : Set (P × E)}
  {U : Set P} {n : ℕ∞}

/-- **The local parametric Morse chart on a product with a ball.** Let `F (b, v)` be `C^{n+2}`,
with `1 ≤ n ≤ ∞`, on a neighbourhood `W` of `(b₀, 0)`, with zero section critical near `b₀` and
invertible vertical Hessian at `(b₀, 0)`. Then the canonical map
`(b, v) ↦ (b, parametricMorseCoord F (b, v))` is a `C^n` partial diffeomorphism `Θ` on a source
`U₀ ×ˢ ball 0 r ⊆ W`, with `U₀` an open neighbourhood of `b₀`, on which `F` is in normal form. -/
theorem exists_parametricMorseCoord_partialDiffeomorph_prod_ball {b₀ : P} (hW : W ∈ 𝓝 (b₀, 0))
    (hF : ContDiffOn ℝ (n + 2) F W)
    (hcrit : ∀ᶠ b in 𝓝 b₀, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : (fderiv ℝ (fderiv ℝ (fun v ↦ F (b₀, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ (U₀ : Set P) (r : ℝ)
      (Θ : PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n),
      IsOpen U₀ ∧ b₀ ∈ U₀ ∧ 0 < r ∧ Θ.source = U₀ ×ˢ Metric.ball 0 r ∧
      U₀ ×ˢ Metric.ball 0 r ⊆ W ∧
      (∀ z ∈ U₀ ×ˢ Metric.ball 0 r, Θ z = (z.1, parametricMorseCoord F z)) ∧
      ∀ z ∈ U₀ ×ˢ Metric.ball 0 r, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0
          (parametricMorseCoord F z) (parametricMorseCoord F z) := by
  obtain ⟨ψ, U₀, V, hU₀, hV, hbU₀, h0V, hsource, hsubW, hψeq, -, -, -, hψ, hψsymm, hψF⟩ :=
    exists_parametric_morse_chart_of_contDiffOn hW hF hcrit hH hn
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV 0 h0V
  have hsub : U₀ ×ˢ Metric.ball (0 : E) r ⊆ ψ.source := hsource ▸ prod_mono le_rfl hrV
  let Θ := PartialDiffeomorph.ofOpenPartialHomeomorph ψ hψ hψsymm
  have hΘ := PartialDiffeomorph.ofOpenPartialHomeomorph_toPartialEquiv ψ hψ hψsymm
  have hΘψ : (Θ : P × E → P × E) = ψ :=
    (congrArg (fun e : PartialEquiv (P × E) (P × E) ↦ (e : P × E → P × E)) hΘ).trans
      ψ.coe_toPartialEquiv
  refine ⟨U₀, r, Θ.restrOpen (U₀ ×ˢ Metric.ball 0 r) (hU₀.prod Metric.isOpen_ball), hU₀, hbU₀,
    hr, ?_, (prod_mono le_rfl hrV).trans hsubW, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · rw [PartialDiffeomorph.restrOpen_source, congrArg PartialEquiv.source hΘ]
    exact inter_eq_right.mpr hsub
  · rw [PartialDiffeomorph.coe_restrOpen, hΘψ, hψeq z (hsub hz)]
  · have h := hψF z (hsub hz)
    rw [hψeq z (hsub hz)] at h
    exact h

/-- **The parametric Morse lemma along the whole zero section.** Let `F (b, v)` be `C^{n+2}`, with
`1 ≤ n ≤ ∞`, on an open set `W` containing the zero section over an open set `U` of the base,
with critical zero section and invertible vertical Hessian `H_b` at every `(b, 0)`, `b ∈ U`.
Then there is a single chart `ψ`, `C^n` in both directions and with source in `W` containing the
whole zero section over `U`, which is given on its source by the canonical parametric Morse
coordinate, `ψ (b, v) = (b, parametricMorseCoord F (b, v))`, preserves the base in both
directions, and puts `F` in normal form:
`F (b, v) = F (b, 0) + ½ H_b (ψ (b, v)).2 (ψ (b, v)).2`. -/
theorem exists_parametricMorseCoord_chart (hW : IsOpen W) (hF : ContDiffOn ℝ (n + 2) F W)
    (hU : IsOpen U) (hUW : ∀ b ∈ U, (b, (0 : E)) ∈ W)
    (hcrit : ∀ b ∈ U, fderiv ℝ (fun v ↦ F (b, v)) 0 = 0)
    (hH : ∀ b ∈ U, (fderiv ℝ (fderiv ℝ (fun v ↦ F (b, v))) 0).IsInvertible) (hn : n ≠ 0) :
    ∃ ψ : OpenPartialHomeomorph (P × E) (P × E),
      ψ.source ⊆ W ∧ (∀ b ∈ U, (b, (0 : E)) ∈ ψ.source) ∧
      (∀ z ∈ ψ.source, ψ z = (z.1, parametricMorseCoord F z)) ∧
      (∀ z ∈ ψ.target, (ψ.symm z).1 = z.1) ∧
      ContDiffOn ℝ n ψ ψ.source ∧ ContDiffOn ℝ n ψ.symm ψ.target ∧
      ∀ z ∈ ψ.source, F z = F (z.1, 0) + (2 : ℝ)⁻¹ *
        fderiv ℝ (fderiv ℝ (fun v ↦ F (z.1, v))) 0 (ψ z).2 (ψ z).2 := by
  -- Near each point `(b, 0)` of the zero section over `U`, the canonical map is a partial
  -- diffeomorphism on a product of an open set with a ball.
  have hloc := fun b (hb : b ∈ U) ↦
    exists_parametricMorseCoord_partialDiffeomorph_prod_ball (hW.mem_nhds (hUW b hb)) hF
      (Filter.mem_of_superset (hU.mem_nhds hb) hcrit) (hH b hb) hn
  have : Nonempty (PartialDiffeomorph 𝓘(ℝ, P × E) 𝓘(ℝ, P × E) (P × E) (P × E) n) :=
    ⟨(Diffeomorph.refl 𝓘(ℝ, P × E) (P × E) n).toPartialDiffeomorph⟩
  choose! U₀ r Θ hU₀ hbU₀ hr hΘsource hsubW hΘeq hnf using hloc
  -- These local partial diffeomorphisms glue along the nested balls of their sources.
  obtain ⟨Ψ, hΨsource, hΨ⟩ := exists_partialDiffeomorph_source_eq_biUnion_prod_ball
    (Φ := fun z : P × E ↦ (z.1, parametricMorseCoord F z)) (fun _ _ ↦ rfl) hU₀
    (fun b hb ↦ (hΘsource b hb).ge) fun b hb z hz ↦ (hΘeq b hb z hz).symm
  have hmem {z : P × E} : z ∈ Ψ.source ↔ ∃ b ∈ U, z ∈ U₀ b ×ˢ Metric.ball 0 (r b) := by
    simp only [hΨsource, mem_iUnion, exists_prop]
  let ψ := Ψ.toOpenPartialHomeomorph
  have hψ : (ψ : P × E → P × E) = fun z ↦ (z.1, parametricMorseCoord F z) :=
    (Ψ.toFun'_toOpenPartialHomeomorph).trans hΨ
  refine ⟨ψ, fun z hz ↦ ?_, fun b hb ↦ ?_, fun z _ ↦ by rw [hψ], fun z hz ↦ ?_,
    Ψ.contMDiffOn_toFun.contDiffOn, Ψ.contMDiffOn_invFun.contDiffOn, fun z hz ↦ ?_⟩
  · obtain ⟨b, hb, hzb⟩ := hmem.mp hz
    exact hsubW b hb hzb
  · exact hmem.mpr ⟨b, hb, hbU₀ b hb, Metric.mem_ball_self (hr b hb)⟩
  · -- the first coordinate of `ψ (ψ.symm z) = z` is that of `ψ.symm z`
    have h := congrArg Prod.fst (ψ.right_inv hz)
    rwa [hψ] at h
  · obtain ⟨b, hb, hzb⟩ := hmem.mp hz
    rw [hψ]
    exact hnf b hb z hzb

end Chart

end TauCeti
