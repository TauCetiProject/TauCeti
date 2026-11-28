/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Regularity
public import TauCeti.Analysis.Complex.Wirtinger.Regularity.Holder
public import TauCeti.Analysis.Sobolev.Local.Morrey
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Normed.Operator.Holder

/-!
# Continuous weak solutions of linear Cauchy–Riemann equations are classical

Let `Ω ⊆ ℂ` be open. This file upgrades *continuous* distributional solutions of `\bar∂` equations
on `Ω` to classical ones, in two steps.

* **Hölder continuity.** If `u` is continuous on `Ω` and solves `\bar∂u = g` in the sense of
  distributions, with `g` locally `Lᵖ` on `Ω` for some `2 < p < ∞`, then `u` is Hölder continuous
  with exponent `1 - 2 / p` on every compact subset of `Ω`
  (`TauCeti.HasWeakConjWirtingerDerivOn.exists_holderOnWith_of_memLpLoc`). Indeed `u` lies in
  `W^{1,p}_loc(Ω)` (`TauCeti.HasWeakConjWirtingerDerivOn.memWkpLoc_one`), so its precise
  representative is Hölder on compact sets by Morrey's embedding
  (`TauCeti.MemWkpLoc.exists_holderOnWith_preciseRepresentative_of_isCompact`), and a continuous
  function is its own precise representative.
* **Linear equations with Hölder coefficients.** If `u : ℂ → ℂ` is continuous on `Ω` and solves
  the real-linear equation

  `\bar∂u + a u + b \bar u = 0`

  in the sense of distributions, with coefficients `a`, `b` that are `α`-Hölder on every compact
  subset of `Ω`, then `u` is `C¹` on `Ω`, solves the equation at every point of `Ω`, and its
  derivative is Hölder with exponent `min α (1 / 2)` on compact subsets of `Ω`
  (`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_linear_of_holderOnWith`). The right
  side `-(a u + b \bar u)` is continuous, hence locally `L⁴`, so `u` is `1 / 2`-Hölder on compact
  sets by the first step; then the right side is Hölder of exponent `min α (1 / 2)` on compact sets,
  and the interior Schauder estimate for `\bar∂`
  (`TauCeti.HasWeakConjWirtingerDerivOn.contDiffOn_one_of_holderOnWith`) applies.

The second statement is how continuous solutions obtained by gluing or by limits, which a priori
solve a linear Cauchy–Riemann equation only distributionally, for instance across an isolated point
(`TauCeti.HasWeakConjWirtingerDerivOn.of_diff_singleton`), are shown to be classical.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B (elliptic regularity for the Cauchy–Riemann operator).
-/

public section

noncomputable section

open Complex Metric MeasureTheory Set TopologicalSpace TauCeti.MeasureTheory
open scoped NNReal ENNReal ComplexConjugate

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {Ω : Opens ℂ} {u g : ℂ → F} {p : ℝ≥0∞}

/-- **Continuous weak solutions are Hölder.** For `2 < p < ∞`, a map `u` continuous on `Ω` that
solves `\bar∂u = g` in the sense of distributions on `Ω`, with `g` locally `Lᵖ` on `Ω`, is Hölder
continuous with exponent `1 - 2 / p` on every compact subset of `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.exists_holderOnWith_of_memLpLoc (hp : 2 < p)
    (hp_top : p ≠ ∞) (h : HasWeakConjWirtingerDerivOn volume Ω u g) (hu : ContinuousOn u Ω)
    (hg : MemLpLoc p Ω g) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal u K := by
  have hW : MemWkpLoc p Ω 1 u :=
    h.memWkpLoc_one (ENNReal.one_lt_two.trans hp) hp_top hu.memLpLoc hg
  obtain ⟨C, hC⟩ := hW.exists_holderOnWith_preciseRepresentative_of_isCompact hp hK hKΩ
  -- a continuous function is its own precise representative
  have heq : EqOn (preciseRepresentative volume u) u Ω :=
    eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
      (hu.locallyIntegrableOn Ω.isOpen.measurableSet) Filter.EventuallyEq.rfl hu
  exact ⟨C, hC.congr (heq.mono hKΩ)⟩

/-- **Continuous weak solutions of linear Cauchy–Riemann equations are classical.** Let `u` be
continuous on `Ω` and solve `\bar∂u + a u + b \bar u = 0` in the sense of distributions on `Ω`,
where the coefficients `a` and `b` are `α`-Hölder on every compact subset of `Ω` for some `α > 0`.
Then `u` is `C¹` on `Ω`, solves the equation at every point of `Ω`, and its derivative is Hölder
with exponent `min α (1 / 2)` on every compact subset of `Ω`. -/
theorem HasWeakConjWirtingerDerivOn.contDiffOn_one_of_linear_of_holderOnWith {u a b : ℂ → ℂ}
    {α : ℝ≥0} (hα : 0 < α)
    (h : HasWeakConjWirtingerDerivOn volume Ω u fun z ↦ -(a z * u z + b z * conj (u z)))
    (hu : ContinuousOn u Ω) (ha : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α a K)
    (hb : ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C α b K) :
    ContDiffOn ℝ 1 u Ω ∧ (∀ z ∈ Ω, conjWirtingerDeriv u z 1 + a z * u z + b z * conj (u z) = 0) ∧
      ∀ K ⊆ (Ω : Set ℂ), IsCompact K → ∃ C, HolderOnWith C (min α 2⁻¹) (fderiv ℝ u) K := by
  set γ : ℝ≥0 := min α 2⁻¹
  have hγ : 0 < γ := lt_min hα (by norm_num)
  have hγ1 : γ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  -- the right side is continuous, hence locally `L⁴`, so `u` is `1 / 2`-Hölder on compact sets
  have hg : ContinuousOn (fun z ↦ -(a z * u z + b z * conj (u z))) Ω := by
    have hac := continuousOn_of_forall_isCompact_holderOnWith Ω.isOpen hα ha
    have hbc := continuousOn_of_forall_isCompact_holderOnWith Ω.isOpen hα hb
    exact ((hac.mul hu).add (hbc.mul (Complex.continuous_conj.comp_continuousOn hu))).neg
  have hexp : ((1 : ℝ≥0∞) - 2 / 4).toNNReal = 2⁻¹ := by
    rw [ENNReal.toNNReal_sub (ENNReal.div_ne_top (by simp) (by simp)), ENNReal.toNNReal_div,
      ENNReal.toNNReal_ofNat, ENNReal.toNNReal_ofNat, ENNReal.toNNReal_one, ← NNReal.coe_inj]
    norm_num [NNReal.coe_sub]
  -- on a compact set the right side is `γ`-Hölder
  have hgH : ∀ K ⊆ (Ω : Set ℂ), IsCompact K →
      ∃ C, HolderOnWith C γ (fun z ↦ -(a z * u z + b z * conj (u z))) K := by
    intro K hKΩ hK
    obtain ⟨Cu, hCu⟩ := h.exists_holderOnWith_of_memLpLoc (p := 4) (by norm_num) (by simp) hu
      hg.memLpLoc hK hKΩ
    rw [hexp] at hCu
    obtain ⟨Ca, hCa⟩ := ha K hKΩ hK
    obtain ⟨Cb, hCb⟩ := hb K hKΩ hK
    -- lower all exponents to `γ`, then multiply on the compact set `K`
    obtain ⟨_, hu'⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨_, hCu⟩ (min_le_right _ _)
      hK.isBounded
    obtain ⟨_, hc'⟩ := HolderOnWith.exists_holderOnWith_of_le
      ⟨_, Complex.conjLIE.lipschitzWith.comp_holderOnWith hCu⟩ (min_le_right _ _) hK.isBounded
    obtain ⟨_, ha'⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨_, hCa⟩ (min_le_left _ _)
      hK.isBounded
    obtain ⟨_, hb'⟩ := HolderOnWith.exists_holderOnWith_of_le ⟨_, hCb⟩ (min_le_left _ _)
      hK.isBounded
    obtain ⟨_, hau⟩ := (ContinuousLinearMap.mul ℂ ℂ).exists_holderOnWith_comp₂_of_isCompact hK hγ
      ha' hu'
    obtain ⟨_, hbc⟩ := (ContinuousLinearMap.mul ℂ ℂ).exists_holderOnWith_comp₂_of_isCompact hK hγ
      hb' hc'
    exact ⟨_, (hau.add hbc).neg.congr fun z _ ↦ by simp⟩
  obtain ⟨h1, h2, h3⟩ := h.contDiffOn_one_of_holderOnWith hγ hγ1 hu hgH
  exact ⟨h1, fun z hz ↦ by rw [h2 z hz]; ring, h3⟩

end TauCeti
