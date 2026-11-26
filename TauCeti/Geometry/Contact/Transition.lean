/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Proportional
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Transition functions for contact forms

Two nowhere-zero smooth real one-forms define the same hyperplane field exactly when one is a
unique nowhere-zero smooth function times the other. Applied on an overlap of contact charts,
this gives the transition function between their defining forms, without a metric or a chosen
transverse field. In particular, contactness depends only on the hyperplane field: a form with
the same hyperplanes as a contact form is contact. Multipliers of either sign are allowed:
preservation of a chosen coorientation would additionally require positivity.

On a compact manifold the multiplier can be pushed above `1` by a rescaling that is constant on
each connected component: if `β` has the same hyperplanes as `α`, then `c β = f α` for a locally
constant nowhere vanishing `c` and a smooth `f > 1`
(`TauCeti.SmoothForm.exists_isLocallyConstant_smul_eq_smul_one_lt`). The constant takes the sign
of the multiplier, so it reverses the coorientation where the two forms disagree. Such a rescaling
keeps the hyperplanes, and for contact forms it keeps the closed Reeb orbits as subsets, only
changing their speed and possibly their direction
(`TauCeti.SmoothForm.IsContactForm.isMIntegralCurve_comp_mul_of_eq_smul_of_isLocallyConstant`).
This is how Barraud–Damian–Humilière–Oancea, in the proof of their Corollary E, bring an arbitrary
contact form defining a contact structure `ξ = ker α₀` to a form `f α₀` with `f > 1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, proof of Corollary E.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {α β : SmoothForm I M ℝ 1}

/-- A smooth one-form has the same hyperplanes as a nowhere-zero smooth one-form exactly when it
is a unique nowhere-zero smooth multiple of it. This applies, in particular, to local defining
forms restricted to an overlap. -/
theorem kerDistribution_eq_iff_existsUnique_fun_smul (hα : ∀ x, α.val x ≠ 0) :
    β.kerDistribution = α.kerDistribution ↔
      ∃! f : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ f ∧ (∀ x, f x ≠ 0) ∧
        ∀ x, β.val x = f x • α.val x := by
  constructor
  · intro hker
    have hle (x : M) : RoughForm.ker α.val x ≤ RoughForm.ker β.val x := by
      intro v hv
      simpa only [RoughForm.mem_ker, ← mem_kerDistribution, hker] using hv
    obtain ⟨f, ⟨hf, hmul⟩, huniq⟩ := existsUnique_fun_smul_of_ker_le hα hle
    have hf₀ (x : M) : f x ≠ 0 := by
      intro hz
      exact hα x ((apply_eq_zero_iff_of_kerDistribution_eq hker x).mp
        (by rw [hmul, hz, zero_smul]))
    exact ⟨f, ⟨hf, hf₀, hmul⟩, fun g hg ↦ huniq g ⟨hg.1, hg.2.2⟩⟩
  · rintro ⟨f, ⟨_, hf₀, hmul⟩, _⟩
    exact kerDistribution_of_eq_smul hf₀ hmul

/-- A smooth form with the same hyperplanes as a contact form is itself contact. -/
theorem IsContactForm.isContactForm_of_kerDistribution_eq (hα : α.IsContactForm)
    (hker : β.kerDistribution = α.kerDistribution) : β.IsContactForm := by
  obtain ⟨f, ⟨hf, hf₀, hmul⟩, _⟩ :=
    (kerDistribution_eq_iff_existsUnique_fun_smul hα.apply_ne_zero).mp hker
  exact (isContactForm_iff_of_eq_smul (hf.of_le (by simp)) hf₀ hmul).mpr hα

/-- **Rescaling a form with the same hyperplanes to a multiplier above `1`.** Let `α` be a nowhere
vanishing smooth one-form on a compact manifold and `β` a smooth one-form with the same
hyperplanes. Multiplying `β` by a nonzero constant on each connected component, through a locally
constant nowhere vanishing `c`, makes it `f α` for a smooth `f > 1`. The constant `c` has the sign
of the multiplier `β / α`, and its modulus is twice the reciprocal of the least modulus of the
multiplier, which exists by compactness. -/
theorem exists_isLocallyConstant_smul_eq_smul_one_lt [CompactSpace M] (hα : ∀ x, α.val x ≠ 0)
    (hker : β.kerDistribution = α.kerDistribution) :
    ∃ c f : M → ℝ, IsLocallyConstant c ∧ (∀ x, c x ≠ 0) ∧ ContMDiff I 𝓘(ℝ) ∞ f ∧
      (∀ x, 1 < f x) ∧ ∀ x, c x • β.val x = f x • α.val x := by
  obtain ⟨g, ⟨hg, hg₀, hβ⟩, -⟩ := (kerDistribution_eq_iff_existsUnique_fun_smul hα).1 hker
  -- A lower bound `m > 0` for `|g|` on the compact `M`.
  obtain ⟨m, hm, hgm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x, m ≤ |g x| := by
    rcases isEmpty_or_nonempty M with hM | hM
    · exact ⟨1, one_pos, fun x ↦ isEmptyElim x⟩
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
      hg.continuous.abs.continuousOn
    exact ⟨|g x₀|, abs_pos.2 (hg₀ x₀), fun x ↦ hx₀ (Set.mem_univ x)⟩
  -- Rescale by `± 2 / m`, with the sign of `g`, which is locally constant.
  set c : M → ℝ := fun x ↦ if 0 < g x then 2 / m else -(2 / m) with hc_def
  have hc : IsLocallyConstant c := by
    refine (IsLocallyConstant.iff_eventually_eq c).2 fun x ↦ ?_
    rcases (hg₀ x).lt_or_gt with hx | hx
    · filter_upwards [hg.continuous.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      simp [hc_def, hy.le.not_gt, hx.le.not_gt]
    · filter_upwards [hg.continuous.continuousAt.eventually (lt_mem_nhds hx)] with y hy
      simp [hc_def, hy, hx]
  have hcg (x : M) : c x * g x = 2 / m * |g x| := by
    rcases (hg₀ x).lt_or_gt with hx | hx
    · simp [hc_def, hx.le.not_gt, abs_of_neg hx]
    · simp [hc_def, hx, abs_of_pos hx]
  refine ⟨c, fun x ↦ c x * g x, hc, fun x ↦ ?_, hc.contMDiff.mul hg, fun x ↦ ?_, fun x ↦ ?_⟩
  · by_cases hx : 0 < g x <;> simp [hc_def, hx, hm.ne']
  · dsimp only
    rw [hcg]
    calc (1 : ℝ) < 2 := one_lt_two
      _ = 2 / m * m := by field_simp
      _ ≤ 2 / m * |g x| := by gcongr; exact hgm x
  · dsimp only
    rw [hβ, smul_smul]

end TauCeti.SmoothForm
