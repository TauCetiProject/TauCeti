/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Nonmonic.Multiplicity
public import TauCeti.Analysis.Polynomial.RealRoots.Descent

/-!
# Ordered real roots of finite nonmonic Laurent limits

The finite limits of a nonmonic Puiseux splitting give strictly ordered real analytic root
sections of a nonzero divided central-fiber family, with constant positive multiplicities.
Branches with negative Laurent exponent contribute no finite root. Repeated finite limits
are allowed and are removed by one fixed selection of labels on a common open neighborhood.

The complex root multiset of the real divided family is an input along the real parameter
space: for Lazard evaluations it is supplied by
`MvPolynomial.roots_lazardEval_eq_map_of_laurent`. This family need not be the ordinary
central fiber, which can be nullified. Nonzeroness of the divided family is required
separately, including when there are no finite branches. Reality of the selected labels,
their strict ordering, and constancy of their multiplicities are conclusions.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, §5.2, proof of Theorem 5.1.
-/

public section

open Filter Polynomial Set Topology

namespace TauCeti

variable {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Finite Laurent limits of a prepared nonmonic splitting descend to a complete, strictly
ordered analytic list of real roots of a nonzero divided central-fiber family. Every section
has constant positive multiplicity on one open neighborhood. The real label set and distinct
root count are derived, and an empty finite-label set or an empty real-root set is allowed.

For Lazard evaluation, `MvPolynomial.roots_lazardEval_eq_map_of_laurent` supplies the root
multiset identity; this statement concerns the real divided family `F`, not a possibly zero
ordinary central fiber of `P`. Analyticity of the Laurent amplitudes `w i` is required only
for the finite branches. -/
theorem exists_analyticOnNhd_ordered_real_roots_of_finite_laurent_limits
    {d a c : ℕ} {P : E × ℂ → ℂ[X]} {r s : Fin d → E × ℂ → ℂ}
    {φ : B → E} {b₀ : B} {F : B → ℝ[X]}
    {u v : E × ℂ → ℂ} {e : Fin d → ℤ} {w : Fin d → E × ℂ → ℂ}
    (hs : ∀ i, AnalyticAt ℂ (s i) (φ b₀, 0))
    (hu : AnalyticAt ℂ u (φ b₀, 0)) (hu0 : u (φ b₀, 0) ≠ 0)
    (hv : AnalyticAt ℂ v (φ b₀, 0)) (hv0 : v (φ b₀, 0) ≠ 0)
    (hnorm : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).integralNormalization = ∏ i, (X - C (s i p)))
    (hlead : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).coeff d = p.2 ^ c * v p)
    (hdiscr : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      (P p).discr = p.2 ^ a * u p)
    (hscale : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, 0 ≤ e i → (P p).coeff d * r i p = s i p)
    (hw : ∀ i, 0 ≤ e i → AnalyticAt ℂ (w i) (φ b₀, 0))
    (hLaurent : ∀ᶠ p in 𝓝 (φ b₀, (0 : ℂ)), p.2 ≠ 0 →
      ∀ i, 0 ≤ e i → r i p = p.2 ^ e i * w i p)
    (hroots : ∀ᶠ b in 𝓝 b₀, ((F b).map (algebraMap ℝ ℂ)).roots =
      (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
        (fun i ↦ if e i = 0 then w i (φ b, 0) else 0))
    (hF : ∀ᶠ b in 𝓝 b₀, F b ≠ 0)
    (hφ : AnalyticAt ℝ φ b₀) :
    ∃ k : ℕ, ∃ t : Fin k → B → ℝ, ∃ U : Set B, IsOpen U ∧ b₀ ∈ U ∧
      (∀ b ∈ U, F b ≠ 0) ∧
      (∀ i, AnalyticOnNhd ℝ (t i) U) ∧
      (∀ b ∈ U, StrictMono (fun i ↦ t i b)) ∧
      (∀ b ∈ U, ∀ z, (F b).IsRoot z ↔ ∃ i, t i b = z) ∧
      (∀ i, 0 < (F b₀).rootMultiplicity (t i b₀)) ∧
      ∀ b ∈ U, ∀ i,
        (F b).rootMultiplicity (t i b) = (F b₀).rootMultiplicity (t i b₀) := by
  classical
  let I := {i : Fin d // 0 ≤ e i}
  let f : I → B → ℂ := fun i b ↦ if e i.val = 0 then w i.val (φ b, 0) else 0
  have hf (i : I) : AnalyticAt ℝ (f i) b₀ := by
    by_cases he : e i.val = 0
    · simpa [f, he, Function.comp_def] using
        (((hw i.val i.property).restrictScalars (𝕜 := ℝ)).comp_of_eq
          (hφ.prod (analyticAt_const (v := (0 : ℂ)))) rfl)
    · simpa [f, he] using (analyticAt_const (v := (0 : ℂ)))
  have hcollision : ∀ᶠ b in 𝓝 b₀, ∀ i j : I,
      f i b = f j b ↔ f i b₀ = f j b₀ := by
    have hc := hφ.continuousAt.tendsto.eventually
      (eventually_finite_laurent_limit_eq_iff hs hu hu0 hv hv0 hnorm
        (by simpa only [sub_zero] using hlead)
        (by simpa only [sub_zero] using hdiscr) hscale hw
        (by simpa only [sub_zero] using hLaurent))
    filter_upwards [hc] with b hb i j
    exact hb i.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.property⟩)
      j.val (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.property⟩)
  have hroots' : ∀ᶠ b in 𝓝 b₀, ((F b).map (algebraMap ℝ ℂ)).roots =
      Finset.univ.val.map (fun i ↦ f i b) := by
    filter_upwards [hroots] with b hb
    simpa only [f, ← Finset.univ_val_map_subtype_restrict,
      Subtype.restrict_def, Function.comp_def] using hb
  exact exists_analyticOnNhd_ordered_real_roots_of_persistent_collisions
    (fun i ↦ (hf i).continuousAt)
    (fun i ↦ Complex.reCLM.analyticAt _ |>.comp (hf i)) hroots' hF hcollision

end TauCeti
