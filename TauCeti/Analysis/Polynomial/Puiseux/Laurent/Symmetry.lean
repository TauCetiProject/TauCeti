/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Factorization
public import TauCeti.Analysis.Analytic.Laurent.Conjugation
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Polynomial.Puiseux.RootPermutation

/-!
# Conjugation symmetry of constructed Laurent factorizations

A conjugation-compatible nonmonic polynomial family admits a Puiseux Laurent factorization
whose labels, integer exponents, and local analytic units all respect conjugation. The
exponents are independent of the base parameter. Units at two conjugate parameters agree
after conjugation on a full neighborhood, including the exceptional hyperplane; the base
parameters need not be fixed points of the involution.

The branches are constructed by `exists_analyticOnNhd_nonmonic_laurent`. The unique
conjugation permutation of a distinct root labelling,
`existsUnique_root_conj_perm_of_powerSubstitution`, then acts on those same branches.
`AnalyticAt.laurent_eq_of_conj` identifies the exponents and unit germs at paired parameters.
No symmetry assumption on the leading or trailing coefficient units is needed. Original
fibers may drop degree or be nullified on the hyperplane.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §4, Corollary 4.2.
-/

public section

open Filter Function Metric Polynomial Set Topology ComplexConjugate

namespace TauCeti.Polynomial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {U : Set E} [SimplyConnectedSpace U] {F : E × ℂ → ℂ[X]} {d a c : ℕ} {R : ℝ}
  {u v : E × ℂ → ℂ} {τ : E → E}

/-- Construct a nonmonic Puiseux Laurent factorization with conjugation symmetry on the same
labels. Conjugation preserves the parameter-independent Laurent exponents and interchanges
the unit germs at paired base points. These unit identities hold across the exceptional
hyperplane, even for branches with poles. Degree zero and one are included. -/
theorem exists_analyticOnNhd_nonmonic_laurent_conj
    (hU : IsOpen U) (hR : 0 < R)
    (hF : ∀ i ≤ d, AnalyticOnNhd ℂ (fun b ↦ (F b).coeff i) (U ×ˢ ball 0 R))
    (hdeg : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).natDegree = d)
    (hdiscr : ∀ b ∈ U ×ˢ (ball 0 R \ {0}), (F b).discr ≠ 0)
    (hu : AnalyticOnNhd ℂ u (U ×ˢ ball 0 R))
    (hu0 : ∀ b ∈ U ×ˢ ball 0 R, u b ≠ 0)
    (hv : AnalyticOnNhd ℂ v (U ×ˢ ball 0 R))
    (hv0 : ∀ b ∈ U ×ˢ ball 0 R, v b ≠ 0)
    (hlead : ∀ b ∈ U ×ˢ ball 0 R, (F b).coeff d = b.2 ^ a * u b)
    (hconst : ∀ b ∈ U ×ˢ ball 0 R, (F b).coeff 0 = b.2 ^ c * v b)
    (hτ : ContinuousOn τ U) (hτU : MapsTo τ U U) (hττ : ∀ x ∈ U, τ (τ x) = x)
    (hconj : ∀ b ∈ U ×ˢ (ball 0 R \ {0}),
      F (τ b.1, conj b.2) = (F b).map (starRingEnd ℂ)) :
    ∃ R' : ℝ, 0 < R' ∧ R' ^ d.factorial ≤ R ∧
      ∃ r g : Fin d → E × ℂ → ℂ,
        (∀ i, AnalyticOnNhd ℂ (r i) (U ×ˢ (ball 0 R' \ {0}))) ∧
        (∀ i, AnalyticOnNhd ℂ (g i) (U ×ˢ ball 0 R') ∧
          EqOn (g i) (fun b ↦ b.2 ^ (d.factorial * a) * r i b)
            (U ×ˢ (ball 0 R' \ {0}))) ∧
        (∀ b ∈ U ×ˢ (ball 0 R' \ {0}),
          Injective (fun i ↦ r i b) ∧ F (b.1, b.2 ^ d.factorial) =
            C ((F (b.1, b.2 ^ d.factorial)).coeff d) * ∏ i, (X - C (r i b))) ∧
        ∃ σ : Equiv.Perm (Fin d), Involutive σ ∧
          (∀ i b, b ∈ U ×ˢ (ball 0 R' \ {0}) →
            r (σ i) b = conj (r i (τ b.1, conj b.2))) ∧
          (∀ i b, b ∈ U ×ˢ ball 0 R' → g (σ i) b = conj (g i (τ b.1, conj b.2))) ∧
          ∃ (e : Fin d → ℤ) (w : U → Fin d → E × ℂ → ℂ),
            (∀ i, -(d.factorial * a : ℤ) ≤ e i) ∧ (∀ i, e (σ i) = e i) ∧
            (∀ x i, AnalyticAt ℂ (w x i) (x.val, 0) ∧ w x i (x.val, 0) ≠ 0) ∧
            (∀ x, ∀ᶠ b in 𝓝 (x.val, (0 : ℂ)), (∀ i, w x i b ≠ 0) ∧
              (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w x i b)) ∧
            ∀ x i, ∀ᶠ b in 𝓝 (x.val, (0 : ℂ)),
              w x (σ i) b = conj (w ⟨τ x.val, hτU x.property⟩ i (τ b.1, conj b.2)) := by
  obtain ⟨R', hR', hfit, r, g, hra, hg, hr, e, W, hbound, hWa, hW0, hWform⟩ :=
    exists_analyticOnNhd_nonmonic_laurent hU hR hF hdeg hdiscr hu hu0 hv hv0 hlead hconst
  have hform (x : E) (hx : x ∈ U) : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      (∀ i, W i b ≠ 0) ∧ (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * W i b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds
      (x := (x, (0 : ℂ))) ⟨hx, mem_ball_self hR'⟩] with b hb
    exact ⟨fun i ↦ hW0 i b hb, fun hb0 i ↦ hWform b ⟨hb.1, hb.2, hb0⟩ i⟩
  obtain ⟨σ, ⟨hσσ, hσ⟩, -⟩ := existsUnique_root_conj_perm_of_powerSubstitution hR'
    d.factorial_ne_zero hfit (fun b hb ↦ hlead b ⟨hb.1, hb.2.1⟩ ▸
      mul_ne_zero (pow_ne_zero _ hb.2.2) (hu0 b ⟨hb.1, hb.2.1⟩))
    hτ hτU hττ hconj (fun i ↦ (hra i).continuousOn) hr
  obtain ⟨hκ, hκT, -⟩ := TauCeti.continuousOn_mapsTo_prodMap_conj hτ hτU
  obtain ⟨x₀⟩ : Nonempty U := inferInstance
  -- Compare units at `x` and `τ x`; a fixed point of `τ` is unnecessary.
  have hcompat (x : U) (i : Fin d) := AnalyticAt.laurent_eq_of_conj_of_forms
    (D₁ := r (σ i)) (D₂ := r i)
    ((hWa (σ i) _ ⟨x.property, mem_ball_self hR'⟩).restrictScalars (𝕜 := ℝ))
    (hW0 (σ i) _ ⟨x.property, mem_ball_self hR'⟩)
    ((hWa i _ ⟨hτU x.property, mem_ball_self hR'⟩).restrictScalars (𝕜 := ℝ))
    (hW0 i _ ⟨hτU x.property, mem_ball_self hR'⟩)
    (hτ.continuousAt (hU.mem_nhds x.property))
    ((hform x.val x.property).mono fun _ h hb ↦ h.2 hb (σ i))
    ((hform (τ x.val) (hτU x.property)).mono fun _ h hb ↦ h.2 hb i)
    (by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds
        (x := (x.val, (0 : ℂ))) ⟨x.property, mem_ball_self hR'⟩] with b hb hb0
      exact hσ i b ⟨hb.1, hb.2, hb0⟩)
  exact ⟨R', hR', hfit, r, g, hra, hg, hr, σ, hσσ, hσ,
    TauCeti.eqOn_conj_extension (τ := τ) (fun i ↦ (hg i).1.continuousOn) (fun i ↦ (hg i).2) hσ
      hκ hκT,
    e, fun _ ↦ W, hbound, fun i ↦ (hcompat x₀ i).1,
    fun x i ↦ ⟨hWa i _ ⟨x.property, mem_ball_self hR'⟩, hW0 i _ ⟨x.property, mem_ball_self hR'⟩⟩,
    fun x ↦ hform x.val x.property, fun x i ↦ (hcompat x i).2⟩

end TauCeti.Polynomial
