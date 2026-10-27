/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Factorization
public import TauCeti.Analysis.Analytic.Laurent.Conjugation
import TauCeti.Analysis.Polynomial.Conjugation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Conjugation symmetry of constructed Laurent factorizations

A conjugation-compatible nonmonic polynomial family admits a Puiseux Laurent factorization
whose labels, integer exponents, and local analytic units all respect conjugation. The
exponents are independent of the base parameter. Units at two conjugate parameters agree
after conjugation on a full neighborhood, including the exceptional hyperplane; the base
parameters need not be fixed points of the involution.

The branches are constructed by `exists_analyticOnNhd_nonmonic_laurent`. The unique
conjugation permutation of a distinct root labelling then acts on those same branches.
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
            (∀ x i, AnalyticAt ℂ (w x i) (x.1, 0) ∧ w x i (x.1, 0) ≠ 0) ∧
            (∀ x, ∀ᶠ b in 𝓝 (x.1, (0 : ℂ)), (∀ i, w x i b ≠ 0) ∧
              (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * w x i b)) ∧
            ∀ x i, ∀ᶠ b in 𝓝 (x.1, (0 : ℂ)),
              w x (σ i) b = conj (w ⟨τ x.1, hτU x.2⟩ i (τ b.1, conj b.2)) := by
  obtain ⟨R', hR', hfit, r, g, hra, hg, hr, e, he⟩ :=
    exists_analyticOnNhd_nonmonic_laurent hU hR hF hdeg hdiscr hu hu0 hv hv0 hlead hconst
  choose w hbound hwa hw0 hwform using fun x : U ↦ he x.1 x.2
  let S := U ×ˢ (ball (0 : ℂ) R' \ {0})
  let T := U ×ˢ ball (0 : ℂ) R'
  let κ : E × ℂ → E × ℂ := fun b ↦ (τ b.1, conj b.2)
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ d.factorial)
  have hST : S ⊆ T := prod_mono subset_rfl sdiff_subset
  have hq : MapsTo q S (U ×ˢ (ball 0 R \ {0})) := by
    intro b hb
    exact ⟨hb.1, mapsTo_pow_ball_zero d.factorial_ne_zero hfit hb.2.1,
      pow_ne_zero _ hb.2.2⟩
  have hconjBall : MapsTo conj (ball (0 : ℂ) R') (ball 0 R') := by
    intro z hz
    simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
  have hκ : ContinuousOn κ T := hτ.prodMap Complex.continuous_conj.continuousOn
  have hκT : MapsTo κ T T := hτU.prodMap hconjBall
  have hκS : MapsTo κ S S :=
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩
  have hroot (b : E × ℂ) (hb : b ∈ S) (z : ℂ) :
      (F (q b)).IsRoot z ↔ ∃ i, r i b = z := by
    have hl : (F (q b)).coeff d ≠ 0 := by
      rw [hlead _ ⟨(hq hb).1, (hq hb).2.1⟩]
      exact mul_ne_zero (pow_ne_zero _ (hq hb).2.2) (hu0 _ ⟨(hq hb).1, (hq hb).2.1⟩)
    rw [(hr b hb).2, root_mul, iff_false_intro (not_isRoot_C _ z hl),
      false_or, isRoot_prod]
    simp [sub_eq_zero, eq_comm]
  -- The punctured product is connected; conjugation therefore uses one permutation.
  let := isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_ball_sdiff_singleton (by simp [Complex.rank_real_complex])
      (0 : ℂ) hR')
  have hSc : IsPreconnected S :=
    (isPreconnected_iff_preconnectedSpace.2 inferInstance).prod
      (isPreconnected_iff_preconnectedSpace.2 inferInstance)
  obtain ⟨x₀⟩ : Nonempty U := inferInstance
  obtain ⟨t₀⟩ : Nonempty ↥(ball (0 : ℂ) R' \ {0}) := inferInstance
  obtain ⟨σ, ⟨hσσ, hσ⟩, -⟩ := TauCeti.existsUnique_root_conj_perm_of_subset_closure
    hSc subset_rfl subset_closure (fun i ↦ (hra i).continuousOn)
    (fun b hb ↦ (hr b hb).1) hroot (hκ.mono hST) hκS hκS
    (fun b hb ↦ Prod.ext (hττ b.1 hb.1) (Complex.conj_conj b.2))
    (fun b hb ↦ by simpa only [q, κ, map_pow] using hconj _ (hq hb))
    ⟨(x₀, t₀), x₀.2, t₀.2⟩
  have hgfull (i : Fin d) : EqOn (g (σ i)) (fun b ↦ conj (g i (κ b))) T := by
    refine TauCeti.eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball
      (hg (σ i)).1.continuousOn
      (Complex.continuous_conj.comp_continuousOn ((hg i).1.continuousOn.comp hκ hκT)) ?_
    intro b hb
    simp only [(hg (σ i)).2 hb, (hg i).2 (hκS hb), hσ i b hb,
      κ, map_mul, map_pow, Complex.conj_conj]
  -- Compare units at `x` and `τ x`; a fixed point of `τ` is unnecessary.
  have hcompat (x : U) (i : Fin d) : e (σ i) = e i ∧
      ∀ᶠ b in 𝓝 (x.1, (0 : ℂ)),
        w x (σ i) b = conj (w ⟨τ x.1, hτU x.2⟩ i (τ b.1, conj b.2)) := by
    have hκt : Tendsto κ (𝓝 (x.1, (0 : ℂ))) (𝓝 (τ x.1, (0 : ℂ))) := by
      simpa only [κ, Prod.map_def, map_zero] using
        (hτ.continuousAt (hU.mem_nhds x.2)).tendsto.prodMap_nhds
          (Complex.continuous_conj.tendsto (0 : ℂ))
    apply ((hwa x (σ i)).restrictScalars (𝕜 := ℝ)).laurent_eq_of_conj (hw0 x (σ i))
      ((hwa ⟨τ x.1, hτU x.2⟩ i).restrictScalars (𝕜 := ℝ)) (hw0 _ i)
      (hτ.continuousAt (hU.mem_nhds x.2))
    filter_upwards [hwform x, hκt.eventually (hwform ⟨τ x.1, hτU x.2⟩),
      (hU.prod isOpen_ball).mem_nhds (x := (x.1, (0 : ℂ))) ⟨x.2, mem_ball_self hR'⟩]
      with b hb hκb hbT hb0
    rw [← hb.2 hb0 (σ i), hσ i b ⟨hbT.1, hbT.2, hb0⟩,
      hκb.2 (by simpa only [κ, ne_eq, map_eq_zero] using hb0) i]
  exact ⟨R', hR', hfit, r, g, hra, hg, hr, σ, hσσ, hσ, hgfull,
    e, w, hbound x₀, fun i ↦ (hcompat x₀ i).1,
    fun x i ↦ ⟨hwa x i, hw0 x i⟩, hwform, fun x i ↦ (hcompat x i).2⟩

end TauCeti.Polynomial
