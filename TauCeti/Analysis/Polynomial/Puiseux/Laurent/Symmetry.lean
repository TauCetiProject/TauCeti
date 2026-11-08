/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Roots
public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Factorization
public import TauCeti.Analysis.Analytic.Laurent.Conjugation
import TauCeti.Analysis.Complex.RemovableSingularity
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

namespace TauCeti

/-- Two Laurent branches of conjugation-related roots, at paired base points `x` and `τ x`, have
the same exponent and conjugation-related unit germs near `(x, 0)`, including on the hyperplane
`z = 0`. The branch `r₂` has Laurent form `z ^ n * W₂` near `(x, 0)` and `r₁` has form
`z ^ m * W₁` near `(τ x, 0)`, with `r₂ b = conj (r₁ (τ b.1, conj b.2))` off the hyperplane. -/
theorem exponent_eq_and_unit_conj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {r₁ r₂ W₁ W₂ : E × ℂ → ℂ} {m n : ℤ} {τ : E → E} {x : E} (hτ : ContinuousAt τ x)
    (hW₂a : AnalyticAt ℂ W₂ (x, 0)) (hW₂0 : W₂ (x, 0) ≠ 0)
    (hW₁a : AnalyticAt ℂ W₁ (τ x, 0)) (hW₁0 : W₁ (τ x, 0) ≠ 0)
    (hform₂ : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 → r₂ b = b.2 ^ n * W₂ b)
    (hform₁ : ∀ᶠ b in 𝓝 (τ x, (0 : ℂ)), b.2 ≠ 0 → r₁ b = b.2 ^ m * W₁ b)
    (hr : ∀ᶠ b in 𝓝 (x, (0 : ℂ)), b.2 ≠ 0 → r₂ b = conj (r₁ (τ b.1, conj b.2))) :
    n = m ∧ ∀ᶠ b in 𝓝 (x, (0 : ℂ)), W₂ b = conj (W₁ (τ b.1, conj b.2)) := by
  have hκt : Tendsto (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (𝓝 (x, (0 : ℂ))) (𝓝 (τ x, (0 : ℂ))) := by
    simpa only [Prod.map_def, map_zero] using
      hτ.tendsto.prodMap_nhds (Complex.continuous_conj.tendsto (0 : ℂ))
  refine hW₂a.restrictScalars (𝕜 := ℝ) |>.laurent_eq_of_conj hW₂0
    (hW₁a.restrictScalars (𝕜 := ℝ)) hW₁0 hτ ?_
  filter_upwards [hform₂, hr, hκt.eventually hform₁] with b h₂ h₃ h₁ hb0
  rw [← h₂ hb0, h₃ hb0, h₁ (by simpa only [ne_eq, map_eq_zero] using hb0)]

/-- Two continuous extensions across the hyperplane `z = 0` of conjugation-related branches are
conjugation-related on the whole ball, provided the branches are on the punctured ball. -/
theorem eqOn_conj_comp_of_eqOn_punctured {E : Type*} [TopologicalSpace E]
    {U : Set E} {R' : ℝ} {k : ℕ} {τ : E → E}
    {g₁ g₂ r₁ r₂ : E × ℂ → ℂ} (hg₁ : ContinuousOn g₁ (U ×ˢ ball 0 R'))
    (hg₂ : ContinuousOn g₂ (U ×ˢ ball 0 R'))
    (he₁ : EqOn g₁ (fun b ↦ b.2 ^ k * r₁ b) (U ×ˢ (ball 0 R' \ {0})))
    (he₂ : EqOn g₂ (fun b ↦ b.2 ^ k * r₂ b) (U ×ˢ (ball 0 R' \ {0})))
    (hκ : ContinuousOn (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 R'))
    (hκT : MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ ball 0 R') (U ×ˢ ball 0 R'))
    (hκS : MapsTo (fun b : E × ℂ ↦ (τ b.1, conj b.2)) (U ×ˢ (ball 0 R' \ {0}))
      (U ×ˢ (ball 0 R' \ {0})))
    (hr : ∀ b ∈ U ×ˢ (ball 0 R' \ {0}), r₂ b = conj (r₁ (τ b.1, conj b.2))) :
    EqOn g₂ (fun b ↦ conj (g₁ (τ b.1, conj b.2))) (U ×ˢ ball 0 R') := by
  refine eqOn_prod_of_eqOn_prod_diff_singleton (c := (0 : ℂ)) isOpen_ball
    hg₂ (Complex.continuous_conj.comp_continuousOn (hg₁.comp hκ hκT)) ?_
  intro b hb
  simp only [he₂ hb, he₁ (hκS hb), hr b hb, map_mul, map_pow, Complex.conj_conj]

end TauCeti

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
  obtain ⟨R', hR', hfit, r, g, hra, hg, hr, e, W, hbound, hWa, hW0, hWform⟩ :=
    exists_analyticOnNhd_nonmonic_laurent hU hR hF hdeg hdiscr hu hu0 hv hv0 hlead hconst
  have hform (x : E) (hx : x ∈ U) : ∀ᶠ b in 𝓝 (x, (0 : ℂ)),
      (∀ i, W i b ≠ 0) ∧ (b.2 ≠ 0 → ∀ i, r i b = b.2 ^ e i * W i b) := by
    filter_upwards [(hU.prod isOpen_ball).mem_nhds
      (x := (x, (0 : ℂ))) ⟨hx, mem_ball_self hR'⟩] with b hb
    exact ⟨fun i ↦ hW0 i b hb, fun hb0 i ↦ hWform b ⟨hb.1, hb.2, hb0⟩ i⟩
  let S := U ×ˢ (ball (0 : ℂ) R' \ {0})
  let T := U ×ˢ ball (0 : ℂ) R'
  let κ : E × ℂ → E × ℂ := fun b ↦ (τ b.1, conj b.2)
  let q : E × ℂ → E × ℂ := fun b ↦ (b.1, b.2 ^ d.factorial)
  have hq : MapsTo q S (U ×ˢ (ball 0 R \ {0})) := fun b hb ↦
    ⟨hb.1, mapsTo_pow_ball_zero d.factorial_ne_zero hfit hb.2.1, pow_ne_zero _ hb.2.2⟩
  have hconjBall : MapsTo conj (ball (0 : ℂ) R') (ball 0 R') := by
    intro z hz
    simpa only [mem_ball_zero_iff, Complex.norm_conj] using hz
  have hκ : ContinuousOn κ T := hτ.prodMap Complex.continuous_conj.continuousOn
  have hκT : MapsTo κ T T := hτU.prodMap hconjBall
  have hκS : MapsTo κ S S :=
    hτU.prodMap fun z hz ↦ ⟨hconjBall hz.1, by simpa using hz.2⟩
  have hroot (b : E × ℂ) (hb : b ∈ S) (z : ℂ) :
      (F (q b)).IsRoot z ↔ ∃ i, r i b = z := by
    obtain ⟨h₁, h₂, h₃⟩ := hq hb
    rw [(hr b hb).2, isRoot_C_mul_prod_X_sub_C_iff (by
      rw [hlead _ ⟨h₁, h₂⟩]
      exact mul_ne_zero (pow_ne_zero _ h₃) (hu0 _ ⟨h₁, h₂⟩))]
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
    (fun b hb ↦ (hr b hb).1) hroot (hκ.mono (prod_mono subset_rfl sdiff_subset)) hκS hκS
    (fun b hb ↦ Prod.ext (hττ b.1 hb.1) (Complex.conj_conj b.2))
    (fun b hb ↦ by simpa only [q, κ, map_pow] using hconj _ (hq hb))
    ⟨(x₀, t₀), x₀.2, t₀.2⟩
  have hcompat (x : U) (i : Fin d) := exponent_eq_and_unit_conj
    (r₁ := r i) (r₂ := r (σ i)) (W₁ := W i) (W₂ := W (σ i)) (m := e i) (n := e (σ i))
    (hτ.continuousAt (hU.mem_nhds x.2))
    (hWa (σ i) _ ⟨x.2, mem_ball_self hR'⟩) (hW0 (σ i) _ ⟨x.2, mem_ball_self hR'⟩)
    (hWa i _ ⟨hτU x.2, mem_ball_self hR'⟩) (hW0 i _ ⟨hτU x.2, mem_ball_self hR'⟩)
    ((hform x.1 x.2).mono fun _ h hb ↦ h.2 hb (σ i))
    ((hform (τ x.1) (hτU x.2)).mono fun _ h hb ↦ h.2 hb i)
    (by
      filter_upwards [(hU.prod isOpen_ball).mem_nhds
        (x := (x.1, (0 : ℂ))) ⟨x.2, mem_ball_self hR'⟩] with b hb hb0
      exact hσ i b ⟨hb.1, hb.2, hb0⟩)
  exact ⟨R', hR', hfit, r, g, hra, hg, hr, σ, hσσ, hσ,
    fun i ↦ eqOn_conj_comp_of_eqOn_punctured (hg i).1.continuousOn (hg (σ i)).1.continuousOn
      (hg i).2 (hg (σ i)).2 hκ hκT hκS (hσ i),
    e, fun _ ↦ W, hbound, fun i ↦ (hcompat x₀ i).1,
    fun x i ↦ ⟨hWa i _ ⟨x.2, mem_ball_self hR'⟩, hW0 i _ ⟨x.2, mem_ball_self hR'⟩⟩,
    fun x ↦ hform x.1 x.2, fun x i ↦ (hcompat x i).2⟩

end TauCeti.Polynomial
