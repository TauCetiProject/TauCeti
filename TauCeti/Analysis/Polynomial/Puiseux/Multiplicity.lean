/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.RootDifference

/-!
# Root collisions and multiplicities on the Puiseux hyperplane

Suppose a polynomial family has a complete analytic splitting near `(x₀, y₀)` and its
discriminant is `(y - y₀)^a` times an analytic unit. On the distinguished hyperplane
`y = y₀`, the equivalence relation identifying coincident root labels is locally constant.
Consequently the multiplicity of each labelled root of the specialized polynomial is
locally constant, even when several labels collide there.

These conclusions supply the multiplicity information needed to pass from a ramified
analytic splitting to distinct root sections. No constancy of multiplicities or collisions
is assumed. The splitting itself is an input; its construction is separate.

The proof uses `TauCeti.exists_root_sub_eq_pow_mul_unit`: a root difference with positive
exponent vanishes identically on the hyperplane, whereas one with exponent zero is a unit.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ} {r : Fin n → E × 𝕜 → 𝕜} {P : E × 𝕜 → Polynomial 𝕜}
  {x₀ : E} {y₀ : 𝕜} {a : ℕ} {u : E × 𝕜 → 𝕜}

/-- Coincidence of two root labels is locally constant on the distinguished hyperplane
when the discriminant is a centered power times an analytic unit. Collisions at the
hyperplane are allowed. -/
theorem eventually_root_eq_iff_on_hyperplane
    (hr : ∀ i, AnalyticAt 𝕜 (r i) (x₀, y₀))
    (hP : ∀ᶠ p in 𝓝 (x₀, y₀), P p = ∏ i, (X - C (r i p)))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).discr = (p.2 - y₀) ^ a * u p)
    (i j : Fin n) :
    ∀ᶠ x in 𝓝 x₀, r i (x, y₀) = r j (x, y₀) ↔ r i (x₀, y₀) = r j (x₀, y₀) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  obtain ⟨b, v, hv, hv0, heq⟩ := exists_root_sub_eq_pow_mul_unit hr hP hu hu0 hdiscr hij
  have hslice : Tendsto (fun x : E ↦ (x, y₀)) (𝓝 x₀) (𝓝 (x₀, y₀)) :=
    continuousAt_id.prodMk continuousAt_const
  have heq' := hslice.eventually heq
  have hunit := hslice.eventually (hv.continuousAt.eventually_ne hv0)
  have hcenter := heq.self_of_nhds
  filter_upwards [heq', hunit] with x hx hxunit
  conv_lhs => rw [← sub_eq_zero, hx]
  conv_rhs => rw [← sub_eq_zero, hcenter]
  by_cases hb : b = 0 <;> simp [hb, hxunit, hv0]

/-- On one common neighborhood of the central parameter, every labelled root on the
distinguished hyperplane has its central multiplicity. This multiplicity counts all
labels coinciding there and may be greater than one. -/
theorem eventually_rootMultiplicity_eq_on_hyperplane
    (hr : ∀ i, AnalyticAt 𝕜 (r i) (x₀, y₀))
    (hP : ∀ᶠ p in 𝓝 (x₀, y₀), P p = ∏ i, (X - C (r i p)))
    (hu : AnalyticAt 𝕜 u (x₀, y₀)) (hu0 : u (x₀, y₀) ≠ 0)
    (hdiscr : ∀ᶠ p in 𝓝 (x₀, y₀), (P p).discr = (p.2 - y₀) ^ a * u p) :
    ∀ᶠ x in 𝓝 x₀, ∀ i,
      (P (x, y₀)).rootMultiplicity (r i (x, y₀)) =
        (P (x₀, y₀)).rootMultiplicity (r i (x₀, y₀)) := by
  classical
  have hrel := eventually_all.2 fun i ↦ eventually_all.2 fun j ↦
    eventually_root_eq_iff_on_hyperplane hr hP hu hu0 hdiscr i j
  have hslice : Tendsto (fun x : E ↦ (x, y₀)) (𝓝 x₀) (𝓝 (x₀, y₀)) :=
    continuousAt_id.prodMk continuousAt_const
  have hroots (x : E) (hx : P (x, y₀) = ∏ i, (X - C (r i (x, y₀)))) :
      (P (x, y₀)).roots = Finset.univ.val.map (fun i ↦ r i (x, y₀)) := by
    rw [hx, roots_prod _ _ (Finset.prod_ne_zero_iff.2 fun i _ ↦ X_sub_C_ne_zero _)]
    simp only [roots_X_sub_C, Multiset.bind_singleton]
  filter_upwards [hrel, hslice.eventually hP] with x hx hxP
  intro i
  rw [← count_roots, ← count_roots, hroots x hxP, hroots x₀ hP.self_of_nhds,
    Multiset.count_map, Multiset.count_map]
  congr 1
  exact Multiset.filter_congr fun j _ ↦ hx i j

end TauCeti
