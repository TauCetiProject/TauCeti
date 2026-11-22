/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
import Mathlib.Analysis.Normed.Field.Lemmas
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.Topology.Algebra.Polynomial.Root.Multiplicity

/-!
# Approximation of finite roots across degree drops

Every root of a nonzero central polynomial is approximated by roots of a continuous
coefficient family with locally bounded degree. Nearby degrees may exceed the central degree;
roots escaping to infinity do not affect the approximation of finite roots.

Translate to a nonroot of the central polynomial and reflect at a fixed degree bound.
The reflected leading coefficient stays nonzero. Writing a nearby reflected polynomial as
its leading coefficient times the product of `X - b` over its roots, its small value at
the reflected central root forces one of those roots to be close. Reciprocal coordinates
then recover the finite roots. No local compactness of the field is needed.
This is useful for polynomial deformations whose limiting leading coefficient vanishes.

## References

S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Springer (2006), §5.1 (continuity of polynomial roots).
-/

public section

open Filter Polynomial Topology

namespace TauCeti

/-- Every finite root of a nonzero central fiber is approximated by roots of nearby fibers
of a continuous coefficient family with locally bounded degree. No constancy of degree or
root multiplicity is required. -/
theorem eventually_exists_isRoot_norm_sub_lt
    {K B : Type*} [NormedField K] [IsAlgClosed K] [TopologicalSpace B]
    {F : B → K[X]} {x₀ : B} {d : ℕ}
    (hF : ∀ i ≤ d, ContinuousAt (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hzero : F x₀ ≠ 0)
    {z : K} (hz : (F x₀).IsRoot z) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∃ w : K, (F x).IsRoot w ∧ ‖z - w‖ < ε := by
  classical
  obtain ⟨τ, hτ⟩ := not_forall.mp (fun h ↦ hzero (Polynomial.funext fun x ↦ by simpa using h x))
  have hzτ : z - τ ≠ 0 := sub_ne_zero.mpr fun h ↦ hτ (h ▸ hz.eq_zero)
  let G : B → K[X] := fun x ↦ (taylor τ (F x)).reflect d
  have hGcoeff (i : ℕ) : ContinuousAt (fun x ↦ (G x).coeff i) x₀ := by
    simp only [G, coeff_reflect, taylor_coeff]
    exact continuousAt_hasseDeriv_eval _ (fun j _ hj ↦ hF j hj) hdeg continuousAt_const
  have htop (x : B) : (G x).coeff d = (F x).eval τ := by
    simp [G, coeff_reflect, revAt_le le_rfl]
  have hne : ∀ᶠ x in 𝓝 x₀, (F x).eval τ ≠ 0 :=
    (continuousAt_eval hF hdeg continuousAt_const).eventually_ne hτ
  have hGdeg : ∀ᶠ x in 𝓝 x₀, (G x).degree = d := by
    filter_upwards [hdeg, hne] with x hx hxτ
    apply degree_eq_of_le_of_coeff_ne_zero
    · exact degree_le_of_natDegree_le (natDegree_reflect_le.trans
        (max_le (le_refl d) (by simpa using hx)))
    · rwa [htop]
  let u : K := (z - τ)⁻¹
  have hu : u ≠ 0 := inv_ne_zero hzτ
  have hroot : (G x₀).IsRoot u :=
    (isRoot_reflect_taylor_iff hdeg.self_of_nhds τ hu).2 (by simpa [u] using hz)
  -- Choose the matching tolerance in reciprocal coordinates, keeping away from zero.
  have hclose : ∀ᶠ b in 𝓝 u, b ≠ 0 ∧ ‖z - (b⁻¹ + τ)‖ < ε := by
    have hcont : ContinuousAt (fun b : K ↦ ‖z - (b⁻¹ + τ)‖) u :=
      (continuousAt_const.sub ((continuousAt_id.inv₀ hu).add continuousAt_const)).norm
    apply (continuousAt_id.eventually_ne hu).and
    apply hcont.eventually_lt continuousAt_const
    simpa [u, sub_add_cancel] using hε
  obtain ⟨δ, hδ, hδclose⟩ := Metric.eventually_nhds_iff.1 hclose
  -- Near `x₀`, `G x` is small at `u` compared with its leading coefficient.
  have hδ' : 0 < min δ 1 := lt_min hδ one_pos
  have hsmall : ∀ᶠ x in 𝓝 x₀, ‖(G x).eval u‖ < ‖(G x).coeff d‖ * min δ 1 ^ d := by
    have hGd : ∀ᶠ x in 𝓝 x₀, (G x).natDegree ≤ d :=
      hGdeg.mono fun x hx ↦ natDegree_le_of_degree_le hx.le
    refine (continuousAt_eval (fun i _ ↦ hGcoeff i) hGd continuousAt_const).norm.eventually_lt
      ((hGcoeff d).norm.mul continuousAt_const) ?_
    rw [hroot.eq_zero, norm_zero, htop]
    exact mul_pos (norm_pos_iff.2 hτ) (pow_pos hδ' d)
  filter_upwards [hsmall, hGdeg, hdeg] with x hx hxGdeg hxdeg
  -- So some root of `G x` lies within `δ` of `u`.
  obtain ⟨b, hb, hub⟩ : ∃ b ∈ (G x).roots, ‖u - b‖ < min δ 1 := by
    by_contra! h
    have hnat : (G x).natDegree = d := natDegree_eq_of_degree_eq_some hxGdeg
    have hprod : min δ 1 ^ d ≤ ((G x).roots.map fun b ↦ ‖u - b‖).prod :=
      calc min δ 1 ^ d ≤ min δ 1 ^ Multiset.card (G x).roots :=
            pow_le_pow_of_le_one hδ'.le (min_le_right _ _) (hnat ▸ card_roots' _)
        _ = ((G x).roots.map fun _ ↦ min δ 1).prod := by simp
        _ ≤ _ := Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ hδ'.le) h
    rw [(IsAlgClosed.splits (G x)).eval_eq_prod_roots, norm_mul, Multiset.norm_prod_map,
      leadingCoeff, hnat] at hx
    exact hx.not_ge (by gcongr)
  have hbu := hδclose (by rw [dist_eq_norm, norm_sub_rev]; exact hub.trans_le (min_le_left _ _))
  exact ⟨b⁻¹ + τ, (isRoot_reflect_taylor_iff hxdeg τ hbu.1).1 (isRoot_of_mem_roots hb), hbu.2⟩

end TauCeti
