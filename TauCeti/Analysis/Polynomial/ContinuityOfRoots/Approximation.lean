/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.ContinuityOfRoots.Basic
import TauCeti.Topology.Algebra.Polynomial.Root.Multiplicity

/-!
# Approximation of finite roots across degree drops

Every root of a nonzero central polynomial is approximated by roots of a continuous
coefficient family with locally bounded degree. Nearby degrees may exceed the central degree;
roots escaping to infinity do not affect the approximation of finite roots.

Translate to a nonroot of the central polynomial and reflect at a fixed degree bound.
The reflected leading coefficient stays nonzero, so the existing fixed-degree root
matching theorem `Polynomial.eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt` applies.
Reciprocal coordinates then recover the finite roots.
This is useful for polynomial deformations whose limiting leading coefficient vanishes.

## References

S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, second edition,
Springer (2006), §5.1 (continuity of polynomial roots).
-/

public section

open Filter Polynomial Topology

namespace Polynomial

/-- Translating by `τ` and reflecting at a degree bound `d` sends the root `a⁻¹ + τ` of `p` to
the root `a` of `(taylor τ p).reflect d`, for nonzero `a`, when `natDegree p ≤ d`. -/
theorem isRoot_reflect_taylor_iff {K : Type*} [Field K] {p : K[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (τ : K) {a : K} (ha : a ≠ 0) :
    ((taylor τ p).reflect d).IsRoot a ↔ p.IsRoot (a⁻¹ + τ) := by
  let : Invertible a⁻¹ := invertibleOfNonzero (inv_ne_zero ha)
  have h := eval₂_reflect_eq_zero_iff (RingHom.id K) a⁻¹ d (taylor τ p) (by simpa using hp)
  simpa [IsRoot.def, eval₂_id, taylor_apply, eval_comp] using h

end Polynomial

namespace TauCeti

/-- Every finite root of a nonzero central fiber is approximated by roots of nearby fibers
of a continuous coefficient family with locally bounded degree. No constancy of degree or
root multiplicity is required. -/
theorem eventually_exists_isRoot_norm_sub_lt
    {K B : Type*} [NormedField K] [IsAlgClosed K] [ProperSpace K] [TopologicalSpace B]
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
  filter_upwards [eventually_exists_C_mul_prod_X_sub_C_norm_sub_lt
    (fun i _ ↦ hGcoeff i) hGdeg hδ, hdeg] with x hx hxdeg
  obtain ⟨a, b, ha, hb, hab⟩ := hx
  have hGa : ∃ i, a i = u := by
    have heval := hroot.eq_zero
    rw [ha, eval_mul, eval_C, eval_prod] at heval
    have hlc : (G x₀).leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero.mpr (ne_zero_of_coe_le_degree hGdeg.self_of_nhds.ge)
    have hprod := (mul_eq_zero.mp heval).resolve_left hlc
    obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hprod
    exact ⟨i, (sub_eq_zero.mp (by simpa using hi)).symm⟩
  obtain ⟨i, hi⟩ := hGa
  have hbi : b i ≠ 0 ∧ ‖z - ((b i)⁻¹ + τ)‖ < ε :=
    hδclose (by simpa [dist_eq_norm, hi, norm_sub_rev] using hab i)
  refine ⟨(b i)⁻¹ + τ, ?_, hbi.2⟩
  have hbroot : (G x).eval (b i) = 0 := by
    rw [hb, eval_mul, eval_C, eval_prod]
    apply mul_eq_zero_of_right
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  exact (isRoot_reflect_taylor_iff hxdeg τ hbi.1).1 hbroot

end TauCeti
