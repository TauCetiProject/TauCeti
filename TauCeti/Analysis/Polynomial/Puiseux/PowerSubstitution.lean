/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
public import TauCeti.Topology.Covering.PowerSubstitution
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Continuous roots after a power substitution

A continuous monic family of degree `d` over a simply connected, locally path connected parameter
space and a punctured disc, separable at every point, splits into `d` pointwise distinct continuous
linear factors after the substitution `(w, t) ↦ (w, t ^ n)`, provided `d ! ∣ n` and the
substituted disc fits inside the original disc.

The analytic version, with ambient root functions on an open simply connected domain, is
`TauCeti.Polynomial.exists_analyticOnNhd_eq_prod_X_sub_C_powerSubstitution` in
`TauCeti.Analysis.Polynomial.Puiseux.Branches`.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 4.
-/

public section

noncomputable section

open Function Filter Metric Polynomial Set Topology

namespace TauCeti.Polynomial

/-- A continuous family of degree `d`, separable over a punctured disc, has `d` pointwise
distinct continuous root functions after a power substitution of exponent divisible by `d !`.
The parameter space can be any simply connected, locally path connected space. -/
theorem exists_continuousMap_isRoot_powerSubstitution
    {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {d n : ℕ} {R R' : ℝ} {F : U × ↥(ball (0 : ℂ) R \ {0}) → ℂ[X]}
    (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hdeg : ∀ b, (F b).natDegree = d) (hsep : ∀ b, (F b).Separable)
    (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ), ∀ b,
      Injective (fun i => r i b) ∧ ∀ i, (F (powerSubstitution U hn hR b)).IsRoot (r i b) := by
  classical
  obtain hempty | ⟨⟨a⟩⟩ := isEmpty_or_nonempty (U × ↥(ball (0 : ℂ) R' \ {0}))
  · let := hempty
    exact ⟨fun _ => 0, fun b => isEmptyElim b⟩
  let B := U × ↥(ball (0 : ℂ) R \ {0})
  let Z := {q : B × ℂ // (F q.1).IsRoot q.2}
  let p : Z → B := fun q => q.1.1
  let q := powerSubstitution U hn hR
  -- Lift all points of one fibre, then use their root coordinates as the global labels.
  have hp : IsCoveringMap p := isCoveringMap_fst_isRoot hF hdeg hsep
  let : Finite (p ⁻¹' {q a}) := finite_preimage_fst_isRoot (hsep _).ne_zero
  have hcard : Nat.card (p ⁻¹' {q a}) = d := natCard_preimage_fst_isRoot (hdeg _) (hsep _)
  obtain ⟨L, hL, hinj⟩ := hp.exists_continuousMap_lifts_powerSubstitution hn hR a
    (by rwa [hcard])
  let := Fintype.ofFinite (p ⁻¹' {q a})
  let e : Fin d ≃ p ⁻¹' {q a} :=
    (Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])).symm
  let r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ) := fun i =>
    ⟨fun b => (L (e i) b).1.2,
      ((continuous_snd : Continuous (Prod.snd : B × ℂ → ℂ)).comp
        (continuous_subtype_val : Continuous (Subtype.val : Z → B × ℂ))).comp (L (e i)).continuous⟩
  have hbase : ∀ i b, p (L (e i) b) = q b := fun i b => congrFun (hL (e i)).2 b
  refine ⟨r, fun b => ⟨?_, fun i => (hbase i b) ▸ (L (e i) b).2⟩⟩
  intro i j hij
  apply e.injective
  apply hinj b
  exact Subtype.ext (Prod.ext ((hbase i b).trans (hbase j b).symm) hij)

/-- A continuous monic family of degree `d`, separable over a punctured disc, splits into `d`
pointwise distinct continuous linear factors after a power substitution of exponent divisible by
`d !`. The parameter space can be any simply connected, locally path connected space. -/
theorem exists_continuousMap_prod_X_sub_C_powerSubstitution
    {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] [LocallyPathConnectedSpace U]
    {d n : ℕ} {R R' : ℝ} {F : U × ↥(ball (0 : ℂ) R \ {0}) → ℂ[X]}
    (hF : ∀ i ≤ d, Continuous fun b => (F b).coeff i)
    (hmonic : ∀ b, (F b).Monic) (hdeg : ∀ b, (F b).natDegree = d)
    (hsep : ∀ b, (F b).Separable) (hn : n ≠ 0) (hR : R' ^ n ≤ R) (hdvd : d.factorial ∣ n) :
    ∃ r : Fin d → C(U × ↥(ball (0 : ℂ) R' \ {0}), ℂ), ∀ b,
      Injective (fun i => r i b) ∧
      F (powerSubstitution U hn hR b) = ∏ i, (X - C (r i b)) := by
  obtain ⟨r, hr⟩ := exists_continuousMap_isRoot_powerSubstitution hF hdeg hsep hn hR hdvd
  exact ⟨r, fun b => ⟨(hr b).1, (Sym.toMonic_ofFn_eq_of_forall_isRoot (hmonic _) (hdeg _)
    (hr b).1 (hr b).2).symm.trans (Sym.toMonic_ofFn _)⟩⟩

end TauCeti.Polynomial
