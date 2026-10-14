/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import TauCeti.Topology.LocallyConstant.Preconnected

/-!
# Laurent exponents in connected families

Suppose a function on a product has, near every point of a distinguished hyperplane, a
Laurent-power expression in the transverse variable with an analytic nonvanishing unit.
For a fixed global function the integer exponent is locally constant along the hyperplane:
two such expressions at nearby points overlap, and uniqueness of the order of an analytic
germ identifies their exponents. Consequently the exponent is constant on a preconnected
set of parameters.

The result is stated simultaneously for an arbitrary family of functions. It is used for
global root labels in parameterized Puiseux factorizations: the labels having finite limits
are precisely those with nonnegative exponent, so their set cannot change over a connected
base.

## References

* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), 52–69, §5.2.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {I E 𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

omit [CompleteSpace 𝕜] in
private theorem laurentExponent_eq {r u v : E × 𝕜 → 𝕜} {x : E} {m n : ℤ}
    (hu : AnalyticAt 𝕜 u (x, 0)) (hu0 : u (x, 0) ≠ 0)
    (hv : AnalyticAt 𝕜 v (x, 0)) (hv0 : v (x, 0) ≠ 0)
    (hm : ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 → r b = b.2 ^ m * u b)
    (hn : ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 → r b = b.2 ^ n * v b) : m = n := by
  let f : 𝕜 → 𝕜 := fun z ↦ r (x, z)
  have hline : Tendsto (fun z : 𝕜 ↦ (x, z)) (𝓝 0) (𝓝 (x, (0 : 𝕜))) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hu' : AnalyticAt 𝕜 (fun z ↦ u (x, z)) 0 :=
    hu.comp_of_eq (analyticAt_const.prod analyticAt_id) (by simp)
  have hv' : AnalyticAt 𝕜 (fun z ↦ v (x, z)) 0 :=
    hv.comp_of_eq (analyticAt_const.prod analyticAt_id) (by simp)
  apply AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero
    (f := f) (z₀ := (0 : 𝕜))
  · refine ⟨_, hu', by simpa using hu0, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hline.eventually hm] with z hz
    intro hz0
    simpa only [f, sub_zero, smul_eq_mul] using hz (by simpa using hz0)
  · refine ⟨_, hv', by simpa using hv0, ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hline.eventually hn] with z hz
    intro hz0
    simpa only [f, sub_zero, smul_eq_mul] using hz (by simpa using hz0)

/-- **Laurent exponents are constant in preconnected families.** Suppose that, near every
`(x, 0)` with `x ∈ S`, every function `r i` is a power of the transverse coordinate times
an analytic unit. Then one exponent can be chosen for each global label `i`, independently
of `x`. The analytic unit may still depend on the point.

No finiteness assumption on the label type is needed. Any pointwise property `P i e` of the
exponents, such as a common lower bound, is retained. Negative exponents and an empty label type
are allowed. -/
theorem exists_laurentExponents_of_isPreconnected {S : Set E} (hSne : S.Nonempty)
    (hS : IsPreconnected S) (r : I → E × 𝕜 → 𝕜) {P : I → ℤ → Prop}
    (h : ∀ i x, x ∈ S → ∃ e : ℤ, P i e ∧ ∃ w : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 w (x, 0) ∧ w (x, 0) ≠ 0 ∧
        ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 → r i b = b.2 ^ e * w b) :
    ∃ e : I → ℤ, (∀ i, P i (e i)) ∧ ∀ i x, x ∈ S → ∃ w : E × 𝕜 → 𝕜,
      AnalyticAt 𝕜 w (x, 0) ∧ w (x, 0) ≠ 0 ∧
        ∀ᶠ b in 𝓝 (x, (0 : 𝕜)), b.2 ≠ 0 → r i b = b.2 ^ e i * w b := by
  classical
  let e : I → S → ℤ := fun i x ↦ (h i x x.2).choose
  let w : I → (x : S) → E × 𝕜 → 𝕜 := fun i x ↦ (h i x x.2).choose_spec.2.choose
  have he_prop (i : I) (x : S) : P i (e i x) := (h i x x.2).choose_spec.1
  have hw (i : I) (x : S) :
      AnalyticAt 𝕜 (w i x) (x.1, 0) ∧ w i x (x.1, 0) ≠ 0 ∧
        ∀ᶠ b in 𝓝 (x.1, (0 : 𝕜)), b.2 ≠ 0 →
          r i b = b.2 ^ e i x * w i x b :=
    (h i x x.2).choose_spec.2.choose_spec
  let e' (i : I) (x : E) : ℤ := if hx : x ∈ S then e i ⟨x, hx⟩ else 0
  have he_local (i : I) (x : E) (hx : x ∈ S) :
      ∀ᶠ y in 𝓝[S] x, e' i y = e' i x := by
    let xs : S := ⟨x, hx⟩
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp
      ((hw i xs).1.eventually_analyticAt.and
        ((hw i xs).1.continuousAt.eventually_ne (hw i xs).2.1) |>.and (hw i xs).2.2)
    have hmem : ∀ᶠ y in 𝓝 x, (y, (0 : 𝕜)) ∈ U :=
      (continuous_id.prodMk continuous_const).continuousAt.eventually (hUopen.mem_nhds hxU)
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with y hy hyS
    let ys : S := ⟨y, hyS⟩
    have heq := laurentExponent_eq (r := r i) (u := w i ys) (v := w i xs)
      (hw i ys).1 (hw i ys).2.1 (hUsub hy).1.1 (hUsub hy).1.2
      (hw i ys).2.2 (by
        filter_upwards [hUopen.mem_nhds hy] with b hb
        exact (hUsub hb).2)
    simpa only [e', dite_eq_left hyS, dite_eq_left hx] using heq
  obtain ⟨x₀, hx₀⟩ := hSne
  refine ⟨fun i ↦ e i ⟨x₀, hx₀⟩, fun i ↦ he_prop i ⟨x₀, hx₀⟩, fun i x hx ↦ ?_⟩
  let y : S := ⟨x, hx⟩
  have hey' : e' i x = e' i x₀ := hS.apply_eq_of_eventually_eq (he_local i) hx hx₀
  have hey : e i y = e i ⟨x₀, hx₀⟩ := by
    simpa only [e', dite_eq_left hx, dite_eq_left hx₀, y] using hey'
  refine ⟨w i y, (hw i y).1, (hw i y).2.1, ?_⟩
  simpa only [hey] using (hw i y).2.2

end TauCeti
