/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.EndomorphismLieDeriv
public import TauCeti.Geometry.Manifold.Complex.Family.Block
import TauCeti.Analysis.Calculus.ContDiff.Differentiable
import TauCeti.Geometry.Symplectic.Finrank
import Mathlib.Tactic.Module

/-!
# Integrability of product-trivialized almost complex families

In a product trivialization `B × V` over a base `B` with constant complex structure `i`, an almost
complex family of block form `J(p)(a, v) = (i a, α(p) a + j(p) v)` has three Nijenhuis components
(`TauCeti.ComplexStructureFamily.nijenhuis_eq_zero_iff`): the mixed equation `mixedTerm`, the
horizontal curvature equation `horizontalTerm`, and the vertical fibre Nijenhuis component
`verticalTerm`.

This file develops the Lie-derivative and integrability theory of these equations:

1. **Lie-derivative and Lie-bracket dictionary**: `mixedTerm_eq_add_lieDerivEndomorphism` rewrites
   `mixedTerm` as `∂_a j + j ∂_{i a} j + j L_{α a} j`, and `horizontalTerm_eq_sub_lieBracket`
   relates `horizontalTerm` to Mathlib's `VectorField.lieBracket` (with the opposite sign from
   Robbin–Salamon's source bracket).
2. **Horizontal connection dictionary**: when `α` arises from a horizontal connection lift
   `(a, -v(a))` via `connectionOfHorizontal i v j q a = j(q)(v(q) a + j(q)(v(q)(i a)))`,
   `mixedTerm_connectionOfHorizontal` identifies `mixedTerm` (when `verticalTerm j p` vanishes)
   with `(∂_a j - L_{v a} j) + j (∂_{i a} j - L_{v(i a)} j)`, twice the complex-antilinear part
   `2 • ∂bar^H j` of the horizontal covariant derivative `∇^H_a j = ∂_a j - L_{v a} j`.
3. **Surface-fibre and split-family criteria**: when `Module.finrank ℝ V ≤ 2` (in particular on
   real 2-dimensional surface fibres), the vertical Nijenhuis component vanishes automatically
   (`nijenhuis_eq_zero_iff_of_finrank_le_two`, `nijenhuis_eq_zero_iff_of_finrank_eq_two`). When
   `α =ᶠ[𝓝 p] 0`, `horizontalTerm` vanishes and `mixedTerm` reduces to base-holomorphy
   `∂_a j + j ∂_{i a} j = 0` (`nijenhuis_eq_zero_iff_of_eventuallyEq_zero_of_finrank_le_two`).
4. **Robbin–Salamon Corrigendum Lemma B**: `lieDerivEndomorphism_horizontalTerm_eq_zero` proves on
   arbitrary real normed spaces `B, V` under `C²` regularity of `α` and `j` that if `mixedTerm`
   and `verticalTerm` vanish on a neighborhood of `p` (automatic when `Module.finrank ℝ V ≤ 2`,
   `lieDerivEndomorphism_horizontalTerm_eq_zero_of_finrank_le_two`), then the horizontal curvature
   `y ↦ horizontalTerm i α j (p.1, y) a b` is an infinitesimal automorphism of the fibre complex
   structure (`L_{ζ(a, b)} j = 0` at `p.2`). On a product `B × V` this does not force
   `horizontalTerm = 0` on its own (since `(ℝ², j)` carries nonzero holomorphic vector fields), so
   both `mixedTerm = 0` and `horizontalTerm = 0` remain necessary in a local product chart
   (`nijenhuis_eq_zero_iff_of_finrank_eq_two`); Lemma B provides the local chart identity used when
   globalizing to closed fibres without nonzero holomorphic vector fields.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*, J. Eur. Math.
  Soc. 8 (2006), 611–699, Section 8.9.
* J. W. Robbin and D. A. Salamon, *Corrigendum to A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. 9 (2007), 901–905, Lemmas A and B and Remark.
-/

public noncomputable section

open VectorField
open scoped Manifold ContDiff Topology

namespace TauCeti.ComplexStructureFamily

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Fibre derivatives, Lie derivatives, and bracket form -/

/-- Directional derivative along the fibre `{p.1} × V` of `y ↦ j (p.1, y)`. -/
theorem fderiv_fiber_apply {j : B × V → V →L[ℝ] V} {p : B × V}
    (hj : DifferentiableAt ℝ j p) (u v : V) :
    fderiv ℝ (fun y ↦ j (p.1, y)) p.2 u v = fderiv ℝ j p (0, u) v := by
  have hd := (hj.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)).fderiv
  rw [Function.comp_def] at hd
  simpa using congrArg (fun L : V →L[ℝ] V ↦ L v)
    (congrArg (fun D : V →L[ℝ] V →L[ℝ] V ↦ D u) hd)

/-- The fibre Lie derivative `L_{α(a)} j` at `p.2` matches the last three terms of `mixedTerm`. -/
theorem lieDerivEndomorphism_fiber_connection_apply {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (a : B) (v : V) :
    lieDerivEndomorphism (fun y ↦ α (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 v =
      fderiv ℝ j p (0, α p a) v + j p (fderiv ℝ α p (0, v) a) -
        fderiv ℝ α p (0, j p v) a := by
  rw [lieDerivEndomorphism_apply, fderiv_fiber_apply hj, fderiv_fiber_connection hα,
    fderiv_fiber_connection hα]

/-- Express `mixedTerm` in terms of the fibre endomorphism Lie derivative:
`mixedTerm i α j p a v = ∂_a j(v) + j(∂_{i a} j(v)) + j((L_{α a} j) v)`. -/
theorem mixedTerm_eq_add_lieDerivEndomorphism (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (a : B) (v : V) :
    mixedTerm i α j p a v =
      fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) +
        j p (lieDerivEndomorphism (fun y ↦ α (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 v) := by
  rw [mixedTerm_def, lieDerivEndomorphism_fiber_connection_apply hα hj]

/-- Express `horizontalTerm` in terms of Mathlib's `VectorField.lieBracket` on the fibre. Because
Robbin–Salamon's source bracket is `-lieBracket`, the bracket appears with a minus sign. -/
theorem horizontalTerm_eq_sub_lieBracket (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    (j : B × V → V →L[ℝ] V) {p : B × V}
    (hα : DifferentiableAt ℝ α p) (a b : B) :
    horizontalTerm i α j p a b =
      fderiv ℝ α p (i b, 0) a - j p (fderiv ℝ α p (b, 0) a) -
        fderiv ℝ α p (i a, 0) b + j p (fderiv ℝ α p (a, 0) b) -
        lieBracket ℝ (fun y ↦ α (p.1, y) a) (fun y ↦ α (p.1, y) b) p.2 := by
  rw [horizontalTerm_def, lieBracket_fiber_eq α hα a b]
  abel

/-! ### Horizontal connection dictionary (`α(a) = j(v(a) + j v(i a))`) -/

/-- The off-diagonal connection block `a ↦ j(q)(v(q) a + j(q)(v(q)(i a)))` induced by a horizontal
connection 1-form `v` (whose horizontal lift of `a` is `(a, -v(q) a)`). -/
def connectionOfHorizontal (i : B →L[ℝ] B) (v : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (q : B × V) : B →L[ℝ] V :=
  (j q).comp (v q + (j q).comp ((v q).comp i))

@[simp]
theorem connectionOfHorizontal_apply (i : B →L[ℝ] B) (v : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (q : B × V) (a : B) :
    connectionOfHorizontal i v j q a = j q (v q a + j q (v q (i a))) :=
  (rfl)

/-- When `i² = -1` and `j(q)² = -1`, `connectionOfHorizontal i v j q` is `(i, j(q))`-antilinear. -/
theorem connectionOfHorizontal_anticommute {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    (v : B × V → B →L[ℝ] V) {j : B × V → V →L[ℝ] V} {q : B × V}
    (hj : ∀ w, j q (j q w) = -w) (a : B) :
    connectionOfHorizontal i v j q (i a) + j q (connectionOfHorizontal i v j q a) = 0 := by
  simp only [connectionOfHorizontal_apply, map_add, hi, map_neg, hj]
  abel

/-- **Horizontal `∂bar^H j` identity**: when `α = connectionOfHorizontal i v j` and the vertical
Nijenhuis expression `verticalTerm j p` vanishes, `mixedTerm` equals
`(∂_a j - L_{v a} j) + j (∂_{i a} j - L_{v(i a)} j)`, twice the complex-antilinear part of the
covariant horizontal derivative `∇^H_a j = ∂_a j - L_{v a} j` along `(a, -v(a))`. -/
theorem mixedTerm_connectionOfHorizontal (i : B →L[ℝ] B) {v : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hv : DifferentiableAt ℝ v p) (hj : DifferentiableAt ℝ j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ w, j q (j q w) = -w)
    (hvert : ∀ u w, verticalTerm j p u w = 0)
    (a : B) (w : V) :
    mixedTerm i (connectionOfHorizontal i v j) j p a w =
      (fderiv ℝ j p (a, 0) w -
          lieDerivEndomorphism (fun y ↦ v (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 w) +
        j p (fderiv ℝ j p (i a, 0) w -
          lieDerivEndomorphism (fun y ↦ v (p.1, y) (i a)) (fun y ↦ j (p.1, y)) p.2 w) := by
  have hα : DifferentiableAt ℝ (connectionOfHorizontal i v j) p :=
    hj.clm_comp (hv.add (hj.clm_comp (hv.clm_comp (differentiableAt_const i))))
  have he : DifferentiableAt ℝ (fun y : V ↦ (p.1, y)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  have hjf : DifferentiableAt ℝ (fun y ↦ j (p.1, y)) p.2 := hj.comp p.2 he
  have hvf (c : B) : DifferentiableAt ℝ (fun y ↦ v (p.1, y) c) p.2 :=
    (hv.comp p.2 he).clm_apply (differentiableAt_const c)
  have hj_sq_f : ∀ᶠ y in 𝓝 p.2, ∀ u, j (p.1, y) (j (p.1, y) u) = -u :=
    he.continuousAt.eventually hj_sq
  have hα_eq : (fun y ↦ connectionOfHorizontal i v j (p.1, y) a) =ᶠ[𝓝 p.2]
      ((fun y ↦ j (p.1, y) (v (p.1, y) a)) - fun y ↦ v (p.1, y) (i a)) :=
    hj_sq_f.mono fun y hy ↦ by
      simp [connectionOfHorizontal_apply, map_add, hy, sub_eq_add_neg]
  have hjv : lieDerivEndomorphism (fun y ↦ j (p.1, y) (v (p.1, y) a)) (fun y ↦ j (p.1, y)) p.2 w =
      j p (lieDerivEndomorphism (fun y ↦ v (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 w) := by
    apply sub_eq_zero.1
    rw [lieDerivEndomorphism_apply_sub_apply hjf (hvf a) hj_sq.self_of_nhds w,
      fderiv_fiber_apply hj, fderiv_fiber_apply hj, fderiv_fiber_apply hj, fderiv_fiber_apply hj,
      ← verticalTerm_def]
    exact hvert (v p a) w
  have hLα : lieDerivEndomorphism (fun y ↦ connectionOfHorizontal i v j (p.1, y) a)
      (fun y ↦ j (p.1, y)) p.2 w =
      j p (lieDerivEndomorphism (fun y ↦ v (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 w) -
        lieDerivEndomorphism (fun y ↦ v (p.1, y) (i a)) (fun y ↦ j (p.1, y)) p.2 w := by
    rw [hα_eq.lieDerivEndomorphism_eq (Filter.EventuallyEq.refl _ _),
      lieDerivEndomorphism_sub_left (hjf.clm_apply (hvf a)) (hvf (i a)), sub_apply, hjv]
  rw [mixedTerm_eq_add_lieDerivEndomorphism i hα hj a w, hLα]
  simp only [map_sub, hj_sq.self_of_nhds]
  abel

/-! ### Surface-fibre (`finrank ≤ 2`) and split-family (`α = 0`) integrability -/

/-- When `V` has real dimension at most `2` and `j(q)² = -1` on a neighborhood of `p`, the
fibrewise Nijenhuis expression `verticalTerm j p` vanishes automatically at `p`. -/
theorem fiber_nijenhuis_eq_zero_of_finrank_le_two [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 2) {j : B × V → V →L[ℝ] V} {p : B × V}
    (hj : DifferentiableAt ℝ j p) (hj_sq : ∀ᶠ q in 𝓝 p, ∀ w, j q (j q w) = -w)
    (u w : V) :
    verticalTerm j p u w = 0 := by
  have he : DifferentiableAt ℝ (fun y : V ↦ (p.1, y)) p.2 :=
    (hasFDerivAt_prodMk_right p.1 p.2).differentiableAt
  let jf : V → V →L[ℝ] V := fun y ↦ j (p.1, y)
  have hjf : DifferentiableAt ℝ jf p.2 := hj.comp p.2 he
  have hsq_ev : (fun y ↦ (jf y).comp (jf y)) =ᶠ[𝓝 p.2] fun _ ↦ -ContinuousLinearMap.id ℝ V :=
    (he.continuousAt.eventually hj_sq).mono fun y hy ↦
      ContinuousLinearMap.ext fun z ↦ by simp [jf, hy z]
  have hsq_deriv (h z : V) :
      fderiv ℝ j p (0, h) (j p z) + j p (fderiv ℝ j p (0, h) z) = 0 := by
    have hd1 := (hjf.hasFDerivAt.clm_comp hjf.hasFDerivAt).fderiv
    have hd0 : fderiv ℝ (fun y ↦ (jf y).comp (jf y)) p.2 = 0 := by rw [hsq_ev.fderiv_eq]; simp
    have hdz := congrArg (· z) (congrArg (· h) (hd1.symm.trans hd0))
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, zero_apply, jf, Prod.mk.eta, fderiv_fiber_apply hj] at hdz
    simpa only [add_comm] using hdz
  let Jp : AlmostComplexStructure V := ⟨(j p).toLinearMap, LinearMap.ext hj_sq.self_of_nhds⟩
  have hJp_apply (z : V) : Jp z = j p z := rfl
  let D : V →L[ℝ] V →L[ℝ] V := (fderiv ℝ j p).comp (ContinuousLinearMap.inr ℝ B V)
  let Nf : V →ₗ[ℝ] V →ₗ[ℝ] V := LinearMap.mk₂ ℝ
    (fun x y ↦ D (j p x) y - D (j p y) x + j p (D y x) - j p (D x y))
    (fun _ _ _ ↦ by simp only [map_add, add_apply]; abel)
    (fun _ _ _ ↦ by simp only [map_smul, smul_apply]; module)
    (fun _ _ _ ↦ by simp only [map_add, add_apply]; abel)
    (fun _ _ _ ↦ by simp only [map_smul, smul_apply]; module)
  have hNf_self (v : V) : Nf v v = 0 := by simp only [Nf, LinearMap.mk₂_apply]; abel
  have hNf_Jp (v : V) : Nf v (Jp v) = 0 := by
    have h1 : D (j p v) (j p v) = -j p (D (j p v) v) :=
      eq_neg_of_add_eq_zero_left (hsq_deriv (j p v) v)
    have h2 : D v (j p v) = -j p (D v v) := eq_neg_of_add_eq_zero_left (hsq_deriv v v)
    rw [hJp_apply]
    simp only [Nf, LinearMap.mk₂_apply, hj_sq.self_of_nhds, map_neg, neg_apply, h1, h2]
    abel
  simpa [Nf, D, verticalTerm_def] using LinearMap.congr_fun₂
    (Jp.bilin_eq_zero_of_finrank_le_two (B := Nf) hdim hNf_self hNf_Jp) u w

section FiniteDimTotal

variable [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
  (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
  (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
  {p : B × V}
  (hJ : (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 p]
    blockEndomorphism i α j)
  (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p)

include hJ hα hj in
/-- On surface fibres (`Module.finrank ℝ V ≤ 2`), the vertical Nijenhuis component vanishes
automatically. -/
theorem nijenhuis_vertical_vertical_eq_zero_of_finrank_le_two
    (hdim : Module.finrank ℝ V ≤ 2) (v w : V) :
    J.nijenhuis p (0, v) (0, w) = 0 := by
  have hj_sq : ∀ᶠ q in 𝓝 p, ∀ z, j q (j q z) = -z := hJ.mono fun q hq ↦
    ((blockEndomorphism_comp_self_eq_neg_id_iff i α j q).1 (hq ▸ J.square_neg q)).2.1
  rw [nijenhuis_vertical_vertical J i α j hJ hα hj v w,
    fiber_nijenhuis_eq_zero_of_finrank_le_two hdim hj hj_sq v w]
  -- On `𝓘(ℝ, B × V)`, the tangent-space zero at `p` is the model-space pair `(0, 0)`.
  exact Prod.mk_zero_zero

include hJ hα hj in
/-- On fibres of real dimension at most `2`, vanishing of `J.nijenhuis p` reduces to the mixed and
horizontal family equations. -/
theorem nijenhuis_eq_zero_iff_of_finrank_le_two (hdim : Module.finrank ℝ V ≤ 2) :
    J.nijenhuis p = 0 ↔
      (∀ a v, mixedTerm i α j p a v = 0) ∧
        (∀ a b, horizontalTerm i α j p a b = 0) := by
  rw [nijenhuis_eq_zero_iff J i α j hJ hα hj]
  exact and_congr_right fun _ ↦ and_iff_left
    (nijenhuis_vertical_vertical_eq_zero_of_finrank_le_two J i α j hJ hα hj hdim)

include hJ hα hj in
/-- Real surface-fibre (`Module.finrank ℝ V = 2`) specialization of
`nijenhuis_eq_zero_iff_of_finrank_le_two`. -/
theorem nijenhuis_eq_zero_iff_of_finrank_eq_two (hdim : Module.finrank ℝ V = 2) :
    J.nijenhuis p = 0 ↔
      (∀ a v, mixedTerm i α j p a v = 0) ∧
        (∀ a b, horizontalTerm i α j p a b = 0) :=
  nijenhuis_eq_zero_iff_of_finrank_le_two J i α j hJ hα hj hdim.le

end FiniteDimTotal

/-- When `α =ᶠ[𝓝 p] 0`, the horizontal curvature equation vanishes identically at `p`. -/
theorem horizontalTerm_eq_zero_of_eventuallyEq_zero (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    (j : B × V → V →L[ℝ] V) {p : B × V} (hα : α =ᶠ[𝓝 p] 0) (a b : B) :
    horizontalTerm i α j p a b = 0 := by
  simp [horizontalTerm_def, hα.fderiv_eq.trans (fderiv_const_apply 0), hα.self_of_nhds]

/-- When `α =ᶠ[𝓝 p] 0`, `mixedTerm` reduces to the base-holomorphy expression
`∂_a j(v) + j(∂_{i a} j(v))`. -/
theorem mixedTerm_of_eventuallyEq_zero (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    (j : B × V → V →L[ℝ] V) {p : B × V} (hα : α =ᶠ[𝓝 p] 0) (a : B) (v : V) :
    mixedTerm i α j p a v = fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) := by
  simp [mixedTerm_def, hα.fderiv_eq.trans (fderiv_const_apply 0), hα.self_of_nhds,
    Prod.mk_zero_zero]

/-- For a split family (`α =ᶠ[𝓝 p] 0`), integrability at `p` is equivalent to base-holomorphy of
`j` together with fibrewise Nijenhuis vanishing. -/
theorem nijenhuis_eq_zero_iff_of_eventuallyEq_zero [FiniteDimensional ℝ B] [FiniteDimensional ℝ V]
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} (j : B × V → V →L[ℝ] V) {p : B × V}
    (hJ : (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 p]
      blockEndomorphism i α j)
    (hα0 : α =ᶠ[𝓝 p] 0) (hj : DifferentiableAt ℝ j p) :
    J.nijenhuis p = 0 ↔
      (∀ a v, fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) = 0) ∧
        (∀ v w : V, J.nijenhuis p (0, v) (0, w) = 0) := by
  rw [nijenhuis_eq_zero_iff J i α j hJ
    ((differentiableAt_const 0).congr_of_eventuallyEq hα0) hj]
  simp only [mixedTerm_of_eventuallyEq_zero i j hα0,
    horizontalTerm_eq_zero_of_eventuallyEq_zero i j hα0, implies_true, true_and]

/-- For a split family (`α =ᶠ[𝓝 p] 0`) on fibres of real dimension at most `2`
(`Module.finrank ℝ V ≤ 2`), base-holomorphy of `j` is necessary and sufficient for
`J.nijenhuis p = 0`. -/
theorem nijenhuis_eq_zero_iff_of_eventuallyEq_zero_of_finrank_le_two
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V ≤ 2)
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} (j : B × V → V →L[ℝ] V) {p : B × V}
    (hJ : (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 p]
      blockEndomorphism i α j)
    (hα0 : α =ᶠ[𝓝 p] 0) (hj : DifferentiableAt ℝ j p) :
    J.nijenhuis p = 0 ↔
      ∀ a v, fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) = 0 := by
  rw [nijenhuis_eq_zero_iff_of_finrank_le_two J i α j hJ
    ((differentiableAt_const 0).congr_of_eventuallyEq hα0) hj hdim]
  simp only [mixedTerm_of_eventuallyEq_zero i j hα0,
    horizontalTerm_eq_zero_of_eventuallyEq_zero i j hα0, implies_true, and_true]

/-! ### Robbin–Salamon Corrigendum Lemma B (`L_{ζ(a, b)} j = 0`) -/

/-- When `mixedTerm` and `verticalTerm` vanish at `q` (with `j(q)² = -1`), `blockNijenhuisExpr`
reduces on all vectors `U, W` to `(0, -horizontalTerm i α j q U.1 W.1)`. -/
private theorem blockNijenhuisExpr_eq (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {q : B × V} (hα : DifferentiableAt ℝ α q)
    (hj : DifferentiableAt ℝ j q) (hj_sq : ∀ v, j q (j q v) = -v)
    (hmix : ∀ a v, mixedTerm i α j q a v = 0) (hvert : ∀ v w, verticalTerm j q v w = 0)
    (U W : B × V) : blockNijenhuisExpr i α j q U W = (0, -horizontalTerm i α j q U.1 W.1) := by
  have hdecomp : blockNijenhuisExpr i α j q U W =
      blockNijenhuisExpr i α j q (U.1, 0) (W.1, 0) +
        blockNijenhuisExpr i α j q (U.1, 0) (0, W.2) -
        blockNijenhuisExpr i α j q (W.1, 0) (0, U.2) +
        blockNijenhuisExpr i α j q (0, U.2) (0, W.2) := by
    conv_lhs => rw [show U = (U.1, 0) + (0, U.2) by simp, show W = (W.1, 0) + (0, W.2) by simp]
    simp only [blockNijenhuisExpr_def, map_add, add_apply]; abel
  rw [hdecomp, blockNijenhuisExpr_horizontal_horizontal i j hα hj,
    blockNijenhuisExpr_horizontal_vertical i hα hj hj_sq,
    blockNijenhuisExpr_horizontal_vertical i hα hj hj_sq,
    blockNijenhuisExpr_vertical_vertical i hα hj]
  simp [hmix, hvert]

/-- Restricting the block Lie derivative along a vertical vector field `Z` (`(Z q).1 = 0`) to a
vertical vector `(0, v)` gives the fibrewise Lie derivative along `y ↦ (Z (p.1, y)).2`. -/
private theorem lieDerivEndomorphism_vertical_apply (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {Z : B × V → B × V} {p : B × V} (hZ : DifferentiableAt ℝ Z p)
    (hZ1 : ∀ q, (Z q).1 = 0) (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (v : V) :
    lieDerivEndomorphism Z (blockEndomorphism i α j) p (0, v) =
      (0, lieDerivEndomorphism (fun y ↦ (Z (p.1, y)).2) (fun y ↦ j (p.1, y)) p.2 v) := by
  have hdZ1 (u : B × V) : (fderiv ℝ Z p u).1 = 0 := by
    have hf1 := (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.comp p hZ.hasFDerivAt
    rw [show (ContinuousLinearMap.fst ℝ B V ∘ Z) = fun _ ↦ (0 : B) from funext hZ1] at hf1
    exact congrArg (· u) (hf1.unique (hasFDerivAt_const (0 : B) p))
  have hdZ2 (u : V) : fderiv ℝ (fun y ↦ (Z (p.1, y)).2) p.2 u = (fderiv ℝ Z p (0, u)).2 := by
    have hf2 := (ContinuousLinearMap.snd ℝ B V).hasFDerivAt.comp p.2
      (hZ.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2))
    simpa [Function.comp_def] using congrArg (· u) hf2.fderiv
  simp only [lieDerivEndomorphism_apply, blockEndomorphism_apply, map_zero, zero_add,
    fderiv_blockEndomorphism_apply i hα hj, fderiv_fiber_apply hj, hdZ2]
  rw [(Prod.ext (hZ1 p) rfl : Z p = (0, (Z p).2))]; ext <;> simp [hdZ1]

/-- When `mixedTerm` and `verticalTerm` vanish at `q`, `L_{A Y} A (q)` and `A(q) ∘ L_Y A (q)`
agree on every vertical vector `(0, v)`. -/
private theorem lieDerivEndomorphism_blockEndomorphism_apply_zero_snd (i : B →L[ℝ] B)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {Y : B × V → B × V} {q : B × V}
    (hαq : DifferentiableAt ℝ α q) (hjq : DifferentiableAt ℝ j q) (hjsqq : ∀ v, j q (j q v) = -v)
    (hAsqq : ∀ u, blockEndomorphism i α j q (blockEndomorphism i α j q u) = -u)
    (hmixq : ∀ a v, mixedTerm i α j q a v = 0) (hvertq : ∀ v w, verticalTerm j q v w = 0)
    (hYq : DifferentiableAt ℝ Y q) (v : V) :
    lieDerivEndomorphism (fun r ↦ blockEndomorphism i α j r (Y r))
        (blockEndomorphism i α j) q (0, v) =
      blockEndomorphism i α j q (lieDerivEndomorphism Y (blockEndomorphism i α j) q (0, v)) := by
  have hN0 : blockNijenhuisExpr i α j q (Y q) (0, v) = 0 := by
    rw [blockNijenhuisExpr_eq i hαq hjq hjsqq hmixq hvertq]
    simp [horizontalTerm_def, Prod.mk_zero_zero]
  rw [blockNijenhuisExpr_def] at hN0
  exact eq_of_sub_eq_zero ((lieDerivEndomorphism_apply_sub_apply
    (differentiableAt_blockEndomorphism i hαq hjq) hYq hAsqq (0, v)).trans hN0)

/-- The `J`-compatible lift `q ↦ (c, (1/2) • j(q)(α(q) c))` of a constant base vector `c`, chosen
so that `blockEndomorphism i α j q (horizontalLiftHalf α j c q) = horizontalLiftHalf α j (i c) q`
whenever `j(q)² = -1` and `α(q)` is `(i, j(q))`-antilinear. -/
private def horizontalLiftHalf (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V)
    (c : B) (q : B × V) : B × V := (c, (2⁻¹ : ℝ) • j q (α q c))

private theorem contDiffAt_horizontalLiftHalf {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    {n : ℕ∞ω} {p : B × V} (hα : ContDiffAt ℝ n α p) (hj : ContDiffAt ℝ n j p) (c : B) :
    ContDiffAt ℝ n (horizontalLiftHalf α j c) p :=
  contDiffAt_const.prodMk (contDiffAt_const.smul (hj.clm_apply (hα.clm_apply contDiffAt_const)))

private theorem fderiv_horizontalLiftHalf_fst {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V}
    {p : B × V} (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (c : B) (u : B × V) :
    (fderiv ℝ (horizontalLiftHalf α j c) p u).1 = 0 := by
  have hd : DifferentiableAt ℝ (horizontalLiftHalf α j c) p := (differentiableAt_const c).prodMk
    ((hj.clm_apply (hα.clm_apply (differentiableAt_const c))).const_smul (2⁻¹ : ℝ))
  exact congrArg (· u) (((ContinuousLinearMap.fst ℝ B V).hasFDerivAt.comp p hd.hasFDerivAt).unique
    (hasFDerivAt_const c p))

private theorem blockEndomorphism_horizontalLiftHalf_eventuallyEq (i : B →L[ℝ] B)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0) (c : B) :
    (fun q ↦ blockEndomorphism i α j q (horizontalLiftHalf α j c q)) =ᶠ[𝓝 p]
      horizontalLiftHalf α j (i c) := by
  filter_upwards [hj_sq, hαj] with q hjq hαjq
  simp only [horizontalLiftHalf, blockEndomorphism_apply, map_smul, hjq,
    eq_neg_of_add_eq_zero_left (hαjq c), map_neg, smul_neg, neg_neg]
  ext <;> [rfl; module]

/-- Express `q ↦ (0, -horizontalTerm i α j q a b)` near `p` as the Nijenhuis Lie-bracket
combination of the lifts `horizontalLiftHalf α j`. -/
private theorem neg_horizontalTerm_eventuallyEq_lieBracket {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ᶠ q in 𝓝 p, ∀ v w, verticalTerm j q v w = 0) (a b : B) :
    (fun q ↦ ((0 : B), -horizontalTerm i α j q a b)) =ᶠ[𝓝 p]
      lieBracket ℝ (horizontalLiftHalf α j (i a)) (horizontalLiftHalf α j (i b)) -
        lieBracket ℝ (horizontalLiftHalf α j a) (horizontalLiftHalf α j b) -
        (fun q ↦ blockEndomorphism i α j q
          (lieBracket ℝ (horizontalLiftHalf α j (i a)) (horizontalLiftHalf α j b) q)) -
        (fun q ↦ blockEndomorphism i α j q
          (lieBracket ℝ (horizontalLiftHalf α j a) (horizontalLiftHalf α j (i b)) q)) := by
  have hAsq_ev : ∀ᶠ q in 𝓝 p,
      ∀ u, blockEndomorphism i α j q (blockEndomorphism i α j q u) = -u :=
    (hj_sq.and hαj).mono fun q ⟨hjq, hαjq⟩ u ↦
      congrArg (· u) ((blockEndomorphism_comp_self_eq_neg_id_iff i α j q).2 ⟨hi, hjq, hαjq⟩)
  filter_upwards [hα.eventually_differentiableAt one_le_two,
    hj.eventually_differentiableAt one_le_two, hj_sq, hAsq_ev, hmix, hvert,
    (contDiffAt_horizontalLiftHalf hα hj a).eventually_differentiableAt one_le_two,
    (contDiffAt_horizontalLiftHalf hα hj b).eventually_differentiableAt one_le_two,
    (blockEndomorphism_horizontalLiftHalf_eventuallyEq i hj_sq hαj a).eventuallyEq_nhds,
    (blockEndomorphism_horizontalLiftHalf_eventuallyEq i hj_sq hαj b).eventuallyEq_nhds] with
    q hαq hjq hjsqq hAsqq hmixq hvertq hXaq hXbq hAXaq hAXbq
  simp only [Pi.sub_apply]
  have hN : blockNijenhuisExpr i α j q (horizontalLiftHalf α j a q) (horizontalLiftHalf α j b q) =
      (0, -horizontalTerm i α j q a b) :=
    blockNijenhuisExpr_eq i hαq hjq hjsqq hmixq hvertq
      (horizontalLiftHalf α j a q) (horizontalLiftHalf α j b q)
  rw [← hN, blockNijenhuisExpr_def, ← hAXaq.lieBracket_vectorField_eq hAXbq,
    ← hAXaq.lieBracket_vectorField_eq (.refl _ _),
    ← (Filter.EventuallyEq.refl _ _).lieBracket_vectorField_eq hAXbq]
  exact (lieBracket_apply_sub_lieBracket_eq
    (differentiableAt_blockEndomorphism i hαq hjq) hXaq hXbq hAsqq).symm

/-- Projection `(a, v) ↦ (0, v)` onto the vertical factor of `B × V`. -/
private def verticalProj : (B × V) →L[ℝ] B × V :=
  (0 : (B × V) →L[ℝ] B).prod (ContinuousLinearMap.snd ℝ B V)

@[simp]
private theorem verticalProj_apply (w : B × V) : verticalProj w = (0, w.2) := (rfl)

/-- Restriction `(L_{X c} A) ∘ verticalProj` of the block Lie derivative to vertical inputs. -/
private def verticalLieDeriv (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (c : B) (q : B × V) : (B × V) →L[ℝ] B × V :=
  (lieDerivEndomorphism (horizontalLiftHalf α j c) (blockEndomorphism i α j) q).comp verticalProj

@[simp]
private theorem verticalLieDeriv_apply (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (c : B) (q w : B × V) : verticalLieDeriv i α j c q w =
      lieDerivEndomorphism (horizontalLiftHalf α j c) (blockEndomorphism i α j) q (0, w.2) := (rfl)

/-- On vertical vectors `(0, v)`, taking `L_{X c₁}` of `L_{X c₂} A` agrees with taking `L_{X c₁}`
of `verticalLieDeriv i α j c₂` because `D(X c₁)(0, v)` is purely vertical. -/
private theorem lieDerivEndomorphism_lieDerivEndomorphism_eq_verticalLieDeriv (i : B →L[ℝ] B)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p) (c₁ c₂ : B) (v : V) :
    lieDerivEndomorphism (horizontalLiftHalf α j c₁)
        (lieDerivEndomorphism (horizontalLiftHalf α j c₂) (blockEndomorphism i α j)) p (0, v) =
      lieDerivEndomorphism (horizontalLiftHalf α j c₁)
        (verticalLieDeriv i α j c₂) p (0, v) := by
  have h11 : (1 + 1 : ℕ∞ω) ≤ 2 := by norm_cast
  have hD_diff : DifferentiableAt ℝ
      (lieDerivEndomorphism (horizontalLiftHalf α j c₂) (blockEndomorphism i α j)) p :=
    (contDiffAt_lieDerivEndomorphism (contDiffAt_horizontalLiftHalf hα hj c₂)
      (contDiffAt_blockEndomorphism i hα hj) h11).differentiableAt_one
  have hdE : fderiv ℝ (verticalLieDeriv i α j c₂) p =
      (ContinuousLinearMap.compL ℝ (B × V) (B × V) (B × V)).flip verticalProj ∘L
        fderiv ℝ (lieDerivEndomorphism (horizontalLiftHalf α j c₂)
          (blockEndomorphism i α j)) p := by
    have hfun : verticalLieDeriv i α j c₂ = fun q ↦
      (lieDerivEndomorphism (horizontalLiftHalf α j c₂) (blockEndomorphism i α j) q).comp
        verticalProj := rfl
    rw [hfun]
    simpa using (hD_diff.hasFDerivAt.clm_comp
      (hasFDerivAt_const (verticalProj (B := B) (V := V)) p)).fderiv
  have hdX : (0, (fderiv ℝ (horizontalLiftHalf α j c₁) p (0, v)).2) =
      fderiv ℝ (horizontalLiftHalf α j c₁) p (0, v) :=
    Prod.ext (fderiv_horizontalLiftHalf_fst ((hα.of_le one_le_two).differentiableAt_one)
      ((hj.of_le one_le_two).differentiableAt_one) c₁ (0, v)).symm rfl
  simp only [lieDerivEndomorphism_apply, hdE, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    verticalProj_apply, verticalLieDeriv_apply, hdX]

/-- Near `p`, `verticalLieDeriv i α j (i c)` equals `A ∘ verticalLieDeriv i α j c`. -/
private theorem verticalLieDeriv_complex_eventuallyEq {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ᶠ q in 𝓝 p, ∀ v w, verticalTerm j q v w = 0) (c : B) :
    verticalLieDeriv i α j (i c) =ᶠ[𝓝 p]
      fun q ↦ (blockEndomorphism i α j q).comp (verticalLieDeriv i α j c q) := by
  have hAsq_ev : ∀ᶠ q in 𝓝 p,
      ∀ u, blockEndomorphism i α j q (blockEndomorphism i α j q u) = -u :=
    (hj_sq.and hαj).mono fun q ⟨hjq, hαjq⟩ u ↦
      congrArg (· u) ((blockEndomorphism_comp_self_eq_neg_id_iff i α j q).2 ⟨hi, hjq, hαjq⟩)
  filter_upwards [hα.eventually_differentiableAt one_le_two,
    hj.eventually_differentiableAt one_le_two, hj_sq, hAsq_ev, hmix, hvert,
    (contDiffAt_horizontalLiftHalf hα hj c).eventually_differentiableAt one_le_two,
    (blockEndomorphism_horizontalLiftHalf_eventuallyEq i hj_sq hαj c).eventuallyEq_nhds] with
    q hαq hjq hjsqq hAsqq hmixq hvertq hXcq hAXcq
  refine ContinuousLinearMap.ext fun w ↦ ?_
  simp only [verticalLieDeriv_apply, ContinuousLinearMap.comp_apply,
    ← hAXcq.lieDerivEndomorphism_eq (.refl _ _)]
  exact lieDerivEndomorphism_blockEndomorphism_apply_zero_snd i hαq hjq hjsqq hAsqq hmixq hvertq
    hXcq w.2

/-- Leibniz expansion of `L_{X c₁} (verticalLieDeriv (i c₂))` at `p` on `(0, v)`. -/
private theorem lieDerivEndomorphism_verticalLieDeriv_complex_apply {i : B →L[ℝ] B}
    (hi : ∀ a, i (i a) = -a) {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ᶠ q in 𝓝 p, ∀ v w, verticalTerm j q v w = 0) (c₁ c₂ : B) (v : V) :
    lieDerivEndomorphism (horizontalLiftHalf α j c₁) (verticalLieDeriv i α j (i c₂)) p (0, v) =
      verticalLieDeriv i α j c₁ p (verticalLieDeriv i α j c₂ p (0, v)) +
        blockEndomorphism i α j p (lieDerivEndomorphism (horizontalLiftHalf α j c₁)
          (verticalLieDeriv i α j c₂) p (0, v)) := by
  have h11 : (1 + 1 : ℕ∞ω) ≤ 2 := by norm_cast
  have hα1 : DifferentiableAt ℝ α p := (hα.of_le one_le_two).differentiableAt_one
  have hj1 : DifferentiableAt ℝ j p := (hj.of_le one_le_two).differentiableAt_one
  have hE_diff : DifferentiableAt ℝ (verticalLieDeriv i α j c₂) p :=
    ((contDiffAt_lieDerivEndomorphism (contDiffAt_horizontalLiftHalf hα hj c₂)
      (contDiffAt_blockEndomorphism i hα hj) h11).differentiableAt_one).clm_comp
      (differentiableAt_const _)
  have hEw_fst (w : B × V) : (verticalLieDeriv i α j c₂ p w).1 = 0 := by
    simp only [verticalLieDeriv_apply, lieDerivEndomorphism_apply,
      fderiv_blockEndomorphism_apply i hα1 hj1, blockEndomorphism_apply, map_zero,
      Prod.fst_add, Prod.fst_sub, fderiv_horizontalLiftHalf_fst hα1 hj1, add_zero, sub_self]
  have hDE_eq_EE (w : B × V) :
      lieDerivEndomorphism (horizontalLiftHalf α j c₁) (blockEndomorphism i α j) p
          (verticalLieDeriv i α j c₂ p w) =
        verticalLieDeriv i α j c₁ p (verticalLieDeriv i α j c₂ p w) := by
    rw [verticalLieDeriv_apply i α j c₁,
      (Prod.ext (hEw_fst w).symm rfl :
        (0, (verticalLieDeriv i α j c₂ p w).2) = verticalLieDeriv i α j c₂ p w)]
  rw [(Filter.EventuallyEq.refl (𝓝 p) _).lieDerivEndomorphism_eq
      (verticalLieDeriv_complex_eventuallyEq hi hα hj hj_sq hαj hmix hvert c₂),
    lieDerivEndomorphism_comp (differentiableAt_blockEndomorphism i hα1 hj1) hE_diff]
  simp only [add_apply, ContinuousLinearMap.comp_apply, hDE_eq_EE]

/-- **Robbin–Salamon Corrigendum Lemma B** (on arbitrary real normed spaces under `C²` regularity):
if `i² = -1`, `j(q)² = -1`, `α(q)(i a) + j(q)(α(q) a) = 0`, `mixedTerm i α j q = 0`, and
`verticalTerm j q = 0` on a neighborhood of `p`, then the fibre vector field
`y ↦ horizontalTerm i α j (p.1, y) a b` has vanishing endomorphism Lie derivative on `j(p.1, ·)`
at `p.2`. -/
theorem lieDerivEndomorphism_horizontalTerm_eq_zero {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ᶠ q in 𝓝 p, ∀ v w, verticalTerm j q v w = 0) (a b : B) :
    lieDerivEndomorphism (fun y ↦ horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 = 0 := by
  -- Step 1: Write `Z q = (0, -horizontalTerm i α j q a b)` near `p` as the Nijenhuis Lie-bracket
  -- combination of `X c = horizontalLiftHalf α j c`, giving `DifferentiableAt ℝ Z p`.
  let A : B × V → (B × V) →L[ℝ] B × V := blockEndomorphism i α j
  let X : B → B × V → B × V := horizontalLiftHalf α j
  let Z : B × V → B × V := fun q ↦ (0, -horizontalTerm i α j q a b)
  have hA : ContDiffAt ℝ 2 A p := contDiffAt_blockEndomorphism i hα hj
  have h11 : (1 + 1 : ℕ∞ω) ≤ 2 := by norm_cast
  have hα1 : DifferentiableAt ℝ α p := (hα.of_le one_le_two).differentiableAt_one
  have hj1 : DifferentiableAt ℝ j p := (hj.of_le one_le_two).differentiableAt_one
  have hAp : DifferentiableAt ℝ A p := differentiableAt_blockEndomorphism i hα1 hj1
  have hAsqp (u : B × V) : A p (A p u) = -u := congrArg (· u)
    ((blockEndomorphism_comp_self_eq_neg_id_iff i α j p).2
      ⟨hi, hj_sq.self_of_nhds, hαj.self_of_nhds⟩)
  have hZ_eq := neg_horizontalTerm_eventuallyEq_lieBracket hi hα hj hj_sq hαj hmix hvert a b
  have hbr_c1 (c₁ c₂ : B) : ContDiffAt ℝ 1 (lieBracket ℝ (X c₁) (X c₂)) p := by
    have hX1 := contDiffAt_horizontalLiftHalf hα hj c₁
    have hX2 := contDiffAt_horizontalLiftHalf hα hj c₂
    rw [show lieBracket ℝ (X c₁) (X c₂) = fun q ↦
      fderiv ℝ (X c₂) q (X c₁ q) - fderiv ℝ (X c₁) q (X c₂ q) by funext q; simp [lieBracket_eq]]
    exact ((hX2.fderiv_right h11).clm_apply (hX1.of_le one_le_two)).sub
      ((hX1.fderiv_right h11).clm_apply (hX2.of_le one_le_two))
  have hbr_d (c₁ c₂ : B) : DifferentiableAt ℝ (lieBracket ℝ (X c₁) (X c₂)) p :=
    (hbr_c1 c₁ c₂).differentiableAt_one
  have hZ_diff : DifferentiableAt ℝ Z p :=
    ((((hbr_c1 (i a) (i b)).sub (hbr_c1 a b)).sub ((hA.of_le one_le_two).clm_apply
      (hbr_c1 (i a) b))).sub ((hA.of_le one_le_two).clm_apply
      (hbr_c1 a (i b)))).differentiableAt_one.congr_of_eventuallyEq hZ_eq
  -- Step 2: Expand `L_Z A (p) (0, v)` via the `C²` Lie-bracket commutator identity, rewrite
  -- vertical evaluations through `verticalLieDeriv`, apply `verticalLieDeriv_complex_eventuallyEq`
  -- and the composition Leibniz rule, and cancel all terms using `A(p)² = -1`.
  ext v
  have hLZ_zero : lieDerivEndomorphism Z A p (0, v) = 0 := by
    have hn2 : minSmoothness ℝ 2 ≤ 2 := by simp
    have hX (c : B) : ContDiffAt ℝ 2 (X c) p := contDiffAt_horizontalLiftHalf hα hj c
    have hLD := lieDerivEndomorphism_lieDerivEndomorphism_eq_verticalLieDeriv i hα hj
    have hLAE := lieDerivEndomorphism_verticalLieDeriv_complex_apply hi hα hj hj_sq hαj hmix hvert
    rw [hZ_eq.lieDerivEndomorphism_eq (.refl _ A), lieDerivEndomorphism_sub_left
        (((hbr_d (i a) (i b)).sub (hbr_d a b)).sub (hAp.clm_apply (hbr_d (i a) b)))
        (hAp.clm_apply (hbr_d a (i b))),
      lieDerivEndomorphism_sub_left ((hbr_d (i a) (i b)).sub (hbr_d a b))
        (hAp.clm_apply (hbr_d (i a) b)),
      lieDerivEndomorphism_sub_left (hbr_d (i a) (i b)) (hbr_d a b)]
    simp only [sub_apply]
    rw [lieDerivEndomorphism_blockEndomorphism_apply_zero_snd i hα1 hj1 hj_sq.self_of_nhds hAsqp
        hmix.self_of_nhds hvert.self_of_nhds (hbr_d (i a) b),
      lieDerivEndomorphism_blockEndomorphism_apply_zero_snd i hα1 hj1 hj_sq.self_of_nhds hAsqp
        hmix.self_of_nhds hvert.self_of_nhds (hbr_d a (i b)),
      lieDerivEndomorphism_lieBracket hn2 (hX (i a)) (hX (i b)) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX a) (hX b) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX (i a)) (hX b) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX a) (hX (i b)) hA]
    simp only [sub_apply]
    rw [hLD (i a) (i b), hLD (i b) (i a), hLD a b, hLD b a, hLD (i a) b, hLD b (i a),
      hLD a (i b), hLD (i b) a, hLAE (i a) b, hLAE (i b) a, hLAE b a, hLAE a b]
    have hE_i (c : B) (w : B × V) :
        verticalLieDeriv i α j (i c) p w = A p (verticalLieDeriv i α j c p w) := congrArg (· w)
      (verticalLieDeriv_complex_eventuallyEq hi hα hj hj_sq hαj hmix hvert c).self_of_nhds
    simp only [A, hE_i a, hE_i b, map_add, map_sub, hAsqp]; abel
  -- Step 3: Restrict `L_Z A (p) (0, v) = 0` to `{p.1} × V` to obtain `L_{ζ(a, b)} j = 0`.
  have hL_vert := lieDerivEndomorphism_vertical_apply i hZ_diff (fun _ ↦ rfl) hα1 hj1 v
  have hsnd : lieDerivEndomorphism (fun y ↦ -horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 v = 0 := by
    simpa [Z] using congrArg Prod.snd (hL_vert.symm.trans hLZ_zero)
  rw [← Pi.neg_def, lieDerivEndomorphism_neg_left, neg_apply, neg_eq_zero] at hsnd
  simpa using hsnd

/-- Surface-fibre (`Module.finrank ℝ V ≤ 2`) version of
`lieDerivEndomorphism_horizontalTerm_eq_zero`: the `verticalTerm` hypothesis is discharged
automatically. -/
theorem lieDerivEndomorphism_horizontalTerm_eq_zero_of_finrank_le_two
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V ≤ 2)
    {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0) (a b : B) :
    lieDerivEndomorphism (fun y ↦ horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 = 0 :=
  lieDerivEndomorphism_horizontalTerm_eq_zero hi hα hj hj_sq hαj hmix
    ((hj.eventually_differentiableAt one_le_two |>.and hj_sq.eventually_nhds).mono
      fun _ ⟨hjq, hjsqq⟩ ↦ fiber_nijenhuis_eq_zero_of_finrank_le_two hdim hjq hjsqq) a b

end TauCeti.ComplexStructureFamily
