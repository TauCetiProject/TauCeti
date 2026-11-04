/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.EndomorphismLieDeriv
public import TauCeti.Geometry.Manifold.Complex.Family.Block
import TauCeti.Geometry.Symplectic.Finrank
import Mathlib.Tactic.Module

/-!
# Integrability of product-trivialized almost complex families

In a product trivialization `B × V` over a base `B` with constant complex structure `i`, an almost
complex family of block form `J(p)(a, v) = (i a, α(p) a + j(p) v)` has three Nijenhuis components
(`TauCeti.ComplexStructureFamily.nijenhuis_eq_zero_iff`): the mixed equation `mixedTerm`, the
horizontal curvature equation `horizontalTerm`, and the vertical fibre Nijenhuis component.

This file develops the Lie-derivative and integrability theory of these equations:

1. **Lie-derivative and Lie-bracket dictionary**: `mixedTerm_eq_add_lieDerivEndomorphism` rewrites
   `mixedTerm` as `∂_a j + j ∂_{i a} j + j L_{α a} j`, and `horizontalTerm_eq_sub_lieBracket`
   relates `horizontalTerm` to Mathlib's `VectorField.lieBracket` (with the opposite sign from
   Robbin–Salamon's source bracket).
2. **Horizontal connection dictionary**: when `α` arises from a horizontal connection lift
   `(a, -v(a))` via `connectionOfHorizontal i v j q a = j(q)(v(q) a + j(q)(v(q)(i a)))`,
   `mixedTerm_connectionOfHorizontal` identifies `mixedTerm` (when the vertical Nijenhuis
   expression vanishes) with `(∂_a j - L_{v a} j) + j (∂_{i a} j - L_{v(i a)} j)`, matching
   horizontal `∂bar^H j` for a symplectic horizontal connection.
3. **Surface-fibre and split-family criteria**: when `Module.finrank ℝ V ≤ 2` (in particular on
   real 2-dimensional surface fibres), the vertical Nijenhuis component vanishes automatically
   (`nijenhuis_eq_zero_iff_of_finrank_le_two`, `nijenhuis_eq_zero_iff_of_finrank_eq_two`). When
   `α =ᶠ[𝓝 p] 0`, `horizontalTerm` vanishes and `mixedTerm` reduces to base-holomorphy
   `∂_a j + j ∂_{i a} j = 0` (`nijenhuis_eq_zero_iff_of_eventuallyEq_zero_of_finrank_eq_two`).
4. **Robbin–Salamon Corrigendum Lemma B**: `lieDerivEndomorphism_horizontalTerm_eq_zero` proves on
   arbitrary real normed spaces `B, V` under `C²` regularity of `α` and `j` that if `mixedTerm`
   and the vertical Nijenhuis expression vanish on a neighborhood of `p` (automatic when
   `Module.finrank ℝ V ≤ 2`, `lieDerivEndomorphism_horizontalTerm_eq_zero_of_finrank_le_two`), then
   the horizontal curvature `y ↦ horizontalTerm i α j (p.1, y) a b` is an infinitesimal
   automorphism of the fibre complex structure (`L_{ζ(a, b)} j = 0` at `p.2`). Consequently, along
   any surface fibre admitting no nonzero `j`-infinitesimal automorphisms (such as closed curves in
   the stable range), local vanishing of `mixedTerm` alone implies full Nijenhuis vanishing
   (`nijenhuis_eq_zero_of_mixedTerm_eq_zero_fiber`).

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

/-- Directional derivative along the fibre `{p.1} × V` of `y ↦ α (p.1, y) a`. -/
theorem fderiv_fiber_connection {α : B × V → B →L[ℝ] V} {p : B × V}
    (hα : DifferentiableAt ℝ α p) (a : B) (v : V) :
    fderiv ℝ (fun y ↦ α (p.1, y) a) p.2 v = fderiv ℝ α p (0, v) a := by
  have he : HasFDerivAt (fun y : V ↦ (p.1, y))
      ((0 : V →L[ℝ] B).prod (ContinuousLinearMap.id ℝ V)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd := ((hα.hasFDerivAt.comp p.2 he).clm_apply (hasFDerivAt_const a p.2)).fderiv
  simpa using congrArg (fun D : V →L[ℝ] V ↦ D v) hd

/-- Directional derivative along the fibre `{p.1} × V` of `y ↦ j (p.1, y)`. -/
theorem fderiv_fiber_apply {j : B × V → V →L[ℝ] V} {p : B × V}
    (hj : DifferentiableAt ℝ j p) (u v : V) :
    fderiv ℝ (fun y ↦ j (p.1, y)) p.2 u v = fderiv ℝ j p (0, u) v := by
  have he : HasFDerivAt (fun y : V ↦ (p.1, y))
      ((0 : V →L[ℝ] B).prod (ContinuousLinearMap.id ℝ V)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd := (hj.hasFDerivAt.comp p.2 he).fderiv
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
Nijenhuis expression of `j` vanishes at `p`, `mixedTerm` equals
`(∂_a j - L_{v a} j) + j (∂_{i a} j - L_{v(i a)} j)`, the complex-antilinear part of the covariant
horizontal derivative `∇^H_a j = ∂_a j - L_{v a} j` along `(a, -v(a))`. -/
theorem mixedTerm_connectionOfHorizontal (i : B →L[ℝ] B) {v : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {p : B × V}
    (hv : DifferentiableAt ℝ v p) (hj : DifferentiableAt ℝ j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ w, j q (j q w) = -w)
    (hvert : ∀ u w, fderiv ℝ j p (0, j p u) w - fderiv ℝ j p (0, j p w) u +
      j p (fderiv ℝ j p (0, w) u) - j p (fderiv ℝ j p (0, u) w) = 0)
    (a : B) (w : V) :
    mixedTerm i (connectionOfHorizontal i v j) j p a w =
      (fderiv ℝ j p (a, 0) w -
          lieDerivEndomorphism (fun y ↦ v (p.1, y) a) (fun y ↦ j (p.1, y)) p.2 w) +
        j p (fderiv ℝ j p (i a, 0) w -
          lieDerivEndomorphism (fun y ↦ v (p.1, y) (i a)) (fun y ↦ j (p.1, y)) p.2 w) := by
  have hα : DifferentiableAt ℝ (connectionOfHorizontal i v j) p :=
    hj.clm_comp (hv.add (hj.clm_comp (hv.clm_comp (differentiableAt_const i))))
  have he : DifferentiableAt ℝ (fun y : V ↦ (p.1, y)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
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
      fderiv_fiber_apply hj, fderiv_fiber_apply hj, fderiv_fiber_apply hj, fderiv_fiber_apply hj]
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
fibrewise Nijenhuis expression of `j` vanishes automatically at `p`. -/
theorem fiber_nijenhuis_eq_zero_of_finrank_le_two [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 2) {j : B × V → V →L[ℝ] V} {p : B × V}
    (hj : DifferentiableAt ℝ j p) (hj_sq : ∀ᶠ q in 𝓝 p, ∀ w, j q (j q w) = -w)
    (u w : V) :
    fderiv ℝ j p (0, j p u) w - fderiv ℝ j p (0, j p w) u +
      j p (fderiv ℝ j p (0, w) u) - j p (fderiv ℝ j p (0, u) w) = 0 := by
  have he : DifferentiableAt ℝ (fun y : V ↦ (p.1, y)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
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
  let D : V →L[ℝ] V →L[ℝ] V :=
    (fderiv ℝ j p).comp ((0 : V →L[ℝ] B).prod (ContinuousLinearMap.id ℝ V))
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
    change Nf v (j p v) = 0
    simp only [Nf, LinearMap.mk₂_apply, hj_sq.self_of_nhds, map_neg, neg_apply, h1, h2]
    abel
  simpa [Nf, D] using LinearMap.congr_fun₂
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
    fiber_nijenhuis_eq_zero_of_finrank_le_two hdim hj hj_sq v w]; rfl

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

/-- For a split family (`α =ᶠ[𝓝 p] 0`) with surface fibres (`Module.finrank ℝ V = 2`),
base-holomorphy of `j` is necessary and sufficient for `J.nijenhuis p = 0`. -/
theorem nijenhuis_eq_zero_iff_of_eventuallyEq_zero_of_finrank_eq_two
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V} (j : B × V → V →L[ℝ] V) {p : B × V}
    (hJ : (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 p]
      blockEndomorphism i α j)
    (hα0 : α =ᶠ[𝓝 p] 0) (hj : DifferentiableAt ℝ j p) :
    J.nijenhuis p = 0 ↔
      ∀ a v, fderiv ℝ j p (a, 0) v + j p (fderiv ℝ j p (i a, 0) v) = 0 := by
  rw [nijenhuis_eq_zero_iff_of_finrank_eq_two J i α j hJ
    ((differentiableAt_const 0).congr_of_eventuallyEq hα0) hj hdim]
  simp only [mixedTerm_of_eventuallyEq_zero i j hα0,
    horizontalTerm_eq_zero_of_eventuallyEq_zero i j hα0, implies_true, and_true]

/-! ### Robbin–Salamon Corrigendum Lemma B (`L_{ζ(a, b)} j = 0`) -/

private def blockNijenhuisExpr (i : B →L[ℝ] B) (α : B × V → B →L[ℝ] V)
    (j : B × V → V →L[ℝ] V) (q U W : B × V) : B × V :=
  let A := blockEndomorphism i α j
  fderiv ℝ A q (A q U) W - fderiv ℝ A q (A q W) U +
    A q (fderiv ℝ A q W U) - A q (fderiv ℝ A q U W)

private theorem blockNijenhuisExpr_eq (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {q : B × V}
    (hα : DifferentiableAt ℝ α q) (hj : DifferentiableAt ℝ j q)
    (hj_sq : ∀ v, j q (j q v) = -v)
    (hmix : ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ v w, fderiv ℝ j q (0, j q v) w - fderiv ℝ j q (0, j q w) v +
      j q (fderiv ℝ j q (0, w) v) - j q (fderiv ℝ j q (0, v) w) = 0)
    (U W : B × V) :
    blockNijenhuisExpr i α j q U W = (0, -horizontalTerm i α j q U.1 W.1) := by
  have hsplit (c : B) : (i c, α q c) = (i c, 0) + (0, α q c) := by simp
  have hmv (a : B) (v : V) : blockNijenhuisExpr i α j q (a, 0) (0, v) = 0 := by
    simp only [blockNijenhuisExpr, blockEndomorphism_apply, map_zero, add_zero, zero_add]
    rw [hsplit a, map_add]
    simp only [add_apply, fderiv_blockEndomorphism_apply i hα hj, map_zero,
      add_zero, zero_add, Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero]
    refine Prod.ext (by simp) (calc
      _ = -j q (mixedTerm i α j q a v) := by
        simp only [mixedTerm_def, map_add, map_sub, map_neg, hj_sq]; abel
      _ = 0 := by rw [hmix a v, map_zero, neg_zero])
  have hvm (v : V) (a : B) : blockNijenhuisExpr i α j q (0, v) (a, 0) = 0 := by
    rw [show blockNijenhuisExpr i α j q (0, v) (a, 0) =
        -blockNijenhuisExpr i α j q (a, 0) (0, v) by simp only [blockNijenhuisExpr]; abel,
      hmv, neg_zero]
  have hvv (v w : V) : blockNijenhuisExpr i α j q (0, v) (0, w) = 0 := by
    simp only [blockNijenhuisExpr, blockEndomorphism_apply, map_zero, zero_add,
      fderiv_blockEndomorphism_apply i hα hj, Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero]
    exact Prod.ext (by simp) (hvert v w)
  have hhh (a b : B) : blockNijenhuisExpr i α j q (a, 0) (b, 0) =
      (0, -horizontalTerm i α j q a b) := by
    simp only [blockNijenhuisExpr, blockEndomorphism_apply, map_zero, add_zero]
    rw [hsplit a, hsplit b, map_add, map_add]
    simp only [add_apply, fderiv_blockEndomorphism_apply i hα hj, map_zero, add_zero,
      zero_add, Prod.mk_add_mk, Prod.mk_sub_mk, sub_zero, horizontalTerm_def]
    ext <;> [simp; abel_nf]
  have hbilin : blockNijenhuisExpr i α j q U W =
      blockNijenhuisExpr i α j q (U.1, 0) (W.1, 0) +
        blockNijenhuisExpr i α j q (U.1, 0) (0, W.2) +
        blockNijenhuisExpr i α j q (0, U.2) (W.1, 0) +
        blockNijenhuisExpr i α j q (0, U.2) (0, W.2) := by
    conv_lhs => rw [show U = (U.1, 0) + (0, U.2) by simp, show W = (W.1, 0) + (0, W.2) by simp]
    simp only [blockNijenhuisExpr, map_add, add_apply]; abel
  rw [hbilin, hhh, hmv, hvm, hvv]; simp

private theorem lieDerivEndomorphism_vertical_apply (i : B →L[ℝ] B) {α : B × V → B →L[ℝ] V}
    {j : B × V → V →L[ℝ] V} {Z : B × V → B × V} {p : B × V}
    (hZ : DifferentiableAt ℝ Z p) (hZ1 : ∀ q, (Z q).1 = 0)
    (hα : DifferentiableAt ℝ α p) (hj : DifferentiableAt ℝ j p) (v : V) :
    lieDerivEndomorphism Z (blockEndomorphism i α j) p (0, v) =
      (0, lieDerivEndomorphism (fun y ↦ (Z (p.1, y)).2) (fun y ↦ j (p.1, y)) p.2 v) := by
  have he : HasFDerivAt (fun y : V ↦ (p.1, y))
      ((0 : V →L[ℝ] B).prod (ContinuousLinearMap.id ℝ V)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hdZ1 (u : B × V) : (fderiv ℝ Z p u).1 = 0 := by
    have hf1 : HasFDerivAt (fun q ↦ (Z q).1)
        ((ContinuousLinearMap.fst ℝ B V).comp (fderiv ℝ Z p)) p :=
      (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.comp p hZ.hasFDerivAt
    rw [funext hZ1] at hf1
    exact congrArg (· u) (hf1.unique (hasFDerivAt_const (0 : B) p))
  have hdZ2 (u : V) : fderiv ℝ (fun y ↦ (Z (p.1, y)).2) p.2 u = (fderiv ℝ Z p (0, u)).2 := by
    have hf2 : HasFDerivAt (fun y ↦ (Z (p.1, y)).2)
        ((ContinuousLinearMap.snd ℝ B V).comp
          ((fderiv ℝ Z p).comp ((0 : V →L[ℝ] B).prod (ContinuousLinearMap.id ℝ V)))) p.2 :=
      (ContinuousLinearMap.snd ℝ B V).hasFDerivAt.comp p.2 (hZ.hasFDerivAt.comp p.2 he)
    simpa using congrArg (· u) hf2.fderiv
  have hZp : Z p = (0, (Z p).2) := Prod.ext (hZ1 p) rfl
  simp only [lieDerivEndomorphism_apply, blockEndomorphism_apply, map_zero, zero_add,
    fderiv_blockEndomorphism_apply i hα hj, fderiv_fiber_apply hj, hdZ2]
  rw [hZp]; ext <;> simp [hdZ1]

/-- **Robbin–Salamon Corrigendum Lemma B** (on arbitrary real normed spaces under `C²` regularity):
if `i² = -1`, `j(q)² = -1`, `α(q)(i a) + j(q)(α(q) a) = 0`, `mixedTerm i α j q = 0`, and the
vertical Nijenhuis expression of `j` vanishes on a neighborhood of `p`, then the fibre vector field
`y ↦ horizontalTerm i α j (p.1, y) a b` has vanishing endomorphism Lie derivative on `j(p.1, ·)`
at `p.2`. -/
theorem lieDerivEndomorphism_horizontalTerm_eq_zero
    {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (hvert : ∀ᶠ q in 𝓝 p, ∀ v w, fderiv ℝ j q (0, j q v) w - fderiv ℝ j q (0, j q w) v +
      j q (fderiv ℝ j q (0, w) v) - j q (fderiv ℝ j q (0, v) w) = 0)
    (a b : B) :
    lieDerivEndomorphism (fun y ↦ horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 = 0 := by
  let A : B × V → (B × V) →L[ℝ] B × V := blockEndomorphism i α j
  have hA : ContDiffAt ℝ 2 A p := contDiffAt_blockEndomorphism i hα hj
  have h11 : (1 + 1 : ℕ∞ω) = 2 := by norm_cast
  have h12 : (1 : ℕ∞ω) ≤ 2 := one_le_two
  have hα_ev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ α q :=
    ((hα.of_le h12).eventually (by simp)).mono fun _ hq ↦ hq.differentiableAt one_ne_zero
  have hj_ev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ j q :=
    ((hj.of_le h12).eventually (by simp)).mono fun _ hq ↦ hq.differentiableAt one_ne_zero
  let X : B → B × V → B × V := fun c q ↦ (c, (2⁻¹ : ℝ) • j q (α q c))
  have hX (c : B) : ContDiffAt ℝ 2 (X c) p := contDiffAt_const.prodMk
    (contDiffAt_const.smul (hj.clm_apply (hα.clm_apply contDiffAt_const)))
  have hX_ev (c : B) : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ (X c) q :=
    (((hX c).of_le h12).eventually (by simp)).mono fun _ hq ↦ hq.differentiableAt one_ne_zero
  have hdX1 (c : B) (u : B × V) : (fderiv ℝ (X c) p u).1 = 0 := by
    have hf1 := (ContinuousLinearMap.fst ℝ B V).hasFDerivAt.comp p
      (((hX c).of_le h12).differentiableAt one_ne_zero).hasFDerivAt
    exact congrArg (· u) (hf1.unique (hasFDerivAt_const c p))
  have hAX (c : B) : (fun q ↦ A q (X c q)) =ᶠ[𝓝 p] X (i c) := by
    filter_upwards [hj_sq, hαj] with q hjq hαjq
    simp only [A, X, blockEndomorphism_apply, map_smul, hjq,
      eq_neg_of_add_eq_zero_left (hαjq c), map_neg, smul_neg, neg_neg]
    ext <;> [rfl; module]
  have hAsq_ev : ∀ᶠ q in 𝓝 p, ∀ u, A q (A q u) = -u := by
    filter_upwards [hj_sq, hαj] with q hjq hαjq u
    exact congrArg (· u) ((blockEndomorphism_comp_self_eq_neg_id_iff i α j q).2 ⟨hi, hjq, hαjq⟩)
  let Z : B × V → B × V := fun q ↦ (0, -horizontalTerm i α j q a b)
  let RHS : B × V → B × V :=
    lieBracket ℝ (X (i a)) (X (i b)) - lieBracket ℝ (X a) (X b) -
      (fun q ↦ A q (lieBracket ℝ (X (i a)) (X b) q)) -
      (fun q ↦ A q (lieBracket ℝ (X a) (X (i b)) q))
  have hZ_eq : Z =ᶠ[𝓝 p] RHS := by
    filter_upwards [hα_ev, hj_ev, hj_sq, hAsq_ev, hmix, hvert,
      hX_ev a, hX_ev b, (hAX a).eventuallyEq_nhds, (hAX b).eventuallyEq_nhds] with
      q hαq hjq hjsqq hAsqq hmixq hvertq hXaq hXbq hAXaq hAXbq
    simp only [Z, RHS, Pi.sub_apply]
    rw [← blockNijenhuisExpr_eq i hαq hjq hjsqq hmixq hvertq (X a q) (X b q),
      ← hAXaq.lieBracket_vectorField_eq hAXbq,
      ← hAXaq.lieBracket_vectorField_eq (Filter.EventuallyEq.refl _ (X b)),
      ← (Filter.EventuallyEq.refl _ (X a)).lieBracket_vectorField_eq hAXbq]
    exact (lieBracket_apply_sub_lieBracket_eq
      (differentiableAt_blockEndomorphism i hαq hjq) hXaq hXbq hAsqq).symm
  have hbr_c1 (c₁ c₂ : B) : ContDiffAt ℝ 1 (lieBracket ℝ (X c₁) (X c₂)) p := by
    rw [show lieBracket ℝ (X c₁) (X c₂) =
        fun q ↦ fderiv ℝ (X c₂) q (X c₁ q) - fderiv ℝ (X c₁) q (X c₂ q) by
      funext q; simp [lieBracket_eq]]
    exact (((hX c₂).fderiv_right h11.le).clm_apply ((hX c₁).of_le h12)).sub
      (((hX c₁).fderiv_right h11.le).clm_apply ((hX c₂).of_le h12))
  have hA1 : ContDiffAt ℝ 1 A p := hA.of_le h12
  have hZ_diff : DifferentiableAt ℝ Z p :=
    (((((hbr_c1 (i a) (i b)).sub (hbr_c1 a b)).sub (hA1.clm_apply (hbr_c1 (i a) b))).sub
      (hA1.clm_apply (hbr_c1 a (i b)))).differentiableAt one_ne_zero).congr_of_eventuallyEq hZ_eq
  let P : (B × V) →L[ℝ] B × V := (0 : (B × V) →L[ℝ] B).prod (ContinuousLinearMap.snd ℝ B V)
  let D : B → B × V → (B × V) →L[ℝ] B × V := fun c ↦ lieDerivEndomorphism (X c) A
  let E : B → B × V → (B × V) →L[ℝ] B × V := fun c q ↦ (D c q).comp P
  have hD_diff (c : B) : DifferentiableAt ℝ (D c) p :=
    (contDiffAt_lieDerivEndomorphism (hX c) hA h11.le).differentiableAt one_ne_zero
  have hAp : DifferentiableAt ℝ A p := hA1.differentiableAt one_ne_zero
  have hLA_vert {q : B × V} {Y : B × V → B × V} (hαq : DifferentiableAt ℝ α q)
      (hjq : DifferentiableAt ℝ j q) (hjsqq : ∀ v, j q (j q v) = -v)
      (hAsqq : ∀ u, A q (A q u) = -u) (hmixq : ∀ a v, mixedTerm i α j q a v = 0)
      (hvertq : ∀ v w, fderiv ℝ j q (0, j q v) w - fderiv ℝ j q (0, j q w) v +
        j q (fderiv ℝ j q (0, w) v) - j q (fderiv ℝ j q (0, v) w) = 0)
      (hYq : DifferentiableAt ℝ Y q) (v : V) :
      lieDerivEndomorphism (fun r ↦ A r (Y r)) A q (0, v) =
        A q (lieDerivEndomorphism Y A q (0, v)) := by
    have hN0 : blockNijenhuisExpr i α j q (Y q) (0, v) = 0 := by
      rw [blockNijenhuisExpr_eq i hαq hjq hjsqq hmixq hvertq]
      simp [horizontalTerm_def, Prod.mk_zero_zero]
    exact eq_of_sub_eq_zero ((lieDerivEndomorphism_apply_sub_apply
      (differentiableAt_blockEndomorphism i hαq hjq) hYq hAsqq (0, v)).trans hN0)
  have hLD_eq_LE (c₁ c₂ : B) (v : V) :
      lieDerivEndomorphism (X c₁) (lieDerivEndomorphism (X c₂) A) p (0, v) =
        lieDerivEndomorphism (X c₁) (E c₂) p (0, v) := by
    have hdE : fderiv ℝ (E c₂) p =
        (ContinuousLinearMap.compL ℝ (B × V) (B × V) (B × V)).flip P ∘L fderiv ℝ (D c₂) p := by
      simpa using ((hD_diff c₂).hasFDerivAt.clm_comp (hasFDerivAt_const P p)).fderiv
    have hPdX : P (fderiv ℝ (X c₁) p (0, v)) = fderiv ℝ (X c₁) p (0, v) :=
      Prod.ext (hdX1 c₁ (0, v)).symm rfl
    simp only [lieDerivEndomorphism_apply, D, E, hdE, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, hPdX]
    rfl
  have hE_ic (c : B) : E (i c) =ᶠ[𝓝 p] fun q ↦ (A q).comp (E c q) := by
    filter_upwards [hα_ev, hj_ev, hj_sq, hAsq_ev, hmix, hvert, hX_ev c,
      (hAX c).eventuallyEq_nhds] with q hαq hjq hjsqq hAsqq hmixq hvertq hXcq hAXcq
    refine ContinuousLinearMap.ext fun w ↦ ?_
    simp only [E, D, ContinuousLinearMap.comp_apply]
    rw [show P w = (0, w.2) from rfl,
      ← hAXcq.lieDerivEndomorphism_eq (Filter.EventuallyEq.refl _ A)]
    exact hLA_vert hαq hjq hjsqq hAsqq hmixq hvertq hXcq w.2
  have hDE_eq_EE (c₁ c₂ : B) (w : B × V) :
      lieDerivEndomorphism (X c₁) A p (E c₂ p w) = E c₁ p (E c₂ p w) := by
    have hEw1 : (E c₂ p w).1 = 0 := by
      simp only [E, D, P, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        zero_apply, ContinuousLinearMap.coe_snd', lieDerivEndomorphism_apply,
        fderiv_blockEndomorphism_apply i hα_ev.self_of_nhds hj_ev.self_of_nhds,
        A, blockEndomorphism_apply, map_zero, Prod.fst_add, Prod.fst_sub, hdX1, add_zero, sub_self]
    have hPEw : P (E c₂ p w) = E c₂ p w := Prod.ext hEw1.symm rfl
    exact (congrArg (lieDerivEndomorphism (X c₁) A p) hPEw).symm
  have hLAE (c₁ c₂ : B) (v : V) :
      lieDerivEndomorphism (X c₁) (E (i c₂)) p (0, v) =
        E c₁ p (E c₂ p (0, v)) + A p (lieDerivEndomorphism (X c₁) (E c₂) p (0, v)) := by
    have hE_diff : DifferentiableAt ℝ (E c₂) p := (hD_diff c₂).clm_comp (differentiableAt_const P)
    rw [(Filter.EventuallyEq.refl (𝓝 p) (X c₁)).lieDerivEndomorphism_eq (hE_ic c₂),
      lieDerivEndomorphism_comp hAp hE_diff]
    simp only [add_apply, ContinuousLinearMap.comp_apply, hDE_eq_EE]
  ext v
  have hLZ_zero : lieDerivEndomorphism Z A p (0, v) = 0 := by
    have hn2 : minSmoothness ℝ 2 ≤ 2 := by simp
    have hbr_d (c₁ c₂ : B) := (hbr_c1 c₁ c₂).differentiableAt one_ne_zero
    rw [hZ_eq.lieDerivEndomorphism_eq (Filter.EventuallyEq.refl _ A)]
    simp only [RHS]
    rw [lieDerivEndomorphism_sub_left
        (((hbr_d (i a) (i b)).sub (hbr_d a b)).sub (hAp.clm_apply (hbr_d (i a) b)))
        (hAp.clm_apply (hbr_d a (i b))),
      lieDerivEndomorphism_sub_left ((hbr_d (i a) (i b)).sub (hbr_d a b))
        (hAp.clm_apply (hbr_d (i a) b)),
      lieDerivEndomorphism_sub_left (hbr_d (i a) (i b)) (hbr_d a b)]
    simp only [sub_apply]
    rw [hLA_vert hα_ev.self_of_nhds hj_ev.self_of_nhds hj_sq.self_of_nhds hAsq_ev.self_of_nhds
        hmix.self_of_nhds hvert.self_of_nhds (hbr_d (i a) b),
      hLA_vert hα_ev.self_of_nhds hj_ev.self_of_nhds hj_sq.self_of_nhds hAsq_ev.self_of_nhds
        hmix.self_of_nhds hvert.self_of_nhds (hbr_d a (i b)),
      lieDerivEndomorphism_lieBracket hn2 (hX (i a)) (hX (i b)) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX a) (hX b) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX (i a)) (hX b) hA,
      lieDerivEndomorphism_lieBracket hn2 (hX a) (hX (i b)) hA]
    simp only [sub_apply]
    rw [hLD_eq_LE (i a) (i b), hLD_eq_LE (i b) (i a), hLD_eq_LE a b, hLD_eq_LE b a,
      hLD_eq_LE (i a) b, hLD_eq_LE b (i a), hLD_eq_LE a (i b), hLD_eq_LE (i b) a,
      hLAE (i a) b, hLAE (i b) a, hLAE b a, hLAE a b]
    have hE_ia (w : B × V) : E (i a) p w = A p (E a p w) := congrArg (· w) (hE_ic a).self_of_nhds
    have hE_ib (w : B × V) : E (i b) p w = A p (E b p w) := congrArg (· w) (hE_ic b).self_of_nhds
    simp only [hE_ia, hE_ib, map_add, map_sub, hAsq_ev.self_of_nhds]
    abel
  have hL_vert := lieDerivEndomorphism_vertical_apply i hZ_diff (fun _ ↦ rfl)
    hα_ev.self_of_nhds hj_ev.self_of_nhds v
  have hsnd : lieDerivEndomorphism (fun y ↦ -horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 v = 0 := by
    simpa [Z] using congrArg Prod.snd (hL_vert.symm.trans hLZ_zero)
  rw [← Pi.neg_def, lieDerivEndomorphism_neg_left, neg_apply, neg_eq_zero] at hsnd
  simpa using hsnd

/-- Surface-fibre (`Module.finrank ℝ V ≤ 2`) version of
`lieDerivEndomorphism_horizontalTerm_eq_zero`: the vertical Nijenhuis hypothesis is discharged
automatically. -/
theorem lieDerivEndomorphism_horizontalTerm_eq_zero_of_finrank_le_two
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V ≤ 2)
    {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    {α : B × V → B →L[ℝ] V} {j : B × V → V →L[ℝ] V} {p : B × V}
    (hα : ContDiffAt ℝ 2 α p) (hj : ContDiffAt ℝ 2 j p)
    (hj_sq : ∀ᶠ q in 𝓝 p, ∀ v, j q (j q v) = -v)
    (hαj : ∀ᶠ q in 𝓝 p, ∀ a, α q (i a) + j q (α q a) = 0)
    (hmix : ∀ᶠ q in 𝓝 p, ∀ a v, mixedTerm i α j q a v = 0)
    (a b : B) :
    lieDerivEndomorphism (fun y ↦ horizontalTerm i α j (p.1, y) a b)
      (fun y ↦ j (p.1, y)) p.2 = 0 := by
  have hj_ev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ j q :=
    ((hj.of_le one_le_two).eventually (by simp)).mono fun _ hq ↦ hq.differentiableAt one_ne_zero
  have hvert : ∀ᶠ q in 𝓝 p, ∀ v w, fderiv ℝ j q (0, j q v) w - fderiv ℝ j q (0, j q w) v +
      j q (fderiv ℝ j q (0, w) v) - j q (fderiv ℝ j q (0, v) w) = 0 := by
    filter_upwards [hj_ev, hj_sq.eventually_nhds] with q hjq hjsqq v w
    exact fiber_nijenhuis_eq_zero_of_finrank_le_two hdim hjq hjsqq v w
  exact lieDerivEndomorphism_horizontalTerm_eq_zero hi hα hj hj_sq hαj hmix hvert a b

/-- **Closed/automorphism-free fibre reconciliation**: along a fibre `{b₀} × V` of real dimension
at most `2` on which `j(b₀, ·)` admits no nonzero infinitesimal automorphisms, if `mixedTerm`
vanishes on a neighborhood of `{b₀} × V`, then the full Nijenhuis tensor `J.nijenhuis` vanishes at
every point of `{b₀} × V`. -/
theorem nijenhuis_eq_zero_of_mixedTerm_eq_zero_fiber
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V ≤ 2)
    (J : SmoothAlmostComplexStructure 𝓘(ℝ, B × V) (B × V))
    {i : B →L[ℝ] B} (hi : ∀ a, i (i a) = -a)
    (α : B × V → B →L[ℝ] V) (j : B × V → V →L[ℝ] V) (b₀ : B)
    (hJ : ∀ y : V, (fun q ↦ (J.toEndomorphism q : (B × V) →L[ℝ] B × V)) =ᶠ[𝓝 (b₀, y)]
      blockEndomorphism i α j)
    (hα : ∀ y : V, ContDiffAt ℝ 2 α (b₀, y))
    (hj : ∀ y : V, ContDiffAt ℝ 2 j (b₀, y))
    (hmix : ∀ y : V, ∀ᶠ q in 𝓝 (b₀, y), ∀ a v, mixedTerm i α j q a v = 0)
    (haut : ∀ ξ : V → V,
      (∀ y : V, lieDerivEndomorphism ξ (fun z ↦ j (b₀, z)) y = 0) → ξ = 0)
    (y : V) :
    J.nijenhuis (b₀, y) = 0 := by
  rw [nijenhuis_eq_zero_iff_of_finrank_le_two J i α j (hJ y)
    (((hα y).of_le one_le_two).differentiableAt one_ne_zero)
    (((hj y).of_le one_le_two).differentiableAt one_ne_zero) hdim]
  refine ⟨(hmix y).self_of_nhds, fun a b ↦
    congrFun (haut (fun w ↦ horizontalTerm i α j (b₀, w) a b) fun z ↦ ?_) y⟩
  have hsq_αj : ∀ᶠ q in 𝓝 (b₀, z),
      (∀ v, j q (j q v) = -v) ∧ (∀ c, α q (i c) + j q (α q c) = 0) :=
    (hJ z).mono fun q hq ↦ ((blockEndomorphism_comp_self_eq_neg_id_iff i α j q).1
      (by rw [← hq]; exact J.square_neg q)).2
  exact lieDerivEndomorphism_horizontalTerm_eq_zero_of_finrank_le_two hdim hi
    (hα z) (hj z) (hsq_αj.mono fun _ h ↦ h.1) (hsq_αj.mono fun _ h ↦ h.2) (hmix z) a b

end TauCeti.ComplexStructureFamily
