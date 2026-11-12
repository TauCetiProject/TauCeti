/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LocalFrame
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic

/-!
# Covariant derivatives of one-parameter families of vector fields

Let `∇` be a covariant derivative on the tangent bundle of a finite-dimensional manifold `M`, and
let `W_s` be a one-parameter family of vector fields which is jointly `C²` in `(s, y)` at
`(t, x)`, as a map into the tangent bundle. This file proves that the parameter derivative
commutes with `∇` at `x`:

`∂ₛ (∇_v W_s)(x) = ∇_v (∂ₛ W_s)(x)` at `s = t`.

No regularity of `∇` is needed: in the trivialization at `x`, `∇_v W_s` is the differential of the
coordinates of `W_s` plus the Christoffel map applied to the value of `W_s` at `x`
(`TauCeti.Manifold.covariantDerivative_symm_comp_apply_symm`). The parameter derivative of the
first term is the differential of the parameter derivative, by the symmetry of mixed partial
derivatives `TauCeti.Manifold.hasDerivAt_mvfderiv_apply`, and the second term is linear in the
value of `W_s`.

This is the step that commutes a time derivative with a fixed connection in the variation
formulas of geometric quantities along a family of metrics.

## Main results

* `TauCeti.Manifold.hasDerivAt_covariantDerivative_apply_of_contMDiffAt`: the parameter
  derivative of `∇_v W_s` is `∇_v` of the parameter derivative of `W_s`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 4:
  the coordinate formula for a connection.
-/

public section

noncomputable section

open Bundle Filter Function
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {W : ℝ → Π y : M, TangentSpace I y} {t : ℝ} {x : M}

/-- Near `x`, the parameter derivative of a family of vector fields which is jointly `C¹` at
`(t, x)` is read, in the trivialization at `x`, by the parameter derivative of its coordinates. -/
private theorem eventually_deriv_eq_symm {n : WithTop ℕ∞} (hn : 1 ≤ n)
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x)) :
    ∀ᶠ y in 𝓝 x, deriv (fun s ↦ W s y) t = (trivializationAt E (TangentSpace I) x).symm y
      (deriv (fun s ↦ (trivializationAt E (TangentSpace I) x ⟨y, W s y⟩).2) t) := by
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hG : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) 1
      (uncurry fun s y ↦ (e (TotalSpace.mk' E y (W s y))).2) (t, x) :=
    (contMDiffAt_totalSpace.mp (hW.of_le hn)).2
  have hG1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp hG
  have hcurve : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ (fun s ↦ (e ⟨y, W s y⟩).2) t :=
    ((continuous_const.prodMk continuous_id).continuousAt.eventually hG1).mono fun y hy ↦
      ((hy.comp t (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
        one_ne_zero).differentiableAt
  filter_upwards [hcurve, e.open_baseSet.mem_nhds hx] with y hy hyb
  -- The fibre `T_y M` is read as the model space `E`.
  let L : E →L[ℝ] E := e.symmL ℝ y
  have hd := (L.hasFDerivAt.comp_hasDerivAt t hy.hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦
      (e.symm_apply_apply_mk hyb (W s y)).symm.trans (e.symmL_apply (R := ℝ) hyb _).symm)
  exact hd.deriv.trans (e.symmL_apply (R := ℝ) hyb _)

/-- **Regularity of the parameter derivative of a family of vector fields.** If a family `W_s` of
vector fields is jointly `C^n` in `(s, y)` at `(t, x)` as a map into the tangent bundle, then its
parameter derivative `y ↦ ∂ₛ W_s(y)` at `s = t` is a `C^m` vector field at `x` whenever
`m + 1 ≤ n`. -/
theorem contMDiffAt_deriv_vectorField_of_contMDiffAt {m n : WithTop ℕ∞}
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) n
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x)) (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) m
      (fun y ↦ TotalSpace.mk' E y (deriv (fun s ↦ W s y) t)) x := by
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have hG' := contMDiffAt_deriv_of_contMDiffAt_uncurry
    (F := fun s y ↦ (e ⟨y, W s y⟩).2) (contMDiffAt_totalSpace.mp hW).2 hmn
  refine (contMDiffAt_section x).2 (hG'.congr_of_eventuallyEq ?_)
  filter_upwards [eventually_deriv_eq_symm (le_trans le_add_self hmn) hW,
    e.open_baseSet.mem_nhds hx] with y hy hyb
  rw [hy, e.apply_mk_symm hyb]

variable [FiniteDimensional ℝ E]

/-- **Parameter derivatives commute with a covariant derivative.** Let `W_s` be a family of vector
fields on `M`, jointly `C²` in `(s, y)` at `(t, x)` as a map into the tangent bundle. Then for
every covariant derivative `∇` on `TM` and every `v ∈ T_x M`, the curve `s ↦ ∇_v W_s` in `T_x M`
has derivative `∇_v W'` at `t`, where `W' y = ∂ₛ W_s(y)` at `s = t`. -/
theorem hasDerivAt_covariantDerivative_apply_of_contMDiffAt
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hW : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E)) 2
      (fun q : ℝ × M ↦ TotalSpace.mk' E q.2 (W q.1 q.2)) (t, x))
    (v : TangentSpace I x) :
    HasDerivAt (fun s ↦ cov (W s) x v) (cov (fun y ↦ deriv (fun s ↦ W s y) t) x v) t := by
  -- Read the family in the trivialization `e` at `x`, with coordinates `G s y`.
  set e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  let b := Module.finBasis ℝ E
  have hcov : IsCovariantDerivativeOn E cov e.baseSet := cov.isCovariantDerivativeOn
  set G : ℝ → M → E := fun s y ↦ (e (TotalSpace.mk' E y (W s y))).2
  have hG : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ, E) 2 (uncurry G) (t, x) :=
    (contMDiffAt_totalSpace.mp hW).2
  set G' : M → E := fun y ↦ deriv (fun s ↦ G s y) t
  have hG' : MDifferentiableAt I 𝓘(ℝ, E) G' x :=
    (contMDiffAt_deriv_of_contMDiffAt_uncurry hG (by norm_num)).mdifferentiableAt one_ne_zero
  have hsymm (σ : Π y : M, TangentSpace I y) :
      ∀ᶠ y in 𝓝 x, σ y = e.symm y ((e (TotalSpace.mk' E y (σ y))).2) :=
    eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ (e.symm_apply_apply_mk hy _).symm
  -- Near `(t, x)` the family is jointly `C¹`, so its slices are differentiable.
  have hW1 := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by simp)).mp (hW.of_le (by norm_num))
  have hslice : ∀ᶠ s in 𝓝 t, MDiffAt (T% (W s)) x :=
    ((continuous_id.prodMk continuous_const).continuousAt.eventually hW1).mono fun s hs ↦
      (hs.comp x (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt one_ne_zero
  have hcurve : DifferentiableAt ℝ (fun s ↦ G s x) t :=
    ((hG.comp t (contMDiffAt_id.prodMk contMDiffAt_const)).mdifferentiableAt
      two_ne_zero).differentiableAt
  -- `v` is the vector with coordinates `u` at `x`.
  set u : E := (e (TotalSpace.mk' E x v)).2
  have hv : e.symm x u = v := e.symm_apply_apply_mk hx v
  -- Both sides, read through the coordinate formula for `∇`.
  have hformula (σ : Π y : M, TangentSpace I y) (g : M → E) (hσ : MDiffAt (T% σ) x)
      (hg : MDifferentiableAt I 𝓘(ℝ, E) g x) (heq : ∀ᶠ y in 𝓝 x, σ y = e.symm y (g y)) :
      cov σ x v = e.symm x (mvfderiv I g x v + christoffelMap b hcov x (g x) u) := by
    have hread : ∀ᶠ y in 𝓝 x, (e ⟨y, e.symm y (g y)⟩).2 = g y :=
      eventually_of_mem (e.open_baseSet.mem_nhds hx) fun y hy ↦ by rw [e.apply_mk_symm hy]
    have hσ' : MDiffAt (T% (fun y ↦ e.symm y (g y))) x :=
      (e.mdifferentiableAt_section_iff I _ hx).2 (hg.congr_of_eventuallyEq hread)
    rw [hcov.congr_of_eventuallyEq hσ hσ' (e.open_baseSet.mem_nhds hx) heq, ← hv,
      covariantDerivative_symm_comp_apply_symm b hcov hx hg u]
  rw [hformula _ G' ((contMDiffAt_deriv_vectorField_of_contMDiffAt hW
    (by norm_num)).mdifferentiableAt one_ne_zero) hG' (eventually_deriv_eq_symm (by norm_num) hW)]
  -- Differentiate the coordinate formula for `∇_v W_s` in `s`.
  let L : E →L[ℝ] E := e.symmL ℝ x
  have hd : HasDerivAt (fun s ↦ L (mvfderiv I (G s) x v + christoffelMap b hcov x (G s x) u))
      (L (mvfderiv I G' x v + christoffelMap b hcov x (G' x) u)) t := by
    have h1 : HasDerivAt (fun s ↦ mvfderiv I (G s) x v) (mvfderiv I G' x v) t := by
      refine hasDerivAt_mvfderiv_apply ?_ v
      rwa [minSmoothness_of_isRCLikeNormedField]
    have h2 : HasDerivAt (fun s ↦ christoffelMap b hcov x (G s x) u)
        (christoffelMap b hcov x (G' x) u) t :=
      ((christoffelMap b hcov x).hasFDerivAt.comp_hasDerivAt t
        hcurve.hasDerivAt).clm_apply (hasDerivAt_const t u) |>.congr_deriv
        (by simp [G'])
    exact L.hasFDerivAt.comp_hasDerivAt t (h1.add h2)
  rw [← e.symmL_apply (R := ℝ) hx]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hslice] with s hs
  exact (hformula (W s) (G s) hs ((e.mdifferentiableAt_section_iff I _ hx).1 hs)
    (hsymm (W s))).trans (e.symmL_apply (R := ℝ) hx _).symm

end TauCeti.Manifold
