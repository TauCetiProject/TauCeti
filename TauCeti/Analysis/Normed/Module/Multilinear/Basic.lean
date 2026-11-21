/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Operator-norm bounds for continuous multilinear maps

A continuous multilinear map `D` on `E × F` in `j + l` variables, evaluated on `j` directions
`(u i, 0)` in `E` followed by `l` directions `(0, w i)` in `F`, is bounded by
`‖D‖ * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖)`. This is the form in which mixed derivatives in two groups
of variables are estimated by a full Fréchet derivative.

Postcomposition with a continuous linear map `g` is Lipschitz on continuous multilinear maps,
with constant `‖g‖`.

Inserting a fixed vector `v` as the last of `m + 1` arguments is a continuous linear map from
continuous multilinear maps in `m + 1` variables to those in `m` variables, of norm at most `‖v‖`.

## Main declarations

* `ContinuousMultilinearMap.norm_apply_append_prod_le`: the operator-norm bound on
  `Fin.append (fun i ↦ (u i, 0)) (fun i ↦ (0, w i))`.
* `ContinuousLinearMap.norm_compContinuousMultilinearMap_sub_le`: the Lipschitz bound for
  postcomposition with a continuous linear map.
* `ContinuousMultilinearMap.evalLastL`: inserting `v` as the last argument, with
  `ContinuousMultilinearMap.norm_evalLastL_le` bounding its norm by `‖v‖`.
-/

public section

namespace ContinuousMultilinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- The operator-norm bound for a multilinear map on `E × F` evaluated on `j` directions in `E`
followed by `l` directions in `F`. -/
theorem norm_apply_append_prod_le {j l : ℕ} (D : (E × F) [×(j + l)]→L[𝕜] G) (u : Fin j → E)
    (w : Fin l → F) :
    ‖D (Fin.append (fun i => (u i, 0)) (fun i => (0, w i)))‖ ≤
      ‖D‖ * ((∏ i, ‖u i‖) * ∏ i, ‖w i‖) := by
  refine (D.le_opNorm _).trans_eq ?_
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Prod.norm_mk, norm_zero,
    norm_nonneg, max_eq_left, max_eq_right]

variable (𝕜 F) in
/-- Inserting `v` as the last of `m + 1` arguments, as a continuous linear map
`(E [×(m+1)]→L[𝕜] F) →L[𝕜] (E [×m]→L[𝕜] F)`. -/
noncomputable def evalLastL (v : E) (m : ℕ) : (E [×(m + 1)]→L[𝕜] F) →L[𝕜] (E [×m]→L[𝕜] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜 (fun _ : Fin m ↦ E) (E →L[𝕜] F) F
    (ContinuousLinearMap.apply 𝕜 F v)).comp
    (continuousMultilinearCurryRightEquiv' 𝕜 m E F).toLinearIsometry.toContinuousLinearMap

/-- `evalLastL 𝕜 F v m g` evaluates `g` on `w` followed by `v`. -/
@[simp]
theorem evalLastL_apply (v : E) {m : ℕ} (g : E [×(m + 1)]→L[𝕜] F) (w : Fin m → E) :
    evalLastL 𝕜 F v m g w = g (Fin.snoc w v) := by
  rw [evalLastL, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry,
    ContinuousLinearMap.compContinuousMultilinearMapL_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, continuousMultilinearCurryRightEquiv_apply']

/-- Inserting `v` last commutes with separating the first argument. -/
theorem evalLastL_comp_curryLeft (v : E) {m : ℕ} (g : E [×(m + 2)]→L[𝕜] F) :
    (evalLastL 𝕜 F v m).comp g.curryLeft = (evalLastL 𝕜 F v (m + 1) g).curryLeft := by
  ext u w
  simp only [ContinuousLinearMap.comp_apply, evalLastL_apply, curryLeft_apply,
    Fin.cons_snoc_eq_snoc_cons]

/-- Inserting `v` as the last argument has operator norm at most `‖v‖`. -/
theorem norm_evalLastL_le (v : E) (m : ℕ) : ‖evalLastL 𝕜 F v m‖ ≤ ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun g ↦ ?_
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  refine mul_le_mul ?_ (LinearIsometryEquiv.norm_map _ g).le (norm_nonneg _) (norm_nonneg v)
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun φ ↦ ?_
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact φ.le_opNorm v

end ContinuousMultilinearMap

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {E : ι → Type*} {G G' : Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] [SeminormedAddCommGroup G]
  [NormedSpace 𝕜 G] [SeminormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- Postcomposition with a fixed continuous linear map is Lipschitz on continuous multilinear
maps, with constant its operator norm. -/
theorem norm_compContinuousMultilinearMap_sub_le (g : G →L[𝕜] G')
    (f f' : ContinuousMultilinearMap 𝕜 E G) :
    ‖g.compContinuousMultilinearMap f - g.compContinuousMultilinearMap f'‖ ≤ ‖g‖ * ‖f - f'‖ := by
  have : g.compContinuousMultilinearMap f - g.compContinuousMultilinearMap f' =
      g.compContinuousMultilinearMap (f - f') := by
    ext
    simp
  rw [this]
  exact g.norm_compContinuousMultilinearMap_le _

end ContinuousLinearMap
