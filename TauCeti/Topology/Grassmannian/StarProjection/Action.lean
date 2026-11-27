/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ContinuousFunctionalCalculus
public import TauCeti.Topology.Grassmannian.StarProjection.Basic

/-!
# The unitary action on the projection-form Grassmannian

The unitary group `unitary (E →L[𝕜] E)` of an inner product space `E` over `𝕜 = ℝ` or `ℂ` acts
on the Grassmannian `G(E, k) = Euclidean.grassmannian 𝕜 E k` in its projection form by
conjugation, `u • P = u P u*`, and the action is jointly continuous
(`Euclidean.grassmannian.instMulActionUnitary`,
`Euclidean.grassmannian.instContinuousSMulUnitary`). For `𝕜 = ℝ` this is the action of the
orthogonal group of `E`, which moves varifolds, measures on `E × G(E, k)`, by acting on both
factors.

The point `u • P` is `(Unitary.linearIsometryEquiv u).grassmannianCongr k P`
(`Euclidean.grassmannian.smul_eq_grassmannianCongr`), the image of `P` under the homeomorphism
`LinearIsometryEquiv.grassmannianCongr` induced by the linear isometry equivalence of `u`; its
plane is `u (range P)` (`Euclidean.grassmannian.range_coe_smul`). The conjugation itself is
Mathlib's `Unitary.conjStarAlgAut`: Mathlib's `Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv`
identifies it with conjugation by the linear isometry equivalence `Unitary.linearIsometryEquiv u`,
which is how `Euclidean.grassmannian.coe_smul` reads `u • P` as `u P u*`.

The `k`-planes of `E` as orthogonal projections follow L. Simon, *Lectures on Geometric Measure
Theory*, §38.
-/

public section

namespace Euclidean

namespace grassmannian

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {k : ℕ}

/-- A unitary `u` of `E →L[𝕜] E` moves a point `P` of `G(E, k)` to its conjugate `u P u*`, the
image of `P` under the homeomorphism `LinearIsometryEquiv.grassmannianCongr` of the linear
isometry equivalence of `u`. -/
noncomputable instance instSMulUnitary : SMul (unitary (E →L[𝕜] E)) (grassmannian 𝕜 E k) where
  smul u P := (Unitary.linearIsometryEquiv u).grassmannianCongr k P

/-- The action of a unitary `u` on `G(E, k)` is the homeomorphism
`LinearIsometryEquiv.grassmannianCongr` of the linear isometry equivalence of `u`. -/
theorem smul_eq_grassmannianCongr (u : unitary (E →L[𝕜] E)) (P : grassmannian 𝕜 E k) :
    u • P = (Unitary.linearIsometryEquiv u).grassmannianCongr k P :=
  (rfl)

/-- The action of a unitary `u` on `G(E, k)` is conjugation, `u • P = u P u*`. -/
@[simp]
theorem coe_smul (u : unitary (E →L[𝕜] E)) (P : grassmannian 𝕜 E k) :
    ((u • P : grassmannian 𝕜 E k) : E →L[𝕜] E) =
      (u : E →L[𝕜] E) * P * star (u : E →L[𝕜] E) := by
  simp only [smul_eq_grassmannianCongr, LinearIsometryEquiv.coe_grassmannianCongr_apply,
    Unitary.conjStarAlgEquiv_unitaryLinearIsometryEquiv, Unitary.conjStarAlgAut_apply]

/-- The unitary group of `E →L[𝕜] E` acts on `G(E, k)` by conjugation, `u • P = u P u*`. For
`𝕜 = ℝ` this is the action of the orthogonal group of `E`. -/
noncomputable instance instMulActionUnitary :
    MulAction (unitary (E →L[𝕜] E)) (grassmannian 𝕜 E k) where
  one_smul P := by
    simp only [smul_eq_grassmannianCongr, map_one, LinearIsometryEquiv.one_def,
      LinearIsometryEquiv.grassmannianCongr_refl, Homeomorph.refl_apply, id_eq]
  mul_smul u v P := by
    simp only [smul_eq_grassmannianCongr, map_mul, LinearIsometryEquiv.mul_def,
      LinearIsometryEquiv.grassmannianCongr_trans, Homeomorph.trans_apply]

/-- The plane of `u • P` is the image of the plane of `P` under `u`. It is a `simp↓` lemma so that
it fires before `coe_smul` expands `u • P` into an operator product. -/
@[simp↓]
theorem range_coe_smul (u : unitary (E →L[𝕜] E)) (P : grassmannian 𝕜 E k) :
    ((u • P : grassmannian 𝕜 E k) : E →L[𝕜] E).range =
      (P : E →L[𝕜] E).range.map (u : E →L[𝕜] E).toLinearMap :=
  (Unitary.linearIsometryEquiv u).range_coe_grassmannianCongr_apply P

/-- The unitary group of `E` acts continuously on `G(E, k)`: the conjugation
`(u, P) ↦ u P u*` is jointly continuous. -/
instance instContinuousSMulUnitary :
    ContinuousSMul (unitary (E →L[𝕜] E)) (grassmannian 𝕜 E k) where
  continuous_smul := by
    refine continuous_induced_rng.2 ?_
    simp only [Function.comp_def, coe_smul]
    fun_prop

end grassmannian

end Euclidean
