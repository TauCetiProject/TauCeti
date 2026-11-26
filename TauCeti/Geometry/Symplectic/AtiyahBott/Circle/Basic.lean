/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.LogDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic
public import TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle

/-!
# The Atiyah–Bott symplectic structure of the trivial circle bundle over a surface

Let `M` be a closed oriented surface, that is a compact boundaryless smooth manifold of
dimension two with an orientation `o`, and let `P = M × U(1)` be the trivial circle bundle. The
covariant derivative `d + i a` identifies the connections on `P` with the real `1`-forms `a` on
`M`, and their tangent space `Ω¹(M; u(1))` with the real `1`-forms as well, the Lie algebra
`u(1) = iℝ` carrying the invariant inner product `B(i x, i y) = x y`. This file develops the
Atiyah–Bott description of the gauge action on this affine space as a Hamiltonian action.

* **The gauge action.** A gauge transformation, a smooth map `u : M → U(1)`, acts on connections
  by `u · A = u A u⁻¹ - du u⁻¹`, that is by the translation
  `a ↦ a - circleLogDeriv u` by the real logarithmic derivative `-i u⁻¹ du`
  (`TauCeti.circleGaugeAction`). It is a group homomorphism into the affine automorphisms whose
  linear parts are all the identity. On a connected surface, the stabilizer of every connection is
  the group of constant maps (`TauCeti.circleGaugeAction_apply_eq_self_iff`), the ineffective
  constant `U(1)`.
* **The infinitesimal action.** The Lie algebra of the gauge group is `C^∞(M, ℝ)`, a function `ξ`
  generating the one-parameter group `t ↦ exp (i t ξ)`, and
  `exp (i t ξ) · a = a - t dξ` (`TauCeti.circleGaugeAction_circleExp_smul`). So the gauge
  action moves `a` along straight lines, with infinitesimal generator `ξ_a = -dξ`, which is
  `-d_A ξ` for this abelian group.
* **The symplectic form.** `Ω(a, b) = ∫_M a ∧ b` (`TauCeti.atiyahBottForm`) is an alternating
  bilinear form on the tangent space, independent of the base point, so the gauge
  transformations preserve it. It is weakly nondegenerate
  (`TauCeti.atiyahBottForm_nondegenerate`): if `Ω(a, b) = 0` for all `b` then `a = 0`, since
  `Ω(a, ⋆a) = ∫_M |a|² vol` for the Hodge star of any Riemannian metric.
* **The moment map.** The curvature of `d + i a` is `i da`, and
  `⟨μ(a), ξ⟩ = ∫_M B(i da, i ξ) = ∫_M ξ da` (`TauCeti.atiyahBottMoment`). By Stokes' theorem on
  the closed surface, `∫_M ξ db = -∫_M dξ ∧ b`, which is the moment map equation
  `ι_(ξ_a) Ω = dμ_ξ` in directional form: `μ_ξ(a + t b) = μ_ξ(a) + t Ω(ξ_a, b)`
  (`TauCeti.atiyahBottMoment_add_smul_apply`). The moment map is gauge invariant
  (`TauCeti.atiyahBottMoment_circleGaugeAction`), which is equivariance for the trivial coadjoint
  action of an abelian group, and its zero level is the set of flat connections, `da = 0`
  (`TauCeti.atiyahBottMoment_eq_zero_iff`).

The form and the moment map are the case `𝔨 = ℝ`, with the zero bracket and the product as
invariant form, of the Atiyah–Bott form and the curvature moment map of
`TauCeti.Geometry.Symplectic.AtiyahBott.TrivialBundle`
(`TauCeti.atiyahBottMoment_eq_atiyahBottMomentWith`), and the integration by parts and the flat
level are derived from the general results there.

The form `Ω` is the same at every connection, so all its directional derivatives along the
affine space of connections vanish and it is closed. Directional formulas along the lines
`a + t b` replace derivatives on this Fréchet space throughout.

## References

* M. F. Atiyah and R. Bott, *The Yang–Mills equations over Riemann surfaces*, Philos. Trans.
  Roy. Soc. London Ser. A 308 (1983), 523–615 (the symplectic form on the space of connections
  and the curvature as its moment map).
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-! ### The gauge action -/

/-- The **gauge action** of the smooth circle-valued maps `u : M → U(1)` on the connections
`d + i a` of the trivial circle bundle, written in terms of the real `1`-forms `a`: the gauge
transformation `u · A = u A u⁻¹ - du u⁻¹` is the translation `a ↦ a - circleLogDeriv u` by the
real logarithmic derivative of `u`. -/
def circleGaugeAction :
    C^∞⟮I, M; 𝓡 1, Circle⟯ →* (SmoothForm I M ℝ 1 ≃ᵃ[ℝ] SmoothForm I M ℝ 1) where
  toFun u := AffineEquiv.constVAdd ℝ (SmoothForm I M ℝ 1) (-u.circleLogDeriv)
  map_one' := by
    rw [ContMDiffMap.circleLogDeriv_one, neg_zero, AffineEquiv.constVAdd_zero,
      AffineEquiv.one_def]
  map_mul' u v := by
    rw [ContMDiffMap.circleLogDeriv_mul, neg_add, AffineEquiv.constVAdd_add, AffineEquiv.mul_def]

@[simp]
theorem circleGaugeAction_apply (u : C^∞⟮I, M; 𝓡 1, Circle⟯) (a : SmoothForm I M ℝ 1) :
    circleGaugeAction u a = a - u.circleLogDeriv := by
  simp [circleGaugeAction, neg_add_eq_sub]

/-- The gauge transformations are translations: their linear parts are the identity. -/
@[simp]
theorem linear_circleGaugeAction (u : C^∞⟮I, M; 𝓡 1, Circle⟯) :
    (circleGaugeAction u).linear = LinearEquiv.refl ℝ (SmoothForm I M ℝ 1) :=
  (rfl)

/-- The infinitesimal generator `ξ_a = -dξ` of the gauge action for the function `ξ` in the Lie
algebra `C^∞(M, ℝ)` of the gauge group. It does not depend on the connection `a`. -/
def _root_.ContMDiffMap.circleGaugeGenerator (ξ : C^∞⟮I, M; ℝ⟯) : SmoothForm I M ℝ 1 :=
  -mextDerivₗ I 0 (SmoothForm.ofFunction ξ)

theorem _root_.ContMDiffMap.circleGaugeGenerator_def (ξ : C^∞⟮I, M; ℝ⟯) :
    ξ.circleGaugeGenerator = -mextDerivₗ I 0 (SmoothForm.ofFunction ξ) :=
  (rfl)

/-- The infinitesimal generator `ξ_a = -dξ` evaluated at a tangent vector. -/
@[simp]
theorem _root_.ContMDiffMap.circleGaugeGenerator_apply (ξ : C^∞⟮I, M; ℝ⟯) (x : M)
    (v : Fin 1 → TangentSpace I x) :
    ξ.circleGaugeGenerator.val x v = -mvfderiv I ξ x (v 0) := by
  simp [ξ.circleGaugeGenerator_def, mextDerivₗ_apply, mextDeriv_ofFunction]

/-- **The exponential formula for the gauge action.** The one-parameter group
`t ↦ exp (i t ξ)` moves every connection along the straight line `a + t ξ_a`, so its velocity at
`t = 0` is the infinitesimal generator `ξ_a = -dξ`. -/
theorem circleGaugeAction_circleExp_smul (ξ : C^∞⟮I, M; ℝ⟯) (t : ℝ) (a : SmoothForm I M ℝ 1) :
    circleGaugeAction (t • ξ).circleExp a = a + t • ξ.circleGaugeGenerator := by
  have hξ : SmoothForm.ofFunction (t • ξ) = t • SmoothForm.ofFunction (I := I) ξ :=
    Subtype.ext (funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
      simp [RoughForm.ofFunction_apply])
  rw [circleGaugeAction_apply, ContMDiffMap.circleLogDeriv_circleExp, hξ, map_smul,
    ξ.circleGaugeGenerator_def, smul_neg, sub_eq_add_neg]

/-- **The stabilizer of a connection is the constant gauge group.** On a connected manifold a gauge
transformation fixes a connection exactly when it is a constant map to `U(1)`. In particular the
gauge group acts with the ineffective kernel `U(1)` of constants. -/
theorem circleGaugeAction_apply_eq_self_iff [PreconnectedSpace M] {u : C^∞⟮I, M; 𝓡 1, Circle⟯}
    {a : SmoothForm I M ℝ 1} :
    circleGaugeAction u a = a ↔ ∃ z : Circle, ∀ x, u x = z := by
  rw [circleGaugeAction_apply, sub_eq_self, ContMDiffMap.circleLogDeriv_eq_zero_iff]

/-! ### The Atiyah–Bott form -/

variable [FiniteDimensional ℝ E] [CompactSpace M] [BoundarylessManifold I M] [T2Space M]
  (o : Manifold.Orientation I M (Fin 2))

/-- The **Atiyah–Bott symplectic form** `Ω(a, b) = ∫_M a ∧ b` on the tangent space `Ω¹(M; u(1))`
of the space of connections of the trivial circle bundle over the closed oriented surface `M`,
with `u(1) = iℝ` identified with `ℝ` by its invariant inner product. It does not depend on the
base connection. It is the Atiyah–Bott form `TauCeti.atiyahBottFormWith` of `𝔨 = ℝ` with the
product as its bilinear form. -/
def atiyahBottForm : LinearMap.BilinForm ℝ (SmoothForm I M ℝ 1) :=
  atiyahBottFormWith (ContinuousLinearMap.mul ℝ ℝ) o

omit [BoundarylessManifold I M] [T2Space M] in
@[simp]
theorem atiyahBottForm_apply (a b : SmoothForm I M ℝ 1) :
    atiyahBottForm o a b = integralTopForm o (RoughForm.wedge a.val b.val) := by
  rw [atiyahBottForm, atiyahBottFormWith_apply, RoughForm.wedge_def]

omit [BoundarylessManifold I M] [T2Space M] in
/-- The Atiyah–Bott form is antisymmetric. -/
theorem atiyahBottForm_swap (a b : SmoothForm I M ℝ 1) :
    atiyahBottForm o b a = -atiyahBottForm o a b :=
  atiyahBottFormWith_swap _ o mul_comm a b

omit [BoundarylessManifold I M] [T2Space M] in
/-- The Atiyah–Bott form is alternating. -/
theorem atiyahBottForm_isAlt : (atiyahBottForm o).IsAlt :=
  atiyahBottFormWith_isAlt _ o mul_comm

omit [BoundarylessManifold I M] in
/-- **The Atiyah–Bott form is weakly nondegenerate**: if `Ω(a, b) = 0` for every `b`, then
`a = 0`, and likewise in the second argument. Indeed `Ω(a, ⋆a) = ∫_M |a|² vol` for the Hodge
star of any Riemannian metric on `M`. -/
theorem atiyahBottForm_nondegenerate : (atiyahBottForm o).Nondegenerate :=
  atiyahBottFormWith_nondegenerate _ o mul_comm fun u h ↦ by simpa using h 1

/-! ### The moment map -/

/-- The **curvature moment map** of the gauge action: the pairing
`⟨μ(a), ξ⟩ = ∫_M B(i da, i ξ) = ∫_M ξ da` of the curvature `i da` of the connection `d + i a` with
an element `ξ` of the Lie algebra `C^∞(M, ℝ)` of the gauge group. It is linear in `a` because the
trivial connection `d` is taken as the origin of the space of connections. -/
def atiyahBottMoment : SmoothForm I M ℝ 1 →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun a ξ ↦ SmoothForm.integralTopFormₗ o (SmoothForm.funSMulₗ ξ (mextDerivₗ I 1 a)))
    (fun a a' ξ ↦ by rw [map_add, map_add, map_add])
    (fun c a ξ ↦ by rw [map_smul, map_smul, map_smul, smul_eq_mul])
    (fun a ξ η ↦ by
      rw [← map_add]
      refine congrArg _ (Subtype.ext (funext fun x ↦ ?_))
      simp [add_smul])
    fun c a ξ ↦ by
      rw [smul_eq_mul, ← smul_eq_mul, ← map_smul]
      refine congrArg _ (Subtype.ext (funext fun x ↦ ?_))
      simp [mul_smul]

omit [BoundarylessManifold I M] [T2Space M] in
@[simp]
theorem atiyahBottMoment_apply (a : SmoothForm I M ℝ 1) (ξ : C^∞⟮I, M; ℝ⟯) :
    atiyahBottMoment o a ξ =
      integralTopForm o (fun x ↦ ξ x • mextDeriv a.val x : RoughForm I M ℝ 2) := by
  rw [atiyahBottMoment, LinearMap.mk₂_apply, SmoothForm.integralTopFormₗ_apply,
    SmoothForm.coe_funSMulₗ, mextDerivₗ_apply]

omit [BoundarylessManifold I M] [T2Space M] in
/-- The moment map is the curvature moment map `TauCeti.atiyahBottMomentWith` of `𝔨 = ℝ` with the
zero bracket and the product as its bilinear form, evaluated on the `0`-form of `ξ`. -/
theorem atiyahBottMoment_eq_atiyahBottMomentWith (a : SmoothForm I M ℝ 1) (ξ : C^∞⟮I, M; ℝ⟯) :
    atiyahBottMoment o a ξ =
      atiyahBottMomentWith 0 (ContinuousLinearMap.mul ℝ ℝ) o a (SmoothForm.ofFunction ξ) := by
  rw [atiyahBottMoment_apply, atiyahBottMomentWith_apply, gaugeCurvature_zero_bracket,
    mextDerivₗ_apply]
  congr 1
  funext x
  ext v
  simp [RoughForm.ofFunction_apply, mul_comm]

/-- **Integration by parts on the closed surface**: `∫_M ξ db = -∫_M dξ ∧ b`, that is
`⟨μ(b), ξ⟩ = Ω(ξ_a, b)` for the infinitesimal generator `ξ_a = -dξ`. -/
theorem atiyahBottForm_circleGaugeGenerator (ξ : C^∞⟮I, M; ℝ⟯) (b : SmoothForm I M ℝ 1) :
    atiyahBottForm o ξ.circleGaugeGenerator b = atiyahBottMoment o b ξ := by
  -- the `β = 0` case of `atiyahBottFormWith_neg_gaugeCovariantDeriv`, at the connection `0`
  have h := atiyahBottFormWith_neg_gaugeCovariantDeriv 0 (ContinuousLinearMap.mul ℝ ℝ) o mul_comm
    (by simp) (by simp) 0 b (SmoothForm.ofFunction ξ)
  rw [gaugeCovariantDeriv_zero_bracket, gaugeCovariantExtDeriv_zero_bracket,
    SmoothForm.integralTopFormₗ_apply, SmoothForm.coe_wedgeWith] at h
  rw [atiyahBottMoment_eq_atiyahBottMomentWith, atiyahBottForm, ξ.circleGaugeGenerator_def, h,
    atiyahBottMomentWith_apply, gaugeCurvature_zero_bracket]

/-- **The moment map equation** `ι_(ξ_a) Ω = dμ_ξ`, in directional form: along the line
`a + t b` through any connection `a`, the moment map changes by `t Ω(ξ_a, b)`. -/
theorem atiyahBottMoment_add_smul_apply (a b : SmoothForm I M ℝ 1) (t : ℝ) (ξ : C^∞⟮I, M; ℝ⟯) :
    atiyahBottMoment o (a + t • b) ξ =
      atiyahBottMoment o a ξ + t * atiyahBottForm o ξ.circleGaugeGenerator b := by
  rw [atiyahBottForm_circleGaugeGenerator, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]

omit [BoundarylessManifold I M] [T2Space M] in
/-- **Gauge invariance of the moment map.** Since the gauge group is abelian, its coadjoint action
is trivial, and equivariance says that the gauge transformations preserve the moment map: the
curvature `d (a - circleLogDeriv u) = da` does not change. -/
theorem atiyahBottMoment_circleGaugeAction (u : C^∞⟮I, M; 𝓡 1, Circle⟯)
    (a : SmoothForm I M ℝ 1) :
    atiyahBottMoment o (circleGaugeAction u a) = atiyahBottMoment o a := by
  rw [circleGaugeAction_apply, map_sub, sub_eq_self]
  ext ξ
  rw [atiyahBottMoment_apply, u.mextDeriv_circleLogDeriv, LinearMap.zero_apply]
  simp only [Pi.zero_apply, smul_zero]
  exact integralTopForm_zero o

omit [BoundarylessManifold I M] in
/-- **The zero level of the moment map is the flat connections**: `μ(a) = 0` exactly when the
curvature `da` vanishes. -/
theorem atiyahBottMoment_eq_zero_iff {a : SmoothForm I M ℝ 1} :
    atiyahBottMoment o a = 0 ↔ mextDerivₗ I 1 a = 0 := by
  -- the `β = 0` case of `atiyahBottMomentWith_eq_zero_iff`; every `0`-form is a function
  rw [← gaugeCurvature_zero_bracket,
    ← atiyahBottMomentWith_eq_zero_iff 0 (ContinuousLinearMap.mul ℝ ℝ) o
      fun u h ↦ by simpa using h 1]
  refine ⟨fun h ↦ LinearMap.ext fun η ↦ ?_, fun h ↦ LinearMap.ext fun ξ ↦ ?_⟩
  · rw [η.eq_ofFunction, ← atiyahBottMoment_eq_atiyahBottMomentWith, h, LinearMap.zero_apply,
      LinearMap.zero_apply]
  · rw [atiyahBottMoment_eq_atiyahBottMomentWith, h, LinearMap.zero_apply, LinearMap.zero_apply]

end TauCeti
