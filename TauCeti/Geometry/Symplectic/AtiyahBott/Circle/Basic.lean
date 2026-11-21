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
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.Riemannian.Codifferential

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

omit [BoundarylessManifold I M] [T2Space M] in
/-- Integration of smooth `2`-forms over the closed surface is additive. -/
private theorem integralTopForm_add_two (φ ψ : SmoothForm I M ℝ 2) :
    integralTopForm o (φ + ψ).val = integralTopForm o φ.val + integralTopForm o ψ.val :=
  integralTopForm_add_of_compactSpace o (φ.isSmoothForm.of_le (by simp))
    (ψ.isSmoothForm.of_le (by simp))

/-- The **Atiyah–Bott symplectic form** `Ω(a, b) = ∫_M a ∧ b` on the tangent space `Ω¹(M; u(1))`
of the space of connections of the trivial circle bundle over the closed oriented surface `M`,
with `u(1) = iℝ` identified with `ℝ` by its invariant inner product. It does not depend on the
base connection. -/
def atiyahBottForm : LinearMap.BilinForm ℝ (SmoothForm I M ℝ 1) :=
  LinearMap.mk₂ ℝ (fun a b ↦ integralTopForm o (SmoothForm.wedge a b).val)
    (fun a a' b ↦ by rw [map_add, LinearMap.add_apply, integralTopForm_add_two])
    (fun c a b ↦ by
      rw [map_smul, LinearMap.smul_apply, Submodule.coe_smul, integralTopForm_smul, smul_eq_mul])
    (fun a b b' ↦ by rw [map_add, integralTopForm_add_two])
    fun c a b ↦ by rw [map_smul, Submodule.coe_smul, integralTopForm_smul, smul_eq_mul]

omit [BoundarylessManifold I M] [T2Space M] in
@[simp]
theorem atiyahBottForm_apply (a b : SmoothForm I M ℝ 1) :
    atiyahBottForm o a b = integralTopForm o (RoughForm.wedge a.val b.val) := by
  rw [atiyahBottForm, LinearMap.mk₂_apply, SmoothForm.coe_wedge]

omit [BoundarylessManifold I M] [T2Space M] in
/-- The Atiyah–Bott form is antisymmetric. -/
theorem atiyahBottForm_swap (a b : SmoothForm I M ℝ 1) :
    atiyahBottForm o b a = -atiyahBottForm o a b := by
  have h : (SmoothForm.wedge b a).val = -(SmoothForm.wedge a b).val :=
    funext fun x ↦ ContinuousAlternatingMap.ext fun v ↦ by
      rw [SmoothForm.wedge_comm, Fin.cast_refl, Function.comp_id]
      simp
  rw [atiyahBottForm, LinearMap.mk₂_apply, LinearMap.mk₂_apply, h, ← neg_one_smul ℝ,
    integralTopForm_smul, neg_one_mul]

omit [BoundarylessManifold I M] [T2Space M] in
/-- The Atiyah–Bott form is alternating. -/
theorem atiyahBottForm_isAlt : (atiyahBottForm o).IsAlt := fun a ↦ by
  have h := atiyahBottForm_swap o a a
  linarith

omit [BoundarylessManifold I M] in
/-- **The Atiyah–Bott form is weakly nondegenerate**: if `Ω(a, b) = 0` for every `b`, then
`a = 0`, and likewise in the second argument. Indeed `Ω(a, ⋆a) = ∫_M |a|² vol` for the Hodge
star of any Riemannian metric on `M`. -/
theorem atiyahBottForm_nondegenerate : (atiyahBottForm o).Nondegenerate := by
  have hleft : LinearMap.SeparatingLeft (atiyahBottForm o) := fun a ha ↦ by
    by_contra hne
    obtain ⟨b, hb⟩ := SmoothForm.exists_integralTopForm_wedge_ne_zero o
      (show 1 + 1 = 2 from rfl)
      ((mem_compactlySupportedForms I).mpr (isClosed_tsupport _).isCompact) hne
    refine hb ?_
    rw [← ha b, atiyahBottForm_apply, SmoothForm.cast_self, SmoothForm.coe_wedge]
  refine ⟨hleft, fun b hb ↦ hleft b fun a ↦ ?_⟩
  rw [atiyahBottForm_swap, hb, neg_zero]

/-! ### The moment map -/

/-- The **curvature moment map** of the gauge action: the pairing
`⟨μ(a), ξ⟩ = ∫_M B(i da, i ξ) = ∫_M ξ da` of the curvature `i da` of the connection `d + i a` with
an element `ξ` of the Lie algebra `C^∞(M, ℝ)` of the gauge group. It is linear in `a` because the
trivial connection `d` is taken as the origin of the space of connections. -/
def atiyahBottMoment : SmoothForm I M ℝ 1 →ₗ[ℝ] C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun a ξ ↦ integralTopForm o (SmoothForm.funSMulₗ ξ (mextDerivₗ I 1 a)).val)
    (fun a a' ξ ↦ by rw [map_add, map_add, integralTopForm_add_two])
    (fun c a ξ ↦ by
      rw [map_smul, map_smul, Submodule.coe_smul, integralTopForm_smul, smul_eq_mul])
    (fun a ξ η ↦ by
      rw [← integralTopForm_add_two]
      congr 1
      funext x
      simp [add_smul])
    fun c a ξ ↦ by
      rw [smul_eq_mul, ← integralTopForm_smul]
      congr 1
      funext x
      simp [mul_smul]

omit [BoundarylessManifold I M] [T2Space M] in
@[simp]
theorem atiyahBottMoment_apply (a : SmoothForm I M ℝ 1) (ξ : C^∞⟮I, M; ℝ⟯) :
    atiyahBottMoment o a ξ =
      integralTopForm o (fun x ↦ ξ x • mextDeriv a.val x : RoughForm I M ℝ 2) := by
  rw [atiyahBottMoment, LinearMap.mk₂_apply, SmoothForm.coe_funSMulₗ, mextDerivₗ_apply]

/-- **Integration by parts on the closed surface**: `∫_M ξ db = -∫_M dξ ∧ b`, that is
`⟨μ(b), ξ⟩ = Ω(ξ_a, b)` for the infinitesimal generator `ξ_a = -dξ`. -/
theorem atiyahBottForm_circleGaugeGenerator (ξ : C^∞⟮I, M; ℝ⟯) (b : SmoothForm I M ℝ 1) :
    atiyahBottForm o ξ.circleGaugeGenerator b = atiyahBottMoment o b ξ := by
  -- Stokes' theorem for the compactly supported `1`-form `ξ b`, with the Leibniz rule
  -- `d (ξ b) = dξ ∧ b + ξ db`.
  have hS := integralTopForm_mextDeriv_eq_zero (n := 1) o
    ((SmoothForm.funSMulₗ ξ b).isSmoothForm.of_le (by simp)) (isClosed_tsupport _).isCompact
  rw [← mextDerivₗ_apply, SmoothForm.mextDerivₗ_funSMulₗ, Submodule.coe_add,
    integralTopForm_add_of_compactSpace o ((SmoothForm.isSmoothForm _).of_le (by simp))
      ((SmoothForm.isSmoothForm _).of_le (by simp))] at hS
  -- the degree transport `0 + 1 + 1 = 1 + 1` of `dξ ∧ b` does not change the form
  rw [SmoothForm.cast_self] at hS
  rw [ξ.circleGaugeGenerator_def, map_neg, LinearMap.neg_apply, atiyahBottForm, atiyahBottMoment,
    LinearMap.mk₂_apply, LinearMap.mk₂_apply]
  linarith

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
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    -- Pair the curvature `F = da` with a function `s` such that `∫_M F ∧ s ≠ 0`, for instance
    -- `s = ⋆F` for a Riemannian metric: then `⟨μ(a), s⟩ = ∫_M F ∧ s ≠ 0`.
    set F := mextDerivₗ I 1 a
    obtain ⟨s, hFs⟩ := SmoothForm.exists_integralTopForm_wedge_ne_zero o
      (show 2 + 0 = 2 from rfl)
      ((mem_compactlySupportedForms I).mpr (isClosed_tsupport _).isCompact) hne
    have hs : ContMDiff I 𝓘(ℝ, ℝ) ∞ fun x ↦ s.val x 0 := by
      rw [← isSmoothForm_ofFunction_iff, ← RoughForm.eq_ofFunction]
      exact s.isSmoothForm
    refine hFs ?_
    have hξ := (atiyahBottMoment_apply o a ⟨fun x ↦ s.val x 0, hs⟩).symm.trans
      ((LinearMap.congr_fun h _).trans (LinearMap.zero_apply _))
    rw [← hξ]
    congr 1
    funext x
    ext v
    rw [SmoothForm.cast_self, SmoothForm.coe_wedge]
    conv_lhs => rw [RoughForm.eq_ofFunction s.val, RoughForm.wedge_ofFunction]
    simp [F, mextDerivₗ_apply]
  · ext ξ
    rw [atiyahBottMoment_apply, ← mextDerivₗ_apply, h, LinearMap.zero_apply]
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, smul_zero]
    exact integralTopForm_zero o

end TauCeti
