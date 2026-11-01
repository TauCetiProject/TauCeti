/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Schur
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Parallel curvature and local symmetry

In this file a connection `∇` on the tangent bundle *has parallel curvature* when its curvature
tensor is parallel, `∇R = 0`, where `∇R` is `CovariantDerivative.derivCurvatureTensor` taken with
`∇` itself. No condition on the torsion is imposed. The classical notion of an affine locally
symmetric connection is a torsion-free connection with parallel curvature (Kobayashi–Nomizu,
Vol. II, Chapter XI). For the Levi-Civita connection, `∇R = 0` is equivalent to the Riemannian
manifold being locally symmetric (Cartan's characterization); it is not the geodesic-symmetry
definition itself.

Flat connections have parallel curvature. For a metric-compatible connection whose curvature has the
pointwise constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)`, the covariant derivative
of the curvature is `(∇_v R)(u, w)s = dκ(v) (⟨w, s⟩ u - ⟨u, s⟩ w)`. In particular a
metric-compatible torsion-free connection of constant sectional curvature, such as the Levi-Civita
connection of a round sphere or of hyperbolic space, has parallel curvature, so it is locally
symmetric.

Conversely, when the curvature has the pointwise constant-curvature form above in dimension at
least two, it is parallel at a point exactly when `dκ` vanishes there. Every metric on a surface
has curvature of this form, with `κ` the Gaussian curvature `Scal / 2`. So a metric-compatible
torsion-free connection on a surface has parallel curvature exactly when its Gaussian curvature is
locally constant, and on a connected surface exactly when it has constant sectional curvature. In
dimension at least three Schur's theorem already makes `κ` locally constant, without assuming
parallel curvature.

## Main definitions and results

* `CovariantDerivative.HasParallelCurvature`: the curvature tensor of a connection on the tangent
  bundle is parallel.
* `CovariantDerivative.hasParallelCurvature_iff_curvatureOperator`: parallel curvature as the
  product rule `∇_X (R(Y, Z) W) = R(∇_X Y, Z) W + R(Y, ∇_X Z) W + R(Y, Z) (∇_X W)` on smooth
  fields.
* `CovariantDerivative.hasParallelCurvature_of_curvatureTensor_eq_zero`: flat connections have
  parallel curvature.
* `CovariantDerivative.IsMetricCompatible.derivCurvatureTensor_eq_mvfderiv_smul`: the covariant
  derivative at `x` of a curvature tensor of pointwise constant-curvature form near `x`.
* `CovariantDerivative.HasConstantSectionalCurvature.hasParallelCurvature`: constant sectional
  curvature implies parallel curvature.
* `CovariantDerivative.IsMetricCompatible.derivCurvatureTensor_eq_zero_iff_mfderiv_eq_zero`: a
  curvature tensor of pointwise constant-curvature form is parallel at `x` exactly when `dκ`
  vanishes at `x`.
* `CovariantDerivative.hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two`
  (**locally symmetric surfaces**): a surface has parallel curvature exactly when its Gaussian
  curvature is locally constant.
* `CovariantDerivative.HasParallelCurvature.hasConstantSectionalCurvature_of_finrank_eq_two` and
  `hasParallelCurvature_iff_exists_hasConstantSectionalCurvature_of_finrank_eq_two`, in the
  namespace `CovariantDerivative`: a connected surface has parallel curvature exactly when it has
  constant sectional curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (locally symmetric spaces, as manifolds with parallel curvature tensor).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience
  (1963), Chapter V, Section 2 (sectional curvature and spaces of constant curvature).
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Interscience
  (1969), Chapter XI (affine locally symmetric spaces, as torsion-free connections with parallel
  curvature tensor).
-/

public section

open Bundle FiberBundle
open scoped ContDiff InnerProductSpace Manifold Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

section Affine

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- A smooth connection on the tangent bundle **has parallel curvature** when the covariant
derivative `∇R` of its curvature tensor, taken with the connection itself, vanishes at every
point. The torsion is unrestricted; a torsion-free connection with parallel curvature is an affine
locally symmetric connection. For the Levi-Civita connection the condition is equivalent to local
symmetry of the Riemannian manifold. -/
def HasParallelCurvature : Prop :=
  ∀ x : M, cov.derivCurvatureTensor cov x = 0

/-- The pointwise characterization of parallel curvature. -/
theorem hasParallelCurvature_iff :
    cov.HasParallelCurvature ↔ ∀ x : M, cov.derivCurvatureTensor cov x = 0 :=
  Iff.rfl

/-- A connection on the tangent bundle has parallel curvature exactly when its curvature operator
satisfies the product rule
`∇_X (R(Y, Z) W) = R(∇_X Y, Z) W + R(Y, ∇_X Z) W + R(Y, Z) (∇_X W)` on smooth vector fields. -/
theorem hasParallelCurvature_iff_curvatureOperator :
    cov.HasParallelCurvature ↔
      ∀ ⦃X Y Z W : Π x : M, TangentSpace I x⦄, CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
        CMDiff ∞ (T% Z) → CMDiff ∞ (T% W) → ∀ x : M,
          cov (curvatureOperator cov Y Z W) x (X x) =
            curvatureOperator cov (fun y ↦ cov Y y (X y)) Z W x +
              curvatureOperator cov Y (fun y ↦ cov Z y (X y)) W x +
                curvatureOperator cov Y Z (fun y ↦ cov W y (X y)) x := by
  refine ⟨fun h X Y Z W hX hY hZ hW x ↦ ?_, fun h x ↦ ?_⟩
  · have hx := congr($(h x) (X x) (Y x) (Z x) (W x))
    rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW] at hx
    simp only [LinearMap.zero_apply] at hx
    rw [← sub_eq_zero, ← hx]
    abel
  · ext v u w s
    obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E v
    obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
    obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
    obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E s
    rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW,
      h hX hY hZ hW x]
    simp only [LinearMap.zero_apply, sub_sub, sub_self]

/-- A flat connection on the tangent bundle has parallel curvature. -/
theorem hasParallelCurvature_of_curvatureTensor_eq_zero (h : ∀ x : M, cov.curvatureTensor x = 0) :
    cov.HasParallelCurvature :=
  derivCurvatureTensor_eq_zero_of_curvatureTensor_eq_zero cov cov h

end Affine

section Riemannian

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

/-- Let the curvature tensor of a metric-compatible connection have the pointwise
constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)` near `x`. If `κ` is
differentiable at `x`, the covariant derivative of the curvature is
`(∇_v R)(u, w)s = dκ(v) (⟨w, s⟩ u - ⟨u, s⟩ w)`. -/
theorem IsMetricCompatible.derivCurvatureTensor_eq_mvfderiv_smul
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {κ : M → ℝ} {x : M} (hκ : ∀ᶠ y in 𝓝 x, ∀ (w u v : TangentSpace I y),
      cov.curvatureTensor y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u))
    (hκx : MDifferentiableAt I 𝓘(ℝ) κ x) (v u w s : TangentSpace I x) :
    cov.derivCurvatureTensor cov x v u w s = mvfderiv I κ x v • (⟪w, s⟫_ℝ • u - ⟪u, s⟫_ℝ • w) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E v
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E w
  obtain ⟨W, hW, rfl⟩ := exists_contMDiff_section_eq I E s
  rw [derivCurvatureTensor_apply_eq_curvatureOperator cov cov x hX hY hZ hW]
  exact hcov.covariantDerivative_curvatureOperator_eq_mvfderiv_smul hκ hX hY hZ hW hκx

/-- A metric-compatible torsion-free connection of constant sectional curvature, such as the
Levi-Civita connection of a space form, has parallel curvature. -/
theorem HasConstantSectionalCurvature.hasParallelCurvature
    {hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov}
    {κ : ℝ} (h : cov.HasConstantSectionalCurvature hcov κ) (ht : cov.torsion = 0) :
    cov.HasParallelCurvature := by
  intro x
  ext v u w s
  rw [hcov.derivCurvatureTensor_eq_mvfderiv_smul (κ := fun _ ↦ κ)
    (.of_forall fun y ↦ (h.hasSectionalCurvatureAt y).curvatureTensor_eq_smul_inner_sub ht)
    mdifferentiableAt_const]
  simp [mvfderiv_const]

/-- Let the curvature tensor of a metric-compatible connection have the pointwise
constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)` at every point `y` near `x`, in
dimension at least two. Then the curvature is parallel at `x` exactly when `dκ` vanishes at `x`. -/
theorem IsMetricCompatible.derivCurvatureTensor_eq_zero_iff_mfderiv_eq_zero
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (hdim : 2 ≤ Module.finrank ℝ E) {κ : M → ℝ} {x : M}
    (hκ : ∀ᶠ y in 𝓝 x, ∀ (w u v : TangentSpace I y),
      cov.curvatureTensor y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u)) :
    cov.derivCurvatureTensor cov x = 0 ↔ mfderiv I 𝓘(ℝ) κ x = 0 := by
  have hκx := cov.mdifferentiableAt_of_eventually_curvatureTensor_eq_smul_inner_sub hdim hκ
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- On an orthonormal pair `e₀, e₁`, the parallel curvature gives `dκ(v) e₀ = 0`.
    have hx : 2 ≤ Module.finrank ℝ (TangentSpace I x) := by
      rwa [TauCeti.finrank_tangentSpace]
    let b := stdOrthonormalBasis ℝ (TangentSpace I x)
    have hb := b.orthonormal
    let i : Fin (Module.finrank ℝ (TangentSpace I x)) := ⟨0, by omega⟩
    let j : Fin (Module.finrank ℝ (TangentSpace I x)) := ⟨1, by omega⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    have hL : mvfderiv I κ x = 0 := by
      ext v
      have hv := congr($h v (b i) (b j) (b j))
      rw [hcov.derivCurvatureTensor_eq_mvfderiv_smul hκ hκx, real_inner_self_eq_norm_sq,
        hb.1 j, hb.2 hij] at hv
      simp only [one_pow, one_smul, zero_smul, sub_zero, LinearMap.zero_apply] at hv
      exact (smul_eq_zero.1 hv).resolve_right (hb.ne_zero i)
    ext v
    simpa [mvfderiv] using congr($hL v)
  · ext v u w s
    rw [hcov.derivCurvatureTensor_eq_mvfderiv_smul hκ hκx]
    simp [mvfderiv, h]

section Surface

variable (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
  (ht : cov.torsion = 0) (hE : Module.finrank ℝ E = 2)
include hcov ht hE

/-- **Locally symmetric surfaces.** A metric-compatible torsion-free connection on the tangent
bundle of a surface has parallel curvature exactly when its scalar curvature, twice the Gaussian
curvature, is locally constant. -/
theorem hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two :
    cov.HasParallelCurvature ↔ IsLocallyConstant cov.scalarCurvature := by
  have hx (x : M) : Module.finrank ℝ (TangentSpace I x) = 2 := by
    rw [TauCeti.finrank_tangentSpace, hE]
  -- The Gaussian curvature `K = Scal / 2` puts the curvature in constant-curvature form.
  have hform (x : M) : ∀ᶠ y in 𝓝 x, ∀ (w u v : TangentSpace I y),
      cov.curvatureTensor y w u v =
        (cov.scalarCurvature y / 2) • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u) :=
    .of_forall fun y ↦ cov.curvatureTensor_eq_scalarCurvature_div_two_smul hcov ht (hx y)
  have hK : MDifferentiable I 𝓘(ℝ) fun y ↦ cov.scalarCurvature y / 2 :=
    (cov.contMDiff_scalarCurvature.div_const 2).mdifferentiable (by simp)
  have hiff : IsLocallyConstant cov.scalarCurvature ↔
      IsLocallyConstant fun y ↦ cov.scalarCurvature y / 2 :=
    ⟨fun h ↦ h.comp (· / 2), fun h ↦ by
      convert h.comp (· * 2)
      ext y
      simp⟩
  rw [hiff, hasParallelCurvature_iff]
  refine ⟨fun h ↦ MDifferentiable.isLocallyConstant_of_mfderiv_eq_zero hK fun x ↦
    (hcov.derivCurvatureTensor_eq_zero_iff_mfderiv_eq_zero hE.ge (hform x)).1 (h x),
    fun h x ↦ (hcov.derivCurvatureTensor_eq_zero_iff_mfderiv_eq_zero hE.ge (hform x)).2 ?_⟩
  rw [Filter.EventuallyEq.mfderiv_eq ((IsLocallyConstant.iff_eventually_eq _).1 h x)]
  exact mfderiv_const

/-- **Locally symmetric surfaces have constant curvature.** A metric-compatible torsion-free
connection with parallel curvature on the tangent bundle of a preconnected surface has constant
sectional curvature, namely the Gaussian curvature `Scal(x₀) / 2` at any point `x₀`. -/
theorem HasParallelCurvature.hasConstantSectionalCurvature_of_finrank_eq_two
    [PreconnectedSpace M] (h : cov.HasParallelCurvature) (x₀ : M) :
    cov.HasConstantSectionalCurvature hcov (cov.scalarCurvature x₀ / 2) := by
  have hc :=
    (hasParallelCurvature_iff_isLocallyConstant_scalarCurvature_of_finrank_eq_two hcov ht hE).1 h
  refine (cov.hasConstantSectionalCurvature_iff hcov _).2 fun x ↦ ?_
  rw [← hc.apply_eq_of_preconnectedSpace x x₀]
  exact cov.hasSectionalCurvatureAt_scalarCurvature_div_two hcov
    (by rw [TauCeti.finrank_tangentSpace, hE])

/-- On a preconnected surface, a metric-compatible torsion-free connection on the tangent bundle
has parallel curvature exactly when it has constant sectional curvature. -/
theorem hasParallelCurvature_iff_exists_hasConstantSectionalCurvature_of_finrank_eq_two
    [PreconnectedSpace M] :
    cov.HasParallelCurvature ↔ ∃ κ : ℝ, cov.HasConstantSectionalCurvature hcov κ := by
  refine ⟨fun h ↦ ?_, fun ⟨κ, hκ⟩ ↦ hκ.hasParallelCurvature ht⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, (cov.hasConstantSectionalCurvature_iff hcov 0).2 hM.elim⟩
  · exact ⟨_, h.hasConstantSectionalCurvature_of_finrank_eq_two hcov ht hE x₀⟩

end Surface

end Riemannian

end CovariantDerivative
