/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Polarization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondBianchi
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Schur's theorem

Let `∇` be a smooth metric-compatible torsion-free connection on the tangent bundle of a
Riemannian manifold `M` of dimension `n ≥ 3`, such as its Levi-Civita connection. Suppose that
at every point `x` all tangent two-planes have the same sectional curvature `κ x`, so that the
curvature tensor is `R(w, u)v = κ(x) (⟨u, v⟩ w - ⟨w, v⟩ u)`. Schur's theorem states that the
function `κ` is then locally constant, hence constant when `M` is connected.

The tensor `(Y, Z, σ) ↦ ⟨Z, σ⟩ Y - ⟨Y, σ⟩ Z` is parallel for a metric connection, so the
covariant derivative of the curvature is `(∇_X R)(Y, Z)σ = dκ(X) (⟨Z, σ⟩ Y - ⟨Y, σ⟩ Z)`.
Inserting this into the second Bianchi identity and evaluating on three orthonormal vectors
kills `dκ`; this is where `n ≥ 3` is used. In dimension two every tangent space has a single
two-plane, so the curvature is pointwise isotropic for every metric, and the conclusion fails for
any surface whose Gaussian curvature is not constant.

## Main results

* `CovariantDerivative.IsMetricCompatible.covariantDerivative_curvatureOperator_eq_mvfderiv_smul`:
  the covariant derivative of a curvature tensor of pointwise constant-curvature form.
* `CovariantDerivative.mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub`: the local form of
  Schur's theorem, `dκ = 0` in dimension at least three.
* `CovariantDerivative.eq_of_forall_hasSectionalCurvatureAt` and
  `CovariantDerivative.hasConstantSectionalCurvature_of_forall_hasSectionalCurvatureAt`:
  **Schur's theorem** on a preconnected manifold.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Interscience
  (1963), Chapter V, Section 2 (Schur's theorem, proved from the second Bianchi identity).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

omit [T2Space M] [ContMDiffCovariantDerivative cov ∞] in
/-- For a metric-compatible connection, the tensor `(Y, Z, σ) ↦ ⟨Z, σ⟩ Y - ⟨Y, σ⟩ Z` is parallel:
the covariant derivative of `⟨Z, σ⟩ Y - ⟨Y, σ⟩ Z` along `X` is the sum of the three expressions
obtained by differentiating one of `Y`, `Z`, `σ` at a time. -/
private theorem IsMetricCompatible.covariantDerivative_inner_smul_sub_inner_smul
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (X : Π x : M, TangentSpace I x) {Y Z σ : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov (fun y ↦ ⟪Z y, σ y⟫_ℝ • Y y - ⟪Y y, σ y⟫_ℝ • Z y) x (X x) =
      (⟪Z x, σ x⟫_ℝ • cov Y x (X x) - ⟪cov Y x (X x), σ x⟫_ℝ • Z x) +
        (⟪cov Z x (X x), σ x⟫_ℝ • Y x - ⟪Y x, σ x⟫_ℝ • cov Z x (X x)) +
          (⟪Z x, cov σ x (X x)⟫_ℝ • Y x - ⟪Y x, cov σ x (X x)⟫_ℝ • Z x) := by
  set f₁ : M → ℝ := fun y ↦ ⟪Z y, σ y⟫_ℝ
  set f₂ : M → ℝ := fun y ↦ ⟪Y y, σ y⟫_ℝ
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  have hf₁ : CMDiff ∞ f₁ :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hZ hσ
  have hf₂ : CMDiff ∞ f₂ :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hY hσ
  have hd {A B : Π y : M, TangentSpace I y} (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) :
      mvfderiv I (fun y ↦ ⟪A y, B y⟫_ℝ) x (X x) =
        ⟪cov A x (X x), B x⟫_ℝ + ⟪A x, cov B x (X x)⟫_ℝ :=
    hcov.mvfderiv_inner_eq X (hA.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp))
  have hcd := cov.isCovariantDerivativeOnUniv
  change cov (f₁ • Y - f₂ • Z) x (X x) = _
  rw [hcd.sub ((hf₁.smul_section hY).mdifferentiableAt (by simp))
      ((hf₂.smul_section hZ).mdifferentiableAt (by simp)),
    hcd.leibniz (hY.mdifferentiableAt (by simp)) (hf₁.mdifferentiableAt (by simp)),
    hcd.leibniz (hZ.mdifferentiableAt (by simp)) (hf₂.mdifferentiableAt (by simp))]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, f₁, f₂,
    hd hZ hσ, hd hY hσ]
  module

/-- Let the curvature tensor of a metric-compatible connection have the pointwise
constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)` at every point `y`. At a point
where `κ` is differentiable, the covariant derivative of the curvature along `X`,
`(∇_X R)(Y, Z)σ = ∇_X (R(Y, Z)σ) - R(∇_X Y, Z)σ - R(Y, ∇_X Z)σ - R(Y, Z)(∇_X σ)`,
is then `dκ(X) (⟨Z, σ⟩ Y - ⟨Y, σ⟩ Z)`. -/
theorem IsMetricCompatible.covariantDerivative_curvatureOperator_eq_mvfderiv_smul
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    {κ : M → ℝ} (hκ : ∀ (y : M) (w u v : TangentSpace I y),
      curvature y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u))
    {X Y Z σ : Π x : M, TangentSpace I x} (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (hσ : CMDiff ∞ (T% σ)) {x : M}
    (hκx : MDifferentiableAt I 𝓘(ℝ) κ x) :
    cov (curvatureOperator cov Y Z σ) x (X x) -
        curvatureOperator cov (fun y ↦ cov Y y (X y)) Z σ x -
          curvatureOperator cov Y (fun y ↦ cov Z y (X y)) σ x -
            curvatureOperator cov Y Z (fun y ↦ cov σ y (X y)) x =
      mvfderiv I κ x (X x) • (⟪Z x, σ x⟫_ℝ • Y x - ⟪Y x, σ x⟫_ℝ • Z x) := by
  have hR : curvatureOperator cov Y Z σ =
      κ • fun y ↦ ⟪Z y, σ y⟫_ℝ • Y y - ⟪Y y, σ y⟫_ℝ • Z y := by
    funext y
    rw [← curvatureTensor_apply cov y hY hZ hσ, hκ, Pi.smul_apply']
  have hP : CMDiff ∞ (T% fun y ↦ ⟪Z y, σ y⟫_ℝ • Y y - ⟪Y y, σ y⟫_ℝ • Z y) := by
    have hf₁ : CMDiff ∞ fun y ↦ ⟪Z y, σ y⟫_ℝ :=
      ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hZ hσ
    have hf₂ : CMDiff ∞ fun y ↦ ⟪Y y, σ y⟫_ℝ :=
      ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hY hσ
    exact (hf₁.smul_section hY).sub_section (hf₂.smul_section hZ)
  -- Leibniz splits off `dκ(X)`; the parallel model tensor accounts for the rest.
  rw [hR, cov.isCovariantDerivativeOnUniv.leibniz (hP.mdifferentiableAt (by simp)) hκx,
    add_apply, smul_apply,
    hcov.covariantDerivative_inner_smul_sub_inner_smul X hY hZ hσ x,
    ← curvatureTensor_apply cov x (cov.contMDiff_apply hX hY) hZ hσ,
    ← curvatureTensor_apply cov x hY (cov.contMDiff_apply hX hZ) hσ,
    ← curvatureTensor_apply cov x hY hZ (cov.contMDiff_apply hX hσ), hκ, hκ, hκ]
  simp only [ContinuousLinearMap.smulRight_apply]
  module

/-- **Schur's theorem**, local form. Let a metric-compatible torsion-free connection have
curvature tensor of the pointwise constant-curvature form `R(w, u)v = κ(y) (⟨u, v⟩ w - ⟨w, v⟩ u)`
at every point `y`, in dimension at least three. Then `dκ` vanishes wherever `κ` is
differentiable. -/
theorem mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ}
    (hκ : ∀ (y : M) (w u v : TangentSpace I y),
      curvature y w u v = κ y • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u))
    {x : M} (hκx : MDifferentiableAt I 𝓘(ℝ) κ x) : mfderiv I 𝓘(ℝ) κ x = 0 := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have ho := orthonormal_iff_ite.1 b.orthonormal
  -- Evaluate the second Bianchi identity on three orthonormal fields `X, Y, Z` and `σ = Y`, and
  -- pair it with `Z`: only the term `-dκ(X)` survives.
  have hb (i : Fin (Module.finrank ℝ (TangentSpace I x))) : mvfderiv I κ x (b i) = 0 := by
    obtain ⟨j, k, hij, hik, hjk⟩ : ∃ j k, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
      have h1 : 1 < ({i}ᶜ : Finset (Fin (Module.finrank ℝ (TangentSpace I x)))).card := by
        rw [Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
        exact Nat.lt_sub_of_add_lt hdim
      obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 h1
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj hk
      exact ⟨j, k, Ne.symm hj, Ne.symm hk, hjk⟩
    obtain ⟨X, hX, hXx⟩ := FiberBundle.exists_contMDiff_section_eq I E (b i)
    obtain ⟨Y, hY, hYx⟩ := FiberBundle.exists_contMDiff_section_eq I E (b j)
    obtain ⟨Z, hZ, hZx⟩ := FiberBundle.exists_contMDiff_section_eq I E (b k)
    have h := covariantDerivative_curvatureOperator_cyclic_eq_zero cov cov
      ((isTorsionFree_iff_torsion_eq_zero cov).2 ht) hX hY hZ hY x
    rw [hcov.covariantDerivative_curvatureOperator_eq_mvfderiv_smul hκ hX hY hZ hY hκx,
      hcov.covariantDerivative_curvatureOperator_eq_mvfderiv_smul hκ hY hZ hX hY hκx,
      hcov.covariantDerivative_curvatureOperator_eq_mvfderiv_smul hκ hZ hX hY hY hκx,
      hXx, hYx, hZx] at h
    have h' := congrArg (fun v ↦ ⟪v, b k⟫_ℝ) h
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, ho, inner_zero_left,
      hij, hik, hjk, hjk.symm, ite_true, ite_false] at h'
    linarith
  have hL : mvfderiv I κ x = 0 := by
    ext v
    rw [← b.sum_repr v]
    simp [map_sum, map_smul, hb]
  ext v
  simpa [mvfderiv] using congr($hL v)

/-- **Schur's theorem.** Let a metric-compatible torsion-free connection on a preconnected
manifold of dimension at least three have, at every point `x`, the same sectional curvature `κ x`
on all tangent two-planes at `x`. Then `κ` is constant. -/
theorem eq_of_forall_hasSectionalCurvatureAt [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ}
    (hκ : ∀ x, cov.HasSectionalCurvatureAt hcov x (κ x)) (x y : M) : κ x = κ y := by
  have hform (y : M) := (hκ y).curvatureTensor_eq_smul_inner_sub ht
  -- `κ` is a constant multiple of the smooth scalar curvature `n (n - 1) κ`.
  have hn : ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E - 1)) ≠ 0 := by
    have : (3 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hdim
    nlinarith
  have hκeq : κ = fun y ↦ cov.scalarCurvature y / ((Module.finrank ℝ E : ℝ) *
      (Module.finrank ℝ E - 1)) := by
    funext y
    rw [(hκ y).scalarCurvature_eq ht, eq_div_iff hn]
    exact mul_comm _ _
  have hκd : MDifferentiable I 𝓘(ℝ) κ := by
    rw [hκeq]
    exact (cov.contMDiff_scalarCurvature.div_const _).mdifferentiable (by simp)
  exact hκd.apply_eq_of_mfderiv_eq_zero (fun z ↦
    mfderiv_eq_zero_of_curvatureTensor_eq_smul_inner_sub hcov ht hdim hform (hκd z)) x y

/-- **Schur's theorem**, global form. If a metric-compatible torsion-free connection on a
preconnected manifold of dimension at least three has, at every point `x`, the same sectional
curvature `κ x` on all tangent two-planes at `x`, then it has constant sectional curvature
`κ x₀` for any point `x₀`. -/
theorem hasConstantSectionalCurvature_of_forall_hasSectionalCurvatureAt [PreconnectedSpace M]
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (ht : cov.torsion = 0) (hdim : 3 ≤ Module.finrank ℝ E) {κ : M → ℝ}
    (hκ : ∀ x, cov.HasSectionalCurvatureAt hcov x (κ x)) (x₀ : M) :
    cov.HasConstantSectionalCurvature hcov (κ x₀) :=
  (cov.hasConstantSectionalCurvature_iff hcov _).2 fun x ↦
    eq_of_forall_hasSectionalCurvatureAt hcov ht hdim hκ x x₀ ▸ hκ x

end CovariantDerivative
