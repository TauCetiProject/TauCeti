/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Tensor
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# The second covariant derivative of a section and the Ricci identity

Let `∇` be a smooth connection on a vector bundle `V` and `∇ᵀ` a connection on the tangent
bundle. The second covariant derivative of a smooth section `σ` of `V` is the tensor

`∇²σ(X, Y) = ∇_X (∇_Y σ) - ∇_{∇ᵀ_X Y} σ`.

It is linear over functions in both `X` and `Y`, so at each point it is a bilinear map from pairs
of tangent vectors to the fibre. This file constructs it with globally smooth extensions of the
tangent vectors and the tensoriality criterion `TauCeti.Manifold.eq_of_contMDiff_tensorial`.

The **Ricci identity** expresses the failure of `∇²σ` to be symmetric through the curvature `R`
of `∇` and the torsion `T` of `∇ᵀ`:

`∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ - ∇_{T(u, v)} σ`,

where `T(X, Y) = ∇ᵀ_X Y - ∇ᵀ_Y X - [X, Y]` is Mathlib's `CovariantDerivative.torsion`.
For a torsion-free `∇ᵀ`, such as a Levi-Civita connection, the torsion term disappears and the
antisymmetric part of `∇²σ` is the curvature `R(u, v) σ`. For `V` the tangent bundle this is the
Ricci identity for vector fields. It is the rule for commuting covariant derivatives used in
Bochner and Weitzenböck formulas.

## Main definitions and results

* `CovariantDerivative.secondCovariantDerivative`: the second covariant derivative `∇²σ` at a
  point, as a bilinear map. It is zero when `σ` is not smooth.
* `CovariantDerivative.secondCovariantDerivative_apply`: its value on a smooth vector field in
  the second slot, `∇²σ(u, Y) = ∇_u (∇_Y σ) - ∇_{∇ᵀ_u Y} σ`.
* `CovariantDerivative.eq_secondCovariantDerivative_iff`: this value characterizes `∇²σ`.
* `CovariantDerivative.secondCovariantDerivative_sub_swap`: the Ricci identity with its torsion
  correction.
* `CovariantDerivative.secondCovariantDerivative_sub_swap_of_isTorsionFree`: the Ricci identity
  `∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ` for a torsion-free connection on the tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 4 (the total covariant derivative and the second covariant derivative) and Chapter 7
  (the Ricci identities).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
  {σ : Π y : M, V y}

/-- The expression `∇_u (∇_Y σ) - ∇_{∇ᵀ_u Y} σ`, for a vector field `Y` and a tangent vector `u`
at `x`. -/
private def secondDerivAux (σ : Π y : M, V y) (x : M) (Y : Π y : M, TangentSpace I y)
    (u : TangentSpace I x) : V x :=
  cov (fun y ↦ cov σ y (Y y)) x u - cov σ x (covT Y x u)

private theorem secondDerivAux_add (hσ : CMDiff ∞ (T% σ)) (x : M)
    {Y Y' : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (u : TangentSpace I x) :
    secondDerivAux cov covT σ x (Y + Y') u =
      secondDerivAux cov covT σ x Y u + secondDerivAux cov covT σ x Y' u := by
  have hYσ := (cov.contMDiff_apply hY hσ).mdifferentiable (by simp) x
  have hY'σ := (cov.contMDiff_apply hY' hσ).mdifferentiable (by simp) x
  have hsum : (fun y ↦ cov σ y ((Y + Y') y)) =
      (fun y ↦ cov σ y (Y y)) + fun y ↦ cov σ y (Y' y) := by
    funext y
    exact map_add (cov σ y) (Y y) (Y' y)
  simp only [secondDerivAux, hsum, cov.isCovariantDerivativeOnUniv.add hYσ hY'σ,
    covT.isCovariantDerivativeOnUniv.add (hY.mdifferentiable (by simp) x)
      (hY'.mdifferentiable (by simp) x),
    add_apply, map_add]
  abel

private theorem secondDerivAux_smul (hσ : CMDiff ∞ (T% σ)) (x : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {Y : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y))
    (u : TangentSpace I x) :
    secondDerivAux cov covT σ x (f • Y) u = f x • secondDerivAux cov covT σ x Y u := by
  have hYσ := (cov.contMDiff_apply hY hσ).mdifferentiable (by simp) x
  have hfx := hf.mdifferentiable (by simp) x
  have hprod : (fun y ↦ cov σ y ((f • Y) y)) = f • fun y ↦ cov σ y (Y y) := by
    funext y
    exact map_smul (cov σ y) (f y) (Y y)
  simp only [secondDerivAux, hprod, cov.isCovariantDerivativeOnUniv.leibniz hYσ hfx,
    covT.isCovariantDerivativeOnUniv.leibniz (hY.mdifferentiable (by simp) x) hfx,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_sub]
  abel

variable [FiniteDimensional ℝ E] [T2Space M]

/-- The expression `∇_u (∇_Y σ) - ∇_{∇ᵀ_u Y} σ` depends on the smooth field `Y` only through its
value at the base point. -/
private theorem secondDerivAux_congr (hσ : CMDiff ∞ (T% σ)) (x : M)
    {Y Y' : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (hY' : CMDiff ∞ (T% Y'))
    (hYY' : Y x = Y' x) (u : TangentSpace I x) :
    secondDerivAux cov covT σ x Y u = secondDerivAux cov covT σ x Y' u := by
  refine TauCeti.Manifold.eq_of_contMDiff_tensorial (I := I)
    (fun Z ↦ secondDerivAux cov covT σ x Z u) x ?_
    (fun hZ hZ' ↦ secondDerivAux_add cov covT hσ x hZ hZ' u)
    (fun hf hZ ↦ secondDerivAux_smul cov covT hσ x hf hZ u) hY hY' hYY'
  intro Z Z' hZ hZ' hZZ'
  have hnhds : Set.univ ∈ nhds x := Filter.univ_mem
  have hZσ : ∀ᶠ y in nhds x, cov σ y (Z y) = cov σ y (Z' y) := hZZ'.mono fun y hy ↦ by rw [hy]
  simp only [secondDerivAux,
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      ((cov.contMDiff_apply hZ hσ).mdifferentiable (by simp) x)
      ((cov.contMDiff_apply hZ' hσ).mdifferentiable (by simp) x) hnhds hZσ,
    covT.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hZ.mdifferentiable (by simp) x) (hZ'.mdifferentiable (by simp) x) hnhds hZZ']

/-- The value of `∇²σ` at `(u, v)`, computed with a chosen smooth extension of `v`. -/
private def secondDerivValue (σ : Π y : M, V y) (x : M) (u v : TangentSpace I x) : V x :=
  secondDerivAux cov covT σ x (Classical.choose (exists_contMDiff_section_eq I E v)) u

private theorem secondDerivValue_eq (hσ : CMDiff ∞ (T% σ)) (x : M)
    {Y : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (u : TangentSpace I x) :
    secondDerivValue cov covT σ x u (Y x) = secondDerivAux cov covT σ x Y u :=
  secondDerivAux_congr cov covT hσ x
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).1 hY
    (Classical.choose_spec (exists_contMDiff_section_eq I E (Y x))).2 u

/-- The second covariant derivative of a smooth section, as a bilinear map. -/
private def secondCovariantDerivativeOfContMDiff (hσ : CMDiff ∞ (T% σ)) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x :=
  LinearMap.mk₂ ℝ (secondDerivValue cov covT σ x)
    (fun u u' v ↦ by simp only [secondDerivValue, secondDerivAux, map_add]; abel)
    (fun c u v ↦ by simp only [secondDerivValue, secondDerivAux, map_smul, smul_sub])
    (fun u v v' ↦ by
      obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
      obtain ⟨Y', hY', rfl⟩ := exists_contMDiff_section_eq I E v'
      rw [← Pi.add_apply Y Y', secondDerivValue_eq cov covT hσ x (hY.add_section hY'),
        secondDerivValue_eq cov covT hσ x hY, secondDerivValue_eq cov covT hσ x hY',
        secondDerivAux_add cov covT hσ x hY hY'])
    (fun c u v ↦ by
      obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
      have hcY : CMDiff ∞ (T% ((fun _ : M ↦ c) • Y)) := contMDiff_const.smul_section hY
      have h := secondDerivValue_eq cov covT hσ x hcY u
      rw [secondDerivAux_smul cov covT hσ x contMDiff_const hY,
        ← secondDerivValue_eq cov covT hσ x hY] at h
      simpa only [Pi.smul_apply'] using h)

open scoped Classical in
/-- The second covariant derivative `∇²σ(u, v) = ∇_u (∇_Y σ) - ∇_{∇ᵀ_u Y} σ` of a smooth section
`σ` at `x`, where `Y` is any smooth vector field with `Y x = v`. It is bilinear in `(u, v)`, and
is defined to be zero when `σ` is not smooth. -/
def secondCovariantDerivative (σ : Π y : M, V y) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x :=
  if hσ : CMDiff ∞ (T% σ) then secondCovariantDerivativeOfContMDiff cov covT hσ x else 0

/-- The second covariant derivative of a smooth section, evaluated on a smooth vector field in
its second slot: `∇²σ(u, Y) = ∇_u (∇_Y σ) - ∇_{∇ᵀ_u Y} σ`. -/
theorem secondCovariantDerivative_apply (hσ : CMDiff ∞ (T% σ)) (x : M)
    {Y : Π y : M, TangentSpace I y} (hY : CMDiff ∞ (T% Y)) (u : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u (Y x) =
      cov (fun y ↦ cov σ y (Y y)) x u - cov σ x (covT Y x u) := by
  simp only [secondCovariantDerivative, hσ, ↓reduceDIte]
  exact secondDerivValue_eq cov covT hσ x hY u

/-- The second covariant derivative of a section which is not smooth is zero. -/
theorem secondCovariantDerivative_of_not_contMDiff (hσ : ¬CMDiff ∞ (T% σ)) (x : M) :
    cov.secondCovariantDerivative covT σ x = 0 := by
  simp only [secondCovariantDerivative, hσ, ↓reduceDIte]

/-- Evaluation on smooth vector fields in the second slot uniquely characterizes the second
covariant derivative of a smooth section. -/
theorem eq_secondCovariantDerivative_iff (hσ : CMDiff ∞ (T% σ)) (x : M)
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] V x) :
    B = cov.secondCovariantDerivative covT σ x ↔
      ∀ (Y : Π y : M, TangentSpace I y), CMDiff ∞ (T% Y) → ∀ u : TangentSpace I x,
        B u (Y x) = cov (fun y ↦ cov σ y (Y y)) x u - cov σ x (covT Y x u) := by
  constructor
  · rintro rfl Y hY u
    exact secondCovariantDerivative_apply cov covT hσ x hY u
  · intro h
    ext u v
    obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
    rw [h Y hY u, secondCovariantDerivative_apply cov covT hσ x hY u]

/-- The second covariant derivative is additive in the section. -/
theorem secondCovariantDerivative_add {τ : Π y : M, V y} (hσ : CMDiff ∞ (T% σ))
    (hτ : CMDiff ∞ (T% τ)) (x : M) :
    cov.secondCovariantDerivative covT (σ + τ) x =
      cov.secondCovariantDerivative covT σ x + cov.secondCovariantDerivative covT τ x := by
  refine ((eq_secondCovariantDerivative_iff cov covT (hσ.add_section hτ) x _).2
    fun Y hY u ↦ ?_).symm
  have hYσ := cov.contMDiff_apply hY hσ
  have hYτ := cov.contMDiff_apply hY hτ
  have hsum : (fun y ↦ cov (σ + τ) y (Y y)) =
      (fun y ↦ cov σ y (Y y)) + fun y ↦ cov τ y (Y y) := by
    funext y
    rw [Pi.add_apply, cov.isCovariantDerivativeOnUniv.add (hσ.mdifferentiable (by simp) y)
      (hτ.mdifferentiable (by simp) y), add_apply]
  rw [LinearMap.add_apply, LinearMap.add_apply, secondCovariantDerivative_apply cov covT hσ x hY,
    secondCovariantDerivative_apply cov covT hτ x hY, hsum,
    cov.isCovariantDerivativeOnUniv.add (hYσ.mdifferentiable (by simp) x)
      (hYτ.mdifferentiable (by simp) x),
    cov.isCovariantDerivativeOnUniv.add (hσ.mdifferentiable (by simp) x)
      (hτ.mdifferentiable (by simp) x)]
  simp only [add_apply]
  abel

/-- The second covariant derivative commutes with multiplication of the section by a constant. -/
theorem secondCovariantDerivative_const_smul (c : ℝ) (hσ : CMDiff ∞ (T% σ)) (x : M) :
    cov.secondCovariantDerivative covT (c • σ) x = c • cov.secondCovariantDerivative covT σ x := by
  refine ((eq_secondCovariantDerivative_iff cov covT hσ.const_smul_section x _).2
    fun Y hY u ↦ ?_).symm
  have hYσ := cov.contMDiff_apply hY hσ
  have hprod : (fun y ↦ cov (c • σ) y (Y y)) = c • fun y ↦ cov σ y (Y y) := by
    funext y
    rw [Pi.smul_apply,
      cov.isCovariantDerivativeOnUniv.smul_const c (hσ.mdifferentiable (by simp) y), smul_apply]
  rw [LinearMap.smul_apply, LinearMap.smul_apply, secondCovariantDerivative_apply cov covT hσ x hY,
    hprod, cov.isCovariantDerivativeOnUniv.smul_const c (hYσ.mdifferentiable (by simp) x),
    cov.isCovariantDerivativeOnUniv.smul_const c (hσ.mdifferentiable (by simp) x)]
  simp only [smul_apply, smul_sub]

section RicciIdentity

variable [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V I]

/-- **The Ricci identity**, with its torsion correction. For a smooth section `σ`, the
antisymmetric part of its second covariant derivative is the curvature of `∇` applied to `σ`,
corrected by the covariant derivative of `σ` along the torsion of `∇ᵀ`:

`∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ - ∇_{T(u, v)} σ`. -/
theorem secondCovariantDerivative_sub_swap (hσ : CMDiff ∞ (T% σ)) (x : M)
    (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v - cov.secondCovariantDerivative covT σ x v u =
      cov.curvatureTensor x u v (σ x) - cov σ x (covT.torsion x u v) := by
  obtain ⟨X, hX, rfl⟩ := exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E v
  rw [secondCovariantDerivative_apply cov covT hσ x hY,
    secondCovariantDerivative_apply cov covT hσ x hX, curvatureTensor_apply cov x hX hY hσ,
    curvatureOperator_apply,
    covT.torsion_apply (hX.mdifferentiable (by simp) x) (hY.mdifferentiable (by simp) x)]
  simp only [map_sub]
  abel

/-- **The Ricci identity.** For a torsion-free connection `∇ᵀ` on the tangent bundle, the
antisymmetric part of the second covariant derivative of a smooth section `σ` is the curvature
of `∇` applied to `σ`: `∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ`. -/
theorem secondCovariantDerivative_sub_swap_of_isTorsionFree (ht : covT.IsTorsionFree)
    (hσ : CMDiff ∞ (T% σ)) (x : M) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v - cov.secondCovariantDerivative covT σ x v u =
      cov.curvatureTensor x u v (σ x) := by
  rw [secondCovariantDerivative_sub_swap cov covT hσ x u v,
    (isTorsionFree_iff_torsion_eq_zero covT).1 ht]
  simp

/-- For a flat connection `∇` and a torsion-free connection `∇ᵀ` on the tangent bundle, the
second covariant derivative of every smooth section is symmetric. -/
theorem secondCovariantDerivative_comm_of_curvatureTensor_eq_zero (ht : covT.IsTorsionFree)
    {x : M} (hR : cov.curvatureTensor x = 0) (hσ : CMDiff ∞ (T% σ)) (u v : TangentSpace I x) :
    cov.secondCovariantDerivative covT σ x u v = cov.secondCovariantDerivative covT σ x v u := by
  rw [← sub_eq_zero, secondCovariantDerivative_sub_swap_of_isTorsionFree cov covT ht hσ x, hR]
  simp only [LinearMap.zero_apply]

end RicciIdentity

end CovariantDerivative
