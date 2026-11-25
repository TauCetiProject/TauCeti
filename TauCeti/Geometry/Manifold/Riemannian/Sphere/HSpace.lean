/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Topology.Homotopy.HSpaces
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.VectorField
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# A tangent frame on a sphere gives a multiplication with a strict unit

Let `E` be a real inner product space of dimension `n + 1` and `Sⁿ = sphere (0 : E) 1`. Suppose
`V : Fin n → Sⁿ → E` is a continuous family of vectors such that, at every `x ∈ Sⁿ`, the
`n + 1` vectors `x, V 0 x, …, V (n - 1) x` are linearly independent. This holds for the ambient
images of `n` tangent vector fields on `Sⁿ` that are linearly independent at every point.

Applying the Gram–Schmidt process to `x, V 0 x, …, V (n - 1) x` gives an orthonormal basis
`TauCeti.sphereFrameBasis V x` of `E` whose first vector is `x` itself
(`TauCeti.sphereFrameBasis_zero`), depending continuously on `x`
(`TauCeti.continuous_sphereFrameBasis`). For a base point `x₀ ∈ Sⁿ`, the linear isometry
`TauCeti.sphereFrameIsometry V x₀ x` sending the basis at `x₀` to the basis at `x` is the
orthogonal transformation `A_x` with `A_x x₀ = x` and `A_x₀ = id`, and `A_x y` is jointly
continuous in `x` and `y`. Restricting to the sphere gives a continuous multiplication
`TauCeti.sphereFrameMul V x₀ x y = A_x y` on `Sⁿ` for which `x₀` is a strict two-sided unit,
hence an H-space structure `TauCeti.sphereFrameHSpace` in the sense of Mathlib's `HSpace`, whose
unit homotopies are constant.

For tangent frames, `TauCeti.exists_linearIsometryEquiv_family_of_tangentFrame` and
`TauCeti.exists_continuous_unital_mul_of_tangentFrame` state the result for `n` continuous tangent
vector fields on `Sⁿ` that are linearly independent at every point. This is the first step of the
classical argument that a parallelizable sphere `Sⁿ` has `n ∈ {0, 1, 3, 7}`: the Hopf construction
on such a multiplication produces a map `S²ⁿ⁺¹ → Sⁿ⁺¹` of Hopf invariant `±1`.

## Main definitions

* `TauCeti.sphereFrameBasis`: the Gram–Schmidt orthonormal basis of `E` built from
  `x, V 0 x, …, V (n - 1) x`.
* `TauCeti.sphereFrameIsometry`: the linear isometry `A_x` sending the basis at `x₀` to the basis
  at `x`.
* `TauCeti.sphereFrameMul`: the multiplication `(x, y) ↦ A_x y` on the unit sphere.
* `TauCeti.sphereFrameHSpace`: the resulting H-space structure on the unit sphere.

## Main results

* `TauCeti.sphereFrameIsometry_apply_basepoint`, `TauCeti.sphereFrameIsometry_self`: `A_x x₀ = x`
  and `A_x₀ = id`.
* `TauCeti.continuous_sphereFrameIsometry_apply`, `TauCeti.continuous_sphereFrameMul`: joint
  continuity of `(x, y) ↦ A_x y`.
* `TauCeti.sphereFrameMul_basepoint_left`, `TauCeti.sphereFrameMul_basepoint_right`: `x₀` is a
  strict two-sided unit.
* `TauCeti.exists_continuous_unital_mul_of_tangentFrame`: a unit sphere with `n` continuous tangent
  vector fields, linearly independent at every point, carries a continuous multiplication with a
  strict two-sided unit at any prescribed point.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §2.3.
-/

public section

noncomputable section

open Metric Module InnerProductSpace
open scoped InnerProductSpace Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

section Basis

/-- The orthonormal basis of `E` obtained by applying the Gram–Schmidt process to the `n + 1`
vectors `x, V 0 x, …, V (n - 1) x`. When these vectors are linearly independent, it is their
normalized Gram–Schmidt process (`TauCeti.sphereFrameBasis_eq_gramSchmidtNormed`); its first vector
is always `x` (`TauCeti.sphereFrameBasis_zero`). -/
def sphereFrameBasis (V : Fin n → sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    OrthonormalBasis (Fin (n + 1)) ℝ E :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  gramSchmidtOrthonormalBasis (by rw [Fintype.card_fin]; exact Fact.out)
    (Fin.cons (x : E) fun i ↦ V i x)

/-- When `x, V 0 x, …, V (n - 1) x` are linearly independent, `TauCeti.sphereFrameBasis V x` is
the normalized Gram–Schmidt process applied to them. -/
theorem sphereFrameBasis_eq_gramSchmidtNormed {V : Fin n → sphere (0 : E) 1 → E}
    {x : sphere (0 : E) 1} (hli : LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (j : Fin (n + 1)) :
    sphereFrameBasis V x j = gramSchmidtNormed ℝ (Fin.cons (x : E) fun i ↦ V i x) j :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  gramSchmidtOrthonormalBasis_apply _ <|
    (norm_ne_zero_iff.mp ((gramSchmidtNormed_unit_length j hli).symm ▸ one_ne_zero))

/-- The first vector of `TauCeti.sphereFrameBasis V x` is `x`. -/
@[simp]
theorem sphereFrameBasis_zero (V : Fin n → sphere (0 : E) 1 → E) (x : sphere (0 : E) 1) :
    sphereFrameBasis V x 0 = x := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hx : gramSchmidtNormed ℝ (Fin.cons (x : E) fun i ↦ V i x) 0 = x :=
    gramSchmidtNormed_eq_self_of_inner_eq_zero (fun j hj ↦ absurd hj (Fin.not_lt_zero j))
      (by simp)
  rw [sphereFrameBasis,
    gramSchmidtOrthonormalBasis_apply _ (by simp [hx, ne_zero_of_mem_unit_sphere]), hx]

/-- If `V` is continuous and `x, V 0 x, …, V (n - 1) x` are linearly independent at every point,
then each vector of `TauCeti.sphereFrameBasis V x` depends continuously on `x`. -/
theorem continuous_sphereFrameBasis {V : Fin n → sphere (0 : E) 1 → E}
    (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (j : Fin (n + 1)) :
    Continuous fun x ↦ sphereFrameBasis V x j := by
  have hF (k : Fin (n + 1)) :
      Continuous fun x : sphere (0 : E) 1 ↦
        (Fin.cons (x : E) fun i ↦ V i x : Fin (n + 1) → E) k := by
    cases k using Fin.cases with
    | zero => simpa using continuous_subtypeVal
    | succ i => simpa using hV i
  simp_rw [sphereFrameBasis_eq_gramSchmidtNormed (hli _)]
  exact Continuous.gramSchmidtNormed
    (v := fun k (x : sphere (0 : E) 1) ↦ (Fin.cons (x : E) fun i ↦ V i x : Fin (n + 1) → E) k)
    j (fun k _ ↦ hF k) fun x ↦ (hli x).linearIndepOn _

end Basis

section Isometry

/-- The linear isometry `A_x` of `E` sending `TauCeti.sphereFrameBasis V x₀` to
`TauCeti.sphereFrameBasis V x`, index by index. It sends `x₀` to `x`
(`TauCeti.sphereFrameIsometry_apply_basepoint`) and is the identity at `x = x₀`
(`TauCeti.sphereFrameIsometry_self`). -/
def sphereFrameIsometry (V : Fin n → sphere (0 : E) 1 → E) (x₀ x : sphere (0 : E) 1) :
    E ≃ₗᵢ[ℝ] E :=
  (sphereFrameBasis V x₀).equiv (sphereFrameBasis V x) (Equiv.refl _)

/-- `TauCeti.sphereFrameIsometry V x₀ x` sends the `j`-th basis vector at `x₀` to the `j`-th
basis vector at `x`. -/
@[simp]
theorem sphereFrameIsometry_apply_sphereFrameBasis (V : Fin n → sphere (0 : E) 1 → E)
    (x₀ x : sphere (0 : E) 1) (j : Fin (n + 1)) :
    sphereFrameIsometry V x₀ x (sphereFrameBasis V x₀ j) = sphereFrameBasis V x j :=
  OrthonormalBasis.equiv_apply_basis _ _ _ j

/-- `TauCeti.sphereFrameIsometry V x₀ x` sends the base point `x₀` to `x`. -/
@[simp]
theorem sphereFrameIsometry_apply_basepoint (V : Fin n → sphere (0 : E) 1 → E)
    (x₀ x : sphere (0 : E) 1) :
    sphereFrameIsometry V x₀ x x₀ = x := by
  simpa using sphereFrameIsometry_apply_sphereFrameBasis V x₀ x 0

/-- At the base point, `TauCeti.sphereFrameIsometry V x₀ x₀` is the identity. -/
@[simp]
theorem sphereFrameIsometry_self (V : Fin n → sphere (0 : E) 1 → E) (x₀ : sphere (0 : E) 1) :
    sphereFrameIsometry V x₀ x₀ = LinearIsometryEquiv.refl ℝ E :=
  OrthonormalBasis.equiv_self_rfl _

/-- `TauCeti.sphereFrameIsometry V x₀ x y` expands `y` in the basis at `x₀` and recombines the
coefficients with the basis at `x`. -/
theorem sphereFrameIsometry_apply (V : Fin n → sphere (0 : E) 1 → E) (x₀ x : sphere (0 : E) 1)
    (y : E) :
    sphereFrameIsometry V x₀ x y =
      ∑ j, ⟪sphereFrameBasis V x₀ j, y⟫_ℝ • sphereFrameBasis V x j := by
  simp [sphereFrameIsometry, OrthonormalBasis.equiv_apply, OrthonormalBasis.repr_apply_apply]

/-- If `V` is continuous and `x, V 0 x, …, V (n - 1) x` are linearly independent at every point,
then `(x, y) ↦ TauCeti.sphereFrameIsometry V x₀ x y` is jointly continuous. -/
theorem continuous_sphereFrameIsometry_apply {V : Fin n → sphere (0 : E) 1 → E}
    (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (x₀ : sphere (0 : E) 1) :
    Continuous fun p : sphere (0 : E) 1 × E ↦ sphereFrameIsometry V x₀ p.1 p.2 := by
  simp_rw [sphereFrameIsometry_apply]
  exact continuous_finsetSum _ fun j _ ↦ (continuous_const.inner continuous_snd).smul
    ((continuous_sphereFrameBasis hV hli j).comp continuous_fst)

end Isometry

section Mul

/-- The multiplication `(x, y) ↦ A_x y` on the unit sphere, where `A_x` is the linear isometry
`TauCeti.sphereFrameIsometry V x₀ x`. The base point `x₀` is a strict two-sided unit
(`TauCeti.sphereFrameMul_basepoint_left`, `TauCeti.sphereFrameMul_basepoint_right`). -/
def sphereFrameMul (V : Fin n → sphere (0 : E) 1 → E) (x₀ x y : sphere (0 : E) 1) :
    sphere (0 : E) 1 :=
  ⟨sphereFrameIsometry V x₀ x y, by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, norm_eq_of_mem_sphere]⟩

/-- The product `TauCeti.sphereFrameMul V x₀ x y`, as a vector of `E`, is `A_x y`. -/
@[simp]
theorem coe_sphereFrameMul (V : Fin n → sphere (0 : E) 1 → E) (x₀ x y : sphere (0 : E) 1) :
    (sphereFrameMul V x₀ x y : E) = sphereFrameIsometry V x₀ x y :=
  (rfl)

/-- The base point is a left unit for `TauCeti.sphereFrameMul V x₀`. -/
@[simp]
theorem sphereFrameMul_basepoint_left (V : Fin n → sphere (0 : E) 1 → E)
    (x₀ y : sphere (0 : E) 1) :
    sphereFrameMul V x₀ x₀ y = y :=
  Subtype.ext <| by simp

/-- The base point is a right unit for `TauCeti.sphereFrameMul V x₀`. -/
@[simp]
theorem sphereFrameMul_basepoint_right (V : Fin n → sphere (0 : E) 1 → E)
    (x₀ x : sphere (0 : E) 1) :
    sphereFrameMul V x₀ x x₀ = x :=
  Subtype.ext <| by simp

/-- If `V` is continuous and `x, V 0 x, …, V (n - 1) x` are linearly independent at every point,
then `TauCeti.sphereFrameMul V x₀` is jointly continuous. -/
theorem continuous_sphereFrameMul {V : Fin n → sphere (0 : E) 1 → E}
    (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (x₀ : sphere (0 : E) 1) :
    Continuous (Function.uncurry (sphereFrameMul V x₀)) :=
  ((continuous_sphereFrameIsometry_apply hV hli x₀).comp
    (continuous_fst.prodMk (continuous_subtypeVal.comp continuous_snd))).subtype_mk _

/-- The H-space structure on the unit sphere given by `TauCeti.sphereFrameMul V x₀`. Since `x₀` is
a strict two-sided unit, both unit homotopies are constant. -/
@[instance_reducible]
def sphereFrameHSpace {V : Fin n → sphere (0 : E) 1 → E} (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (x₀ : sphere (0 : E) 1) : HSpace (sphere (0 : E) 1) where
  hmul := ⟨Function.uncurry (sphereFrameMul V x₀), continuous_sphereFrameMul hV hli x₀⟩
  e := x₀
  hmul_e_e := sphereFrameMul_basepoint_left V x₀ x₀
  eHmul := (ContinuousMap.HomotopyRel.refl _ _).cast
    (ContinuousMap.ext fun y ↦ (sphereFrameMul_basepoint_left V x₀ y).symm) rfl
  hmulE := (ContinuousMap.HomotopyRel.refl _ _).cast
    (ContinuousMap.ext fun x ↦ (sphereFrameMul_basepoint_right V x₀ x).symm) rfl

/-- The multiplication of `TauCeti.sphereFrameHSpace` is `TauCeti.sphereFrameMul`. -/
@[simp]
theorem sphereFrameHSpace_hmul_apply {V : Fin n → sphere (0 : E) 1 → E}
    (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (x₀ : sphere (0 : E) 1) (p : sphere (0 : E) 1 × sphere (0 : E) 1) :
    (sphereFrameHSpace hV hli x₀).hmul p = sphereFrameMul V x₀ p.1 p.2 :=
  (rfl)

/-- The unit of `TauCeti.sphereFrameHSpace` is the chosen base point. -/
@[simp]
theorem sphereFrameHSpace_e {V : Fin n → sphere (0 : E) 1 → E} (hV : ∀ i, Continuous (V i))
    (hli : ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x))
    (x₀ : sphere (0 : E) 1) :
    (sphereFrameHSpace hV hli x₀).e = x₀ :=
  (rfl)

end Mul

section TangentFrame

/-- The ambient images of `n` continuous tangent vector fields on `Sⁿ`, linearly independent at
every point, form a continuous family `V` with `x, V 0 x, …, V (n - 1) x` linearly independent at
every point. -/
theorem exists_continuous_linearIndependent_finCons_of_tangentFrame
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, Continuous fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))
    (hli : ∀ x, LinearIndependent ℝ fun i ↦ v i x) :
    ∃ V : Fin n → sphere (0 : E) 1 → E, (∀ i, Continuous (V i)) ∧
      ∀ x : sphere (0 : E) 1, LinearIndependent ℝ (Fin.cons (x : E) fun i ↦ V i x) := by
  let V : Fin n → sphere (0 : E) 1 → E := fun i x ↦ sphereTangentEquiv x (v i x)
  have hVorth (i : Fin n) (x : sphere (0 : E) 1) : V i x ∈ (ℝ ∙ (x : E))ᗮ :=
    (sphereTangentEquiv x (v i x)).property
  refine ⟨V, fun i ↦ ?_, fun x ↦ ?_⟩
  · have hpush := contMDiff_tangentBundle_sphere_iff.mp (contMDiff_zero_iff.mpr (hv i))
    simpa only [V, coe_sphereTangentEquiv_apply, mvfderiv_apply_eq_mfderiv_apply] using
      hpush.continuous
  · have hVli : LinearIndependent ℝ fun i ↦ V i x := by
      rw [← linearIndependent_sphereTangentField_iff (n := n) (fun i x ↦ hVorth i x) x]
      simpa only [V, sphereTangentField_coe_sphereTangentEquiv] using hli x
    refine hVli.finCons fun hx ↦ ?_
    -- The span of the tangent vectors lies in `(ℝ ∙ x)ᗮ`, which does not contain `x ≠ 0`.
    have hspan : Submodule.span ℝ (Set.range fun i ↦ V i x) ≤ (ℝ ∙ (x : E))ᗮ :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ hVorth i x)
    have hx0 := Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
      (hspan hx)
    simp at hx0

/-- **A tangent frame on `Sⁿ` gives orthogonal transformations `A_x` with `A_x x₀ = x`.** If the
unit sphere of an `(n + 1)`-dimensional real inner product space carries `n` continuous tangent
vector fields that are linearly independent at every point, then for every base point `x₀` there
are linear isometries `A_x` of `E`, depending jointly continuously on `x` and the argument, such
that `A_x x₀ = x` and `A_x₀` is the identity. -/
theorem exists_linearIsometryEquiv_family_of_tangentFrame (x₀ : sphere (0 : E) 1)
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, Continuous fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))
    (hli : ∀ x, LinearIndependent ℝ fun i ↦ v i x) :
    ∃ A : sphere (0 : E) 1 → E ≃ₗᵢ[ℝ] E,
      Continuous (fun p : sphere (0 : E) 1 × E ↦ A p.1 p.2) ∧
        A x₀ = LinearIsometryEquiv.refl ℝ E ∧ ∀ x, A x x₀ = x := by
  obtain ⟨V, hV, hVli⟩ := exists_continuous_linearIndependent_finCons_of_tangentFrame hv hli
  exact ⟨sphereFrameIsometry V x₀, continuous_sphereFrameIsometry_apply hV hVli x₀,
    sphereFrameIsometry_self V x₀, sphereFrameIsometry_apply_basepoint V x₀⟩

/-- **A tangent frame on `Sⁿ` gives a multiplication with a strict two-sided unit.** If the unit
sphere of an `(n + 1)`-dimensional real inner product space carries `n` continuous tangent vector
fields that are linearly independent at every point, then for every base point `x₀` it carries a
jointly continuous multiplication `μ` with `μ x₀ y = y` and `μ x x₀ = x`. -/
theorem exists_continuous_unital_mul_of_tangentFrame (x₀ : sphere (0 : E) 1)
    {v : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hv : ∀ i, Continuous fun x ↦ (⟨x, v i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))
    (hli : ∀ x, LinearIndependent ℝ fun i ↦ v i x) :
    ∃ μ : sphere (0 : E) 1 → sphere (0 : E) 1 → sphere (0 : E) 1,
      Continuous (Function.uncurry μ) ∧ (∀ y, μ x₀ y = y) ∧ ∀ x, μ x x₀ = x := by
  obtain ⟨V, hV, hVli⟩ := exists_continuous_linearIndependent_finCons_of_tangentFrame hv hli
  exact ⟨sphereFrameMul V x₀, continuous_sphereFrameMul hV hVli x₀,
    sphereFrameMul_basepoint_left V x₀, sphereFrameMul_basepoint_right V x₀⟩

end TangentFrame

end TauCeti
