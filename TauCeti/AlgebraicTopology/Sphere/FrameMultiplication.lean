/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The multiplication on a sphere with a tangent frame

Let `E` be a real inner product space of dimension `n + 1` and `Sⁿ` its unit sphere. Suppose that
every point `x` of `Sⁿ` carries a basis `F x` of `E` whose first vector is `x` itself, depending
continuously on `x`. A continuous tangent frame `w₁, …, wₙ` of `Sⁿ` gives one, namely
`(x, w₁ x, …, wₙ x)`. Orthonormalizing `F x` by the Gram-Schmidt process gives an orthonormal
basis whose first vector is still `x`; comparing it with the one at a fixed base point `e₀` gives
an orthogonal transformation `A x` of `E` (`TauCeti.sphereFrameIsometry`) with

* `A x e₀ = x` (`TauCeti.sphereFrameIsometry_apply_base`),
* `A e₀ = id` (`TauCeti.sphereFrameIsometry_self`),
* `(x, y) ↦ A x y` continuous (`TauCeti.continuous_sphereFrameIsometry_apply`).

The multiplication `μ (x, y) = A x y` of `Sⁿ` (`TauCeti.sphereFrameMul`) is therefore continuous
and has `e₀` as a strict two-sided unit: `μ (e₀, y) = y` and `μ (x, e₀) = x`
(`TauCeti.sphereFrameMul_base_left`, `TauCeti.sphereFrameMul_base_right`). In particular `Sⁿ` is
an H-space (`TauCeti.sphereFrameHSpace`), with constant unit homotopies.

`TauCeti.exists_sphere_mul_of_tangentFrame` starts from a frame of continuous sections of the
tangent bundle of Mathlib's manifold `sphere (0 : E) 1`, linearly independent at every point,
and produces such a multiplication with any prescribed unit; a smooth tangent frame is in
particular continuous. This is the first step of the proof that `Sⁿ` is parallelizable only for
`n ∈ {0, 1, 3, 7}`: the Hopf construction applied to `μ` gives a map `S²ⁿ⁺¹ → Sⁿ⁺¹` of Hopf
invariant `±1`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §2.3, proof of Theorem 2.16: an orthonormalized
  tangent frame of `Sⁿ`, normalized to the identity at a base point, makes `Sⁿ` an H-space.
-/

public section

open Metric Module InnerProductSpace
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The orthonormal basis of `E` obtained by the Gram-Schmidt process from the frame `F x`. -/
private def frameBasis (F : sphere (0 : E) 1 → Fin (n + 1) → E) (x : sphere (0 : E) 1) :
    OrthonormalBasis (Fin (n + 1)) ℝ E :=
  haveI : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  gramSchmidtOrthonormalBasis (by rw [Fact.out (p := finrank ℝ E = n + 1), Fintype.card_fin])
    (F x)

/-- On a linearly independent frame, `frameBasis` is the normalized Gram-Schmidt process. -/
private theorem frameBasis_apply {F : sphere (0 : E) 1 → Fin (n + 1) → E} {x : sphere (0 : E) 1}
    (hli : LinearIndependent ℝ (F x)) (i : Fin (n + 1)) :
    frameBasis F x i = gramSchmidtNormed ℝ (F x) i := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  refine gramSchmidtOrthonormalBasis_apply _ fun h ↦ ?_
  simpa [h] using gramSchmidtNormed_unit_length (𝕜 := ℝ) i hli

/-- The Gram-Schmidt process keeps the first vector `x` of the frame at `x`. -/
private theorem frameBasis_zero {F : sphere (0 : E) 1 → Fin (n + 1) → E} {x : sphere (0 : E) 1}
    (hF : F x 0 = x) : frameBasis F x 0 = x := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have h : gramSchmidtNormed ℝ (F x) 0 = F x 0 :=
    gramSchmidtNormed_eq_self_of_inner_eq_zero (fun j hj ↦ absurd hj (Fin.not_lt_zero j))
      (by simp [hF])
  rw [frameBasis, gramSchmidtOrthonormalBasis_apply _
    (by rw [h, hF]; exact ne_zero_of_mem_unit_sphere x), h, hF]

/-- The vectors of `frameBasis` depend continuously on the point. -/
private theorem continuous_frameBasis_apply {F : sphere (0 : E) 1 → Fin (n + 1) → E}
    (hF : ∀ i, Continuous fun x ↦ F x i) (hli : ∀ x, LinearIndependent ℝ (F x))
    (i : Fin (n + 1)) : Continuous fun x ↦ frameBasis F x i := by
  simp only [frameBasis_apply (hli _)]
  exact Continuous.gramSchmidtNormed (v := fun i x ↦ F x i) i (fun j _ ↦ hF j)
    fun x ↦ (hli x).linearIndepOn _

/-- **The orthogonal transformation of a sphere frame.** Given a family `F x` of `n + 1` vectors
of `E` at each point `x` of the unit sphere, `sphereFrameIsometry F e₀ x` is the linear isometry of
`E` taking the orthonormal basis `gramSchmidtOrthonormalBasis` of `F e₀` to that of `F x`, vector
by vector; when `F x` is a basis, that orthonormal basis is its Gram-Schmidt orthonormalization.
When the first vector of each `F x` is `x`, it takes `e₀` to `x`
(`TauCeti.sphereFrameIsometry_apply_base`); it is the identity at `x = e₀`
(`TauCeti.sphereFrameIsometry_self`). -/
def sphereFrameIsometry (F : sphere (0 : E) 1 → Fin (n + 1) → E) (e₀ x : sphere (0 : E) 1) :
    E ≃ₗᵢ[ℝ] E :=
  (frameBasis F e₀).equiv (frameBasis F x) (Equiv.refl _)

variable {F : sphere (0 : E) 1 → Fin (n + 1) → E}

/-- The orthogonal transformation of a sphere frame at its base point is the identity. -/
@[simp]
theorem sphereFrameIsometry_self (e₀ : sphere (0 : E) 1) :
    sphereFrameIsometry F e₀ e₀ = LinearIsometryEquiv.refl ℝ E :=
  OrthonormalBasis.equiv_self_rfl _

/-- The orthogonal transformation of a sphere frame at `x` takes the base point `e₀` to `x`,
when the first vector of each frame is its point. -/
@[simp]
theorem sphereFrameIsometry_apply_base (hF₀ : ∀ x, F x 0 = x) (e₀ x : sphere (0 : E) 1) :
    sphereFrameIsometry F e₀ x e₀ = x := by
  rw [sphereFrameIsometry, ← frameBasis_zero (hF₀ e₀), OrthonormalBasis.equiv_apply_basis,
    Equiv.refl_apply, frameBasis_zero (hF₀ x)]

/-- The orthogonal transformation of a continuous sphere frame depends continuously on the
point. -/
theorem continuous_sphereFrameIsometry_apply (hF : ∀ i, Continuous fun x ↦ F x i)
    (hli : ∀ x, LinearIndependent ℝ (F x)) (e₀ : sphere (0 : E) 1) :
    Continuous fun p : sphere (0 : E) 1 × E ↦ sphereFrameIsometry F e₀ p.1 p.2 := by
  simp only [sphereFrameIsometry, OrthonormalBasis.equiv_apply, OrthonormalBasis.repr_apply_apply,
    Equiv.refl_apply]
  exact continuous_finsetSum _ fun i _ ↦ (continuous_const.inner continuous_snd).smul
    ((continuous_frameBasis_apply hF hli i).comp continuous_fst)

/-- **The multiplication of a sphere frame.** For a continuous family `F` of bases of `E`
indexed by the unit sphere, `sphereFrameMul hF hli e₀` is the continuous multiplication
`(x, y) ↦ A x y` of the unit sphere, where `A = TauCeti.sphereFrameIsometry F e₀`. The point `e₀`
is a strict left unit, and also a strict right unit when the first vector of each `F x` is `x`
(`TauCeti.sphereFrameMul_base_left`, `TauCeti.sphereFrameMul_base_right`). -/
def sphereFrameMul (hF : ∀ i, Continuous fun x ↦ F x i) (hli : ∀ x, LinearIndependent ℝ (F x))
    (e₀ : sphere (0 : E) 1) : C(sphere (0 : E) 1 × sphere (0 : E) 1, sphere (0 : E) 1) where
  toFun p := ⟨sphereFrameIsometry F e₀ p.1 p.2,
    by rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
       exact mem_sphere_zero_iff_norm.1 p.2.2⟩
  continuous_toFun := by
    exact ((continuous_sphereFrameIsometry_apply hF hli e₀).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _

variable (hF : ∀ i, Continuous fun x ↦ F x i) (hli : ∀ x, LinearIndependent ℝ (F x))

/-- The multiplication of a sphere frame applies its orthogonal transformation at the left
factor to the right factor. -/
@[simp]
theorem coe_sphereFrameMul_apply (e₀ : sphere (0 : E) 1)
    (p : sphere (0 : E) 1 × sphere (0 : E) 1) :
    (sphereFrameMul hF hli e₀ p : E) = sphereFrameIsometry F e₀ p.1 p.2 :=
  (rfl)

/-- The base point is a strict left unit of the multiplication of a sphere frame. -/
@[simp]
theorem sphereFrameMul_base_left (e₀ y : sphere (0 : E) 1) :
    sphereFrameMul hF hli e₀ (e₀, y) = y :=
  Subtype.ext (by simp)

/-- The base point is a strict right unit of the multiplication of a sphere frame, when the first
vector of each frame is its point. -/
@[simp]
theorem sphereFrameMul_base_right (hF₀ : ∀ x, F x 0 = x) (e₀ x : sphere (0 : E) 1) :
    sphereFrameMul hF hli e₀ (x, e₀) = x :=
  Subtype.ext (by simp [sphereFrameIsometry_apply_base hF₀])

/-- **A sphere with a frame is an H-space.** A continuous family of bases of `E`, indexed by the
unit sphere, whose first vectors are the points of the sphere makes the sphere an H-space with
multiplication `TauCeti.sphereFrameMul` and unit the base point. The unit laws hold strictly, so
the unit homotopies are constant. -/
@[reducible, simps hmul e]
def sphereFrameHSpace (hF₀ : ∀ x, F x 0 = x) (e₀ : sphere (0 : E) 1) :
    HSpace (sphere (0 : E) 1) where
  hmul := sphereFrameMul hF hli e₀
  e := e₀
  hmul_e_e := sphereFrameMul_base_left hF hli e₀ e₀
  eHmul := (ContinuousMap.HomotopyRel.refl _ _).cast rfl
    (ContinuousMap.ext fun y ↦ sphereFrameMul_base_left hF hli e₀ y)
  hmulE := (ContinuousMap.HomotopyRel.refl _ _).cast rfl
    (ContinuousMap.ext fun x ↦ sphereFrameMul_base_right hF hli hF₀ e₀ x)

/-- **A tangent frame on a sphere gives a multiplication with strict unit.** If the unit sphere
`Sⁿ` of a real inner product space of dimension `n + 1` carries `n` continuous tangent vector
fields that are linearly independent at every point, then for every point `e₀` there is a
continuous multiplication `μ` of `Sⁿ` with `μ (e₀, y) = y` and `μ (x, e₀) = x`, whose left
translations are restrictions of linear isometries of `E`. -/
theorem exists_sphere_mul_of_tangentFrame
    {w : Fin n → (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
    (hw : ∀ i, Continuous fun x ↦ (⟨x, w i x⟩ : TangentBundle (𝓡 n) (sphere (0 : E) 1)))
    (hwli : ∀ x, LinearIndependent ℝ fun i ↦ w i x) (e₀ : sphere (0 : E) 1) :
    ∃ μ : C(sphere (0 : E) 1 × sphere (0 : E) 1, sphere (0 : E) 1),
      (∀ y, μ (e₀, y) = y) ∧ (∀ x, μ (x, e₀) = x) ∧
        ∀ x, ∃ A : E ≃ₗᵢ[ℝ] E, ∀ y, (μ (x, y) : E) = A y := by
  -- The frame `(x, dι w₁ x, …, dι wₙ x)` of `E`, read through the differential of the inclusion.
  let G : sphere (0 : E) 1 → Fin (n + 1) → E := fun x ↦
    Fin.cons (x : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x (w i x)
  have hG : ∀ i, Continuous fun x ↦ G x i := Fin.cases continuous_subtype_val fun i ↦
    ((contMDiff_coe_sphere (m := 1)).contMDiff_mvfderiv_apply (m := 0) le_rfl).continuous.comp
      (hw i)
  have hGli : ∀ x, LinearIndependent ℝ (G x) := fun x ↦
    (hwli x).finCons_mvfderiv_coe_sphere x
  have hG₀ : ∀ x, G x 0 = x := fun x ↦ Fin.cons_zero _ _
  exact ⟨sphereFrameMul hG hGli e₀, sphereFrameMul_base_left hG hGli e₀,
    sphereFrameMul_base_right hG hGli hG₀ e₀, fun x ↦ ⟨sphereFrameIsometry G e₀ x, fun _ ↦ rfl⟩⟩

end TauCeti
