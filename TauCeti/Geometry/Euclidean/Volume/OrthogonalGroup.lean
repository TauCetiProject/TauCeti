/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.Analysis.Matrix.MeasurableSpace
public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.BlockSucc
public import TauCeti.LinearAlgebra.OrthogonalGroup
public import TauCeti.Topology.Algebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# The volume of the orthogonal group

The orthogonal group `O(n + 1)` fibres over the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` by the orbit map
`g ↦ g eₙ` of the last basis vector, and the fibre through `g` is the coset `g · O(n)` of the
stabilizer `O(n)`, embedded by `TauCeti.orthogonalBlockSucc`. This file builds the measure on
`O(n)` determined by the Euclidean surface measure of the spheres along this fibration, and
computes its total mass:

  `vol(O(n)) = ∏_{j = 1}^{n} 2 π ^ (j / 2) / Γ(j / 2)`,
  `vol(SO(n)) = ∏_{j = 2}^{n} 2 π ^ (j / 2) / Γ(j / 2)`, and `vol(O(n)) = 2 vol(SO(n))` for
  `n ≥ 1`.

The construction is recursive. `O(0)` is the trivial group, with the unit point mass. For the
step, a measurable choice `u ↦ s(u)` of orthogonal matrices with `s(u) eₙ = u` (the reflection
exchanging `eₙ` and `u`) identifies `Sⁿ × O(n)` with `O(n + 1)` through `(u, h) ↦ s(u) h`, and
the measure on `O(n + 1)` is the image of the product of the surface measure of `Sⁿ` with the
measure on `O(n)`. The main theorem is that this measure is **left invariant**, so that it is a
Haar measure of the compact group `O(n)`: a left translate `g s(u) h` equals `s(g u) h' h` with
`h' ∈ O(n)` depending only on `g` and `u`, so left translation acts on `Sⁿ × O(n)` as a skew
product of a rotation of the sphere, which preserves the surface measure, with left translations
of `O(n)`, which preserve the measure on `O(n)` by induction. As a Haar measure is determined by
its total mass, which here is the product of the areas of the spheres, the measure does not depend
on the chosen section.

Its normalization is the Euclidean one: the image of the measure under the orbit map is
`vol(O(n))` times the surface measure of `Sⁿ`, so the fibres of `O(n + 1) → Sⁿ` carry the
volume of `O(n)` and the base carries the Euclidean area of the sphere. This is the normalization
of the Riemannian volume of the bi-invariant metric `⟨X, Y⟩ = ½ tr (Xᵀ Y)`, for which the orbit
map is a Riemannian submersion; that comparison is not formalized here.

Finally, the volume is put in the form in which it enters the Minkowski–Siegel mass formula,

  `2 π ^ (-n (n + 1) / 4) ∏_{j = 1}^{n} Γ(j / 2) = 2 ^ (n + 1) / vol(O(n))`.

## Main definitions

* `TauCeti.orthogonalGroupLastColumn`: the orbit map `O(n + 1) → Sⁿ`, `g ↦ g eₙ`.
* `TauCeti.orthogonalGroupMeasure`: the Euclidean Haar measure on the matrix group `O(n)`.
* `TauCeti.orthogonalGroupVolume`, `TauCeti.specialOrthogonalGroupVolume`: the volumes of `O(n)`
  and of `SO(n)` for this measure.

## Main results

* `TauCeti.instIsMulLeftInvariantOrthogonalGroupMeasure` and
  `TauCeti.instIsHaarMeasureOrthogonalGroupMeasure`: the measure is a Haar measure.
* `TauCeti.orthogonalGroupLastColumn_surjective` and `TauCeti.orthogonalGroupLastColumn_eq_iff`:
  the orbit map is onto the sphere, and its fibres are the cosets of `O(n)`.
* `TauCeti.map_orthogonalGroupLastColumn_orthogonalGroupMeasure`: the fibration
  `O(n + 1) → Sⁿ` pushes the measure forward to `vol(O(n))` times the surface measure.
* `TauCeti.orthogonalGroupVolume_eq_prod` and `TauCeti.specialOrthogonalGroupVolume_eq_prod`:
  the product formulas for `vol(O(n))` and `vol(SO(n))`.
* `TauCeti.orthogonalGroupVolume_eq_two_mul_specialOrthogonalGroupVolume`:
  `vol(O(n)) = 2 vol(SO(n))` for `n ≥ 1`.
* `TauCeti.two_mul_pi_rpow_mul_prod_Gamma_eq_two_pow_div_orthogonalGroupVolume`: the form of the
  volume that enters the mass formula.

## References

* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), 259–285.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Module Set
open scoped ENNReal

/-! ### The fibration over the sphere -/

/-- The orbit map `O(n + 1) → Sⁿ` of the last standard basis vector `eₙ`: an orthogonal matrix
goes to its last column, a point of the unit sphere of `ℝⁿ⁺¹`. Its fibres are the left cosets of
the stabilizer `O(n)` of `eₙ`, embedded by `TauCeti.orthogonalBlockSucc`. -/
def orthogonalGroupLastColumn (n : ℕ) (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨orthogonalGroupToLinearIsometryEquiv g (EuclideanSpace.single (Fin.last n) 1), by
    rw [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
    simp⟩

/-- The orbit map sends an orthogonal matrix to the image of the last basis vector. -/
@[simp]
theorem coe_orthogonalGroupLastColumn (n : ℕ) (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    (orthogonalGroupLastColumn n g : EuclideanSpace ℝ (Fin (n + 1))) =
      orthogonalGroupToLinearIsometryEquiv g (EuclideanSpace.single (Fin.last n) 1) :=
  (rfl)

/-- The orbit map `O(n + 1) → Sⁿ` is continuous. -/
theorem continuous_orthogonalGroupLastColumn (n : ℕ) :
    Continuous (orthogonalGroupLastColumn n) := by
  refine Continuous.subtype_mk ?_ _
  simp only [orthogonalGroupToLinearIsometryEquiv_apply]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_subtype_val.matrix_mulVec continuous_const)

variable {n : ℕ}

/-- The last standard basis vector, as a point of the unit sphere. -/
private def lastSphere (n : ℕ) : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨EuclideanSpace.single (Fin.last n) 1, by simp⟩

/-- The rotation of the unit sphere by an orthogonal matrix. -/
private def rotateSphere (g : Matrix.orthogonalGroup (Fin n) ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  Subtype.map (orthogonalGroupToLinearIsometryEquiv g) fun x hx ↦ by
    rwa [mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map, ← mem_sphere_zero_iff_norm]

private theorem coe_rotateSphere (g : Matrix.orthogonalGroup (Fin n) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (rotateSphere g u : EuclideanSpace ℝ (Fin n)) = orthogonalGroupToLinearIsometryEquiv g u :=
  (rfl)

/-- Rotations preserve the surface measure of the sphere. -/
private theorem measurePreserving_rotateSphere (g : Matrix.orthogonalGroup (Fin n) ℝ) :
    MeasurePreserving (rotateSphere g) (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  refine ⟨(orthogonalGroupToLinearIsometryEquiv g).continuous.measurable.subtype_map _, ?_⟩
  rw [rotateSphere, LinearIsometryEquiv.map_toSphere,
    (orthogonalGroupToLinearIsometryEquiv g).measurePreserving.map_eq]

/-- The reflection of `ℝⁿ⁺¹` exchanging the last basis vector with a point `u` of the sphere. -/
private def sphereReflection (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (ℝ ∙ ((lastSphere n : EuclideanSpace ℝ (Fin (n + 1))) - u))ᗮ.reflection

private theorem sphereReflection_last (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereReflection u (lastSphere n) = u :=
  Submodule.reflection_sub (by simp)

/-- The section of the orbit map: the matrix of `sphereReflection u`, an orthogonal matrix whose
last column is `u`. -/
private def sphereSection (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  ⟨LinearMap.toMatrix (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis (sphereReflection u).toLinearEquiv,
    (sphereReflection u).toMatrix_mem_unitaryGroup _ _⟩

private theorem orthogonalGroupToLinearIsometryEquiv_sphereSection
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    orthogonalGroupToLinearIsometryEquiv (sphereSection u) = sphereReflection u := by
  ext x i
  have h := congrFun (LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
    ((sphereReflection u).toLinearEquiv : _ →ₗ[ℝ] _) x) i
  have hrepr : ⇑((EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis.repr x) = x.ofLp := by
    ext j
    simp
  rw [hrepr] at h
  simpa [sphereSection] using h

private theorem sphereSection_mul_self (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereSection u * sphereSection u = 1 := by
  apply orthogonalGroupToLinearIsometryEquiv_injective
  ext x : 1
  simp [orthogonalGroupToLinearIsometryEquiv_sphereSection, sphereReflection]

private theorem measurable_sphereSection :
    Measurable fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (sphereSection u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  have hw : Continuous fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (lastSphere n : EuclideanSpace ℝ (Fin (n + 1))) - u :=
    continuous_const.sub continuous_subtype_val
  have hc : Measurable fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      inner ℝ ((lastSphere n : EuclideanSpace ℝ (Fin (n + 1))) - u)
        (EuclideanSpace.single j (1 : ℝ)) /
        ‖(lastSphere n : EuclideanSpace ℝ (Fin (n + 1))) - u‖ ^ 2 :=
    (hw.inner continuous_const).measurable.div (hw.norm.pow 2).measurable
  have hwi : Measurable fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      ((lastSphere n : EuclideanSpace ℝ (Fin (n + 1))) - u).ofLp i :=
    ((PiLp.continuous_apply 2 _ i).comp hw).measurable
  simp only [sphereSection, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    sphereReflection, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    PiLp.neg_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  fun_prop

private theorem measurable_blockSucc :
    Measurable (Matrix.blockSucc : Matrix (Fin n) (Fin n) ℝ → _) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.measurable_apply]

/-- The trivialization map `Sⁿ × O(n) → O(n + 1)`, `(u, h) ↦ s(u) h`. -/
private def decompose
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Matrix.orthogonalGroup (Fin n) ℝ) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  sphereSection p.1 * orthogonalBlockSucc ℝ n p.2

/-- A map into `O(m)` is measurable once its underlying matrix is. -/
private theorem measurable_of_measurable_coe {α : Type*} [MeasurableSpace α] {m : ℕ}
    {f : α → Matrix.orthogonalGroup (Fin m) ℝ}
    (hf : Measurable fun x ↦ (f x : Matrix (Fin m) (Fin m) ℝ)) : Measurable f :=
  hf.subtype_mk (h := fun x ↦ (f x).2)

private theorem coe_decompose
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Matrix.orthogonalGroup (Fin n) ℝ) :
    (decompose p : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) =
      sphereSection p.1 * Matrix.blockSucc (p.2 : Matrix (Fin n) (Fin n) ℝ) := by
  rw [decompose, Submonoid.coe_mul, coe_orthogonalBlockSucc]

private theorem measurable_decompose : Measurable (decompose (n := n)) := by
  refine measurable_of_measurable_coe ?_
  simp only [coe_decompose]
  exact (measurable_sphereSection.comp measurable_fst).mul
    (measurable_blockSucc.comp (measurable_subtype_coe.comp measurable_snd))

/-- An orthogonal matrix fixes the last basis vector of Euclidean space exactly when it fixes the
last coordinate vector. -/
private theorem orthogonalGroupToLinearIsometryEquiv_single_last_eq_iff
    (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    orthogonalGroupToLinearIsometryEquiv g (EuclideanSpace.single (Fin.last n) 1) =
        EuclideanSpace.single (Fin.last n) 1 ↔
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).mulVec (Pi.single (Fin.last n) 1) =
        Pi.single (Fin.last n) 1 := by
  rw [orthogonalGroupToLinearIsometryEquiv_apply, ← (WithLp.ofLp_injective 2).eq_iff]
  simp

private theorem orthogonalGroupLastColumn_decompose
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Matrix.orthogonalGroup (Fin n) ℝ) :
    orthogonalGroupLastColumn n (decompose p) = p.1 := by
  have hfix := (orthogonalGroupToLinearIsometryEquiv_single_last_eq_iff _).2
    ((exists_orthogonalBlockSucc_eq_iff_mulVec_single ℝ n _).1 ⟨p.2, rfl⟩)
  apply Subtype.ext
  rw [coe_orthogonalGroupLastColumn, decompose, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply, hfix, orthogonalGroupToLinearIsometryEquiv_sphereSection]
  exact sphereReflection_last p.1

/-- The orbit map `O(n + 1) → Sⁿ` is surjective: `O(n + 1)` acts transitively on the unit
sphere. -/
theorem orthogonalGroupLastColumn_surjective (n : ℕ) :
    Function.Surjective (orthogonalGroupLastColumn n) :=
  fun u ↦ ⟨decompose (u, 1), orthogonalGroupLastColumn_decompose (u, 1)⟩

/-- **The fibres of the orbit map are the cosets of `O(n)`.** Two orthogonal matrices have the same
last column exactly when they differ on the right by an element of the stabilizer `O(n)` of the
last basis vector, embedded by `TauCeti.orthogonalBlockSucc`. -/
theorem orthogonalGroupLastColumn_eq_iff {g g' : Matrix.orthogonalGroup (Fin (n + 1)) ℝ} :
    orthogonalGroupLastColumn n g = orthogonalGroupLastColumn n g' ↔
      ∃ h, g * orthogonalBlockSucc ℝ n h = g' := by
  simp_rw [← eq_inv_mul_iff_mul_eq]
  rw [exists_orthogonalBlockSucc_eq_iff_mulVec_single,
    ← orthogonalGroupToLinearIsometryEquiv_single_last_eq_iff, map_mul, map_inv,
    LinearIsometryEquiv.coe_mul, Function.comp_apply, LinearIsometryEquiv.coe_inv,
    LinearIsometryEquiv.symm_apply_eq, Subtype.ext_iff, coe_orthogonalGroupLastColumn,
    coe_orthogonalGroupLastColumn, eq_comm]

/-- The element `s(g u) g s(u)` of `O(n + 1)`, which fixes the last basis vector. -/
private def fibreShift (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  sphereSection (rotateSphere g u) * g * sphereSection u

private theorem exists_orthogonalBlockSucc_eq_fibreShift
    (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ∃ h, orthogonalBlockSucc ℝ n h = fibreShift g u := by
  refine (exists_orthogonalBlockSucc_eq_iff_mulVec_single ℝ n _).2 ?_
  rw [← orthogonalGroupToLinearIsometryEquiv_single_last_eq_iff, fibreShift, map_mul, map_mul,
    LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply,
    Function.comp_apply, orthogonalGroupToLinearIsometryEquiv_sphereSection]
  have hlast := sphereReflection_last u
  have hrot := sphereReflection_last (rotateSphere g u)
  simp only [lastSphere] at hlast hrot
  rw [orthogonalGroupToLinearIsometryEquiv_sphereSection, hlast, ← coe_rotateSphere, ← hrot,
    sphereReflection, Submodule.reflection_reflection]

private theorem submatrix_coe_orthogonalBlockSucc (h : Matrix.orthogonalGroup (Fin n) ℝ) :
    (orthogonalBlockSucc ℝ n h : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix Fin.castSucc
      Fin.castSucc = h := by
  ext i j
  simp

/-- The element of `O(n)` by which left translation by `g` moves the fibre coordinate over `u`:
the upper-left block of `fibreShift g u`. -/
private def fibreCorner (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨(fibreShift g u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix Fin.castSucc Fin.castSucc, by
    obtain ⟨h, hh⟩ := exists_orthogonalBlockSucc_eq_fibreShift g u
    rw [← hh, submatrix_coe_orthogonalBlockSucc]
    exact h.2⟩

private theorem coe_fibreCorner (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    (fibreCorner g u : Matrix (Fin n) (Fin n) ℝ) =
      (fibreShift g u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix Fin.castSucc
        Fin.castSucc :=
  (rfl)

private theorem orthogonalBlockSucc_fibreCorner (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    orthogonalBlockSucc ℝ n (fibreCorner g u) = fibreShift g u := by
  obtain ⟨h, hh⟩ := exists_orthogonalBlockSucc_eq_fibreShift g u
  have : fibreCorner g u = h :=
    Subtype.ext (by rw [coe_fibreCorner, ← hh, submatrix_coe_orthogonalBlockSucc])
  rw [this, hh]

private theorem measurable_fibreCorner_mul (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ) :
    Measurable fun p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ×
        Matrix.orthogonalGroup (Fin n) ℝ ↦ fibreCorner g p.1 * p.2 := by
  have hshift : Measurable fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (fibreShift g u : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) := by
    simp only [fibreShift, Submonoid.coe_mul]
    exact ((measurable_sphereSection.comp
      ((orthogonalGroupToLinearIsometryEquiv g).continuous.measurable.subtype_map _)).mul
      measurable_const).mul measurable_sphereSection
  have hcorner : Measurable fun u : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ↦
      (fibreCorner g u : Matrix (Fin n) (Fin n) ℝ) := by
    simp only [coe_fibreCorner]
    exact Measurable.of_eval_matrix _ fun i j ↦ hshift.eval_matrix
  refine measurable_of_measurable_coe ?_
  simp only [Submonoid.coe_mul]
  exact (hcorner.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)

/-- Left translation by `g` acts on the trivialization as the skew product
`(u, h) ↦ (g u, fibreCorner g u * h)`. -/
private theorem mul_decompose (g : Matrix.orthogonalGroup (Fin (n + 1)) ℝ)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × Matrix.orthogonalGroup (Fin n) ℝ) :
    g * decompose p = decompose (rotateSphere g p.1, fibreCorner g p.1 * p.2) := by
  simp only [decompose, map_mul, orthogonalBlockSucc_fibreCorner, fibreShift, mul_assoc]
  rw [← mul_assoc (sphereSection _), sphereSection_mul_self, one_mul]

/-! ### The measure -/

/-- **The Euclidean Haar measure on the orthogonal group** `O(n)` of `n × n` real matrices.

`O(0)` is the trivial group and carries the unit point mass. The measure on `O(n + 1)` is the
image of the product of the surface measure of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` with the measure on
`O(n)` under a measurable trivialization `Sⁿ × O(n) → O(n + 1)` of the orbit map
`TauCeti.orthogonalGroupLastColumn`. It is left invariant
(`TauCeti.instIsMulLeftInvariantOrthogonalGroupMeasure`), hence a Haar measure, and the orbit map
pushes it forward to `vol(O(n))` times the surface measure
(`TauCeti.map_orthogonalGroupLastColumn_orthogonalGroupMeasure`). -/
def orthogonalGroupMeasure : (n : ℕ) → Measure (Matrix.orthogonalGroup (Fin n) ℝ)
  | 0 => Measure.dirac 1
  | n + 1 => (((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere).prod
      (orthogonalGroupMeasure n)).map decompose

/-- The measure on the trivial group `O(0)` is the unit point mass. -/
@[simp]
theorem orthogonalGroupMeasure_zero : orthogonalGroupMeasure 0 = Measure.dirac 1 :=
  (rfl)

private theorem orthogonalGroupMeasure_succ (n : ℕ) :
    orthogonalGroupMeasure (n + 1) =
      (((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere).prod
        (orthogonalGroupMeasure n)).map decompose :=
  (rfl)

instance instIsFiniteMeasureOrthogonalGroupMeasure (n : ℕ) :
    IsFiniteMeasure (orthogonalGroupMeasure n) := by
  induction n with
  | zero => rw [orthogonalGroupMeasure_zero]; infer_instance
  | succ n ih => rw [orthogonalGroupMeasure_succ]; infer_instance

/-- **The Euclidean measure on `O(n)` is left invariant.** A left translation acts on the
trivialization `Sⁿ × O(n) ≃ O(n + 1)` as a skew product of a rotation of the sphere, which
preserves the surface measure, with left translations of `O(n)`, which preserve the measure on
`O(n)` by induction. -/
instance instIsMulLeftInvariantOrthogonalGroupMeasure (n : ℕ) :
    (orthogonalGroupMeasure n).IsMulLeftInvariant := by
  induction n with
  | zero =>
    refine ⟨fun g ↦ ?_⟩
    rw [Subsingleton.elim g 1]
    simp only [one_mul]
    exact Measure.map_id
  | succ n ih =>
    refine ⟨fun g ↦ ?_⟩
    have hT := (measurePreserving_rotateSphere g).skew_product
      (g := fun u h ↦ fibreCorner g u * h) (measurable_fibreCorner_mul g)
      (Filter.Eventually.of_forall fun u ↦ map_mul_left_eq_self
        (orthogonalGroupMeasure n) (fibreCorner g u))
    have hcomp : (fun x ↦ g * x) ∘ decompose = decompose ∘
        fun p ↦ (rotateSphere g p.1, fibreCorner g p.1 * p.2) :=
      funext (mul_decompose g)
    rw [orthogonalGroupMeasure_succ, Measure.map_map (by fun_prop : Measurable (g * ·))
      measurable_decompose, hcomp, ← Measure.map_map measurable_decompose hT.measurable,
      hT.map_eq]

/-- **The fibration `O(n + 1) → Sⁿ`.** The orbit map `g ↦ g eₙ` pushes the Euclidean measure on
`O(n + 1)` forward to `vol(O(n))` times the surface measure of the unit sphere: the base of the
fibration carries the Euclidean area of `Sⁿ`, and each fibre the volume of `O(n)`. -/
theorem map_orthogonalGroupLastColumn_orthogonalGroupMeasure (n : ℕ) :
    (orthogonalGroupMeasure (n + 1)).map (orthogonalGroupLastColumn n) =
      orthogonalGroupMeasure n univ •
        (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere := by
  rw [orthogonalGroupMeasure_succ,
    Measure.map_map (continuous_orthogonalGroupLastColumn n).measurable measurable_decompose]
  have : orthogonalGroupLastColumn n ∘ decompose = Prod.fst :=
    funext orthogonalGroupLastColumn_decompose
  rw [this, Measure.map_fst_prod]

/-- The total mass of the Euclidean measure on `O(n + 1)` is the area of `Sⁿ` times the total
mass on `O(n)`. -/
theorem orthogonalGroupMeasure_univ_succ (n : ℕ) :
    orthogonalGroupMeasure (n + 1) univ =
      (volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).toSphere univ *
        orthogonalGroupMeasure n univ := by
  have h := congrArg (fun μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ↦ μ univ)
    (map_orthogonalGroupLastColumn_orthogonalGroupMeasure n)
  simp only [Measure.map_apply (continuous_orthogonalGroupLastColumn n).measurable
    MeasurableSet.univ, preimage_univ, Measure.smul_apply, smul_eq_mul] at h
  rw [h, mul_comm]

/-! ### The volumes of `O(n)` and `SO(n)` -/

/-- The volume `vol(O(n))` of the orthogonal group for its Euclidean measure
`TauCeti.orthogonalGroupMeasure`. -/
def orthogonalGroupVolume (n : ℕ) : ℝ :=
  (orthogonalGroupMeasure n).real univ

/-- The volume `vol(SO(n))` of the special orthogonal group, the subgroup of determinant one,
for the Euclidean measure `TauCeti.orthogonalGroupMeasure` of `O(n)`. -/
def specialOrthogonalGroupVolume (n : ℕ) : ℝ :=
  (orthogonalGroupMeasure n).real {g | (g : Matrix (Fin n) (Fin n) ℝ).det = 1}

/-- **The volume of the orthogonal group**:
`vol(O(n)) = ∏_{j = 1}^{n} 2 π ^ (j / 2) / Γ(j / 2)`, the product of the areas of the spheres
`S⁰, S¹, …, Sⁿ⁻¹` along the tower of fibrations `O(j) → Sʲ⁻¹`. -/
theorem orthogonalGroupVolume_eq_prod (n : ℕ) :
    orthogonalGroupVolume n =
      ∏ j ∈ Finset.Icc 1 n, 2 * Real.pi ^ ((j : ℝ) / 2) / Real.Gamma ((j : ℝ) / 2) := by
  induction n with
  | zero => simp [orthogonalGroupVolume]
  | succ n ih =>
    rw [orthogonalGroupVolume, measureReal_def] at ih ⊢
    rw [orthogonalGroupMeasure_univ_succ, ENNReal.toReal_mul, ih,
      Finset.prod_Icc_succ_top (by omega), mul_comm, toSphere_volume_apply_univ,
      finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (by positivity)]

/-- The orthogonal group has positive volume. -/
theorem orthogonalGroupVolume_pos (n : ℕ) : 0 < orthogonalGroupVolume n := by
  rw [orthogonalGroupVolume_eq_prod]
  exact Finset.prod_pos fun j hj ↦ by
    have : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.1 hj).1
    positivity

/-- **The Euclidean measure on `O(n)` is a Haar measure.** It is finite and left invariant, and
it is positive on nonempty open sets because the compact group `O(n)` has positive measure. -/
instance instIsHaarMeasureOrthogonalGroupMeasure (n : ℕ) :
    (orthogonalGroupMeasure n).IsHaarMeasure where
  toIsOpenPosMeasure := isOpenPosMeasure_of_mulLeftInvariant_of_compact univ isCompact_univ
    fun h ↦ (orthogonalGroupVolume_pos n).ne' (by rw [orthogonalGroupVolume, measureReal_def, h,
      ENNReal.toReal_zero])

/-- The determinant of a real orthogonal matrix is `1` or `-1`. -/
private theorem det_eq_one_or_eq_neg_one (g : Matrix.orthogonalGroup (Fin n) ℝ) :
    (g : Matrix (Fin n) (Fin n) ℝ).det = 1 ∨ (g : Matrix (Fin n) (Fin n) ℝ).det = -1 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 g.2)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

/-- The diagonal reflection `diag(-1, 1, …, 1)`, an orthogonal matrix of determinant `-1`. -/
private def diagonalReflection (n : ℕ) : Matrix.orthogonalGroup (Fin (n + 1)) ℝ :=
  ⟨Matrix.diagonal (Function.update 1 0 (-1)), by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = 0 <;> simp [hi]⟩

private theorem det_diagonalReflection (n : ℕ) :
    ((diagonalReflection n : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)).det = -1 := by
  rw [diagonalReflection, Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ 0)]
  simp

/-- **`vol(O(n)) = 2 vol(SO(n))`** for `n ≥ 1`: left translation by a reflection exchanges the
two cosets of `SO(n)` and preserves the Haar measure. For `n = 0` both groups are trivial and
both volumes are `1`. -/
theorem orthogonalGroupVolume_eq_two_mul_specialOrthogonalGroupVolume {n : ℕ} (hn : 1 ≤ n) :
    orthogonalGroupVolume n = 2 * specialOrthogonalGroupVolume n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  set S : Set (Matrix.orthogonalGroup (Fin (m + 1)) ℝ) :=
    {g | (g : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ).det = 1}
  have hS : MeasurableSet S := measurableSet_eq_fun
    ((Continuous.matrix_det continuous_subtype_val).measurable) measurable_const
  -- Left translation by the reflection carries `SO(m + 1)` onto its complement.
  have hpre : (fun g ↦ diagonalReflection m * g) ⁻¹' S = Sᶜ := by
    ext g
    simp only [S, mem_preimage, mem_compl_iff, Set.mem_ofPred_eq, Submonoid.coe_mul,
      Matrix.det_mul, det_diagonalReflection, neg_one_mul, neg_eq_iff_eq_neg]
    rcases det_eq_one_or_eq_neg_one g with h | h <;> rw [h] <;> norm_num
  have hcompl : orthogonalGroupMeasure (m + 1) Sᶜ = orthogonalGroupMeasure (m + 1) S := by
    rw [← hpre, measure_preimage_mul]
  rw [orthogonalGroupVolume, specialOrthogonalGroupVolume, measureReal_def, measureReal_def,
    ← measure_add_measure_compl hS, hcompl, ← two_mul, ENNReal.toReal_mul, ENNReal.toReal_ofNat]

/-- **The volume of the special orthogonal group**:
`vol(SO(n)) = ∏_{j = 2}^{n} 2 π ^ (j / 2) / Γ(j / 2)`. The factor `j = 1` of the product for
`vol(O(n))` is the area `2` of the zero-sphere `S⁰ = {±1}`, the index of `SO(n)` in `O(n)`. -/
theorem specialOrthogonalGroupVolume_eq_prod (n : ℕ) :
    specialOrthogonalGroupVolume n =
      ∏ j ∈ Finset.Icc 2 n, 2 * Real.pi ^ ((j : ℝ) / 2) / Real.Gamma ((j : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [specialOrthogonalGroupVolume]
  have h := orthogonalGroupVolume_eq_two_mul_specialOrthogonalGroupVolume hn
  rw [orthogonalGroupVolume_eq_prod, Finset.Icc_eq_cons_Ioc hn, Finset.prod_cons,
    ← Finset.Icc_add_one_left_eq_Ioc, Nat.cast_one, Real.Gamma_one_half_eq,
    ← Real.sqrt_eq_rpow, mul_div_assoc, div_self (Real.sqrt_pos.2 Real.pi_pos).ne', mul_one,
    one_add_one_eq_two] at h
  exact (mul_left_cancel₀ two_ne_zero h).symm

/-- **The archimedean factor of the mass formula**:
`2 π ^ (-n (n + 1) / 4) ∏_{j = 1}^{n} Γ(j / 2) = 2 ^ (n + 1) / vol(O(n))`. -/
theorem two_mul_pi_rpow_mul_prod_Gamma_eq_two_pow_div_orthogonalGroupVolume (n : ℕ) :
    2 * Real.pi ^ (-((n : ℝ) * (n + 1) / 4)) * ∏ j ∈ Finset.Icc 1 n, Real.Gamma ((j : ℝ) / 2) =
      2 ^ (n + 1) / orthogonalGroupVolume n := by
  rw [eq_div_iff (orthogonalGroupVolume_pos n).ne', orthogonalGroupVolume_eq_prod]
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hΓ : 0 < Real.Gamma (((n + 1 : ℕ) : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
    have hπ : 0 < Real.pi ^ (((n + 1 : ℕ) : ℝ) / 2) := by positivity
    rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega)]
    have hexp : -(((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) + 1) / 4) =
        -((n : ℝ) * (n + 1) / 4) - ((n + 1 : ℕ) : ℝ) / 2 := by
      push_cast
      ring
    rw [hexp, Real.rpow_sub Real.pi_pos, pow_succ, ← ih]
    field_simp

end TauCeti
