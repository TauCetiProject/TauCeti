/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
public import TauCeti.RepresentationTheory.SU2.Adjoint
public import TauCeti.Topology.Compactification.OnePoint.Antipode
import Mathlib.LinearAlgebra.Matrix.Action
import TauCeti.Algebra.Ring.Idempotent
import TauCeti.Algebra.Star.SelfAdjoint
import TauCeti.Analysis.InnerProductSpace.PiL2
import TauCeti.Geometry.Manifold.Instances.OnePoint.Projectivization
import TauCeti.Geometry.RealAlgebraic.HermitianProjectorEmbedding
import TauCeti.LinearAlgebra.Matrix.Trace.Basic

/-!
# The Riemann sphere as the round sphere of `ℝ³`

A point `x` of the Riemann sphere `OnePoint ℂ` is a complex line in `ℂ²`
(`OnePoint.equivProjectivization`). Its orthogonal projector `P`
(`Projectivization.hermitianProjector`) is a Hermitian matrix of trace one with `P² = P`, so
`2 P - 1` is a traceless Hermitian matrix with square `1`. Its coordinates in the Pauli basis
(`TauCeti.pauliCoord`) form the vector `OnePoint.sphereCoords x` of `ℝ³`, a unit vector because
the Pauli map turns the trace form into twice the dot product (`TauCeti.trace_pauli_mul_pauli`).
Equivalently, `√2 (P - 1 / 2)` is a unit vector for the real inner product `Re tr (A* B)` on
traceless Hermitian matrices, read in the orthonormal basis `σᵢ / √2`.

Explicitly, `∞` goes to the north pole `(0, 0, 1)`, `0` to the south pole `(0, 0, -1)`, and a
finite point `z` to `(2 Re z, -2 Im z, |z|² - 1) / (1 + |z|²)`
(`OnePoint.sphereCoords_coe`). This is the inverse of the stereographic projection from the north
pole, followed by the reflection `(a, b, c) ↦ (a, -b, c)`. The antipodal map
`z ↦ -1 / conj z` of the Riemann sphere becomes `v ↦ -v` (`OnePoint.sphereCoords_antipode`),
since it sends a line to its orthogonal complement.

The construction is invariant: a unitary matrix `U` moves the line by the Möbius transformation of
`U` and conjugates its projector by `U`, so `sphereCoords` intertwines the Möbius action of
`U(2)` with the rotations `TauCeti.pauliRotation U`
(`Matrix.UnitaryGroup.sphereCoords_toUnits_smul`), and the action of `SU(2)` through `PSL(2, ℂ)`
with the double cover `TauCeti.SU2.toSO3`
(`Matrix.specialUnitaryGroup.sphereCoords_toPSL_smul`). Conversely, a Möbius transformation that
acts on the round sphere by any linear map commutes with `v ↦ -v`, hence with the antipodal map,
so it lies in `PSU(2)`
(`Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_exists_sphereCoords_smul`).
Thus `PSU(2)` is the group of Möbius transformations acting on the round sphere by rotations.

Since the Hermitian projector map is continuous and injective, and every traceless Hermitian
involution `A` is `2 P - 1` for the projector `P = (1 + A) / 2`, the map `sphereCoords` is a
continuous bijection from the compact space `OnePoint ℂ` onto the unit sphere, hence a
homeomorphism `OnePoint.homeomorphSphere` onto the unit sphere of `EuclideanSpace ℝ (Fin 3)`.

## Main definitions

* `OnePoint.sphereCoords`: the Pauli coordinates of `2 P - 1`, for `P` the orthogonal projector of
  the line `x`.
* `OnePoint.homeomorphSphere`: the homeomorphism from the Riemann sphere onto the unit sphere of
  `ℝ³` given by `sphereCoords`.

## Main results

* `OnePoint.pauli_sphereCoords`: the Pauli matrix of `sphereCoords x` is `2 P - 1`.
* `OnePoint.dotProduct_sphereCoords_self` and `OnePoint.range_sphereCoords`: the image of
  `sphereCoords` is exactly the unit sphere.
* `OnePoint.sphereCoords_injective` and `OnePoint.continuous_sphereCoords`.
* `OnePoint.sphereCoords_infty` and `OnePoint.sphereCoords_coe`: the explicit formula.
* `OnePoint.sphereCoords_antipode`: the antipodal map becomes `v ↦ -v`.
* `Matrix.UnitaryGroup.sphereCoords_toUnits_smul` and
  `Matrix.specialUnitaryGroup.sphereCoords_toPSL_smul`: equivariance for `U(2) → SO(3)` and for
  the double cover `SU(2) → SO(3)`.
* `Matrix.ProjectiveSpecialLinearGroup.mem_range_toPSL_iff_exists_sphereCoords_smul`: the Möbius
  transformations acting on the round sphere by a linear map are exactly those of `PSU(2)`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91, Springer,
  1983, Chapters 3 and 4 (stereographic projection, and complex Möbius transformations with the
  unitary subgroup acting by rotations).
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Springer, 1991, §7.3 (the double cover `SU(2) → SO(3)` through the Pauli matrices).
-/

public section

open Matrix Complex TauCeti Projectivization
open scoped MatrixGroups

namespace OnePoint

/-- The point of the unit sphere of `ℝ³` attached to a point `x` of the Riemann sphere: the Pauli
coordinates of `2 P - 1`, where `P` is the orthogonal projector onto the complex line
`equivProjectivization ℂ x` of `ℂ²`. It sends `∞` to `(0, 0, 1)` and a finite point `z` to
`(2 Re z, -2 Im z, |z|² - 1) / (1 + |z|²)` (`OnePoint.sphereCoords_coe`). -/
noncomputable def sphereCoords (x : OnePoint ℂ) : Fin 3 → ℝ :=
  pauliCoord (2 * hermitianProjector (equivProjectivization ℂ x) - 1)

theorem sphereCoords_def (x : OnePoint ℂ) :
    sphereCoords x = pauliCoord (2 * hermitianProjector (equivProjectivization ℂ x) - 1) :=
  (rfl)

/-- The Pauli matrix of `sphereCoords x` is `2 P - 1`, for `P` the orthogonal projector onto the
line `x`. -/
theorem pauli_sphereCoords (x : OnePoint ℂ) :
    pauli (sphereCoords x) = 2 * hermitianProjector (equivProjectivization ℂ x) - 1 := by
  have hP := hermitianProjector_mem_hermitianProjectorLocus (equivProjectivization ℂ x)
  have h2 := trace_two_mul_sub_one (hermitianProjector (equivProjectivization ℂ x))
  rw [(mem_hermitianProjectorLocus.mp hP).2, Fintype.card_fin, mul_one, Nat.cast_ofNat,
    sub_self] at h2
  exact pauli_pauliCoord (isHermitian_iff_isSelfAdjoint.mpr
    (mem_hermitianProjectorLocus.mp hP).1.isSelfAdjoint.two_mul_sub_one) h2

/-- `sphereCoords x` is a unit vector. -/
@[simp]
theorem dotProduct_sphereCoords_self (x : OnePoint ℂ) :
    sphereCoords x ⬝ᵥ sphereCoords x = 1 := by
  have hP := hermitianProjector_mem_hermitianProjectorLocus (equivProjectivization ℂ x)
  have h3 := (mem_hermitianProjectorLocus.mp hP).1.isIdempotentElem.two_mul_sub_one_mul_self
  have h := trace_pauli_mul_pauli (sphereCoords x) (sphereCoords x)
  rw [pauli_sphereCoords, h3, trace_one, Fintype.card_fin] at h
  exact_mod_cast (mul_left_cancel₀ two_ne_zero (h.symm.trans (mul_one 2).symm) :)

/-- Distinct points of the Riemann sphere go to distinct points of the round sphere. -/
theorem sphereCoords_injective : Function.Injective sphereCoords := by
  intro x y h
  have h' := congrArg pauli h
  rw [pauli_sphereCoords, pauli_sphereCoords, sub_left_inj] at h'
  refine (equivProjectivization ℂ).injective (hermitianProjector_injective ?_)
  refine smul_right_injective _ (two_ne_zero (α := ℂ)) ?_
  simpa only [two_smul, two_mul] using h'

/-- `sphereCoords` is continuous. -/
theorem continuous_sphereCoords : Continuous sphereCoords := by
  have hc : Continuous (equivProjectivization ℂ) := by
    simpa using (diffeomorphProjectivization ℂ 0).continuous
  exact (LinearMap.continuous_of_finiteDimensional pauliCoord).comp
    ((continuous_const.mul (continuous_hermitianProjector.comp hc)).sub continuous_const)

/-- `∞` goes to the north pole. -/
@[simp]
theorem sphereCoords_infty : sphereCoords ∞ = ![0, 0, 1] := by
  ext i
  fin_cases i <;> simp [sphereCoords_def, pauliCoord_apply, two_mul,
    rankOneHermitianProjector_apply, dotProduct, Fin.sum_univ_two]

/-- A finite point `z` goes to `(2 Re z, -2 Im z, |z|² - 1) / (1 + |z|²)`. -/
theorem sphereCoords_coe (z : ℂ) :
    sphereCoords z = (1 + normSq z)⁻¹ • ![2 * z.re, -(2 * z.im), normSq z - 1] := by
  have h : (1 + normSq z : ℝ) ≠ 0 := by linarith [normSq_nonneg z]
  have hs : (star ![z, 1] ⬝ᵥ ![z, 1] : ℂ) = ((1 + normSq z : ℝ) : ℂ) := by
    simp [dotProduct, Fin.sum_univ_two, mul_comm, normSq_eq_conj_mul_self, add_comm]
  have hP (i j : Fin 2) : rankOneHermitianProjector ![z, 1] i j =
      ![z, 1] i * star (![z, 1] j) * (((1 + normSq z)⁻¹ : ℝ) : ℂ) := by
    rw [rankOneHermitianProjector_apply, hs, div_eq_mul_inv, ofReal_inv]
  have hn : normSq (1 + (normSq z : ℂ)) = (1 + normSq z) ^ 2 := by
    rw [← ofReal_one, ← ofReal_add, normSq_ofReal, sq]
  ext i
  fin_cases i <;> simp [sphereCoords_def, pauliCoord_apply, two_mul, hP, mul_conj] <;>
    simp only [hn]
  · field_simp
  · field_simp
  · field_simp
    ring

/-- `0` goes to the south pole. -/
@[simp]
theorem sphereCoords_zero : sphereCoords ((0 : ℂ) : OnePoint ℂ) = ![0, 0, -1] := by
  rw [sphereCoords_coe]
  ext i
  fin_cases i <;> simp

/-- The antipodal map `z ↦ -1 / conj z` of the Riemann sphere is the antipodal map `v ↦ -v` of the
round sphere. -/
@[simp]
theorem sphereCoords_antipode (x : OnePoint ℂ) : sphereCoords (antipode x) = -sphereCoords x := by
  induction x using OnePoint.rec with
  | infty => ext i; fin_cases i <;> simp
  | coe z =>
    rcases eq_or_ne z 0 with rfl | hz
    · ext i; fin_cases i <;> simp
    have hn : normSq z ≠ 0 := normSq_eq_zero.not.mpr hz
    rw [antipode_coe hz, sphereCoords_coe, sphereCoords_coe]
    ext i
    fin_cases i <;> simp [map_inv₀, inv_re, inv_im] <;> field_simp <;> ring

/-- Every unit vector `v` of `ℝ³` is a value of `sphereCoords`: the matrix `A = pauli v` satisfies
`A² = 1`, so `(1 + A) / 2` is the orthogonal projector onto a line `x`, and
`sphereCoords x = v`. -/
private theorem mem_range_sphereCoords {v : Fin 3 → ℝ} (hv : v ⬝ᵥ v = 1) :
    v ∈ Set.range sphereCoords := by
  set A := pauli v
  have hA : A * A = 1 := by simp [A, pauli_mul_self, hv]
  have hsq : (1 + A) * (1 + A) = (2 : ℂ) • (1 + A) := by
    rw [add_mul, mul_add, mul_add, hA, two_smul]
    simp only [one_mul, mul_one]
    abel
  have hP : (2⁻¹ : ℂ) • (1 + A) ∈ hermitianProjectorLocus (Fin 2) ℂ := by
    refine mem_hermitianProjectorLocus.mpr ⟨⟨?_, ?_⟩, ?_⟩
    · rw [IsIdempotentElem, smul_mul_smul_comm, hsq, smul_smul]
      norm_num
    · exact IsSelfAdjoint.smul (by simp [isSelfAdjoint_iff]) ((IsSelfAdjoint.one _).add
        (isHermitian_pauli v).isSelfAdjoint)
    · rw [trace_smul, trace_add, trace_one, trace_pauli, Fintype.card_fin]
      norm_num
  obtain ⟨p, hp⟩ := range_hermitianProjector.symm.subset hP
  refine ⟨(equivProjectivization ℂ).symm p, ?_⟩
  rw [sphereCoords_def, Equiv.apply_symm_apply, hp, Matrix.mul_smul, two_mul,
    ← two_smul ℂ (1 + A), smul_smul]
  norm_num [A]

/-- The image of `sphereCoords` is the unit sphere of `ℝ³`. -/
theorem range_sphereCoords : Set.range sphereCoords = {v : Fin 3 → ℝ | v ⬝ᵥ v = 1} :=
  Set.Subset.antisymm (Set.range_subset_iff.mpr dotProduct_sphereCoords_self)
    fun _ hv ↦ mem_range_sphereCoords hv

/-- `sphereCoords`, as a map onto the unit sphere of `EuclideanSpace ℝ (Fin 3)`. -/
private noncomputable def toSphere (x : OnePoint ℂ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨WithLp.toLp 2 (sphereCoords x),
    EuclideanSpace.toLp_mem_sphere_zero_one_iff.mpr (dotProduct_sphereCoords_self x)⟩

private theorem bijective_toSphere : Function.Bijective toSphere := by
  refine ⟨fun x y h ↦ sphereCoords_injective ?_, fun v ↦ ?_⟩
  · simpa [toSphere] using h
  · obtain ⟨x, hx⟩ := mem_range_sphereCoords (EuclideanSpace.toLp_mem_sphere_zero_one_iff.mp v.2)
    exact ⟨x, Subtype.ext (by simp [toSphere, hx])⟩

/-- **The Riemann sphere is the round sphere.** `sphereCoords` is a homeomorphism from `OnePoint ℂ`
onto the unit sphere of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def homeomorphSphere :
    OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective toSphere bijective_toSphere)
    (((PiLp.continuous_toLp 2 _).comp continuous_sphereCoords).subtype_mk _)

@[simp]
theorem coe_homeomorphSphere (x : OnePoint ℂ) :
    (homeomorphSphere x : EuclideanSpace ℝ (Fin 3)) = WithLp.toLp 2 (sphereCoords x) :=
  (rfl)

end OnePoint

open OnePoint

namespace Matrix.UnitaryGroup

/-- **Equivariance for `U(2) → SO(3)`.** The Möbius transformation of a unitary matrix `U` acts on
the round sphere by the rotation `pauliRotation U`. -/
theorem sphereCoords_toUnits_smul (U : unitaryGroup (Fin 2) ℂ) (x : OnePoint ℂ) :
    sphereCoords ((Unitary.toUnits U : GL (Fin 2) ℂ) • x) = pauliRotation U *ᵥ sphereCoords x := by
  refine pauli_injective ?_
  rw [pauli_pauliRotation_mulVec, pauli_sphereCoords, pauli_sphereCoords,
    equivProjectivization_smul, hermitianProjector_unitary_smul]
  have hU := mem_unitaryGroup_iff.mp U.2
  simp only [two_mul, mul_add, add_mul, mul_sub, sub_mul, mul_one, hU, mul_assoc]

end Matrix.UnitaryGroup

namespace Matrix.specialUnitaryGroup

/-- **Equivariance for the double cover `SU(2) → SO(3)`.** An element `g` of `SU(2)` acts on the
Riemann sphere through `PSL(2, ℂ)` and on the round sphere by the rotation `SU2.toSO3 g`, and
`sphereCoords` intertwines the two actions. -/
theorem sphereCoords_toPSL_smul (g : specialUnitaryGroup (Fin 2) ℂ) (x : OnePoint ℂ) :
    sphereCoords (toPSL g • x) = SU2.toSO3 g *ᵥ sphereCoords x := by
  rw [SU2.coe_toSO3, ← UnitaryGroup.sphereCoords_toUnits_smul, toPSL_apply, pslMk_smul]
  congr 2
  ext i j
  simp

end Matrix.specialUnitaryGroup

namespace Matrix.ProjectiveSpecialLinearGroup

/-- **`PSU(2)` is the group of Möbius transformations acting linearly on the round sphere.** A
Möbius transformation `g` lies in `PSU(2)` exactly when it acts on the round sphere by some linear
map of `ℝ³`. -/
theorem mem_range_toPSL_iff_exists_sphereCoords_smul (g : PSL(2, ℂ)) :
    g ∈ (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* _).range ↔
      ∃ R : Matrix (Fin 3) (Fin 3) ℝ, ∀ x, sphereCoords (g • x) = R *ᵥ sphereCoords x := by
  refine ⟨?_, fun ⟨R, hR⟩ ↦ ?_⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, specialUnitaryGroup.sphereCoords_toPSL_smul h⟩
  -- A linear map commutes with `v ↦ -v`, so `g` commutes with the antipodal map.
  refine (mem_range_toPSL_iff_forall_smul_antipode g).mpr fun x ↦ sphereCoords_injective ?_
  rw [hR, sphereCoords_antipode, sphereCoords_antipode, hR, mulVec_neg]

end Matrix.ProjectiveSpecialLinearGroup
