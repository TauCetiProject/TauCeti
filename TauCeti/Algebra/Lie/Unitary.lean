/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RepresentationTheory.Stabilizer
public import TauCeti.Algebra.Lie.Coadjoint
public import TauCeti.Algebra.Lie.SkewAdjoint.Star
public import TauCeti.Algebra.Star.SelfAdjoint
public import TauCeti.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.PosDef
import TauCeti.LinearAlgebra.Complex.Conjugation
import TauCeti.LinearAlgebra.Matrix.Trace.Hermitian

/-!
# The unitary Lie algebra and the coadjoint orbits of `U(n)`

The Lie algebra of the unitary group `U(n) = Matrix.unitaryGroup ι ℂ` is the real Lie algebra
`𝔲(n)` of skew-Hermitian matrices, `Xᴴ = -X` (`TauCeti.unitaryLieAlgebra ι`), the instance for
matrices of the Lie subalgebra of skew-adjoint elements of a star algebra
(`TauCeti.skewAdjoint.lieSubalgebra`). It is a real Lie subalgebra of `Matrix ι ι ℂ`, not a
complex one, and multiplication by `-i` identifies it, as a real vector space, with the Hermitian
matrices (`TauCeti.unitaryLieAlgebraEquivSelfAdjoint`, an instance of
`skewAdjoint.negISMulEquiv`). The group acts on it by conjugation, `Ad_U X = U X Uᴴ`
(`TauCeti.unitaryAdjointRepresentation`), and on its dual by the dual action
`(Ad*_U ν)(X) = ν (Ad_(U⁻¹) X)` (`TauCeti.unitaryCoadjointRepresentation`), as for the coadjoint
representation of a Lie group. This is the matrix model of the Lie-group data: in the algebra
coordinates of the general linear group, the Lie algebra of the unitary subgroup is the
skew-Hermitian matrices
(`TauCeti.Lie.unitsLieAlgebraLieEquiv_symm_mem_lieSubalgebraOfSubgroup_iff_conjTranspose_eq_neg`),
and the tangent adjoint action of a unit is conjugation (`TauCeti.Lie.unitsLieAlgebraEquiv_Ad`).

This file identifies the coadjoint representation with conjugation of Hermitian matrices. The
pairing between a Hermitian matrix `H` and `X ∈ 𝔲(n)`,

`⟨H, X⟩ = -i tr(H X)`,

is real (`TauCeti.ofReal_unitaryTracePairing_apply`): with `X = i K` for a Hermitian `K` it is
`tr(H K)`. It is nondegenerate, since `⟨H, i H⟩ = tr(H²) = tr(Hᴴ H)` vanishes only for `H = 0`, so
it identifies the Hermitian matrices with `𝔲(n)*` (`TauCeti.unitaryTracePairingEquiv`). Through it:

* the coadjoint action is conjugation, `Ad*_U ⟨H, ·⟩ = ⟨U H Uᴴ, ·⟩`
  (`TauCeti.unitaryCoadjointRepresentation_unitaryTracePairing`), so the coadjoint orbit of
  `⟨H, ·⟩` is the unitary conjugacy class of `H`;
* the coadjoint stabilizer of `⟨H, ·⟩` is the commutant of `H` in `U(n)`
  (`TauCeti.mem_stabilizer_unitaryCoadjointRepresentation_unitaryTracePairing_iff`);
* the infinitesimal coadjoint action is the commutator, `⁅ξ, ⟨H, ·⟩⁆ = ⟨ξ H - H ξ, ·⟩`
  (`TauCeti.lie_unitaryTracePairing`), so the stabilizer of `⟨H, ·⟩` in `𝔲(n)` is the commutant of
  `H` in `𝔲(n)` (`TauCeti.mem_lieAnnihilator_unitaryTracePairing_iff`);
* the Kirillov–Kostant–Souriau form of the orbit through `⟨H, ·⟩` is
  `ω([ξ], [η]) = -i tr(H ⁅ξ, η⁆)` (`TauCeti.ofReal_kksForm_unitaryTracePairing_mk`).

These are the coordinates in which the diagonal torus of `U(n)` has the diagonal entries as its
moment map, and in which its moment image is computed by the Schur–Horn theorem, in
`TauCeti.Analysis.Matrix.UnitaryGroup.Kostant`.

## Main definitions

* `TauCeti.unitaryLieAlgebra ι`: the real Lie algebra `𝔲(n)` of skew-Hermitian matrices.
* `TauCeti.unitaryAdjointRepresentation ι`, `TauCeti.unitaryCoadjointRepresentation ι`: the
  adjoint and coadjoint representations of `U(n)`.
* `TauCeti.unitaryTracePairing ι`: the pairing `⟨H, X⟩ = -i tr(H X)` of Hermitian matrices with
  `𝔲(n)`, and `TauCeti.unitaryTracePairingEquiv ι` the identification of the Hermitian matrices
  with `𝔲(n)*` that it induces.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Chapter 1 (coadjoint orbits and the Kirillov–Kostant–Souriau form).
* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. **14** (1982),
  1–15, §1.
-/

public section

noncomputable section

open Matrix Module Complex
open scoped ComplexOrder

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-! ### The unitary Lie algebra -/

/-- The **unitary Lie algebra** `𝔲(n)`: the real Lie subalgebra of `Matrix ι ι ℂ` consisting of the
skew-Hermitian matrices, `Xᴴ = -X`. It is the Lie algebra of the unitary group
`Matrix.unitaryGroup ι ℂ`. -/
def unitaryLieAlgebra : LieSubalgebra ℝ (Matrix ι ι ℂ) :=
  skewAdjoint.lieSubalgebra ℝ (Matrix ι ι ℂ)

variable {ι}

@[simp]
theorem mem_unitaryLieAlgebra_iff {X : Matrix ι ι ℂ} : X ∈ unitaryLieAlgebra ι ↔ Xᴴ = -X :=
  skewAdjoint.mem_lieSubalgebra.trans skewAdjoint.mem_iff

@[simp]
theorem conjTranspose_coe_unitaryLieAlgebra (X : unitaryLieAlgebra ι) :
    (X : Matrix ι ι ℂ)ᴴ = -X :=
  mem_unitaryLieAlgebra_iff.mp X.property

open ComplexConjugate in
/-- The entries of a skew-Hermitian matrix satisfy `X_(b a) = -conj X_(a b)`. -/
theorem coe_unitaryLieAlgebra_apply_swap (X : unitaryLieAlgebra ι) (a b : ι) :
    (X : Matrix ι ι ℂ) b a = -conj ((X : Matrix ι ι ℂ) a b) := by
  have h := congr_fun (congr_fun (conjTranspose_coe_unitaryLieAlgebra X) a) b
  rw [conjTranspose_apply, Matrix.neg_apply] at h
  rw [← map_neg, ← h, star_def, conj_conj]

variable (ι) in
/-- **`𝔲(n)` is `-i` times the Hermitian matrices**: `X ↦ -i X` is a real linear equivalence from
the skew-Hermitian onto the Hermitian matrices, with inverse `K ↦ i K`. -/
def unitaryLieAlgebraEquivSelfAdjoint :
    unitaryLieAlgebra ι ≃ₗ[ℝ] selfAdjoint.submodule ℝ (Matrix ι ι ℂ) :=
  (LinearEquiv.ofEq _ _ (skewAdjoint.toSubmodule_lieSubalgebra ℝ (Matrix ι ι ℂ))).trans
    skewAdjoint.negISMulEquiv

@[simp]
theorem coe_unitaryLieAlgebraEquivSelfAdjoint_apply (X : unitaryLieAlgebra ι) :
    (unitaryLieAlgebraEquivSelfAdjoint ι X : Matrix ι ι ℂ) = -I • (X : Matrix ι ι ℂ) :=
  skewAdjoint.coe_negISMulEquiv_apply
    ⟨(X : Matrix ι ι ℂ), skewAdjoint.mem_lieSubalgebra.mp X.property⟩

@[simp]
theorem coe_unitaryLieAlgebraEquivSelfAdjoint_symm_apply
    (K : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    ((unitaryLieAlgebraEquivSelfAdjoint ι).symm K : Matrix ι ι ℂ) = I • (K : Matrix ι ι ℂ) :=
  skewAdjoint.coe_negISMulEquiv_symm_apply (A := Matrix ι ι ℂ) K

instance : FiniteDimensional ℝ (unitaryLieAlgebra ι) :=
  (unitaryLieAlgebraEquivSelfAdjoint ι).symm.finiteDimensional

variable (ι) in
/-- **`𝔲(n)` has real dimension `n²`**: it is identified with the Hermitian matrices, whose real
dimension is the complex dimension `n²` of all `n × n` matrices. -/
theorem finrank_unitaryLieAlgebra :
    finrank ℝ (unitaryLieAlgebra ι) = Fintype.card ι * Fintype.card ι := by
  rw [(unitaryLieAlgebraEquivSelfAdjoint ι).finrank_eq, finrank_selfAdjoint_submodule,
    finrank_matrix, finrank_self, mul_one]

/-! ### The adjoint and coadjoint representations -/

variable (ι) in
/-- The **adjoint representation** of `U(n)` on `𝔲(n)`, by conjugation `Ad_U X = U X Uᴴ`. -/
def unitaryAdjointRepresentation :
    Representation ℝ (unitaryGroup ι ℂ) (unitaryLieAlgebra ι) where
  toFun U :=
    { toFun X := ⟨U * X * star (U : Matrix ι ι ℂ), skewAdjoint.mem_lieSubalgebra.mpr <|
        skewAdjoint.conjugate (skewAdjoint.mem_lieSubalgebra.mp X.property) _⟩
      map_add' X Y := Subtype.ext (by simp [Matrix.mul_add, Matrix.add_mul])
      map_smul' c X := Subtype.ext (by simp) }
  map_one' := LinearMap.ext fun X => Subtype.ext (by simp)
  map_mul' U V := LinearMap.ext fun X => Subtype.ext (by simp [Matrix.mul_assoc])

@[simp]
theorem coe_unitaryAdjointRepresentation_apply (U : unitaryGroup ι ℂ) (X : unitaryLieAlgebra ι) :
    (unitaryAdjointRepresentation ι U X : Matrix ι ι ℂ) = U * X * star (U : Matrix ι ι ℂ) :=
  (rfl)

/-- **The adjoint action is by Lie algebra automorphisms.** -/
theorem unitaryAdjointRepresentation_lie (U : unitaryGroup ι ℂ) (X Y : unitaryLieAlgebra ι) :
    unitaryAdjointRepresentation ι U ⁅X, Y⁆ =
      ⁅unitaryAdjointRepresentation ι U X, unitaryAdjointRepresentation ι U Y⁆ := by
  have hU : star (U : Matrix ι ι ℂ) * U = 1 := Unitary.star_mul_self_of_mem U.property
  ext1
  simp only [coe_unitaryAdjointRepresentation_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
  calc (U : Matrix ι ι ℂ) * (X * Y - Y * X) * star (U : Matrix ι ι ℂ)
      = U * X * (star (U : Matrix ι ι ℂ) * U) * Y * star (U : Matrix ι ι ℂ) -
          U * Y * (star (U : Matrix ι ι ℂ) * U) * X * star (U : Matrix ι ι ℂ) := by
        rw [hU]; noncomm_ring
    _ = _ := by noncomm_ring

variable (ι) in
/-- The **coadjoint representation** of `U(n)` on `𝔲(n)*`, the dual of the adjoint
representation: `(Ad*_U ν)(X) = ν (Ad_(U⁻¹) X)`. -/
def unitaryCoadjointRepresentation :
    Representation ℝ (unitaryGroup ι ℂ) (Dual ℝ (unitaryLieAlgebra ι)) :=
  (unitaryAdjointRepresentation ι).dual

theorem unitaryCoadjointRepresentation_apply_apply (U : unitaryGroup ι ℂ)
    (ν : Dual ℝ (unitaryLieAlgebra ι)) (X : unitaryLieAlgebra ι) :
    unitaryCoadjointRepresentation ι U ν X = ν (unitaryAdjointRepresentation ι U⁻¹ X) :=
  (rfl)

/-! ### The trace pairing -/

variable (ι) in
/-- The **trace pairing** `⟨H, X⟩ = -i tr(H X)` of a Hermitian matrix `H` with an element `X` of
`𝔲(n)`. Its values are real (`TauCeti.ofReal_unitaryTracePairing_apply`), and it identifies the
Hermitian matrices with `𝔲(n)*` (`TauCeti.unitaryTracePairingEquiv`). -/
def unitaryTracePairing :
    selfAdjoint.submodule ℝ (Matrix ι ι ℂ) →ₗ[ℝ] Dual ℝ (unitaryLieAlgebra ι) :=
  LinearMap.mk₂ ℝ (fun H X => (-I * ((H : Matrix ι ι ℂ) * X).trace).re)
    (fun H H' X => by simp [Matrix.add_mul, mul_add])
    (fun c H X => by simp [mul_left_comm (I : ℂ)])
    (fun H X X' => by simp [mul_add])
    (fun c H X => by simp [mul_left_comm (I : ℂ)])

theorem unitaryTracePairing_apply (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ))
    (X : unitaryLieAlgebra ι) :
    unitaryTracePairing ι H X = (-I * ((H : Matrix ι ι ℂ) * X).trace).re :=
  (rfl)

/-- **The trace pairing is real**: `-i tr(H X)` is a real number for Hermitian `H` and
skew-Hermitian `X`, namely `⟨H, X⟩`. -/
theorem ofReal_unitaryTracePairing_apply (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ))
    (X : unitaryLieAlgebra ι) :
    (unitaryTracePairing ι H X : ℂ) = -I * ((H : Matrix ι ι ℂ) * X).trace := by
  have h := IsHermitian.re_trace_mul_eq_zero_of_conjTranspose_eq_neg
    (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).isHermitian (conjTranspose_coe_unitaryLieAlgebra
        X)
  rw [RCLike.re_to_complex] at h
  apply Complex.ext <;> simp [unitaryTracePairing_apply, h]

/-- The trace pairing is nondegenerate: `⟨H, i H⟩ = tr(Hᴴ H)` vanishes only for `H = 0`. -/
theorem unitaryTracePairing_injective : Function.Injective (unitaryTracePairing ι) := by
  refine (injective_iff_map_eq_zero _).mpr fun H hH => ?_
  have hHh : (H : Matrix ι ι ℂ)ᴴ = H := (H.property : IsSelfAdjoint
      (H : Matrix ι ι ℂ)).isHermitian.eq
  have h := ofReal_unitaryTracePairing_apply H ((unitaryLieAlgebraEquivSelfAdjoint ι).symm H)
  rw [hH, LinearMap.zero_apply, ofReal_zero, coe_unitaryLieAlgebraEquivSelfAdjoint_symm_apply] at h
  -- `tr(Hᴴ H) = -i tr(H (i H)) = ⟨H, i H⟩ = 0`.
  refine Subtype.ext (trace_conjTranspose_mul_self_eq_zero_iff.mp (Eq.trans ?_ h.symm))
  simp [hHh, ← mul_assoc]

variable (ι) in
/-- **The trace pairing identifies the Hermitian matrices with `𝔲(n)*`**: `H ↦ ⟨H, ·⟩` is a real
linear equivalence. -/
def unitaryTracePairingEquiv :
    selfAdjoint.submodule ℝ (Matrix ι ι ℂ) ≃ₗ[ℝ] Dual ℝ (unitaryLieAlgebra ι) :=
  (unitaryTracePairing ι).linearEquivOfInjective unitaryTracePairing_injective (by
    rw [Subspace.dual_finrank_eq, (unitaryLieAlgebraEquivSelfAdjoint ι).finrank_eq])

@[simp]
theorem unitaryTracePairingEquiv_apply (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryTracePairingEquiv ι H = unitaryTracePairing ι H :=
  LinearMap.linearEquivOfInjective_apply _ _ _

/-! ### The coadjoint action through the trace pairing -/

/-- **The coadjoint action is conjugation of Hermitian matrices**:
`Ad*_U ⟨H, ·⟩ = ⟨U H Uᴴ, ·⟩`. -/
@[simp]
theorem unitaryCoadjointRepresentation_unitaryTracePairing (U : unitaryGroup ι ℂ)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    unitaryCoadjointRepresentation ι U (unitaryTracePairing ι H) =
      unitaryTracePairing ι ⟨U * H * star (U : Matrix ι ι ℂ),
        (H.property : IsSelfAdjoint (H : Matrix ι ι ℂ)).conjugate _⟩ := by
  ext X
  apply Complex.ofReal_injective
  simp only [unitaryCoadjointRepresentation_apply_apply, ofReal_unitaryTracePairing_apply,
    coe_unitaryAdjointRepresentation_apply, ← Unitary.star_eq_inv, Unitary.coe_star, star_star]
  -- `tr(H Uᴴ X U) = tr(U H Uᴴ X)` by cyclicity of the trace.
  simp only [← Matrix.mul_assoc]
  rw [trace_mul_comm _ (U : Matrix ι ι ℂ)]
  simp only [Matrix.mul_assoc]

/-- **The coadjoint orbit of `⟨H, ·⟩` is the unitary conjugacy class of `H`**, read through the
trace pairing. -/
theorem mem_range_unitaryCoadjointRepresentation_unitaryTracePairing_iff
    {H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)} {μ : Dual ℝ (unitaryLieAlgebra ι)} :
    μ ∈ Set.range (fun U => unitaryCoadjointRepresentation ι U (unitaryTracePairing ι H)) ↔
      ∃ U : unitaryGroup ι ℂ, ((unitaryTracePairingEquiv ι).symm μ : Matrix ι ι ℂ) =
        U * H * star (U : Matrix ι ι ℂ) := by
  simp only [Set.mem_range, unitaryCoadjointRepresentation_unitaryTracePairing]
  refine exists_congr fun U => ?_
  rw [eq_comm, ← unitaryTracePairingEquiv_apply, ← LinearEquiv.symm_apply_eq, Subtype.ext_iff]

/-- **The coadjoint stabilizer of `⟨H, ·⟩` is the commutant of `H`**: `U` fixes `⟨H, ·⟩` exactly
when it commutes with `H`. -/
theorem mem_stabilizer_unitaryCoadjointRepresentation_unitaryTracePairing_iff
    {U : unitaryGroup ι ℂ} {H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)} :
    U ∈ (unitaryCoadjointRepresentation ι).stabilizer (unitaryTracePairing ι H) ↔
      (U : Matrix ι ι ℂ) * H = H * U := by
  have hU₁ : star (U : Matrix ι ι ℂ) * U = 1 := Unitary.star_mul_self_of_mem U.property
  have hU₂ : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := Unitary.mul_star_self_of_mem
      U.property
  rw [Representation.mem_stabilizer, unitaryCoadjointRepresentation_unitaryTracePairing,
    unitaryTracePairing_injective.eq_iff, Subtype.ext_iff]
  dsimp only
  refine ⟨fun h => ?_, fun h => by rw [h, Matrix.mul_assoc, hU₂, Matrix.mul_one]⟩
  calc (U : Matrix ι ι ℂ) * H = U * H * (star (U : Matrix ι ι ℂ) * U) := by
        rw [hU₁, Matrix.mul_one]
    _ = U * H * star (U : Matrix ι ι ℂ) * U := by simp only [Matrix.mul_assoc]
    _ = H * U := by rw [h]

/-! ### The infinitesimal coadjoint action and the Kirillov–Kostant–Souriau form -/

/-- **The infinitesimal coadjoint action is the commutator**: `⁅ξ, ⟨H, ·⟩⁆ = ⟨ξ H - H ξ, ·⟩` for
`ξ ∈ 𝔲(n)`, where `ξ H - H ξ` is again Hermitian. -/
theorem lie_unitaryTracePairing (ξ : unitaryLieAlgebra ι)
    (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)) :
    ⁅ξ, unitaryTracePairing ι H⁆ = unitaryTracePairing ι
      ⟨ξ * H - H * ξ,
        IsSelfAdjoint.mul_sub_mul_of_mem_skewAdjoint H.property (mem_unitaryLieAlgebra_iff.mp
            ξ.property)⟩ := by
  ext X
  apply Complex.ofReal_injective
  rw [Dual.lie_apply, ofReal_neg, ofReal_unitaryTracePairing_apply,
    ofReal_unitaryTracePairing_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
  -- `tr(H X ξ) = tr(ξ H X)` by cyclicity of the trace.
  rw [Matrix.mul_sub, Matrix.sub_mul, trace_sub, trace_sub]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_cycle' (H : Matrix ι ι ℂ) (X : Matrix ι ι ℂ) (ξ : Matrix ι ι ℂ)]
  ring

/-- **The stabilizer of `⟨H, ·⟩` in `𝔲(n)` is the commutant of `H`**: `⁅ξ, ⟨H, ·⟩⁆ = 0` exactly
when `ξ` commutes with `H`. -/
theorem mem_lieAnnihilator_unitaryTracePairing_iff {ξ : unitaryLieAlgebra ι}
    {H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ)} :
    ξ ∈ lieAnnihilator ℝ (unitaryLieAlgebra ι) (unitaryTracePairing ι H) ↔
      (ξ : Matrix ι ι ℂ) * H = H * ξ := by
  rw [mem_lieAnnihilator, lie_unitaryTracePairing, ← map_zero (unitaryTracePairing ι),
    unitaryTracePairing_injective.eq_iff, Subtype.ext_iff, Submodule.coe_zero, sub_eq_zero]

/-- **The Kirillov–Kostant–Souriau form in the trace pairing**: on the algebraic tangent model of
the coadjoint orbit through `⟨H, ·⟩`, `ω([ξ], [η]) = -i tr(H ⁅ξ, η⁆)`. -/
theorem ofReal_kksForm_unitaryTracePairing_mk (H : selfAdjoint.submodule ℝ (Matrix ι ι ℂ))
    (ξ η : unitaryLieAlgebra ι) :
    ((unitaryTracePairing ι H).kksForm (Submodule.Quotient.mk ξ) (Submodule.Quotient.mk η) : ℂ) =
      -I * ((H : Matrix ι ι ℂ) * (ξ * η - η * ξ)).trace := by
  rw [Dual.kksForm_mk, ofReal_unitaryTracePairing_apply, LieSubalgebra.coe_bracket, Ring.lie_def]

end TauCeti
