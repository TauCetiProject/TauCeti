/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia.Basic
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
import TauCeti.RepresentationTheory.Dual
import TauCeti.RepresentationTheory.Quotient
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Unramified and tamely ramified local Galois representations, and Frobenius polynomials

Let `K` be a nonarchimedean local field with absolute Galois group `G_K`, inertia subgroup `I_K`
(`TauCeti.inertiaSubgroup`) and wild inertia subgroup `P_K` (`TauCeti.wildInertiaSubgroup`).
A continuous representation `ρ` of `G_K` is *unramified* if `ρ(I_K) = 1` and *tamely ramified*
if `ρ(P_K) = 1`; since `P_K ≤ I_K`, unramified representations are tamely ramified.

All arithmetic Frobenius lifts `Φ` (`TauCeti.IsArithFrobeniusLift`) differ by elements of
inertia, so on an unramified representation the operator `ρ(Φ)` does not depend on the lift. For
`ρ` on a finite free module of rank `n`, the *Frobenius polynomial* is
`frobCharpoly ρ = det(X - ρ(Φ))`, computed at the lift `TauCeti.arithFrobLift K` chosen once and
for all; for unramified `ρ` it is the characteristic polynomial of `ρ(Φ)` at every arithmetic
lift (`frobCharpoly_eq_charpoly`). Frobenius is arithmetic: the geometric variant
`frobCharpolyGeom ρ = det(X - ρ(Φ⁻¹))` is the Frobenius polynomial of the contragredient
(`frobCharpoly_dual`).

## Main declarations

* `TauCeti.ContinuousRep.IsUnramified`, `TauCeti.ContinuousRep.IsTamelyRamified`: the
  ramification predicates `I_K ≤ ker ρ` and `P_K ≤ ker ρ`, with `IsUnramified.isTamelyRamified`,
  the trivial representation, characters, products, base change, contragredients and isomorphism
  invariance, all from the corresponding facts about the kernel of `ρ`.
* `TauCeti.ContinuousRep.IsUnramified.apply_eq_of_isArithFrobeniusLift`: an unramified
  representation takes the same value at all arithmetic Frobenius lifts, and likewise at their
  inverses (`IsUnramified.apply_inv_eq_of_isArithFrobeniusLift`).
* `TauCeti.ContinuousRep.frobCharpoly`: the Frobenius polynomial, monic of degree the rank
  (`frobCharpoly_monic`, `natDegree_frobCharpoly`), with `nextCoeff` minus the trace of Frobenius
  (`nextCoeff_frobCharpoly`) and constant term `(-1)^n det ρ(Φ)` (`coeff_zero_frobCharpoly`);
  its behaviour under products (`frobCharpoly_prod`), coefficient change
  (`frobCharpoly_baseChange`) and isomorphism (`Iso.frobCharpoly_eq`); and its value on the trivial
  representation and on characters.
* `TauCeti.ContinuousRep.frobCharpolyGeom`: the geometric Frobenius polynomial, which is the
  Frobenius polynomial of the contragredient (`frobCharpoly_dual`) and the signed reverse of the
  arithmetic one (`frobCharpolyGeom_eq_reverse`), with the same structural API.
-/

public section

noncomputable section

open Polynomial

open scoped TensorProduct

namespace TauCeti

namespace ContinuousRep

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

section Predicates

variable {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]

/-- A continuous representation of the absolute Galois group of a nonarchimedean local field is
**unramified** if the inertia subgroup acts trivially. -/
def IsUnramified (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) : Prop :=
  inertiaSubgroup K ≤ ρ.toRepresentation.ker

/-- A continuous representation of the absolute Galois group of a nonarchimedean local field is
**tamely ramified** if the wild inertia subgroup acts trivially. -/
def IsTamelyRamified (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) : Prop :=
  wildInertiaSubgroup K ≤ ρ.toRepresentation.ker

variable {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup K) A N}

theorem isUnramified_iff : ρ.IsUnramified ↔ ∀ σ ∈ inertiaSubgroup K, ρ σ = 1 :=
  Iff.rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem isTamelyRamified_iff : ρ.IsTamelyRamified ↔ ∀ σ ∈ wildInertiaSubgroup K, ρ σ = 1 :=
  Iff.rfl

/-- Unramified representations are tamely ramified, since wild inertia lies in inertia. -/
theorem IsUnramified.isTamelyRamified (h : ρ.IsUnramified) : ρ.IsTamelyRamified :=
  (wildInertiaSubgroup_le_inertiaSubgroup K).trans h

variable (K A M) in
@[simp]
theorem isUnramified_trivial : (trivial (Field.absoluteGaloisGroup K) A M).IsUnramified := by
  rw [IsUnramified, toRepresentation_trivial, Representation.ker_trivial]
  exact le_top

variable (K A M) in
@[simp]
theorem isTamelyRamified_trivial :
    (trivial (Field.absoluteGaloisGroup K) A M).IsTamelyRamified :=
  (isUnramified_trivial K A M).isTamelyRamified

/-- A product of unramified representations is unramified. -/
theorem IsUnramified.prod (h : ρ.IsUnramified) (h' : ρ'.IsUnramified) :
    (ρ.prod ρ').IsUnramified := by
  rw [IsUnramified, toRepresentation_prod, Representation.ker_prod]
  exact le_inf h h'

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A product of tamely ramified representations is tamely ramified. -/
theorem IsTamelyRamified.prod (h : ρ.IsTamelyRamified) (h' : ρ'.IsTamelyRamified) :
    (ρ.prod ρ').IsTamelyRamified := by
  rw [IsTamelyRamified, toRepresentation_prod, Representation.ker_prod]
  exact le_inf h h'

/-- An isomorphism preserves unramifiedness. -/
theorem Iso.isUnramified_iff (e : Iso ρ ρ') : ρ.IsUnramified ↔ ρ'.IsUnramified := by
  rw [IsUnramified, IsUnramified, e.toRepresentationEquiv.ker_eq]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An isomorphism preserves tame ramification. -/
theorem Iso.isTamelyRamified_iff (e : Iso ρ ρ') :
    ρ.IsTamelyRamified ↔ ρ'.IsTamelyRamified := by
  rw [IsTamelyRamified, IsTamelyRamified, e.toRepresentationEquiv.ker_eq]

/-- **Independence of the Frobenius lift.** An unramified representation takes the same value
at any two arithmetic Frobenius lifts, since they differ by an element of inertia. -/
theorem IsUnramified.apply_eq_of_isArithFrobeniusLift (h : ρ.IsUnramified)
    {Φ Φ' : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ)
    (hΦ' : IsArithFrobeniusLift K Φ') : ρ Φ = ρ Φ' := by
  have hmem := (hΦ.isArithFrobeniusLift_iff_inv_mul_mem).1 hΦ'
  rw [← mul_inv_cancel_left Φ Φ', map_mul, isUnramified_iff.1 h _ hmem, mul_one]

/-- An unramified representation takes the value `ρ(Φ)` at every arithmetic Frobenius lift `Φ`
also at the chosen lift `TauCeti.arithFrobLift K`. -/
theorem IsUnramified.apply_arithFrobLift (h : ρ.IsUnramified)
    {Φ : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ) :
    ρ (arithFrobLift K) = ρ Φ :=
  h.apply_eq_of_isArithFrobeniusLift (isArithFrobeniusLift_arithFrobLift K) hΦ

/-- An unramified representation takes the same value at the inverses of any two arithmetic
Frobenius lifts, since `ρ(Φ⁻¹)` is the inverse of `ρ(Φ) = ρ(Φ')`. -/
theorem IsUnramified.apply_inv_eq_of_isArithFrobeniusLift (h : ρ.IsUnramified)
    {Φ Φ' : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ)
    (hΦ' : IsArithFrobeniusLift K Φ') : ρ Φ⁻¹ = ρ Φ'⁻¹ :=
  left_inv_eq_right_inv (by rw [← map_mul, inv_mul_cancel, map_one])
    (by rw [h.apply_eq_of_isArithFrobeniusLift hΦ hΦ', ← map_mul, mul_inv_cancel, map_one])

/-- An unramified representation takes the value `ρ(Φ⁻¹)` at the inverse of every arithmetic
Frobenius lift `Φ` also at the inverse of the chosen lift `TauCeti.arithFrobLift K`. -/
theorem IsUnramified.apply_inv_arithFrobLift (h : ρ.IsUnramified)
    {Φ : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ) :
    ρ (arithFrobLift K)⁻¹ = ρ Φ⁻¹ :=
  h.apply_inv_eq_of_isArithFrobeniusLift (isArithFrobeniusLift_arithFrobLift K) hΦ

end Predicates

section Character

variable {A : Type*} [CommSemiring A] [TopologicalSpace A] [ContinuousMul A]

/-- The line of a continuous character is unramified exactly when the character is trivial on
inertia. -/
theorem isUnramified_ofCharacter_iff (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).IsUnramified ↔ ∀ σ ∈ inertiaSubgroup K, χ σ = 1 := by
  rw [IsUnramified, toRepresentation_ofCharacter, Representation.ker_ofLinearCharacter]
  exact IsConcreteLE.le_iff.trans <| forall₂_congr fun _ _ ↦ MonoidHom.mem_ker

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The line of a continuous character is tamely ramified exactly when the character is trivial
on wild inertia. -/
theorem isTamelyRamified_ofCharacter_iff (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).IsTamelyRamified ↔ ∀ σ ∈ wildInertiaSubgroup K, χ σ = 1 := by
  rw [IsTamelyRamified, toRepresentation_ofCharacter, Representation.ker_ofLinearCharacter]
  exact IsConcreteLE.le_iff.trans <| forall₂_congr fun _ _ ↦ MonoidHom.mem_ker

end Character

section BaseChange

variable {A M : Type*} [CommSemiring A] [TopologicalSpace A] [AddCommMonoid M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] (B : Type*) [Ring B] [TopologicalSpace B]
  [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)]
  [IsModuleTopology B (B ⊗[A] M)] {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}

/-- Extension of scalars preserves unramifiedness. -/
theorem IsUnramified.baseChange [Module.Finite A M] (h : ρ.IsUnramified) :
    (ρ.baseChange B).IsUnramified := by
  rw [IsUnramified, toRepresentation_baseChange]
  exact h.trans (ρ.toRepresentation.ker_le_ker_baseChange B)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Extension of scalars preserves tame ramification. -/
theorem IsTamelyRamified.baseChange [Module.Finite A M] (h : ρ.IsTamelyRamified) :
    (ρ.baseChange B).IsTamelyRamified := by
  rw [IsTamelyRamified, toRepresentation_baseChange]
  exact h.trans (ρ.toRepresentation.ker_le_ker_baseChange B)

end BaseChange

section Dual

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [AddCommGroup M]
  [Module A M] [TopologicalSpace M] [IsModuleTopology A M] [Module.Finite A M]
  [Module.Projective A M] [TopologicalSpace (Module.Dual A M)]
  [IsModuleTopology A (Module.Dual A M)] {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}

/-- The contragredient of an unramified representation is unramified. -/
theorem IsUnramified.dual (h : ρ.IsUnramified) : ρ.dual.IsUnramified := by
  rw [IsUnramified, toRepresentation_dual]
  exact h.trans ρ.toRepresentation.ker_le_ker_dual

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The contragredient of a tamely ramified representation is tamely ramified. -/
theorem IsTamelyRamified.dual (h : ρ.IsTamelyRamified) : ρ.dual.IsTamelyRamified := by
  rw [IsTamelyRamified, toRepresentation_dual]
  exact h.trans ρ.toRepresentation.ker_le_ker_dual

end Dual

section FrobCharpoly

variable {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M]
  [Module.Free A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [TopologicalSpace N]
  [Module.Free A N] [Module.Finite A N]
  {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup K) A N}

variable (ρ) in
/-- **The Frobenius polynomial** `det(X - ρ(Φ))` of a continuous representation of `G_K` on a
finite free module, at the chosen arithmetic Frobenius lift `Φ = TauCeti.arithFrobLift K`. For
unramified `ρ` it does not depend on the lift (`frobCharpoly_eq_charpoly`). Frobenius is
arithmetic: for `ℤ_ℓ(1)` this is `X - q`, while the geometric `frobCharpolyGeom` is `X - q⁻¹`. -/
def frobCharpoly : A[X] :=
  (ρ (arithFrobLift K)).charpoly

variable (ρ) in
/-- **The geometric Frobenius polynomial** `det(X - ρ(Φ⁻¹))`, at the inverse of the chosen
arithmetic Frobenius lift. It is the Frobenius polynomial of the contragredient
(`frobCharpoly_dual`). -/
def frobCharpolyGeom : A[X] :=
  (ρ (arithFrobLift K)⁻¹).charpoly

variable (ρ) in
theorem frobCharpoly_def : ρ.frobCharpoly = (ρ (arithFrobLift K)).charpoly :=
  (rfl)

variable (ρ) in
theorem frobCharpolyGeom_def : ρ.frobCharpolyGeom = (ρ (arithFrobLift K)⁻¹).charpoly :=
  (rfl)

/-- For an unramified representation the Frobenius polynomial is the characteristic polynomial of
`ρ(Φ)` at any arithmetic Frobenius lift `Φ`. -/
theorem frobCharpoly_eq_charpoly (h : ρ.IsUnramified) {Φ : Field.absoluteGaloisGroup K}
    (hΦ : IsArithFrobeniusLift K Φ) : ρ.frobCharpoly = (ρ Φ).charpoly := by
  rw [frobCharpoly_def, h.apply_arithFrobLift hΦ]

/-- For an unramified representation the geometric Frobenius polynomial is the characteristic
polynomial of `ρ(Φ⁻¹)` at any arithmetic Frobenius lift `Φ`. -/
theorem frobCharpolyGeom_eq_charpoly (h : ρ.IsUnramified) {Φ : Field.absoluteGaloisGroup K}
    (hΦ : IsArithFrobeniusLift K Φ) : ρ.frobCharpolyGeom = (ρ Φ⁻¹).charpoly := by
  rw [frobCharpolyGeom_def, h.apply_inv_arithFrobLift hΦ]

theorem frobCharpoly_monic : ρ.frobCharpoly.Monic :=
  LinearMap.charpoly_monic _

theorem frobCharpolyGeom_monic : ρ.frobCharpolyGeom.Monic :=
  LinearMap.charpoly_monic _

theorem natDegree_frobCharpoly [Nontrivial A] :
    ρ.frobCharpoly.natDegree = Module.finrank A M :=
  LinearMap.charpoly_natDegree _

theorem natDegree_frobCharpolyGeom [Nontrivial A] :
    ρ.frobCharpolyGeom.natDegree = Module.finrank A M :=
  LinearMap.charpoly_natDegree _

/-- The second coefficient of the Frobenius polynomial is minus the trace of Frobenius. -/
theorem nextCoeff_frobCharpoly :
    ρ.frobCharpoly.nextCoeff = -LinearMap.trace A M (ρ (arithFrobLift K)) := by
  let b := Module.Free.chooseBasis A M
  rw [frobCharpoly_def, ← LinearMap.charpoly_toMatrix _ b, LinearMap.trace_eq_matrix_trace A b,
    Matrix.trace_eq_neg_charpoly_nextCoeff, neg_neg]

/-- The constant term of the Frobenius polynomial is `(-1)^n` times the determinant of
Frobenius, for `n` the rank. -/
theorem coeff_zero_frobCharpoly :
    ρ.frobCharpoly.coeff 0 =
      (-1) ^ Module.finrank A M * LinearMap.det (ρ (arithFrobLift K)) := by
  nontriviality A
  let b := Module.Free.chooseBasis A M
  rw [frobCharpoly_def, ← LinearMap.charpoly_toMatrix _ b, ← LinearMap.det_toMatrix b,
    Matrix.det_eq_sign_charpoly_coeff]
  simp [Module.finrank_eq_card_chooseBasisIndex, ← mul_assoc, ← pow_add]

/-- The geometric Frobenius polynomial is the signed reverse of the arithmetic one:
`det(X - ρ(Φ⁻¹)) = (-1)^n det ρ(Φ⁻¹) · X^n det(X⁻¹ - ρ(Φ))`. -/
theorem frobCharpolyGeom_eq_reverse :
    ρ.frobCharpolyGeom = (-1) ^ Module.finrank A M *
      C (LinearMap.det (ρ (arithFrobLift K)⁻¹)) * ρ.frobCharpoly.reverse :=
  Representation.charpoly_apply_inv ρ.toRepresentation _

/-- The Frobenius polynomial of the trivial representation of rank `n` is `(X - 1)^n`. -/
@[simp]
theorem frobCharpoly_trivial :
    (trivial (Field.absoluteGaloisGroup K) A M).frobCharpoly = (X - 1) ^ Module.finrank A M :=
  charpoly_trivial_apply _ A M _

/-- The geometric Frobenius polynomial of the trivial representation of rank `n` is
`(X - 1)^n`. -/
@[simp]
theorem frobCharpolyGeom_trivial :
    (trivial (Field.absoluteGaloisGroup K) A M).frobCharpolyGeom = (X - 1) ^ Module.finrank A M :=
  charpoly_trivial_apply _ A M _

/-- The Frobenius polynomial of a direct sum is the product of the Frobenius polynomials. -/
@[simp]
theorem frobCharpoly_prod : (ρ.prod ρ').frobCharpoly = ρ.frobCharpoly * ρ'.frobCharpoly :=
  charpoly_prod_apply ρ ρ' _

/-- The geometric Frobenius polynomial of a direct sum is the product of the geometric Frobenius
polynomials. -/
@[simp]
theorem frobCharpolyGeom_prod :
    (ρ.prod ρ').frobCharpolyGeom = ρ.frobCharpolyGeom * ρ'.frobCharpolyGeom :=
  charpoly_prod_apply ρ ρ' _

/-- Isomorphic representations have the same Frobenius polynomial. -/
theorem Iso.frobCharpoly_eq (e : Iso ρ ρ') : ρ.frobCharpoly = ρ'.frobCharpoly :=
  e.charpoly_apply_eq _

/-- Isomorphic representations have the same geometric Frobenius polynomial. -/
theorem Iso.frobCharpolyGeom_eq (e : Iso ρ ρ') : ρ.frobCharpolyGeom = ρ'.frobCharpolyGeom :=
  e.charpoly_apply_eq _

/-- The Frobenius polynomial of the line of a continuous character `χ` is `X - χ(Φ)`. -/
@[simp]
theorem frobCharpoly_ofCharacter [TopologicalSpace A] [ContinuousMul A]
    (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).frobCharpoly = X - C (χ (arithFrobLift K) : A) :=
  charpoly_ofCharacter_apply χ _

/-- The geometric Frobenius polynomial of the line of a continuous character `χ` is
`X - χ(Φ)⁻¹`. -/
@[simp]
theorem frobCharpolyGeom_ofCharacter [TopologicalSpace A] [ContinuousMul A]
    (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).frobCharpolyGeom = X - C (((χ (arithFrobLift K))⁻¹ : Aˣ) : A) := by
  rw [frobCharpolyGeom_def, charpoly_ofCharacter_apply, map_inv]

section BaseChange

variable [TopologicalSpace A] [IsModuleTopology A M] (B : Type*) [CommRing B] [TopologicalSpace B]
  [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)]
  [IsModuleTopology B (B ⊗[A] M)]

/-- **Coefficient change.** Extension of scalars along `A → B` maps the Frobenius polynomial to
`B[X]`. -/
theorem frobCharpoly_baseChange :
    (ρ.baseChange B).frobCharpoly = ρ.frobCharpoly.map (algebraMap A B) :=
  charpoly_baseChange_apply B ρ _

/-- **Coefficient change.** Extension of scalars along `A → B` maps the geometric Frobenius
polynomial to `B[X]`. -/
theorem frobCharpolyGeom_baseChange :
    (ρ.baseChange B).frobCharpolyGeom = ρ.frobCharpolyGeom.map (algebraMap A B) :=
  charpoly_baseChange_apply B ρ _

end BaseChange

/-- The Frobenius polynomial of the contragredient is the geometric Frobenius polynomial. -/
@[simp]
theorem frobCharpoly_dual [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology A M]
    [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)] :
    ρ.dual.frobCharpoly = ρ.frobCharpolyGeom := by
  rw [frobCharpoly_def, frobCharpolyGeom_def, ← coe_toRepresentation, toRepresentation_dual,
    Representation.charpoly_dual_apply, coe_toRepresentation]

end FrobCharpoly

end ContinuousRep

end TauCeti
