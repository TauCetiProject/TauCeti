/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.WildInertia
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
import TauCeti.LinearAlgebra.Charpoly.Dual
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
  ramification predicates, with `IsUnramified.isTamelyRamified`, the trivial representation,
  characters, products, base change and isomorphism invariance.
* `TauCeti.arithFrobLift`: a chosen arithmetic Frobenius lift.
* `TauCeti.ContinuousRep.IsUnramified.apply_eq_of_isArithFrobeniusLift`: an unramified
  representation takes the same value at all arithmetic Frobenius lifts.
* `TauCeti.ContinuousRep.frobCharpoly`: the Frobenius polynomial, monic of degree the rank
  (`frobCharpoly_monic`, `natDegree_frobCharpoly`), with `nextCoeff` minus the trace of Frobenius
  (`nextCoeff_frobCharpoly`) and constant term `(-1)^n det ρ(Φ)` (`coeff_zero_frobCharpoly`);
  its behaviour under products (`frobCharpoly_prod`), coefficient change
  (`frobCharpoly_baseChange`) and isomorphism (`Iso.frobCharpoly_eq`); and its value on the trivial
  representation and on characters.
* `TauCeti.ContinuousRep.frobCharpolyGeom`: the geometric Frobenius polynomial, which is the
  Frobenius polynomial of the contragredient (`frobCharpoly_dual`) and the signed reverse of the
  arithmetic one (`frobCharpolyGeom_eq_reverse`).
-/

@[expose] public section

noncomputable section

open Polynomial

open scoped TensorProduct

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- A chosen arithmetic Frobenius lift in the absolute Galois group of a nonarchimedean local
field (`TauCeti.exists_isArithFrobeniusLift`). Statements about unramified representations do not
depend on this choice: see `TauCeti.ContinuousRep.IsUnramified.apply_eq_of_isArithFrobeniusLift`. -/
def arithFrobLift : Field.absoluteGaloisGroup K :=
  (exists_isArithFrobeniusLift K).choose

theorem isArithFrobeniusLift_arithFrobLift : IsArithFrobeniusLift K (arithFrobLift K) :=
  (exists_isArithFrobeniusLift K).choose_spec

namespace ContinuousRep

variable {K}

section Predicates

variable {A M N : Type*} [Semiring A] [AddCommMonoid M] [Module A M] [TopologicalSpace M]
  [AddCommMonoid N] [Module A N] [TopologicalSpace N]

/-- A continuous representation of the absolute Galois group of a nonarchimedean local field is
**unramified** if the inertia subgroup acts trivially. -/
def IsUnramified (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) : Prop :=
  ∀ σ ∈ inertiaSubgroup K, ρ σ = 1

/-- A continuous representation of the absolute Galois group of a nonarchimedean local field is
**tamely ramified** if the wild inertia subgroup acts trivially. -/
def IsTamelyRamified (ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M) : Prop :=
  ∀ σ ∈ wildInertiaSubgroup K, ρ σ = 1

variable {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}
  {ρ' : ContinuousRep (Field.absoluteGaloisGroup K) A N}

/-- Unramified representations are tamely ramified, since wild inertia lies in inertia. -/
theorem IsUnramified.isTamelyRamified (h : ρ.IsUnramified) : ρ.IsTamelyRamified :=
  fun σ hσ ↦ h σ (wildInertiaSubgroup_le_inertiaSubgroup K hσ)

variable (K A M) in
theorem isUnramified_trivial : (trivial (Field.absoluteGaloisGroup K) A M).IsUnramified :=
  fun _ _ ↦ LinearMap.ext fun x ↦ trivial_apply _ x

variable (K A M) in
theorem isTamelyRamified_trivial :
    (trivial (Field.absoluteGaloisGroup K) A M).IsTamelyRamified :=
  (isUnramified_trivial K A M).isTamelyRamified

/-- A product of unramified representations is unramified. -/
theorem IsUnramified.prod (h : ρ.IsUnramified) (h' : ρ'.IsUnramified) :
    (ρ.prod ρ').IsUnramified := fun σ hσ ↦
  LinearMap.ext fun x ↦ by simp [prod_apply, h σ hσ, h' σ hσ]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A product of tamely ramified representations is tamely ramified. -/
theorem IsTamelyRamified.prod (h : ρ.IsTamelyRamified) (h' : ρ'.IsTamelyRamified) :
    (ρ.prod ρ').IsTamelyRamified := fun σ hσ ↦
  LinearMap.ext fun x ↦ by simp [prod_apply, h σ hσ, h' σ hσ]

/-- An isomorphism preserves unramifiedness. -/
theorem Iso.isUnramified_iff (e : Iso ρ ρ') : ρ.IsUnramified ↔ ρ'.IsUnramified := by
  refine ⟨fun h σ hσ ↦ LinearMap.ext fun y ↦ ?_, fun h σ hσ ↦ LinearMap.ext fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := EquivLike.surjective e y
    rw [← e.isIntertwining, h σ hσ]
    rfl
  · apply EquivLike.injective e
    rw [e.isIntertwining, h σ hσ]
    rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- An isomorphism preserves tame ramification. -/
theorem Iso.isTamelyRamified_iff (e : Iso ρ ρ') :
    ρ.IsTamelyRamified ↔ ρ'.IsTamelyRamified := by
  refine ⟨fun h σ hσ ↦ LinearMap.ext fun y ↦ ?_, fun h σ hσ ↦ LinearMap.ext fun x ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := EquivLike.surjective e y
    rw [← e.isIntertwining, h σ hσ]
    rfl
  · apply EquivLike.injective e
    rw [e.isIntertwining, h σ hσ]
    rfl

/-- **Independence of the Frobenius lift.** An unramified representation takes the same value
at any two arithmetic Frobenius lifts, since they differ by an element of inertia. -/
theorem IsUnramified.apply_eq_of_isArithFrobeniusLift (h : ρ.IsUnramified)
    {Φ Φ' : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ)
    (hΦ' : IsArithFrobeniusLift K Φ') : ρ Φ = ρ Φ' := by
  have hmem := (hΦ.isArithFrobeniusLift_iff_inv_mul_mem).1 hΦ'
  rw [← mul_inv_cancel_left Φ Φ', map_mul, h _ hmem, mul_one]

/-- An unramified representation takes the value `ρ(Φ)` at every arithmetic Frobenius lift `Φ`
also at the chosen lift `TauCeti.arithFrobLift K`. -/
theorem IsUnramified.apply_arithFrobLift (h : ρ.IsUnramified)
    {Φ : Field.absoluteGaloisGroup K} (hΦ : IsArithFrobeniusLift K Φ) :
    ρ (arithFrobLift K) = ρ Φ :=
  h.apply_eq_of_isArithFrobeniusLift (isArithFrobeniusLift_arithFrobLift K) hΦ

end Predicates

section Character

variable {A : Type*} [CommRing A] [TopologicalSpace A] [ContinuousMul A]

/-- The line of a continuous character is unramified exactly when the character is trivial on
inertia. -/
theorem isUnramified_ofCharacter_iff (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).IsUnramified ↔ ∀ σ ∈ inertiaSubgroup K, χ σ = 1 := by
  refine forall₂_congr fun σ _ ↦ ⟨fun h ↦ Units.ext ?_, fun h ↦ LinearMap.ext fun a ↦ ?_⟩
  · simpa [ofCharacter_apply] using LinearMap.congr_fun h 1
  · simp [ofCharacter_apply, h]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The line of a continuous character is tamely ramified exactly when the character is trivial
on wild inertia. -/
theorem isTamelyRamified_ofCharacter_iff (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).IsTamelyRamified ↔ ∀ σ ∈ wildInertiaSubgroup K, χ σ = 1 := by
  refine forall₂_congr fun σ _ ↦ ⟨fun h ↦ Units.ext ?_, fun h ↦ LinearMap.ext fun a ↦ ?_⟩
  · simpa [ofCharacter_apply] using LinearMap.congr_fun h 1
  · simp [ofCharacter_apply, h]

end Character

section BaseChange

variable {A M : Type*} [CommRing A] [TopologicalSpace A] [AddCommGroup M] [Module A M]
  [TopologicalSpace M] [IsModuleTopology A M] (B : Type*) [CommRing B] [TopologicalSpace B]
  [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B] [TopologicalSpace (B ⊗[A] M)]
  [IsModuleTopology B (B ⊗[A] M)] {ρ : ContinuousRep (Field.absoluteGaloisGroup K) A M}

/-- Extension of scalars preserves unramifiedness. -/
theorem IsUnramified.baseChange [Module.Finite A M] (h : ρ.IsUnramified) :
    (ρ.baseChange B).IsUnramified := fun σ hσ ↦ by
  rw [baseChange_apply, h σ hσ, Module.End.one_eq_id, LinearMap.baseChange_id]
  rfl

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Extension of scalars preserves tame ramification. -/
theorem IsTamelyRamified.baseChange [Module.Finite A M] (h : ρ.IsTamelyRamified) :
    (ρ.baseChange B).IsTamelyRamified := fun σ hσ ↦ by
  rw [baseChange_apply, h σ hσ, Module.End.one_eq_id, LinearMap.baseChange_id]
  rfl

end BaseChange

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

/-- For an unramified representation the Frobenius polynomial is the characteristic polynomial of
`ρ(Φ)` at any arithmetic Frobenius lift `Φ`. -/
theorem frobCharpoly_eq_charpoly (h : ρ.IsUnramified) {Φ : Field.absoluteGaloisGroup K}
    (hΦ : IsArithFrobeniusLift K Φ) : ρ.frobCharpoly = (ρ Φ).charpoly := by
  rw [frobCharpoly, h.apply_arithFrobLift hΦ]

/-- For an unramified representation the geometric Frobenius polynomial is the characteristic
polynomial of `ρ(Φ⁻¹)` at any arithmetic Frobenius lift `Φ`. -/
theorem frobCharpolyGeom_eq_charpoly (h : ρ.IsUnramified) {Φ : Field.absoluteGaloisGroup K}
    (hΦ : IsArithFrobeniusLift K Φ) : ρ.frobCharpolyGeom = (ρ Φ⁻¹).charpoly := by
  have h' : ρ (arithFrobLift K)⁻¹ = ρ Φ⁻¹ :=
    calc ρ (arithFrobLift K)⁻¹ = ρ (arithFrobLift K)⁻¹ * ρ Φ * ρ Φ⁻¹ := by
          rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
      _ = ρ Φ⁻¹ := by
          rw [← h.apply_arithFrobLift hΦ, ← map_mul, inv_mul_cancel, map_one, one_mul]
  rw [frobCharpolyGeom, h']

theorem frobCharpoly_monic : ρ.frobCharpoly.Monic :=
  LinearMap.charpoly_monic _

theorem natDegree_frobCharpoly [Nontrivial A] :
    ρ.frobCharpoly.natDegree = Module.finrank A M :=
  LinearMap.charpoly_natDegree _

/-- The second coefficient of the Frobenius polynomial is minus the trace of Frobenius. -/
theorem nextCoeff_frobCharpoly :
    ρ.frobCharpoly.nextCoeff = -LinearMap.trace A M (ρ (arithFrobLift K)) := by
  let b := Module.Free.chooseBasis A M
  rw [frobCharpoly, ← LinearMap.charpoly_toMatrix _ b, LinearMap.trace_eq_matrix_trace A b,
    Matrix.trace_eq_neg_charpoly_nextCoeff, neg_neg]

/-- The constant term of the Frobenius polynomial is `(-1)^n` times the determinant of
Frobenius, for `n` the rank. -/
theorem coeff_zero_frobCharpoly :
    ρ.frobCharpoly.coeff 0 =
      (-1) ^ Module.finrank A M * LinearMap.det (ρ (arithFrobLift K)) := by
  nontriviality A
  let b := Module.Free.chooseBasis A M
  rw [frobCharpoly, ← LinearMap.charpoly_toMatrix _ b, ← LinearMap.det_toMatrix b,
    Matrix.det_eq_sign_charpoly_coeff, Module.finrank_eq_card_chooseBasisIndex, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

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

/-- The Frobenius polynomial of a direct sum is the product of the Frobenius polynomials. -/
theorem frobCharpoly_prod : (ρ.prod ρ').frobCharpoly = ρ.frobCharpoly * ρ'.frobCharpoly := by
  have h : (ρ.prod ρ') (arithFrobLift K) =
      ρ.toRepresentation.prod ρ'.toRepresentation (arithFrobLift K) :=
    LinearMap.ext fun x ↦ by rw [prod_apply]; rfl
  rw [frobCharpoly, h, Representation.charpoly_prod_apply]
  rfl

/-- Isomorphic representations have the same Frobenius polynomial. -/
theorem Iso.frobCharpoly_eq (e : Iso ρ ρ') : ρ.frobCharpoly = ρ'.frobCharpoly :=
  e.charpoly_apply_eq _

/-- The Frobenius polynomial of the line of a continuous character `χ` is `X - χ(Φ)`. -/
theorem frobCharpoly_ofCharacter [TopologicalSpace A] [ContinuousMul A]
    (χ : Field.absoluteGaloisGroup K →ₜ* Aˣ) :
    (ofCharacter χ).frobCharpoly = X - C (χ (arithFrobLift K) : A) :=
  charpoly_ofCharacter_apply χ _

/-- **Coefficient change.** Extension of scalars along `A → B` maps the Frobenius polynomial to
`B[X]`. -/
theorem frobCharpoly_baseChange [TopologicalSpace A] [IsModuleTopology A M] (B : Type*)
    [CommRing B] [TopologicalSpace B] [IsTopologicalSemiring B] [Algebra A B] [ContinuousSMul A B]
    [TopologicalSpace (B ⊗[A] M)] [IsModuleTopology B (B ⊗[A] M)] :
    (ρ.baseChange B).frobCharpoly = ρ.frobCharpoly.map (algebraMap A B) := by
  unfold frobCharpoly
  exact charpoly_baseChange_apply B ρ _

/-- The Frobenius polynomial of the contragredient is the geometric Frobenius polynomial. -/
theorem frobCharpoly_dual [TopologicalSpace A] [IsTopologicalRing A] [IsModuleTopology A M]
    [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)] :
    ρ.dual.frobCharpoly = ρ.frobCharpolyGeom := by
  unfold frobCharpoly frobCharpolyGeom
  rw [dual_apply, ← LinearMap.dualMap_def, LinearMap.charpoly_dualMap]

end FrobCharpoly

end ContinuousRep

end TauCeti
