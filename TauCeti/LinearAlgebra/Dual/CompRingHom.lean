/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Transporting the coefficients of linear forms

`Module.Dual.compRingHom` applies a ring homomorphism to the coefficients of a linear
form on a finite coordinate module. It treats extension of scalars and conjugation by a
field automorphism uniformly, without choosing an algebra structure or forming a tensor
product in its interface. Evaluation commutes with mapping the coordinates, and transport
respects identity homomorphisms, composition, addition and scalar multiplication.

For an injective homomorphism into an integral domain, transport preserves and reflects
linear independence, including for rectangular systems of forms. The determinant of a
square system is mapped by the homomorphism. These facts allow a system of independent
algebraic linear forms to be extended to a larger coefficient field and then conjugated.

The construction uses Mathlib's `Module.Basis.constr`; independence is transferred through
the coefficient equivalences using `linearIndependent_algebraMap_comp_iff`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006),
  Theorem 7.2.2 and Remark 7.2.3, for extension and conjugation of coefficient systems.
-/

public section

namespace Module.Dual

section Semiring

variable {R S T ι : Type*} [Semiring R] [Semiring S] [Semiring T]
  [Fintype ι]

/-- Apply a ring homomorphism to the coefficients of a linear form on a finite
coordinate module. -/
noncomputable def compRingHom (L : Dual R (ι → R)) (f : R →+* S) : Dual S (ι → S) := by
  classical
  exact (Pi.basisFun S ι).constr ℕ fun i ↦ f (L (Pi.basisFun R ι i))

/-- Evaluate a transported form as a sum of its transported coefficients. -/
theorem compRingHom_apply (L : Dual R (ι → R)) (f : R →+* S) (x : ι → S) :
    L.compRingHom f x = ∑ i, x i * f (L (Pi.basisFun R ι i)) := by
  classical
  simp [compRingHom, Basis.constr_apply_fintype, Pi.basisFun_equivFun, smul_eq_mul]

open scoped Classical in
/-- A transported form on a single coordinate is determined by the image of that coefficient. -/
@[simp]
theorem compRingHom_single (L : Dual R (ι → R)) (f : R →+* S) (i : ι) (a : S) :
    L.compRingHom f (Pi.single i a) = a * f (L (Pi.single i 1)) := by
  classical
  rw [compRingHom_apply]
  simp [Pi.single_apply]

/-- Mapping the coordinates and the coefficients commutes with evaluation. -/
@[simp]
theorem compRingHom_apply_map (L : Dual R (ι → R)) (f : R →+* S) (x : ι → R) :
    L.compRingHom f (f ∘ x) = f (L x) := by
  classical
  conv_rhs => rw [← (Pi.basisFun R ι).sum_repr x, map_sum, map_sum]
  simp [compRingHom_apply, map_smul, smul_eq_mul]

/-- Transport along the identity leaves a form unchanged. -/
@[simp]
theorem compRingHom_id (L : Dual R (ι → R)) : L.compRingHom (RingHom.id R) = L := by
  classical
  exact (Pi.basisFun R ι).ext fun i ↦ by simp

/-- Successive coefficient transports compose. -/
@[simp]
theorem compRingHom_comp (L : Dual R (ι → R)) (f : R →+* S) (g : S →+* T) :
    (L.compRingHom f).compRingHom g = L.compRingHom (g.comp f) := by
  classical
  exact (Pi.basisFun T ι).ext fun i ↦ by simp

/-- Transport preserves the zero form. -/
@[simp]
theorem compRingHom_zero (f : R →+* S) : (0 : Dual R (ι → R)).compRingHom f = 0 := by
  classical
  exact (Pi.basisFun S ι).ext fun i ↦ by simp

/-- Transport preserves addition of forms. -/
@[simp]
theorem compRingHom_add (L M : Dual R (ι → R)) (f : R →+* S) :
    (L + M).compRingHom f = L.compRingHom f + M.compRingHom f := by
  classical
  exact (Pi.basisFun S ι).ext fun i ↦ by simp

/-- Coordinate projections are unchanged by coefficient transport. -/
@[simp]
theorem compRingHom_proj (f : R →+* S) (i : ι) :
    compRingHom (LinearMap.proj i : Dual R (ι → R)) f = LinearMap.proj i := by
  classical
  exact (Pi.basisFun S ι).ext fun j ↦ by simp [Pi.basisFun_apply, Pi.single_apply]

/-- An injective coefficient homomorphism gives an injective transport on forms. -/
theorem compRingHom_injective (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (fun L : Dual R (ι → R) ↦ L.compRingHom f) := by
  classical
  intro L M h
  apply (Pi.basisFun R ι).ext
  intro i
  apply hf
  simpa using LinearMap.congr_fun h (Pi.basisFun S ι i)

end Semiring

section CommSemiring

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]

/-- Transport applies the coefficient homomorphism to scalars. -/
@[simp]
theorem compRingHom_smul (L : Dual R (ι → R)) (f : R →+* S) (a : R) :
    (a • L).compRingHom f = f a • L.compRingHom f := by
  classical
  exact (Pi.basisFun S ι).ext fun i ↦ by simp [smul_eq_mul]

end CommSemiring

section Algebra

variable {A R S ι : Type*} [CommSemiring A] [Semiring R] [Semiring S]
  [Algebra A R] [Algebra A S] [Fintype ι]

/-- Transport along an algebra homomorphism commutes with evaluation on points over the
base ring. In particular this applies to conjugation fixing the base field. -/
@[simp]
theorem compRingHom_apply_algebraMap (L : Dual R (ι → R)) (f : R →ₐ[A] S) (x : ι → A) :
    L.compRingHom (f : R →+* S) (algebraMap A S ∘ x) =
      f (L (algebraMap A R ∘ x)) := by
  have h : algebraMap A S ∘ x = (f : R →+* S) ∘ (algebraMap A R ∘ x) := by
    ext i
    simp
  rw [h, compRingHom_apply_map, AlgHom.coe_toRingHom]

end Algebra

section Matrix

variable {R S ι κ : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]

open scoped Classical in
/-- The matrix of a transported system is its original matrix with the homomorphism
applied entrywise. -/
theorem toMatrix'_pi_compRingHom (L : κ → Dual R (ι → R)) (f : R →+* S) :
    LinearMap.toMatrix' (LinearMap.pi fun i ↦ (L i).compRingHom f) =
      (LinearMap.toMatrix' (LinearMap.pi L)).map f := by
  ext i j
  simp [LinearMap.toMatrix'_apply]

end Matrix

section CommRing

variable {R S ι κ : Type*} [CommRing R] [CommRing S] [Fintype ι]

/-- The determinant of a square system of forms commutes with coefficient transport. -/
theorem det_pi_compRingHom (L : ι → Dual R (ι → R)) (f : R →+* S) :
    LinearMap.det (LinearMap.pi fun i ↦ (L i).compRingHom f) =
      f (LinearMap.det (LinearMap.pi L)) := by
  classical
  rw [← LinearMap.det_toMatrix', toMatrix'_pi_compRingHom, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, LinearMap.det_toMatrix']

/-- An injective homomorphism into an integral domain preserves and reflects linear
independence of forms. The system need not be square, nor have finitely many forms. -/
@[simp]
theorem linearIndependent_compRingHom_iff [IsDomain S] (L : κ → Dual R (ι → R))
    (f : R →+* S) (hf : Function.Injective f) :
    LinearIndependent S (fun i ↦ (L i).compRingHom f) ↔ LinearIndependent R L := by
  classical
  let := f.toAlgebra
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hf
  let eR : Dual R (ι → R) ≃ₗ[R] (ι → R) := ((Pi.basisFun R ι).constr R).symm
  let eS : Dual S (ι → S) ≃ₗ[S] (ι → S) := ((Pi.basisFun S ι).constr S).symm
  have hcoeff : (fun i ↦ eS ((L i).compRingHom f)) =
      fun i ↦ algebraMap R S ∘ eR (L i) := by
    ext i j
    simp [eR, eS, RingHom.algebraMap_toAlgebra]
  calc
    _ ↔ LinearIndependent S (fun i ↦ eS ((L i).compRingHom f)) :=
      (eS.toLinearMap.linearIndependent_iff_of_injOn eS.injective.injOn).symm
    _ ↔ LinearIndependent R (fun i ↦ eR (L i)) := by
      rw [hcoeff]
      exact linearIndependent_algebraMap_comp_iff
    _ ↔ _ := eR.toLinearMap.linearIndependent_iff_of_injOn eR.injective.injOn

end CommRing

section Examples

variable {K F E ι κ : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Fintype ι]

-- Extending coefficients and then conjugating preserves independence of the whole system.
example (L : κ → Dual F (ι → F)) (hL : LinearIndependent F L) (f : F →ₐ[K] E)
    (σ : E ≃ₐ[K] E) :
    LinearIndependent E (fun i ↦ ((L i).compRingHom f.toRingHom).compRingHom σ.toRingHom) := by
  rw [linearIndependent_compRingHom_iff _ σ.toRingHom σ.injective]
  exact (linearIndependent_compRingHom_iff L f.toRingHom f.injective).2 hL

-- On base-field points, the new value is the conjugate of the extended original value.
example (L : Dual F (ι → F)) (f : F →ₐ[K] E) (σ : E ≃ₐ[K] E) (x : ι → K) :
    (L.compRingHom ((σ.toAlgHom : E →+* E).comp (f : F →+* E)))
      (algebraMap K E ∘ x) = σ (f (L (algebraMap K F ∘ x))) := by
  rw [← compRingHom_comp]
  rw [compRingHom_apply_algebraMap _ σ.toAlgHom, compRingHom_apply_algebraMap]
  simp

end Examples

end Module.Dual
