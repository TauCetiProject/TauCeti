/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import TauCeti.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.LinearIndependent.BaseChange

/-!
# Transporting the coefficients of linear forms

`Module.Dual.compRingHom` applies a ring homomorphism to the coefficients of a linear
form on a finite coordinate module. It treats extension of scalars and conjugation by a
field automorphism uniformly, without choosing an algebra structure or forming a tensor
product in its interface. Evaluation commutes with mapping the coordinates, and transport
respects identity homomorphisms, composition, addition and scalar multiplication.

For an injective homomorphism into an integral domain, or a homomorphism from a field into
a nontrivial commutative semiring, transport preserves and reflects linear independence,
including for rectangular systems of forms. The determinant of a
square system is mapped by the homomorphism. These facts allow a system of independent
algebraic linear forms to be extended to a larger coefficient field and then conjugated.

The construction uses Mathlib's `Module.Basis.constr`; independence is transferred to the
coefficient vectors of the forms by `Module.Dual.linearIndependent_iff_apply_basis` and then
through Mathlib's `linearIndependent_algebraMap_comp_iff` or, for a field source,
`TauCeti.linearIndependent_algebraMap_comp_iff_of_field`, which adapts part of Oliver Nash's
proof in Mathlib's `Mathlib/LinearAlgebra/LinearIndependent/BaseChange.lean`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry* (2006),
  Theorem 7.2.2 and Remark 7.2.3, for extension and conjugation of coefficient systems.
-/

public section

namespace Module.Dual

section Semiring

variable {R S T ι : Type*} [Semiring R] [Semiring S] [Semiring T]

/-- Apply a ring homomorphism to the coefficients of a linear form on a finite
coordinate module. -/
noncomputable def compRingHom [Finite ι] (L : Dual R (ι → R)) (f : R →+* S) : Dual S (ι → S) := by
  classical
  exact (Pi.basisFun S ι).constr ℕ fun i ↦ f (L (Pi.basisFun R ι i))

/-- Evaluate a transported form as a sum of its transported coefficients. -/
theorem compRingHom_apply [Fintype ι] (L : Dual R (ι → R)) (f : R →+* S) (x : ι → S) :
    L.compRingHom f x = ∑ i, x i * f (L (Pi.basisFun R ι i)) := by
  classical
  simp [compRingHom, Basis.constr_apply_fintype, Pi.basisFun_equivFun, smul_eq_mul]

variable [Finite ι]

/-- Evaluation at a standard basis vector gives the corresponding transported coefficient. -/
@[simp]
theorem compRingHom_basisFun (L : Dual R (ι → R)) (f : R →+* S) (i : ι) :
    L.compRingHom f (Pi.basisFun S ι i) = f (L (Pi.basisFun R ι i)) := by
  classical
  cases nonempty_fintype ι
  simp [compRingHom_apply, Pi.single_apply]

/-- A transported form on a single coordinate is determined by the image of that coefficient. -/
@[simp]
theorem compRingHom_single [DecidableEq ι] (L : Dual R (ι → R)) (f : R →+* S) (i : ι) (a : S) :
    L.compRingHom f (Pi.single i a) = a * f (L (Pi.single i 1)) := by
  classical
  cases nonempty_fintype ι
  rw [compRingHom_apply]
  simp [Pi.single_apply]

/-- Mapping the coordinates and the coefficients commutes with evaluation. -/
@[simp]
theorem compRingHom_apply_comp (L : Dual R (ι → R)) (f : R →+* S) (x : ι → R) :
    L.compRingHom f (f ∘ x) = f (L x) := by
  classical
  cases nonempty_fintype ι
  conv_rhs => rw [← (Pi.basisFun R ι).sum_repr x, map_sum, map_sum]
  simp [compRingHom_apply, map_smul, smul_eq_mul]

/-- Evaluation commutes with applying the homomorphism to each coordinate. -/
@[simp]
theorem compRingHom_apply_fun_comp (L : Dual R (ι → R)) (f : R →+* S) (x : ι → R) :
    L.compRingHom f (fun i ↦ f (x i)) = f (L x) :=
  L.compRingHom_apply_comp f x

/-- Evaluation commutes with a bundled homomorphism acting on the coordinates. -/
@[simp]
theorem compRingHom_toRingHom_apply_comp {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (L : Dual R (ι → R)) (f : F) (x : ι → R) :
    L.compRingHom (f : R →+* S) (f ∘ x) = f (L x) := by
  simpa only [RingHom.coe_coe] using L.compRingHom_apply_comp (f : R →+* S) x

/-- Evaluation commutes with a bundled homomorphism applied to each coordinate. -/
@[simp]
theorem compRingHom_toRingHom_apply_fun_comp {F : Type*} [FunLike F R S] [RingHomClass F R S]
    (L : Dual R (ι → R)) (f : F) (x : ι → R) :
    L.compRingHom (f : R →+* S) (fun i ↦ f (x i)) = f (L x) :=
  L.compRingHom_toRingHom_apply_comp f x

/-- Transport along the identity leaves a form unchanged. -/
@[simp]
theorem compRingHom_id (L : Dual R (ι → R)) : L.compRingHom (RingHom.id R) = L := by
  classical
  exact (Pi.basisFun R ι).ext fun i ↦ by simp

/-- Successive coefficient transports compose. -/
theorem compRingHom_compRingHom (L : Dual R (ι → R)) (f : R →+* S) (g : S →+* T) :
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

/-- Transport preserves finite sums of forms. -/
@[simp]
theorem compRingHom_sum {κ : Type*} (s : Finset κ) (L : κ → Dual R (ι → R))
    (f : R →+* S) :
    (∑ i ∈ s, L i).compRingHom f = ∑ i ∈ s, (L i).compRingHom f := by
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

/-- Transport along an injective homomorphism detects the zero form. -/
theorem compRingHom_eq_zero_iff_of_injective {L : Dual R (ι → R)} {f : R →+* S}
    (hf : Function.Injective f) : L.compRingHom f = 0 ↔ L = 0 :=
  (compRingHom_injective f hf).eq_iff' (compRingHom_zero f)

/-- Transport along an injective homomorphism detects equality of forms. -/
theorem compRingHom_inj_of_injective {L M : Dual R (ι → R)} {f : R →+* S}
    (hf : Function.Injective f) : L.compRingHom f = M.compRingHom f ↔ L = M :=
  (compRingHom_injective f hf).eq_iff

end Semiring

section SimpleRing

variable {R S ι : Type*} [Ring R] [IsSimpleRing R] [Semiring S] [Nontrivial S] [Finite ι]

/-- Coefficient transport from a simple ring, such as a division ring, detects the zero form. -/
@[simp]
theorem compRingHom_eq_zero_iff {L : Dual R (ι → R)} {f : R →+* S} :
    L.compRingHom f = 0 ↔ L = 0 :=
  compRingHom_eq_zero_iff_of_injective f.injective

/-- Coefficient transport from a simple ring, such as a division ring, detects equality of
forms. -/
@[simp]
theorem compRingHom_inj {L M : Dual R (ι → R)} {f : R →+* S} :
    L.compRingHom f = M.compRingHom f ↔ L = M :=
  compRingHom_inj_of_injective f.injective

end SimpleRing

section Ring

variable {R S ι : Type*} [Ring R] [Ring S] [Finite ι]

/-- Transport preserves negation of forms. -/
@[simp]
theorem compRingHom_neg (L : Dual R (ι → R)) (f : R →+* S) :
    (-L).compRingHom f = -L.compRingHom f := by
  classical
  exact (Pi.basisFun S ι).ext fun i ↦ by simp

/-- Transport preserves subtraction of forms. -/
@[simp]
theorem compRingHom_sub (L M : Dual R (ι → R)) (f : R →+* S) :
    (L - M).compRingHom f = L.compRingHom f - M.compRingHom f := by
  simp [sub_eq_add_neg]

end Ring

section CommSemiring

variable {R S ι : Type*} [CommSemiring R] [CommSemiring S] [Finite ι]

/-- Transport applies the coefficient homomorphism to scalars. -/
@[simp]
theorem compRingHom_smul (L : Dual R (ι → R)) (f : R →+* S) (a : R) :
    (a • L).compRingHom f = f a • L.compRingHom f := by
  classical
  exact (Pi.basisFun S ι).ext fun i ↦ by simp [smul_eq_mul]

end CommSemiring

section Algebra

variable {A R S ι : Type*} [CommSemiring A] [Semiring R] [Semiring S]
  [Algebra A R] [Algebra A S] [Finite ι]

/-- A coefficient homomorphism commuting with the base-ring maps preserves evaluation
on base-ring points. -/
theorem compRingHom_apply_algebraMap_comp_of_commutes (L : Dual R (ι → R)) (f : R →+* S)
    (hf : ∀ a, f (algebraMap A R a) = algebraMap A S a) (x : ι → A) :
    L.compRingHom f (algebraMap A S ∘ x) = f (L (algebraMap A R ∘ x)) := by
  have h : algebraMap A S ∘ x = f ∘ (algebraMap A R ∘ x) := by
    ext i
    exact (hf (x i)).symm
  rw [h, compRingHom_apply_comp]

/-- Transport along an algebra homomorphism commutes with evaluation on points over the
base ring. In particular this applies to conjugation fixing the base field. -/
@[simp]
theorem compRingHom_apply_algebraMap_comp {F : Type*} [FunLike F R S] [AlgHomClass F A R S]
    (L : Dual R (ι → R)) (f : F) (x : ι → A) :
    L.compRingHom (f : R →+* S) (algebraMap A S ∘ x) =
      f (L (algebraMap A R ∘ x)) := by
  exact L.compRingHom_apply_algebraMap_comp_of_commutes (f : R →+* S)
    (AlgHomClass.commutes f) x

/-- Evaluation on base-ring coordinates commutes with transport by an algebra homomorphism. -/
@[simp]
theorem compRingHom_apply_fun_algebraMap {F : Type*} [FunLike F R S] [AlgHomClass F A R S]
    (L : Dual R (ι → R)) (f : F) (x : ι → A) :
    L.compRingHom (f : R →+* S) (fun i ↦ algebraMap A S (x i)) =
      f (L (fun i ↦ algebraMap A R (x i))) :=
  L.compRingHom_apply_algebraMap_comp f x

end Algebra

section ScalarTower

variable {A R S ι : Type*} [CommSemiring A] [CommSemiring R] [Semiring S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Finite ι]

/-- Extension of coefficients in an algebra tower preserves evaluation on base-ring points. -/
@[simp]
theorem compRingHom_algebraMap_apply_algebraMap_comp (L : Dual R (ι → R)) (x : ι → A) :
    L.compRingHom (algebraMap R S) (algebraMap A S ∘ x) =
      algebraMap R S (L (algebraMap A R ∘ x)) :=
  L.compRingHom_apply_algebraMap_comp_of_commutes (algebraMap R S)
    (fun a ↦ (IsScalarTower.algebraMap_apply A R S a).symm) x

/-- Evaluation on base-ring coordinates commutes with extension along an algebra tower. -/
@[simp]
theorem compRingHom_algebraMap_apply_fun_algebraMap (L : Dual R (ι → R)) (x : ι → A) :
    L.compRingHom (algebraMap R S) (fun i ↦ algebraMap A S (x i)) =
      algebraMap R S (L (fun i ↦ algebraMap A R (x i))) :=
  L.compRingHom_algebraMap_apply_algebraMap_comp x

end ScalarTower

section Matrix

variable {R S ι κ : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]
  [DecidableEq ι]

/-- The matrix of a transported system is its original matrix with the homomorphism
applied entrywise. -/
@[simp]
theorem toMatrix'_pi_compRingHom (L : κ → Dual R (ι → R)) (f : R →+* S) :
    LinearMap.toMatrix' (LinearMap.pi fun i ↦ (L i).compRingHom f) =
      (LinearMap.toMatrix' (LinearMap.pi L)).map f := by
  ext i j
  simp [LinearMap.toMatrix'_apply]

end Matrix

section LinearIndependent

variable {R S ι κ : Type*} [Semiring R] [CommSemiring S] [Finite ι]

/-- A transported system of forms is linearly independent exactly when the transported
coefficient vectors of its forms are. -/
theorem linearIndependent_compRingHom_iff_comp {L : κ → Dual R (ι → R)} {f : R →+* S} :
    LinearIndependent S (fun i ↦ (L i).compRingHom f) ↔
      LinearIndependent S (fun i ↦ f ∘ fun j ↦ L i (Pi.basisFun R ι j)) := by
  rw [linearIndependent_iff_apply_basis (Pi.basisFun S ι)]
  simp only [compRingHom_basisFun, Function.comp_def]

end LinearIndependent

section CommRing

variable {R S ι κ : Type*} [CommRing R] [CommRing S] [Finite ι]

/-- The determinant of a square system of forms commutes with coefficient transport. -/
@[simp]
theorem det_pi_compRingHom (L : ι → Dual R (ι → R)) (f : R →+* S) :
    LinearMap.det (LinearMap.pi fun i ↦ (L i).compRingHom f) =
      f (LinearMap.det (LinearMap.pi L)) := by
  classical
  cases nonempty_fintype ι
  rw [← LinearMap.det_toMatrix', toMatrix'_pi_compRingHom, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, LinearMap.det_toMatrix']

/-- An injective homomorphism into an integral domain preserves and reflects linear
independence of forms. The system need not be square, nor have finitely many forms. -/
theorem linearIndependent_compRingHom_iff_of_injective [IsDomain S]
    {L : κ → Dual R (ι → R)} {f : R →+* S} (hf : Function.Injective f) :
    LinearIndependent S (fun i ↦ (L i).compRingHom f) ↔ LinearIndependent R L := by
  let := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).2 hf
  rw [linearIndependent_compRingHom_iff_comp, linearIndependent_iff_apply_basis (Pi.basisFun R ι),
    ← f.algebraMap_toAlgebra]
  exact linearIndependent_algebraMap_comp_iff

end CommRing

section Field

variable {R S ι κ : Type*} [Field R] [CommSemiring S] [Nontrivial S] [Finite ι]

/-- Transport from a field preserves and reflects linear independence of forms. -/
@[simp]
theorem linearIndependent_compRingHom_iff {L : κ → Dual R (ι → R)} {f : R →+* S} :
    LinearIndependent S (fun i ↦ (L i).compRingHom f) ↔ LinearIndependent R L := by
  let := f.toAlgebra
  rw [linearIndependent_compRingHom_iff_comp, linearIndependent_iff_apply_basis (Pi.basisFun R ι),
    ← f.algebraMap_toAlgebra]
  exact TauCeti.linearIndependent_algebraMap_comp_iff_of_field

end Field

section Examples

variable {K F E ι κ : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Finite ι]

-- Extending coefficients and then conjugating preserves independence of the whole system.
example (L : κ → Dual F (ι → F)) (hL : LinearIndependent F L) (f : F →ₐ[K] E)
    (σ : E ≃ₐ[K] E) :
    LinearIndependent E (fun i ↦ ((L i).compRingHom f.toRingHom).compRingHom σ.toRingHom) := by
  simpa using hL

-- On base-field points, the new value is the conjugate of the extended original value.
example (L : Dual F (ι → F)) (f : F →ₐ[K] E) (σ : E ≃ₐ[K] E) (x : ι → K) :
    (L.compRingHom ((σ : E →+* E).comp (f : F →+* E)))
      (fun i ↦ algebraMap K E (x i)) = σ (f (L (fun i ↦ algebraMap K F (x i)))) := by
  rw [← compRingHom_compRingHom]
  simp

end Examples

end Module.Dual
