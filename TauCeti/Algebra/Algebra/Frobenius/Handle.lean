/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Frobenius.Transport

/-!
# The handle element of a Frobenius algebra

For a Frobenius algebra `A` over a commutative semiring `R`, the **handle element** (also called the
Euler or Casimir element) is `h = m (Δ 1) : A`. In 2D TQFT and foam evaluations, `m ∘ Δ` is the
handle-attachment operator on a surface.

## Main definitions and results

* `TauCeti.Coalgebra.handleElement`: `LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A))`.
* `TauCeti.Coalgebra.handleElement_self`, `TauCeti.Coalgebra.handleElement_tensorProduct`,
  `TauCeti.Coalgebra.handleElement_baseChange`, `CoalgHom.map_handleElement`,
  `AlgEquiv.map_handleElement_of_isFrobenius`: functoriality under tensor products, scalar
  extension, and morphisms.
* `TauCeti.Coalgebra.IsFrobenius.mul'_comul_apply`,
  `TauCeti.Coalgebra.IsFrobenius.mul'_comul_apply_right`,
  `TauCeti.Coalgebra.IsFrobenius.commute_handleElement`,
  `TauCeti.Coalgebra.IsFrobenius.mul'_comp_comul_eq_mulLeft`,
  `TauCeti.Coalgebra.IsFrobenius.mul'_comp_comul_pow_apply`: handle-operator identities and
  centrality.
* `LinearMap.handleElement_frobeniusCoalgebra_eq_sum`,
  `LinearMap.apply_handleElement_frobeniusCoalgebra_eq_card`,
  `TauCeti.Coalgebra.IsFrobenius.handleElement_eq_sum`,
  `TauCeti.Coalgebra.IsFrobenius.counit_handleElement_eq_card`: dual-basis expansion and rank trace
  formula.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

open TensorProduct

namespace TauCeti.Coalgebra

section Defs

variable (R A : Type*) [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]

/-- The handle element `m (Δ 1)` of a unital algebra equipped with a coalgebra structure. -/
def handleElement : A :=
  LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A))

/-- Unfolding the handle element as `LinearMap.mul' R A (Coalgebra.comul (1 : A))`. -/
theorem handleElement_def :
    handleElement R A = LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A)) := (rfl)

end Defs

/-- The handle element of the base commutative semiring `R` is `1`. -/
@[simp]
theorem handleElement_self (R : Type*) [CommSemiring R] : handleElement R R = 1 := by
  simp [handleElement]

section TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonAssocSemiring A] [Module R A] [Module S A] [IsScalarTower R S A]
  [SMulCommClass R S A] [SMulCommClass R A A] [IsScalarTower R A A]
  [SMulCommClass S A A] [IsScalarTower S A A]
  [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct S A] [CoalgebraStruct R B]

/-- The handle element of a heterobasic tensor product `A ⊗[R] B` is the pure tensor of the handle
elements of `A` and `B`. -/
@[simp]
theorem handleElement_tensorProduct :
    handleElement S (A ⊗[R] B) = handleElement S A ⊗ₜ[R] handleElement R B := by
  rw [handleElement_def, handleElement_def, handleElement_def, Algebra.TensorProduct.one_def,
    TensorProduct.comul_tmul]
  induction Coalgebra.comul (R := S) (1 : A) using TensorProduct.inductionOn with
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
  | tmul u₁ u₂ =>
    induction Coalgebra.comul (R := R) (1 : B) using TensorProduct.inductionOn with
    | add v w hv hw => simp only [tmul_add, map_add, hv, hw]
    | tmul v₁ v₂ => simp

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [CoalgebraStruct R A]

/-- Extending scalars sends the handle element `h` of `A` to `1 ⊗ₜ h` in `S ⊗[R] A`. -/
theorem handleElement_baseChange :
    handleElement S (S ⊗[R] A) = (1 : S) ⊗ₜ[R] handleElement R A := by
  rw [handleElement_tensorProduct, handleElement_self]

end BaseChange

end TauCeti.Coalgebra

namespace CoalgHom

variable {R A B : Type*} [CommSemiring R]
  [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- A coalgebra homomorphism that preserves `1` and multiplication preserves the handle element. -/
theorem map_handleElement (f : A →ₗc[R] B) (h1 : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f x * f y) :
    f (TauCeti.Coalgebra.handleElement R A) = TauCeti.Coalgebra.handleElement R B := by
  have hcomul : Coalgebra.comul (R := R) (f 1) =
      TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) (Coalgebra.comul (R := R) 1) :=
    (congrArg (fun g : A →ₗ[R] B ⊗[R] B ↦ g 1) f.map_comp_comul).symm
  rw [TauCeti.Coalgebra.handleElement_def, TauCeti.Coalgebra.handleElement_def, ← h1, hcomul]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [hmul]
  | add t u ht hu => simp_all

end CoalgHom

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras preserves the handle
element. -/
theorem map_handleElement_of_isFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    e (TauCeti.Coalgebra.handleElement R A) = TauCeti.Coalgebra.handleElement R B := by
  simpa using (e.toCoalgEquivOfIsFrobenius hε).toCoalgHom.map_handleElement
    (by simp) (fun _ _ ↦ by simp)

end AlgEquiv

namespace TauCeti.Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
  [Coalgebra.IsFrobenius R A]

/-- The handle operator `m ∘ Δ` acts by left multiplication by the handle element. -/
theorem mul'_comul_apply (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = handleElement R A * a := by
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ LinearMap.mul' R A (f (1 ⊗ₜ[R] a)))
    (Coalgebra.IsFrobenius.left_eq_comul_comp_mul' (R := R) (A := A))
  simp only [Coalgebra.IsFrobenius.left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply, one_mul] at h
  rw [← h, handleElement_def]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add t u ht hu => simp_all [add_tmul, add_mul]

/-- The handle operator `m ∘ Δ` acts by right multiplication by the handle element. -/
theorem mul'_comul_apply_right (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = a * handleElement R A := by
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ LinearMap.mul' R A (f (a ⊗ₜ[R] 1)))
    (Coalgebra.IsFrobenius.right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [Coalgebra.IsFrobenius.right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, mul_one] at h
  rw [← h, handleElement_def]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add t u ht hu => simp_all [tmul_add, mul_add]

/-- The handle element of any Frobenius algebra is central. -/
theorem commute_handleElement (a : A) : Commute (handleElement R A) a :=
  (mul'_comul_apply a).symm.trans (mul'_comul_apply_right a)

/-- The handle operator `m ∘ Δ` equals left multiplication by the handle element. -/
theorem mul'_comp_comul_eq_mulLeft :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A) =
      LinearMap.mulLeft R (handleElement R A) :=
  LinearMap.ext mul'_comul_apply

/-- The handle operator `m ∘ Δ` equals right multiplication by the handle element. -/
theorem mul'_comp_comul_eq_mulRight :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A) =
      LinearMap.mulRight R (handleElement R A) :=
  LinearMap.ext mul'_comul_apply_right

/-- Iterating the handle operator `g` times multiplies on the left by `handleElement ^ g`. -/
theorem mul'_comp_comul_pow_apply (g : ℕ) (a : A) :
    ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) ^ g) a =
      handleElement R A ^ g * a := by
  rw [mul'_comp_comul_eq_mulLeft, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply]

/-- Applying the `g`-fold handle operator to `1` yields `handleElement ^ g`. -/
@[simp]
theorem mul'_comp_comul_pow_one (g : ℕ) :
    ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) ^ g) 1 =
      handleElement R A ^ g := by
  rw [mul'_comp_comul_pow_apply, mul_one]

end TauCeti.Coalgebra.IsFrobenius

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- In any finite basis `b`, the handle element of `ε.frobeniusCoalgebra` is
`∑ i, b i * traceDualBasis ε b i`. -/
theorem handleElement_frobeniusCoalgebra_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) :
    (letI := ε.frobeniusCoalgebra; TauCeti.Coalgebra.handleElement R A) =
      ∑ i, b i * traceDualBasis ε b i := by
  let := ε.frobeniusCoalgebra
  rw [TauCeti.Coalgebra.handleElement_def, frobeniusCoalgebra_comul_eq_sum ε b 1]
  simp

/-- The trace of the handle element of `ε.frobeniusCoalgebra` equals the rank of any finite
basis. -/
theorem apply_handleElement_frobeniusCoalgebra_eq_card {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) :
    ε (letI := ε.frobeniusCoalgebra; TauCeti.Coalgebra.handleElement R A) = Fintype.card ι := by
  classical
  rw [handleElement_frobeniusCoalgebra_eq_sum ε b, map_sum]
  simp [apply_mul_traceDualBasis]

end LinearMap

namespace TauCeti.Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Coalgebra R A] [Coalgebra.IsFrobenius R A]

/-- In any finite basis `b` of a commutative Frobenius algebra, the handle element is
`∑ i, b i * traceDualBasis counit b i`. -/
theorem handleElement_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    handleElement R A =
      ∑ i, b i * LinearMap.traceDualBasis (Coalgebra.counit (R := R) (A := A)) b i := by
  have hc : (Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra = ‹Coalgebra R A› :=
    LinearMap.frobeniusCoalgebra_eq _ _ rfl inferInstance
  have hsum := LinearMap.handleElement_frobeniusCoalgebra_eq_sum
    (Coalgebra.counit (R := R) (A := A)) b
  rw [hc] at hsum
  exact hsum

/-- In any finite basis `b` of a commutative Frobenius algebra, the counit of the handle element
equals the rank `Fintype.card ι`. -/
theorem counit_handleElement_eq_card {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    Coalgebra.counit (R := R) (handleElement R A) = Fintype.card ι := by
  have hc : (Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra = ‹Coalgebra R A› :=
    LinearMap.frobeniusCoalgebra_eq _ _ rfl inferInstance
  have hcard := LinearMap.apply_handleElement_frobeniusCoalgebra_eq_card
    (Coalgebra.counit (R := R) (A := A)) b
  rw [hc] at hcard
  exact hcard

end TauCeti.Coalgebra.IsFrobenius
