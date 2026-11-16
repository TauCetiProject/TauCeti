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

* `Coalgebra.handleElement`: `LinearMap.mul' R A (Coalgebra.comul (R := R) (1 : A))`.
* `Coalgebra.handleElement_self`, `Coalgebra.handleElement_tensorProduct`,
  `Coalgebra.handleElement_baseChange`, `Coalgebra.map_handleElement`,
  `AlgEquiv.map_handleElement_of_isFrobenius`: functoriality under tensor products, scalar
  extension, and morphisms.
* `Coalgebra.IsFrobenius.mul'_comul_apply`, `Coalgebra.IsFrobenius.mul'_comul_apply_right`,
  `Coalgebra.IsFrobenius.commute_handleElement`, `Coalgebra.IsFrobenius.mul'_comp_comul_eq_mulLeft`,
  `Coalgebra.IsFrobenius.mul'_comp_comul_pow_apply`: handle-operator identities and centrality.
* `LinearMap.handleElement_frobeniusCoalgebra_eq_sum`,
  `LinearMap.apply_handleElement_frobeniusCoalgebra_eq_card`,
  `Coalgebra.IsFrobenius.counit_handleElement_eq_card`: dual-basis expansion and rank trace formula.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

open TensorProduct

namespace Coalgebra

section Defs

variable (R A : Type*) [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [SMulCommClass R A A] [IsScalarTower R A A] [CoalgebraStruct R A]

/-- The handle element `m (Δ 1)` of a unital algebra equipped with a coalgebra structure. -/
def handleElement : A :=
  LinearMap.mul' R A (comul (R := R) (1 : A))

/-- Unfolding the handle element as `LinearMap.mul' R A (Coalgebra.comul (1 : A))`. -/
theorem handleElement_def :
    handleElement R A = LinearMap.mul' R A (comul (R := R) (1 : A)) := (rfl)

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
  change LinearMap.mul' S (A ⊗[R] B) (comul (R := S) ((1 : A) ⊗ₜ[R] (1 : B))) = _
  rw [handleElement_def, handleElement_def, TensorProduct.comul_tmul]
  induction comul (R := S) (1 : A) using TensorProduct.inductionOn with
  | add u v hu hv => simp only [add_tmul, map_add, hu, hv]
  | tmul u₁ u₂ =>
    induction comul (R := R) (1 : B) using TensorProduct.inductionOn with
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

section Map

variable {R A B : Type*} [CommSemiring R]
  [NonAssocSemiring A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
  [NonAssocSemiring B] [Module R B] [SMulCommClass R B B] [IsScalarTower R B B]
  [CoalgebraStruct R A] [CoalgebraStruct R B]

/-- A coalgebra homomorphism that preserves `1` and multiplication preserves the handle element. -/
theorem map_handleElement (f : A →ₗc[R] B) (h1 : f 1 = 1)
    (hmul : ∀ x y, f (x * y) = f x * f y) :
    f (handleElement R A) = handleElement R B := by
  have hcomul : comul (R := R) (f 1) =
      _root_.TensorProduct.map (f : A →ₗ[R] B) (f : A →ₗ[R] B) (comul (R := R) 1) :=
    (congrArg (fun g : A →ₗ[R] B ⊗[R] B ↦ g 1) f.map_comp_comul).symm
  rw [handleElement_def, handleElement_def, ← h1, hcomul]
  induction comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [hmul]
  | add t u ht hu => simp_all

end Map

end Coalgebra

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [Coalgebra R A] [Coalgebra R B] [Coalgebra.IsFrobenius R A] [Coalgebra.IsFrobenius R B]

/-- A counit-preserving algebra isomorphism between Frobenius coalgebras preserves the handle
element. -/
theorem map_handleElement_of_isFrobenius (e : A ≃ₐ[R] B)
    (hε : Coalgebra.counit (R := R) (A := B) ∘ₗ e.toLinearMap =
      Coalgebra.counit (R := R) (A := A)) :
    e (Coalgebra.handleElement R A) = Coalgebra.handleElement R B := by
  simpa using Coalgebra.map_handleElement (e.toCoalgEquivOfIsFrobenius hε).toCoalgHom
    (by simp) (fun _ _ ↦ by simp)

end AlgEquiv

namespace Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
  [IsFrobenius R A]

/-- The handle operator `m ∘ Δ` acts by left multiplication by the handle element. -/
theorem mul'_comul_apply (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = Coalgebra.handleElement R A * a := by
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ LinearMap.mul' R A (f (1 ⊗ₜ[R] a)))
    (left_eq_comul_comp_mul' (R := R) (A := A))
  simp only [left_def, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
    one_mul] at h
  rw [← h, Coalgebra.handleElement_def]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add t u ht hu => simp_all [add_tmul, add_mul]

/-- The handle operator `m ∘ Δ` acts by right multiplication by the handle element. -/
theorem mul'_comul_apply_right (a : A) :
    LinearMap.mul' R A (Coalgebra.comul (R := R) a) = a * Coalgebra.handleElement R A := by
  have h := congrArg (fun f : A ⊗[R] A →ₗ[R] A ⊗[R] A ↦ LinearMap.mul' R A (f (a ⊗ₜ[R] 1)))
    (right_eq_comul_comp_mul' (R := R) (A := A))
  simp only [right_def, LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
    mul_one] at h
  rw [← h, Coalgebra.handleElement_def]
  induction Coalgebra.comul (R := R) (1 : A) using TensorProduct.inductionOn with
  | tmul u v => simp [mul_assoc]
  | add t u ht hu => simp_all [tmul_add, mul_add]

/-- The handle element of any Frobenius algebra is central. -/
theorem commute_handleElement (a : A) : Commute (Coalgebra.handleElement R A) a :=
  (mul'_comul_apply a).symm.trans (mul'_comul_apply_right a)

/-- The handle operator `m ∘ Δ` equals left multiplication by the handle element. -/
theorem mul'_comp_comul_eq_mulLeft :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A) =
      LinearMap.mulLeft R (Coalgebra.handleElement R A) :=
  LinearMap.ext mul'_comul_apply

/-- The handle operator `m ∘ Δ` equals right multiplication by the handle element. -/
theorem mul'_comp_comul_eq_mulRight :
    LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A) =
      LinearMap.mulRight R (Coalgebra.handleElement R A) :=
  LinearMap.ext mul'_comul_apply_right

/-- Iterating the handle operator `g` times multiplies on the left by `handleElement ^ g`. -/
theorem mul'_comp_comul_pow_apply (g : ℕ) (a : A) :
    ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) ^ g) a =
      Coalgebra.handleElement R A ^ g * a := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [pow_succ', mul_apply_eq_comp, LinearMap.comp_apply, mul'_comul_apply, ih, pow_succ',
      mul_assoc]

/-- Applying the `g`-fold handle operator to `1` yields `handleElement ^ g`. -/
@[simp]
theorem mul'_comp_comul_pow_one (g : ℕ) :
    ((LinearMap.mul' R A ∘ₗ Coalgebra.comul (R := R) (A := A)) ^ g) 1 =
      Coalgebra.handleElement R A ^ g := by
  rw [mul'_comp_comul_pow_apply, mul_one]

end Coalgebra.IsFrobenius

namespace LinearMap

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

/-- In any finite basis `b`, the handle element of `ε.frobeniusCoalgebra` is
`∑ i, b i * traceDualBasis ε b i`. -/
theorem handleElement_frobeniusCoalgebra_eq_sum {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) :
    (letI := ε.frobeniusCoalgebra; Coalgebra.handleElement R A) =
      ∑ i, b i * traceDualBasis ε b i := by
  let := ε.frobeniusCoalgebra
  rw [Coalgebra.handleElement_def, frobeniusCoalgebra_comul_eq_sum ε b 1]
  simp

/-- The trace of the handle element of `ε.frobeniusCoalgebra` equals the rank of any finite
basis. -/
theorem apply_handleElement_frobeniusCoalgebra_eq_card {ι : Type*} [Fintype ι]
    (b : Module.Basis ι R A) :
    ε (letI := ε.frobeniusCoalgebra; Coalgebra.handleElement R A) = Fintype.card ι := by
  classical
  rw [handleElement_frobeniusCoalgebra_eq_sum ε b, map_sum]
  simp [apply_mul_traceDualBasis]

end LinearMap

namespace Coalgebra.IsFrobenius

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Coalgebra R A] [IsFrobenius R A]

/-- In any finite basis `b` of a commutative Frobenius algebra, the counit of the handle element
equals the rank `Fintype.card ι`. -/
theorem counit_handleElement_eq_card {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    Coalgebra.counit (R := R) (Coalgebra.handleElement R A) = Fintype.card ι := by
  have hc : (Coalgebra.counit (R := R) (A := A)).frobeniusCoalgebra = ‹Coalgebra R A› :=
    LinearMap.frobeniusCoalgebra_eq _ _ rfl inferInstance
  have hcard := LinearMap.apply_handleElement_frobeniusCoalgebra_eq_card
    (Coalgebra.counit (R := R) (A := A)) b
  rw [hc] at hcard
  exact hcard

end Coalgebra.IsFrobenius
