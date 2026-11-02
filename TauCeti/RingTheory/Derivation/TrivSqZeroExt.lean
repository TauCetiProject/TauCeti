/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations and points of trivial square-zero extensions

An `R`-algebra homomorphism `A →ₐ[R] TrivSqZeroExt B M` into the trivial square-zero extension
of `B` by a `B`-bimodule `M`, lifting a fixed point `A →ₐ[R] B`, is the same data as an
`R`-derivation of `A` valued in `M`. This is the infinitesimal-lifting dictionary specialised to
the square-zero extension `TrivSqZeroExt.fstHom R B M`. For `M = B` it is the dual-number
dictionary (`DualNumber B = TrivSqZeroExt B B`), which identifies the tangent space of a functor
of points with a module of derivations: tangent vectors at a point are exactly the dual-number
points lying over it.

The fixed point is carried by the algebra-tower hypotheses `[Algebra A B]`
`[IsScalarTower R A B]`, as in `Mathlib.RingTheory.Derivation.ToSquareZero`. For an
arbitrary point `φ : A →ₐ[R] B`, instantiate the tower locally with
`letI := φ.toRingHom.toAlgebra` and `IsScalarTower.of_algHom φ` — in a fresh scope
only: installing the instance where an `SMul A B` already exists creates a diamond,
and derivations elaborated before it refer to the old point.

The `B`-bimodule `M` is an `A`-module through the point: `IsScalarTower A B M` and
`IsScalarTower A Bᵐᵒᵖ M` say that `a` acts on either side as `algebraMap A B a`. These are
exactly the compatibilities the Leibniz rule needs, and they hold for `M = B` by instance.

The construction is direct (send `d` to `a ↦ inl (algebraMap A B a) + inr (d a)`),
which keeps `B` an arbitrary semiring, where the ideal-general route through
`Mathlib.RingTheory.Derivation.ToSquareZero` would force a `CommRing`.

## Main declarations

* `derivationToTrivSqZeroExtEquivLift`: `R`-derivations `A → M` are equivalent to lifts
  `A →ₐ[R] TrivSqZeroExt B M` of the structure point along `TrivSqZeroExt.fstHom`.
-/

public section

namespace TauCeti

open TrivSqZeroExt

variable (R A B : Type*) {M : Type*} [CommSemiring R] [CommSemiring A] [Semiring B]
  [AddCommMonoid M] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  [Module B M] [Module Bᵐᵒᵖ M] [SMulCommClass B Bᵐᵒᵖ M]
  [Module R M] [IsScalarTower R B M] [IsScalarTower R Bᵐᵒᵖ M]

variable {A B} in
/-- The first component of a lift of the structure point is that point. -/
private lemma fst_apply_of_comp_eq {ψ : A →ₐ[R] TrivSqZeroExt B M}
    (hψ : (fstHom R B M).comp ψ = IsScalarTower.toAlgHom R A B) (a : A) :
    fst (ψ a) = algebraMap A B a :=
  DFunLike.congr_fun hψ a

variable [Module A M] [IsScalarTower A B M] [IsScalarTower A Bᵐᵒᵖ M]

variable {A B} in
/-- A derivation extends the structure point of the tower to a point of the trivial
square-zero extension: the value at `a` has first component `algebraMap A B a` and second
component `d a`. -/
private def liftOfDerivation (d : Derivation R A M) : A →ₐ[R] TrivSqZeroExt B M where
  toFun a := inl (algebraMap A B a) + inr (d a)
  map_one' := by simp
  map_mul' a b := by ext <;> simp [← MulOpposite.algebraMap_apply]
  map_zero' := by simp
  map_add' a b := by ext <;> simp
  commutes' r := by
    simp [algebraMap_eq_inl', IsScalarTower.algebraMap_apply R A B]

/-- Lifting the structure point of an algebra to a trivial square-zero extension is the same
as giving a derivation: the equivalence between `R`-derivations `A → M` and points
`A →ₐ[R] TrivSqZeroExt B M` lying over the point `A →ₐ[R] B` of the tower. -/
def derivationToTrivSqZeroExtEquivLift :
    Derivation R A M ≃
      {ψ : A →ₐ[R] TrivSqZeroExt B M //
        (fstHom R B M).comp ψ = IsScalarTower.toAlgHom R A B} where
  toFun d := ⟨liftOfDerivation R d, by ext a; simp [liftOfDerivation]⟩
  invFun ψ :=
    { toLinearMap := (sndHom B M).restrictScalars R ∘ₗ ψ.1.toLinearMap
      map_one_eq_zero' := by simp
      leibniz' a b := by
        simp [fst_apply_of_comp_eq R ψ.2, ← MulOpposite.algebraMap_apply] }
  left_inv d := by ext a; simp [liftOfDerivation]
  right_inv ψ := by ext a <;> simp [liftOfDerivation, fst_apply_of_comp_eq R ψ.2]

variable {R A B}

@[simp]
lemma derivationToTrivSqZeroExtEquivLift_apply_fst (d : Derivation R A M) (a : A) :
    fst ((derivationToTrivSqZeroExtEquivLift R A B d : A →ₐ[R] TrivSqZeroExt B M) a) =
      algebraMap A B a := by
  simp [derivationToTrivSqZeroExtEquivLift, liftOfDerivation]

@[simp]
lemma derivationToTrivSqZeroExtEquivLift_apply_snd (d : Derivation R A M) (a : A) :
    snd ((derivationToTrivSqZeroExtEquivLift R A B d : A →ₐ[R] TrivSqZeroExt B M) a) =
      d a := by
  simp [derivationToTrivSqZeroExtEquivLift, liftOfDerivation]

@[simp]
lemma derivationToTrivSqZeroExtEquivLift_symm_apply (ψ : {ψ : A →ₐ[R] TrivSqZeroExt B M //
      (fstHom R B M).comp ψ = IsScalarTower.toAlgHom R A B}) (a : A) :
    (derivationToTrivSqZeroExtEquivLift R A B).symm ψ a = snd (ψ.1 a) := by
  simp [derivationToTrivSqZeroExtEquivLift]

end TauCeti
