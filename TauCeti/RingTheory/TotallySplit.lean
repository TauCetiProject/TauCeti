/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import TauCeti.Algebra.Algebra.Pi

/-!
# Finite algebras over a field with many characters are totally split

A finite-dimensional commutative algebra `A` over a field `K` has at most `finrank K A` characters
`A →ₐ[K] K` (Mathlib's `card_algHom_le_finrank`). When it has that many, evaluation at the
characters identifies `A` with the algebra of `K`-valued functions on them
(`TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card`), so `A` is totally split
(`Algebra.IsFiniteSplit`), and in particular étale over `K`. Conversely, a totally split algebra
has exactly `finrank K A` characters (`Algebra.IsFiniteSplit.card_algHom_eq_finrank`) and is the
algebra of functions on them (`Algebra.IsFiniteSplit.pi_id_bijective`).

Geometrically: a finite scheme over a field with as many rational points as its degree is a
disjoint union of copies of the base. This is the criterion used to show that the `n`-torsion of an
elliptic curve over a separably closed field in which `n` is invertible is étale.

## Main results

* `Algebra.IsFiniteSplit.of_finrank_le_card_algHom`: a finite-dimensional commutative algebra over
  a field with at least `finrank K A` characters is totally split.
* `Algebra.IsFiniteSplit.card_algHom_eq_finrank`: a totally split algebra has exactly
  `finrank K A` characters.
* `Algebra.IsFiniteSplit.pi_id_bijective`: evaluation at all characters identifies a totally split
  algebra over a field with the algebra of functions on its characters.
* `TauCeti.Algebra.IsFiniteSplit.tensorProductEquivPi`: the splitting over a field `Ω` indexed
  by the `Ω`-points of the original algebra.
* `TauCeti.Algebra.IsFiniteSplit.tensorProductEquivPiBaseChange`: the same splitting after
  extending scalars to an `Ω`-algebra.
* `TauCeti.Algebra.IsFiniteSplit.algHomTensorProductEquivPi`: the corresponding decomposition
  of maps into the base-changed algebra.
-/

public section

/-- **A finite algebra over a field with as many characters as its dimension is totally split.**
If a finite-dimensional commutative algebra `A` over a field `K` has at least `finrank K A`
characters `A →ₐ[K] K`, then `A` is isomorphic to a finite product of copies of `K`; in
particular it is étale over `K`. -/
theorem Algebra.IsFiniteSplit.of_finrank_le_card_algHom {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Module.Finite K A] (h : Module.finrank K A ≤ Nat.card (A →ₐ[K] K)) :
    Algebra.IsFiniteSplit K A := by
  have := Finite.algHom K A K
  exact .of_algEquiv
    (AlgEquiv.ofBijective _ (TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card h)).symm

/-- **A totally split algebra has as many characters as its dimension.** If `A` is isomorphic to
a finite product of copies of the field `K`, then it has exactly `finrank K A` characters
`A →ₐ[K] K`. -/
theorem Algebra.IsFiniteSplit.card_algHom_eq_finrank {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.IsFiniteSplit K A] :
    Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun K A
  rw [Nat.card_congr (e.arrowCongr AlgEquiv.refl), ← Nat.card_congr (Pi.evalAlgHomEquiv K _),
    e.toLinearEquiv.finrank_eq]
  simp

/-- **A totally split algebra is the algebra of functions on its characters.** If `A` is
isomorphic to a finite product of copies of the field `K`, then evaluation at all characters
`A →ₐ[K] K` is an isomorphism from `A` onto the algebra of `K`-valued functions on them. -/
theorem Algebra.IsFiniteSplit.pi_id_bijective {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.IsFiniteSplit K A] :
    Function.Bijective (AlgHom.pi fun χ : A →ₐ[K] K ↦ χ) := by
  exact TauCeti.AlgHom.pi_id_bijective_of_finrank_le_card card_algHom_eq_finrank.ge

open scoped TensorProduct
open Algebra.TensorProduct

namespace TauCeti.Algebra.IsFiniteSplit

variable (K Ω A : Type*) [Field K] [Field Ω] [Algebra K Ω] [CommRing A] [Algebra K A]

/-- If `Ω ⊗[K] A` is totally split, evaluation identifies it with the algebra of functions on
the `Ω`-valued points of `A`. It sends `ω ⊗ a` to `φ ↦ ω * φ a`. In particular, this applies
to an étale `K`-algebra over a separably closed extension `Ω`. -/
noncomputable def tensorProductEquivPi [_root_.Algebra.IsFiniteSplit Ω (Ω ⊗[K] A)] :
    Ω ⊗[K] A ≃ₐ[Ω] ((A →ₐ[K] Ω) → Ω) :=
  AlgEquiv.ofBijective (AlgHom.pi fun φ ↦ Algebra.TensorProduct.liftEquivRight K Ω A Ω φ) <| by
    -- Points of `A` with values in `Ω` are the characters of the totally split `Ω`-algebra
    -- `Ω ⊗[K] A`, and evaluation at those characters is bijective.
    have h : (AlgHom.pi fun φ ↦ Algebra.TensorProduct.liftEquivRight K Ω A Ω φ : Ω ⊗[K] A → _) =
        (Algebra.TensorProduct.liftEquivRight K Ω A Ω).symm.arrowCongr (Equiv.refl Ω) ∘
          (AlgHom.pi fun χ : Ω ⊗[K] A →ₐ[Ω] Ω ↦ χ) := by
      ext t φ
      simp
    rw [h]
    exact (Equiv.bijective _).comp _root_.Algebra.IsFiniteSplit.pi_id_bijective

variable {K Ω A} in
/-- The splitting sends `ω ⊗ a` to the function `φ ↦ ω * φ a`. -/
@[simp]
theorem tensorProductEquivPi_tmul [_root_.Algebra.IsFiniteSplit Ω (Ω ⊗[K] A)] (ω : Ω) (a : A)
    (φ : A →ₐ[K] Ω) : tensorProductEquivPi K Ω A (ω ⊗ₜ a) φ = ω * φ a := by
  simp [tensorProductEquivPi]

variable (C : Type*) [CommRing C] [Algebra A C]
variable (T : Type*) [CommRing T] [Algebra K T] [Algebra Ω T]
  [IsScalarTower K Ω T] [_root_.Algebra.IsFiniteSplit Ω (Ω ⊗[K] A)]

/-- If `Ω` splits `A`, extending scalars to any `Ω`-algebra `T` gives the algebra of
`T`-valued functions on the `Ω`-points of `A`. -/
noncomputable def tensorProductEquivPiBaseChange :
    T ⊗[K] A ≃ₐ[T] ((A →ₐ[K] Ω) → T) := by
  classical
  let e := Algebra.TensorProduct.liftEquivRight K Ω A Ω
  letI : Finite (A →ₐ[K] Ω) := Finite.of_injective e e.injective
  letI := Fintype.ofFinite (A →ₐ[K] Ω)
  exact (Algebra.TensorProduct.cancelBaseChange K Ω T T A).symm.trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl (tensorProductEquivPi K Ω A)).trans <|
    Algebra.TensorProduct.piScalarRight Ω T T (A →ₐ[K] Ω)

/-- The coordinate at `φ` of a pure tensor `t ⊗ a` is the product of `t`
with the image of `φ a` in `T`. -/
@[simp]
theorem tensorProductEquivPiBaseChange_tmul (t : T) (a : A) (φ : A →ₐ[K] Ω) :
    tensorProductEquivPiBaseChange K Ω A T (t ⊗ₜ[K] a) φ = algebraMap Ω T (φ a) * t := by
  simp [tensorProductEquivPiBaseChange, Algebra.smul_def]

variable {K Ω A T}

/-- On `A ⊗[K] T`, the `φ`-coordinate of the splitting is the tensor product map
induced by `A → Ω → T` and the identity of `T`. -/
theorem evalAlgHom_comp_tensorProductEquivPiBaseChange_comm (φ : A →ₐ[K] Ω) :
    (Pi.evalAlgHom K _ φ).comp
      (((tensorProductEquivPiBaseChange K Ω A T).restrictScalars K).toAlgHom.comp
        (Algebra.TensorProduct.comm K A T).toAlgHom) =
      productMap ((IsScalarTower.toAlgHom K Ω T).comp φ) (AlgHom.id K T) := by
  apply ext'
  intro a t
  simp

variable (K Ω A T)

/-- If `Ω` splits `A`, an `A`-algebra map `C → A ⊗[K] T` amounts to a family of
ring maps `C → T` indexed by the `Ω`-points `φ` of `A`, each extending `A → Ω → T`. -/
noncomputable def algHomTensorProductEquivPi :
    (C →ₐ[A] A ⊗[K] T) ≃
      ((φ : A →ₐ[K] Ω) → {f : C →+* T // f.comp (algebraMap A C) = (algebraMap Ω T).comp φ}) :=
  let e : A ⊗[K] T ≃ₐ[K] ((A →ₐ[K] Ω) → T) :=
    (Algebra.TensorProduct.comm K A T).trans
      ((tensorProductEquivPiBaseChange K Ω A T).restrictScalars K)
  have he (t : A ⊗[K] T) (φ : A →ₐ[K] Ω) :
      e t φ = productMap ((IsScalarTower.toAlgHom K Ω T).comp φ) (AlgHom.id K T) t := by
    simpa only [e, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Pi.evalAlgHom_apply,
      AlgEquiv.coe_restrictScalars, AlgEquiv.trans_apply] using
      AlgHom.congr_fun (evalAlgHom_comp_tensorProductEquivPiBaseChange_comm (T := T) φ) t
  { toFun g φ :=
      ⟨(productMap ((IsScalarTower.toAlgHom K Ω T).comp φ) (AlgHom.id K T)).toRingHom.comp
        g.toRingHom, RingHom.ext fun a ↦ by simp⟩
    invFun f :=
      { toRingHom := e.symm.toRingHom.comp (RingHom.pi fun φ ↦ (f φ).val)
        commutes' a := e.symm_apply_eq.2 <| funext fun φ ↦ by
          rw [he]
          simpa using RingHom.congr_fun (f φ).property a }
    left_inv g := AlgHom.ext fun c ↦ e.symm_apply_eq.2 <| funext fun φ ↦ (he _ φ).symm
    right_inv f := funext fun φ ↦ Subtype.ext <| RingHom.ext fun c ↦
      (he _ φ).symm.trans (congrFun (e.apply_symm_apply fun φ ↦ (f φ).val c) φ) }

variable {K Ω A C T}

/-- The `φ`-component of the splitting evaluates the image of `c` along `a ⊗ t ↦ φ(a)t`,
where `φ(a)` is mapped from `Ω` into `T`. -/
@[simp]
theorem algHomTensorProductEquivPi_apply
    (g : C →ₐ[A] A ⊗[K] T) (φ : A →ₐ[K] Ω) (c : C) :
    (algHomTensorProductEquivPi K Ω A C T g φ : C →+* T) c =
      productMap ((IsScalarTower.toAlgHom K Ω T).comp φ) (AlgHom.id K T) (g c) :=
  (rfl)

/-- Evaluating the map assembled from a family `f` along `φ` recovers the component `f φ`. -/
@[simp]
theorem productMap_algHomTensorProductEquivPi_symm_apply
    (f : (φ : A →ₐ[K] Ω) → {f : C →+* T // f.comp (algebraMap A C) = (algebraMap Ω T).comp φ})
    (φ : A →ₐ[K] Ω) (c : C) :
    productMap ((IsScalarTower.toAlgHom K Ω T).comp φ) (AlgHom.id K T)
      ((algHomTensorProductEquivPi K Ω A C T).symm f c) = (f φ : C →+* T) c := by
  rw [← algHomTensorProductEquivPi_apply, Equiv.apply_symm_apply]

end TauCeti.Algebra.IsFiniteSplit
