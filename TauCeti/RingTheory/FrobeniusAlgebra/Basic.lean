/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Frobenius functionals

A *Frobenius functional* on an algebra `A` over a field `k` is a `k`-linear map `λ : A → k` whose
pairing `(a, b) ↦ λ (a * b)` is nondegenerate on both sides; an algebra carrying one is a Frobenius
algebra. The pairing is automatically associative, `λ ((a * b) * c) = λ (a * (b * c))`, because it
is computed from the product of all three factors.

The point of the notion is the isomorphism `A ≃ A⁺` it produces, where `A⁺ = Module.Dual k A`
carries the right `A`-action `(φ · b) c = φ (b * c)`. Writing that action out, right `A`-linearity
of a map `e : A → A⁺` is the equation `e (a * b) = (e a) ∘ₗ LinearMap.mulLeft k b`, and
`TauCeti.nonempty_frobeniusFunctional_iff` says that on a finite-dimensional algebra the Frobenius
functionals are exactly the right `A`-linear isomorphisms `A ≃ₗ[k] A⁺`: a functional `λ` gives
`TauCeti.FrobeniusFunctional.toDual`, `a ↦ λ (a * ·)`, and an isomorphism `e` gives back the
functional `e 1`. Pairing on the other side gives the left `A`-linear isomorphism
`TauCeti.FrobeniusFunctional.toDualFlip`, `b ↦ λ (· * b)`.

The failure of a Frobenius functional to be a trace is measured by its **Nakayama automorphism**
`ν`, the unique algebra automorphism with `λ (a * b) = λ (b * ν a)`, obtained by comparing those
two isomorphisms. It is the identity exactly when `λ (a * b) = λ (b * a)`, which is the extra datum
recorded by `TauCeti.SymmetricFrobeniusFunctional`.

Nondegeneracy is the right condition over a field, where a finite-dimensional space has the same
dimension as its dual; over a general commutative base ring one asks instead for the pairing to be
perfect, and that theory is not developed here.

## Main definitions

* `TauCeti.FrobeniusFunctional`: a linear functional whose multiplication pairing is nondegenerate
  on both sides.
* `TauCeti.SymmetricFrobeniusFunctional`: a Frobenius functional that is a trace.
* `TauCeti.FrobeniusFunctional.pairing`: the pairing `(a, b) ↦ λ (a * b)`.
* `TauCeti.FrobeniusFunctional.toDual` and `TauCeti.FrobeniusFunctional.toDualFlip`: the induced
  isomorphisms onto the `k`-linear dual.
* `TauCeti.FrobeniusFunctional.nakayama`: the Nakayama automorphism.
* `TauCeti.FrobeniusFunctional.op`: the Frobenius functional transported to the opposite algebra.

## Main results

* `TauCeti.nonempty_frobeniusFunctional_iff`: a finite-dimensional algebra admits a Frobenius
  functional if and only if it is isomorphic to its `k`-linear dual as a right module over itself.
* `TauCeti.FrobeniusFunctional.eq_nakayama`: the Nakayama automorphism is the unique map with
  `λ (a * b) = λ (b * ν a)`.
* `TauCeti.FrobeniusFunctional.nakayama_eq_refl_iff`: it is the identity exactly for a trace.

## References

* T. Y. Lam, *Lectures on modules and rings* (GTM 189, 1999), Section 16.
* Y. Nakayama, *On Frobeniusean algebras. II*, Ann. of Math. 42 (1941), 1–21.
-/

public section

namespace TauCeti

open LinearMap (BilinForm)

variable (k A : Type*) [Field k] [Ring A] [Algebra k A]

/-- A **Frobenius functional** on a `k`-algebra `A`: a linear functional whose multiplication
pairing `(a, b) ↦ functional (a * b)` is nondegenerate on both sides. Finite-dimensionality is not
part of the datum; it is a hypothesis of the results that need it, such as the isomorphism with the
dual. The two nondegeneracy fields make the handedness of the pairing explicit; in finite dimension
either one implies the other, which is `TauCeti.FrobeniusFunctional.ofLeftNondegenerate`. -/
structure FrobeniusFunctional where
  /-- The underlying linear functional. -/
  functional : A →ₗ[k] k
  /-- An element pairing to zero with everything on the right vanishes. -/
  left_nondegenerate : ∀ a : A, (∀ b : A, functional (a * b) = 0) → a = 0
  /-- An element pairing to zero with everything on the left vanishes. -/
  right_nondegenerate : ∀ b : A, (∀ a : A, functional (a * b) = 0) → b = 0

/-- A **symmetric Frobenius functional**: a Frobenius functional that is a trace. This is extra
structure on a Frobenius functional, not a property of the algebra: a Frobenius algebra need not
admit a symmetric Frobenius functional. -/
structure SymmetricFrobeniusFunctional extends FrobeniusFunctional k A where
  /-- The functional is a trace. -/
  functional_mul_comm : ∀ a b : A, functional (a * b) = functional (b * a)

variable {k A}

namespace FrobeniusFunctional

@[ext]
theorem ext {F G : FrobeniusFunctional k A} (h : F.functional = G.functional) : F = G := by
  cases F
  cases G
  subst h
  rfl

variable (F : FrobeniusFunctional k A)

/-- The pairing `(a, b) ↦ λ (a * b)` of a Frobenius functional. -/
def pairing : BilinForm k A := (LinearMap.mul k A).compr₂ F.functional

@[simp]
theorem pairing_apply (a b : A) : F.pairing a b = F.functional (a * b) := (rfl)

/-- **The pairing is associative**: it is computed from the product of all three factors, so the
bracketing is immaterial. -/
theorem pairing_mul_assoc (a b c : A) : F.pairing (a * b) c = F.pairing a (b * c) := by
  simp [mul_assoc]

/-- The left nondegeneracy field, read on the pairing. -/
theorem pairing_separatingLeft : F.pairing.SeparatingLeft :=
  fun a ha => F.left_nondegenerate a fun b => by simpa using ha b

/-- The right nondegeneracy field, read on the pairing. -/
theorem pairing_separatingRight : F.pairing.SeparatingRight :=
  fun b hb => F.right_nondegenerate b fun a => by simpa using hb a

/-- The two nondegeneracy fields say exactly that the pairing is nondegenerate. -/
theorem pairing_nondegenerate : F.pairing.Nondegenerate :=
  ⟨F.pairing_separatingLeft, F.pairing_separatingRight⟩

/-- On a finite-dimensional algebra, nondegeneracy on the left already implies nondegeneracy on the
right, so a Frobenius functional can be built from a single nondegeneracy hypothesis. -/
def ofLeftNondegenerate [FiniteDimensional k A] (l : A →ₗ[k] k)
    (h : ∀ a : A, (∀ b : A, l (a * b) = 0) → a = 0) : FrobeniusFunctional k A where
  functional := l
  left_nondegenerate := h
  right_nondegenerate b hb :=
    (LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
      (B := (LinearMap.mul k A).compr₂ l) (fun a ha => h a fun c => by simpa using ha c)).2 b
      fun a => by simpa using hb a

@[simp]
theorem ofLeftNondegenerate_functional [FiniteDimensional k A] (l : A →ₗ[k] k)
    (h : ∀ a : A, (∀ b : A, l (a * b) = 0) → a = 0) :
    (ofLeftNondegenerate l h).functional = l := (rfl)

/-! ### The isomorphisms onto the dual -/

section FiniteDimensional

variable [FiniteDimensional k A]

/-- The isomorphism `A ≃ A⁺` attached to a Frobenius functional, sending `a` to `λ (a * ·)`. It is
right `A`-linear for the action `(φ · b) c = φ (b * c)` on the dual; see
`TauCeti.FrobeniusFunctional.toDual_mul`. -/
noncomputable def toDual : A ≃ₗ[k] Module.Dual k A := F.pairing.toDual F.pairing_nondegenerate

@[simp]
theorem toDual_apply (a b : A) : F.toDual a b = F.functional (a * b) := (rfl)

/-- **The isomorphism onto the dual is right `A`-linear**, for the right action
`(φ · b) c = φ (b * c)` of `A` on its `k`-linear dual. -/
theorem toDual_mul (a b : A) :
    F.toDual (a * b) = (F.toDual a).comp (LinearMap.mulLeft k b) := by
  ext c
  simp [mul_assoc]

/-- The isomorphism `A ≃ A⁺` sending `b` to `λ (· * b)`, that is, the isomorphism attached to the
flipped pairing. It is left `A`-linear, where `TauCeti.FrobeniusFunctional.toDual` is right
`A`-linear, and comparing the two is what defines the Nakayama automorphism. -/
noncomputable def toDualFlip : A ≃ₗ[k] Module.Dual k A :=
  F.pairing.flip.toDual F.pairing_nondegenerate.flip

@[simp]
theorem toDualFlip_apply (b a : A) : F.toDualFlip b a = F.functional (a * b) := (rfl)

/-- **The isomorphism onto the dual attached to the flipped pairing is left `A`-linear**, for the
left action `(b · φ) c = φ (c * b)` of `A` on its `k`-linear dual. -/
theorem toDualFlip_mul (a b : A) :
    F.toDualFlip (a * b) = (F.toDualFlip b).comp (LinearMap.mulRight k a) := by
  ext c
  simp [mul_assoc]

/-- The flipped pairing, read as a map into the dual, is bijective. This is the hypothesis under
which an associative form makes its algebra self-injective. -/
theorem bijective_pairing_flip : Function.Bijective F.pairing.flip := by
  have h : ⇑F.pairing.flip = ⇑F.toDualFlip := by ext b a; simp
  rw [h]
  exact F.toDualFlip.bijective

end FiniteDimensional

/-! ### Recovering the functional from an isomorphism onto the dual -/

private theorem apply_mul_of_comp {e : A ≃ₗ[k] Module.Dual k A}
    (he : ∀ a b : A, e (a * b) = (e a).comp (LinearMap.mulLeft k b)) (a b : A) :
    e a b = e 1 (a * b) := by
  have h := he 1 a
  rw [one_mul] at h
  simp [h]

/-- A right `A`-linear isomorphism of `A` onto its `k`-linear dual is the isomorphism attached to
the Frobenius functional `e 1`. -/
def ofEquiv (e : A ≃ₗ[k] Module.Dual k A)
    (he : ∀ a b : A, e (a * b) = (e a).comp (LinearMap.mulLeft k b)) :
    FrobeniusFunctional k A where
  functional := e 1
  left_nondegenerate a ha := by
    refine e.injective ?_
    ext b
    simpa [apply_mul_of_comp he a b] using ha b
  right_nondegenerate b hb := by
    refine (Module.forall_dual_apply_eq_zero_iff k b).1 fun φ => ?_
    obtain ⟨a, rfl⟩ := e.surjective φ
    rw [apply_mul_of_comp he a b]
    exact hb a

@[simp]
theorem ofEquiv_functional (e : A ≃ₗ[k] Module.Dual k A)
    (he : ∀ a b : A, e (a * b) = (e a).comp (LinearMap.mulLeft k b)) :
    (ofEquiv e he).functional = e 1 := (rfl)

/-- Every right `A`-linear isomorphism onto the dual arises from a Frobenius functional. -/
@[simp]
theorem toDual_ofEquiv [FiniteDimensional k A] (e : A ≃ₗ[k] Module.Dual k A)
    (he : ∀ a b : A, e (a * b) = (e a).comp (LinearMap.mulLeft k b)) :
    (ofEquiv e he).toDual = e := by
  refine LinearEquiv.ext fun a => LinearMap.ext fun b => ?_
  rw [toDual_apply, ofEquiv_functional, ← apply_mul_of_comp he a b]

/-- A Frobenius functional is recovered from the isomorphism onto the dual that it defines. -/
theorem ofEquiv_toDual [FiniteDimensional k A] : ofEquiv F.toDual F.toDual_mul = F := by
  refine ext (LinearMap.ext fun b => ?_)
  rw [ofEquiv_functional, toDual_apply, one_mul]

/-! ### The Nakayama automorphism -/

section Nakayama

variable [FiniteDimensional k A]

private noncomputable def nakayamaEquiv : A ≃ₗ[k] A := F.toDual.trans F.toDualFlip.symm

private theorem functional_mul_nakayamaEquiv (a b : A) :
    F.functional (b * F.nakayamaEquiv a) = F.functional (a * b) := by
  have h : F.toDualFlip (F.nakayamaEquiv a) = F.toDual a := by
    simp [nakayamaEquiv]
  simpa using congrArg (fun φ : Module.Dual k A => φ b) h

private theorem eq_nakayamaEquiv {a c : A}
    (h : ∀ b : A, F.functional (b * c) = F.functional (a * b)) : c = F.nakayamaEquiv a := by
  refine sub_eq_zero.1 (F.right_nondegenerate _ fun b => ?_)
  rw [mul_sub, map_sub, h b, F.functional_mul_nakayamaEquiv a b, sub_self]

private theorem nakayamaEquiv_one : F.nakayamaEquiv 1 = 1 :=
  (F.eq_nakayamaEquiv (a := 1) (c := 1) (by simp)).symm

-- Each rewrite moves the outermost factor of the right-hand argument across the pairing using the
-- defining property, and reassociates for the next one.
private theorem nakayamaEquiv_mul (a b : A) :
    F.nakayamaEquiv (a * b) = F.nakayamaEquiv a * F.nakayamaEquiv b :=
  (F.eq_nakayamaEquiv fun c => by
    rw [← mul_assoc, F.functional_mul_nakayamaEquiv b (c * F.nakayamaEquiv a), ← mul_assoc,
      F.functional_mul_nakayamaEquiv a (b * c), ← mul_assoc]).symm

/-- **The Nakayama automorphism** of a Frobenius functional: the unique algebra automorphism `ν`
with `λ (a * b) = λ (b * ν a)`. It measures the failure of the functional to be a trace. -/
noncomputable def nakayama : A ≃ₐ[k] A :=
  AlgEquiv.ofLinearEquiv F.nakayamaEquiv F.nakayamaEquiv_one F.nakayamaEquiv_mul

/-- The defining property of the Nakayama automorphism. -/
theorem functional_mul_nakayama (a b : A) :
    F.functional (b * F.nakayama a) = F.functional (a * b) :=
  F.functional_mul_nakayamaEquiv a b

/-- **The Nakayama automorphism is the unique map with the defining property**, by nondegeneracy on
the right. -/
theorem eq_nakayama {a c : A} (h : ∀ b : A, F.functional (b * c) = F.functional (a * b)) :
    c = F.nakayama a :=
  F.eq_nakayamaEquiv h

/-- **The Nakayama automorphism is the identity exactly when the functional is a trace.** -/
theorem nakayama_eq_refl_iff :
    F.nakayama = AlgEquiv.refl ↔ ∀ a b : A, F.functional (a * b) = F.functional (b * a) :=
  ⟨fun h a b => by simp [← F.functional_mul_nakayama b a, h],
    fun h => AlgEquiv.ext fun a => (F.eq_nakayama fun b => (h a b).symm).symm⟩

end Nakayama

/-! ### The opposite algebra -/

/-- A Frobenius functional on `A` read on the opposite algebra: the same functional, paired in the
opposite order. This exchanges the two nondegeneracy conditions, and is what turns a statement
about left modules over `A` into the corresponding statement about right modules. -/
def op : FrobeniusFunctional k Aᵐᵒᵖ where
  functional := F.functional.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap
  left_nondegenerate a ha :=
    MulOpposite.unop_injective (F.right_nondegenerate a.unop fun c => ha (MulOpposite.op c))
  right_nondegenerate b hb :=
    MulOpposite.unop_injective (F.left_nondegenerate b.unop fun c => hb (MulOpposite.op c))

@[simp]
theorem op_functional_apply (a : Aᵐᵒᵖ) : F.op.functional a = F.functional a.unop := (rfl)

end FrobeniusFunctional

/-- **A finite-dimensional algebra is a Frobenius algebra exactly when it is isomorphic to its
`k`-linear dual as a right module over itself.** The right action on the dual is
`(φ · b) c = φ (b * c)`, so right `A`-linearity of `e` is the displayed equation. -/
theorem nonempty_frobeniusFunctional_iff [FiniteDimensional k A] :
    Nonempty (FrobeniusFunctional k A) ↔
      ∃ e : A ≃ₗ[k] Module.Dual k A,
        ∀ a b : A, e (a * b) = (e a).comp (LinearMap.mulLeft k b) :=
  ⟨fun ⟨F⟩ => ⟨F.toDual, F.toDual_mul⟩, fun ⟨e, he⟩ => ⟨FrobeniusFunctional.ofEquiv e he⟩⟩

namespace SymmetricFrobeniusFunctional

@[ext]
theorem ext {S T : SymmetricFrobeniusFunctional k A} (h : S.functional = T.functional) : S = T := by
  cases S
  cases T
  congr 1
  exact FrobeniusFunctional.ext h

/-- A symmetric Frobenius functional needs only one nondegeneracy hypothesis, and no
finite-dimensionality: the trace property carries nondegeneracy from one side to the other. -/
def ofLeftNondegenerate (l : A →ₗ[k] k) (hcomm : ∀ a b : A, l (a * b) = l (b * a))
    (h : ∀ a : A, (∀ b : A, l (a * b) = 0) → a = 0) : SymmetricFrobeniusFunctional k A where
  functional := l
  left_nondegenerate := h
  right_nondegenerate b hb := h b fun a => by rw [hcomm]; exact hb a
  functional_mul_comm := hcomm

@[simp]
theorem ofLeftNondegenerate_functional (l : A →ₗ[k] k) (hcomm : ∀ a b : A, l (a * b) = l (b * a))
    (h : ∀ a : A, (∀ b : A, l (a * b) = 0) → a = 0) :
    (ofLeftNondegenerate l hcomm h).functional = l := (rfl)

variable (S : SymmetricFrobeniusFunctional k A)

/-- The pairing of a symmetric Frobenius functional is a symmetric bilinear form. -/
theorem pairing_isSymm : S.toFrobeniusFunctional.pairing.IsSymm :=
  ⟨fun a b => by simpa using S.functional_mul_comm a b⟩

/-- **The Nakayama automorphism of a symmetric Frobenius functional is the identity.** -/
theorem nakayama_eq_refl [FiniteDimensional k A] :
    S.toFrobeniusFunctional.nakayama = AlgEquiv.refl :=
  S.toFrobeniusFunctional.nakayama_eq_refl_iff.2 S.functional_mul_comm

end SymmetricFrobeniusFunctional

end TauCeti
