/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI
public import TauCeti.GroupTheory.Coprod.Factors
import TauCeti.Algebra.Group.ULift
import TauCeti.GroupTheory.PushoutI.Map

/-!
# Amalgamating a free product along its first factor

For a homomorphism `φ : H →* G` of monoids and a monoid `Q`, the amalgamated product
`G ∗_H (H ∗ Q)` of `G` and the free product `H ∗ Q`, along `φ` and the inclusion of the factor `H`,
is the free product `G ∗ Q`: the amalgamation identifies the factor `H` of `H ∗ Q` with its image
`φ(H)` in `G`, and the free factor `Q` is left untouched. Both monoids have the same universal
property, that of a pair of homomorphisms on `G` and on `Q`. The two factors `G` and `H ∗ Q`, which
may lie in different universes, form the family `Monoid.Coprod.Factors G (H ∗ Q)` of their `ULift`s
indexed by `Bool`.

For a further homomorphism `ψ : Q →* G`, the amalgamated product `G ∗_H (H ∗ Q)` maps to the double
`G ∗_H G` of `G` along `φ` by the identity on `G` and by `φ` together with `ψ` on `H ∗ Q`. For
groups, this homomorphism is injective when `φ` together with `ψ` is an injective homomorphism
`H ∗ Q →* G`.

## Main definitions

* `Monoid.PushoutI.freeFactorMap φ`: the two homomorphisms from `H` that are amalgamated: `φ`
  into `G`, and the inclusion `inl` of the first factor into `H ∗ Q`.
* `Monoid.PushoutI.freeFactorEquiv φ`: the isomorphism `G ∗_H (H ∗ Q) ≃* G ∗ Q`.
* `Monoid.PushoutI.freeFactorToDouble φ ψ`: the homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G`.

## Main results

* `Monoid.PushoutI.freeFactorToDouble_injective`: `freeFactorToDouble φ ψ` is injective when
  `Monoid.Coprod.lift φ ψ` is.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 (amalgamated products and their universal property).
-/

public section

namespace Monoid.PushoutI

open Monoid.Coprod

variable {G H Q : Type*}

section Monoid

variable [Monoid G] [Monoid H] [Monoid Q]

/-- The two homomorphisms from `H` amalgamated in `G ∗_H (H ∗ Q)`, into the factors
`Factors G (H ∗ Q)`: `φ` into `G` and the inclusion `inl` of the first factor into `H ∗ Q`. -/
def freeFactorMap (φ : H →* G) : ∀ b, H →* Factors G (H ∗ Q) b
  | false => MulEquiv.ulift.symm.toMonoidHom.comp φ
  | true => MulEquiv.ulift.symm.toMonoidHom.comp inl

@[simp]
theorem freeFactorMap_false (φ : H →* G) :
    freeFactorMap (Q := Q) φ false = MulEquiv.ulift.symm.toMonoidHom.comp φ :=
  (rfl)

@[simp]
theorem freeFactorMap_true (φ : H →* G) :
    freeFactorMap (Q := Q) φ true = MulEquiv.ulift.symm.toMonoidHom.comp inl :=
  (rfl)

-- The domain of `of true` is written `ULift (H ∗ Q)`, the reduced form of `Factors G (H ∗ Q) true`
-- under which `simp` looks the terms it rewrites up; the discrimination tree would otherwise store
-- it unreduced, and the lemma would never fire.
/-- The amalgamation identifies `h ∈ H` in the factor `H ∗ Q` with `φ h ∈ G`. -/
@[simp]
theorem of_true_up_inl_freeFactorMap (φ : H →* G) (h : H) :
    @DFunLike.coe (ULift (H ∗ Q) →* PushoutI (freeFactorMap (Q := Q) φ)) (ULift (H ∗ Q)) _ _
      (of (φ := freeFactorMap φ) true) (ULift.up (inl h)) =
      of (φ := freeFactorMap φ) false (ULift.up (φ h)) :=
  (of_apply_eq_base (freeFactorMap φ) true h).trans
    (of_apply_eq_base (freeFactorMap φ) false h).symm

/-- The homomorphisms from the factors of `G ∗_H (H ∗ Q)` to `G ∗ Q`: the inclusion of `G`, and
`φ` on `H` together with the inclusion of `Q`. -/
private def toCoprod (φ : H →* G) : ∀ b, Factors G (H ∗ Q) b →* G ∗ Q
  | false => inl.comp MulEquiv.ulift.toMonoidHom
  | true => (Coprod.map φ (.id Q)).comp MulEquiv.ulift.toMonoidHom

/-- **Amalgamating a free product along its first factor.** For `φ : H →* G`, the amalgamated
product `G ∗_H (H ∗ Q)` is the free product `G ∗ Q`: `g ∈ G` and `q ∈ Q` are sent to themselves,
and `h ∈ H` to `φ h`. -/
def freeFactorEquiv (φ : H →* G) : PushoutI (freeFactorMap (Q := Q) φ) ≃* G ∗ Q :=
  MonoidHom.toMulEquiv
    (lift (toCoprod φ) (inl.comp φ) fun b => by cases b <;> ext <;> simp [toCoprod])
    (Coprod.lift ((of (φ := freeFactorMap φ) false).comp MulEquiv.ulift.symm.toMonoidHom)
      ((of (φ := freeFactorMap φ) true).comp (MulEquiv.ulift.symm.toMonoidHom.comp inr)))
    (hom_ext_nonempty fun b => by
      cases b
      · ext; simp [toCoprod]
      · -- Homomorphisms out of `ULift (H ∗ Q)` are compared on `H ∗ Q`.
        let e : H ∗ Q ≃* ULift (H ∗ Q) := MulEquiv.ulift.symm
        rw [← MonoidHom.cancel_right (f := e.toMonoidHom) e.surjective]
        ext <;> simp [toCoprod, e])
    (by ext <;> simp [toCoprod])

variable (φ : H →* G)

-- The factor element is `no_index`: the discrimination tree would store the type
-- `Factors G (H ∗ Q) false` of `of false` unreduced, and the lemma would never fire.
@[simp]
theorem freeFactorEquiv_of_false (x : ULift G) :
    freeFactorEquiv (Q := Q) φ (no_index (of false x)) = inl x.down := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_of_true (x : ULift (H ∗ Q)) :
    freeFactorEquiv φ (no_index (of (φ := freeFactorMap φ) true x)) =
      Coprod.map φ (.id Q) x.down := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_base (h : H) :
    freeFactorEquiv (Q := Q) φ (base (freeFactorMap φ) h) = inl (φ h) := by
  simp [freeFactorEquiv]

@[simp]
theorem freeFactorEquiv_symm_inl (g : G) :
    (freeFactorEquiv (Q := Q) φ).symm (inl g) = of false (ULift.up g) := by
  simp [freeFactorEquiv]

@[simp]
theorem freeFactorEquiv_symm_inr (q : Q) :
    (freeFactorEquiv φ).symm (inr q) = of (φ := freeFactorMap φ) true (ULift.up (inr q)) := by
  simp [freeFactorEquiv]

-- The domain `Factors G (H ∗ Q) b` of the composite is `no_index`, for the reason given at
-- `freeFactorEquiv_of_false`.
/-- On the factor `G`, `freeFactorEquiv φ` is the inclusion of `G`. -/
@[simp]
theorem freeFactorEquiv_comp_of_false :
    (MonoidHom.ofClass (freeFactorEquiv (Q := Q) φ)).comp (M := no_index (Factors G (H ∗ Q) false))
        (of false) =
      inl.comp MulEquiv.ulift.toMonoidHom := by
  ext; simp

/-- On the factor `H ∗ Q`, `freeFactorEquiv φ` is `φ` on `H` and the inclusion on `Q`. -/
@[simp]
theorem freeFactorEquiv_comp_of_true :
    (MonoidHom.ofClass (freeFactorEquiv φ)).comp (M := no_index (Factors G (H ∗ Q) true))
        (of (φ := freeFactorMap (Q := Q) φ) true) =
      (Coprod.map φ (.id Q)).comp MulEquiv.ulift.toMonoidHom := by
  ext; simp

/-- On `G`, the inverse of `freeFactorEquiv φ` is the inclusion of the factor `G`. -/
@[simp]
theorem freeFactorEquiv_symm_comp_inl :
    (MonoidHom.ofClass (freeFactorEquiv (Q := Q) φ).symm).comp inl =
      (of false).comp MulEquiv.ulift.symm.toMonoidHom := by
  ext; simp

/-- On `Q`, the inverse of `freeFactorEquiv φ` is the inclusion of `Q` into the factor `H ∗ Q`. -/
@[simp]
theorem freeFactorEquiv_symm_comp_inr :
    (MonoidHom.ofClass (freeFactorEquiv φ).symm).comp inr =
      (of (φ := freeFactorMap (Q := Q) φ) true).comp
        (MulEquiv.ulift.symm.toMonoidHom.comp inr) := by
  ext; simp

/-- The homomorphisms from the factors `G` and `H ∗ Q` of `G ∗_H (H ∗ Q)` to `G`: the identity, and
`φ` together with `ψ`. -/
private def toDoubleFactor (ψ : Q →* G) : ∀ b, Factors G (H ∗ Q) b →* G
  | false => MulEquiv.ulift.toMonoidHom
  | true => (Coprod.lift φ ψ).comp MulEquiv.ulift.toMonoidHom

private theorem toDoubleFactor_comp_freeFactorMap (ψ : Q →* G) (b : Bool) :
    (toDoubleFactor φ ψ b).comp (freeFactorMap φ b) = φ := by
  cases b <;> ext <;> simp [toDoubleFactor]

-- `noncomputable`: compiled code may only use `map` from a public import, and this file imports
-- `TauCeti.GroupTheory.PushoutI.Map` privately.
/-- The homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G` to the double of `G` along `φ` that is the identity
from `G` to the first copy of `G`, and `φ` together with `ψ : Q →* G` from `H ∗ Q` to the second
copy: the homomorphism of amalgamated products induced by these maps of the factors. -/
noncomputable def freeFactorToDouble (ψ : Q →* G) :
    PushoutI (freeFactorMap (Q := Q) φ) →* PushoutI fun _ : Bool => φ :=
  map (toDoubleFactor φ ψ) (.id H) fun b => by
    rw [toDoubleFactor_comp_freeFactorMap, MonoidHom.comp_id]

variable (ψ : Q →* G)

-- The factor elements are `no_index`, as in `freeFactorEquiv_of_false`.
@[simp]
theorem freeFactorToDouble_of_false (x : ULift G) :
    freeFactorToDouble φ ψ (no_index (of false x)) = of false x.down := by
  rw [freeFactorToDouble, map_of]
  simp [toDoubleFactor]

@[simp]
theorem freeFactorToDouble_of_true (x : ULift (H ∗ Q)) :
    freeFactorToDouble φ ψ (no_index (of (φ := freeFactorMap φ) true x)) =
      of true (Coprod.lift φ ψ x.down) := by
  rw [freeFactorToDouble, map_of]
  simp [toDoubleFactor]

@[simp]
theorem freeFactorToDouble_base (h : H) :
    freeFactorToDouble φ ψ (base (freeFactorMap φ) h) = base _ h := by
  rw [freeFactorToDouble, map_base, MonoidHom.id_apply]

-- The domain of the composite is `no_index`, as in `freeFactorEquiv_comp_of_false`.
/-- On the factor `G`, `freeFactorToDouble φ ψ` is the inclusion of the first copy of `G`. -/
@[simp]
theorem freeFactorToDouble_comp_of_false :
    (freeFactorToDouble φ ψ).comp (M := no_index (Factors G (H ∗ Q) false)) (of false) =
      (of false).comp MulEquiv.ulift.toMonoidHom := by
  ext; simp

/-- On the factor `H ∗ Q`, `freeFactorToDouble φ ψ` is `φ` together with `ψ`, followed by the
inclusion of the second copy of `G`. -/
@[simp]
theorem freeFactorToDouble_comp_of_true :
    (freeFactorToDouble φ ψ).comp (M := no_index (Factors G (H ∗ Q) true))
        (of (φ := freeFactorMap φ) true) =
      (of true).comp ((Coprod.lift φ ψ).comp MulEquiv.ulift.toMonoidHom) := by
  ext; simp

end Monoid

/-- The homomorphism `G ∗_H (H ∗ Q) →* G ∗_H G` is injective when `φ` together with `ψ` is an
injective homomorphism `H ∗ Q →* G`. -/
theorem freeFactorToDouble_injective [Group G] [Group H] [Group Q] {φ : H →* G} {ψ : Q →* G}
    (hφψ : Function.Injective (Coprod.lift φ ψ)) : Function.Injective (freeFactorToDouble φ ψ) := by
  have hφ : Function.Injective φ := fun a b hab => inl_injective (hφψ (by simpa using hab))
  rw [freeFactorToDouble]
  refine map_injective _ (fun _ => hφ) Function.injective_id fun b g ⟨h, hh⟩ => ⟨h, ?_⟩
  cases b
  · simpa [toDoubleFactor, ULift.ext_iff] using hh
  · -- An element of `H ∗ Q` mapped into `φ(H)` lies in the first factor.
    simpa [ULift.ext_iff] using hφψ (by simpa [toDoubleFactor] using hh)

end Monoid.PushoutI
