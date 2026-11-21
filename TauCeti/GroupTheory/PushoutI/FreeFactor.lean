/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.PushoutI

/-!
# Amalgamating a free product along its first factor

For a homomorphism `φ : H →* G` of groups and a group `Q`, the amalgamated product
`G ∗_H (H ∗ Q)` of `G` and the free product `H ∗ Q`, along `φ` and the inclusion of the factor `H`,
is the free product `G ∗ Q`: the amalgamation identifies the factor `H` of `H ∗ Q` with its image
`φ(H)` in `G`, and the free factor `Q` is left untouched. Both groups have the same universal
property, that of a pair of homomorphisms on `G` and on `Q`.

## Main definitions

* `Monoid.PushoutI.FreeFactor G H Q`: the factors `G` and `H ∗ Q`, as a family indexed by `Bool`.
* `Monoid.PushoutI.freeFactorMap φ`: the two embeddings of `H`, by `φ` and as the first factor.
* `Monoid.PushoutI.freeFactorEquiv φ`: the isomorphism `G ∗_H (H ∗ Q) ≃* G ∗ Q`.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.1 (amalgamated products and their universal property).
-/

public section

universe u

namespace Monoid.PushoutI

open Monoid.Coprod

variable {G H Q : Type u} [Group G] [Group H] [Group Q]

variable (G H Q) in
/-- The factors `G` and `H ∗ Q` of the amalgamated product `G ∗_H (H ∗ Q)`, as a family indexed by
`Bool`: `G` at `false` and `H ∗ Q` at `true`. -/
abbrev FreeFactor (b : Bool) : Type u :=
  Bool.rec (motive := fun _ => Type u) G (H ∗ Q) b

instance (b : Bool) : Group (FreeFactor G H Q b) :=
  Bool.rec (motive := fun b => Group (FreeFactor G H Q b)) (inferInstanceAs (Group G))
    (inferInstanceAs (Group (H ∗ Q))) b

/-- The two embeddings of `H` amalgamated in `G ∗_H (H ∗ Q)`: `φ` into `G` and the inclusion of
the first factor into `H ∗ Q`. -/
def freeFactorMap (φ : H →* G) : ∀ b, H →* FreeFactor G H Q b
  | false => φ
  | true => inl

@[simp]
theorem freeFactorMap_false (φ : H →* G) : freeFactorMap (Q := Q) φ false = φ :=
  (rfl)

@[simp]
theorem freeFactorMap_true (φ : H →* G) : freeFactorMap (Q := Q) φ true = inl :=
  (rfl)

/-- The amalgamation identifies `h ∈ H` in the factor `H ∗ Q` with `φ h ∈ G`. -/
theorem of_true_inl_freeFactorMap (φ : H →* G) (h : H) :
    of (φ := freeFactorMap φ) true (inl h : H ∗ Q) = of (φ := freeFactorMap φ) false (φ h) :=
  (of_apply_eq_base (freeFactorMap φ) true h).trans
    (of_apply_eq_base (freeFactorMap φ) false h).symm

/-- The homomorphisms from the factors of `G ∗_H (H ∗ Q)` to `G ∗ Q`: the inclusion of `G`, and
`φ` on `H` together with the inclusion of `Q`. -/
private def toCoprod (φ : H →* G) : ∀ b, FreeFactor G H Q b →* G ∗ Q
  | false => inl
  | true => map φ (.id Q)

/-- **Amalgamating a free product along its first factor.** For `φ : H →* G`, the amalgamated
product `G ∗_H (H ∗ Q)` is the free product `G ∗ Q`: `g ∈ G` and `q ∈ Q` are sent to themselves,
and `h ∈ H` to `φ h`. -/
def freeFactorEquiv (φ : H →* G) : PushoutI (freeFactorMap (Q := Q) φ) ≃* G ∗ Q :=
  MonoidHom.toMulEquiv
    (lift (toCoprod φ) (inl.comp φ) fun b => by cases b <;> ext <;> simp [toCoprod])
    (Coprod.lift (of (φ := freeFactorMap φ) false) ((of (φ := freeFactorMap φ) true).comp inr))
    (hom_ext_nonempty fun b => by
      cases b
      · ext
        simp [toCoprod]
      · ext x
        · simpa [toCoprod] using (of_true_inl_freeFactorMap φ x).symm
        · simp [toCoprod])
    (by ext <;> simp [toCoprod])

variable (φ : H →* G)

-- The factor element is `no_index`: the discrimination tree would store the type
-- `FreeFactor G H Q false` of `of false` unreduced, and the lemma would never fire.
@[simp]
theorem freeFactorEquiv_of_false (g : G) :
    freeFactorEquiv (Q := Q) φ (no_index (of false g)) = inl g := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_of_true (x : H ∗ Q) :
    freeFactorEquiv φ (no_index (of (φ := freeFactorMap φ) true x)) = map φ (.id Q) x := by
  simp [freeFactorEquiv, toCoprod]

@[simp]
theorem freeFactorEquiv_symm_inl (g : G) :
    (freeFactorEquiv (Q := Q) φ).symm (inl g) = of false g := by
  simp [freeFactorEquiv]

@[simp]
theorem freeFactorEquiv_symm_inr (q : Q) :
    (freeFactorEquiv φ).symm (inr q) = of (φ := freeFactorMap φ) true (inr q) := by
  simp [freeFactorEquiv]

end Monoid.PushoutI
