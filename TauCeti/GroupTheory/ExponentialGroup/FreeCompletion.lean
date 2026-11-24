/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.ExponentialGroup.Completion
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# The tensor completion of a group over a ring of exponents

For a semiring `A` and a group `G`, the *tensor `A`-completion* of `G` is an `A`-group `G^A` with a
homomorphism `G →* G^A` through which every homomorphism from `G` to an `A`-group factors by a
unique homomorphism commuting with exponentiation (`IsExponentialGroup.IsCompletion`). For a free
group `F` and `A = ℤ[t]` it is Lyndon's free `ℤ[t]`-group `F^{ℤ[t]}`. This file constructs it as
a term model: the formal expressions built from the elements of `G` by products, inverses and
exponents in `A`, modulo the least congruence containing the group laws, the multiplication of
`G` and the axioms of an `A`-group.

## Main definitions

* `TauCeti.ExponentialGroup.Completion A G`: the tensor `A`-completion of `G`.
* `TauCeti.ExponentialGroup.Completion.of`: the completion map `G →* Completion A G`.
* `TauCeti.ExponentialGroup.Completion.instPow`: the exponentiation of `Completion A G` by `A`,
  with which it is an `A`-group (`TauCeti.ExponentialGroup.Completion.instIsExponentialGroup`).
  Both are scoped instances.

## Main results

* `TauCeti.ExponentialGroup.Completion.isCompletion_of`: the universal property.
* `TauCeti.ExponentialGroup.Completion.eq_top_of_range_le`: a subgroup containing the image of
  `G` and closed under exponentiation is everything.
* `TauCeti.ExponentialGroup.Completion.of_injective`: the completion map is injective when `A`
  has a ring homomorphism to `ℤ`, for instance `ℤ[t] → ℤ`, `t ↦ 1`. More generally it is injective
  as soon as `G` embeds in some `A`-group: apply
  `TauCeti.IsExponentialGroup.IsCompletion.injective_of_injective` to `isCompletion_of`.

## Implementation notes

The last axiom of an `A`-group is conditional (`(g h)^a = g^a h^a` when `g` and `h` commute). Its
rule in the defining congruence has the premise `s t ~ t s`, which refers to the congruence being
defined, so the congruence is an inductive relation whose rules include reflexivity, symmetry,
transitivity and compatibility with the operations, and two expressions are equal in `Completion`
exactly when they are related. The formal expressions and the congruence are private, and neither
`Completion` nor its group structure and exponentiation are exposed: the completion is used
through `of`, `eq_top_of_range_le` and the universal property `isCompletion_of`.

The exponentiation of `Completion A G` by `A` and the resulting `A`-group structure are not global
instances: for `A = ℕ` and `A = ℤ` the exponentiation would compete with the usual powers of the
group `Completion A G`, to which it is only propositionally equal. They are scoped instances,
activated by `open scoped TauCeti.ExponentialGroup.Completion`; applying the `IsCompletion` API to
`isCompletion_of` needs them in scope. A specialisation to a fixed ring such as `ℤ[t]` can declare
them as global instances.

## References

* A. G. Myasnikov, V. N. Remeslennikov, D. E. Serbin, *Regular free length functions on Lyndon's
  free `ℤ[t]`-group `F^{ℤ[t]}`*, §2.1.
* O. Kharlampovich, A. Myasnikov, *Irreducible affine varieties over a free group. I*, §1,
  Definition 7.
* A. G. Myasnikov, V. N. Remeslennikov, *Exponential groups. II. Extensions of centralizers and
  tensor completion of CSA-groups*, Internat. J. Algebra Comput. 6 (1996).
-/

public section

universe w uA uG

namespace TauCeti.ExponentialGroup

variable {A : Type uA} {G : Type uG} [Semiring A] [Group G]

namespace Completion

/-- The formal expressions from which the tensor `A`-completion of `G` is built: elements of `G`,
the identity, products, inverses, and exponents in `A`. -/
private inductive Term (A : Type uA) (G : Type uG) : Type (max uA uG)
  /-- An element of `G`. -/
  | of (g : G)
  /-- The identity. -/
  | one
  /-- A product. -/
  | mul (s t : Term A G)
  /-- An inverse. -/
  | inv (s : Term A G)
  /-- A power with exponent in `A`. -/
  | pow (s : Term A G) (a : A)

open Term in
/-- The least congruence on formal expressions containing the group laws, the multiplication of
`G`, and the axioms of an `A`-group. The last rule, `(s t)^a ~ s^a t^a`, has the premise that
`s t ~ t s`. -/
private inductive Rel : Term A G → Term A G → Prop
  | refl (s) : Rel s s
  | symm {s t} : Rel s t → Rel t s
  | trans {s t r} : Rel s t → Rel t r → Rel s r
  | mul_congr {s s' t t'} : Rel s s' → Rel t t' → Rel (mul s t) (mul s' t')
  | inv_congr {s s'} : Rel s s' → Rel (inv s) (inv s')
  | pow_congr {s s'} (a : A) : Rel s s' → Rel (pow s a) (pow s' a)
  | mul_assoc (s t r) : Rel (mul (mul s t) r) (mul s (mul t r))
  | one_mul (s) : Rel (mul one s) s
  | mul_one (s) : Rel (mul s one) s
  | inv_mul_cancel (s) : Rel (mul (inv s) s) one
  | of_mul (g h : G) : Rel (of (g * h)) (mul (of g) (of h))
  | pow_one (s) : Rel (pow s 1) s
  | pow_add (s) (a b : A) : Rel (pow s (a + b)) (mul (pow s a) (pow s b))
  | pow_mul (s) (a b : A) : Rel (pow s (a * b)) (pow (pow s a) b)
  | conj_pow (s t) (a : A) : Rel (pow (mul (mul s t) (inv s)) a) (mul (mul s (pow t a)) (inv s))
  | mul_pow {s t} (a : A) :
      Rel (mul s t) (mul t s) → Rel (pow (mul s t) a) (mul (pow s a) (pow t a))

end Completion

variable (A G) in
/-- The tensor `A`-completion `G^A` of a group `G`: formal expressions in the elements of `G`,
products, inverses and exponents in `A`, modulo the group laws, the multiplication of `G` and the
axioms of an `A`-group. -/
def Completion : Type (max uA uG) :=
  Quot (Completion.Rel (A := A) (G := G))

namespace Completion

@[no_expose] instance : Group (Completion A G) where
  mul := Quot.map₂ Term.mul (fun _ _ _ h => .mul_congr (.refl _) h)
    fun _ _ _ h => .mul_congr h (.refl _)
  one := Quot.mk _ .one
  inv := Quot.map Term.inv fun _ _ h => .inv_congr h
  mul_assoc x y z := Quot.induction_on₃ x y z fun s t r => Quot.sound (.mul_assoc s t r)
  one_mul := Quot.ind fun s => Quot.sound (.one_mul s)
  mul_one := Quot.ind fun s => Quot.sound (.mul_one s)
  inv_mul_cancel := Quot.ind fun s => Quot.sound (.inv_mul_cancel s)

/-- Exponentiation on the tensor completion. It is a scoped instance, activated by
`open scoped TauCeti.ExponentialGroup.Completion`: for `A = ℕ` and `A = ℤ` it would compete with
the usual powers of the group `Completion A G`. -/
@[no_expose] scoped instance instPow : Pow (Completion A G) A :=
  ⟨fun x a => Quot.map (Term.pow · a) (fun _ _ h => .pow_congr a h) x⟩

/-- The tensor completion is an `A`-group. -/
scoped instance instIsExponentialGroup : IsExponentialGroup A (Completion A G) where
  pow_one := Quot.ind fun s => Quot.sound (.pow_one s)
  pow_add := Quot.ind fun s a b => Quot.sound (.pow_add s a b)
  pow_mul := Quot.ind fun s a b => Quot.sound (.pow_mul s a b)
  conj_pow x y a := Quot.induction_on₂ x y fun s t => Quot.sound (.conj_pow s t a)
  mul_pow {x y} := Quot.induction_on₂ x y fun _ _ hc a =>
    Quot.sound (.mul_pow a ((Equivalence.quot_mk_eq_iff ⟨.refl, .symm, .trans⟩ _ _).1 hc.eq))

/-- The completion map `G →* G^A`. -/
def of : G →* Completion A G :=
  MonoidHom.mk' (fun g => Quot.mk _ (.of g)) fun g h => Quot.sound (.of_mul g h)

/-- The tensor completion is generated, as a group with exponents in `A`, by the image of `G`: a
subgroup containing the image of `G` and closed under exponentiation is everything. Myasnikov and
Remeslennikov include this property in their definition of a tensor completion. -/
theorem eq_top_of_range_le {S : Subgroup (Completion A G)} (hS : (of : G →* _).range ≤ S)
    (hpow : ∀ x ∈ S, ∀ a : A, x ^ a ∈ S) : S = ⊤ := by
  refine eq_top_iff.2 ?_
  rintro ⟨s⟩ -
  induction s with
  | of g => exact hS (MonoidHom.mem_range.2 ⟨g, rfl⟩)
  | one => exact S.one_mem
  | mul s t hs ht => exact S.mul_mem hs ht
  | inv s hs => exact S.inv_mem hs
  | pow s a hs => exact hpow _ hs a

section Lift

variable {H : Type*} [Group H] [Pow H A]

private def Term.eval (φ : G →* H) : Term A G → H
  | .of g => φ g
  | .one => 1
  | .mul s t => s.eval φ * t.eval φ
  | .inv s => (s.eval φ)⁻¹
  | .pow s a => s.eval φ ^ a

private theorem Rel.eval_eq [IsExponentialGroup A H] (φ : G →* H) {s t : Term A G} (h : Rel s t) :
    s.eval φ = t.eval φ := by
  induction h with
  | conj_pow _ _ a => exact IsExponentialGroup.conj_pow _ _ a
  | mul_pow a _ ih => exact IsExponentialGroup.mul_pow ih a
  | _ => simp_all [Term.eval, _root_.mul_assoc, IsExponentialGroup.pow_add,
      IsExponentialGroup.pow_mul]

private def lift [IsExponentialGroup A H] (φ : G →* H) : ExponentialHom A (Completion A G) H where
  toFun := Quot.lift (Term.eval φ) fun _ _ => Rel.eval_eq φ
  map_one' := rfl
  map_mul' x y := Quot.induction_on₂ x y fun _ _ => rfl
  map_pow' x _ := Quot.induction_on x fun _ => rfl

private theorem exponentialHom_ext {ψ ψ' : ExponentialHom A (Completion A G) H}
    (h : ψ.toMonoidHom.comp of = ψ'.toMonoidHom.comp of) : ψ = ψ' := by
  have htop := eq_top_of_range_le (S := ψ.toMonoidHom.eqLocus ψ'.toMonoidHom)
    (by rintro _ ⟨g, rfl⟩; exact MonoidHom.mem_eqLocus.2 (DFunLike.congr_fun h g))
    fun x hx a => by simpa using congrArg (· ^ a) (MonoidHom.mem_eqLocus.1 hx)
  ext x
  exact MonoidHom.mem_eqLocus.1 (htop ▸ Subgroup.mem_top x)

end Lift

/-- **The universal property of the tensor completion.** Every homomorphism from `G` to an
`A`-group factors through `G →* G^A` by a unique homomorphism commuting with exponentiation. -/
theorem isCompletion_of : IsExponentialGroup.IsCompletion.{w} A (of : G →* Completion A G) :=
  ⟨fun _ _ _ _ φ => ⟨lift φ, rfl, fun _ hψ => exponentialHom_ext hψ⟩⟩

/-- If the semiring `A` has a ring homomorphism to `ℤ`, every group embeds in its tensor
`A`-completion. For `A = ℤ[t]`, take the evaluation at `1`. -/
theorem of_injective (f : A →+* ℤ) : Function.Injective (of : G →* Completion A G) := by
  -- `G` is an `A`-group with `g ^ a = g ^ f a`
  let : Pow G A := ⟨fun g a => g ^ f a⟩
  have : IsExponentialGroup A G :=
    { pow_one g := (congrArg (g ^ ·) (map_one f)).trans (zpow_one g)
      pow_add g a b := (congrArg (g ^ ·) (map_add f a b)).trans (zpow_add g _ _)
      pow_mul g a b := (congrArg (g ^ ·) (map_mul f a b)).trans (zpow_mul g _ _)
      conj_pow _ _ _ := conj_zpow
      mul_pow hc a := hc.mul_zpow (f a) }
  exact isCompletion_of.injective_of_injective (φ := .id G) Function.injective_id

end Completion

end TauCeti.ExponentialGroup
