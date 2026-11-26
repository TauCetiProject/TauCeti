/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Stabilizer

/-!
# The twist of a representation by a ring automorphism

Let `σ` be a ring automorphism of a semiring `A` (for instance `σ ∈ Aut(ℂ)`). The `σ`-twist of an
`A`-module `V` is the same additive monoid with `a` acting as `σ⁻¹(a)`; it is `A ⊗_{A,σ} V`, through
`a ⊗ v ↦ σ⁻¹(a) • v`. A representation `ρ` of `G` on `V` gives the `σ`-twisted representation `ρ^σ`
on it, with the same operators: they are additive and commute with every `σ⁻¹(a)`. The twist keeps
the stabilizer of every vector, the invariants and the subrepresentations, so over a field it
preserves irreducibility.

## Main definitions

* `TauCeti.CoeffTwist σ V`: the `A`-module `V` with `a` acting as `σ⁻¹(a)`, and
  `TauCeti.CoeffTwist.of σ V : V ≃+ CoeffTwist σ V` the identity map.
* `TauCeti.CoeffTwist.ofSemilinearEquiv σ V`: the identity map as a `σ`-semilinear equivalence.
* `Representation.coeffTwist σ ρ`: the `σ`-twist `ρ^σ` of a representation.
* `Representation.IntertwiningMap.coeffTwist σ f`: the twist of an intertwining map.
* `Representation.invariantsCoeffTwistEquiv σ ρ`: the `σ`-semilinear identification of the
  invariants of `ρ` and of `ρ^σ`.
* `Representation.subrepresentationCoeffTwistOrderIso σ ρ`: the subrepresentations of `ρ` and
  `ρ^σ` are the same subsets.

## Main results

* `Representation.stabilizer_coeffTwist`: twisting keeps stabilizers.
* `Representation.isIrreducible_coeffTwist_iff`: over a field, `ρ^σ` is irreducible exactly when
  `ρ` is.

## References

* J. Bernstein, *Second adjointness for representations of reductive p-adic groups*, 1987
  manuscript, §2.0, Generalization, p. 9.
-/

public section

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

namespace TauCeti

/-- The **`σ`-twist** of an `A`-module `V` by a ring automorphism `σ` of `A`: the additive monoid
`V`, on which `a ∈ A` acts as `σ⁻¹(a)`. It is `A ⊗_{A,σ} V` through `a ⊗ v ↦ σ⁻¹(a) • v`. -/
@[expose]
def CoeffTwist {A : Type*} [Semiring A] (_σ : A ≃+* A) (V : Type*) : Type _ := V

namespace CoeffTwist

variable {A : Type*} [Semiring A] (σ : A ≃+* A) (V : Type*)

instance instAddCommMonoid [AddCommMonoid V] : AddCommMonoid (CoeffTwist σ V) :=
  inferInstanceAs (AddCommMonoid V)

instance instAddCommGroup [AddCommGroup V] : AddCommGroup (CoeffTwist σ V) :=
  inferInstanceAs (AddCommGroup V)

variable [AddCommMonoid V] [Module A V]

/-- `a ∈ A` acts on the `σ`-twist of `V` as `σ⁻¹(a)` acts on `V`. -/
instance instModule : Module A (CoeffTwist σ V) := Module.compHom V (σ.symm : A →+* A)

/-- The identity map of `V`, as an additive equivalence onto its `σ`-twist. -/
@[expose]
def of : V ≃+ CoeffTwist σ V := AddEquiv.refl V

variable {σ V}

/-- `a` acts on the `σ`-twist as `σ⁻¹(a)` acts on `V`. -/
@[simp]
theorem smul_of (a : A) (v : V) : a • of σ V v = of σ V (σ.symm a • v) :=
  (rfl)

/-- Moving `a • v` to the `σ`-twist turns `a` into `σ(a)`. -/
theorem of_smul (a : A) (v : V) : of σ V (a • v) = σ a • of σ V v := by
  rw [smul_of, RingEquiv.symm_apply_apply]

variable (σ V) in
/-- `of σ V` as a `σ`-semilinear equivalence. -/
def ofSemilinearEquiv : V ≃ₛₗ[(σ : A →+* A)] CoeffTwist σ V where
  __ := of σ V
  map_smul' := of_smul

@[simp]
theorem ofSemilinearEquiv_apply (v : V) : ofSemilinearEquiv σ V v = of σ V v :=
  (rfl)

@[simp]
theorem ofSemilinearEquiv_symm_apply (x : CoeffTwist σ V) :
    (ofSemilinearEquiv σ V).symm x = (of σ V).symm x :=
  (rfl)

omit [Module A V] in
/-- Every vector of the `σ`-twist comes from `V`. -/
@[elab_as_elim]
theorem induction {motive : CoeffTwist σ V → Prop} (h : ∀ v, motive (of σ V v))
    (x : CoeffTwist σ V) : motive x :=
  h ((of σ V).symm x)

end CoeffTwist

end TauCeti

namespace Representation

open TauCeti

section Monoid

variable {A G V : Type*} [CommSemiring A] [Monoid G] [AddCommMonoid V] [Module A V]
  (σ : A ≃+* A) (ρ : Representation A G V)

/-- The **`σ`-twist** `ρ^σ` of a representation by a ring automorphism `σ` of `A`: the same
operators, on the `σ`-twist of `V`. -/
-- Exposed: downstream constructions use that `ρ^σ(g)` is `ρ(g)` on vectors by definition.
@[expose]
def coeffTwist : Representation A G (CoeffTwist σ V) where
  toFun g :=
    { toFun x := CoeffTwist.of σ V (ρ g ((CoeffTwist.of σ V).symm x))
      map_add' x y := by simp
      map_smul' a x := by
        induction x using CoeffTwist.induction
        simp }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable {σ ρ}

@[simp]
theorem coeffTwist_apply_of (g : G) (v : V) :
    ρ.coeffTwist σ g (CoeffTwist.of σ V v) = CoeffTwist.of σ V (ρ g v) :=
  (rfl)

variable (σ ρ) in
/-- The `σ`-twist of a restriction is the restriction of the `σ`-twist. -/
theorem coeffTwist_comp {H : Type*} [Monoid H] (f : H →* G) :
    (ρ.coeffTwist σ).comp f = Representation.coeffTwist σ (ρ.comp f) :=
  (rfl)

variable (σ ρ) in
/-- **The subrepresentations of `ρ` and `ρ^σ` are the same subsets of `V`**: a subset is stable
under `ρ` and closed under the action of `A` exactly when it is stable under `ρ^σ` and closed under
the twisted action, because `σ` is bijective. -/
def subrepresentationCoeffTwistOrderIso :
    Subrepresentation ρ ≃o Subrepresentation (ρ.coeffTwist σ) where
  toFun W :=
    { toSubmodule := W.toSubmodule.comap (CoeffTwist.ofSemilinearEquiv σ V).symm.toLinearMap
      apply_mem_toSubmodule g _ hx := W.apply_mem_toSubmodule g hx }
  invFun W :=
    { toSubmodule := W.toSubmodule.comap (CoeffTwist.ofSemilinearEquiv σ V).toLinearMap
      apply_mem_toSubmodule g _ hv := W.apply_mem_toSubmodule g hv }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem of_mem_subrepresentationCoeffTwistOrderIso (W : Subrepresentation ρ) (v : V) :
    CoeffTwist.of σ V v ∈ subrepresentationCoeffTwistOrderIso σ ρ W ↔ v ∈ W :=
  Iff.rfl

@[simp]
theorem mem_subrepresentationCoeffTwistOrderIso_symm (W : Subrepresentation (ρ.coeffTwist σ))
    (v : V) : v ∈ (subrepresentationCoeffTwistOrderIso σ ρ).symm W ↔ CoeffTwist.of σ V v ∈ W :=
  Iff.rfl

/-- **Twisting preserves irreducibility**, in both directions, over a field. -/
theorem isIrreducible_coeffTwist_iff {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {σ : k ≃+* k} {ρ : Representation k G V} : IsIrreducible (ρ.coeffTwist σ) ↔ IsIrreducible ρ :=
  (subrepresentationCoeffTwistOrderIso σ ρ).isSimpleOrder_iff.symm

variable (σ) in
/-- The intertwining map `ρ^σ → ρ'^σ` with the same underlying function as `f : ρ → ρ'`. -/
-- Exposed, as `Representation.coeffTwist`: it is `f` on vectors by definition.
@[expose]
def IntertwiningMap.coeffTwist {W : Type*} [AddCommMonoid W] [Module A W]
    {ρ' : Representation A G W} (f : ρ.IntertwiningMap ρ') :
    (ρ.coeffTwist σ).IntertwiningMap (ρ'.coeffTwist σ) where
  toFun x := CoeffTwist.of σ W (f ((CoeffTwist.of σ V).symm x))
  map_add' x y := by simp
  map_smul' a x := by
    induction x using CoeffTwist.induction
    simp
  isIntertwining' g := by
    ext x
    induction x using CoeffTwist.induction
    simp [IntertwiningMap.isIntertwining]

variable (σ) in
@[simp]
theorem IntertwiningMap.coeffTwist_apply_of {W : Type*} [AddCommMonoid W] [Module A W]
    {ρ' : Representation A G W} (f : ρ.IntertwiningMap ρ') (v : V) :
    f.coeffTwist σ (CoeffTwist.of σ V v) = CoeffTwist.of σ W (f v) :=
  (rfl)

end Monoid

section Group

variable {A G V : Type*} [CommSemiring A] [Group G] [AddCommMonoid V] [Module A V]
  {σ : A ≃+* A} {ρ : Representation A G V}

/-- **Twisting keeps stabilizers.** -/
@[simp]
theorem stabilizer_coeffTwist (v : V) :
    (ρ.coeffTwist σ).stabilizer (CoeffTwist.of σ V v) = ρ.stabilizer v := by
  ext g
  simp [mem_stabilizer]

end Group

section Invariants

variable {A G V : Type*} [CommRing A] [Group G] [AddCommGroup V] [Module A V]
  {σ : A ≃+* A} {ρ : Representation A G V}

/-- The `σ`-semilinear bijection `V^G → (V^σ)^G` between the invariants of `ρ` and of its
`σ`-twist, the identity on vectors. -/
noncomputable def invariantsCoeffTwistEquiv (σ : A ≃+* A) (ρ : Representation A G V) :
    invariants ρ ≃ₛₗ[(σ : A →+* A)] invariants (ρ.coeffTwist σ) :=
  (CoeffTwist.ofSemilinearEquiv σ V).ofSubmodules _ _ <| by
    ext x
    induction x using CoeffTwist.induction
    simp [Submodule.mem_map_equiv]

@[simp]
theorem coe_invariantsCoeffTwistEquiv_apply (v : invariants ρ) :
    (invariantsCoeffTwistEquiv σ ρ v : CoeffTwist σ V) = CoeffTwist.of σ V v :=
  (rfl)

@[simp]
theorem coe_invariantsCoeffTwistEquiv_symm_apply (x : invariants (ρ.coeffTwist σ)) :
    ((invariantsCoeffTwistEquiv σ ρ).symm x : V) = (CoeffTwist.of σ V).symm x :=
  (rfl)

end Invariants

end Representation
