/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Semisimple.Schur

/-!
# The central character of a simple module

A central element `z` of a `k`-algebra `A` acts on an `A`-module `M` by an `A`-linear map, because
`z` commutes with every scalar; this is the algebra homomorphism `TauCeti.centerToEnd`. Since an
`A`-linear endomorphism commutes with the action of every element of `A`, the centre in fact lands
in the centre of the commutant `End_A M` (`TauCeti.centerToCenterEnd`). For a simple module the
commutant is a division algebra, so this centre is a field, but in general not `k`: on the real
module `ℂ` of the algebra `ℂ` the centre acts through `ℂ` itself.

When the commutant is `k` itself, that is when the structure map `k → End_A M` is bijective, the
action of the centre is by honest scalars, and the resulting `k`-algebra homomorphism `Z(A) → k` is
the **central character** of `M` (`TauCeti.centralCharacterOfBijective`). This is the case of an
absolutely simple module. For a finite-dimensional simple module over an algebraically closed field
`k` it always holds by Schur's lemma, and `TauCeti.centralCharacter` is that special case.

For `A = k[G]` this is the character-theoretic `ωᵪ`. Its value on the class sum of a conjugacy
class `C` with representative `g` is the entry `χ(g)` of the character table weighted by the class
size and normalized by the degree: `ωᵪ(K_C) = |C| · χ(g) / χ(1)`, when `χ(1) ≠ 0` in `k`.

## Main definitions

* `TauCeti.centerToEnd`: a central element of `A` acts on an `A`-module by an `A`-linear
  endomorphism, as a homomorphism of `k`-algebras `Z(A) →ₐ[k] End_A M`. No simplicity or
  finiteness hypothesis is needed.
* `TauCeti.centerToCenterEnd`: the same homomorphism, landing in the centre of `End_A M`. When
  `M` is simple that centre is a field (`TauCeti.isField_center`).
* `TauCeti.centralCharacterOfBijective`: the central character `Z(A) →ₐ[k] k` of a module whose
  commutant is `k`.
* `TauCeti.centralCharacter`: the central character `Z(A) →ₐ[k] k` of a finite-dimensional simple
  module over an algebraically closed field.

## Main statements

* `TauCeti.smul_eq_centralCharacterOfBijective_smul` and
  `TauCeti.centralCharacterOfBijective_eq_of_smul_eq`: a central element acts by its central
  character, which is the only scalar doing so.
* `TauCeti.smul_eq_centralCharacter_smul`: the defining property, that a central element acts as
  multiplication by its central character.
* `TauCeti.centralCharacter_eq_of_smul_eq`: the central character is the *only* scalar with that
  property, in the form asking for the equality at every vector.
* `TauCeti.centralCharacter_eq_of_ne_zero_of_smul_eq`: the sharper form, computing the central
  character from the action on a single nonzero vector.

## References

Central characters are treated here in the generality of a simple module over an arbitrary algebra.
See I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 3, or C. W. Curtis and I. Reiner,
*Representation Theory of Finite Groups and Associative Algebras*, §33.
-/

public section

namespace TauCeti

universe u v w

/-! ### The action of the centre -/

section CenterToEnd

variable (k : Type u) [CommSemiring k] (A : Type v) [Semiring A] [Algebra k A]
variable (M : Type w) [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- A central element of `A` acts on an `A`-module `M` by an `A`-linear endomorphism, and doing so
is a homomorphism of `k`-algebras from the centre of `A` to `End_A M`.

Centrality is exactly what makes the action `A`-linear rather than merely additive; Mathlib's
`Module.End.smulLeft` packages the individual endomorphism. -/
def centerToEnd : Subalgebra.center k A →ₐ[k] Module.End A M where
  toFun z := Module.End.smulLeft (M := M) (z : A)
    (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.2))
  map_one' := by ext m; simp
  map_mul' z w := by ext m; simp [smul_smul, Subalgebra.mem_center_iff.mp w.2 (z : A)]
  map_zero' := by ext m; simp
  map_add' z w := by ext m; simp [add_smul]
  commutes' r := by ext m; simp [algebraMap_smul]

/-- The endomorphism attached to a central element is multiplication by it. -/
@[simp]
theorem centerToEnd_apply (z : Subalgebra.center k A) (m : M) :
    centerToEnd k A M z m = (z : A) • m :=
  (rfl)

/-- A central element acts by an endomorphism commuting with every `A`-linear endomorphism. -/
theorem centerToEnd_mem_center (z : Subalgebra.center k A) :
    centerToEnd k A M z ∈ Subalgebra.center k (Module.End A M) :=
  Subalgebra.mem_center_iff.mpr fun f => by ext m; simp

/-- The action of the centre of `A` on an `A`-module lands in the centre of the commutant
`End_A M`, as a homomorphism of `k`-algebras. For a simple module `End_A M` is a division algebra,
so the target is a field (`TauCeti.isField_center`); it need not be `k`. -/
def centerToCenterEnd : Subalgebra.center k A →ₐ[k] Subalgebra.center k (Module.End A M) :=
  (centerToEnd k A M).codRestrict _ (centerToEnd_mem_center k A M)

@[simp]
theorem coe_centerToCenterEnd_apply (z : Subalgebra.center k A) :
    (centerToCenterEnd k A M z : Module.End A M) = centerToEnd k A M z :=
  (rfl)

end CenterToEnd

/-! ### The centre of a division algebra -/

/-- The centre of a division algebra is a field. Applied to the commutant `End_A M` of a simple
module (Mathlib's `Module.End.instDivisionRing`), this is the field through which the centre of
`A` acts (`TauCeti.centerToCenterEnd`).

This is stated with `IsField`, like Mathlib's `IsSimpleRing.isField_center`, rather than as a
`Field` instance: a global instance transported from `Subring.center D` would carry rational
scalar actions not definitionally equal to those `Subalgebra.center k D` already has. -/
theorem isField_center {k D : Type*} [CommSemiring k] [DivisionRing D] [Algebra k D] :
    IsField (Subalgebra.center k D) :=
  Field.toIsField (Subring.center D)

/-! ### The central character of a module with scalar commutant -/

section OfBijective

variable (k : Type u) [CommSemiring k] (A : Type v) [Semiring A] [Algebra k A]
variable (M : Type w) [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
variable (h : Function.Bijective (algebraMap k (Module.End A M)))

/-- The **central character** of an `A`-module `M` whose commutant is `k`, meaning that the
structure map `k → End_A M` is bijective: the homomorphism of `k`-algebras recording the scalar by
which each central element of `A` acts on `M`.

For a finite-dimensional simple module this hypothesis says that `M` is absolutely simple; it
holds automatically over an algebraically closed field (`TauCeti.centralCharacter`), but not for
real simple modules in general. -/
noncomputable def centralCharacterOfBijective : Subalgebra.center k A →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Module.End A M)) h).symm.toAlgHom.comp
    (centerToEnd k A M)

/-- The central character, viewed as an endomorphism, is the action of the central element. -/
@[simp]
theorem algebraMap_centralCharacterOfBijective (z : Subalgebra.center k A) :
    algebraMap k (Module.End A M) (centralCharacterOfBijective k A M h z) = centerToEnd k A M z :=
  ((AlgEquiv.ofBijective (Algebra.ofId k (Module.End A M)) h).apply_symm_apply _)

/-- A central element acts on the module as multiplication by its central character. -/
theorem smul_eq_centralCharacterOfBijective_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacterOfBijective k A M h z • m := by
  rw [← centerToEnd_apply, ← algebraMap_centralCharacterOfBijective k A M h z,
    Module.algebraMap_end_apply]

variable {k A M h}

/-- The central character is the unique scalar by which a central element acts. -/
theorem centralCharacterOfBijective_eq_of_smul_eq {z : Subalgebra.center k A} {c : k}
    (hc : ∀ m : M, (z : A) • m = c • m) : centralCharacterOfBijective k A M h z = c :=
  h.1 <| by
    ext m
    rw [algebraMap_centralCharacterOfBijective, centerToEnd_apply, Module.algebraMap_end_apply,
      hc]

end OfBijective

/-! ### The central character of a simple module -/

section CentralCharacter

variable (k : Type u) [Field k] [IsAlgClosed k] (A : Type v) [Ring A] [Algebra k A]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable [IsSimpleModule A M] [FiniteDimensional k M]

/-- The **central character** of a finite-dimensional simple module `M` over a `k`-algebra `A`,
for `k` algebraically closed: the homomorphism of `k`-algebras recording the scalar by which each
central element of `A` acts on `M`.

The scalar exists because the action of a central element is `A`-linear (`TauCeti.centerToEnd`)
and every `A`-linear endomorphism of `M` is a scalar (Schur's lemma,
`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`), so this is
`TauCeti.centralCharacterOfBijective`. -/
noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  centralCharacterOfBijective k A M (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k)

/-- Over an algebraically closed field, the central character of a finite-dimensional simple
module is its central character as a module with scalar commutant. -/
theorem centralCharacter_eq_centralCharacterOfBijective
    (h : Function.Bijective (algebraMap k (Module.End A M))) :
    centralCharacter k A M = centralCharacterOfBijective k A M h :=
  (rfl)

/-- The defining property of the central character: a central element acts on the module as
multiplication by the scalar the central character assigns to it.

This is the simp normal form: the opaque action of the centre is replaced by the action of a
scalar, which is the whole point of the construction. -/
@[simp]
theorem smul_eq_centralCharacter_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacter k A M z • m :=
  smul_eq_centralCharacterOfBijective_smul k A M _ z m

variable {k A M}

/-- The central character is determined by the action of a central element on a single nonzero
vector: no other scalar can reproduce it there. -/
theorem centralCharacter_eq_of_ne_zero_of_smul_eq {z : Subalgebra.center k A} {c : k} {m : M}
    (hm : m ≠ 0) (h : (z : A) • m = c • m) : centralCharacter k A M z = c := by
  have hsub : (centralCharacter k A M z - c) • m = 0 := by
    rw [sub_smul, ← smul_eq_centralCharacter_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hm)

/-- The central character is the unique scalar by which a central element acts. -/
theorem centralCharacter_eq_of_smul_eq {z : Subalgebra.center k A} {c : k}
    (h : ∀ m : M, (z : A) • m = c • m) : centralCharacter k A M z = c :=
  centralCharacterOfBijective_eq_of_smul_eq h

end CentralCharacter

end TauCeti
