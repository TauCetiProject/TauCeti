/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
public import TauCeti.Algebra.Subalgebra.Center

/-!
# The central character of a simple module

A central element `z` of a `k`-algebra `A` acts on an `A`-module `M` by an `A`-linear map, because
`z` commutes with every scalar; this is the algebra homomorphism `TauCeti.centerToEnd`. Since an
`A`-linear endomorphism commutes with the action of every element of `A`, the centre in fact lands
in the centre of the commutant `End_A M` (`TauCeti.centerToCenterEnd`). For a simple module the
commutant is a division algebra, so this centre is a field, but in general not `k`: on the real
module `ℂ` of the algebra `ℂ` the centre acts through `ℂ` itself.

When the centre of the commutant is `k`, that is when the structure map `k → Z(End_A M)` is
bijective, the action of the centre is by honest scalars, and the resulting `k`-algebra
homomorphism `Z(A) → k` is the **central character** of `M`
(`TauCeti.centralCharacterOfBijectiveAlgebraMap`). This covers absolutely simple modules, whose
commutant is `k` itself, and also modules whose commutant is a central division algebra over `k`,
such as real simple modules with commutant the quaternions. For a finite-dimensional simple module
over an algebraically closed field `k` the commutant is `k` by Schur's lemma, and
`TauCeti.centralCharacter` is that special case.

For `A = k[G]` this is the character-theoretic `ωᵪ`. Its value on the class sum of a conjugacy
class `C` with representative `g` is the entry `χ(g)` of the character table weighted by the class
size and normalized by the degree: `ωᵪ(K_C) = |C| · χ(g) / χ(1)`, when `χ(1) ≠ 0` in `k`.

## Main definitions

* `TauCeti.centerToEnd`: a central element of `A` acts on an `A`-module by an `A`-linear
  endomorphism, as a homomorphism of `k`-algebras `Z(A) →ₐ[k] End_A M`. No simplicity or
  finiteness hypothesis is needed.
* `TauCeti.centerToCenterEnd`: the same homomorphism, landing in the centre of `End_A M`. When
  `M` is simple that centre is a field (`TauCeti.isField_center`).
* `TauCeti.centralCharacterOfBijectiveAlgebraMap`: the central character `Z(A) →ₐ[k] k` of a
  module whose commutant has centre `k`.
* `TauCeti.centralCharacter`: the central character `Z(A) →ₐ[k] k` of a finite-dimensional simple
  module over an algebraically closed field.

## Main statements

* `TauCeti.smul_eq_centralCharacterOfBijectiveAlgebraMap_smul` and
  `TauCeti.centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq`: a central element acts by its
  central character, which is the only scalar doing so; over a torsion-free module the action on a
  single nonzero vector determines it
  (`TauCeti.centralCharacterOfBijectiveAlgebraMap_eq_of_ne_zero_of_smul_eq`).
* `TauCeti.centralCharacterOfBijectiveAlgebraMap_congr`: isomorphic modules have the same central
  character.
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
    (Semigroup.mem_center_iff.mpr (Subalgebra.mem_center_iff.mp z.property))
  map_one' := by ext m; simp
  map_mul' z w := by ext m; simp [smul_smul, Subalgebra.mem_center_iff.mp w.property (z : A)]
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

/-- The central action landing in the centre of the commutant is the central action. -/
@[simp]
theorem coe_centerToCenterEnd_apply (z : Subalgebra.center k A) :
    (centerToCenterEnd k A M z : Module.End A M) = centerToEnd k A M z :=
  AlgHom.coe_codRestrict _ _ _ z

end CenterToEnd

/-! ### The central character of a module with scalar central commutant -/

section OfBijective

variable (k : Type u) [CommSemiring k] (A : Type v) [Semiring A] [Algebra k A]
variable (M : Type w) [AddCommMonoid M] [Module A M] [Module k M] [IsScalarTower k A M]
variable (h : Function.Bijective (algebraMap k (Subalgebra.center k (Module.End A M))))

/-- The **central character** of an `A`-module `M` whose commutant `End_A M` has centre `k`,
meaning that the structure map `k → Z(End_A M)` is bijective: the homomorphism of `k`-algebras
recording the scalar by which each central element of `A` acts on `M`.

The hypothesis holds when the commutant is `k` itself
(`TauCeti.bijective_algebraMap_center_of_bijective`), that is for an absolutely simple module, and
in particular for a finite-dimensional simple module over an algebraically closed field
(`TauCeti.centralCharacter`). It also holds for modules whose commutant is a central division
algebra over `k`, such as real simple modules with commutant the quaternions, and for isotypic
modules `S ^ n` of such a module `S`. It fails for real simple modules with commutant `ℂ`. -/
noncomputable def centralCharacterOfBijectiveAlgebraMap : Subalgebra.center k A →ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (Subalgebra.center k (Module.End A M))) h).symm.toAlgHom
    |>.comp (centerToCenterEnd k A M)

/-- The central character, viewed as an endomorphism, is the action of the central element. -/
@[simp]
theorem algebraMap_centralCharacterOfBijectiveAlgebraMap (z : Subalgebra.center k A) :
    algebraMap k (Module.End A M) (centralCharacterOfBijectiveAlgebraMap k A M h z) =
      centerToEnd k A M z := by
  have := AlgEquiv.ofBijective_apply_symm_apply
    (Algebra.ofId k (Subalgebra.center k (Module.End A M))) h (centerToCenterEnd k A M z)
  simpa [centralCharacterOfBijectiveAlgebraMap] using congrArg Subtype.val this

/-- A central element acts on the module as multiplication by its central character. -/
theorem smul_eq_centralCharacterOfBijectiveAlgebraMap_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacterOfBijectiveAlgebraMap k A M h z • m := by
  rw [← centerToEnd_apply, ← algebraMap_centralCharacterOfBijectiveAlgebraMap k A M h z,
    Module.algebraMap_end_apply]

variable {k A M h}

/-- The central character is the unique scalar by which a central element acts. -/
theorem centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq {z : Subalgebra.center k A} {c : k}
    (hc : ∀ m : M, (z : A) • m = c • m) : centralCharacterOfBijectiveAlgebraMap k A M h z = c :=
  h.1 <| Subtype.ext <| by
    ext m
    rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
      algebraMap_centralCharacterOfBijectiveAlgebraMap, centerToEnd_apply,
      Module.algebraMap_end_apply, hc]

/-- **Isomorphic modules have the same central character.** -/
theorem centralCharacterOfBijectiveAlgebraMap_congr {N : Type*} [AddCommMonoid N] [Module A N]
    [Module k N] [IsScalarTower k A N]
    {hN : Function.Bijective (algebraMap k (Subalgebra.center k (Module.End A N)))}
    (e : M ≃ₗ[A] N) :
    centralCharacterOfBijectiveAlgebraMap k A M h =
      centralCharacterOfBijectiveAlgebraMap k A N hN := by
  ext z
  refine (centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq fun n => ?_).symm
  rw [← e.apply_symm_apply n, ← map_smul,
    smul_eq_centralCharacterOfBijectiveAlgebraMap_smul k A M h, LinearMapClass.map_smul_of_tower]

end OfBijective

section OfBijectiveTorsionFree

variable {k : Type u} [CommRing k] [IsCancelMulZero k] {A : Type v} [Semiring A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable [Module.IsTorsionFree k M]
variable {h : Function.Bijective (algebraMap k (Subalgebra.center k (Module.End A M)))}

/-- The central character is determined by the action of a central element on a single nonzero
vector: no other scalar can reproduce it there. -/
theorem centralCharacterOfBijectiveAlgebraMap_eq_of_ne_zero_of_smul_eq
    {z : Subalgebra.center k A} {c : k} {m : M} (hm : m ≠ 0) (hc : (z : A) • m = c • m) :
    centralCharacterOfBijectiveAlgebraMap k A M h z = c :=
  smul_left_injective k hm
    ((smul_eq_centralCharacterOfBijectiveAlgebraMap_smul k A M h z m).symm.trans hc)

end OfBijectiveTorsionFree

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
`TauCeti.centralCharacterOfBijectiveAlgebraMap`. -/
noncomputable def centralCharacter : Subalgebra.center k A →ₐ[k] k :=
  centralCharacterOfBijectiveAlgebraMap k A M
    (bijective_algebraMap_center_of_bijective
      (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k))

/-- Over an algebraically closed field, the central character of a finite-dimensional simple
module is its central character as a module with scalar central commutant. -/
theorem centralCharacter_eq_centralCharacterOfBijectiveAlgebraMap
    (h : Function.Bijective (algebraMap k (Subalgebra.center k (Module.End A M)))) :
    centralCharacter k A M = centralCharacterOfBijectiveAlgebraMap k A M h :=
  (rfl)

/-- The central character, viewed as an endomorphism, is the action of the central element. -/
@[simp]
theorem algebraMap_centralCharacter (z : Subalgebra.center k A) :
    algebraMap k (Module.End A M) (centralCharacter k A M z) = centerToEnd k A M z :=
  algebraMap_centralCharacterOfBijectiveAlgebraMap k A M _ z

/-- The defining property of the central character: a central element acts on the module as
multiplication by the scalar the central character assigns to it.

This is the simp normal form: the opaque action of the centre is replaced by the action of a
scalar, which is the whole point of the construction. -/
@[simp]
theorem smul_eq_centralCharacter_smul (z : Subalgebra.center k A) (m : M) :
    (z : A) • m = centralCharacter k A M z • m :=
  smul_eq_centralCharacterOfBijectiveAlgebraMap_smul k A M _ z m

variable {k A M}

/-- The central character is determined by the action of a central element on a single nonzero
vector: no other scalar can reproduce it there. -/
theorem centralCharacter_eq_of_ne_zero_of_smul_eq {z : Subalgebra.center k A} {c : k} {m : M}
    (hm : m ≠ 0) (h : (z : A) • m = c • m) : centralCharacter k A M z = c :=
  centralCharacterOfBijectiveAlgebraMap_eq_of_ne_zero_of_smul_eq hm h

/-- The central character is the unique scalar by which a central element acts. -/
theorem centralCharacter_eq_of_smul_eq {z : Subalgebra.center k A} {c : k}
    (h : ∀ m : M, (z : A) • m = c • m) : centralCharacter k A M z = c :=
  centralCharacterOfBijectiveAlgebraMap_eq_of_smul_eq h

end CentralCharacter

end TauCeti
