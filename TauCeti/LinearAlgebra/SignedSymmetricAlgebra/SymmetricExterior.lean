/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import TauCeti.LinearAlgebra.SignedSymmetricAlgebra.Basic
import TauCeti.Algebra.CharP.Invertible

/-!
# The signed symmetric algebra of an evenly or oddly graded module

If an internally graded module `V` is concentrated in degrees of Koszul sign `1` (for instance,
even integer degrees, or parity `0 : ZMod 2`), the Koszul sign `(-1) ^ (p * q)` is always `1`, so
the signed symmetric algebra `A(V) = TauCeti.SignedSym G` is the ordinary symmetric algebra of `V`.
If `V` is concentrated in degrees of Koszul sign `-1` (odd integer degrees, or parity `1 : ZMod 2`),
the sign is always `-1`, and once `2` is invertible in the coefficients `A(V)` is the exterior
algebra of `V`. These are the two factors of the comparison `A(V) ≃ Sym(V_even) ⊗ Λ(V_odd)` of the
free supercommutative algebra over `ℚ` with Mathlib's unsigned constructions.

The invertibility of `2` cannot be dropped in the odd case: over `ℤ`, the relation only gives
`2 • x ^ 2 = 0` for an odd generator `x`, while `x ^ 2 = 0` holds in the exterior algebra.
Conversely, Mathlib's `SymmetricAlgebra` is the wrong carrier for odd generators, since there
`x ^ 2 ≠ 0`.

The inverse of the symmetric comparison is built from `SymmetricAlgebra.lift`, which only maps
into commutative algebras. It is applied with values in the center of `A(V)`, which contains the
generators when `V` is concentrated in Koszul-even degrees.

## Main results

* `TauCeti.SignedSym.commute_generator_of_piece_eq_bot` and
  `TauCeti.SignedSym.mul_comm_of_piece_eq_bot` (with integer specializations
  `commute_generator_of_piece_odd_eq_bot` and `mul_comm_of_piece_odd_eq_bot`): when all pieces of
  Koszul sign `-1` vanish, generators commute, hence `A(V)` is commutative.
* `TauCeti.SignedSym.symmetricAlgebraEquiv`: when all pieces of Koszul sign `-1` vanish,
  `A(V) ≃ Sym(V)`.
* `TauCeti.SignedSym.generator_mul_generator_eq_neg_of_piece_eq_bot` and
  `TauCeti.SignedSym.generator_mul_self_eq_zero_of_piece_eq_bot` (with integer specializations
  `generator_mul_generator_eq_neg_of_piece_even_eq_bot` and
  `generator_mul_self_eq_zero_of_piece_even_eq_bot`): when all pieces of Koszul sign `1` vanish,
  generators anticommute, and square to zero when `2` is invertible.
* `TauCeti.SignedSym.exteriorAlgebraEquiv`: when all pieces of Koszul sign `1` vanish and `2` is
  invertible, `A(V) ≃ Λ(V)`.

## References

* J. Pardon, *Contact homology and virtual fundamental cycles*, equation (1.1), for the free
  supercommutative algebra.
-/

public section

namespace TauCeti.SignedSym

universe u v

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]

section General

variable {ι : Type*} [DecidableEq ι] [CommSemiring ι] [Module ι (Additive ℤˣ)]
variable {G : InternalGrading R V ι}

/-- A commutation rule with a fixed sign `s` between generators of homogeneous elements holds
between all generators. -/
private theorem generator_mul_generator_eq_smul (s : ℤ)
    (h : ∀ (p q : ι) (x y : V), x ∈ G.piece p → y ∈ G.piece q →
      generator G x * generator G y = s • (generator G y * generator G x)) (x y : V) :
    generator G x * generator G y = s • (generator G y * generator G x) := by
  have key : (LinearMap.mul R (SignedSym G)).compl₁₂ (generator G) (generator G) =
      s • (LinearMap.mul R (SignedSym G)).flip.compl₁₂ (generator G) (generator G) :=
    G.linearMap_ext fun p x hx => G.linearMap_ext fun q y hy => by
      simpa using h p q x y hx hy
  simpa using LinearMap.congr_fun₂ key x y

/-! ### Generators of Koszul sign `1` -/

section Even

variable (hG : ∀ p, (-1 : ℤˣ) ^ p = -1 → G.piece p = ⊥)
include hG

/-- If `V` is concentrated in degrees of Koszul sign `1`, the Koszul sign of a nonzero homogeneous
element against any degree is `1`. -/
private theorem eq_zero_or_uzpow_eq_one_of_piece_eq_bot {p : ι} {x : V}
    (hx : x ∈ G.piece p) (q : ι) : x = 0 ∨ (-1 : ℤˣ) ^ (p * q) = 1 := by
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ p) with hp | hp
  · exact .inr (by rw [uzpow_mul, hp, one_uzpow])
  · exact .inl (by simpa [hG p hp] using hx)

/-- If all pieces of Koszul sign `-1` vanish, any two generators of `A(V)` commute. -/
theorem commute_generator_of_piece_eq_bot (x y : V) :
    Commute (generator G x) (generator G y) := by
  refine (commute_iff_eq _ _).2 ?_
  simpa using generator_mul_generator_eq_smul 1 (fun p q x y hx hy => by
    rcases eq_zero_or_uzpow_eq_one_of_piece_eq_bot hG hx q with rfl | h
    · simp
    · simpa [h] using generator_mul_generator G hx hy) x y

/-- If all pieces of Koszul sign `-1` vanish, the generators of `A(V)` are central. -/
private theorem generator_mem_center (x : V) :
    generator G x ∈ Subalgebra.center R (SignedSym G) := by
  refine Subalgebra.mem_center_iff.2 fun b => ?_
  induction b using SignedSym.induction with
  | algebraMap r => exact Algebra.commutes r _
  | generator y => exact commute_generator_of_piece_eq_bot hG y x
  | mul a b ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

/-- If all pieces of Koszul sign `-1` vanish, `A(V)` is commutative. -/
theorem mul_comm_of_piece_eq_bot (a b : SignedSym G) : a * b = b * a := by
  have hcenter : ∀ a : SignedSym G, a ∈ Subalgebra.center R (SignedSym G) := by
    intro a
    induction a using SignedSym.induction with
    | algebraMap r => exact Subalgebra.algebraMap_mem _ r
    | generator x => exact generator_mem_center hG x
    | mul a b ha hb => exact mul_mem ha hb
    | add a b ha hb => exact add_mem ha hb
  exact ((Subalgebra.mem_center_iff.1 (hcenter a)) b).symm

/-- The map `A(V) → Sym(V)` fixing generators, when all pieces of Koszul sign `-1` vanish. -/
private def toSymmetricAlgebra : SignedSym G →ₐ[R] SymmetricAlgebra R V :=
  lift G (SymmetricAlgebra.ι R V) fun p q x y hx _ => by
    rcases eq_zero_or_uzpow_eq_one_of_piece_eq_bot hG hx q with rfl | h
    · simp
    · simp [h, mul_comm]

/-- The map `Sym(V) → A(V)` fixing generators, when all pieces of Koszul sign `-1` vanish. It takes
values in the center of `A(V)`, which is commutative. -/
private noncomputable def ofSymmetricAlgebra : SymmetricAlgebra R V →ₐ[R] SignedSym G :=
  (Subalgebra.center R (SignedSym G)).val.comp <| SymmetricAlgebra.lift <|
    (generator G).codRestrict (Subalgebra.center R (SignedSym G)).toSubmodule
      (generator_mem_center hG)

private theorem ofSymmetricAlgebra_ι (x : V) :
    ofSymmetricAlgebra hG (SymmetricAlgebra.ι R V x) = generator G x := by
  rw [ofSymmetricAlgebra, AlgHom.comp_apply, SymmetricAlgebra.lift_ι_apply, Subalgebra.coe_val]
  -- The subalgebra and its underlying submodule have the same subtype coercion.
  exact LinearMap.codRestrict_apply _ (generator G) (h := generator_mem_center hG) x

/-- **The signed symmetric algebra of an evenly graded module is its symmetric algebra.** When all
pieces of Koszul sign `-1` vanish, `A(V)` is isomorphic to `SymmetricAlgebra R V`, compatibly with
the generators. -/
noncomputable def symmetricAlgebraEquiv : SignedSym G ≃ₐ[R] SymmetricAlgebra R V :=
  AlgEquiv.ofAlgHom (toSymmetricAlgebra hG) (ofSymmetricAlgebra hG)
    (SymmetricAlgebra.algHom_ext <| LinearMap.ext fun x => by
      simp [toSymmetricAlgebra, ofSymmetricAlgebra_ι])
    (hom_ext G fun x => by simp [toSymmetricAlgebra, ofSymmetricAlgebra_ι])

/-- The symmetric comparison sends the generator of `x` to `x`. -/
@[simp]
theorem symmetricAlgebraEquiv_generator (x : V) :
    symmetricAlgebraEquiv hG (generator G x) = SymmetricAlgebra.ι R V x := by
  simp [symmetricAlgebraEquiv, toSymmetricAlgebra]

/-- The inverse symmetric comparison sends `x` to its generator. -/
@[simp]
theorem symmetricAlgebraEquiv_symm_ι (x : V) :
    (symmetricAlgebraEquiv hG).symm (SymmetricAlgebra.ι R V x) = generator G x := by
  rw [AlgEquiv.symm_apply_eq, symmetricAlgebraEquiv_generator]

end Even

/-! ### Generators of Koszul sign `-1` -/

section Odd

variable (hG : ∀ p, (-1 : ℤˣ) ^ p = 1 → G.piece p = ⊥)
include hG

/-- If `V` is concentrated in degrees of Koszul sign `-1`, the Koszul sign of two nonzero
homogeneous elements is `-1`. -/
private theorem eq_zero_or_eq_zero_or_uzpow_eq_neg_one_of_piece_eq_bot {p q : ι}
    {x y : V} (hx : x ∈ G.piece p) (hy : y ∈ G.piece q) :
    x = 0 ∨ y = 0 ∨ (-1 : ℤˣ) ^ (p * q) = -1 := by
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ p) with hp | hp
  · exact .inl (by simpa [hG p hp] using hx)
  rcases Int.units_eq_one_or ((-1 : ℤˣ) ^ q) with hq | hq
  · exact .inr (.inl (by simpa [hG q hq] using hy))
  exact .inr (.inr (by rw [uzpow_mul, hp, hq]))

/-- If all pieces of Koszul sign `1` vanish, any two generators of `A(V)` anticommute. -/
theorem generator_mul_generator_eq_neg_of_piece_eq_bot (x y : V) :
    generator G x * generator G y = -(generator G y * generator G x) := by
  simpa using generator_mul_generator_eq_smul (-1) (fun p q x y hx hy => by
    rcases eq_zero_or_eq_zero_or_uzpow_eq_neg_one_of_piece_eq_bot hG hx hy with
      rfl | rfl | h
    · simp
    · simp
    · simpa [h] using generator_mul_generator G hx hy) x y

/-- If all pieces of Koszul sign `1` vanish and `2` is invertible, every generator of `A(V)`
squares to zero. -/
theorem generator_mul_self_eq_zero_of_piece_eq_bot [Invertible (2 : R)] (x : V) :
    generator G x * generator G x = 0 :=
  eq_zero_of_eq_neg_of_invertible_two (R := R)
    (generator_mul_generator_eq_neg_of_piece_eq_bot hG x x)

/-- The map `A(V) → Λ(V)` fixing generators, when all pieces of Koszul sign `1` vanish. -/
private def toExteriorAlgebra : SignedSym G →ₐ[R] ExteriorAlgebra R V :=
  lift G (ExteriorAlgebra.ι R) fun p q x y hx hy => by
    rcases eq_zero_or_eq_zero_or_uzpow_eq_neg_one_of_piece_eq_bot hG hx hy with
      rfl | rfl | h
    · simp
    · simp
    · simpa [h] using eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (R := R) x y)

variable [Invertible (2 : R)]

/-- The map `Λ(V) → A(V)` fixing generators, when all pieces of Koszul sign `1` vanish and `2` is
invertible. -/
private noncomputable def ofExteriorAlgebra : ExteriorAlgebra R V →ₐ[R] SignedSym G :=
  ExteriorAlgebra.lift R ⟨generator G, generator_mul_self_eq_zero_of_piece_eq_bot hG⟩

/-- **The signed symmetric algebra of an oddly graded module is its exterior algebra.** When all
pieces of Koszul sign `1` vanish and `2` is invertible in `R`, `A(V)` is isomorphic to
`ExteriorAlgebra R V`, compatibly with the generators. -/
noncomputable def exteriorAlgebraEquiv : SignedSym G ≃ₐ[R] ExteriorAlgebra R V :=
  AlgEquiv.ofAlgHom (toExteriorAlgebra hG) (ofExteriorAlgebra hG)
    (ExteriorAlgebra.hom_ext <| LinearMap.ext fun x => by
      simp [toExteriorAlgebra, ofExteriorAlgebra])
    (hom_ext G fun x => by simp [toExteriorAlgebra, ofExteriorAlgebra])

/-- The exterior comparison sends the generator of `x` to `x`. -/
@[simp]
theorem exteriorAlgebraEquiv_generator (x : V) :
    exteriorAlgebraEquiv hG (generator G x) = ExteriorAlgebra.ι R x := by
  simp [exteriorAlgebraEquiv, toExteriorAlgebra]

/-- The inverse exterior comparison sends `x` to its generator. -/
@[simp]
theorem exteriorAlgebraEquiv_symm_ι (x : V) :
    (exteriorAlgebraEquiv hG).symm (ExteriorAlgebra.ι R x) = generator G x := by
  rw [AlgEquiv.symm_apply_eq, exteriorAlgebraEquiv_generator]

end Odd

end General

/-! ### Integer-graded specializations -/

section Int

variable {G : InternalGrading R V ℤ}

/-- If an integer-graded `V` is concentrated in even degrees, any two generators of `A(V)`
commute. -/
theorem commute_generator_of_piece_odd_eq_bot (hG : ∀ p, Odd p → G.piece p = ⊥) (x y : V) :
    Commute (generator G x) (generator G y) :=
  commute_generator_of_piece_eq_bot
    (fun p hp => hG p ((Int.negOnePow_eq_neg_one_iff p).mp hp)) x y

/-- If an integer-graded `V` is concentrated in even degrees, `A(V)` is commutative. -/
theorem mul_comm_of_piece_odd_eq_bot (hG : ∀ p, Odd p → G.piece p = ⊥) (a b : SignedSym G) :
    a * b = b * a :=
  mul_comm_of_piece_eq_bot (fun p hp => hG p ((Int.negOnePow_eq_neg_one_iff p).mp hp)) a b

/-- If an integer-graded `V` is concentrated in odd degrees, any two generators of `A(V)`
anticommute. -/
theorem generator_mul_generator_eq_neg_of_piece_even_eq_bot (hG : ∀ p, Even p → G.piece p = ⊥)
    (x y : V) : generator G x * generator G y = -(generator G y * generator G x) :=
  generator_mul_generator_eq_neg_of_piece_eq_bot
    (fun p hp => hG p ((Int.negOnePow_eq_one_iff p).mp hp)) x y

/-- If an integer-graded `V` is concentrated in odd degrees and `2` is invertible, every generator
of `A(V)` squares to zero. -/
theorem generator_mul_self_eq_zero_of_piece_even_eq_bot [Invertible (2 : R)]
    (hG : ∀ p, Even p → G.piece p = ⊥) (x : V) :
    generator G x * generator G x = 0 :=
  generator_mul_self_eq_zero_of_piece_eq_bot
    (fun p hp => hG p ((Int.negOnePow_eq_one_iff p).mp hp)) x

end Int

end TauCeti.SignedSym
