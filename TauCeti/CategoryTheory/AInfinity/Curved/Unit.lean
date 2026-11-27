/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Curved.Basic
public import TauCeti.CategoryTheory.AInfinity.Unit

/-!
# Strict units of curved A-infinity categories

A family of **strict units** of a curved `A∞` category `𝒞` is a degree-zero endomorphism `e X` of
every object `X`, which is a two-sided identity for `m₂` and on which every operation of arity
other than two vanishes. This is the definition `TauCeti.AInfinityCategory.StrictUnit` of the
uncurved case; the curvature is not constrained by it.

Strict units are unique, are cycles for the unary operation, and restrict to strict units of the
endomorphism algebras. An operation of arity other than two vanishes on a tuple containing a scalar
multiple of a strict unit, and `m₂` with a scalar multiple `c • e` on either side is scalar
multiplication by `c`. The strict units of an uncurved `A∞` category are those of it as a curved
one.

## Main definitions

* `TauCeti.CurvedAInfinityCategory.StrictUnit`: a family of strict units of a curved `A∞`
  category.

## Main results

* `TauCeti.CurvedAInfinityCategory.StrictUnit.eq`: strict units are unique.
* `TauCeti.CurvedAInfinityCategory.StrictUnit.m_eq_zero_of_eq_smul`: an operation of arity other
  than two vanishes on a scalar multiple of a strict unit.
* `TauCeti.CurvedAInfinityCategory.StrictUnit.endAlgebra`: a strict unit of `𝒞` at `X` is a strict
  unit of the endomorphism algebra of `X`.
* `TauCeti.CurvedAInfinityCategory.strictUnit_iff_of_m_eq`: a curved and an uncurved `A∞`
  category with the same operations have the same strict units.
* `TauCeti.AInfinityCategory.strictUnit_toCurvedAInfinityCategory_iff`: the strict units of an
  uncurved `A∞` category are those of it as a curved one.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.5 and 7.1, for strict
  units.
-/

public section

namespace TauCeti

universe u v w

open GradedLinearQuiver AInfinity

namespace CurvedAInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- A family of **strict units** for a curved `A∞` category, as for uncurved ones.

For every object `X`, the endomorphism `e X` has degree zero. These endomorphisms are the left and
right identities for `m₂`, and every operation of arity other than two vanishes on a tuple
containing an included identity. The curvature is not constrained. -/
structure StrictUnit (𝒞 : CurvedAInfinityCategory R C)
    (e : ∀ X : C, homModule (R := R) X X) : Prop where
  /-- Every identity has degree zero. -/
  degree_zero (X : C) : e X ∈ (grading (R := R) X X).piece 0
  /-- The identity at the target is a left identity for `m₂`. -/
  binary_left (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion Y Y (e Y), homInclusion X Y f] = homInclusion X Y f
  /-- The identity at the source is a right identity for `m₂`. -/
  binary_right (X Y : C) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion X Y f, homInclusion X X (e X)] = homInclusion X Y f
  /-- Every operation of arity other than two vanishes on a tuple containing an included
  identity. -/
  higher (n : ℕ) (hn : n ≠ 2) (x : Fin n → TotalHom R C) :
    (∃ i X, x i = homInclusion X X (e X)) → 𝒞.m n x = 0

attribute [simp] StrictUnit.binary_left StrictUnit.binary_right

namespace StrictUnit

variable {𝒞 : CurvedAInfinityCategory R C} {e e' : ∀ X : C, homModule (R := R) X X}

/-- An operation of arity other than two vanishes when one of its inputs is a scalar multiple of
an included strict identity. -/
theorem m_eq_zero_of_eq_smul (h : 𝒞.StrictUnit e) {n : ℕ} (hn : n ≠ 2)
    (x : Fin n → TotalHom R C) {i : Fin n} {X : C} {c : R}
    (hi : x i = c • homInclusion X X (e X)) : 𝒞.m n x = 0 := by
  rw [← Function.update_eq_self i x, hi, (𝒞.m n).map_update_smul,
    h.higher n hn _ ⟨i, X, Function.update_self ..⟩, smul_zero]

/-- An included strict identity is closed under the unary operation. -/
@[simp]
theorem unary_eq_zero (h : 𝒞.StrictUnit e) (X : C) : 𝒞.m 1 ![homInclusion X X (e X)] = 0 :=
  h.higher 1 (by decide) _ ⟨0, X, rfl⟩

/-- Composing on the left with a scalar multiple of the strict identity at the target is scalar
multiplication. -/
theorem m_two_smul_left (h : 𝒞.StrictUnit e) {X Y : C} (c : R) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![c • homInclusion Y Y (e Y), homInclusion X Y f] = c • homInclusion X Y f := by
  have hu (y : TotalHom R C) :
      Function.update ![homInclusion Y Y (e Y), homInclusion X Y f] 0 y =
        ![y, homInclusion X Y f] :=
    Fin.update_cons_zero ..
  rw [← hu, (𝒞.m 2).map_update_smul, hu, h.binary_left, RingHom.id_apply]

/-- Composing on the right with a scalar multiple of the strict identity at the source is scalar
multiplication. -/
theorem m_two_smul_right (h : 𝒞.StrictUnit e) {X Y : C} (c : R) (f : homModule (R := R) X Y) :
    𝒞.m 2 ![homInclusion X Y f, c • homInclusion X X (e X)] = c • homInclusion X Y f := by
  have hu (y : TotalHom R C) :
      Function.update ![homInclusion X Y f, homInclusion X X (e X)] 1 y =
        ![homInclusion X Y f, y] := by
    ext i
    fin_cases i <;> rfl
  rw [← hu, (𝒞.m 2).map_update_smul, hu, h.binary_right, RingHom.id_apply]

/-- A family of strict identities in a curved `A∞` category is unique. -/
theorem eq (h : 𝒞.StrictUnit e) (h' : 𝒞.StrictUnit e') : e = e' := by
  funext X
  apply homInclusion_injective X X
  calc
    homInclusion X X (e X) = 𝒞.m 2 ![homInclusion X X (e' X), homInclusion X X (e X)] :=
      (h'.binary_left X X (e X)).symm
    _ = homInclusion X X (e' X) := h.binary_right X X (e' X)

/-- **A strict unit restricts to the endomorphism algebras**: the strict identity of `X` is a
strict unit of the curved `A∞` algebra of endomorphisms of `X`. -/
theorem endAlgebra (h : 𝒞.StrictUnit e) (X : C) : (𝒞.endAlgebra X).StrictUnit (e X) where
  degree_zero := by simpa using h.degree_zero X
  binary_left f := homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X two_pos]
    convert h.binary_left X X f using 2
    ext i
    fin_cases i <;> rfl
  binary_right f := homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X two_pos]
    convert h.binary_right X X f using 2
    ext i
    fin_cases i <;> rfl
  higher n hn y := fun ⟨i, hi⟩ ↦ homInclusion_injective X X <| by
    rw [𝒞.homInclusion_endAlgebra_m X (Fin.pos i), map_zero]
    exact h.higher n hn _ ⟨i, X, by rw [hi]⟩

end StrictUnit

/-! ### Comparison with uncurved strict units -/

/-- The strict units of a curved `A∞` category are those of any uncurved `A∞` category with the
same operations: both notions only read the operations on the total module of morphisms. -/
theorem strictUnit_iff_of_m_eq {𝒞 : AInfinityCategory R C} {𝒟 : CurvedAInfinityCategory R C}
    (hm : 𝒟.m = 𝒞.m) {e : ∀ X : C, homModule (R := R) X X} :
    𝒟.StrictUnit e ↔ 𝒞.StrictUnit e := by
  have hl (X Y : C) (f : homModule (R := R) X Y) :
      𝒞.comp X Y Y (e Y) f = f ↔ 𝒟.m 2 ![homInclusion Y Y (e Y), homInclusion X Y f] =
        homInclusion X Y f := by
    rw [hm, ← 𝒞.homInclusion_comp, (homInclusion_injective X Y).eq_iff]
  have hr (X Y : C) (f : homModule (R := R) X Y) :
      𝒞.comp X X Y f (e X) = f ↔ 𝒟.m 2 ![homInclusion X Y f, homInclusion X X (e X)] =
        homInclusion X Y f := by
    rw [hm, ← 𝒞.homInclusion_comp, (homInclusion_injective X Y).eq_iff]
  refine ⟨fun h ↦ ⟨h.degree_zero, fun X Y f ↦ (hl X Y f).2 (h.binary_left X Y f),
    fun X Y f ↦ (hr X Y f).2 (h.binary_right X Y f), fun n hn x hx ↦ hm ▸ h.higher n hn x hx⟩,
    fun h ↦ ⟨h.degree_zero, fun X Y f ↦ (hl X Y f).1 (h.binary_left X Y f),
      fun X Y f ↦ (hr X Y f).1 (h.binary_right X Y f), fun n hn x hx ↦ hm ▸ h.higher n hn x hx⟩⟩

end CurvedAInfinityCategory

namespace AInfinityCategory

variable {R : Type w} [CommRing R] {C : Type u} [GradedLinearQuiver.{u, v, w} R C]

/-- The strict units of an uncurved `A∞` category are those of it as a curved one. -/
@[simp]
theorem strictUnit_toCurvedAInfinityCategory_iff {𝒞 : AInfinityCategory R C}
    {e : ∀ X : C, homModule (R := R) X X} :
    𝒞.toCurvedAInfinityCategory.StrictUnit e ↔ 𝒞.StrictUnit e :=
  CurvedAInfinityCategory.strictUnit_iff_of_m_eq 𝒞.toCurvedAInfinityCategory_m

/-- A strict unit of an uncurved `A∞` category is a strict unit of it as a curved one. -/
theorem StrictUnit.toCurvedAInfinityCategory {𝒞 : AInfinityCategory R C}
    {e : ∀ X : C, homModule (R := R) X X} (h : 𝒞.StrictUnit e) :
    𝒞.toCurvedAInfinityCategory.StrictUnit e :=
  strictUnit_toCurvedAInfinityCategory_iff.2 h

end AInfinityCategory

end TauCeti
