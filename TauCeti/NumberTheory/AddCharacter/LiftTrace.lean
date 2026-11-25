/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.Trace.Basic

/-!
# Lifting additive characters through the trace

For an extension `E/F` of commutative rings and an additive character `ψ` of `F`, the character
`ψ.liftTrace E` of `E` is `ψ ∘ Tr_{E/F}`, where `Tr_{E/F} = Algebra.trace F E` is the trace. For a
finite extension of finite fields it is the additive character against which the Gauss sum of a
norm-lifted multiplicative character is taken in the Hasse–Davenport relation, and it carries the
canonical additive character of `F` to that of `E` (`TauCeti.FiniteField.liftTrace_stdAddChar`).

Lifting is compatible with the group structure of the characters and with shifts, and it is
transitive in a tower of finite free extensions, by the transitivity of the trace
(`Algebra.trace_trace`). For a finite separable extension of fields the trace is surjective
(`Algebra.trace_surjective`), so lifting is injective and preserves primitivity.

## Main definitions

* `AddChar.liftTrace`: the lift `ψ ∘ Tr_{E/F}` of an additive character of `F` to `E`.

## Main results

* `AddChar.liftTrace_mulShift`: the lift of the shift of `ψ` by `a ∈ F` is the shift of the lift
  by the image of `a` in `E`.
* `AddChar.liftTrace_liftTrace`: lifting is transitive in a tower `F ⊆ E ⊆ K`.
* `AddChar.liftTrace_injective`: for a finite separable extension of fields, lifting is injective.
* `AddChar.IsPrimitive.liftTrace`: for a finite separable extension of fields, the lift of a
  primitive character is primitive.

## References

* R. Lidl and H. Niederreiter, *Finite Fields*, Chapter 5, §1 and §5.2.
-/

public section

namespace AddChar

section CommRing

variable {F : Type*} [CommRing F] (E : Type*) [CommRing E] [Algebra F E]
  {R : Type*} [CommMonoid R]

/-- The **lift of an additive character through the trace**: for an extension `E/F` and an
additive character `ψ` of `F`, the character `ψ ∘ Tr_{E/F}` of `E`. -/
noncomputable def liftTrace (ψ : AddChar F R) : AddChar E R :=
  ψ.compAddMonoidHom (Algebra.trace F E).toAddMonoidHom

variable {E}

/-- The lift of `ψ` takes the value `ψ (Tr_{E/F} x)` at `x`. -/
@[simp]
theorem liftTrace_apply (ψ : AddChar F R) (x : E) : ψ.liftTrace E x = ψ (Algebra.trace F E x) :=
  (rfl)

variable (E)

/-- The lift of the trivial character is trivial. -/
@[simp]
theorem liftTrace_one : (1 : AddChar F R).liftTrace E = 1 := by
  ext x
  rw [liftTrace_apply, one_apply, one_apply]

/-- Lifting is multiplicative. -/
@[simp]
theorem liftTrace_mul (ψ ψ' : AddChar F R) :
    (ψ * ψ').liftTrace E = ψ.liftTrace E * ψ'.liftTrace E := by
  ext x
  simp only [liftTrace_apply, mul_apply]

/-- Lifting commutes with inverses. -/
@[simp]
theorem liftTrace_inv (ψ : AddChar F R) : ψ⁻¹.liftTrace E = (ψ.liftTrace E)⁻¹ := by
  ext x
  simp only [liftTrace_apply, inv_apply, map_neg]

/-- The lift of the shift `x ↦ ψ (a x)` is the shift of the lift by the image of `a` in `E`. -/
@[simp]
theorem liftTrace_mulShift (ψ : AddChar F R) (a : F) :
    (ψ.mulShift a).liftTrace E = (ψ.liftTrace E).mulShift (algebraMap F E a) := by
  ext x
  rw [liftTrace_apply, mulShift_apply, mulShift_apply, liftTrace_apply, ← Algebra.smul_def,
    map_smul, smul_eq_mul]

/-- **Transitivity of lifting.** In a tower `F ⊆ E ⊆ K` of finite free extensions, lifting from
`F` to `E` and then to `K` is lifting from `F` to `K`. -/
@[simp]
theorem liftTrace_liftTrace (K : Type*) [CommRing K] [Algebra F K] [Algebra E K]
    [IsScalarTower F E K] [Module.Free F E] [Module.Finite F E] [Module.Free E K]
    [Module.Finite E K] (ψ : AddChar F R) :
    (ψ.liftTrace E).liftTrace K = ψ.liftTrace K := by
  ext x
  simp only [liftTrace_apply, Algebra.trace_trace]

end CommRing

section Field

variable {F : Type*} [Field F] (E : Type*) [Field E] [Algebra F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] {R : Type*} [CommMonoid R]

/-- For a finite separable extension of fields, lifting additive characters through the trace is
injective, the trace being surjective. -/
theorem liftTrace_injective : Function.Injective (liftTrace (F := F) (R := R) E) :=
  compAddMonoidHom_injective_left _ (Algebra.trace_surjective F E)

variable {E}

/-- For a finite separable extension of fields, two additive characters with the same lift are
equal. -/
@[simp]
theorem liftTrace_inj {ψ ψ' : AddChar F R} : ψ.liftTrace E = ψ'.liftTrace E ↔ ψ = ψ' :=
  (liftTrace_injective E).eq_iff

/-- For a finite separable extension of fields, an additive character lifts to the trivial
character only if it is trivial. -/
@[simp]
theorem liftTrace_eq_one_iff {ψ : AddChar F R} : ψ.liftTrace E = 1 ↔ ψ = 1 :=
  (liftTrace_injective E).eq_iff' (liftTrace_one E)

variable (E) in
/-- For a finite separable extension of fields, the lift of a primitive additive character through
the trace is primitive. -/
theorem IsPrimitive.liftTrace {ψ : AddChar F R} (hψ : ψ.IsPrimitive) :
    (ψ.liftTrace E).IsPrimitive :=
  IsPrimitive.of_ne_one (liftTrace_eq_one_iff.not.2 fun h1 ↦ hψ one_ne_zero (by simp [h1]))

end Field

end AddChar
