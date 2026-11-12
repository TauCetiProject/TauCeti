/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.Basic

/-!
# Reversing a simple-root crystal string

In a normal crystal, the involution reversing an `i`-string exchanges the raising and lowering
lengths and reflects the weight by the simple reflection. It gives a bijection between the
weight fibres at `μ` and `sᵢ μ`, without finiteness of the crystal or of the root system.

Only rank-one normality is used here. In particular, this file does not assert that these
involutions satisfy the braid relations on an arbitrary normal crystal. Their weight-fibre
bijections suffice to prove reflection invariance of finite crystal characters.

## References

* D. Bump and A. Schilling, *Crystal bases: representations and combinatorics*,
  World Scientific (2017), Ch. 2 (strings and crystal reflections).
-/

public section

namespace TauCeti.NormalCrystal

variable {ι X Y B : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} (c : NormalCrystal P b B)
  (i : b.support)

/-- Reverse the simple-root string through `x`: lower `φ - ε` times in its upper half,
or raise `ε - φ` times in its lower half. -/
noncomputable def stringReflection (x : B) : B :=
  if c.ε i x ≤ c.φ i x then
    (c.fIter i (c.φ i x - c.ε i x) x).get (c.isSome_fIter_iff.mpr (Nat.sub_le _ _))
  else
    (c.eIter i (c.ε i x - c.φ i x) x).get (c.isSome_eIter_iff.mpr (Nat.sub_le _ _))

/-- In the upper half of a string, reversal is iterated lowering. -/
theorem fIter_eq_some_stringReflection {x : B} (h : c.ε i x ≤ c.φ i x) :
    c.fIter i (c.φ i x - c.ε i x) x = some (c.stringReflection i x) := by
  unfold stringReflection
  rw [ite_eq_left h]
  exact (Option.some_get _).symm

/-- In the lower half of a string, reversal is iterated raising. Equality belongs to both
halves, since reversal then fixes the middle of the string. -/
theorem eIter_eq_some_stringReflection {x : B} (h : c.φ i x ≤ c.ε i x) :
    c.eIter i (c.ε i x - c.φ i x) x = some (c.stringReflection i x) := by
  by_cases h' : c.ε i x ≤ c.φ i x
  · have heq := le_antisymm h' h
    have hf := c.fIter_eq_some_stringReflection i h'
    simpa [heq] using hf
  · unfold stringReflection
    rw [ite_eq_right h']
    exact (Option.some_get _).symm

/-- String reversal exchanges raising and lowering lengths. -/
@[simp]
theorem ε_stringReflection (x : B) : c.ε i (c.stringReflection i x) = c.φ i x := by
  by_cases h : c.ε i x ≤ c.φ i x
  · have := c.ε_of_fIter_eq_some (c.fIter_eq_some_stringReflection i h)
    omega
  · have := c.ε_of_eIter_eq_some
      (c.eIter_eq_some_stringReflection i (le_of_not_ge h))
    omega

/-- String reversal exchanges lowering and raising lengths. -/
@[simp]
theorem φ_stringReflection (x : B) : c.φ i (c.stringReflection i x) = c.ε i x := by
  by_cases h : c.ε i x ≤ c.φ i x
  · have := c.φ_of_fIter_eq_some (c.fIter_eq_some_stringReflection i h)
    omega
  · have := c.φ_of_eIter_eq_some
      (c.eIter_eq_some_stringReflection i (le_of_not_ge h))
    omega

/-- Reversing a string twice is the identity. -/
@[simp]
theorem stringReflection_stringReflection (x : B) :
    c.stringReflection i (c.stringReflection i x) = x := by
  by_cases h : c.ε i x ≤ c.φ i x
  · have hback := c.eIter_eq_some_stringReflection i
      (x := c.stringReflection i x) (by simpa using h)
    simp only [ε_stringReflection, φ_stringReflection] at hback
    exact Option.some.inj (hback.symm.trans
      (c.fIter_eq_some_iff.mp (c.fIter_eq_some_stringReflection i h)))
  · have hback := c.fIter_eq_some_stringReflection i
      (x := c.stringReflection i x) (by simpa using le_of_not_ge h)
    simp only [ε_stringReflection, φ_stringReflection] at hback
    exact Option.some.inj (hback.symm.trans
      (c.fIter_eq_some_iff.mpr (c.eIter_eq_some_stringReflection i (le_of_not_ge h))))

/-- The involutive permutation reversing every `i`-string. This is not a strict crystal
isomorphism: it reflects, rather than preserves, weights. -/
noncomputable def stringReflectionEquiv : B ≃ B :=
  Function.Involutive.toPerm (c.stringReflection i) (c.stringReflection_stringReflection i)

@[simp]
theorem stringReflectionEquiv_apply (x : B) :
    c.stringReflectionEquiv i x = c.stringReflection i x := (rfl)

@[simp]
theorem stringReflectionEquiv_symm :
    (c.stringReflectionEquiv i).symm = c.stringReflectionEquiv i := (rfl)

/-- Reversing an `i`-string acts on weights by the actual simple-root reflection. -/
@[simp]
theorem wt_stringReflection (x : B) :
    c.wt (c.stringReflection i x) = P.reflection i (c.wt x) := by
  have hpair := c.φ_sub_ε i x
  simp only [P.reflection_apply, LinearMap.flip_apply, ← hpair]
  by_cases h : c.ε i x ≤ c.φ i x
  · rw [c.wt_of_fIter_eq_some (c.fIter_eq_some_stringReflection i h)]
    push_cast [Nat.cast_sub h, ← Nat.cast_smul_eq_nsmul ℤ]
    module
  · rw [c.wt_of_eIter_eq_some (c.eIter_eq_some_stringReflection i (le_of_not_ge h))]
    push_cast [Nat.cast_sub (le_of_not_ge h), ← Nat.cast_smul_eq_nsmul ℤ]
    module

/-- String reversal fixes an element exactly when its weight lies on the simple wall. -/
@[simp]
theorem stringReflection_eq_self_iff (x : B) :
    c.stringReflection i x = x ↔ P.toLinearMap (c.wt x) (P.coroot i) = 0 := by
  have hlen := c.φ_sub_ε i x
  constructor
  · intro h
    have hswap := c.ε_stringReflection i x
    rw [h] at hswap
    omega
  · intro h
    have heq : c.ε i x = c.φ i x := by omega
    have hf := c.fIter_eq_some_stringReflection i heq.le
    simpa [heq] using hf.symm

/-- String reversal identifies the weight fibres at `μ` and `sᵢ μ`. -/
noncomputable def weightFiberReflectionEquiv (μ : X) :
    {x : B // c.wt x = μ} ≃ {x : B // c.wt x = P.reflection i μ} :=
  (c.stringReflectionEquiv i).subtypeEquiv fun x => by
    simp [(P.reflection i).injective.eq_iff]

@[simp]
theorem weightFiberReflectionEquiv_apply (μ : X) (x : {x : B // c.wt x = μ}) :
    (c.weightFiberReflectionEquiv i μ x).val = c.stringReflection i x := (rfl)

/-- Reflection preserves weight multiplicities. `Nat.card` also makes sense without a
finiteness assumption, although finite fibres are the usual application. -/
@[simp]
theorem card_weightFiber_reflection (μ : X) :
    Nat.card {x : B // c.wt x = P.reflection i μ} = Nat.card {x : B // c.wt x = μ} :=
  (Nat.card_congr (c.weightFiberReflectionEquiv i μ)).symm

end TauCeti.NormalCrystal
