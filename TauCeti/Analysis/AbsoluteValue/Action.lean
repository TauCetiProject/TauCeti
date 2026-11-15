/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# The action of algebra automorphisms on absolute values

For an `R`-algebra `F`, the group `F ≃ₐ[R] F` acts on the absolute values of `F` by
`σ • w = w ∘ σ⁻¹`, that is, `(σ • w) x = w (σ⁻¹ x)`. This extends Mathlib's action of
`Gal(K/k)` on the infinite places of a number field `K` to all absolute values
(`NumberField.InfinitePlace.coe_smul`). For a finite extension of number fields `F / K` this is
the action that permutes the absolute values of `F` lying over a given place of `K`. These need
not be places of `F`: over a finite place they are in general real powers of finite places. That
is why the action is defined on all of `AbsoluteValue F S`, rather than on a type of places.

Since `σ` fixes `R`, it does not change the restriction of an absolute value to `R`
(`AbsoluteValue.under_smul`), so it preserves the relation `AbsoluteValue.LiesOver`.

The same action, under the same name, is defined in Ralf Stephan's `rwst/Subspace-Theorems` at
`09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file `DiophantineApproximation/ConjugatePlaces.lean`
(Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3, Corollaries 1.3.2 and 1.3.5.
-/

public section

namespace AbsoluteValue

variable {R F S : Type*} [CommSemiring R] [Semiring F] [Algebra R F] [Semiring S] [PartialOrder S]

/-- The algebra automorphisms of `F` act on the absolute values of `F` by `σ • w = w ∘ σ⁻¹`. -/
instance instMulActionAlgEquiv : MulAction (F ≃ₐ[R] F) (AbsoluteValue F S) where
  smul σ w := w.comp (f := (σ.symm : F ≃+* F).toRingHom) σ.symm.injective
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp]
theorem smul_apply (σ : F ≃ₐ[R] F) (w : AbsoluteValue F S) (x : F) : (σ • w) x = w (σ.symm x) :=
  rfl

variable [FaithfulSMul R F]

/-- An algebra automorphism does not change the restriction of an absolute value to the base. -/
@[simp]
theorem under_smul (σ : F ≃ₐ[R] F) (w : AbsoluteValue F S) : (σ • w).under R = w.under R :=
  ext fun x ↦ by simp [under_def]

@[simp]
theorem liesOver_smul_iff {σ : F ≃ₐ[R] F} {w : AbsoluteValue F S} {v : AbsoluteValue R S} :
    (σ • w).LiesOver v ↔ w.LiesOver v :=
  ⟨fun ⟨h⟩ ↦ ⟨by rwa [under_smul] at h⟩, fun ⟨h⟩ ↦ ⟨by rwa [under_smul]⟩⟩

instance (σ : F ≃ₐ[R] F) (w : AbsoluteValue F S) (v : AbsoluteValue R S) [w.LiesOver v] :
    (σ • w).LiesOver v :=
  liesOver_smul_iff.mpr ‹_›

end AbsoluteValue
