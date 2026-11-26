/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.WithAbs

/-!
# The action of ring automorphisms on absolute values

A group `G` acting on a semiring `F` by ring automorphisms (`MulSemiringAction G F`) acts on the
absolute values of `F` by `g • w = w ∘ g⁻¹`, that is, `(g • w) x = w (g⁻¹ • x)`
(`AbsoluteValue.instMulAction`). This covers the Galois group `F ≃ₐ[R] F` of an `R`-algebra (through
Mathlib's `AlgEquiv.applyMulSemiringAction`, where `(σ • w) x = w (σ.symm x)` by
`AbsoluteValue.smul_apply`, `AlgEquiv.smul_def` and `AlgEquiv.aut_inv`), as well as an abstract
Galois group `G` acting on `F` with `IsGaloisGroup G K F`. For `F ≃ₐ[k] F` it extends Mathlib's
action of `Gal(F/k)` on the infinite places of a number field `F` to all absolute values
(`NumberField.InfinitePlace.coe_smul`). For a finite extension of number fields `F / K` this is the
action that permutes the absolute values of `F` lying over a given place of `K`. These need not be
places of `F`: over a finite place they are in general real powers of finite places. That is why the
action is defined on all of `AbsoluteValue F S`, rather than on a type of places.

If `F` is an `R`-algebra and the action of `G` commutes with that of `R`
(`SMulCommClass G R F`), then `g` fixes `R`, so it does not change the restriction of an absolute
value to `R` (`AbsoluteValue.under_smul`) and it preserves the relation `AbsoluteValue.LiesOver`.
If instead `G` maps `R` to itself (`SMulDistribClass G R F`), restricting to `R` commutes with the
action (`AbsoluteValue.smul_under`). The action also preserves nonarchimedean absolute values
(`AbsoluteValue.isNonarchimedean_smul_iff`).

The action of `F ≃ₐ[R] F`, under the name `instMulActionAlgEquiv`, is also defined in Ralf
Stephan's `rwst/Subspace-Theorems` at `09835cb23557ae5ae0cf55a9c4ab9055f5d60338`, file
`DiophantineApproximation/ConjugatePlaces.lean` (Apache 2.0).

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  §1.3, Corollaries 1.3.2 and 1.3.5.
-/

public section

namespace AbsoluteValue

section MulAction

variable {G F S : Type*} [Group G] [Semiring F] [MulSemiringAction G F] [Semiring S]
  [PartialOrder S]

/-- A group acting on `F` by ring automorphisms acts on the absolute values of `F` by
`g • w = w ∘ g⁻¹`. -/
instance instMulAction : MulAction G (AbsoluteValue F S) where
  smul g w := w.comp (f := MulSemiringAction.toRingHom G F g⁻¹) (MulAction.injective g⁻¹)
  one_smul w := ext fun x ↦ congrArg w (by simp)
  mul_smul g h w := ext fun x ↦ congrArg w (by simp [mul_smul])

@[simp]
theorem smul_apply (g : G) (w : AbsoluteValue F S) (x : F) : (g • w) x = w (g⁻¹ • x) :=
  rfl

/-- A ring automorphism preserves the nonarchimedean absolute values. -/
@[simp]
theorem isNonarchimedean_smul_iff {S : Type*} [Semiring S] [LinearOrder S] {g : G}
    {w : AbsoluteValue F S} : IsNonarchimedean (g • w) ↔ IsNonarchimedean w := by
  refine ⟨fun h x y ↦ ?_, fun h x y ↦ by simpa [smul_add] using h (g⁻¹ • x) (g⁻¹ • y)⟩
  simpa [smul_add] using h (g • x) (g • y)

end MulAction

section LiesOver

variable {G R F S : Type*} [Group G] [CommSemiring R] [Semiring F] [Algebra R F]
  [FaithfulSMul R F] [MulSemiringAction G F] [SMulCommClass G R F] [Semiring S] [PartialOrder S]

/-- A ring automorphism that fixes `R` does not change the restriction of an absolute value to
`R`. -/
@[simp]
theorem under_smul (g : G) (w : AbsoluteValue F S) : (g • w).under R = w.under R :=
  ext fun x ↦ by simp [under_def]

@[simp]
theorem liesOver_smul_iff {g : G} {w : AbsoluteValue F S} {v : AbsoluteValue R S} :
    (g • w).LiesOver v ↔ w.LiesOver v :=
  ⟨fun ⟨h⟩ ↦ ⟨by rwa [under_smul] at h⟩, fun ⟨h⟩ ↦ ⟨by rwa [under_smul]⟩⟩

instance (g : G) (w : AbsoluteValue F S) (v : AbsoluteValue R S) [w.LiesOver v] :
    (g • w).LiesOver v :=
  liesOver_smul_iff.mpr ‹_›

end LiesOver

section Under

variable {G R F S : Type*} [Group G] [CommSemiring R] [Semiring F] [Algebra R F]
  [FaithfulSMul R F] [MulSemiringAction G R] [MulSemiringAction G F] [SMulDistribClass G R F]
  [Semiring S] [PartialOrder S]

/-- Restricting an absolute value to a subring `R` that `G` maps to itself commutes with the action
of `G`. -/
@[simp]
theorem smul_under (g : G) (w : AbsoluteValue F S) : g • w.under R = (g • w).under R :=
  ext fun x ↦ by rw [smul_apply, under_apply, under_apply, smul_apply, algebraMap.smul']

end Under

end AbsoluteValue
