/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Component.Base
public import TauCeti.LinearAlgebra.RootSystem.EquivComp

/-!
# Automorphisms restricted to irreducible components

When an automorphism `τ` of a finite root system fixes an irreducible component `C`, it restricts
to an automorphism `Equiv.restrictComponentAut τ C hC` of `P.componentPairing C`. This file
records its coercion and monoid laws, compatibility with `autCongr`, and preservation of the
component base `b.componentBase C`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Ch. VI §1, no. 2;
  J. S. Milne, *Algebraic Groups* (2017), Appendix C, C.23 and C.55.
-/

public section

namespace RootPairing

section Field

variable {ι ι₂ K M N M₂ N₂ : Type*} [Field K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup M₂] [Module K M₂] [AddCommGroup N₂] [Module K N₂]
  {P : RootPairing ι K M N} {Q : RootPairing ι₂ K M₂ N₂}
  [Finite ι] [Finite ι₂] [P.IsRootSystem] [Q.IsRootSystem]

section RestrictComponentAut

variable (τ : P.Aut) (C : P.Component) (hC : τ.componentEquiv C = C)

/-- **Restriction of a component-fixing automorphism to the component pairing.** -/
noncomputable def Equiv.restrictComponentAut : (P.componentPairing C).Aut :=
  Equiv.comp (P.componentPairingCongr hC) (τ.componentPairingEquiv C)

/-- The weight map of `restrictComponentAut` preserves `τ.weightMap` on ambient vectors. -/
@[simp] theorem Equiv.coe_restrictComponentAut_weightMap (x : P.componentSpace C) :
    ((τ.restrictComponentAut C hC).weightMap x : M) = τ.weightMap x := by
  simp [restrictComponentAut, Equiv.comp, Hom.comp]

/-- The weight equivalence of `restrictComponentAut` preserves `τ.weightMap` on ambient vectors. -/
theorem Equiv.coe_restrictComponentAut_weightEquiv (x : P.componentSpace C) :
    ((τ.restrictComponentAut C hC).weightEquiv x : M) = τ.weightMap x :=
  τ.coe_restrictComponentAut_weightMap C hC x

/-- The coweight map of `restrictComponentAut` preserves `τ.coweightMap` on ambient covectors. -/
@[simp] theorem Equiv.coe_restrictComponentAut_coweightMap (y : P.corootComponentSpace C) :
    ((τ.restrictComponentAut C hC).coweightMap y : N) = τ.coweightMap y := by
  simp [restrictComponentAut, Equiv.comp, Hom.comp]

/-- The index permutation of `restrictComponentAut` acts as `τ.indexEquiv`. -/
@[simp] theorem Equiv.coe_restrictComponentAut_indexEquiv (i : C.supp) :
    ((τ.restrictComponentAut C hC).indexEquiv i : ι) = τ.indexEquiv i := by
  simp [restrictComponentAut, Equiv.comp, Hom.comp]

/-- The inverse index permutation of `restrictComponentAut` acts as `τ.indexEquiv.symm`. -/
@[simp] theorem Equiv.coe_restrictComponentAut_indexEquiv_symm (i : C.supp) :
    ((τ.restrictComponentAut C hC).indexEquiv.symm i : ι) = τ.indexEquiv.symm i := by
  simp [restrictComponentAut, Equiv.comp, Hom.comp]

end RestrictComponentAut

/-- Restriction to a component respects equality of automorphisms. -/
theorem Equiv.restrictComponentAut_congr {τ₁ τ₂ : P.Aut} {C : P.Component}
    (h : τ₁ = τ₂) (h₁ : τ₁.componentEquiv C = C) (h₂ : τ₂.componentEquiv C = C) :
    τ₁.restrictComponentAut C h₁ = τ₂.restrictComponentAut C h₂ := by subst h; rfl

/-- The identity automorphism restricts to the identity on every component. -/
@[simp] theorem Equiv.restrictComponentAut_one (C : P.Component) :
    (1 : P.Aut).restrictComponentAut C (by simp) = 1 := by
  ext x <;> simp

/-- Restriction to a component is multiplicative. -/
theorem Equiv.restrictComponentAut_mul {τ₁ τ₂ : P.Aut} {C : P.Component}
    (h₁ : τ₁.componentEquiv C = C) (h₂ : τ₂.componentEquiv C = C) :
    (τ₁ * τ₂).restrictComponentAut C (by simp [h₁, h₂]) =
      τ₁.restrictComponentAut C h₁ * τ₂.restrictComponentAut C h₂ := by
  ext x <;> simp [HMul.hMul, Mul.mul, Equiv.comp, Hom.comp]

/-- Restriction to a component preserves inverses. -/
@[simp] theorem Equiv.restrictComponentAut_inv {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) :
    (τ⁻¹).restrictComponentAut C
        (by rw [componentEquiv_inv, _root_.Equiv.Perm.inv_eq_iff_eq, hC]) =
      (τ.restrictComponentAut C hC)⁻¹ :=
  eq_inv_of_mul_eq_one_left <| by
    rw [← restrictComponentAut_mul, restrictComponentAut_congr (inv_mul_cancel τ) _ (by simp),
      restrictComponentAut_one]

/-- Restriction to a component preserves natural powers. -/
@[simp] theorem Equiv.restrictComponentAut_pow {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) (n : ℕ) :
    (τ ^ n).restrictComponentAut C
        (by rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n) =
      τ.restrictComponentAut C hC ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : (τ ^ n).componentEquiv C = C := by
      rw [componentEquiv_pow]; exact Function.IsFixedPt.perm_pow hC n
    simp only [pow_succ', restrictComponentAut_mul hC hpow, ih]

/-- **Conjugating `τ.restrictComponentAut C hC` along `e.componentPairingEquiv C` restricts
`e.autCongr τ` to `e.componentEquiv C`.** -/
theorem Equiv.autCongr_restrictComponentAut (e : P.Equiv Q) {τ : P.Aut} {C : P.Component}
    (hC : τ.componentEquiv C = C) :
    (e.componentPairingEquiv C).autCongr (τ.restrictComponentAut C hC) =
      (e.autCongr τ).restrictComponentAut (e.componentEquiv C) (by simp [autCongr_apply, hC]) := by
  ext x <;> simp [autCongr_apply]

/-- A base-preserving automorphism fixing `C` permutes the simple roots of `b.componentBase C`. -/
theorem Equiv.mem_support_restrictComponentAut_indexEquiv_iff {τ : P.Aut} {b : P.Base}
    (hb : ∀ i, i ∈ b.support ↔ τ.indexEquiv i ∈ b.support) {C : P.Component}
    (hC : τ.componentEquiv C = C) (i : C.supp) :
    (τ.restrictComponentAut C hC).indexEquiv i ∈ (b.componentBase C).support ↔
      i ∈ (b.componentBase C).support := by
  rw [Base.mem_support_componentBase, Base.mem_support_componentBase,
    Equiv.coe_restrictComponentAut_indexEquiv, ← hb]

end Field

end RootPairing
