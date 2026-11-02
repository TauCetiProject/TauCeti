/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Differential
-- Proof-only: a separable isogeny has trivial different.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Unramified
-- Proof-only: the Kähler pullback is the cotrace of Weil differentials.
import TauCeti.FieldTheory.FunctionField.Differential.Pullback

/-!
# An isogeny pulls the invariant differential back to a constant multiple

Let `φ : W₁ → W₂` be an isogeny of elliptic curves over a field `F`, with invariant differentials
`ω₁` and `ω₂`. The differentials of `F(W₁)` form a one-dimensional `F(W₁)`-vector space spanned by
`ω₁`, so `φ^*ω₂ = a ω₁` for a unique function `a ∈ F(W₁)`. This file proves that `a` is a
**constant**: `φ^*ω₂ = c ω₁` with a unique `c ∈ F` (Silverman, III.5). The same holds for every
morphism `W₁ → W₂`, the zero morphism pulling `ω₂` back to `0`.

This constant compares the invariant differentials of isogenous curves; it is the input for
comparing their real periods.

If `φ` is inseparable then `φ^*ω₂ = 0`
(`TauCeti.Isogeny.isSeparable_iff_pullbackDifferential_ne_zero`), so `c = 0`. If `φ` is separable,
compare divisors through the Kähler–Weil comparison, which carries the pullback `φ^*` to the cotrace
of Weil differentials (`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_map`). The
divisor of the cotrace of `ω₂` is `Con (ω₂) + Diff(F(W₁)/F(W₂))`. Here `(ω₂) = 0` (Silverman,
Proposition III.1.5) and the different of a separable isogeny vanishes
(`TauCeti.Isogeny.different_eq_zero`), so `φ^*ω₂` has divisor zero, like `ω₁`. Hence `a` has no
zeros or poles, and since `F` is the exact constant field of `F(W₁)`, `a` is a constant.

## Main results

* `TauCeti.Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`:
  `φ^*ω₂ = c ω₁` for a unique `c ∈ F`.
* `TauCeti.Isogeny.isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul`: this constant is
  nonzero exactly when `φ` is separable, and `ne_zero_of_pullbackDifferential_eq_smul`: in
  characteristic zero it is always nonzero.
* `TauCeti.Isogeny.Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul`: the same
  for every morphism `W₁ → W₂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.5 and III.5.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.6 and Theorem 4.3.2.
-/

public section

open WeierstrassCurve.Affine

namespace TauCeti.Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

section Separable

variable (φ : Isogeny W₁ W₂) [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField]

/-- The Weil differential attached to the pullback of `ω₂` along a separable isogeny is nonzero. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_pullbackDifferential_ne_zero :
    letI := weilDifferentialSpaceModule W₁.isFunctionField
    ((kaehlerDifferentialEquivWeilDifferentialOfSeparating W₁.isFunctionField
        (isIntegrallyClosedIn_functionField W₁) (transcendental_genericX W₁)
        (φ.pullbackDifferential (invariantDifferential W₂)) :
          ↥(weilDifferentialSpace F W₁.FunctionField)) :
        Module.Dual F ↥(repartitionSpace F W₁.FunctionField)) ≠ 0 := by
  let _ := weilDifferentialSpaceModule W₁.isFunctionField
  rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
  exact (isSeparable_iff_pullbackDifferential_ne_zero φ).mp ‹_›

/-- **A separable isogeny pulls the invariant differential back to a differential with divisor
zero**: under the Kähler–Weil comparison determined by `x`, `φ^*ω₂` is a Weil differential of
`F(W₁) / F` with neither zeros nor poles. -/
@[simp]
theorem weilDifferentialDivisor_pullbackDifferential_invariantDifferential :
    letI := weilDifferentialSpaceModule W₁.isFunctionField
    weilDifferentialDivisor W₁.isFunctionField (isIntegrallyClosedIn_functionField W₁)
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating W₁.isFunctionField
          (isIntegrallyClosedIn_functionField W₁) (transcendental_genericX W₁)
          (φ.pullbackDifferential (invariantDifferential W₂))).2
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating_pullbackDifferential_ne_zero φ) =
      0 := by
  let _ := weilDifferentialSpaceModule W₁.isFunctionField
  have hex₁ := isIntegrallyClosedIn_functionField W₁
  have hex₂ := isIntegrallyClosedIn_functionField W₂
  -- View `F(W₁)` as an `F(W₂)`-algebra through `φ`; then `φ^*` is `KaehlerDifferential.map`.
  let _ := φ.fieldPullback.toRingHom.toAlgebra
  have h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z :=
    RingHom.congr_fun (RingHom.algebraMap_toAlgebra φ.fieldPullback.toRingHom)
  have := φ.isScalarTower_of_algebraMap_eq_fieldPullback h
  have := φ.finiteDimensional_functionField h
  have := φ.isSeparable_functionField h
  -- The comparison carries `φ^*ω₂` to the cotrace of `ω₂`, whose divisor is
  -- `Con (ω₂) + Diff(F(W₁)/F(W₂)) = 0`.
  have hcot := kaehlerDifferentialEquivWeilDifferentialOfSeparating_map W₂.isFunctionField
    W₁.isFunctionField hex₂ hex₁ (transcendental_genericX W₂) (transcendental_genericX W₁)
    (invariantDifferential W₂)
  rw [kaehlerDifferentialMap_eq_pullbackDifferential φ h] at hcot
  have hω₂ : kaehlerDifferentialEquivWeilDifferentialOfSeparating W₂.isFunctionField hex₂
      (transcendental_genericX W₂) (invariantDifferential W₂) ≠ 0 := by
    rw [ne_eq, LinearEquiv.map_eq_zero_iff]
    exact invariantDifferential_ne_zero W₂
  rw [weilDifferentialDivisor_congr _ _ (congrArg Subtype.val hcot) _ _ (Submodule.coe_mem _),
    weilDifferentialDivisor_weilDifferentialCotrace _ _ hex₂ hex₁ _ hω₂,
    weilDifferentialDivisor_invariantDifferential, map_zero, zero_add, different_eq_zero φ h]
  rwa [ne_eq, ZeroMemClass.coe_eq_zero, weilDifferentialCotrace_eq_zero_iff]

end Separable

/-- **An isogeny pulls the invariant differential back to a constant multiple** (Silverman, III.5):
`φ^*ω₂ = c ω₁` for a unique constant `c ∈ F`, where `ω₁` and `ω₂` are the invariant differentials.
By `TauCeti.Isogeny.isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul`, the constant is
nonzero exactly when `φ` is separable. -/
theorem existsUnique_pullbackDifferential_invariantDifferential_eq_smul (φ : Isogeny W₁ W₂) :
    ∃! c : F, φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁ := by
  refine existsUnique_of_exists_of_unique ?_ fun c c' hc hc' ↦
    smul_left_injective F (invariantDifferential_ne_zero W₁) (hc.symm.trans hc')
  by_cases hsep : Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField
  swap
  · refine ⟨0, ?_⟩
    rw [zero_smul]
    exact not_not.mp ((isSeparable_iff_pullbackDifferential_ne_zero φ).not.mp hsep)
  let _ := weilDifferentialSpaceModule W₁.isFunctionField
  have hex₁ := isIntegrallyClosedIn_functionField W₁
  -- Write `φ^*ω₂ = a ω₁` with `a ∈ F(W₁)`, necessarily nonzero.
  obtain ⟨a, ha, -⟩ := existsUnique_smul_invariantDifferential W₁
    (φ.pullbackDifferential (invariantDifferential W₂))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact (isSeparable_iff_pullbackDifferential_ne_zero φ).mp hsep (by rw [← ha, zero_smul])
  -- Both `ω₁` and `φ^*ω₂ = a ω₁` have divisor zero, and `(a ω₁) = div a + (ω₁)`.
  have hcoe : repartitionDualMul W₁.isFunctionField a
      (kaehlerDifferentialEquivWeilDifferentialOfSeparating W₁.isFunctionField hex₁
        (transcendental_genericX W₁) (invariantDifferential W₁)) =
      kaehlerDifferentialEquivWeilDifferentialOfSeparating W₁.isFunctionField hex₁
        (transcendental_genericX W₁) (φ.pullbackDifferential (invariantDifferential W₂)) := by
    rw [← coe_weilDifferentialSpaceModule_smul, ← map_smul, ha]
  have hdiv := (weilDifferentialDivisor_repartitionDualMul W₁.isFunctionField hex₁
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating W₁.isFunctionField hex₁
      (transcendental_genericX W₁) (invariantDifferential W₁)).2
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero W₁)
    (Units.mk0 a ha0)).symm.trans ((weilDifferentialDivisor_congr _ _ hcoe _ _ (Submodule.coe_mem _)
      (kaehlerDifferentialEquivWeilDifferentialOfSeparating_pullbackDifferential_ne_zero φ)).trans
        (weilDifferentialDivisor_pullbackDifferential_invariantDifferential φ))
  rw [weilDifferentialDivisor_invariantDifferential W₁, add_zero] at hdiv
  -- So `a` has divisor zero, hence is a constant.
  obtain ⟨c, hc⟩ := (Divisor.principal_eq_zero_iff W₁.isFunctionField hex₁ _).mp hdiv
  rw [Units.val_mk0] at hc
  exact ⟨c, by rw [← ha, ← hc, algebraMap_smul]⟩

/-- **The constant is nonzero exactly when the isogeny is separable**: if `φ^*ω₂ = c ω₁` for a
constant `c ∈ F`, then `φ` is separable if and only if `c ≠ 0`. -/
theorem isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul (φ : Isogeny W₁ W₂) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.FunctionField ↔ c ≠ 0 := by
  rw [isSeparable_iff_pullbackDifferential_ne_zero, hc,
    smul_ne_zero_iff_left (invariantDifferential_ne_zero W₁)]

/-- **In characteristic zero the constant is nonzero**: every isogeny is separable, so if
`φ^*ω₂ = c ω₁` then `c ≠ 0`. -/
theorem ne_zero_of_pullbackDifferential_eq_smul [CharZero F] (φ : Isogeny W₁ W₂) {c : F}
    (hc : φ.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁) :
    c ≠ 0 :=
  (isSeparable_iff_ne_zero_of_pullbackDifferential_eq_smul φ hc).mp inferInstance

/-- **A morphism pulls the invariant differential back to a constant multiple**: for every
morphism `f : W₁ → W₂`, `f^*ω₂ = c ω₁` for a unique constant `c ∈ F`, with `c = 0` for the zero
morphism. -/
theorem Hom.existsUnique_pullbackDifferential_invariantDifferential_eq_smul (f : Hom W₁ W₂) :
    ∃! c : F, f.pullbackDifferential (invariantDifferential W₂) = c • invariantDifferential W₁ := by
  refine existsUnique_of_exists_of_unique ?_ fun c c' hc hc' ↦
    smul_left_injective F (invariantDifferential_ne_zero W₁) (hc.symm.trans hc')
  rcases Hom.eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩
  · exact ⟨0, by rw [Hom.pullbackDifferential_zero, LinearMap.zero_apply, zero_smul]⟩
  · rw [Hom.pullbackDifferential_ofIsogeny]
    exact (Isogeny.existsUnique_pullbackDifferential_invariantDifferential_eq_smul φ).exists

end TauCeti.Isogeny
