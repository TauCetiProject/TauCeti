/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.CoeffAction
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Degree
import TauCeti.NumberTheory.ModularForms.LevelOne.FunctionField

/-!
# Modular functions of level `N` holomorphic on `Y(N)`

Let `ℂ(X(N))` be the field of meromorphic functions on the compactified modular curve `X(N)`,
and `Y(N) = Γ(N) \ ℍ` the open modular curve, the complement of the cusps. The functions without
poles on `Y(N)` form a `ℂ`-subalgebra of `ℂ(X(N))`, written `𝒪(Y(N))` here
(`TauCeti.RiemannSurface.MeromorphicFunction.holomorphicSubalgebra` of the range of
`Subgroup.CompactifiedQuotient.ofQuotient`). For a modular form `f` of weight `k` on `Γ(N)`, the
quotient `f ^ 12 / Δ ^ k` lies in `𝒪(Y(N))`, since the discriminant `Δ` has no zero on `ℍ`.

This file identifies `𝒪(Y(N))` algebraically, as the integral closure of `ℂ[j]` in `ℂ(X(N))`
(`TauCeti.isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra`), the case `H = Γ(N)` of
`Subgroup.isIntegral_adjoin_jMeromorphicFunction_iff`. The pullback of `j` itself has no pole on
`Y(N)`, since the functions on `X(1)` with no pole on `Y(1)` are the polynomials in `j`
(`TauCeti.ModularGroup.holomorphicSubalgebra_range_ofQuotient_eq_adjoin`), and the fractional
linear action of `SL(2, ℤ/Nℤ)` on `ℂ(X(N))` preserves `𝒪(Y(N))`.

The ring `ℂ[j]` is defined without reference to values: its elements are the polynomials in `j`
with complex coefficients. So `𝒪(Y(N))` is preserved by every ring automorphism of `ℂ(X(N))`
which maps `ℂ` onto `ℂ` and fixes `j`. In particular it is preserved by the action of the
automorphisms `σ` of `ℂ` through the Fourier coefficients at `∞`
(`TauCeti.modularFunctionCoeffAction_mem_holomorphicSubalgebra_iff`), even though `σ` need not be
continuous and `F^σ` is not computed from the values of `F`. This is the step of Shimura's
construction of Galois conjugates of modular forms that controls their poles on `ℍ`.

## Main declarations

* `TauCeti.jPolynomialSubalgebra`: the ring `ℂ[j]` of polynomials in `j`, inside `ℂ(X(N))`.
* `TauCeti.unop_modularFunctionActionZMod_mem_holomorphicSubalgebra_iff`: the action of
  `SL(2, ℤ/Nℤ)` preserves `𝒪(Y(N))`.
* `TauCeti.isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra`: `𝒪(Y(N))` is the
  integral closure of `ℂ[j]` in `ℂ(X(N))`.
* `TauCeti.modularFunctionCoeffAction_mem_holomorphicSubalgebra_iff` and
  `TauCeti.forall_ne_infty_modularFunctionCoeffAction_iff`: the automorphisms of `ℂ`, acting
  through the Fourier coefficients, preserve `𝒪(Y(N))`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.4, 6.1–6.2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Subgroup.CompactifiedQuotient UpperHalfPlane
open TauCeti.RiemannSurface TauCeti.RiemannSurface.MeromorphicFunction OnePoint
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- Coefficient conjugation preserves the modular functions of level `N` integral over `ℂ[j]`. -/
private theorem isIntegral_adjoin_jMeromorphicFunction_coeffAction
    (σ : ℂ ≃+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : IsIntegral (Algebra.adjoin ℂ
      {Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction}) F) :
    IsIntegral (Algebra.adjoin ℂ
      {Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction}) (modularFunctionCoeffAction N σ F) := by
  let J := Subgroup.compactifiedQuotientComap
    (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction
  let A := Algebra.adjoin ℂ ({J} : Set _)
  let ψ := (modularFunctionCoeffAction N σ).toRingHom
  have hA : ∀ a ∈ A, ψ a ∈ A := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rw [Set.mem_singleton_iff.mp ha]
      have hJ : ψ J = J :=
        modularFunctionCoeffAction_compactifiedQuotientComap_jMeromorphicFunction (N := N) σ
      rw [hJ]
      exact Algebra.subset_adjoin (Set.mem_singleton J)
    | algebraMap c =>
      simpa only [ψ, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        modularFunctionCoeffAction_algebraMap] using
        A.algebraMap_mem (σ c)
    | add a b _ _ ha hb => exact (map_add ψ a b) ▸ A.add_mem ha hb
    | mul a b _ _ ha hb => exact (map_mul ψ a b) ▸ A.mul_mem ha hb
  let φ : A →+* A := (ψ.comp A.val.toRingHom).codRestrict A.toSubring
    (fun a ↦ hA a a.property)
  exact hF.map_of_comp_eq φ ψ (by ext a; rfl)

/-- Applying an arbitrary automorphism of `ℂ` to the Fourier coefficients preserves
holomorphy on the upper half-plane for meromorphic modular functions. -/
@[simp]
theorem forall_ne_infty_modularFunctionCoeffAction_iff (σ : ℂ ≃+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    (∀ τ : ℍ, modularFunctionCoeffAction N σ F (ofQuotient (Quotient.mk _ τ)) ≠ ∞) ↔
      ∀ τ : ℍ, F (ofQuotient (Quotient.mk _ τ)) ≠ ∞ := by
  rw [← (Gamma N).isIntegral_adjoin_jMeromorphicFunction_iff,
    ← (Gamma N).isIntegral_adjoin_jMeromorphicFunction_iff]
  refine ⟨fun h ↦ ?_, isIntegral_adjoin_jMeromorphicFunction_coeffAction σ⟩
  have h := isIntegral_adjoin_jMeromorphicFunction_coeffAction σ.symm h
  rwa [modularFunctionCoeffAction_symm_apply_apply] at h

variable (N) in
/-- The ring `ℂ[j]` of polynomials in the modular invariant `j`, as a `ℂ`-subalgebra of the
meromorphic functions on `X(N)`. -/
abbrev jPolynomialSubalgebra :
    Subalgebra ℂ (MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :=
  Algebra.adjoin ℂ {(Subgroup.compactifiedQuotientComap
    (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction)}

omit [NeZero N] in
/-- **Fractional linear maps preserve holomorphy on `Y(N)`.** For `g ∈ SL(2, ℤ/Nℤ)`, the function
`F ∘ g` has no pole on `Y(N)` exactly when `F` has none. -/
@[simp]
theorem unop_modularFunctionActionZMod_mem_holomorphicSubalgebra_iff (g : SL(2, ZMod N))
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    unop (modularFunctionActionZMod N g) F ∈ holomorphicSubalgebra (Set.range ofQuotient) ↔
      F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
  -- `F ∘ γ` takes at the orbit of `τ` the value of `F` at the orbit of `γ • τ`
  have key (g : SL(2, ZMod N))
      {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
      (hF : F ∈ holomorphicSubalgebra (Set.range ofQuotient)) :
      unop (modularFunctionActionZMod N g) F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
    obtain ⟨γ, rfl⟩ := Matrix.SpecialLinearGroup.map_intCast_zmod_surjective (d := N) g
    rw [modularFunctionActionZMod_map, mem_holomorphicSubalgebra, Set.forall_mem_range]
    intro p
    induction p using Quotient.inductionOn with | h τ =>
    rw [modularFunctionAction_apply_ofQuotient]
    exact mem_holomorphicSubalgebra.mp hF _ ⟨_, rfl⟩
  refine ⟨fun hF ↦ ?_, key g⟩
  simpa only [map_inv, unop_inv, AlgEquiv.coe_inv, AlgEquiv.symm_apply_apply] using key g⁻¹ hF

omit [NeZero N] in
/-- The modular invariant `j`, pulled back to `X(N)`, has no pole on `Y(N)`. -/
theorem compactifiedQuotientComap_jMeromorphicFunction_mem_holomorphicSubalgebra :
    Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
  rw [Subgroup.compactifiedQuotientComap_mem_holomorphicSubalgebra_iff,
    ModularGroup.holomorphicSubalgebra_range_ofQuotient_eq_adjoin]
  exact Algebra.self_mem_adjoin_singleton ℂ _

omit [NeZero N] in
/-- A function on `X(N)` is holomorphic on `Y(N)` exactly when it has no pole at the orbit of any
point of the upper half-plane. -/
private theorem mem_holomorphicSubalgebra_range_ofQuotient_iff
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    F ∈ holomorphicSubalgebra (Set.range ofQuotient) ↔
      ∀ τ : ℍ, F (ofQuotient (Quotient.mk _ τ)) ≠ ∞ := by
  rw [mem_holomorphicSubalgebra, Set.forall_mem_range]
  exact ⟨fun h τ ↦ h _, fun h p ↦ Quotient.inductionOn p h⟩

/-- **The modular functions holomorphic on `Y(N)` are the integral closure of `ℂ[j]`.** A
meromorphic function on `X(N)` is integral over the ring of polynomials in `j` exactly when it
has no pole on `Y(N)`. -/
theorem isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    IsIntegral (jPolynomialSubalgebra N) F ↔
      F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
  rw [mem_holomorphicSubalgebra_range_ofQuotient_iff]
  exact (Gamma N).isIntegral_adjoin_jMeromorphicFunction_iff F

/-- **Conjugating Fourier coefficients preserves holomorphy on `Y(N)`.** For every automorphism
`σ` of `ℂ`, the function `F^σ` whose expansion at `∞` has the `σ`-conjugate coefficients has no
pole on `Y(N)` exactly when `F` has none. -/
@[simp]
theorem modularFunctionCoeffAction_mem_holomorphicSubalgebra_iff (σ : ℂ ≃+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    modularFunctionCoeffAction N σ F ∈ holomorphicSubalgebra (Set.range ofQuotient) ↔
      F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
  rw [mem_holomorphicSubalgebra_range_ofQuotient_iff,
    mem_holomorphicSubalgebra_range_ofQuotient_iff]
  exact forall_ne_infty_modularFunctionCoeffAction_iff σ F

end TauCeti
