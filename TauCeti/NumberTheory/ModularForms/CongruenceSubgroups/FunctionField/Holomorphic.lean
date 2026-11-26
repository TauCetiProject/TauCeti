/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.CoeffAction
import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.Degree

/-!
# Modular functions of level `N` holomorphic on `Y(N)`

Let `ℂ(X(N))` be the field of meromorphic functions on the compactified modular curve `X(N)`,
and `Y(N) = Γ(N) \ ℍ` the open modular curve, the complement of the cusps. The functions without
poles on `Y(N)` form a `ℂ`-subalgebra of `ℂ(X(N))`, written `𝒪(Y(N))` here
(`TauCeti.RiemannSurface.MeromorphicFunction.holomorphicSubalgebra` of the range of
`Subgroup.CompactifiedQuotient.ofQuotient`). For a modular form `f` of weight `k` on `Γ(N)`, the
quotient `f ^ 12 / Δ ^ k` lies in `𝒪(Y(N))`, since the discriminant `Δ` has no zero on `ℍ`.

This file identifies `𝒪(Y(N))` algebraically, as the integral closure of `ℂ[j]` in `ℂ(X(N))`
(`TauCeti.isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra`):

* a function integral over `ℂ[j]` has no pole on `Y(N)`, because `j` has none and the functions
  without a pole at a point form a valuation ring, which is integrally closed;
* conversely, let `F ∈ 𝒪(Y(N))`. The group `SL(2, ℤ/Nℤ)` acts on `ℂ(X(N))` by fractional linear
  maps, through a finite group of automorphisms preserving `𝒪(Y(N))`, whose fixed field is
  `ℂ(j)`. The product of the `X - F ∘ g` over this finite group is monic, vanishes at `F`, and has
  coefficients in `𝒪(Y(N))` fixed by `SL(2, ℤ/Nℤ)`. These coefficients are therefore functions on
  `X(1)` with no pole on `Y(1)`, which are the polynomials in `j`
  (`TauCeti.ModularGroup.holomorphicSubalgebra_range_ofQuotient_eq_adjoin`).

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
* `TauCeti.modularFunctionCoeffAction_mem_holomorphicSubalgebra_iff`: the automorphisms of `ℂ`,
  acting through the Fourier coefficients, preserve `𝒪(Y(N))`.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton
  University Press, 1971, §§2.4, 6.1–6.2.
-/

public noncomputable section

open CongruenceSubgroup MulOpposite Polynomial Subgroup.CompactifiedQuotient
open TauCeti.RiemannSurface TauCeti.RiemannSurface.MeromorphicFunction
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

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

/-- A function on `X(N)` with no pole on `Y(N)` which is fixed by `SL(2, ℤ/Nℤ)` is a polynomial
in `j`. -/
private theorem mem_jPolynomialSubalgebra_of_mem_fixedField
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ holomorphicSubalgebra (Set.range ofQuotient))
    (hfix : F ∈ IntermediateField.fixedField (modularFunctionActionZMod N).range.unop) :
    F ∈ jPolynomialSubalgebra N := by
  rw [fixedField_unop_range_modularFunctionActionZMod, AlgHom.mem_fieldRange] at hfix
  obtain ⟨G, rfl⟩ := hfix
  rw [Subgroup.compactifiedQuotientComap_mem_holomorphicSubalgebra_iff,
    ModularGroup.holomorphicSubalgebra_range_ofQuotient_eq_adjoin] at hF
  rw [jPolynomialSubalgebra, ← AlgHom.map_adjoin_singleton]
  exact Subalgebra.mem_map.mpr ⟨G, hF, rfl⟩

/-- **A function holomorphic on `Y(N)` is integral over `ℂ[j]`**: it is a root of the monic
polynomial `∏ (X - F ∘ g)`, over the image of `SL(2, ℤ/Nℤ)` in the automorphisms of `ℂ(X(N))`,
whose coefficients are polynomials in `j`. -/
private theorem isIntegral_jPolynomialSubalgebra_of_mem_holomorphicSubalgebra
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ holomorphicSubalgebra (Set.range ofQuotient)) :
    IsIntegral (jPolynomialSubalgebra N) F := by
  let H := (modularFunctionActionZMod N).range.unop
  let : Fintype H := Fintype.ofFinite _
  -- the conjugates of `F` have no pole on `Y(N)`
  have hconj (h : H) : h • F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
    obtain ⟨g, hg⟩ := Subgroup.mem_unop.mp h.property
    rw [Subgroup.smul_def, AlgEquiv.smul_def,
      show (h : _ ≃ₐ[ℂ] _) = unop (modularFunctionActionZMod N g) by rw [hg, unop_op]]
    exact (unop_modularFunctionActionZMod_mem_holomorphicSubalgebra_iff g).mpr hF
  -- so neither have the coefficients of `∏ (X - h • F)`
  have hhol (n : ℕ) :
      (MulSemiringAction.charpoly H F).coeff n ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
    have hmap : (∏ h : H, (X - C (⟨h • F, hconj h⟩ :
        holomorphicSubalgebra (Set.range ofQuotient)))).map
          (holomorphicSubalgebra (Set.range ofQuotient)).val.toRingHom =
        MulSemiringAction.charpoly H F := by
      simp [MulSemiringAction.charpoly_eq, Polynomial.map_prod]
    rw [← hmap, coeff_map]
    exact Subtype.property _
  -- the coefficients are fixed by `SL(2, ℤ/Nℤ)`, hence polynomials in `j`
  have hcoeff (n : ℕ) :
      (MulSemiringAction.charpoly H F).coeff n ∈
        Set.range (algebraMap (jPolynomialSubalgebra N) _) := by
    refine ⟨⟨_, mem_jPolynomialSubalgebra_of_mem_fixedField (hhol n) ?_⟩, rfl⟩
    refine (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ ↦ ?_
    simpa only [Subgroup.smul_def, AlgEquiv.smul_def] using
      MulSemiringAction.smul_coeff_charpoly (G := H) F n ⟨σ, hσ⟩
  obtain ⟨q, hq, -, hmonic⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts _).mpr hcoeff) (MulSemiringAction.monic_charpoly H F)
  exact ⟨q, hmonic, by rw [eval₂_eq_eval_map, hq, MulSemiringAction.eval_charpoly]⟩

/-- **The modular functions holomorphic on `Y(N)` are the integral closure of `ℂ[j]`.** A
meromorphic function on `X(N)` is integral over the ring of polynomials in `j` exactly when it
has no pole on `Y(N)`. -/
theorem isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    IsIntegral (jPolynomialSubalgebra N) F ↔
      F ∈ holomorphicSubalgebra (Set.range ofQuotient) :=
  ⟨mem_holomorphicSubalgebra_of_isIntegral (Algebra.adjoin_le (Set.singleton_subset_iff.mpr
    compactifiedQuotientComap_jMeromorphicFunction_mem_holomorphicSubalgebra)),
    isIntegral_jPolynomialSubalgebra_of_mem_holomorphicSubalgebra⟩

/-- An automorphism of `ℂ`, acting through the Fourier coefficients, sends a polynomial in `j` to
the polynomial in `j` with conjugate coefficients; in particular it preserves `ℂ[j]`. -/
private theorem modularFunctionCoeffAction_mem_jPolynomialSubalgebra (σ : ℂ ≃+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : F ∈ jPolynomialSubalgebra N) :
    modularFunctionCoeffAction N σ F ∈ jPolynomialSubalgebra N := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx,
      modularFunctionCoeffAction_compactifiedQuotientComap_jMeromorphicFunction]
    exact Algebra.self_mem_adjoin_singleton ℂ _
  | algebraMap c =>
    rw [modularFunctionCoeffAction_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact mul_mem hx hy

/-- **Conjugating Fourier coefficients preserves holomorphy on `Y(N)`.** For every automorphism
`σ` of `ℂ`, the function `F^σ` whose expansion at `∞` has the `σ`-conjugate coefficients has no
pole on `Y(N)` exactly when `F` has none. -/
@[simp]
theorem modularFunctionCoeffAction_mem_holomorphicSubalgebra_iff (σ : ℂ ≃+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient} :
    modularFunctionCoeffAction N σ F ∈ holomorphicSubalgebra (Set.range ofQuotient) ↔
      F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
  -- `F ↦ F^σ` restricts to a ring endomorphism of `ℂ[j]`, so it preserves integrality over `ℂ[j]`
  have key (σ : ℂ ≃+* ℂ)
      {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
      (hF : F ∈ holomorphicSubalgebra (Set.range ofQuotient)) :
      modularFunctionCoeffAction N σ F ∈ holomorphicSubalgebra (Set.range ofQuotient) := by
    rw [← isIntegral_jPolynomialSubalgebra_iff_mem_holomorphicSubalgebra] at hF ⊢
    let A := jPolynomialSubalgebra N
    let φ : A →+* A := ((modularFunctionCoeffAction N σ).toRingHom.comp A.val.toRingHom).codRestrict
      A fun F ↦ modularFunctionCoeffAction_mem_jPolynomialSubalgebra σ F.property
    exact hF.map_of_comp_eq φ (modularFunctionCoeffAction N σ).toRingHom rfl
  refine ⟨fun hF ↦ ?_, key σ⟩
  simpa only [map_inv, RingAut.inv_apply, RingEquiv.symm_apply_apply] using key σ⁻¹ hF

end TauCeti
