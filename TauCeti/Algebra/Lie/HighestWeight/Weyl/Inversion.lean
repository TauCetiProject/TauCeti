/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Decomposition
public import TauCeti.Algebra.Lie.HighestWeight.Weyl.Character
import Mathlib.LinearAlgebra.RootSystem.BaseExists

/-!
# Weyl-alternating inversion of isotypic multiplicities

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field of characteristic zero, let `H` be a Cartan subalgebra and `b` a base of its root
system. By Weyl's complete reducibility theorem, the formal character of a finite-dimensional
`L`-module `M` is the multiplicity-weighted sum of the irreducible characters
(`TauCeti.formalCharacter_eq_finsum_isotypicMultiplicity_smul`):

`ch M = ∑_λ m_λ · ch L(λ)`.

This file proves that multiplication by the Weyl denominator `Δ = ∏_{α>0}(1 - e^{-α})` inverts that
expansion at the dominant integral weights: for a dominant integral weight `ν`, the coefficient of
`ch L(λ) · Δ` at `ν` is `1` when `λ = ν` and `0` otherwise, so

`[e^ν] (ch M · Δ) = m_ν`,

reading the isotypic multiplicity `m_ν = dim Hom_L(L(ν), M)` off `ch M` by **Weyl-alternating
inversion** (`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`).

Consequently the formal character determines a finite-dimensional module up to equivalence. Two
modules with the same character contain every `L(λ)` equally often, by this inversion, and two
modules containing every `L(λ)` equally often are equivalent, because their packaged isotypic
decompositions `M ≃ ⨁ L(λ)^{m_λ}` are the same direct sum. So `M ≃ N` exactly when
`ch M = ch N` (`TauCeti.nonempty_lieModuleEquiv_iff_formalCharacter_eq`). Equal dimension does
not suffice: for `sl₂`, `V(1) ⊗ V(1)` and `V(1) × V(1)` both have dimension `4`, but only the
first contains the weight `0`.

## Main results

* `TauCeti.coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral`:
  orthogonality of irreducible characters against the Weyl denominator at dominant integral weights.
* `TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`:
  multiplication by the Weyl denominator reads off the isotypic multiplicities.
* `TauCeti.nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq`: two
  finite-dimensional modules are equivalent exactly when every `L(λ)` occurs in them equally often.
* `TauCeti.nonempty_lieModuleEquiv_iff_formalCharacter_eq`: **two finite-dimensional modules are
  equivalent exactly when their formal characters agree.**
* `TauCeti.isotypicMultiplicity_eq_of_formalCharacter_eq`: modules with the same formal character
  have the same multiplicities.

## References

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VIII, §9, Exercise 2 (the Brauer–Klimyk formula
  and its specialization to minuscule weights).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24,
  Exercise 9.
-/

public section

namespace TauCeti

open LieAlgebra _root_.LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

section Inversion

variable (b : (IsKilling.rootSystem H).Base)

attribute [local instance] Classical.propDecidable

/-- **Orthogonality of the irreducible characters against the Weyl denominator at dominant integral
weights**: for dominant integral `lam` and `nu`, the coefficient of `ch L(lam) · Δ` at `nu` is `1`
when `lam = nu` and `0` otherwise. -/
theorem coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral
    (lam : {l : Dual K H // IsDominantIntegral b l}) {nu : Dual K H}
    (hnu : IsDominantIntegral b nu) :
    (irreducibleFormalCharacter b lam * weylDenominator (IsKilling.rootSystem H) b).coeff nu =
      if lam.1 = nu then 1 else 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  have hv := isHighestWeightVector_irreducibleQuotientGenerator b lam.1
  have hgen := lieSpan_irreducibleQuotientGenerator_eq_top b lam.1
  rw [irreducibleFormalCharacter_def]
  split_ifs with h
  · subst h
    exact
      coeff_formalCharacter_mul_weylDenominator_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top
        hv hgen
  · exact coeff_formalCharacter_mul_weylDenominator_eq_zero_of_isDominantIntegral_of_ne
      hv hgen hnu (Ne.symm h)

/-- **Weyl-alternating inversion of isotypic multiplicity**: for any finite-dimensional `L`-module
`M` and any dominant integral weight `nu`, the coefficient of `ch M · Δ` at `nu` is the multiplicity
of `L(nu)` in `M`.

Expanding `ch M = ∑_λ m_λ · ch L(λ)` by
`TauCeti.formalCharacter_eq_finsum_isotypicMultiplicity_smul` and multiplying by `Δ`, every summand
`λ ≠ ν` vanishes at `ν` while the `λ = ν` summand has coefficient `1` there
(`TauCeti.coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral`). -/
theorem coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity [FiniteDimensional K M]
    {nu : Dual K H} (hnu : IsDominantIntegral b nu) :
    (formalCharacter K H M * weylDenominator (IsKilling.rootSystem H) b).coeff nu =
      (LieModule.isotypicMultiplicity K L M (irreducibleQuotient b nu) : ℤ) := by
  classical
  -- Evaluate the additive functional `x ↦ (x * Δ).coeff nu` on the finite character decomposition.
  let φ : AddMonoidAlgebra ℤ (Dual K H) →+ ℤ :=
    { toFun := fun x ↦ (x * weylDenominator (IsKilling.rootSystem H) b).coeff nu
      map_zero' := by simp
      map_add' := fun x y ↦ by simp [add_mul] }
  have hφ : ∀ x, φ x = (x * weylDenominator (IsKilling.rootSystem H) b).coeff nu := fun _ ↦ rfl
  have hsupp : Function.HasFiniteSupport fun lam : {l : Dual K H // IsDominantIntegral b l} ↦
      (LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam.1) : ℤ) •
        irreducibleFormalCharacter b lam := by
    refine (((formalCharacter K H M).coeff.support : Set (Dual K H)).toFinite.preimage
      Subtype.val_injective.injOn).subset fun lam hlam ↦ ?_
    rw [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff, Ne,
      formalCharacter_coeff_eq_zero_iff]
    refine genWeightSpace_ne_bot_of_isotypicMultiplicity_irreducibleQuotient_ne_zero b fun h0 ↦
      hlam ?_
    simp [h0]
  have hφ_smul (c : ℤ) (lam : {l : Dual K H // IsDominantIntegral b l}) :
      φ (c • irreducibleFormalCharacter b lam) = c * (if lam.1 = nu then 1 else 0) := by
    rw [map_zsmul]
    simp [hφ, coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral b lam hnu]
  rw [← hφ, formalCharacter_eq_finsum_isotypicMultiplicity_smul b, φ.map_finsum hsupp,
    finsum_eq_single _ ⟨nu, hnu⟩]
  · rw [hφ_smul]
    simp
  · intro lam hlam
    rw [hφ_smul]
    simp [Subtype.ext_iff.not.mp hlam]

end Inversion

/-! ### The character determines the module -/

section Determination

open DirectSum

universe w₁ w₂

variable {N : Type w₁} [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- **A finite-dimensional module is determined by its multiplicities.** Two finite-dimensional
`L`-modules are equivalent exactly when every `L(λ)`, for `λ` dominant integral, occurs in them
equally often: then their packaged isotypic decompositions
(`TauCeti.nonempty_lieModuleEquiv_directSum_irreducibleQuotient`) are the same direct sum. -/
theorem nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq
    (b : (IsKilling.rootSystem H).Base) [FiniteDimensional K M] [FiniteDimensional K N] :
    Nonempty (M ≃ₗ⁅K,L⁆ N) ↔ ∀ lam : Dual K H, IsDominantIntegral b lam →
      isotypicMultiplicity K L M (irreducibleQuotient b lam) =
        isotypicMultiplicity K L N (irreducibleQuotient b lam) := by
  refine ⟨fun ⟨e⟩ _ _ ↦ isotypicMultiplicity_eq_of_lieModuleEquiv e, fun h ↦ ?_⟩
  obtain ⟨eM⟩ := nonempty_lieModuleEquiv_directSum_irreducibleQuotient (M := M) b
  obtain ⟨eN⟩ := nonempty_lieModuleEquiv_directSum_irreducibleQuotient (M := N) b
  -- The two decompositions are indexed by the same multiplicities, so are one direct sum.
  have key : ∀ m m' : {l : Dual K H // IsDominantIntegral b l} → ℕ, m = m' →
      Nonempty ((⨁ q : Σ lam, Fin (m lam), irreducibleQuotient b q.1.1) ≃ₗ⁅K,L⁆
        ⨁ q : Σ lam, Fin (m' lam), irreducibleQuotient b q.1.1) := by
    rintro m _ rfl
    exact ⟨LieModuleEquiv.refl⟩
  obtain ⟨f⟩ := key _ _ (funext fun lam ↦ h lam.1 lam.2)
  exact ⟨eM.trans (f.trans eN.symm)⟩

variable (H) in
/-- **The formal character determines a finite-dimensional module up to equivalence.** Two
finite-dimensional modules over a Lie algebra with non-degenerate Killing form, over an
algebraically closed field of characteristic zero, are equivalent exactly when their formal
characters with respect to a Cartan subalgebra `H` agree.

Choosing a base `b`, both characters give the multiplicity of each `L(ν)`, `ν` dominant integral,
by Weyl-alternating inversion
(`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`), and equal
multiplicities give an equivalence
(`TauCeti.nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq`). -/
theorem nonempty_lieModuleEquiv_iff_formalCharacter_eq [FiniteDimensional K M]
    [FiniteDimensional K N] :
    Nonempty (M ≃ₗ⁅K,L⁆ N) ↔ formalCharacter K H M = formalCharacter K H N := by
  refine ⟨fun ⟨e⟩ ↦ formalCharacter_congr (e.restrictLie H), fun h ↦ ?_⟩
  obtain ⟨b⟩ := (IsKilling.rootSystem H).nonempty_base
  refine (nonempty_lieModuleEquiv_iff_forall_isotypicMultiplicity_irreducibleQuotient_eq b).mpr
    fun nu hnu ↦ ?_
  have hM := coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity (M := M) b hnu
  rw [h, coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity b hnu] at hM
  exact_mod_cast hM.symm

/-- **The formal character determines every multiplicity.** Two finite-dimensional `L`-modules
with the same formal character have the same multiplicity `dim Hom_L(S, -)` of every `L`-module
`S`, irreducible or not, since they are equivalent
(`TauCeti.nonempty_lieModuleEquiv_iff_formalCharacter_eq`). -/
theorem isotypicMultiplicity_eq_of_formalCharacter_eq [FiniteDimensional K M]
    [FiniteDimensional K N] {S : Type w₂} [AddCommGroup S] [Module K S] [LieRingModule L S]
    (h : formalCharacter K H M = formalCharacter K H N) :
    isotypicMultiplicity K L M S = isotypicMultiplicity K L N S :=
  isotypicMultiplicity_eq_of_lieModuleEquiv
    ((nonempty_lieModuleEquiv_iff_formalCharacter_eq H).mpr h).some

end Determination

end TauCeti
