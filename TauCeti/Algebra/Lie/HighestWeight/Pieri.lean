/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.Minuscule
public import TauCeti.Algebra.Lie.HighestWeight.Tensor
public import TauCeti.Algebra.Lie.HighestWeight.Weyl.Character

/-!
# Weyl-alternating inversion, the Racah–Speiser formula, and the minuscule Pieri rule

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

## The Racah–Speiser / Brauer–Klimyk formula

Specializing `M` to the tensor product `L(λ) ⊗ L(μ)` of two finite-dimensional irreducibles turns
Weyl-alternating inversion into a closed form for the tensor multiplicity
`c^ν_{λμ} = TauCeti.tensorMultiplicity b λ μ ν`. Formal characters are multiplicative on tensor
products (`TauCeti.formalCharacter_tensor`), and the Weyl character formula rewrites the first
factor as `ch L(λ) · Δ = N(λ)` (`TauCeti.formalCharacter_mul_weylDenominator_eq_weylNumerator`), so

`c^ν_{λμ} = [e^ν] (ch L(μ) · N(λ)) = ∑_{w ∈ W} sgn(w) · [e^{ν - w ⬝ λ}] ch L(μ)`

(`TauCeti.tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator` and
`TauCeti.tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff`). This is the
**Racah–Speiser** (or **Brauer–Klimyk**) formula: to compute the multiplicity of `L(ν)` in
`L(λ) ⊗ L(μ)`, shift the weights of `L(μ)` by `λ`, fold those that land outside the dominant
chamber back into it by the dot action of the Weyl group with signs `sgn(w)`, and read off the
resulting coefficient at `ν`.

## The minuscule Pieri rule

When `μ` is **minuscule** (`TauCeti.IsMinuscule b μ`), no folding occurs: every `w ≠ 1` term in the
Racah–Speiser sum vanishes
(`TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`).
Indeed, if `τ = ν - w ⬝ λ` is a weight of `L(μ)`, then `τ` pairs with every simple coroot `αᵢ^∨`
to an integer `z ≤ 1` (`TauCeti.IsMinuscule.le_one_of_apply_coroot_eq_intCast`). Because `ν` is
dominant integral, `ν + ρ` pairs with `αᵢ^∨` in `1 + ℕ`, so the difference
`w(λ + ρ) = w ⬝ λ + ρ = (ν + ρ) - τ` still takes a natural value on every simple coroot. Since
`λ + ρ` is strictly dominant integral,
`TauCeti.eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one`
forces `w = 1`.

Only the `w = 1` term therefore survives, and since every weight of a minuscule module has
multiplicity one (`TauCeti.formalCharacter_coeff_irreducibleQuotient_eq_ite_of_isMinuscule`), the
tensor multiplicity is `1` when `ν - λ` is a weight of `L(μ)` and `0` otherwise
(`TauCeti.minuscule_pieri`). Dominance of `ν` is essential: for `sl₂` with `λ = 0` and `μ = ω` the
fundamental weight, `ν = -ω` satisfies `-ω - 0 = -ω` being a weight of `L(ω)`, whereas
`L(0) ⊗ L(ω) ≅ L(ω)` contains no copy of `L(-ω)`.

## Main results

* `TauCeti.irreducibleFormalCharacter_mul_weylDenominator_eq_weylNumerator`: the Weyl character
  formula `ch L(λ) · Δ = N(λ)` stated for `TauCeti.irreducibleFormalCharacter`.
* `TauCeti.genWeightSpace_ne_bot_of_isotypicMultiplicity_irreducibleQuotient_ne_zero`: any
  irreducible `L(λ)` occurring with nonzero multiplicity in `M` has `λ` as a weight of `M`.
* `TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`: **Weyl-alternating
  inversion of isotypic multiplicity**, `[e^ν] (ch M · Δ) = m_ν` for dominant integral `ν`.
* `TauCeti.tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator` and
  `TauCeti.tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff`: **the Racah–Speiser /
  Brauer–Klimyk formula** for tensor multiplicities.
* `TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`:
  for dominant integral `λ`, `ν` and minuscule `μ`, `ν - w ⬝ λ` is not a weight of `L(μ)` when
  `w ≠ 1`, so every `w ≠ 1` term of the Racah–Speiser sum vanishes.
* `TauCeti.tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule`: for dominant integral
  `λ`, `ν` and minuscule `μ`, the tensor multiplicity `c^ν_{λμ}` is the weight multiplicity of
  `ν - λ` in `L(μ)`.
* `TauCeti.minuscule_pieri`: **the minuscule Pieri rule**, together with
  `TauCeti.tensorMultiplicity_le_one_of_isMinuscule`,
  `TauCeti.tensorMultiplicity_eq_one_iff_of_isMinuscule`, and
  `TauCeti.tensorMultiplicity_eq_zero_iff_of_isMinuscule`.

## References

This supplies the Weyl-alternating inversion of `isotypicMultiplicity`, the Racah–Speiser formula
for `tensorMultiplicity`, and the `minuscule_pieri` target of Layer 6 ("The decomposition toolkit")
of `TauCetiRoadmap/RepresentationTheory/LieHighestWeight/README.md`.

* N. Bourbaki, *Groupes et algèbres de Lie*, Ch. VIII, §9, Exercise 2 (the Brauer–Klimyk formula
  and its specialization to minuscule weights).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. VI, §24,
  Exercise 9.
-/

public section

open scoped TensorProduct

namespace TauCeti

open LieAlgebra _root_.LieModule Module

universe u v w

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-! ### Weyl-alternating inversion of isotypic multiplicities -/

section Inversion

variable (b : (IsKilling.rootSystem H).Base)

/-- **The Weyl character formula for `TauCeti.irreducibleFormalCharacter`**: at a dominant integral
weight `lam`, the formal character of `L(lam)` times the Weyl denominator is the Weyl numerator
`N(lam)`. -/
@[simp]
theorem irreducibleFormalCharacter_mul_weylDenominator_eq_weylNumerator
    [Fintype (IsKilling.rootSystem H).weylGroup]
    (lam : {l : Dual K H // IsDominantIntegral b l}) :
    irreducibleFormalCharacter b lam * weylDenominator (IsKilling.rootSystem H) b =
      weylNumerator (IsKilling.rootSystem H) b lam.1 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral lam.2
  rw [irreducibleFormalCharacter_def]
  exact formalCharacter_mul_weylDenominator_eq_weylNumerator
    (isHighestWeightVector_irreducibleQuotientGenerator b lam.1)
    (lieSpan_irreducibleQuotientGenerator_eq_top b lam.1)

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

/-- **Any irreducible `L(lam)` occurring with nonzero multiplicity in `M` has `lam` as a weight of
`M`.** A nonzero morphism `L(lam) →ₗ⁅K,L⁆ M` cannot kill the canonical generator (which spans
`L(lam)` over `L`), so it sends that generator to a highest weight vector of weight `lam` in `M`
(`TauCeti.IsHighestWeightVector.map`). -/
theorem genWeightSpace_ne_bot_of_isotypicMultiplicity_irreducibleQuotient_ne_zero
    {lam : Dual K H}
    (h : LieModule.isotypicMultiplicity K L M (irreducibleQuotient b lam) ≠ 0) :
    genWeightSpace M (lam : H → K) ≠ ⊥ := by
  have hsub : ¬ Subsingleton (irreducibleQuotient b lam →ₗ⁅K,L⁆ M) := fun hsub ↦
    h (by rw [LieModule.isotypicMultiplicity_def]; exact finrank_zero_of_subsingleton)
  obtain ⟨f, hf⟩ : ∃ f : irreducibleQuotient b lam →ₗ⁅K,L⁆ M, f ≠ 0 := by
    rw [not_subsingleton_iff_nontrivial] at hsub
    exact exists_ne 0
  have hfv : f (irreducibleQuotientGenerator b lam) ≠ 0 := fun h0 ↦ by
    have htop : f.ker = ⊤ := top_unique <| by
      rw [← lieSpan_irreducibleQuotientGenerator_eq_top b lam, LieSubmodule.lieSpan_le]
      exact Set.singleton_subset_iff.mpr h0
    exact hf (LieModuleHom.ext fun x ↦ (htop ▸ LieSubmodule.mem_top x : x ∈ f.ker))
  exact ((isHighestWeightVector_irreducibleQuotientGenerator b lam).map f hfv).genWeightSpace_ne_bot

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
  rw [← hφ, formalCharacter_eq_finsum_isotypicMultiplicity_smul b, φ.map_finsum hsupp,
    finsum_eq_single _ ⟨nu, hnu⟩]
  · rw [hφ, smul_mul_assoc, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral b ⟨nu, hnu⟩ hnu,
      ite_eq_left rfl, mul_one]
  · intro lam hlam
    rw [hφ, smul_mul_assoc, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
      coeff_irreducibleFormalCharacter_mul_weylDenominator_of_isDominantIntegral b lam hnu,
      ite_eq_right (Subtype.ext_iff.not.mp hlam), mul_zero]

end Inversion

/-! ### The Racah–Speiser / Brauer–Klimyk formula -/

section RacahSpeiser

variable (b : (IsKilling.rootSystem H).Base)

/-- **The Racah–Speiser (or Brauer–Klimyk) formula, in group-algebra form**: for dominant integral
weights `lam`, `mu`, and `nu`, the tensor multiplicity `c^nu_{lam mu}` of `L(nu)` in
`L(lam) ⊗ L(mu)` is the coefficient at `nu` of `ch L(mu) · N(lam)`.

This combines Weyl-alternating inversion
(`TauCeti.coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity`) on `L(lam) ⊗ L(mu)`,
multiplicativity of formal characters (`TauCeti.formalCharacter_tensor`), and the Weyl character
formula `ch L(lam) · Δ = N(lam)`. -/
theorem tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsDominantIntegral b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
    (tensorMultiplicity b lam mu nu : ℤ) =
      (formalCharacter K H (irreducibleQuotient b mu) *
        weylNumerator (IsKilling.rootSystem H) b lam).coeff nu := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  have hchar : formalCharacter K H (irreducibleQuotient b lam ⊗[K] irreducibleQuotient b mu) =
      formalCharacter K H (irreducibleQuotient b lam) *
        formalCharacter K H (irreducibleQuotient b mu) :=
    formalCharacter_tensor
  rw [tensorMultiplicity_def,
    ← coeff_formalCharacter_mul_weylDenominator_eq_isotypicMultiplicity b hnu,
    hchar, mul_comm (formalCharacter K H (irreducibleQuotient b lam)),
    mul_assoc,
    formalCharacter_mul_weylDenominator_eq_weylNumerator
      (isHighestWeightVector_irreducibleQuotientGenerator b lam)
      (lieSpan_irreducibleQuotientGenerator_eq_top b lam)]

/-- **The Racah–Speiser (or Brauer–Klimyk) formula, expanded over the Weyl group**: for dominant
integral weights `lam`, `mu`, and `nu`,
`c^nu_{lam mu} = ∑_{w ∈ W} sgn(w) · [e^{nu - w ⬝ lam}] ch L(mu)`. -/
theorem tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff
    [Fintype (IsKilling.rootSystem H).weylGroup]
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsDominantIntegral b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
    (tensorMultiplicity b lam mu nu : ℤ) =
      ∑ w : (IsKilling.rootSystem H).weylGroup,
        (weylSign (IsKilling.rootSystem H) b w : ℤ) *
          (formalCharacter K H (irreducibleQuotient b mu)).coeff
            (nu - dotAction (IsKilling.rootSystem H) b w lam) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu
  rw [tensorMultiplicity_eq_coeff_formalCharacter_mul_weylNumerator b hlam hmu hnu,
    weylNumerator_def, Finset.mul_sum, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [AddMonoidAlgebra.coeff_mul_single_apply, ← sub_eq_add_neg, mul_comm]

end RacahSpeiser

/-! ### The minuscule Pieri rule -/

section MinusculePieri

variable (b : (IsKilling.rootSystem H).Base)

/-- **No nontrivial Weyl-group element contributes to the Racah–Speiser sum when `mu` is
minuscule**: for dominant integral `lam` and `nu`, a minuscule weight `mu`, and `w ≠ 1`, the weight
`nu - w ⬝ lam` is not a weight of `L(mu)`.

If `τ = nu - w ⬝ lam` were a weight of `L(mu)`, it would pair with every simple coroot `αᵢ^∨` to an
integer `z ≤ 1` (`TauCeti.IsMinuscule.le_one_of_apply_coroot_eq_intCast`). Since `nu` is dominant
integral, `nu + ρ` pairs with `αᵢ^∨` to `n + 1` with `n : ℕ`, so
`w • (lam + ρ) = w ⬝ lam + ρ = (nu + ρ) - τ` takes the natural value `n + 1 - z ≥ 0` on every
simple coroot. Because `lam + ρ` is strictly dominant integral,
`TauCeti.eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one` then forces
`w = 1`. -/
theorem genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu)
    (hnu : IsDominantIntegral b nu) {w : (IsKilling.rootSystem H).weylGroup} (hw : w ≠ 1) :
    genWeightSpace (irreducibleQuotient b mu)
      ((nu - dotAction (IsKilling.rootSystem H) b w lam : Dual K H) : H → K) = ⊥ := by
  by_contra htau
  set ρ := weylVector (IsKilling.rootSystem H) b
  -- `lam + ρ` is strictly dominant integral
  have hlamρ : ∀ i ∈ b.support, ∃ n : ℕ,
      (IsKilling.rootSystem H).coroot' i (lam + ρ) = (n : K) + 1 := by
    intro i hi
    obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hlam i hi
    exact ⟨n, by rw [coroot'_add_weylVector (IsKilling.rootSystem H) b hi,
      rootSystem_coroot'_apply, hn]⟩
  -- `w • (lam + ρ) = (nu + ρ) - (nu - w ⬝ lam)` is dominant integral
  have hwlamρ : ∀ i ∈ b.support, ∃ n : ℕ,
      (IsKilling.rootSystem H).coroot' i (w • (lam + ρ)) = (n : K) := by
    intro i hi
    obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hnu i hi
    obtain ⟨z, ⟨-, hzle⟩, hz⟩ := hmu.exists_int_abs_le_one_apply_coroot htau i
    have hrel : w • (lam + ρ) =
        (nu + ρ) - (nu - dotAction (IsKilling.rootSystem H) b w lam) := by
      rw [← dotAction_add_weylVector]
      abel
    have hval : (IsKilling.rootSystem H).coroot' i (w • (lam + ρ)) =
        (((n : ℤ) + 1 - z : ℤ) : K) := by
      rw [hrel, map_sub, coroot'_add_weylVector (IsKilling.rootSystem H) b hi,
        rootSystem_coroot'_apply, rootSystem_coroot'_apply, hn, hz]
      push_cast
      ring
    refine ⟨((n : ℤ) + 1 - z).toNat, ?_⟩
    rw [hval, ← Int.cast_natCast (R := K), Int.toNat_of_nonneg (by omega)]
  exact hw (eq_one_of_forall_coroot'_smul_eq_natCast_of_forall_coroot'_eq_natCast_add_one
    hlamρ hwlamρ)

/-- **For a minuscule weight `mu`, the tensor multiplicity `c^nu_{lam mu}` at dominant integral
`lam` and `nu` is the weight multiplicity of `nu - lam` in `L(mu)`.** All `w ≠ 1` terms in the
Racah–Speiser formula vanish by
`TauCeti.genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one`,
leaving only the `w = 1` term. -/
theorem tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule
    {lam mu nu : Dual K H} (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu)
    (hnu : IsDominantIntegral b nu) :
    letI := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
    (tensorMultiplicity b lam mu nu : ℤ) =
      (formalCharacter K H (irreducibleQuotient b mu)).coeff (nu - lam) := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
  have _ : Finite (IsKilling.rootSystem H).weylGroup :=
    RootPairing.finite_weylGroup (IsKilling.rootSystem H)
  let _ : Fintype (IsKilling.rootSystem H).weylGroup :=
    Fintype.ofFinite (IsKilling.rootSystem H).weylGroup
  rw [tensorMultiplicity_eq_sum_weylSign_mul_formalCharacter_coeff
    b hlam hmu.isDominantIntegral hnu, Finset.sum_eq_single 1]
  · simp
  · intro w _ hw
    rw [formalCharacter_coeff_eq_zero_iff.mpr
      (genWeightSpace_irreducibleQuotient_sub_dotAction_eq_bot_of_isMinuscule_of_ne_one
        b hlam hmu hnu hw), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ 1) h

attribute [local instance] Classical.propDecidable

/-- **The minuscule Pieri rule**: for dominant integral `lam`, minuscule `mu`, and dominant integral
`nu`, the tensor multiplicity of `L(nu)` in `L(lam) ⊗ L(mu)` is `1` when `nu - lam` is a weight of
`L(mu)` and `0` otherwise.

In particular `L(lam) ⊗ L(mu)` is multiplicity-free, decomposing into the direct sum of those
`L(lam + τ)` for which `τ` is a weight of `L(mu)` and `lam + τ` is dominant integral. -/
theorem minuscule_pieri {lam mu : Dual K H} (hlam : IsDominantIntegral b lam)
    (hmu : IsMinuscule b mu) (nu : Dual K H) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu =
      if genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) ≠ ⊥ then 1 else 0 := by
  have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
  have h := tensorMultiplicity_eq_formalCharacter_coeff_sub_of_isMinuscule b hlam hmu hnu
  rw [formalCharacter_coeff_irreducibleQuotient_eq_ite_of_isMinuscule hmu (nu - lam),
    ← genWeightSpace_ne_bot_iff_mem_orbit_of_isHighestWeightVector_of_lieSpan_eq_top
      (isHighestWeightVector_irreducibleQuotientGenerator b mu)
      (lieSpan_irreducibleQuotientGenerator_eq_top b mu)
      (fun _ ↦ hmu.exists_weylGroup_smul_eq) (nu - lam)] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- **A tensor product with a minuscule module is multiplicity-free**: for dominant integral `lam`
and minuscule `mu`, every irreducible `L(nu)` occurs with multiplicity at most `1` in
`L(lam) ⊗ L(mu)`. -/
theorem tensorMultiplicity_le_one_of_isMinuscule {lam mu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (nu : Dual K H) :
    tensorMultiplicity b lam mu nu ≤ 1 := by
  by_cases hnu : IsDominantIntegral b nu
  · rw [minuscule_pieri b hlam hmu nu hnu]
    split_ifs <;> omega
  · have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    have _ := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hmu.isDominantIntegral
    rw [tensorMultiplicity_def,
      isotypicMultiplicity_irreducibleQuotient_eq_zero_of_not_isDominantIntegral hnu]
    omega

/-- For dominant integral `lam` and `nu` and minuscule `mu`, `L(nu)` occurs in `L(lam) ⊗ L(mu)`
with multiplicity `1` exactly when `nu - lam` is a weight of `L(mu)`. -/
theorem tensorMultiplicity_eq_one_iff_of_isMinuscule {lam mu nu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu = 1 ↔
      genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) ≠ ⊥ := by
  rw [minuscule_pieri b hlam hmu nu hnu]
  split_ifs with h <;> simp [h]

/-- For dominant integral `lam` and `nu` and minuscule `mu`, `L(nu)` does not occur in
`L(lam) ⊗ L(mu)` exactly when `nu - lam` is not a weight of `L(mu)`. -/
theorem tensorMultiplicity_eq_zero_iff_of_isMinuscule {lam mu nu : Dual K H}
    (hlam : IsDominantIntegral b lam) (hmu : IsMinuscule b mu) (hnu : IsDominantIntegral b nu) :
    tensorMultiplicity b lam mu nu = 0 ↔
      genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) = ⊥ := by
  rw [minuscule_pieri b hlam hmu nu hnu]
  by_cases h : genWeightSpace (irreducibleQuotient b mu) ⇑(nu - lam) = ⊥ <;> simp [h]

end MinusculePieri

end TauCeti
