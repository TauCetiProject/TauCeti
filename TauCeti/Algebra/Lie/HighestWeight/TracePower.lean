/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Linear
public import TauCeti.Algebra.Lie.HighestWeight.FiniteDimensional
public import TauCeti.Algebra.Lie.HighestWeight.OrbitSum
public import TauCeti.Algebra.Lie.Weights.InvariantForm
import TauCeti.Algebra.Lie.HighestWeight.Weight.Density
import TauCeti.RepresentationTheory.SymmetricAlgebra.Reynolds

/-!
# Trace-power polynomials on a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a Cartan subalgebra and `b` a base of its root system.
For a finite-dimensional module `M` and a natural number `m`, the function `x ↦ tr (ρ_M(x) ^ m)` is
an invariant polynomial function on `L`. On `H` it is the power sum of the weights of `M`
(`TauCeti.trace_toEnd_pow_eq_sum_finrank_nsmul`),

`tr (ρ_M(h) ^ m) = ∑_μ dim M_μ · μ(h) ^ m`,

which this file transports along the Killing duality `H ≃ H*` to an element of `S(H)`, the algebra
of polynomial functions on the weights. Writing `t_μ ∈ H` for the vector that represents a weight
`μ` under the Killing form, it is

`TauCeti.tracePowerRestriction K H M m = ∑_μ dim M_μ · t_μ ^ m`,

whose value at a weight `λ` is `∑_μ dim M_μ ⟨λ, μ⟩ ^ m`, with `⟨·,·⟩ = TauCeti.invForm`. The main
theorem is that these elements, for the irreducible modules `L(λ)` of the dominant integral weights
`λ`, span the whole degree-`m` component of the Weyl invariants `S(H)^W`
(`TauCeti.linearInvariants`). This is the Cartan-side input to the surjectivity half of
Chevalley's restriction theorem: it says that every Weyl-invariant polynomial on `H` is a
combination of the restrictions to `H` of the polynomial functions `x ↦ tr (ρ_λ(x) ^ m)` on `L`.

The proof combines three earlier results.

* **Unitriangularity.** The character of `L(λ)` is the Weyl orbit sum of `λ` plus a combination
  of the orbit sums of the dominant weights strictly below `λ`
  (`TauCeti.formalCharacter_irreducibleQuotient_eq_orbitSum_add_lower`). A downward induction on
  the finitely many dominant weights below `λ` therefore writes the power sum of every Weyl orbit
  of a dominant integral weight as a combination of the elements above.
* **Density.** The `m`-th powers of the vectors `t_λ`, for `λ` dominant integral, span the
  degree-`m` component of `S(H)` (`TauCeti.span_pow_cartanEquivDual_symm_eq_homogeneousSubmodule`);
  this is the polarization form of the polynomial density of the dominant integral weights.
* **Averaging.** The Reynolds operator of the Weyl group acting on `H`
  (`Representation.symmetricAlgebraReynolds`) sends `t_λ ^ m` to a multiple of the power sum of
  `∑_w e^{w λ}`, because the form `⟨·,·⟩` is Weyl-invariant. That element is Weyl-invariant and
  supported on the Weyl orbit of `λ`, hence a combination of orbit sums, and the Reynolds operator
  fixes a Weyl invariant (`TauCeti.linearInvariants_eq_symmetricAlgebraInvariants`).

## Main definitions

* `TauCeti.weightPowerSum H m`: the additive map `ℤ[H*] → S(H)` sending `e^μ` to `t_μ ^ m`.
* `TauCeti.tracePowerRestriction K H M m`: the degree-`m` power sum `∑_μ dim M_μ · t_μ ^ m` of the
  weights of `M`.
* `TauCeti.highestWeightTracePowerRestriction hlam m`: the same for `M = L(λ)`, `λ` dominant
  integral.

## Main results

* `TauCeti.lift_weightPowerSum`: the value of `weightPowerSum H m f` at a weight `λ` is
  `∑_μ f(μ) ⟨λ, μ⟩ ^ m`.
* `TauCeti.weightPowerSum_mem_linearInvariants`: a Weyl-invariant element of `ℤ[H*]` is sent to a
  Weyl invariant.
* `TauCeti.lift_cartanEquivDual_tracePowerRestriction`: the value of
  `tracePowerRestriction K H M m` at the weight `κ(h, ·)` is `tr (ρ_M(h) ^ m)`, so it is the
  Killing transport of the restriction of `x ↦ tr (ρ_M(x) ^ m)` to `H`.
* `TauCeti.span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule`:
  **the trace-power polynomials of the modules `L(λ)` span the degree-`m` Weyl invariants.**

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1.
-/

public section

namespace TauCeti

open LieAlgebra LieModule Module RootPairing

universe u v w

variable {K : Type u} {L : Type v} [Field K]
  [LieRing L] [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/-! ### Power sums of weights -/

variable (H) in
/-- **The degree-`m` power sum of a weight function**: the additive map `ℤ[H*] → S(H)` sending
`e^μ` to `t_μ ^ m`, where `t_μ ∈ H` represents the weight `μ` under the Killing form. Read as a
polynomial function on the weights, `weightPowerSum H m f` is `λ ↦ ∑_μ f(μ) ⟨λ, μ⟩ ^ m`
(`TauCeti.lift_weightPowerSum`). -/
noncomputable def weightPowerSum (m : ℕ) :
    AddMonoidAlgebra ℤ (Dual K H) →+ SymmetricAlgebra K H :=
  (Finsupp.linearCombination ℤ fun mu ↦
      SymmetricAlgebra.ι K H ((IsKilling.cartanEquivDual H).symm mu) ^ m).toAddMonoidHom.comp
    (AddMonoidAlgebra.coeffAddEquiv : AddMonoidAlgebra ℤ (Dual K H) ≃+ _).toAddMonoidHom

/-- The power sum `weightPowerSum H m f` is `∑_μ f(μ) • t_μ ^ m`. -/
theorem weightPowerSum_apply (m : ℕ) (f : AddMonoidAlgebra ℤ (Dual K H)) :
    weightPowerSum H m f = f.coeff.sum fun mu c ↦
      c • SymmetricAlgebra.ι K H ((IsKilling.cartanEquivDual H).symm mu) ^ m :=
  Finsupp.linearCombination_apply ℤ _

/-- The power sum of a single weight `e^μ` is `t_μ ^ m`. -/
@[simp]
theorem weightPowerSum_single (m : ℕ) (mu : Dual K H) (c : ℤ) :
    weightPowerSum H m (AddMonoidAlgebra.single mu c) =
      c • SymmetricAlgebra.ι K H ((IsKilling.cartanEquivDual H).symm mu) ^ m := by
  rw [weightPowerSum_apply, AddMonoidAlgebra.coeff_single]
  exact Finsupp.sum_single_index (zero_smul ℤ _)

/-- The vector `t_μ` representing a weight `μ` under the Killing form takes the value `⟨λ, μ⟩` at
a weight `λ`. -/
theorem lift_ι_cartanEquivDual_symm (lam mu : Dual K H) :
    SymmetricAlgebra.lift lam (SymmetricAlgebra.ι K H ((IsKilling.cartanEquivDual H).symm mu)) =
      invForm lam mu := by
  rw [SymmetricAlgebra.lift_ι_apply, invForm_apply_apply]

/-- **The value of a power sum at a weight**: `weightPowerSum H m f` takes the value
`∑_μ f(μ) ⟨λ, μ⟩ ^ m` at the weight `λ`. -/
theorem lift_weightPowerSum (lam : Dual K H) (m : ℕ) (f : AddMonoidAlgebra ℤ (Dual K H)) :
    SymmetricAlgebra.lift lam (weightPowerSum H m f) =
      f.coeff.sum fun mu c ↦ (c : K) * invForm lam mu ^ m := by
  rw [weightPowerSum_apply, map_finsuppSum]
  refine Finsupp.sum_congr fun mu _ ↦ ?_
  rw [map_zsmul, map_pow, lift_ι_cartanEquivDual_symm, zsmul_eq_mul]

/-- A power sum of degree `m` is homogeneous of degree `m`. -/
theorem weightPowerSum_mem_homogeneousSubmodule (m : ℕ) (f : AddMonoidAlgebra ℤ (Dual K H)) :
    weightPowerSum H m f ∈ SymmetricAlgebra.homogeneousSubmodule K H m := by
  rw [weightPowerSum_apply]
  exact Submodule.finsuppSum_mem _ _ _ _ fun mu _ ↦ Submodule.smul_of_tower_mem _ _ <|
    Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ _) m

/-! ### Trace powers of a module -/

section TracePower

variable [CharZero K] (K H) (M : Type w) [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M] [FiniteDimensional K M]

/-- **The trace-power polynomial of a module on the Cartan subalgebra**: the degree-`m` power sum
`∑_μ dim M_μ · t_μ ^ m` of the weights of `M`, counted with multiplicity, as an element of `S(H)`.
When `K` is algebraically closed, its value at the weight `κ(h, ·)` is `tr (ρ_M(h) ^ m)`
(`TauCeti.lift_cartanEquivDual_tracePowerRestriction`), so it is the restriction to `H` of the
invariant polynomial function `x ↦ tr (ρ_M(x) ^ m)` on `L`, transported along the Killing duality
`H ≃ H*`. Without that hypothesis the formal character can miss the part of `M` on which `H` does
not split, and the identification may fail. -/
noncomputable def tracePowerRestriction (m : ℕ) : SymmetricAlgebra K H :=
  weightPowerSum H m (formalCharacter K H M)

variable {K H M}

/-- The trace-power polynomial of `M` is the power sum of its formal character. -/
theorem tracePowerRestriction_def (m : ℕ) :
    tracePowerRestriction K H M m = weightPowerSum H m (formalCharacter K H M) :=
  (rfl)

/-- A trace-power polynomial of degree `m` is homogeneous of degree `m`. -/
theorem tracePowerRestriction_mem_homogeneousSubmodule (m : ℕ) :
    tracePowerRestriction K H M m ∈ SymmetricAlgebra.homogeneousSubmodule K H m :=
  weightPowerSum_mem_homogeneousSubmodule m _

variable [IsAlgClosed K]

/-- **The trace-power polynomial restricts the trace powers.** The value of
`tracePowerRestriction K H M m` at the weight `κ(h, ·)` represented by `h ∈ H` is
`tr (ρ_M(h) ^ m)`. -/
theorem lift_cartanEquivDual_tracePowerRestriction (h : H) (m : ℕ) :
    SymmetricAlgebra.lift (IsKilling.cartanEquivDual H h) (tracePowerRestriction K H M m) =
      LinearMap.trace K M (toEnd K H M h ^ m) := by
  rw [trace_toEnd_pow_eq_sum_finrank_nsmul, tracePowerRestriction_def,
    formalCharacter_eq_sum_single, map_sum, map_sum]
  refine Finset.sum_congr rfl fun chi _ ↦ ?_
  rw [weightPowerSum_single, map_zsmul, map_pow, lift_ι_cartanEquivDual_symm,
    invForm_cartanEquivDual_left]
  simp

end TracePower

/-! ### Weyl invariance -/

section Weyl

variable [CharZero K] [IsTriangularizable K H L]

/-- **The power sum of a Weyl-invariant weight function is a Weyl invariant.** -/
theorem weightPowerSum_mem_linearInvariants (m : ℕ) {f : AddMonoidAlgebra ℤ (Dual K H)}
    (hf : IsWeylInvariant (IsKilling.rootSystem H) f) :
    weightPowerSum H m f ∈ linearInvariants H := by
  rw [mem_linearInvariants_iff]
  intro w lam
  rw [lift_weightPowerSum, lift_weightPowerSum, Finsupp.sum, Finsupp.sum]
  -- `⟨w λ, μ⟩ = ⟨λ, w⁻¹ μ⟩` by invariance of the form; reindex the sum by `w⁻¹`
  refine Finset.sum_nbij' (w⁻¹ • ·) (w • ·) (fun mu hmu ↦ ?_) (fun mu hmu ↦ ?_)
    (fun mu _ ↦ smul_inv_smul w mu) (fun mu _ ↦ inv_smul_smul w mu) (fun mu _ ↦ ?_)
  · rwa [Finsupp.mem_support_iff, hf.coeff_smul, ← Finsupp.mem_support_iff]
  · rwa [Finsupp.mem_support_iff, hf.coeff_smul, ← Finsupp.mem_support_iff]
  · rw [hf.coeff_smul, invForm_weylGroup_smul_left]

variable [IsAlgClosed K] {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M]
  [LieModule K L M] [FiniteDimensional K M]

/-- **A trace-power polynomial is a Weyl invariant**, because the formal character is. -/
theorem tracePowerRestriction_mem_linearInvariants (m : ℕ) :
    tracePowerRestriction K H M m ∈ linearInvariants H :=
  weightPowerSum_mem_linearInvariants m isWeylInvariant_formalCharacter

end Weyl

/-! ### The trace-power polynomials of the irreducible modules span the Weyl invariants -/

section Span

variable [CharZero K] [IsTriangularizable K H L] {b : (IsKilling.rootSystem H).Base}

variable [IsAlgClosed K]

/-- **The trace-power polynomial of `L(λ)`** for a dominant integral weight `λ`, the module
`L(λ)` being finite-dimensional exactly then
(`TauCeti.finiteDimensional_irreducibleQuotient_of_isDominantIntegral`). -/
noncomputable def highestWeightTracePowerRestriction {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) (m : ℕ) : SymmetricAlgebra K H :=
  have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  tracePowerRestriction K H (irreducibleQuotient b lam) m

/-- The trace-power polynomial of `L(λ)`, for any choice of the finite-dimensionality instance. -/
theorem highestWeightTracePowerRestriction_def {lam : Dual K H} (hlam : IsDominantIntegral b lam)
    [FiniteDimensional K (irreducibleQuotient b lam)] (m : ℕ) :
    highestWeightTracePowerRestriction hlam m =
      tracePowerRestriction K H (irreducibleQuotient b lam) m :=
  (rfl)

/-- **The orbit power sums lie in the span of the trace-power polynomials.** For a dominant
integral weight `λ`, the power sum of the Weyl orbit sum `m_λ` is a combination of the
trace-power polynomials of the modules `L(μ)`, `μ` dominant integral. -/
theorem weightPowerSum_weightOrbitSum_mem_span [Finite (IsKilling.rootSystem H).weylGroup]
    (m : ℕ) {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) :
    weightPowerSum H m ((IsKilling.rootSystem H).weightOrbitSum lam) ∈
      Submodule.span K {p | ∃ (mu : Dual K H) (hmu : IsDominantIntegral b mu),
        highestWeightTracePowerRestriction hmu m = p} := by
  classical
  set V := Submodule.span K {p | ∃ (mu : Dual K H) (hmu : IsDominantIntegral b mu),
    highestWeightTracePowerRestriction hmu m = p}
  -- strong induction on the number of dominant weights below `lam`, using that the characters are
  -- unitriangular against the orbit sums
  induction hn : ((IsKilling.rootSystem H).dominantWeightsBelow b lam).card using
    Nat.strong_induction_on generalizing lam with
  | _ n ih =>
    have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    -- `m_lam` is the character of `L(lam)` minus the orbit sums of lower dominant weights
    have hsub : weightPowerSum H m ((IsKilling.rootSystem H).weightOrbitSum lam) =
        highestWeightTracePowerRestriction hlam m -
          ∑ mu ∈ ((IsKilling.rootSystem H).dominantWeightsBelow b lam).erase lam,
            (formalCharacter K H (irreducibleQuotient b lam)).coeff mu •
              weightPowerSum H m ((IsKilling.rootSystem H).weightOrbitSum mu) := by
      rw [eq_sub_iff_add_eq, highestWeightTracePowerRestriction_def, tracePowerRestriction_def]
      conv_rhs => rw [formalCharacter_irreducibleQuotient_eq_orbitSum_add_lower]
      rw [map_add, map_sum]
      simp only [map_zsmul]
    rw [hsub]
    refine V.sub_mem (Submodule.subset_span ⟨lam, hlam, rfl⟩) (V.sum_mem fun mu hmu ↦ ?_)
    obtain ⟨hne, hmu⟩ := Finset.mem_erase.mp hmu
    have hmu_dom := (mem_dominantWeightsBelow_iff_isDominantIntegral.mp hmu).2
    refine Submodule.smul_of_tower_mem _ _ (ih _ ?_ hmu_dom rfl)
    rw [← hn]
    exact Finset.card_lt_card <| dominantWeightsBelow_ssubset_of_mem_of_ne
      (isDominantIntegral_iff.mp hlam) hmu hne

/-- **The Weyl-averaged power of a dominant weight lies in the span of the trace-power
polynomials.** For a dominant integral weight `λ`, the power sum of `∑_w e^{w λ}`, in which each
Weyl translate of `λ` occurs once for every Weyl group element, is a combination of the
trace-power polynomials of the modules `L(μ)`, `μ` dominant integral. -/
theorem weightPowerSum_sum_single_smul_mem_span [Fintype (IsKilling.rootSystem H).weylGroup]
    (m : ℕ) {lam : Dual K H} (hlam : IsDominantIntegral b lam) :
    weightPowerSum H m (∑ w : (IsKilling.rootSystem H).weylGroup,
        AddMonoidAlgebra.single (w • lam) 1) ∈
      Submodule.span K {p | ∃ (mu : Dual K H) (hmu : IsDominantIntegral b mu),
        highestWeightTracePowerRestriction hmu m = p} := by
  classical
  have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
  -- the support of `∑_w e^{w lam}` is the Weyl orbit of `lam`, where the character of `L(lam)` is 1
  have hch (y : Dual K H) (hy : (∑ w : (IsKilling.rootSystem H).weylGroup,
      AddMonoidAlgebra.single (w • lam) (1 : ℤ)).coeff y ≠ 0) :
      (formalCharacter K H (irreducibleQuotient b lam)).coeff y ≠ 0 := by
    obtain ⟨w, rfl⟩ : ∃ w : (IsKilling.rootSystem H).weylGroup, w • lam = y := by
      by_contra hcon
      refine hy ?_
      simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', AddMonoidAlgebra.coeff_single]
      exact Finset.sum_eq_zero fun w _ ↦ by
        simpa [Finsupp.single_apply] using fun h ↦ hcon ⟨w, h⟩
    rw [formalCharacter_coeff_weylGroup_smul,
      formalCharacter_coeff_eq_one_of_isHighestWeightVector_of_lieSpan_eq_top
        (isHighestWeightVector_irreducibleQuotientGenerator b lam)
        (lieSpan_irreducibleQuotientGenerator_eq_top b lam)]
    exact one_ne_zero
  -- an invariant element supported on weights of `L(lam)` is a combination of lower orbit sums
  have hexp := (isWeylInvariant_sum_single_smul lam).eq_sum_coeff_smul_weightOrbitSum (b := b)
    (fun y hy ↦ sub_mem_posRootCone_of_formalCharacter_coeff_ne_zero
      (isHighestWeightVector_irreducibleQuotientGenerator b lam)
      (lieSpan_irreducibleQuotientGenerator_eq_top b lam) (hch y hy))
    (fun y hy i _ ↦ by
      obtain ⟨z, hz⟩ := (isIntegralWeight_of_formalCharacter_coeff_ne_zero
        (hch y hy)).exists_int_apply_coroot (i : Weight K H L)
      exact ⟨z, by rw [rootSystem_coroot'_apply, IsKilling.rootSystem_coroot_apply, hz]⟩)
  rw [hexp, map_sum]
  refine Submodule.sum_mem _ fun mu hmu ↦ ?_
  rw [map_zsmul]
  exact Submodule.smul_of_tower_mem _ _ <| weightPowerSum_weightOrbitSum_mem_span m
    (mem_dominantWeightsBelow_iff_isDominantIntegral.mp hmu).2

/-- **The trace-power polynomials of the irreducible modules span the Weyl invariants.** For
every `m`, the trace-power polynomials `tracePowerRestriction K H L(λ) m` of the modules `L(λ)`,
`λ` dominant integral, span the degree-`m` component of the Weyl invariants `S(H)^W`. -/
theorem span_highestWeightTracePowerRestriction_eq_linearInvariants_inf_homogeneousSubmodule
    (b : (IsKilling.rootSystem H).Base) (m : ℕ) :
    Submodule.span K {p | ∃ (lam : Dual K H) (hlam : IsDominantIntegral b lam),
        highestWeightTracePowerRestriction hlam m = p} =
      Subalgebra.toSubmodule (linearInvariants H) ⊓
        SymmetricAlgebra.homogeneousSubmodule K H m := by
  classical
  have := RootPairing.finite_weylGroup (IsKilling.rootSystem H)
  let _ := Fintype.ofFinite (IsKilling.rootSystem H).weylGroup
  set V := Submodule.span K {p | ∃ (lam : Dual K H) (hlam : IsDominantIntegral b lam),
    highestWeightTracePowerRestriction hlam m = p}
  refine le_antisymm (Submodule.span_le.mpr ?_) fun p ⟨hinv, hhom⟩ ↦ ?_
  · rintro _ ⟨lam, hlam, rfl⟩
    have := finiteDimensional_irreducibleQuotient_of_isDominantIntegral hlam
    exact ⟨tracePowerRestriction_mem_linearInvariants m,
      tracePowerRestriction_mem_homogeneousSubmodule m⟩
  -- average over the Weyl group acting on `H`, the coroot space
  let ρW := (IsKilling.rootSystem H).weylGroupCorootRep
  let _ : Fintype (IsKilling.rootSystem H).weylGroup.op := Fintype.ofEquiv _ (Subgroup.equivOp _)
  have : Invertible (Fintype.card (IsKilling.rootSystem H).weylGroup.op : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  -- the Reynolds operator sends each `t_λ ^ m` into `V`
  have havg : SymmetricAlgebra.homogeneousSubmodule K H m ≤
      V.comap ρW.symmetricAlgebra.averageMap := by
    rw [← span_pow_cartanEquivDual_symm_eq_homogeneousSubmodule b m, Submodule.span_le]
    rintro _ ⟨lam, hlam, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← Representation.coe_symmetricAlgebraReynolds,
      Representation.coe_symmetricAlgebraReynolds_eq_sum]
    convert V.smul_mem ⅟(Fintype.card (IsKilling.rootSystem H).weylGroup.op : K)
      (weightPowerSum_sum_single_smul_mem_span m hlam) using 2
    rw [map_sum, ← (Subgroup.equivOp _).sum_comp, ← Equiv.sum_comp (Equiv.inv _)]
    refine Fintype.sum_congr _ _ fun w ↦ ?_
    rw [Representation.symmetricAlgebra_apply, map_pow, SymmetricAlgebra.map_apply_ι,
      weylGroupCorootRep_cartanEquivDual_symm, weightPowerSum_single, one_smul, Equiv.inv_apply,
      inv_inv]
  -- the Reynolds operator fixes the invariant `p`
  rw [linearInvariants_eq_symmetricAlgebraInvariants] at hinv
  have hfix := congrArg Subtype.val (ρW.symmetricAlgebraReynolds_coe ⟨p, hinv⟩)
  rw [Representation.coe_symmetricAlgebraReynolds] at hfix
  have hp := havg hhom
  rwa [Submodule.mem_comap, hfix] at hp

end Span

end TauCeti
