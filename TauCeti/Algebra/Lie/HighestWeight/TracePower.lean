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
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.HighestWeight.Weight.Density
import TauCeti.LinearAlgebra.SymmetricAlgebra.Evaluation
import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
import TauCeti.LinearAlgebra.SymmetricAlgebra.Polarization

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
  degree-`m` component of `S(H)`; this is the polarization form of the polynomial density of the
  dominant integral weights (`TauCeti.polynomial_eq_zero_of_dominantIntegral`).
* **Averaging.** Averaging `t_λ ^ m` over the Weyl group gives the power sum of
  `∑_w e^{w λ}`, a Weyl-invariant element supported on the Weyl orbit of `λ` and hence a
  combination of orbit sums, and averaging fixes a Weyl invariant. Since the form `⟨·,·⟩` is
  Weyl-invariant, the averaging can be read off from values at weights alone.

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
* `TauCeti.trace_toEnd_pow_eq_sum_finrank_nsmul`: `tr (ρ_M(h) ^ m) = ∑_μ dim M_μ · μ(h) ^ m`.
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
  rw [SymmetricAlgebra.lift_ι_apply, ← invForm_cartanEquivDual_right, LinearEquiv.apply_symm_apply]

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
Its value at the weight `κ(h, ·)` is `tr (ρ_M(h) ^ m)`
(`TauCeti.lift_cartanEquivDual_tracePowerRestriction`), so it is the restriction to `H` of the
invariant polynomial function `x ↦ tr (ρ_M(x) ^ m)` on `L`, transported along the Killing duality
`H ≃ H*`. -/
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

/-- **The trace of a power of a Cartan element**: `tr (ρ_M(h) ^ m) = ∑_μ dim M_μ · μ(h) ^ m`, the
sum over the weights `μ` of `M`. -/
theorem trace_toEnd_pow_eq_sum_finrank_nsmul (h : H) (m : ℕ) :
    LinearMap.trace K M (toEnd K H M h ^ m) =
      ∑ chi : Weight K H M, finrank K (genWeightSpace M chi) • chi h ^ m := by
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K H M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K H M)
  -- the weight space of `chi` is an honest eigenspace, on which `h` acts by the scalar `chi h`
  have hact (chi : Weight K H M) (n : ℕ) (x : M) (hx : x ∈ genWeightSpace M chi) :
      (toEnd K H M h ^ n) x = chi h ^ n • x := by
    rw [genWeightSpace_eq_weightSpace, mem_weightSpace] at hx
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, toEnd_apply_apply, hx, smul_smul,
        pow_succ]
  have hmaps (chi : Weight K H M) : Set.MapsTo (toEnd K H M h ^ m)
      (genWeightSpace M chi) (genWeightSpace M chi) := fun x hx ↦ by
    rw [SetLike.mem_coe, hact chi m x hx]
    exact Submodule.smul_mem _ _ hx
  rw [LinearMap.trace_eq_sum_trace_restrict hds hmaps]
  refine Finset.sum_congr rfl fun chi _ ↦ ?_
  have hres : (toEnd K H M h ^ m).restrict (hmaps chi) = chi h ^ m • LinearMap.id :=
    LinearMap.ext fun x ↦ Subtype.ext (hact chi m x x.2)
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, nsmul_eq_mul, mul_comm, finrank_toSubmodule]

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
    (invForm_isSymm (H := H)).eq, invForm_cartanEquivDual_right]
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
  · have hform := (rootInvariantForm (H := H)).apply_weylGroup_smul (IsKilling.rootSystem H) w lam
      (w⁻¹ • mu)
    rw [smul_inv_smul, rootInvariantForm_form] at hform
    rw [hf.coeff_smul, hform]

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

variable (b) in
/-- **The powers `t_λ ^ m` of the dominant integral weights span `Sᵐ(H)`.** This is the
polynomial density of the dominant integral weights, transported along the Killing duality
`H ≃ H*`, in its polarization form. -/
theorem span_pow_cartanEquivDual_symm_eq_homogeneousSubmodule (m : ℕ) :
    Submodule.span K ((fun lam ↦ SymmetricAlgebra.ι K H ((IsKilling.cartanEquivDual H).symm lam) ^
        m) '' {lam | IsDominantIntegral b lam}) =
      SymmetricAlgebra.homogeneousSubmodule K H m := by
  rw [← SymmetricAlgebra.span_pow_eq_homogeneous_of_polynomial_vanishing
    ((IsKilling.cartanEquivDual H).symm '' {lam | IsDominantIntegral b lam}) (fun q hq ↦ ?_) m,
    Set.image_image]
  -- transport `q` from `S(H*)` to `S(H)` along the Killing duality
  let e := SymmetricAlgebra.mapEquiv K (IsKilling.cartanEquivDual H).symm
  have hlift (lam : Dual K H) : SymmetricAlgebra.lift lam (e q) =
      SymmetricAlgebra.lift (Dual.eval K H ((IsKilling.cartanEquivDual H).symm lam)) q := by
    rw [SymmetricAlgebra.mapEquiv_apply, ← AlgHom.comp_apply]
    congr 1
    refine SymmetricAlgebra.algHom_ext <| LinearMap.ext fun mu ↦ ?_
    have hval := invForm_cartanEquivDual_right mu ((IsKilling.cartanEquivDual H).symm lam)
    have hval' := invForm_cartanEquivDual_right lam ((IsKilling.cartanEquivDual H).symm mu)
    rw [LinearEquiv.apply_symm_apply] at hval hval'
    simp only [LinearMap.coe_comp, LinearMap.coe_ofClass, AlgHom.coe_comp, Function.comp_apply,
      SymmetricAlgebra.map_apply_ι, LinearEquiv.coe_coe, SymmetricAlgebra.lift_ι_apply,
      SymmetricAlgebra.lift_comp_ι, Dual.eval_apply]
    rw [← hval, ← hval', (invForm_isSymm (H := H)).eq]
  have hzero : e q = 0 := polynomial_eq_zero_of_dominantIntegral b fun lam hlam ↦ by
    rw [hlift]
    exact hq _ ⟨lam, hlam, rfl⟩
  simpa using hzero

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
    (m : ℕ) :
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
  -- the values of a polynomial, and its Weyl average, at every weight
  let ev : SymmetricAlgebra K H →ₗ[K] Dual K H → K :=
    LinearMap.pi fun nu ↦ (SymmetricAlgebra.lift nu).toLinearMap
  let avg : SymmetricAlgebra K H →ₗ[K] Dual K H → K :=
    LinearMap.pi fun nu ↦ ∑ w : (IsKilling.rootSystem H).weylGroup,
      (SymmetricAlgebra.lift (w⁻¹ • nu)).toLinearMap
  -- every element of `Sᵐ(H)` has a Weyl average which is the value function of an element of `V`
  have havg : SymmetricAlgebra.homogeneousSubmodule K H m ≤ (V.map ev).comap avg := by
    rw [← span_pow_cartanEquivDual_symm_eq_homogeneousSubmodule b m, Submodule.span_le]
    rintro _ ⟨lam, hlam, rfl⟩
    refine ⟨_, weightPowerSum_sum_single_smul_mem_span m hlam, funext fun nu ↦ ?_⟩
    simp only [ev, avg, LinearMap.pi_apply, LinearMap.sum_apply, AlgHom.toLinearMap_apply, map_sum,
      weightPowerSum_single, map_pow, lift_ι_cartanEquivDual_symm, one_smul]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    have hform := (rootInvariantForm (H := H)).apply_weylGroup_smul (IsKilling.rootSystem H) w
      (w⁻¹ • nu) lam
    rw [smul_inv_smul, rootInvariantForm_form] at hform
    rw [hform]
  obtain ⟨r, hr, hrp⟩ := havg hhom
  -- for an invariant `p` the average is `|W|` times the value function, so `p = |W|⁻¹ r`
  have hcard : (Fintype.card (IsKilling.rootSystem H).weylGroup : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hp : p = (Fintype.card (IsKilling.rootSystem H).weylGroup : K)⁻¹ • r := by
    refine SymmetricAlgebra.eq_of_forall_lift_apply_eq fun nu ↦ ?_
    have hval := congrFun hrp nu
    simp only [ev, avg, LinearMap.pi_apply, LinearMap.sum_apply, AlgHom.toLinearMap_apply,
      (mem_linearInvariants_iff.mp hinv) _ nu, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hval
    rw [map_smul, hval, smul_eq_mul, inv_mul_cancel_left₀ hcard]
  rw [hp]
  exact V.smul_mem _ hr

end Span

end TauCeti
