/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.PrincipalIdealRing
public import TauCeti.NumberTheory.LocalField.Different.Basic
public import TauCeti.NumberTheory.LocalField.Topology
public import TauCeti.RingTheory.DedekindDomain.Different.Quotient
public import TauCeti.Topology.Algebra.Module.PontryaginDual.GroupAction
import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
import TauCeti.RingTheory.Length

/-!
# Coefficient-linear Pontryagin duality over rings of integers of local fields

For a nonarchimedean local field `L` with ring of integers `𝒪[L]`, the discrete divisible module
`L ⧸ 𝒪[L]` (written `L ⧸ (1 : Submodule 𝒪[L] L)`) is an injective `𝒪[L]`-module whose
`𝓂[L]`-torsion is isomorphic to the residue field `𝒪[L] ⧸ 𝓂[L]` of length `1`. Consequently,
the general compact–discrete duality of `TauCeti.ModulePontryaginDual` applies directly to
`R = 𝒪[L]` and `E = L ⧸ 𝒪[L]`:

* On discrete `𝒪[L]`-modules, continuity of the `𝒪[L]`-action is equivalent to being an
  `𝒪[L]`-torsion module (`TauCeti.continuousSMul_iff_isTorsion`).
* The Pontryagin dual `Hom_𝒪[L]^cont(-, L ⧸ 𝒪[L])` carries discrete torsion `𝒪[L]`-modules to
  compact `𝒪[L]`-modules and compact `𝒪[L]`-modules to discrete torsion `𝒪[L]`-modules, with
  biduality equivalences in both directions.
* For each `n : ℕ`, the dual of `𝒪[L] ⧸ 𝓂[L]^n` is continuously `𝒪[L]`-linearly equivalent to
  `𝒪[L] ⧸ 𝓂[L]^n`.

For a compatible separable extension `L / K` of nonarchimedean local fields, the trace map
`Tr_{L/K} : L → K` induces a canonical topological `𝒪[K]`-linear equivalence

`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`

for every topological `𝒪[L]`-module `M` with continuous constant `𝒪[L]`-action, compatible with
both the `𝒪[L]`-action and contragredient group representations. Choosing any uniformizer `ϖ` of
`𝒪[L]`, dividing by `ϖ ^ d(L/K)` identifies `L ⧸ 𝒪[L]` with `L ⧸ 𝒪[L]ᵛ` and therefore yields a
continuous linear equivalence `Hom_𝒪[L]^cont(M, L ⧸ 𝒪[L]) ≃L[𝒪[K]] Hom_𝒪[K]^cont(M, K ⧸ 𝒪[K])`.

By contrast, the naive trace pairing `L ⧸ 𝒪[L] → Hom_𝒪[K](𝒪[L], K ⧸ 𝒪[K])` is injective if and
only if `L / K` is unramified; in every ramified extension, the class `[ϖ⁻¹] ∈ L ⧸ 𝒪[L]` is a
nonzero element of its kernel.

## Main definitions and results

* `TauCeti.isOpen_one_submodule_integerRing`, `TauCeti.instDiscreteTopologyQuotientOne`:
  `𝒪[L]` is open in `L`, so `L ⧸ 𝒪[L]` is discrete.
* `TauCeti.continuousSMul_iff_isTorsion`: a discrete `𝒪[L]`-module has continuous `𝒪[L]`-action
  if and only if it is a torsion module.
* `TauCeti.quotientMaximalIdealPowEquivTorsionBySet`: the `𝓂[L]^n`-torsion of `L ⧸ 𝒪[L]` is
  isomorphic to `𝒪[L] ⧸ 𝓂[L]^n`.
* `TauCeti.length_linearMap_quotient_maximalIdeal_eq_one`: the cogenerator condition
  `length_𝒪[L](Hom_𝒪[L](𝒪[L] ⧸ 𝔪, L ⧸ 𝒪[L])) = 1`.
* `TauCeti.dualQuotientMaximalIdealPowEquiv`: self-duality of `𝒪[L] ⧸ 𝓂[L]^n`.
* `TauCeti.isTorsion_dual_of_isCompactModule`: the dual of a compact `𝒪[L]`-module is torsion.
* `TauCeti.traceDualPontryaginEquiv`: topological inverse-different trace comparison
  `ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`.
* `TauCeti.pontryaginDualEquivOfUniformizer`: comparison between `L ⧸ 𝒪[L]`-duals and
  `K ⧸ 𝒪[K]`-duals via a uniformizer `ϖ` and the different exponent `d(L/K)`.
* `TauCeti.ker_directTracePairing_eq_bot_iff_isUnramified`: the naive trace pairing is injective
  if and only if `L / K` is unramified.
* `TauCeti.mk_inv_uniformizer_ne_zero` and `TauCeti.mk_inv_uniformizer_mem_ker_directTracePairing`:
  explicit nonzero element `[ϖ⁻¹]` in the kernel of the naive trace pairing for any ramified
  extension.

## References

* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §2.
* J.-P. Serre, *Local Fields*, Chapter III, §§3 and 6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing TauCeti.ModulePontryaginDual

namespace TauCeti

section SingleField

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The submodule `(1 : Submodule 𝒪[L] L)` is open in `L`, as it coincides with `𝒪[L]`. -/
theorem isOpen_one_submodule_integerRing : IsOpen ((1 : Submodule 𝒪[L] L) : Set L) := by
  have heq : ((1 : Submodule 𝒪[L] L) : Set L) = (𝒪[L] : Set L) := by
    ext x
    rw [SetLike.mem_coe, Submodule.mem_one]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rw [heq]
  exact Valuation.isOpen_integer

/-- The quotient `L ⧸ 𝒪[L]` carries the discrete topology. -/
instance instDiscreteTopologyQuotientOne :
    DiscreteTopology (L ⧸ (1 : Submodule 𝒪[L] L)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_one_submodule_integerRing L)

/-- Every nonzero ideal of `𝒪[L]` is open in `𝒪[L]`. -/
theorem isOpen_ideal_of_ne_bot {I : Ideal 𝒪[L]} (hI : I ≠ ⊥) : IsOpen (I : Set 𝒪[L]) := by
  obtain ⟨a, rfl⟩ := IsPrincipalIdealRing.principal I
  have ha : a ≠ 0 := by
    rintro rfl
    exact hI (by simp)
  have haL : (a : L) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hopen : IsOpen ((Homeomorph.mulLeft₀ (a : L) haL) '' (𝒪[L] : Set L)) :=
    (Homeomorph.mulLeft₀ (a : L) haL).isOpenMap _ Valuation.isOpen_integer
  have hpre : ((↑) : 𝒪[L] → L) ⁻¹' ((Homeomorph.mulLeft₀ (a : L) haL) '' (𝒪[L] : Set L)) =
      (Ideal.span {a} : Set 𝒪[L]) := by
    ext r
    simp only [Set.mem_preimage, Set.mem_image, Homeomorph.coe_mulLeft₀, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨x, hx, hax⟩
      refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
      simpa using hax.symm
    · rintro ⟨c, rfl⟩
      exact ⟨(c : L), c.2, rfl⟩
  rw [← hpre]
  exact hopen.preimage continuous_subtype_val

/-- The ring of integers `𝒪[L]` of a nonarchimedean local field is infinite. -/
private theorem infinite_integerRing : Infinite 𝒪[L] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  refine Infinite.of_injective (fun n : ℕ ↦ ϖ ^ n) fun m n hmn ↦ ?_
  wlog hlt : m ≤ n generalizing m n
  · exact (this n m hmn.symm (le_of_not_ge hlt)).symm
  rcases eq_or_lt_of_le hlt with rfl | hlt
  · rfl
  · exfalso
    dsimp only at hmn
    have hmul : ϖ ^ m * 1 = ϖ ^ m * ϖ ^ (n - m) := by
      rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt), hmn]
    have hpow : ϖ ^ (n - m) = 1 := (mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) hmul).symm
    have hunit : IsUnit (ϖ ^ (n - m)) := hpow ▸ isUnit_one
    exact hϖ.not_isUnit ((isUnit_pow_iff (Nat.sub_ne_zero_of_lt hlt)).mp hunit)

variable {L} in
/-- **Continuity equals torsion on discrete `𝒪[L]`-modules**: a discrete `𝒪[L]`-module has
continuous `𝒪[L]`-action if and only if every element is killed by a nonzero element of `𝒪[L]`. -/
theorem continuousSMul_iff_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMul 𝒪[L] M ↔ Module.IsTorsion 𝒪[L] M := by
  constructor
  · intro _ m
    let I : Ideal 𝒪[L] := LinearMap.ker (LinearMap.toSpanSingleton 𝒪[L] M m)
    have hopen : IsOpen (I : Set 𝒪[L]) := isOpen_annihilator_elem m
    have hfin : Finite (𝒪[L] ⧸ I) := finite_quotient_of_isOpen I hopen
    have hne : I ≠ ⊥ := by
      intro hbot
      have : Finite 𝒪[L] := Finite.of_equiv (𝒪[L] ⧸ I) (Submodule.quotEquivOfEqBot I hbot).toEquiv
      exact (infinite_integerRing L).not_finite this
    obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr0⟩, LinearMap.mem_ker.mp hrI⟩
  · intro htor
    refine ⟨continuous_iff_continuousAt.mpr fun ⟨r₀, m₀⟩ ↦ ?_⟩
    obtain ⟨⟨a, ha⟩, ham⟩ := @htor m₀
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    let I : Ideal 𝒪[L] := Ideal.span {a}
    have hIopen : IsOpen (I : Set 𝒪[L]) :=
      isOpen_ideal_of_ne_bot L (mt Ideal.span_singleton_eq_bot.mp ha0)
    let U : Set 𝒪[L] := (fun r : 𝒪[L] ↦ r - r₀) ⁻¹' (I : Set 𝒪[L])
    have hUopen : IsOpen U := hIopen.preimage (continuous_id.sub continuous_const)
    have hr₀U : r₀ ∈ U := by
      change r₀ - r₀ ∈ I
      rw [sub_self]
      exact I.zero_mem
    have hnhds : U ×ˢ {m₀} ∈ nhds (r₀, m₀) :=
      (hUopen.prod (isOpen_discrete {m₀})).mem_nhds ⟨hr₀U, rfl⟩
    refine (continuousAt_const (y := r₀ • m₀)).congr (Filter.eventually_of_mem hnhds ?_)
    rintro ⟨r, m⟩ ⟨hr, hm⟩
    have hm' : m = m₀ := Set.mem_singleton_iff.mp hm
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
    have hc' : r - r₀ = a * c := hc
    have hdiff : (r - r₀) • m₀ = 0 := by
      rw [hc', mul_comm, mul_smul, show a • m₀ = 0 from ham, smul_zero]
    dsimp only
    rw [hm', ← sub_eq_zero, ← sub_smul, ← neg_sub, neg_smul, hdiff, neg_zero]

variable {L} in
/-- Given a uniformizer `ϖ` of `𝒪[L]`, the `𝓂[L]^n`-torsion submodule of `L ⧸ 𝒪[L]` is
`𝒪[L]`-linearly isomorphic to `𝒪[L] ⧸ 𝓂[L]^n`, via `[a] ↦ [a / ϖ^n]`. -/
def quotientMaximalIdealPowEquivTorsionBySet {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃ₗ[𝒪[L]]
      Submodule.torsionBySet 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
        ((𝓂[L] ^ n : Ideal 𝒪[L]) : Set 𝒪[L]) := by
  have hϖL : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hpowL : (ϖ : L) ^ n ≠ 0 := pow_ne_zero n hϖL
  have hmn : (𝓂[L] ^ n : Ideal 𝒪[L]) = Ideal.span {ϖ ^ n} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  let f : 𝒪[L] →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L)) :=
    { toFun := fun a ↦ Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n)
      map_add' := fun a b ↦ by
        simp only [Subring.coe_add, add_div, Submodule.Quotient.mk_add]
      map_smul' := fun r a ↦ by
        simp only [RingHom.id_apply, smul_eq_mul, Subring.coe_mul, mul_div_assoc]
        rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]
        rfl }
  have hker : LinearMap.ker f = 𝓂[L] ^ n := by
    rw [hmn]
    ext a
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
    change Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((a : L) / (ϖ : L) ^ n) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, Subtype.ext ?_⟩
      have hb' : (b : L) = (a : L) / (ϖ : L) ^ n := hb
      have := (div_eq_iff hpowL).mp hb'.symm
      simpa [mul_comm] using this
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      change (b : L) = ((ϖ : L) ^ n * (b : L)) / (ϖ : L) ^ n
      rw [mul_div_cancel_left₀ _ hpowL]
  have hrange : LinearMap.range f =
      Submodule.torsionBySet 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
        ((𝓂[L] ^ n : Ideal 𝒪[L]) : Set 𝒪[L]) := by
    ext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_range, Submodule.mem_torsionBySet_iff]
    constructor
    · rintro ⟨a, ha⟩ ⟨r, hr⟩
      rw [SetLike.mem_coe, hmn, Ideal.mem_span_singleton] at hr
      obtain ⟨c, rfl⟩ := hr
      rw [← ha]
      change (ϖ ^ n * c) • Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      refine ⟨c * a, ?_⟩
      change ((c * a : 𝒪[L]) : L) = ((ϖ ^ n * c : 𝒪[L]) : L) * ((a : L) / (ϖ : L) ^ n)
      push_cast
      field_simp [hpowL]
    · intro h
      have hϖn : ϖ ^ n ∈ (𝓂[L] ^ n : Ideal 𝒪[L]) := by
        rw [hmn]
        exact Ideal.mem_span_singleton_self (ϖ ^ n)
      have h0 : ϖ ^ n • Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) x = 0 :=
        h ⟨ϖ ^ n, hϖn⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
      obtain ⟨a, ha⟩ := h0
      refine ⟨a, ?_⟩
      change Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) = Submodule.Quotient.mk x
      congr 1
      change (a : L) = ((ϖ ^ n : 𝒪[L]) : L) * x at ha
      push_cast at ha
      rw [ha, mul_div_cancel_left₀ _ hpowL]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

variable {L} in
@[simp]
theorem quotientMaximalIdealPowEquivTorsionBySet_mk {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ)
    (a : 𝒪[L]) :
    (quotientMaximalIdealPowEquivTorsionBySet hϖ n
        (Ideal.Quotient.mk (𝓂[L] ^ n : Ideal 𝒪[L]) a) :
        L ⧸ (1 : Submodule 𝒪[L] L)) =
      Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) := by
  rfl

/-- **Cogenerator condition for `L ⧸ 𝒪[L]`**: for every maximal ideal `𝔪` of `𝒪[L]`, the module
`Hom_𝒪[L](𝒪[L] ⧸ 𝔪, L ⧸ 𝒪[L])` has length `1`. -/
theorem length_linearMap_quotient_maximalIdeal_eq_one :
    ∀ 𝔪 : Ideal 𝒪[L], 𝔪.IsMaximal →
      Module.length 𝒪[L] ((𝒪[L] ⧸ 𝔪) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) = 1 := by
  intro 𝔪 h𝔪
  have hmeq : 𝔪 = 𝓂[L] := IsLocalRing.eq_maximalIdeal h𝔪
  subst hmeq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have e₁ := 𝓂[L].quotientLinearMapEquivTorsionBySet (L ⧸ (1 : Submodule 𝒪[L] L))
  have e₂ := quotientMaximalIdealPowEquivTorsionBySet hϖ 1
  have hpow : (𝓂[L] ^ 1 : Ideal 𝒪[L]) = 𝓂[L] := pow_one _
  have e : ((𝒪[L] ⧸ 𝓂[L]) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) ≃ₗ[𝒪[L]] (𝒪[L] ⧸ 𝓂[L]) :=
    e₁.trans ((LinearEquiv.ofEq _ _ (by rw [hpow])).symm.trans
      (e₂.symm.trans (Submodule.quotEquivOfEq _ _ hpow)))
  rw [e.length_eq, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪[L]).out

/-- **Compactness of the dual of a discrete torsion `𝒪[L]`-module**: `Hom_𝒪[L](M, L ⧸ 𝒪[L])` is
a compact `𝒪[L]`-module whenever `M` is discrete and torsion. -/
theorem isCompactModule_dual_of_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] (hM : Module.IsTorsion 𝒪[L] M) :
    IsCompactModule 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) := by
  have : ContinuousSMul 𝒪[L] M := continuousSMul_iff_isTorsion.mpr hM
  exact isCompactModule_of_discrete (length_linearMap_quotient_maximalIdeal_eq_one L)

/-- **The dual of a compact `𝒪[L]`-module is torsion**: every continuous `𝒪[L]`-linear functional
on a compact `𝒪[L]`-module into `L ⧸ 𝒪[L]` is killed by a nonzero element of `𝒪[L]`. -/
theorem isTorsion_dual_of_isCompactModule {N : Type*} [AddCommGroup N] [Module 𝒪[L] N]
    [TopologicalSpace N] (hN : IsCompactModule 𝒪[L] N) :
    Module.IsTorsion 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) N) := by
  have := hN.compactSpace
  exact continuousSMul_iff_isTorsion.mp inferInstance

variable {L} in
/-- **Self-duality of `𝒪[L] ⧸ 𝓂[L]^n`**: choosing a uniformizer `ϖ`, the Pontryagin dual of
`𝒪[L] ⧸ 𝓂[L]^n` with respect to `L ⧸ 𝒪[L]` is continuously `𝒪[L]`-linearly equivalent to
`𝒪[L] ⧸ 𝓂[L]^n`. -/
def dualQuotientMaximalIdealPowEquiv {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃L[𝒪[L]]
      (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) := by
  have hne : (𝓂[L] ^ n : Ideal 𝒪[L]) ≠ ⊥ := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero n hϖ.ne_zero
  have : DiscreteTopology (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_ideal_of_ne_bot L hne)
  have : CompactSpace (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    have : Finite (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
      finite_quotient_of_isOpen _ (isOpen_ideal_of_ne_bot L hne)
    Finite.compactSpace
  let e : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
        (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃ₗ[𝒪[L]] (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    (equivLinearMap 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L]))).trans
      (((𝓂[L] ^ n : Ideal 𝒪[L]).quotientLinearMapEquivTorsionBySet
        (L ⧸ (1 : Submodule 𝒪[L] L))).trans
        (quotientMaximalIdealPowEquivTorsionBySet hϖ n).symm)
  exact {
    toLinearEquiv := e
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

end SingleField

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
/-- The scalar tower `𝒪[K] → 𝒪[L] → L` for a compatible extension of local fields. -/
instance instIsScalarTowerIntegerRing : IsScalarTower 𝒪[K] 𝒪[L] L :=
  .of_algebraMap_eq' rfl

/-- `𝒪[L]` is the integral closure of `𝒪[K]` in `L`. -/
theorem isIntegralClosure_integerRing : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    have := finite_of_valuativeExtension K L
    have hmem : x ∈ 𝒪[L] ↔ IsIntegral 𝒪[K] x := by
      rw [integerRing_eq_integralClosure K L, Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact ⟨fun hx ↦ ⟨⟨x, hmem.mpr hx⟩, rfl⟩, fun ⟨b, hb⟩ ↦ hmem.mp (hb ▸ b.2)⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Scalar multiplication by `𝒪[K]` on any quotient `L ⧸ P` by an `𝒪[L]`-submodule `P` is
continuous in the second variable. -/
instance instContinuousConstSMulQuotient (P : Submodule 𝒪[L] L) :
    ContinuousConstSMul 𝒪[K] (L ⧸ P) where
  continuous_const_smul a := by
    have heq : (fun q : L ⧸ P ↦ a • q) = fun q : L ⧸ P ↦ algebraMap 𝒪[K] 𝒪[L] a • q :=
      funext fun q ↦ (algebraMap_smul 𝒪[L] a q).symm
    rw [heq]
    exact continuous_const_smul (algebraMap 𝒪[K] 𝒪[L] a)

/-- The inverse different `𝒪[L]ᵛ` is an open `𝒪[L]`-submodule of `L`. -/
theorem isOpen_traceDual_one :
    IsOpen (Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L) : Set L) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  have hle : (1 : Submodule 𝒪[L] L) ≤ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L) :=
    Submodule.one_le_traceDual_one
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(fun y : L ↦ y - x) ⁻¹' ((1 : Submodule 𝒪[L] L) : Set L), ?_,
    (isOpen_one_submodule_integerRing L).preimage (continuous_id.sub continuous_const), ?_⟩
  · intro y hy
    have hy' : y - x ∈ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L) := hle hy
    have : y = (y - x) + x := by abel
    rw [this]
    exact (Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)).add_mem hy' hx
  · change x - x ∈ (1 : Submodule 𝒪[L] L)
    rw [sub_self]
    exact (1 : Submodule 𝒪[L] L).zero_mem

/-- The quotient `L ⧸ 𝒪[L]ᵛ` carries the discrete topology. -/
instance instDiscreteTopologyQuotientTraceDual :
    DiscreteTopology (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_traceDual_one K L)

variable [Algebra.IsSeparable K L]

/-- **Topological inverse-different trace comparison**: for any topological `𝒪[L]`-module `M`
with continuous constant `𝒪[L]`-action, postcomposition with the trace map `L ⧸ 𝒪[L]ᵛ → K ⧸ 𝒪[K]`
gives a canonical continuous `𝒪[K]`-linear equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def traceDualPontryaginEquiv (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  let hfam := exists_sum_trace_mul_smul_eq 𝒪[K] K (B := 𝒪[L]) (L := L)
  let n : ℕ := Classical.choose hfam
  have hn := Classical.choose_spec hfam
  let b : Fin n → 𝒪[L] := Classical.choose hn
  have hb := Classical.choose_spec hn
  let y : Fin n → L := Classical.choose hb
  have hy_all := Classical.choose_spec hb
  let hy := hy_all.1
  let hsum := hy_all.2
  let trCM : C(L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L),
      K ⧸ (1 : Submodule 𝒪[K] K)) :=
    ⟨traceDualQuotientMap 𝒪[K] K 𝒪[L] L, continuous_of_discreteTopology⟩
  let mulCM : Fin n → C(K ⧸ (1 : Submodule 𝒪[K] K),
      L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) := fun i ↦
    ⟨mulByTraceDualQuotientMap 𝒪[K] K 𝒪[L] L (y i) (hy i), continuous_of_discreteTopology⟩
  let toF : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M →
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M := fun φ ↦
    ⟨{ toLinearMap := traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ.toContinuousLinearMap.toLinearMap
       cont := by
         have heq : ⇑(traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
             φ.toContinuousLinearMap.toLinearMap) = fun m ↦ trCM (φ m) := funext fun m ↦
           traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L φ.toContinuousLinearMap.toLinearMap m
         change Continuous ⇑(traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
           φ.toContinuousLinearMap.toLinearMap)
         rw [heq]
         exact trCM.continuous.comp (map_continuous φ) }⟩
  let invF : ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M →
      ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M :=
    fun ψ ↦
      ⟨{ toLinearMap := (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm
            ψ.toContinuousLinearMap.toLinearMap
         cont := by
           have heq : ⇑((traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm
               ψ.toContinuousLinearMap.toLinearMap) =
               fun m ↦ ∑ i : Fin n, mulCM i (ψ (b i • m)) := funext fun m ↦
             traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum
               ψ.toContinuousLinearMap.toLinearMap m
           change Continuous ⇑((traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm
             ψ.toContinuousLinearMap.toLinearMap)
           rw [heq]
           exact continuous_finsetSum Finset.univ fun i _ ↦
             (mulCM i).continuous.comp ((map_continuous ψ).comp (continuous_const_smul (b i))) }⟩
  refine {
    toFun := toF
    invFun := invF
    left_inv := fun φ ↦ ext fun m ↦ by
      change (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm
        (traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ.toContinuousLinearMap.toLinearMap) m = φ m
      rw [LinearEquiv.symm_apply_apply]
      rfl
    right_inv := fun ψ ↦ ext fun m ↦ by
      change traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
        ((traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M).symm ψ.toContinuousLinearMap.toLinearMap) m =
        ψ m
      rw [LinearEquiv.apply_symm_apply]
      rfl
    map_add' := fun φ₁ φ₂ ↦ ext fun m ↦ by
      change traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
          (φ₁ + φ₂).toContinuousLinearMap.toLinearMap m =
        traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ₁.toContinuousLinearMap.toLinearMap m +
          traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ₂.toContinuousLinearMap.toLinearMap m
      rw [traceDualLinearMapEquiv_apply, traceDualLinearMapEquiv_apply,
        traceDualLinearMapEquiv_apply]
      exact map_add _ _ _
    map_smul' := fun a φ ↦ ext fun m ↦ by
      change traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
          (a • φ).toContinuousLinearMap.toLinearMap m =
        a • traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M φ.toContinuousLinearMap.toLinearMap m
      rw [traceDualLinearMapEquiv_apply, traceDualLinearMapEquiv_apply]
      exact map_smul (traceDualQuotientMap 𝒪[K] K 𝒪[L] L) a (φ m)
    continuous_toFun := by
      rw [(isInducing_toContinuousMap (R := 𝒪[K])
        (E := K ⧸ (1 : Submodule 𝒪[K] K)) (M := M)).continuous_iff]
      have heq : (ModulePontryaginDual.toContinuousMap ∘ toF) =
          fun φ ↦ trCM.comp φ.toContinuousMap := by
        ext φ m
        simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.comp_apply]
        exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L φ.toContinuousLinearMap.toLinearMap m
      rw [heq]
      exact (ContinuousMap.continuous_postcomp trCM).comp
        (continuous_toContinuousMap (R := 𝒪[L])
          (E := L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) (M := M))
    continuous_invFun := by
      rw [(isInducing_toContinuousMap (R := 𝒪[L])
        (E := L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) (M := M)).continuous_iff]
      have hterm : ∀ i : Fin n, Continuous (fun ψ : ModulePontryaginDual 𝒪[K]
          (K ⧸ (1 : Submodule 𝒪[K] K)) M ↦
          (mulCM i).comp
            (ψ.toContinuousMap.comp ⟨(b i • ·), continuous_const_smul (b i)⟩)) := fun i ↦
        (ContinuousMap.continuous_postcomp (mulCM i)).comp
          ((ContinuousMap.continuous_precomp ⟨(b i • ·), continuous_const_smul (b i)⟩).comp
            (continuous_toContinuousMap (R := 𝒪[K])
              (E := K ⧸ (1 : Submodule 𝒪[K] K)) (M := M)))
      have heq : (ModulePontryaginDual.toContinuousMap ∘ invF) =
          fun ψ ↦ ∑ i : Fin n, (mulCM i).comp
            (ψ.toContinuousMap.comp ⟨(b i • ·), continuous_const_smul (b i)⟩) := by
        ext ψ m
        simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.coe_sum,
          Finset.sum_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        exact traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum
          ψ.toContinuousLinearMap.toLinearMap m
      rw [heq]
      exact continuous_finsetSum Finset.univ fun i _ ↦ hterm i }

@[simp]
theorem traceDualPontryaginEquiv_apply {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) :
    traceDualPontryaginEquiv K L M φ m = traceDualQuotientMap 𝒪[K] K 𝒪[L] L (φ m) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L φ.toContinuousLinearMap.toLinearMap m

/-- Compatibility of `traceDualPontryaginEquiv` with the `𝒪[L]`-action on `M`. -/
theorem traceDualPontryaginEquiv_smul_apply {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
    (b : 𝒪[L])
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) :
    traceDualPontryaginEquiv K L M (b • φ) m = traceDualPontryaginEquiv K L M φ (b • m) := by
  rw [traceDualPontryaginEquiv_apply, traceDualPontryaginEquiv_apply,
    ModulePontryaginDual.smul_apply, map_smul φ b m]

/-- Compatibility of `traceDualPontryaginEquiv` with contragredient group representations. -/
theorem traceDualPontryaginEquiv_contragredient {G M : Type*} [Group G]
    [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝒪[L] M]
    (ρ : ContRepresentation 𝒪[L] G M) (g : G)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M) :
    let ρK : ContRepresentation 𝒪[K] G M :=
      ⟨{ toFun := fun h ↦ (ρ h).restrictScalars 𝒪[K]
         map_one' := by ext x; simp
         map_mul' := fun h₁ h₂ ↦ by ext x; simp }⟩
    traceDualPontryaginEquiv K L M
        (contragredient (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) ρ g φ) =
      contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) ρK g (traceDualPontryaginEquiv K L M φ) := by
  intro ρK
  ext m
  simp [traceDualPontryaginEquiv_apply, contragredient_apply, ρK]
  rfl

/-- For any uniformizer `ϖ` of `𝒪[L]`, the different ideal is generated by `ϖ ^ d(L/K)`. -/
theorem differentIdeal_eq_span_pow_uniformizer {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    differentIdeal 𝒪[K] 𝒪[L] = Ideal.span {ϖ ^ differentExponent K L} := by
  rw [differentIdeal_eq_maximalIdeal_pow K L, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- Given a uniformizer `ϖ` of `𝒪[L]`, dividing by `ϖ ^ d(L/K)` gives a continuous `𝒪[L]`-linear
equivalence `(L ⧸ 𝒪[L]) ≃L[𝒪[L]] (L ⧸ 𝒪[L]ᵛ)`. -/
def quotientEquivTraceDualQuotientOfUniformizer {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    (L ⧸ (1 : Submodule 𝒪[L] L)) ≃L[𝒪[L]]
      (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  exact {
    toLinearEquiv := quotientEquivTraceDualQuotientOfDifferentIdealEqSpan 𝒪[K] K 𝒪[L] L
      (differentIdeal_eq_span_pow_uniformizer K L hϖ)
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

@[simp]
theorem quotientEquivTraceDualQuotientOfUniformizer_mk {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (x : L) :
    quotientEquivTraceDualQuotientOfUniformizer K L hϖ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x / ((ϖ : L) ^ differentExponent K L)) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  change quotientEquivTraceDualQuotientOfDifferentIdealEqSpan 𝒪[K] K 𝒪[L] L
    (differentIdeal_eq_span_pow_uniformizer K L hϖ) (Submodule.Quotient.mk x) = _
  rw [quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_mk, map_pow]
  rfl

/-- **Change of coefficient ring for local-field Pontryagin duals**: choosing a uniformizer `ϖ`
of `𝒪[L]`, dividing by `ϖ ^ d(L/K)` and taking `Tr_{L/K}` yields a continuous `𝒪[K]`-linear
equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def pontryaginDualEquivOfUniformizer {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M :=
  let e := congrCodomain (M := M) (quotientEquivTraceDualQuotientOfUniformizer K L hϖ)
  let eK : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M :=
    { toLinearEquiv :=
        { toEquiv := e.toEquiv
          map_add' := e.map_add
          map_smul' := fun a φ ↦ by
            simpa [algebraMap_smul] using e.map_smul (algebraMap 𝒪[K] 𝒪[L] a) φ }
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  eK.trans (traceDualPontryaginEquiv K L M)

@[simp]
theorem pontryaginDualEquivOfUniformizer_apply {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M φ m =
      traceDualQuotientMap 𝒪[K] K 𝒪[L] L
        (quotientEquivTraceDualQuotientOfUniformizer K L hϖ (φ m)) := by
  change traceDualPontryaginEquiv K L M
    (congrCodomain (M := M) (quotientEquivTraceDualQuotientOfUniformizer K L hϖ) φ) m = _
  rw [traceDualPontryaginEquiv_apply, congrCodomain_apply]

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with the `𝒪[L]`-action on `M`. -/
theorem pontryaginDualEquivOfUniformizer_smul_apply {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
    (b : 𝒪[L]) (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M (b • φ) m =
      pontryaginDualEquivOfUniformizer K L hϖ M φ (b • m) := by
  rw [pontryaginDualEquivOfUniformizer_apply, pontryaginDualEquivOfUniformizer_apply,
    ModulePontryaginDual.smul_apply, map_smul φ b m]

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with contragredient group
representations. -/
theorem pontryaginDualEquivOfUniformizer_contragredient {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    {G M : Type*} [Group G] [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul 𝒪[L] M]
    (ρ : ContRepresentation 𝒪[L] G M) (g : G)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) :
    let ρK : ContRepresentation 𝒪[K] G M :=
      ⟨{ toFun := fun h ↦ (ρ h).restrictScalars 𝒪[K]
         map_one' := by ext x; simp
         map_mul' := fun h₁ h₂ ↦ by ext x; simp }⟩
    pontryaginDualEquivOfUniformizer K L hϖ M
        (contragredient (L ⧸ (1 : Submodule 𝒪[L] L)) ρ g φ) =
      contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) ρK g
        (pontryaginDualEquivOfUniformizer K L hϖ M φ) := by
  intro ρK
  ext m
  simp [pontryaginDualEquivOfUniformizer_apply, contragredient_apply, ρK]
  rfl

/-- **Exact criterion for the naive trace pairing**: the direct trace pairing
`L ⧸ 𝒪[L] → Hom_𝒪[K](𝒪[L], K ⧸ 𝒪[K])` is injective if and only if `L / K` is unramified. -/
theorem ker_directTracePairing_eq_bot_iff_isUnramified :
    haveI := finite_of_valuativeExtension K L
    haveI := isIntegralClosure_integerRing K L
    LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) = ⊥ ↔ IsUnramified K L := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  exact (ker_directTracePairing_eq_bot_iff_differentIdeal_eq_top 𝒪[K] K 𝒪[L] L).trans
    (differentIdeal_eq_top_iff K L)

variable {K} in
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The class `[ϖ⁻¹] ∈ L ⧸ 𝒪[L]` of the inverse of any uniformizer `ϖ` is nonzero. -/
theorem mk_inv_uniformizer_ne_zero {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((ϖ : L)⁻¹) ≠ 0 := by
  rw [ne_eq, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  rintro ⟨b, hb⟩
  have hϖL : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hb' : (b : L) = (ϖ : L)⁻¹ := hb
  have hmul : ϖ * b = 1 := Subtype.ext (by
    change (ϖ : L) * (b : L) = 1
    rw [hb', mul_inv_cancel₀ hϖL])
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one b hmul)

/-- **Explicit witness in the kernel of the naive trace pairing**: whenever `L / K` is ramified
and `ϖ` is a uniformizer of `𝒪[L]`, the nonzero class `[ϖ⁻¹] ∈ L ⧸ 𝒪[L]` lies in
`ker(directTracePairing 𝒪[K] K 𝒪[L] L)`. -/
theorem mk_inv_uniformizer_mem_ker_directTracePairing (hram : ¬ IsUnramified K L)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    haveI := finite_of_valuativeExtension K L
    haveI := isIntegralClosure_integerRing K L
    Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((ϖ : L)⁻¹) ∈
      LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  rw [mem_ker_directTracePairing_iff,
    mem_traceDual_one_iff_mul_of_differentIdeal_eq_span
      (differentIdeal_eq_span_pow_uniformizer K L hϖ)]
  have hd : 1 ≤ differentExponent K L :=
    Nat.one_le_iff_ne_zero.mpr (mt (differentExponent_eq_zero_iff K L).mp hram)
  have hϖL : (ϖ : L) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  refine Submodule.mem_one.mpr ⟨ϖ ^ (differentExponent K L - 1), ?_⟩
  change ((ϖ ^ (differentExponent K L - 1) : 𝒪[L]) : L) =
    (ϖ : L)⁻¹ * ((ϖ ^ differentExponent K L : 𝒪[L]) : L)
  push_cast
  have hpow : (ϖ : L) ^ differentExponent K L = (ϖ : L) * (ϖ : L) ^ (differentExponent K L - 1) :=
    by rw [← pow_succ', Nat.sub_add_cancel hd]
  rw [hpow, inv_mul_cancel_left₀ hϖL]

end Extension

end TauCeti
