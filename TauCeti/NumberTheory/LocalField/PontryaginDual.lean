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

For a nonarchimedean local field `L` with ring of integers `𝒪[L]`, `L ⧸ 𝒪[L]` is a discrete
injective `𝒪[L]`-module whose `𝓂[L]`-torsion has length `1`, so `TauCeti.ModulePontryaginDual`
gives compact–discrete duality between discrete torsion `𝒪[L]`-modules and compact `𝒪[L]`-modules,
and self-duality of `𝒪[L] ⧸ 𝓂[L]^n`.

For a compatible separable extension `L / K`, trace induces canonical continuous `𝒪[K]`-linear
equivalences `traceDualPontryaginEquiv` and (given a uniformizer `ϖ`)
`pontryaginDualEquivOfUniformizer` compatible with `𝒪[L]`-actions and contragredient group
representations. By contrast, `directTracePairing` is injective iff `L / K` is unramified, with
`[ϖ⁻¹]` a nonzero kernel element whenever `L / K` is ramified.

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
    ext x; rw [SetLike.mem_coe, Submodule.mem_one]
    exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ a.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  rw [heq]; exact Valuation.isOpen_integer

/-- The quotient `L ⧸ 𝒪[L]` carries the discrete topology. -/
instance instDiscreteTopologyQuotientOne : DiscreteTopology (L ⧸ (1 : Submodule 𝒪[L] L)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_one_submodule_integerRing L)

/-- Every nonzero ideal of `𝒪[L]` is open in `𝒪[L]`. -/
theorem isOpen_ideal_of_ne_bot {I : Ideal 𝒪[L]} (hI : I ≠ ⊥) : IsOpen (I : Set 𝒪[L]) := by
  obtain ⟨a, rfl⟩ := IsPrincipalIdealRing.principal I
  have ha : a ≠ 0 := by rintro rfl; exact hI (by simp)
  have haL : (a : L) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hpre : ((↑) : 𝒪[L] → L) ⁻¹' ((Homeomorph.mulLeft₀ (a : L) haL) '' (𝒪[L] : Set L)) =
      (Ideal.span {a} : Set 𝒪[L]) := by
    ext r
    simp only [Set.mem_preimage, Set.mem_image, Homeomorph.coe_mulLeft₀, SetLike.mem_coe,
      Ideal.mem_span_singleton]
    exact ⟨fun ⟨x, hx, hax⟩ ↦ ⟨⟨x, hx⟩, Subtype.ext hax.symm⟩,
      fun ⟨c, hc⟩ ↦ hc ▸ ⟨(c : L), c.2, rfl⟩⟩
  rw [← hpre]
  exact ((Homeomorph.mulLeft₀ (a : L) haL).isOpenMap _ Valuation.isOpen_integer).preimage
    continuous_subtype_val

/-- The ring of integers `𝒪[L]` of a nonarchimedean local field is infinite. -/
private theorem infinite_integerRing : Infinite 𝒪[L] := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  refine Infinite.of_injective (fun n : ℕ ↦ ϖ ^ n) fun m n hmn ↦ ?_
  wlog hlt : m ≤ n generalizing m n
  · exact (this n m hmn.symm (le_of_not_ge hlt)).symm
  rcases eq_or_lt_of_le hlt with rfl | hlt
  · rfl
  · have hpow : ϖ ^ (n - m) = 1 := mul_left_cancel₀ (pow_ne_zero m hϖ.ne_zero) <| by
      rw [← pow_add, Nat.add_sub_of_le hlt.le, mul_one]; exact hmn.symm
    exact (hϖ.not_isUnit ((isUnit_pow_iff (Nat.sub_ne_zero_of_lt hlt)).mp
      (hpow ▸ isUnit_one))).elim

variable {L} in
/-- **Continuity equals torsion on discrete `𝒪[L]`-modules**: a discrete `𝒪[L]`-module has
continuous `𝒪[L]`-action iff every element is killed by a nonzero element of `𝒪[L]`. -/
theorem continuousSMul_iff_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousSMul 𝒪[L] M ↔ Module.IsTorsion 𝒪[L] M := by
  refine ⟨fun _ m ↦ ?_, fun htor ↦ ⟨continuous_iff_continuousAt.mpr fun ⟨r₀, m₀⟩ ↦ ?_⟩⟩
  · let I := LinearMap.ker (LinearMap.toSpanSingleton 𝒪[L] M m)
    have : Finite (𝒪[L] ⧸ I) := finite_quotient_of_isOpen I (isOpen_annihilator_elem m)
    have hne : I ≠ ⊥ := fun hbot ↦ (infinite_integerRing L).not_finite <|
      Finite.of_equiv (𝒪[L] ⧸ I) (Submodule.quotEquivOfEqBot I hbot).toEquiv
    obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact ⟨⟨r, mem_nonZeroDivisors_of_ne_zero hr0⟩, LinearMap.mem_ker.mp hrI⟩
  · obtain ⟨⟨a, ha⟩, ham⟩ := @htor m₀
    have hIopen := isOpen_ideal_of_ne_bot L
      (mt Ideal.span_singleton_eq_bot.mp (nonZeroDivisors.ne_zero ha))
    refine (continuousAt_const (y := r₀ • m₀)).congr (Filter.eventually_of_mem
      (((hIopen.preimage (continuous_sub_right r₀)).prod
        (isOpen_discrete {m₀})).mem_nhds ⟨by simp, rfl⟩) ?_)
    rintro ⟨r, m⟩ ⟨hr, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hr
    have hdiff : (r - r₀) • m = 0 := by
      rw [show r - r₀ = a * c from hc, mul_comm, mul_smul, show a • m = 0 from ham, smul_zero]
    exact (sub_eq_zero.mp (by rw [← sub_smul, hdiff])).symm

variable {L} in
/-- Given a uniformizer `ϖ` of `𝒪[L]`, the `𝓂[L]^n`-torsion submodule of `L ⧸ 𝒪[L]` is
`𝒪[L]`-linearly isomorphic to `𝒪[L] ⧸ 𝓂[L]^n`, via `[a] ↦ [a / ϖ^n]`. -/
def quotientMaximalIdealPowEquivTorsionBySet {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃ₗ[𝒪[L]]
      Submodule.torsionBySet 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
        ((𝓂[L] ^ n : Ideal 𝒪[L]) : Set 𝒪[L]) := by
  have hpowL : (ϖ : L) ^ n ≠ 0 := pow_ne_zero n fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hmn : (𝓂[L] ^ n : Ideal 𝒪[L]) = Ideal.span {ϖ ^ n} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  let f : 𝒪[L] →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L)) :=
    { toFun := fun a ↦ Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n)
      map_add' := fun _ _ ↦ by simp only [Subring.coe_add, add_div, Submodule.Quotient.mk_add]
      map_smul' := fun _ _ ↦ by
        simp only [RingHom.id_apply, smul_eq_mul, Subring.coe_mul, mul_div_assoc]
        rw [← Submodule.Quotient.mk_smul, Algebra.smul_def]; rfl }
  have hker : LinearMap.ker f = 𝓂[L] ^ n := by
    rw [hmn]; ext a; rw [LinearMap.mem_ker, Ideal.mem_span_singleton]
    change Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((a : L) / (ϖ : L) ^ n) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
    exact ⟨fun ⟨b, hb⟩ ↦ ⟨b, Subtype.ext <| by
        simpa [mul_comm] using (div_eq_iff hpowL).mp (show (b : L) = _ from hb).symm⟩,
      fun ⟨b, hb⟩ ↦ ⟨b, by
        change (b : L) = (a : L) / (ϖ : L) ^ n; rw [hb]; push_cast
        rw [mul_div_cancel_left₀ _ hpowL]⟩⟩
  have hrange : LinearMap.range f = Submodule.torsionBySet 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L))
      ((𝓂[L] ^ n : Ideal 𝒪[L]) : Set 𝒪[L]) := by
    ext q; obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_range, Submodule.mem_torsionBySet_iff]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨a, ha⟩ ⟨r, hr⟩
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp (hmn ▸ hr)
      rw [← ha]; change (ϖ ^ n * c) • Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      exact ⟨c * a, by
        change ((c * a : 𝒪[L]) : L) = ((ϖ ^ n * c : 𝒪[L]) : L) * ((a : L) / (ϖ : L) ^ n)
        push_cast; field_simp [hpowL]⟩
    · have h0 := h ⟨ϖ ^ n, hmn ▸ Ideal.mem_span_singleton_self _⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one] at h0
      obtain ⟨a, ha⟩ := h0
      refine ⟨a, congrArg Submodule.Quotient.mk ?_⟩
      change (a : L) = ((ϖ ^ n : 𝒪[L]) : L) * x at ha
      push_cast at ha; rw [ha, mul_div_cancel_left₀ _ hpowL]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
variable {L} in
@[simp] theorem quotientMaximalIdealPowEquivTorsionBySet_mk {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
    (n : ℕ) (a : 𝒪[L]) :
    (quotientMaximalIdealPowEquivTorsionBySet hϖ n
        (Ideal.Quotient.mk (𝓂[L] ^ n : Ideal 𝒪[L]) a) : L ⧸ (1 : Submodule 𝒪[L] L)) =
      Submodule.Quotient.mk ((a : L) / (ϖ : L) ^ n) := (rfl)

/-- **Cogenerator condition for `L ⧸ 𝒪[L]`**: `Hom_𝒪[L](𝒪[L] ⧸ 𝔪, L ⧸ 𝒪[L])` has length `1` for
every maximal ideal `𝔪` of `𝒪[L]`. -/
theorem length_linearMap_quotient_maximalIdeal_eq_one :
    ∀ 𝔪 : Ideal 𝒪[L], 𝔪.IsMaximal →
      Module.length 𝒪[L] ((𝒪[L] ⧸ 𝔪) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) = 1 := by
  intro 𝔪 h𝔪; obtain rfl := IsLocalRing.eq_maximalIdeal h𝔪
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  have hpow : (𝓂[L] ^ 1 : Ideal 𝒪[L]) = 𝓂[L] := pow_one _
  have e : ((𝒪[L] ⧸ 𝓂[L]) →ₗ[𝒪[L]] (L ⧸ (1 : Submodule 𝒪[L] L))) ≃ₗ[𝒪[L]] (𝒪[L] ⧸ 𝓂[L]) :=
    (𝓂[L].quotientLinearMapEquivTorsionBySet _).trans
      ((LinearEquiv.ofEq _ _ (by rw [hpow])).symm.trans
        ((quotientMaximalIdealPowEquivTorsionBySet hϖ 1).symm.trans
          (Submodule.quotEquivOfEq _ _ hpow)))
  rw [e.length_eq, Module.length_eq_one_iff]
  exact isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal 𝒪[L]).out

/-- **Compactness of the dual of a discrete torsion `𝒪[L]`-module**: `Hom_𝒪[L](M, L ⧸ 𝒪[L])` is
a compact `𝒪[L]`-module whenever `M` is discrete and torsion. -/
theorem isCompactModule_dual_of_isTorsion {M : Type*} [AddCommGroup M] [Module 𝒪[L] M]
    [TopologicalSpace M] [DiscreteTopology M] (hM : Module.IsTorsion 𝒪[L] M) :
    IsCompactModule 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) := by
  have := continuousSMul_iff_isTorsion.mpr hM
  exact isCompactModule_of_discrete (length_linearMap_quotient_maximalIdeal_eq_one L)

/-- **The dual of a compact `𝒪[L]`-module is torsion**: every continuous `𝒪[L]`-linear functional
on a compact `𝒪[L]`-module into `L ⧸ 𝒪[L]` is killed by a nonzero element of `𝒪[L]`. -/
theorem isTorsion_dual_of_isCompactModule {N : Type*} [AddCommGroup N] [Module 𝒪[L] N]
    [TopologicalSpace N] (hN : IsCompactModule 𝒪[L] N) :
    Module.IsTorsion 𝒪[L] (ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) N) := by
  have := hN.compactSpace; exact continuousSMul_iff_isTorsion.mp inferInstance

variable {L} in
/-- **Self-duality of `𝒪[L] ⧸ 𝓂[L]^n`**: choosing a uniformizer `ϖ`, the Pontryagin dual of
`𝒪[L] ⧸ 𝓂[L]^n` with respect to `L ⧸ 𝒪[L]` is continuously `𝒪[L]`-linearly equivalent to
`𝒪[L] ⧸ 𝓂[L]^n`. -/
def dualQuotientMaximalIdealPowEquiv {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) (n : ℕ) :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) ≃L[𝒪[L]]
      (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) := by
  have hopen : IsOpen ((𝓂[L] ^ n : Ideal 𝒪[L]) : Set 𝒪[L]) := isOpen_ideal_of_ne_bot L <| by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero n hϖ.ne_zero
  have : DiscreteTopology (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    Submodule.Quotient.discreteTopology_of_isOpen _ hopen
  have : CompactSpace (𝒪[L] ⧸ (𝓂[L] ^ n : Ideal 𝒪[L])) :=
    have := finite_quotient_of_isOpen _ hopen; Finite.compactSpace
  exact ⟨(equivLinearMap 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) _).trans
      (((𝓂[L] ^ n : Ideal 𝒪[L]).quotientLinearMapEquivTorsionBySet _).trans
        (quotientMaximalIdealPowEquivTorsionBySet hϖ n).symm),
    continuous_of_discreteTopology, continuous_of_discreteTopology⟩

end SingleField

section Extension

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
/-- The scalar tower `𝒪[K] → 𝒪[L] → L` for a compatible extension of local fields. -/
instance instIsScalarTowerIntegerRing : IsScalarTower 𝒪[K] 𝒪[L] L := .of_algebraMap_eq' rfl

/-- `𝒪[L]` is the integral closure of `𝒪[K]` in `L`. -/
theorem isIntegralClosure_integerRing : IsIntegralClosure 𝒪[L] 𝒪[K] L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := by
    have := finite_of_valuativeExtension K L
    have hmem : x ∈ 𝒪[L] ↔ IsIntegral 𝒪[K] x := by
      rw [integerRing_eq_integralClosure K L, Subalgebra.mem_toSubring, mem_integralClosure_iff]
    exact ⟨fun hx ↦ ⟨⟨x, hmem.mpr hx⟩, rfl⟩, fun ⟨b, hb⟩ ↦ hmem.mp (hb ▸ b.2)⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- Scalar multiplication by `𝒪[K]` on `L ⧸ P` is continuous in the second variable. -/
instance instContinuousConstSMulQuotient (P : Submodule 𝒪[L] L) :
    ContinuousConstSMul 𝒪[K] (L ⧸ P) where
  continuous_const_smul a := by
    simpa only [← algebraMap_smul 𝒪[L] a] using
      (continuous_const_smul (algebraMap 𝒪[K] 𝒪[L] a) : Continuous fun q : L ⧸ P ↦ _)

/-- The inverse different `𝒪[L]ᵛ` is an open `𝒪[L]`-submodule of `L`. -/
theorem isOpen_traceDual_one :
    IsOpen (Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L) : Set L) := by
  have := finite_of_valuativeExtension K L
  have := isIntegralClosure_integerRing K L
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦
    ⟨(· - x) ⁻¹' ((1 : Submodule 𝒪[L] L) : Set L), fun y hy ↦ ?_,
      (isOpen_one_submodule_integerRing L).preimage (continuous_id.sub continuous_const), by simp⟩
  simpa using (Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)).add_mem
    (Submodule.one_le_traceDual_one hy) hx

/-- The quotient `L ⧸ 𝒪[L]ᵛ` carries the discrete topology. -/
instance instDiscreteTopologyQuotientTraceDual :
    DiscreteTopology (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) :=
  Submodule.Quotient.discreteTopology_of_isOpen _ (isOpen_traceDual_one K L)

variable [Algebra.IsSeparable K L]

/-- **Topological inverse-different trace comparison**: postcomposition with the trace map
`L ⧸ 𝒪[L]ᵛ → K ⧸ 𝒪[K]` gives a canonical continuous `𝒪[K]`-linear equivalence
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]ᵛ) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def traceDualPontryaginEquiv (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  choose n b y hy hsum using exists_sum_trace_mul_smul_eq 𝒪[K] K (B := 𝒪[L]) (L := L)
  let DL := L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)
  let DK := K ⧸ (1 : Submodule 𝒪[K] K)
  let e := traceDualLinearMapEquiv 𝒪[K] K 𝒪[L] L M
  let trCM : C(DL, DK) := ⟨traceDualQuotientMap 𝒪[K] K 𝒪[L] L, continuous_of_discreteTopology⟩
  let mulCM (i : Fin n) : C(DK, DL) :=
    ⟨mulByTraceDualQuotientMap 𝒪[K] K 𝒪[L] L (y i) (hy i), continuous_of_discreteTopology⟩
  let smulCM (i : Fin n) : C(M, M) := ⟨(b i • ·), continuous_const_smul (b i)⟩
  let toF : ModulePontryaginDual 𝒪[L] DL M → ModulePontryaginDual 𝒪[K] DK M := fun φ ↦
    ⟨⟨e φ.1.toLinearMap, by
      change Continuous ⇑(e φ.1.toLinearMap)
      rw [show ⇑(e φ.1.toLinearMap) = fun m ↦ trCM (φ m) from
        funext (traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L _)]
      exact trCM.continuous.comp (map_continuous φ)⟩⟩
  let invF : ModulePontryaginDual 𝒪[K] DK M → ModulePontryaginDual 𝒪[L] DL M := fun ψ ↦
    ⟨⟨e.symm ψ.1.toLinearMap, by
      change Continuous ⇑(e.symm ψ.1.toLinearMap)
      rw [show ⇑(e.symm ψ.1.toLinearMap) = fun m ↦ ∑ i, mulCM i (ψ (smulCM i m)) from
        funext (traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum _)]
      exact continuous_finsetSum Finset.univ fun i _ ↦
        (mulCM i).continuous.comp ((map_continuous ψ).comp (smulCM i).continuous)⟩⟩
  refine
    { toFun := toF, invFun := invF,
      left_inv := fun _ ↦ ext fun m ↦ LinearMap.congr_fun (e.symm_apply_apply _) m,
      right_inv := fun _ ↦ ext fun m ↦ LinearMap.congr_fun (e.apply_symm_apply _) m,
      map_add' := fun _ _ ↦ ext fun m ↦ LinearMap.congr_fun (e.map_add _ _) m,
      map_smul' := fun a _ ↦ ext fun m ↦ LinearMap.congr_fun (e.map_smul a _) m,
      continuous_toFun :=
        (isInducing_toContinuousMap (R := 𝒪[K]) (E := DK) (M := M)).continuous_iff.mpr <|
          (show ModulePontryaginDual.toContinuousMap ∘ toF = fun φ ↦ trCM.comp φ.toContinuousMap by
            ext φ m
            simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.comp_apply]
            exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L φ.1.toLinearMap m) ▸
          (ContinuousMap.continuous_postcomp trCM).comp
            (continuous_toContinuousMap (R := 𝒪[L]) (E := DL) (M := M)),
      continuous_invFun :=
        (isInducing_toContinuousMap (R := 𝒪[L]) (E := DL) (M := M)).continuous_iff.mpr <|
          (show ModulePontryaginDual.toContinuousMap ∘ invF =
              fun ψ ↦ ∑ i, (mulCM i).comp (ψ.toContinuousMap.comp (smulCM i)) by
            ext ψ m
            simp only [Function.comp_apply, toContinuousMap_apply, ContinuousMap.coe_sum,
              Finset.sum_apply, ContinuousMap.comp_apply]
            exact traceDualLinearMapEquiv_symm_apply_of_dualFamily 𝒪[K] K 𝒪[L] L b y hy hsum _ m) ▸
          continuous_finsetSum Finset.univ fun i _ ↦
            (ContinuousMap.continuous_postcomp (mulCM i)).comp
              ((ContinuousMap.continuous_precomp (smulCM i)).comp
                (continuous_toContinuousMap (R := 𝒪[K]) (E := DK) (M := M))) }
section TraceDualApply
variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
@[simp] theorem traceDualPontryaginEquiv_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) : traceDualPontryaginEquiv K L M φ m = traceDualQuotientMap 𝒪[K] K 𝒪[L] L (φ m) := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  exact traceDualLinearMapEquiv_apply 𝒪[K] K 𝒪[L] L _ m

/-- Compatibility of `traceDualPontryaginEquiv` with the `𝒪[L]`-action on `M`. -/
theorem traceDualPontryaginEquiv_smul_apply (b : 𝒪[L])
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M)
    (m : M) :
    traceDualPontryaginEquiv K L M (b • φ) m = traceDualPontryaginEquiv K L M φ (b • m) := by
  simp [traceDualPontryaginEquiv_apply, map_smul]
end TraceDualApply

/-- Compatibility of `traceDualPontryaginEquiv` with contragredient group representations. -/
theorem traceDualPontryaginEquiv_contragredient {G M : Type*} [Group G]
    [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul 𝒪[L] M]
    (ρ : ContRepresentation 𝒪[L] G M) (g : G)
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) M) :
    let ρK : ContRepresentation 𝒪[K] G M :=
      ⟨{ toFun := fun h ↦ (ρ h).restrictScalars 𝒪[K],
         map_one' := by ext; simp, map_mul' := fun _ _ ↦ by ext; simp }⟩
    traceDualPontryaginEquiv K L M
        (contragredient (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) ρ g φ) =
      contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) ρK g (traceDualPontryaginEquiv K L M φ) := by
  intro ρK; ext m; simp [traceDualPontryaginEquiv_apply, contragredient_apply, ρK]; rfl

section Uniformizer

variable {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ)
include hϖ

/-- For any uniformizer `ϖ` of `𝒪[L]`, the different ideal is generated by `ϖ ^ d(L/K)`. -/
theorem differentIdeal_eq_span_pow_uniformizer :
    differentIdeal 𝒪[K] 𝒪[L] = Ideal.span {ϖ ^ differentExponent K L} := by
  rw [differentIdeal_eq_maximalIdeal_pow K L, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- Given a uniformizer `ϖ` of `𝒪[L]`, dividing by `ϖ ^ d(L/K)` gives a continuous `𝒪[L]`-linear
equivalence `(L ⧸ 𝒪[L]) ≃L[𝒪[L]] (L ⧸ 𝒪[L]ᵛ)`. -/
def quotientEquivTraceDualQuotientOfUniformizer :
    (L ⧸ (1 : Submodule 𝒪[L] L)) ≃L[𝒪[L]]
      (L ⧸ Submodule.traceDual 𝒪[K] K (1 : Submodule 𝒪[L] L)) := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  exact ⟨quotientEquivTraceDualQuotientOfDifferentIdealEqSpan 𝒪[K] K 𝒪[L] L
      (differentIdeal_eq_span_pow_uniformizer K L hϖ),
    continuous_of_discreteTopology, continuous_of_discreteTopology⟩
@[simp] theorem quotientEquivTraceDualQuotientOfUniformizer_mk (x : L) :
    quotientEquivTraceDualQuotientOfUniformizer K L hϖ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (x / ((ϖ : L) ^ differentExponent K L)) := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
  change quotientEquivTraceDualQuotientOfDifferentIdealEqSpan 𝒪[K] K 𝒪[L] L
    (differentIdeal_eq_span_pow_uniformizer K L hϖ) (Submodule.Quotient.mk x) = _
  rw [quotientEquivTraceDualQuotientOfDifferentIdealEqSpan_mk, map_pow]; rfl

/-- **Change of coefficient ring for local-field Pontryagin duals**: choosing a uniformizer `ϖ`,
dividing by `ϖ ^ d(L/K)` and taking `Tr_{L/K}` yields
`ModulePontryaginDual 𝒪[L] (L ⧸ 𝒪[L]) M ≃L[𝒪[K]] ModulePontryaginDual 𝒪[K] (K ⧸ 𝒪[K]) M`. -/
def pontryaginDualEquivOfUniformizer (M : Type*) [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M]
    [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M] :
    ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M ≃L[𝒪[K]]
      ModulePontryaginDual 𝒪[K] (K ⧸ (1 : Submodule 𝒪[K] K)) M :=
  let e := congrCodomain (M := M) (quotientEquivTraceDualQuotientOfUniformizer K L hϖ)
  ContinuousLinearEquiv.trans
    ⟨{ toEquiv := e.toEquiv, map_add' := e.map_add,
       map_smul' := fun a φ ↦ by
         simpa [algebraMap_smul] using e.map_smul (algebraMap 𝒪[K] 𝒪[L] a) φ },
      e.continuous, e.symm.continuous⟩
    (traceDualPontryaginEquiv K L M)

section UniformizerApply
variable {M : Type*} [AddCommGroup M] [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M]
  [TopologicalSpace M] [ContinuousConstSMul 𝒪[L] M]
@[simp] theorem pontryaginDualEquivOfUniformizer_apply
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M φ m =
      traceDualQuotientMap 𝒪[K] K 𝒪[L] L
        (quotientEquivTraceDualQuotientOfUniformizer K L hϖ (φ m)) := by
  change traceDualPontryaginEquiv K L M
    (congrCodomain (M := M) (quotientEquivTraceDualQuotientOfUniformizer K L hϖ) φ) m = _
  rw [traceDualPontryaginEquiv_apply, congrCodomain_apply]

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with the `𝒪[L]`-action on `M`. -/
theorem pontryaginDualEquivOfUniformizer_smul_apply (b : 𝒪[L])
    (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) (m : M) :
    pontryaginDualEquivOfUniformizer K L hϖ M (b • φ) m =
      pontryaginDualEquivOfUniformizer K L hϖ M φ (b • m) := by
  simp [pontryaginDualEquivOfUniformizer_apply, map_smul]
end UniformizerApply

/-- Compatibility of `pontryaginDualEquivOfUniformizer` with contragredient group
representations. -/
theorem pontryaginDualEquivOfUniformizer_contragredient {G M : Type*} [Group G] [AddCommGroup M]
    [Module 𝒪[L] M] [Module 𝒪[K] M] [IsScalarTower 𝒪[K] 𝒪[L] M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul 𝒪[L] M] (ρ : ContRepresentation 𝒪[L] G M)
    (g : G) (φ : ModulePontryaginDual 𝒪[L] (L ⧸ (1 : Submodule 𝒪[L] L)) M) :
    let ρK : ContRepresentation 𝒪[K] G M :=
      ⟨{ toFun := fun h ↦ (ρ h).restrictScalars 𝒪[K],
         map_one' := by ext; simp, map_mul' := fun _ _ ↦ by ext; simp }⟩
    pontryaginDualEquivOfUniformizer K L hϖ M
        (contragredient (L ⧸ (1 : Submodule 𝒪[L] L)) ρ g φ) =
      contragredient (K ⧸ (1 : Submodule 𝒪[K] K)) ρK g
        (pontryaginDualEquivOfUniformizer K L hϖ M φ) := by
  intro ρK; ext m; simp [pontryaginDualEquivOfUniformizer_apply, contragredient_apply, ρK]; rfl

end Uniformizer

/-- **Exact criterion for the naive trace pairing**: `directTracePairing` is injective if and only
if `L / K` is unramified. -/
theorem ker_directTracePairing_eq_bot_iff_isUnramified :
    haveI := finite_of_valuativeExtension K L
    haveI := isIntegralClosure_integerRing K L
    LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) = ⊥ ↔ IsUnramified K L := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
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
  exact hϖ.not_isUnit (IsUnit.of_mul_eq_one b <| Subtype.ext <| by
    change (ϖ : L) * (b : L) = 1
    rw [show (b : L) = (ϖ : L)⁻¹ from hb, mul_inv_cancel₀ hϖL])

/-- **Explicit witness in the kernel of the naive trace pairing**: whenever `L / K` is ramified
and `ϖ` is a uniformizer of `𝒪[L]`, `[ϖ⁻¹]` lies in `ker(directTracePairing 𝒪[K] K 𝒪[L] L)`. -/
theorem mk_inv_uniformizer_mem_ker_directTracePairing (hram : ¬ IsUnramified K L)
    {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    haveI := finite_of_valuativeExtension K L
    haveI := isIntegralClosure_integerRing K L
    Submodule.Quotient.mk (p := (1 : Submodule 𝒪[L] L)) ((ϖ : L)⁻¹) ∈
      LinearMap.ker (directTracePairing 𝒪[K] K 𝒪[L] L) := by
  have := finite_of_valuativeExtension K L; have := isIntegralClosure_integerRing K L
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
  rw [show (ϖ : L) ^ differentExponent K L = (ϖ : L) * (ϖ : L) ^ (differentExponent K L - 1) by
    rw [← pow_succ', Nat.sub_add_cancel hd], inv_mul_cancel_left₀ hϖL]

end Extension

end TauCeti
