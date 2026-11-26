/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import TauCeti.MeasureTheory.Group.OrbitCutoff.Basic
public import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure
public import TauCeti.MeasureTheory.Measure.Count.Topology
public import TauCeti.MeasureTheory.Measure.Haar.Unimodular
public import TauCeti.Topology.Algebra.Group.DiscreteSubgroup

/-!
# Orbit cutoffs of proper actions and of discrete subgroups

A proper action of a group `H` on a σ-compact Hausdorff space has an orbit cutoff for every nonzero
right invariant measure on `H` that is finite on compact sets
(`MeasureTheory.hasOrbitCutoff_of_properSMul`). In particular a discrete subgroup `Γ` of a second
countable locally compact group `G`, with counting measure, acting on `G` by left multiplication has
one, and `Γ.cutoffMeasure μ` computes integrals over `Γ \ G` for a left Haar measure `μ`:
`∫_{Γ\G} ∑_{γ ∈ Γ} f (γ g) dg = ∫_G f dμ` (`Subgroup.integral_cutoffMeasure_tsum`).

The total mass of `Γ.cutoffMeasure μ` is the covolume `vol(Γ \ G)`: for any fundamental domain `s`
of the action of `Γ`, the integral over `Γ \ G` of an invariant function is its integral over `s`
(`MeasureTheory.IsOrbitCutoff.lintegral_withDensity_eq_setLIntegral`), so the cutoff measure has the
mass `MeasureTheory.covolume Γ G μ` (`MeasureTheory.cutoffMeasure_univ_eq_covolume`). If the
covolume is finite, `μ` is also right invariant
(`Subgroup.isMulRightInvariant_of_isFiniteMeasure_cutoffMeasure`), and the covolume is finite when
some compact set meets every orbit (`Subgroup.isFiniteMeasure_cutoffMeasure_of_isCompact`).

Finally, the integral over a quotient by a countable group acting diagonally on a product of a
subgroup `R ⊂ G` and `G` may be taken over either factor
(`MeasureTheory.integral_cutoff_swap`).

## References

* N. Bourbaki, *Intégration*, chapitre VII, Hermann, 1963.

The statements and proofs are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/Basic.lean`
(`New.hasCutoff_of_proper`, `New.integral_quotMeasure_tsum`,
`New.isMulRightInvariant_of_finite_covolume`, `New.isFiniteMeasure_quotMeasure_of_cocompact`) and
`src/Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean` (`New.integral_cutoff_swap`). The comparison
with fundamental domains is new.
-/

public section

open MeasureTheory Measure Set

open scoped ENNReal Pointwise

namespace MeasureTheory

/-! ### Existence of cutoffs for proper actions -/

section Proper

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X] [Group H] [MulAction H X]
  [MeasurableMul H] [MeasurableSMul₂ H X] [TopologicalSpace H] [TopologicalSpace X]

/-- A proper action of `H` on a σ-compact Hausdorff space has an orbit cutoff for every nonzero
s-finite right invariant measure `ν` on `H` that is finite on compact sets. -/
instance hasOrbitCutoff_of_properSMul {ν : Measure H} [SFinite ν] [ν.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts ν] [NeZero ν] [SigmaCompactSpace X] [T2Space X]
    [OpensMeasurableSpace X] [ProperSMul H X] : HasOrbitCutoff ν X := by
  classical
  -- Exhaust `X` by compact sets `K n` and let `t n x = ν {h | h • x ∈ K n}`: it is finite by
  -- properness and constant on orbits. The cutoff is `(t n x)⁻¹` on `K n`, for the least `n` with
  -- `t n x > 0`, and `0` off `K n`.
  let K : ℕ → Set X := compactCovering X
  let t (n : ℕ) (x : X) : ℝ≥0∞ := ν {h : H | h • x ∈ K n}
  have h_pos (x : X) : ∃ n, 0 < t n x := by
    by_contra! h_null
    have h_union : ⋃ n, {h : H | h • x ∈ K n} = univ := by
      ext h; simpa using exists_mem_compactCovering (h • x)
    have : ν univ = 0 := by
      rw [← h_union]; exact measure_iUnion_null fun n ↦ nonpos_iff_eq_zero.1 (h_null n)
    exact NeZero.ne ν (measure_univ_eq_zero.1 this)
  have h_fin (n : ℕ) (x : X) : t n x ≠ ∞ := by
    have : IsCompact {h : H | h • x ∈ K n} := by
      simpa using ProperSMul.isCompact_setOfPred_inter_nonempty (G := H)
        (isCompact_singleton (x := x)) (isCompact_compactCovering X n)
    exact this.measure_ne_top
  have h_inv (n : ℕ) (x : X) (g : H) : t n (g • x) = t n x := by
    simpa [t, mul_smul] using measure_preimage_mul_right ν g {h | h • x ∈ K n}
  have h_meas (n : ℕ) : Measurable (t n) :=
    measurable_measure_prodMk_right
      (measurable_smul (isCompact_compactCovering X n).measurableSet)
  let β (x : X) : ℝ≥0∞ := (K (Nat.find (h_pos x))).indicator (t (Nat.find (h_pos x)))⁻¹ x
  have hβ_meas : Measurable β :=
    .find (fun n ↦ (h_meas n).inv.indicator (isCompact_compactCovering X n).measurableSet)
      (fun n ↦ h_meas n measurableSet_Ioi) h_pos
  refine ⟨β, hβ_meas, fun x ↦ ?_⟩
  set n := Nat.find (h_pos x) with hn
  have hβ (h : H) :
      β (h • x) = ((fun g : H ↦ g • x) ⁻¹' K n).indicator (fun _ ↦ (t n x)⁻¹) h := by
    simp [β, indicator, h_inv, hn]
  simp only [hβ]
  rw [lintegral_indicator_const (measurable_smul_const x
    (isCompact_compactCovering X n).measurableSet)]
  exact ENNReal.inv_mul_cancel (Nat.find_spec (h_pos x)).ne' (h_fin n x)

end Proper

/-! ### Comparison with fundamental domains -/

section FundamentalDomain

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X] [Group H] [MulAction H X]
  [Countable H] [MeasurableSingletonClass H] [MeasurableConstSMul H X] {μ : Measure X}
  [SMulInvariantMeasure H X μ] {β : X → ℝ≥0∞} {s : Set X}

/-- For a countable group with counting measure, the integral over `H \ X` of an invariant
function `F ≥ 0` against an orbit cutoff is its integral over any fundamental domain. -/
theorem IsOrbitCutoff.lintegral_withDensity_eq_setLIntegral
    (hβ : IsOrbitCutoff (count : Measure H) β) (hs : IsFundamentalDomain H s μ) {F : X → ℝ≥0∞}
    (hF : Measurable F) (hF_inv : ∀ (h : H) (x : X), F (h • x) = F x) :
    ∫⁻ x, F x ∂μ.withDensity β = ∫⁻ x in s, F x ∂μ := by
  -- Split `X` into the translates of `s`; on `s` the weights `β (h • x)` sum to one.
  have h_sum (x : X) : ∑' h : H, β (h • x) = 1 := (isOrbitCutoff_count_iff.1 hβ).2 x
  have hβm := hβ.measurable
  rw [lintegral_withDensity_eq_lintegral_mul _ hβm hF, hs.lintegral_eq_tsum'',
    ← lintegral_tsum fun h ↦ by fun_prop]
  refine lintegral_congr fun x ↦ ?_
  simp only [Pi.mul_apply, hF_inv, ENNReal.tsum_mul_right, h_sum, one_mul]

/-- The total mass of the measure computing integrals over `H \ X`, for a countable group with
counting measure, is the covolume of the action. -/
theorem cutoffMeasure_univ_eq_covolume [HasOrbitCutoff (count : Measure H) X]
    [HasFundamentalDomain H X μ] :
    (count : Measure H).cutoffMeasure μ univ = covolume H X μ := by
  obtain ⟨s, hs⟩ := HasFundamentalDomain.ExistsIsFundamentalDomain (G := H) (α := X) (ν := μ)
  have := (isOrbitCutoff_orbitCutoff (count : Measure H)).lintegral_withDensity_eq_setLIntegral
    (μ := μ) hs measurable_const (F := fun _ ↦ 1) fun _ _ ↦ rfl
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at this
  rw [cutoffMeasure_def, this, hs.covolume_eq_volume]

end FundamentalDomain

/-! ### Discrete subgroups -/

namespace Subgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] {μ : Measure G} [μ.IsHaarMeasure]

/-- **Unfolding over a discrete subgroup** (Weil's formula): for `f` integrable for a left Haar
measure `μ`, `g ↦ ∑ γ, f (γ g)` is integrable over `Γ \ G` and its integral is `∫ f dμ`. -/
theorem integral_cutoffMeasure_tsum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : G → E} (hf : Integrable f μ) :
    Integrable (fun g ↦ ∑' γ : Γ, f (γ * g)) (Γ.cutoffMeasure μ) ∧
      ∫ g, ∑' γ : Γ, f (γ * g) ∂Γ.cutoffMeasure μ = ∫ g, f g ∂μ := by
  have : Countable Γ := countable_of_Lindelof_of_discrete
  -- Unfold along `(g, γ) ↦ γ g`; on almost every orbit `γ ↦ f (γ g)` is integrable for counting
  -- measure, and then its integral is its sum.
  have h_int : Integrable (fun p : G × Γ ↦ f (p.2 * p.1)) ((Γ.cutoffMeasure μ).prod count) :=
    (measurePreserving_cutoffMeasure (ν := (count : Measure Γ))).integrable_comp_of_integrable hf
  have h_ae : (fun g ↦ ∫ γ : Γ, f (γ * g) ∂count) =ᵐ[Γ.cutoffMeasure μ]
      fun g ↦ ∑' γ : Γ, f (γ * g) :=
    integral_count_ae_eq_tsum_of_integrable_prod (k := fun (γ : Γ) g ↦ f (γ * g)) h_int
  obtain ⟨h₁, h₂⟩ := integral_cutoffMeasure_integral (ν := (count : Measure Γ)) (μ := μ) hf
  exact ⟨h₁.congr h_ae, (integral_congr_ae h_ae).symm.trans h₂⟩

/-- The measure computing integrals over `Γ \ G` is not zero. -/
instance : NeZero (Γ.cutoffMeasure μ) :=
  ⟨fun h_zero ↦ by
    have h_map : ((Γ.cutoffMeasure μ).prod count).map (fun p : G × Γ ↦ p.2 • p.1) = μ :=
      measurePreserving_cutoffMeasure.map_eq
    simp only [h_zero, zero_prod, Measure.map_zero] at h_map
    exact NeZero.ne μ h_map.symm⟩

/-- **A group with a lattice is unimodular**: if `Γ` is discrete and `Γ \ G` has finite volume for
the left Haar measure `μ`, then `μ` is also right invariant. -/
theorem isMulRightInvariant_of_isFiniteMeasure_cutoffMeasure
    [IsFiniteMeasure (Γ.cutoffMeasure μ)] : μ.IsMulRightInvariant := by
  -- Right translation by `g` scales `μ` by the modular character and commutes with the action of
  -- `Γ`, so `Γ \ G` has the same volume for `μ` and for the scaled measure.
  refine ⟨fun g ↦ ?_⟩
  have h_mod : μ.map (· * g) = modularCharacterFun g • μ :=
    map_right_mul_eq_modularCharacterFun_smul μ g
  have h_vol : ∫⁻ _, 1 ∂Γ.cutoffMeasure (modularCharacterFun g • μ) =
      ∫⁻ _, 1 ∂Γ.cutoffMeasure μ :=
    (identDistrib_cutoffMeasure_comp (.id (count : Measure Γ)) ⟨measurable_mul_const g, h_mod⟩
      (fun γ x ↦ smul_mul_assoc γ x g) measurable_const fun _ _ ↦ rfl).symm.lintegral_eq
  have h_scale : (modularCharacterFun g : ℝ≥0∞) * Γ.cutoffMeasure μ univ =
      Γ.cutoffMeasure μ univ := by
    rw [lintegral_one, lintegral_one, Subgroup.cutoffMeasure, Subgroup.cutoffMeasure,
      cutoffMeasure_def, cutoffMeasure_def, ← coe_nnreal_smul, withDensity_smul_measure,
      smul_apply, smul_eq_mul] at h_vol
    rwa [Subgroup.cutoffMeasure, cutoffMeasure_def]
  have h_one : modularCharacterFun g = 1 := by
    rw [← ENNReal.coe_eq_one]
    exact (ENNReal.mul_eq_right (measure_univ_ne_zero.2 (NeZero.ne _)) (measure_ne_top _ _)).1
      h_scale
  rw [h_mod, h_one, one_smul]

/-- **A cocompact discrete subgroup has finite covolume**: if `Γ C = G` for a compact set `C`, the
measure computing integrals over `Γ \ G` is finite. -/
theorem isFiniteMeasure_cutoffMeasure_of_isCompact {C : Set G} (hC : IsCompact C)
    (hΓC : (Γ : Set G) * C = univ) : IsFiniteMeasure (Γ.cutoffMeasure μ) := by
  -- The number of `γ` with `γ x ∈ C` is at least one; by unfolding its integral over `Γ \ G` is
  -- `μ C < ∞`.
  set σ : Measure G := Γ.cutoffMeasure μ
  let E : Set (G × Γ) := (fun p : G × Γ ↦ p.2 • p.1) ⁻¹' C
  have h_one_le (x : G) : 1 ≤ count (Prod.mk x ⁻¹' E) := by
    obtain ⟨γ, hγ, c, hc, rfl⟩ : x ∈ (Γ : Set G) * C := hΓC ▸ mem_univ _
    have h_mem : (⟨γ⁻¹, Γ.inv_mem hγ⟩ : Γ) ∈ Prod.mk (γ * c) ⁻¹' E := by
      simpa [E, Subgroup.smul_def] using hc
    exact (le_tsum (fun _ ↦ 1) (⟨_, h_mem⟩ : Prod.mk (γ * c) ⁻¹' E)).trans le_count_apply
  constructor
  calc σ univ = ∫⁻ _, 1 ∂σ := lintegral_one.symm
    _ ≤ ∫⁻ x, count (Prod.mk x ⁻¹' E) ∂σ := lintegral_mono h_one_le
    _ = σ.prod count E := (prod_apply (hC.measurableSet.preimage (by fun_prop))).symm
    _ ≤ μ C := measurePreserving_cutoffMeasure.measure_preimage_le C
    _ < ∞ := hC.measure_lt_top

end Subgroup

/-! ### Moving the quotient from one factor to the other -/

/-- **Moving the quotient.** Let `R` be a subgroup of `G` with left invariant measures `ν` on `R`
and `μ` on `G`, and let `i` be a homomorphism from a countable group `Λ` to `R`. Let `β` be a
measurable weight on `G` whose `Λ`-translates sum to one. If `F` from `R × G` to a real normed
space is measurable, invariant under the diagonal action of `Λ`, and `β(s) F(s, x)` is
`ν × μ`-integrable, then
`∫_G β(x) ∫_R F(s, x) dν(s) dμ(x) = ∫_R β(s) ∫_G F(s, x) dμ(x) dν(s)`. -/
theorem integral_cutoff_swap {G Λ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [Group Λ]
    [Countable Λ] {R : Subgroup G} [MeasurableMul R] (μ : Measure G) [SFinite μ]
    [μ.IsMulLeftInvariant]
    (ν : Measure R) [SFinite ν] [ν.IsMulLeftInvariant] (i : Λ →* R) {β : G → ℝ≥0∞}
    (hβ : Measurable β) (hβ_one : ∀ x : G, ∑' l : Λ, β (i l * x) = 1) {F : R × G → E}
    (hF : Measurable F) (hF_inv : ∀ (l : Λ) (s : R) (x : G), F (i l * s, i l * x) = F (s, x))
    (h_int : Integrable (fun p : R × G ↦ (β p.1).toReal • F p) (ν.prod μ)) :
    ∫ x, (β x).toReal • ∫ s, F (s, x) ∂ν ∂μ = ∫ s, (β s).toReal • ∫ x, F (s, x) ∂μ ∂ν := by
  -- Both `β s` and `β x` are cutoffs for the diagonal action of `Λ` on `R × G`, and the integral of
  -- an invariant function does not depend on the cutoff.
  let : MeasurableSpace Λ := ⊤
  let : MulAction Λ (R × G) := .compHom (R × G) i
  have h_smul (l : Λ) (p : R × G) : l • p = (i l * p.1, i l * p.2) := rfl
  have : MeasurableSMul₂ Λ (R × G) :=
    ⟨measurable_from_prod_countable_right fun l ↦
      (measurable_fst.const_mul (i l)).prodMk (measurable_snd.const_mul (i l : G))⟩
  have : SMulInvariantMeasure Λ (R × G) (ν.prod μ) :=
    ⟨fun l T hT ↦ ((measurePreserving_mul_left ν (i l)).prod
      (measurePreserving_mul_left μ (i l : G))).measure_preimage hT.nullMeasurableSet⟩
  have h_fst : IsOrbitCutoff (count : Measure Λ) fun p : R × G ↦ β p.1 :=
    isOrbitCutoff_count_iff.2 ⟨by fun_prop, fun p ↦ by simpa [h_smul] using hβ_one p.1⟩
  have h_snd : IsOrbitCutoff (count : Measure Λ) fun p : R × G ↦ β p.2 :=
    isOrbitCutoff_count_iff.2 ⟨by fun_prop, fun p ↦ by simpa [h_smul] using hβ_one p.2⟩
  have h_inv (l : Λ) (p : R × G) : F (l • p) = F p := hF_inv l p.1 p.2
  have h_int_snd : Integrable (fun p : R × G ↦ (β p.2).toReal • F p) (ν.prod μ) := by
    rwa [← h_snd.integrable_cutoffMeasure_iff hF h_inv, h_fst.integrable_cutoffMeasure_iff hF h_inv]
  calc ∫ x, (β x).toReal • ∫ s, F (s, x) ∂ν ∂μ
      = ∫ p : R × G, (β p.2).toReal • F p ∂ν.prod μ := by
        simp only [integral_prod_symm _ h_int_snd, integral_smul]
    _ = ∫ p : R × G, (β p.1).toReal • F p ∂ν.prod μ := by
        rw [← h_snd.integral_cutoffMeasure hF h_inv, h_fst.integral_cutoffMeasure hF h_inv]
    _ = ∫ s, (β s).toReal • ∫ x, F (s, x) ∂μ ∂ν := by
        simp only [integral_prod _ h_int, integral_smul]

end MeasureTheory
