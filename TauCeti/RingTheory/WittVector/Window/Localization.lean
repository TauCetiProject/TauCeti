/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Adic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Plus
public import TauCeti.RingTheory.WittVector.Window.Subring
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.Topology.Algebra.UniformRing

/-!
# The rational localisation of `𝕎 O` at a window is the interval ring `B^I`

Let `O` be the ring of integers of a valuation `v : Valuation K ℝ≥0` on a field `K`, perfect of
characteristic `p`, and let `ϖ ∈ O` be a pseudouniformiser, `0 < v(ϖ) < 1`. Give `𝕎 O` its
`(p, [ϖ])`-adic topology. For nonnegative rationals `q = a / b` and `q' = a' / b'` in lowest
terms, the window `{q ≤ κ ≤ q'}` of the Fargues–Fontaine curve is cut out by the inequalities
`v([ϖ]) ^ b ≤ v(p) ^ a` and `v(p) ^ a' ≤ v([ϖ]) ^ b'`. Over the denominator `s` below, these are
the conditions `v(t) ≤ v(s)` for the numerators `t ∈ T`:

```text
T = {[ϖ] ^ (b + b'), p ^ (a + a')},      s = p ^ a [ϖ] ^ b'
```

(`TauCeti.WittVector.windowNumerators`, `TauCeti.WittVector.windowDenominator`), whose fractions
are `[ϖ] ^ b / p ^ a` and `p ^ a' / [ϖ] ^ b'`. Wedhorn's topological localisation `𝕎 O(T/s)` puts
on `𝕎 O[1/s]` the topology with ring of definition
`D = 𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']` (`TauCeti.WittVector.windowSubring`) and ideal of
definition `(p, [ϖ]) D`.

When `q ≠ 0`, the ring `𝕎 O[1/s]` is the localisation of `𝕎 O` away from `p [ϖ]`, which also
carries the interval norm `λ_I = max(λ_{ρ₁}, λ_{ρ₂})`
(`TauCeti.WittVector.IntervalLocalization`). For the radii of the window,
`ρ₁ = v(ϖ) ^ (1 / q)` and `ρ₂ = v(ϖ) ^ (1 / q')`, the two topologies agree. Consequently the
completion `𝕎 O⟨T/s⟩` is the interval ring `B^I`, as topological rings and compatibly with the
maps from `𝕎 O`. With plus ring `A⁺ = 𝕎 O`, this isomorphism carries the plus ring `A_U⁺` of the
rational localisation onto `B^{I,+}`, so it is an isomorphism of Huber pairs.

## Proof outline

The localisation topology is at least as fine as the norm topology by the universal property of
`𝕎 O(T/s)`: the map `𝕎 O → 𝕎 O[1/s]` is continuous for the norm, because the Gauss valuations
are continuous for the `(p, [ϖ])`-adic topology, and the two fractions are power-bounded for the
norm, because `D` is bounded. Conversely the `n`-th basic neighbourhood `(p, [ϖ]) ^ n D` of the
localisation topology contains `[ϖ] ^ n D`, the image of the norm-open subring `D` under
multiplication by the unit `[ϖ] ^ n`.

## Main definitions

* `TauCeti.WittVector.windowNumerators`, `TauCeti.WittVector.windowDenominator` : the
  numerators `T` and denominator `s` attached to the window.
* `TauCeti.WittVector.completionLocRingEquivIntervalRing` : the ring isomorphism
  `𝕎 O⟨T/s⟩ ≃+* B^I`.

## Main results

* `TauCeti.WittVector.isLocalization_away_windowDenominator` : for `q ≠ 0`, a localisation away
  from `p [ϖ]` is a localisation away from `s`.
* `TauCeti.WittVector.divBy_teichmuller_pow_windowDenominator` and
  `TauCeti.WittVector.divBy_natCast_pow_windowDenominator` : the fractions of the presentation are
  `[ϖ] ^ b / p ^ a` and `p ^ a' / [ϖ] ^ b'`.
* `TauCeti.WittVector.locSubring_windowNumerators` : the ring of definition `𝕎 O[T/s]` of the
  presentation is the window subring; `TauCeti.WittVector.adjoin_top_windowNumerators` is the same
  for the ring `A⁺[T/s]` with `A⁺ = 𝕎 O`.
* `TauCeti.WittVector.isOpen_span_windowNumerators` and
  `TauCeti.WittVector.hasDenominatorPower_windowNumerators` : the numerators span an open ideal, so
  the presentation satisfies the standing hypothesis of the localisation topology, for every pair
  of definition.
* `TauCeti.WittVector.locTopology_windowNumerators` : the localisation topology of the window is
  the interval-norm topology.
* `TauCeti.WittVector.locUniformSpace_windowNumerators` : the same for the uniformities.
* `TauCeti.WittVector.continuous_completionLocRingEquivIntervalRing` and its `symm` counterpart :
  the isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` is a homeomorphism.
* `TauCeti.WittVector.completionLocRingEquivIntervalRing_coe` and
  `TauCeti.WittVector.completionLocRingEquivIntervalRing_toCompletionLoc` : it is the identity on
  `𝕎 O[1/(p [ϖ])]`, hence compatible with the maps from `𝕎 O`.
* `TauCeti.WittVector.map_completedPlusSubring_windowNumerators` : it carries the plus ring `A_U⁺`
  of the window, for `A⁺ = 𝕎 O`, onto `B^{I,+}`.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the interval rings `B^I` and the windows.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition and
  Definition 5.51, and §8.1 for the plus ring of a rational localisation.
-/

public section

open scoped NNReal Topology

namespace TauCeti.WittVector

open _root_.WittVector TauCeti.Huber TauCeti.Localization

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] {ϖ : O} {q q' : ℚ≥0}

local notation "𝕎" => _root_.WittVector p

/-! ### The presentation of a window -/

section Presentation

variable (p ϖ) in
/-- **The numerators `{[ϖ] ^ (b + b'), p ^ (a + a')}` of the window `{q ≤ κ ≤ q'}`**, for
`q = a / b` and `q' = a' / b'` in lowest terms. Over `windowDenominator p ϖ q q' = p ^ a [ϖ] ^ b'`
they give the fractions `[ϖ] ^ b / p ^ a` and `p ^ a' / [ϖ] ^ b'`. -/
noncomputable def windowNumerators (q q' : ℚ≥0) : Finset (𝕎 O) :=
  open scoped Classical in {teichmuller p ϖ ^ (q.den + q'.den), (p : 𝕎 O) ^ (q.num + q'.num)}

/-- The numerators of a window are `[ϖ] ^ (b + b')` and `p ^ (a + a')`. -/
@[simp]
theorem mem_windowNumerators_iff {t : 𝕎 O} :
    t ∈ windowNumerators p ϖ q q' ↔
      t = teichmuller p ϖ ^ (q.den + q'.den) ∨ t = (p : 𝕎 O) ^ (q.num + q'.num) := by
  simp [windowNumerators]

variable (p ϖ) in
/-- **The denominator `p ^ a [ϖ] ^ b'` of the window `{q ≤ κ ≤ q'}`**, for `q = a / b` and
`q' = a' / b'` in lowest terms. -/
noncomputable def windowDenominator (q q' : ℚ≥0) : 𝕎 O :=
  (p : 𝕎 O) ^ q.num * teichmuller p ϖ ^ q'.den

/-- The denominator of a window is `p ^ a [ϖ] ^ b'`. -/
theorem windowDenominator_def :
    windowDenominator p ϖ q q' = (p : 𝕎 O) ^ q.num * teichmuller p ϖ ^ q'.den :=
  (rfl)

variable {B : Type*} [CommRing B] [Algebra (_root_.WittVector p O) B]
  [IsLocalization.Away ((p : _root_.WittVector p O) * teichmuller p ϖ) B]

variable (B) in
/-- **A localisation away from `p [ϖ]` is a localisation away from `p ^ a [ϖ] ^ b'`**, if
`q = a / b ≠ 0`: the two elements have the same radical, since `a ≥ 1` and `b' ≥ 1`. -/
theorem isLocalization_away_windowDenominator (hq : q ≠ 0) :
    IsLocalization.Away (windowDenominator p ϖ q q') B := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_add_one.mpr (NNRat.num_pos.mpr (pos_iff_ne_zero.mpr hq))
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_one.mpr q'.den_pos
  -- `p ^ a [ϖ] ^ b'` is `p [ϖ]` times `p ^ (a - 1) [ϖ] ^ (b' - 1)`, a unit of `B`
  have hunit : IsUnit (algebraMap (𝕎 O) B ((p : 𝕎 O) ^ a * teichmuller p ϖ ^ b)) := by
    rw [map_mul, map_pow, map_pow]
    exact ((IsLocalization.Away.isUnit_of_dvd ((p : 𝕎 O) * teichmuller p ϖ)
      (dvd_mul_right _ _)).pow _).mul
      ((IsLocalization.Away.isUnit_of_dvd ((p : 𝕎 O) * teichmuller p ϖ)
        (dvd_mul_left _ _)).pow _)
  convert IsLocalization.Away.mul_of_isUnit ((p : 𝕎 O) * teichmuller p ϖ) _ hunit using 1
  rw [windowDenominator_def, ha, hb]
  ring

variable [IsLocalization.Away (windowDenominator p ϖ q q') B]

/-- Over the denominator `p ^ a [ϖ] ^ b'`, the numerator `[ϖ] ^ (b + b')` gives the fraction
`[ϖ] ^ b / p ^ a`. -/
@[simp]
theorem divBy_teichmuller_pow_windowDenominator :
    (divBy (teichmuller p ϖ ^ (q.den + q'.den)) (windowDenominator p ϖ q q') : B) =
      radiusLowerFrac p ϖ B q := by
  -- both sides are determined by their product with the unit `p ^ a [ϖ] ^ b'`
  refine (IsLocalization.Away.algebraMap_isUnit (S := B)
    (windowDenominator p ϖ q q')).mul_left_cancel ?_
  rw [algebraMap_mul_divBy, windowDenominator_def, pow_add, map_mul, map_mul]
  linear_combination (-algebraMap (𝕎 O) B (teichmuller p ϖ ^ q'.den)) *
    radiusLowerFrac_mul_algebraMap (p := p) (ϖ := ϖ) (B := B) q

/-- Over the denominator `p ^ a [ϖ] ^ b'`, the numerator `p ^ (a + a')` gives the fraction
`p ^ a' / [ϖ] ^ b'`. -/
@[simp]
theorem divBy_natCast_pow_windowDenominator :
    (divBy ((p : 𝕎 O) ^ (q.num + q'.num)) (windowDenominator p ϖ q q') : B) =
      radiusUpperFrac p ϖ B q' := by
  refine (IsLocalization.Away.algebraMap_isUnit (S := B)
    (windowDenominator p ϖ q q')).mul_left_cancel ?_
  rw [algebraMap_mul_divBy, windowDenominator_def, pow_add, map_mul, map_mul]
  linear_combination (-algebraMap (𝕎 O) B ((p : 𝕎 O) ^ q.num)) *
    radiusUpperFrac_mul_algebraMap (p := p) (ϖ := ϖ) (B := B) q'

/-- **The ring of definition of the window presentation is the window subring**: for a pair of
definition with ring of definition all of `𝕎 O`, the subring `𝕎 O[T/s]` generated by the fractions
of the presentation is `𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']`. -/
theorem locSubring_windowNumerators [TopologicalSpace (𝕎 O)] (P : PairOfDefinition (𝕎 O))
    (hP : P.ringOfDefinition = ⊤) :
    P.locSubring (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') B =
      windowSubring p ϖ B q q' := by
  refine le_antisymm ((P.locSubring_le_iff _ _ _).mpr ⟨fun a _ ↦ algebraMap_mem_windowSubring a,
    fun t ht ↦ ?_⟩) (windowSubring_le_iff.mpr ⟨fun a ↦ P.algebraMap_mem_locSubring
      (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') B (hP ▸ Subring.mem_top a), ?_, ?_⟩)
  · rcases mem_windowNumerators_iff.mp ht with rfl | rfl
    · rw [divBy_teichmuller_pow_windowDenominator]
      exact radiusLowerFrac_mem_windowSubring
    · rw [divBy_natCast_pow_windowDenominator]
      exact radiusUpperFrac_mem_windowSubring
  · rw [← divBy_teichmuller_pow_windowDenominator (q' := q')]
    exact P.divBy_mem_locSubring _ (windowDenominator p ϖ q q') _
      (mem_windowNumerators_iff.mpr (.inl rfl))
  · rw [← divBy_natCast_pow_windowDenominator (q := q)]
    exact P.divBy_mem_locSubring _ (windowDenominator p ϖ q q') _
      (mem_windowNumerators_iff.mpr (.inr rfl))

/-- **The ring `A⁺[T/s]` of the window presentation is the window subring**, for the plus ring
`A⁺ = 𝕎 O`: the subring generated over `𝕎 O` by the fractions of the presentation is
`𝕎 O[[ϖ] ^ b / p ^ a, p ^ a' / [ϖ] ^ b']`. This is the ring whose integral closure the plus ring
`A_U⁺` of the rational localisation completes
(`TauCeti.Huber.PairOfDefinition.completedPlusSubring`). -/
theorem adjoin_top_windowNumerators :
    (Algebra.adjoin (⊤ : Subring (𝕎 O)) (Set.range fun t : windowNumerators p ϖ q q' ↦
      (divBy (t : 𝕎 O) (windowDenominator p ϖ q q') : B))).toSubring =
      windowSubring p ϖ B q q' := by
  rw [windowSubring_def, Algebra.adjoin_eq_ring_closure, Algebra.adjoin_eq_ring_closure]
  congr 2
  · exact Set.ext fun x ↦ ⟨fun ⟨a, ha⟩ ↦ ⟨a, ha⟩, fun ⟨a, ha⟩ ↦ ⟨⟨a, Subring.mem_top a⟩, ha⟩⟩
  · refine Set.ext fun x ↦ ⟨?_, ?_⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      rcases mem_windowNumerators_iff.mp ht with rfl | rfl
      · exact .inl (divBy_teichmuller_pow_windowDenominator (q' := q'))
      · exact .inr (divBy_natCast_pow_windowDenominator (q := q))
    · rintro (rfl | rfl)
      · exact ⟨⟨_, mem_windowNumerators_iff.mpr (.inl rfl)⟩,
          divBy_teichmuller_pow_windowDenominator (q' := q')⟩
      · exact ⟨⟨_, mem_windowNumerators_iff.mpr (.inr rfl)⟩,
          divBy_natCast_pow_windowDenominator (q := q)⟩

/-- **The numerators of a window span an open ideal** for the `(p, [ϖ])`-adic topology: its
radical contains `p` and `[ϖ]`. -/
theorem isOpen_span_windowNumerators [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) :
    IsOpen (Ideal.span (windowNumerators p ϖ q q' : Set (𝕎 O)) : Set (𝕎 O)) := by
  have hfg : (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}).FG := Submodule.fg_span (by simp)
  have hmem {t : 𝕎 O} (ht : t ∈ windowNumerators p ϖ q q') :
      t ∈ Ideal.span (windowNumerators p ϖ q q' : Set (𝕎 O)) :=
    Ideal.subset_span ht
  rw [(PairOfDefinition.adic _ hI hfg).isOpen_iff_le_radical,
    PairOfDefinition.adic_extendedIdealOfDefinition, Ideal.span_le, Set.insert_subset_iff,
    Set.singleton_subset_iff]
  exact ⟨Ideal.mem_radical_of_pow_mem (Ideal.le_radical
      (hmem (mem_windowNumerators_iff.mpr (.inr rfl)))),
    Ideal.mem_radical_of_pow_mem (Ideal.le_radical
      (hmem (mem_windowNumerators_iff.mpr (.inl rfl))))⟩

omit [IsLocalization.Away ((p : _root_.WittVector p O) * teichmuller p ϖ) B] in
/-- **The window presentation satisfies the standing hypothesis** of the localisation topology,
for every pair of definition of the `(p, [ϖ])`-adic topology: its numerators span an open ideal
(`isOpen_span_windowNumerators`). -/
theorem hasDenominatorPower_windowNumerators [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (P : PairOfDefinition (𝕎 O)) :
    P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') B :=
  P.hasDenominatorPower_of_isOpen_span _ _ _ (isOpen_span_windowNumerators hI)

end Presentation

/-! ### The localisation topology of a window is the interval-norm topology -/

section Interval

variable {K : Type*} [Field K] [Algebra O K] {v : Valuation K ℝ≥0} [CharP O p] [PerfectRing O p]
  (hv : v.Integers O) (hϖ : ϖ ≠ 0) (hϖ' : v (algebraMap O K ϖ) < 1) {ρ₁ ρ₂ : ℝ≥0}
  (hρ₁ : ρ₁ ∈ Set.Ioo 0 1) (hρ₂ : ρ₂ ∈ Set.Ioo 0 1)

local notation "L" => IntervalLocalization p hv hϖ hϖ' hρ₁ hρ₂

/-- The `n`-th basic neighbourhood `(p, [ϖ]) ^ n D` of the localisation topology of the window is a
neighbourhood of `0` for the interval norm: it contains `[ϖ] ^ n D`, and `D` is open. -/
private theorem locIdealImage_mem_nhds [TopologicalSpace (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (h₁ : ρ₁ ^ q.num ≤ v (algebraMap O K ϖ) ^ q.den)
    (h₂ : v (algebraMap O K ϖ) ^ q'.den ≤ ρ₂ ^ q'.num) (hq' : q' ≠ 0) (n : ℕ) :
    ((PairOfDefinition.adic _ hI (Submodule.fg_span (Set.toFinite _))).locIdealImage
      (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L n : Set L) ∈ 𝓝 0 := by
  set P := PairOfDefinition.adic _ hI (Submodule.fg_span (Set.toFinite _))
  have hP : P.ringOfDefinition = ⊤ := PairOfDefinition.adic_ringOfDefinition _ _ _
  have hD := locSubring_windowNumerators (ϖ := ϖ) (q := q) (q' := q') (B := L) P hP
  set u := (IntervalLocalization.isUnit_algebraMap_teichmuller p hv hϖ hϖ' hρ₁ hρ₂).unit
  -- the elements `x` with `[ϖ] ^ -n x ∈ D` form an open neighbourhood of `0`
  have hopen : IsOpen {x : L | ((u⁻¹ ^ n : Lˣ) : L) * x ∈ windowSubring p ϖ L q q'} :=
    (isOpen_windowSubring hv hϖ hϖ' hρ₁ hρ₂ h₁ h₂ hq').preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hopen.mem_nhds (by simp)) fun x hx ↦ ?_
  -- and each of them is `[ϖ] ^ n` times an element of `D`, with `[ϖ]` in the ideal of definition
  have hϖ₀ : teichmuller p ϖ ∈ P.ringOfDefinition := hP ▸ Subring.mem_top _
  have hϖI : (⟨teichmuller p ϖ, hϖ₀⟩ : P.ringOfDefinition) ^ n ∈ P.idealOfDefinition ^ n :=
    Ideal.pow_mem_pow ((PairOfDefinition.mem_adic_idealOfDefinition _ _ _).mpr
      (Ideal.subset_span (by simp))) n
  rw [SetLike.mem_coe, PairOfDefinition.mem_locIdealImage_iff]
  refine ⟨P.toLocSubring _ _ L _ * ⟨_, hD ▸ hx⟩,
    Ideal.mul_mem_right _ _ (P.toLocSubring_mem_locIdeal_pow _ _ L hϖI), ?_⟩
  have hu : (u : L) = algebraMap (𝕎 O) L (teichmuller p ϖ) := IsUnit.unit_spec _
  simp only [MulMemClass.coe_mul, PairOfDefinition.toLocSubring_apply, SubmonoidClass.coe_pow,
    map_pow, ← hu, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_mul, inv_pow]

/-- **The localisation topology of a window is the interval-norm topology.** Let `𝕎 O` carry the
`(p, [ϖ])`-adic topology, with any pair of definition `P`, and let `q = a / b` and `q' = a' / b'`
in lowest terms with radii `ρ₁ ^ a = v(ϖ) ^ b`, `ρ₂ ^ a' = v(ϖ) ^ b'` and `ρ₁ ≤ ρ₂`. Then on
`𝕎 O[1/(p [ϖ])]`, which is also a localisation away from `p ^ a [ϖ] ^ b'`
(`isLocalization_away_windowDenominator`, as `q ≠ 0`), Wedhorn's localisation topology for the
numerators `{[ϖ] ^ (b + b'), p ^ (a + a')}` and denominator `p ^ a [ϖ] ^ b'` is the topology of the
interval norm `λ_I = max(λ_{ρ₁}, λ_{ρ₂})`. -/
theorem locTopology_windowNumerators [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (P : PairOfDefinition (𝕎 O))
    [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    P.locTopology (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden =
      (inferInstance : TopologicalSpace L) := by
  have hq' : q' ≠ 0 := by
    rintro rfl
    simp only [NNRat.num_zero, pow_zero, NNRat.den_zero, pow_one] at h₂
    exact hϖ'.ne' h₂
  -- replace `P` by the `(p, [ϖ])`-adic pair of definition, whose ring of definition is `𝕎 O`
  set P₀ := PairOfDefinition.adic _ hI (Submodule.fg_span (Set.toFinite _))
  have hden₀ := hasDenominatorPower_windowNumerators (q := q) (q' := q') (B := L) hI P₀
  rw [PairOfDefinition.locTopology_congr_pairOfDefinition P P₀ _ _ _ hden hden₀]
  have hD := locSubring_windowNumerators (ϖ := ϖ) (q := q) (q' := q') (B := L) P₀
    (PairOfDefinition.adic_ringOfDefinition _ _ _)
  -- the localisation topology is finer, by its universal property: `𝕎 O → L` is continuous and
  -- the fractions lie in the bounded subring `D`
  have hle : P₀.locTopology (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden₀ ≤
      (inferInstance : TopologicalSpace L) := by
    refine continuous_id_iff_le.mp ?_
    rw [← RingHom.coe_id]
    refine P₀.continuous_of_continuous_algebraMap_of_isPowerBounded _ _ L hden₀ (RingHom.id L)
      (continuous_algebraMap_intervalLocalization p hv hϖ hϖ' hρ₁ hρ₂ hI) fun t ht ↦ ?_
    refine (isBounded_windowSubring hv hϖ hϖ' hρ₁ hρ₂ h₁.ge (h₁ ▸ pow_le_pow_left₀ zero_le h₁₂ _)
      (h₂ ▸ pow_le_pow_left₀ zero_le h₁₂ _) h₂.le).isPowerBounded_of_mem ?_
    exact hD ▸ P₀.divBy_mem_locSubring _ _ L ht
  -- conversely every basic neighbourhood of the localisation topology is a norm neighbourhood
  refine IsTopologicalAddGroup.ext
    (@IsTopologicalRing.isTopologicalAddGroup L _ (P₀.locTopology _ _ L hden₀)
      (P₀.isTopologicalRing_locTopology _ _ L hden₀)) inferInstance
    (le_antisymm (nhds_mono hle) ?_)
  exact (P₀.hasBasis_nhds_zero_locTopology _ _ L hden₀).ge_iff.mpr fun n _ ↦
    locIdealImage_mem_nhds hv hϖ hϖ' hρ₁ hρ₂ hI h₁.le h₂.ge hq' n

/-- **The localisation uniformity of a window is the interval-norm uniformity**, under the
hypotheses of `locTopology_windowNumerators`: both are uniform additive group structures, and
their topologies agree. -/
theorem locUniformSpace_windowNumerators [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (P : PairOfDefinition (𝕎 O))
    [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden =
      (inferInstance : UniformSpace L) :=
  (P.isUniformAddGroup_locUniformSpace _ _ L hden).ext inferInstance <| by
    rw [P.locUniformSpace_toTopologicalSpace,
      locTopology_windowNumerators hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂]

/-- The identity of `𝕎 O[1/(p [ϖ])]` is continuous from the localisation topology of the window
to the interval-norm topology, and back. -/
private theorem continuous_id_locUniformSpace [TopologicalSpace (𝕎 O)] [IsTopologicalRing (𝕎 O)]
    (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ})) (P : PairOfDefinition (𝕎 O))
    [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    @Continuous L L
        (P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L
          hden).toTopologicalSpace inferInstance id ∧
      @Continuous L L inferInstance
        (P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L
          hden).toTopologicalSpace id := by
  rw [locUniformSpace_windowNumerators hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂]
  exact ⟨continuous_id, continuous_id⟩

/-- **The completed coordinate ring of a window is the interval ring**: under the hypotheses of
`locTopology_windowNumerators`, the completion `𝕎 O⟨T/s⟩` of the localisation of `𝕎 O` at the
window presentation is isomorphic to `B^I`. The isomorphism is the identity of
`𝕎 O[1/(p [ϖ])]` on the dense subrings; it is a homeomorphism
(`continuous_completionLocRingEquivIntervalRing` and its `symm` counterpart) and is compatible with
the maps from `𝕎 O` (`completionLocRingEquivIntervalRing_toCompletionLoc`). -/
noncomputable def completionLocRingEquivIntervalRing [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    UniformSpace.Completion L ≃+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ :=
  @UniformSpace.Completion.mapRingEquiv L _ (P.locUniformSpace _ _ L hden)
    (P.isTopologicalRing_locUniformSpace _ _ L hden)
    (P.isUniformAddGroup_locUniformSpace _ _ L hden) L _ _ _ _ (RingEquiv.refl L)
    (continuous_id_locUniformSpace hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).1
    (continuous_id_locUniformSpace hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).2

/-- The isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` is continuous. -/
theorem continuous_completionLocRingEquivIntervalRing [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    Continuous (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂) :=
  @UniformSpace.Completion.continuous_mapRingEquiv L L _ (P.locUniformSpace _ _ L hden)
    (P.isTopologicalRing_locUniformSpace _ _ L hden)
    (P.isUniformAddGroup_locUniformSpace _ _ L hden) _ _ _ _ (RingEquiv.refl L) _ _

/-- The inverse of the isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` is continuous. -/
theorem continuous_completionLocRingEquivIntervalRing_symm [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    Continuous (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).symm :=
  @UniformSpace.Completion.continuous_mapRingEquiv_symm L L _ (P.locUniformSpace _ _ L hden)
    (P.isTopologicalRing_locUniformSpace _ _ L hden)
    (P.isUniformAddGroup_locUniformSpace _ _ L hden) _ _ _ _ (RingEquiv.refl L) _ _

/-- **The isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` is the identity on `𝕎 O[1/(p [ϖ])]`**: it sends the image
of `x` in the completion for the localisation topology to the image of `x` in `B^I`. -/
@[simp]
theorem completionLocRingEquivIntervalRing_coe [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) (x : L) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂
        (x : UniformSpace.Completion L) = (x : IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) :=
  @UniformSpace.Completion.mapRingHom_coe L _ (P.locUniformSpace _ _ L hden)
    (P.isTopologicalRing_locUniformSpace _ _ L hden)
    (P.isUniformAddGroup_locUniformSpace _ _ L hden) L _ _ _ _ (RingHom.id L)
    (continuous_id_locUniformSpace hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).1 x

/-- **The isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` is compatible with the maps from `𝕎 O`**: it carries the
structure map `𝕎 O → 𝕎 O⟨T/s⟩` to the map `𝕎 O → B^I`. -/
theorem completionLocRingEquivIntervalRing_toCompletionLoc [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) (a : 𝕎 O) :
    completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂
        (P.toCompletionLoc _ _ L hden a) =
      algebraMap (𝕎 O) (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) a := by
  rw [UniformSpace.Completion.algebraMap_def, PairOfDefinition.toCompletionLoc_apply]
  exact completionLocRingEquivIntervalRing_coe hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ _

/-- **The isomorphism `𝕎 O⟨T/s⟩ ≃+* B^I` carries the plus ring of the window onto `B^{I,+}`.** With
plus ring `A⁺ = 𝕎 O`, the plus ring `A_U⁺` of the rational localisation at the window is the
closure of the image of the integral closure of `A⁺[T/s]`, which is the window subring
(`adjoin_top_windowNumerators`). The isomorphism is a homeomorphism and the identity on
`𝕎 O[1/(p [ϖ])]`, so it carries that closure to the corresponding closure in `B^I`, which is
`B^{I,+} = (B^I)°` (`topologicalClosure_map_coeRingHom_integralClosure_windowSubring`). Hence the
isomorphism is one of Huber pairs `(𝕎 O⟨T/s⟩, A_U⁺) ≅ (B^I, B^{I,+})`. -/
theorem map_completedPlusSubring_windowNumerators [TopologicalSpace (𝕎 O)]
    [IsTopologicalRing (𝕎 O)] (hI : IsAdic (Ideal.span {(p : 𝕎 O), teichmuller p ϖ}))
    (P : PairOfDefinition (𝕎 O)) [IsLocalization.Away (windowDenominator p ϖ q q') L]
    (hden : P.HasDenominatorPower (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L)
    (h₁ : ρ₁ ^ q.num = v (algebraMap O K ϖ) ^ q.den)
    (h₂ : ρ₂ ^ q'.num = v (algebraMap O K ϖ) ^ q'.den) (h₁₂ : ρ₁ ≤ ρ₂) :
    letI := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
    letI := P.isUniformAddGroup_locUniformSpace _ _ L hden
    letI := P.isTopologicalRing_locUniformSpace _ _ L hden
    (P.completedPlusSubring ⊤ (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L
        hden).map (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ :
          _ →+* IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) =
      powerBoundedSubring (IntervalRing p hv hϖ hϖ' hρ₁ hρ₂) := by
  -- rewrite the right-hand side before `L` acquires the localisation uniformity as a local
  -- instance, since `B^I` completes `L` for the interval norm
  rw [← topologicalClosure_map_coeRingHom_integralClosure_windowSubring hv hϖ hϖ' hρ₁ hρ₂ h₁ h₂
    h₁₂, ← adjoin_top_windowNumerators]
  refine SetLike.coe_injective ?_
  rw [UniformSpace.Completion.coe_topologicalClosure_map_coeRingHom]
  let _ := P.locUniformSpace (windowNumerators p ϖ q q') (windowDenominator p ϖ q q') L hden
  have _ := P.isUniformAddGroup_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  have _ := P.isTopologicalRing_locUniformSpace (windowNumerators p ϖ q q')
    (windowDenominator p ϖ q q') L hden
  let h : UniformSpace.Completion L ≃ₜ IntervalRing p hv hϖ hϖ' hρ₁ hρ₂ :=
    { (completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂).toEquiv with
      continuous_toFun := continuous_completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P
        hden h₁ h₂ h₁₂
      continuous_invFun := continuous_completionLocRingEquivIntervalRing_symm hv hϖ hϖ' hρ₁ hρ₂
        hI P hden h₁ h₂ h₁₂ }
  -- `h` is the isomorphism with its continuity bundled, so it has the same underlying function
  rw [Subring.coe_map, PairOfDefinition.coe_completedPlusSubring, RingHom.coe_coe,
    show ⇑(completionLocRingEquivIntervalRing hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂) = h from rfl,
    h.image_closure, Set.image_image]
  exact congrArg closure (Set.image_congr fun x _ ↦
    completionLocRingEquivIntervalRing_coe hv hϖ hϖ' hρ₁ hρ₂ hI P hden h₁ h₂ h₁₂ x)

end Interval

end TauCeti.WittVector
