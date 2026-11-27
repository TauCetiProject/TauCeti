/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.CharacterAnnihilator
public import TauCeti.NumberTheory.LocalField.AddChar.DualLattice
public import TauCeti.NumberTheory.LocalField.HaarCharacter
public import TauCeti.Topology.LocallyConstant.CompactSupport
import TauCeti.NumberTheory.LocalField.Topology
import TauCeti.Topology.Algebra.Group.LocallyConstant

/-!
# The self-dual Haar measure of an additive character of a nonarchimedean local field

Let `K` be a nonarchimedean local field, with ring of integers `O`, maximal ideal `P` and residue
field of cardinality `q`, and write `P ^ m = {x | valuation K x ≤ uniformizer K ^ m}` for `m : ℤ`.
Let `ψ` be a nontrivial continuous additive character of `K`, with conductor exponent
`ν = ν(ψ)` (`AddChar.conductorExponent`): `ψ` is trivial on `P ^ (-ν)` and not on `P ^ (-ν - 1)`.
Under the pairing `(x, y) ↦ ψ (x * y)` the annihilator of `P ^ m` is `P ^ (-ν - m)`
(`AddChar.characterAnnihilator_leAddSubgroup`).

Every additive Haar measure `μ` on `K` gives `P ^ m` the mass `q ^ (-m) μ(O)`, so
`μ(P ^ m) μ(P ^ (-ν - m)) = q ^ ν μ(O) ^ 2` does not depend on `m`. The **self-dual measure**
`ψ.selfDualMeasure` is the unique Haar measure making this product `1`, the one with
`μ(O) = q ^ (-ν / 2)`. For it the Fourier transform

`𝓕 f (y) = ∫ ψ (-(x * y)) f x dμ(x)`

(Mathlib's `Fourier.fourierIntegral ψ ψ.selfDualMeasure`) satisfies Fourier inversion
`𝓕 (𝓕 f) x = f (-x)` on the Schwartz–Bruhat space of `K`, the locally constant compactly supported
functions; such a function is periodic under some `P ^ m`
(`IsLocallyConstant.exists_forall_periodic_leAddSubgroup_uniformizer_zpow`), which reduces
inversion to `VectorFourier.fourierIntegral_fourierIntegral_of_periodic`. The transform therefore
restricts to a linear automorphism of the Schwartz–Bruhat space
`LocallyConstant.compactlySupported ℂ K E`.
The transform with the opposite sign, `y ↦ ∫ ψ (x * y) f x dμ(x)`, is `y ↦ 𝓕 f (-y)`, so it has
the same self-dual measure and satisfies the same inversion formula.

This is the additive measure of Tate's local theory, whose local functional equation compares the
zeta integrals of `f` and of `𝓕 f`. Nothing here uses the characteristic of `K`.

## Main definitions

* `AddChar.selfDualMeasure`: the Haar measure `q ^ (-ν(ψ) / 2) • dx`, where `dx` gives `O` mass
  one.
* `AddChar.fourierCompactlySupported`: Fourier transform for the self-dual measure, as a linear
  automorphism of the locally constant compactly supported functions on `K`.

## Main results

* `IsLocallyConstant.exists_forall_periodic_leAddSubgroup_uniformizer_zpow`: a locally constant
  compactly supported function on `K` is periodic under some `P ^ m`.
* `AddChar.selfDualMeasure_integer`,
  `AddChar.selfDualMeasure_setOf_valuation_le_uniformizer_zpow`: the self-dual measure gives `O`
  mass `q ^ (-ν / 2)` and `P ^ m` mass `q ^ (-m - ν / 2)`.
* `AddChar.selfDualMeasure_mul_selfDualMeasure`: `μ(P ^ m) μ(P ^ (-ν - m)) = 1` for the self-dual
  measure `μ`.
* `AddChar.addHaar_eq_selfDualMeasure_iff`: a Haar measure `μ` is the self-dual measure exactly
  when `μ(P ^ m) μ(P ^ (-ν - m)) = 1`, for any single `m`.
* `AddChar.isLocallyConstant_fourierIntegral`, `AddChar.hasCompactSupport_fourierIntegral`: the
  Fourier transform of a locally constant compactly supported function is again one.
* `AddChar.fourierIntegral_fourierIntegral_selfDualMeasure`: Fourier inversion
  `𝓕 (𝓕 f) x = f (-x)` for locally constant compactly supported `f`.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, Thesis (1950), in
  Cassels–Fröhlich, *Algebraic Number Theory*, §2.2.
* A. Weil, *Basic Number Theory*, Chapter VII, §2.
-/

public section
noncomputable section

open MeasureTheory Measure Filter Topology ValuativeRel TauCeti Function Set
open scoped ENNReal

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A locally constant compactly supported function on `K` is periodic under some fractional
ideal `P ^ m`: its open subgroup of periods contains one of these neighbourhoods of `0`. -/
theorem IsLocallyConstant.exists_forall_periodic_leAddSubgroup_uniformizer_zpow
    {A : Type*} [Zero A] {f : K → A} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    ∃ m : ℤ, ∀ u ∈ (valuation K).leAddSubgroup (uniformizer K ^ m), Function.Periodic f u := by
  obtain ⟨m, -, hm⟩ := (hasBasis_nhds_zero_valuation_le_uniformizer_zpow K).mem_iff.1
    ((isOpen_addRightTranslationStabilizer_of_hasCompactSupport hf hfc).mem_nhds
      (zero_mem (addRightTranslationStabilizer f)))
  exact ⟨m, fun u hu ↦ mem_addRightTranslationStabilizer.1 (hm hu)⟩

namespace AddChar

section Measure

variable [MeasurableSpace K] [BorelSpace K] {M : Type*} [Monoid M]

variable (ψ : AddChar K M) in
/-- The **self-dual Haar measure** of an additive character `ψ` of `K`: the Haar measure giving
the ring of integers `O` mass `q ^ (-ν(ψ) / 2)`, where `q` is the cardinality of the residue field
and `ν(ψ)` the conductor exponent. For a nontrivial `ψ` trivial on a neighbourhood of `0`, it is
the unique Haar measure for which a fractional ideal and its annihilator under `ψ (x * y)` have
reciprocal volumes (`AddChar.addHaar_eq_selfDualMeasure_iff`), and Fourier transform for it is
inverse to itself up to `x ↦ -x` (`AddChar.fourierIntegral_fourierIntegral_selfDualMeasure`). -/
def selfDualMeasure : Measure K :=
  (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(ψ.conductorExponent : ℝ) / 2) •
    addHaarMeasure (integerPositiveCompacts K)

variable (ψ : AddChar K M)

instance isAddHaarMeasure_selfDualMeasure : ψ.selfDualMeasure.IsAddHaarMeasure :=
  .smul _ (ENNReal.rpow_pos natCard_residueField_pos
    (ENNReal.natCast_ne_top _)).ne' (ENNReal.rpow_ne_top_of_nonneg' (by
      exact_mod_cast natCard_residueField_pos) (ENNReal.natCast_ne_top _))

/-- The self-dual measure gives the ring of integers mass `q ^ (-ν(ψ) / 2)`. -/
@[simp]
theorem selfDualMeasure_integer :
    ψ.selfDualMeasure 𝒪[K] = (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(ψ.conductorExponent : ℝ) / 2) := by
  rw [selfDualMeasure, smul_apply, ← coe_integerPositiveCompacts K, addHaarMeasure_self,
    smul_eq_mul, mul_one]

/-- The self-dual measure gives the fractional ideal `P ^ m` mass `q ^ (-m - ν(ψ) / 2)`. -/
theorem selfDualMeasure_setOf_valuation_le_uniformizer_zpow (m : ℤ) :
    ψ.selfDualMeasure {x | valuation K x ≤ uniformizer K ^ m} =
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(m : ℝ) - ψ.conductorExponent / 2) := by
  rw [addHaar_setOf_valuation_le_uniformizer_zpow, selfDualMeasure_integer,
    ← ENNReal.rpow_intCast, ← ENNReal.rpow_add _ _ natCard_residueField_pos.ne'
      (ENNReal.natCast_ne_top _)]
  congr 1
  push_cast
  ring

/-- **Self-duality.** For the self-dual measure, the fractional ideals `P ^ m` and
`P ^ (-ν(ψ) - m)`, which are annihilators of each other under `ψ (x * y)`
(`AddChar.characterAnnihilator_leAddSubgroup`), have reciprocal volumes. -/
theorem selfDualMeasure_mul_selfDualMeasure (m : ℤ) :
    ψ.selfDualMeasure {x | valuation K x ≤ uniformizer K ^ m} *
        ψ.selfDualMeasure {x | valuation K x ≤ uniformizer K ^ (-ψ.conductorExponent - m)} =
      1 := by
  rw [selfDualMeasure_setOf_valuation_le_uniformizer_zpow,
    selfDualMeasure_setOf_valuation_le_uniformizer_zpow,
    ← ENNReal.rpow_add _ _ natCard_residueField_pos.ne' (ENNReal.natCast_ne_top _)]
  convert ENNReal.rpow_zero using 2
  push_cast
  ring

/-- **Uniqueness of the self-dual measure.** An additive Haar measure `μ` on `K` is the self-dual
measure of `ψ` exactly when the fractional ideals `P ^ m` and `P ^ (-ν(ψ) - m)` have reciprocal
volumes, for any single `m : ℤ`. For a nontrivial `ψ` trivial on a neighbourhood of `0` these
ideals are annihilators of each other (`AddChar.characterAnnihilator_leAddSubgroup`). -/
theorem addHaar_eq_selfDualMeasure_iff (μ : Measure K) [μ.IsAddHaarMeasure] (m : ℤ) :
    μ = ψ.selfDualMeasure ↔
      μ {x | valuation K x ≤ uniformizer K ^ m} *
          μ {x | valuation K x ≤ uniformizer K ^ (-ψ.conductorExponent - m)} = 1 := by
  refine ⟨fun h ↦ by rw [h]; exact selfDualMeasure_mul_selfDualMeasure ψ m, fun h ↦ ?_⟩
  have hq0 : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ 0 := natCard_residueField_pos.ne'
  have hqt : (Nat.card 𝓀[K] : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  -- Both measures are multiples of the Haar measure giving `O` mass one, so it suffices to
  -- compare their masses of `O`; the hypothesis says `q ^ ν * μ(O) ^ 2 = 1`.
  have hν : (Nat.card 𝓀[K] : ℝ≥0∞) ^ (ψ.conductorExponent : ℝ) * μ 𝒪[K] ^ 2 = 1 := by
    rw [addHaar_setOf_valuation_le_uniformizer_zpow,
      addHaar_setOf_valuation_le_uniformizer_zpow] at h
    convert h using 1
    rw [← ENNReal.rpow_intCast, ← ENNReal.rpow_intCast, mul_mul_mul_comm,
      ← ENNReal.rpow_add _ _ hq0 hqt]
    push_cast
    ring_nf
  have hc2 : μ 𝒪[K] ^ (2 : ℝ) =
      (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(ψ.conductorExponent : ℝ)) := by
    rw [ENNReal.rpow_two, ENNReal.rpow_neg]
    exact ENNReal.eq_inv_of_mul_eq_one_left (by rwa [mul_comm])
  have hc : μ 𝒪[K] = (Nat.card 𝓀[K] : ℝ≥0∞) ^ (-(ψ.conductorExponent : ℝ) / 2) := by
    refine ENNReal.rpow_left_injective (x := 2) two_ne_zero ?_
    simp only [hc2, ← ENNReal.rpow_mul]
    ring_nf
  rw [addHaarMeasure_unique μ (integerPositiveCompacts K), coe_integerPositiveCompacts, hc,
    selfDualMeasure]

end Measure

section Fourier

variable [MeasurableSpace K] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {ψ : AddChar K Circle}

/-- The Fourier transform of a compactly supported function on `K`, for any measure and any
continuous additive character, is locally constant. -/
theorem isLocallyConstant_fourierIntegral (hψ : Continuous ψ) (μ : Measure K) {f : K → E}
    (hfc : HasCompactSupport f) : IsLocallyConstant (Fourier.fourierIntegral ψ μ f) := by
  obtain ⟨n, hn⟩ := hfc.isCompact.exists_subset_setOf_valuation_le_uniformizer_zpow
  rw [Fourier.fourierIntegral_eq_vectorFourierIntegral]
  exact VectorFourier.isLocallyConstant_fourierIntegral ψ μ (LinearMap.mul K K)
    (U := (valuation K).leAddSubgroup (uniformizer K ^ n))
    (isCompact_leAddSubgroup K _)
    (by simp only [LinearMap.mul_apply']; exact hψ.comp continuous_mul)
    ((subset_tsupport f).trans ((valuation K).coe_leAddSubgroup _ ▸ hn))

variable [BorelSpace K]

/-- For a nontrivial continuous additive character `ψ` of `K` and a translation-invariant
measure, the Fourier transform of a locally constant compactly supported function has compact
support. -/
theorem hasCompactSupport_fourierIntegral (hψ : Continuous ψ) (h1 : ψ ≠ 1) (μ : Measure K)
    [μ.IsAddRightInvariant] {f : K → E} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) :
    HasCompactSupport (Fourier.fourierIntegral ψ μ f) := by
  obtain ⟨m, hm⟩ := hf.exists_forall_periodic_leAddSubgroup_uniformizer_zpow hfc
  rw [Fourier.fourierIntegral_eq_vectorFourierIntegral]
  refine VectorFourier.hasCompactSupport_fourierIntegral ψ μ (LinearMap.mul K K) hm ?_
  rw [characterAnnihilator_leAddSubgroup (setOf_eq_one_mem_nhds_zero hψ) h1]
  exact isCompact_leAddSubgroup K _

variable [CompleteSpace E]

/-- **Fourier inversion on a nonarchimedean local field.** For a nontrivial continuous additive
character `ψ` of `K` and its self-dual measure, every locally constant compactly supported
`f : K → E` satisfies `𝓕 (𝓕 f) x = f (-x)`. -/
theorem fourierIntegral_fourierIntegral_selfDualMeasure (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    {f : K → E} (hf : IsLocallyConstant f) (hfc : HasCompactSupport f) (x : K) :
    Fourier.fourierIntegral ψ ψ.selfDualMeasure
        (Fourier.fourierIntegral ψ ψ.selfDualMeasure f) x = f (-x) := by
  have h0 := setOf_eq_one_mem_nhds_zero hψ
  obtain ⟨m, hm⟩ := hf.exists_forall_periodic_leAddSubgroup_uniformizer_zpow hfc
  have hdual := characterAnnihilator_leAddSubgroup h0 h1
  have hmeas (n : ℤ) : MeasurableSet ((valuation K).leAddSubgroup (uniformizer K ^ n) : Set K) :=
    (isCompact_leAddSubgroup K _).isClosed.measurableSet
  have h := VectorFourier.fourierIntegral_fourierIntegral_of_periodic ψ ψ.selfDualMeasure
    (LinearMap.mul K K) ψ.selfDualMeasure hψ (by simpa using continuous_mul) (hmeas m)
    (by rw [hdual]; exact hmeas _) (by rw [LinearMap.flip_mul, hdual, hdual, sub_sub_cancel])
    (by simp [hdual, measureReal_def, ← ENNReal.toReal_mul, selfDualMeasure_mul_selfDualMeasure])
    (hf.continuous.integrable_of_hasCompactSupport hfc) hm x
  rwa [LinearMap.flip_mul, ← Fourier.fourierIntegral_eq_vectorFourierIntegral,
    ← Fourier.fourierIntegral_eq_vectorFourierIntegral] at h

open LocallyConstant

variable (ψ) in
/-- **Fourier transform on the Schwartz–Bruhat space.** For a nontrivial continuous additive
character `ψ` of `K`, Fourier transform for the self-dual measure,
`𝓕 f (y) = ∫ ψ (-(x * y)) f x dμ(x)`, is a linear automorphism of the space of locally constant
compactly supported functions `K → E`. Its inverse is `g ↦ 𝓕 g (-·)`
(`AddChar.coe_fourierCompactlySupported_symm_apply`). -/
def fourierCompactlySupported (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    compactlySupported ℂ K E ≃ₗ[ℂ] compactlySupported ℂ K E where
  toFun f := ⟨⟨Fourier.fourierIntegral ψ ψ.selfDualMeasure ⇑(f : LocallyConstant K E),
      isLocallyConstant_fourierIntegral hψ _ (mem_compactlySupported.1 f.property)⟩,
    mem_compactlySupported.2 <| hasCompactSupport_fourierIntegral hψ h1 _
      (f : LocallyConstant K E).isLocallyConstant (mem_compactlySupported.1 f.property)⟩
  invFun g := ⟨⟨fun x ↦ Fourier.fourierIntegral ψ ψ.selfDualMeasure ⇑(g : LocallyConstant K E) (-x),
      (isLocallyConstant_fourierIntegral hψ _
        (mem_compactlySupported.1 g.property)).comp_continuous continuous_neg⟩,
    mem_compactlySupported.2 <| (hasCompactSupport_fourierIntegral hψ h1 _
      (g : LocallyConstant K E).isLocallyConstant
        (mem_compactlySupported.1 g.property)).comp_homeomorph (Homeomorph.neg K)⟩
  map_add' f g := by
    ext x
    simp only [LocallyConstant.coe_mk, Fourier.fourierIntegral_eq_vectorFourierIntegral]
    exact congrFun (VectorFourier.fourierIntegral_add hψ (by simpa using continuous_mul)
      ((f : LocallyConstant K E).continuous.integrable_of_hasCompactSupport
        (mem_compactlySupported.1 f.property))
      ((g : LocallyConstant K E).continuous.integrable_of_hasCompactSupport
        (mem_compactlySupported.1 g.property))) x
  map_smul' c f := by
    ext x
    exact congrFun (Fourier.fourierIntegral_const_smul ψ _ _ c) x
  left_inv f := by
    ext x
    simpa using fourierIntegral_fourierIntegral_selfDualMeasure hψ h1
      (f : LocallyConstant K E).isLocallyConstant (mem_compactlySupported.1 f.property) (-x)
  right_inv g := by
    ext x
    set F := Fourier.fourierIntegral (E := E) ψ ψ.selfDualMeasure
    set g' : K → E := ⇑(g : LocallyConstant K E)
    have hg : IsLocallyConstant g' := (g : LocallyConstant K E).isLocallyConstant
    have hgc : HasCompactSupport g' := mem_compactlySupported.1 g.property
    have hFg := isLocallyConstant_fourierIntegral hψ ψ.selfDualMeasure hgc
    have hFgc := hasCompactSupport_fourierIntegral hψ h1 ψ.selfDualMeasure hg hgc
    -- By inversion for `𝓕 g`, the function `𝓕 g (-·)` is `𝓕 (𝓕 (𝓕 g))`.
    have h3 : (fun y ↦ F g' (-y)) = F (F (F g')) :=
      funext fun y ↦ (fourierIntegral_fourierIntegral_selfDualMeasure hψ h1 hFg hFgc y).symm
    -- The goal is stated through the coercions of the structure literal above.
    change F (fun y ↦ F g' (-y)) x = g' x
    rw [h3]
    exact (fourierIntegral_fourierIntegral_selfDualMeasure hψ h1
      (isLocallyConstant_fourierIntegral hψ _ hFgc)
      (hasCompactSupport_fourierIntegral hψ h1 _ hFg hFgc) x).trans
      ((fourierIntegral_fourierIntegral_selfDualMeasure hψ h1 hg hgc (-x)).trans
        (congrArg g' (neg_neg x)))

@[simp]
theorem coe_fourierCompactlySupported_apply (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (f : compactlySupported ℂ K E) :
    ⇑(fourierCompactlySupported ψ hψ h1 f : LocallyConstant K E) =
      Fourier.fourierIntegral ψ ψ.selfDualMeasure ⇑(f : LocallyConstant K E) :=
  (rfl)

@[simp]
theorem coe_fourierCompactlySupported_symm_apply (hψ : Continuous ψ) (h1 : ψ ≠ 1)
    (g : compactlySupported ℂ K E) (x : K) :
    ((fourierCompactlySupported ψ hψ h1).symm g : LocallyConstant K E) x =
      Fourier.fourierIntegral ψ ψ.selfDualMeasure ⇑(g : LocallyConstant K E) (-x) :=
  (rfl)

end Fourier

end AddChar
