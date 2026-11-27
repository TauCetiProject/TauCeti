/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.Comparison

/-!
# Global reciprocity for isogeny Selmer groups

For an isogeny `φ : E₁ → E₂` of elliptic curves over a number field `K` and its dual
`φ̂ : E₂ → E₁`, global reciprocity for the isogeny Weil cup product (in `TauCeti.Isogeny`:
`sum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteTateKerWeilPairing_eq_zero` and
`sum_ringEquivCongr_localTateKerWeilPairing_eq_zero`) turns local orthogonality of
the Selmer conditions into global orthogonality between `S`-relaxed `φ`-Selmer classes and
`S`-relaxed `φ̂`-Selmer classes:

Specialised to the `S`-relaxed `φ`- and `φ̂`-Selmer structures, every `S`-relaxed `φ`-Selmer
class pairs to zero summed over `S` with every `S`-relaxed `φ̂`-Selmer class
(`TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt`),
and in particular with every unrelaxed class in `Sel_φ̂(E₂/K)` — see
`sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_of_mem_selmerGroup`
in `TauCeti.Isogeny`.
For a single finite place `v₀`, any `{Sum.inl v₀}`-relaxed `φ`-Selmer class is locally
orthogonal at `v₀` to every `{Sum.inl v₀}`-relaxed `φ̂`-Selmer class and every class in
`Sel_φ̂(E₂/K)`
(`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton` and
`localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton_of_mem_selmerGroup`).

This is the global reciprocity half of the Poitou–Tate / Greenberg–Wiles comparison between
`Sel_φ(E₁/K)` and `Sel_φ̂(E₂/K)` used in Cassels' theorem on the isogeny invariance of the
Birch–Swinnerton-Dyer quotient.

## Main results

* `TauCeti.Isogeny.selmerGroup_le_selmerGroup_relaxedAt` and
  `TauCeti.Isogeny.mem_selmerGroup_relaxedAt_iff`: inclusion into and membership in the
  `S`-relaxed `φ`-Selmer group via vanishing of `pointRes` at finite places outside `S` and at
  infinite places.
* `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt`,
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt`,
  `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton`, and
  their `*_of_mem_selmerGroup` specializations to `Sel_φ̂(E₂/K)`: global orthogonality of
  `S`-relaxed `φ`-Selmer classes against `S`-relaxed and unrelaxed `φ̂`-Selmer classes.

## References

* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, §4.
* K. Rubin, *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press,
  2000, I.7.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti TauCeti.ContCohomology TauCeti.ClassFieldTheory
open Hom (ofIsogeny)

/-! ### Global orthogonality of relaxed `φ`- and `φ̂`-Selmer groups -/

section Global

variable {K : Type} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- Every class in `φ.selmerGroup τ` lies in the `T`-relaxed Selmer group for any set `T` of
places. -/
theorem selmerGroup_le_selmerGroup_relaxedAt
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (T : Set (GlobalNumberFields.Place K)) :
    φ.selmerGroup τ ≤ ((φ.selmerStructure τ).relaxedAt T).selmerGroup :=
  (φ.selmerGroup_def τ).symm ▸ (φ.selmerStructure τ).selmerGroup_le_selmerGroup_relaxedAt T

/-- An `S`-relaxed `φ`-Selmer class is precisely a class in `H¹(K, E₁[φ])` whose image under
`pointRes` after pushing forward to `E₁` vanishes at every finite place outside `S` and at
every infinite place. -/
theorem mem_selmerGroup_relaxedAt_iff
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff} :
    a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup ↔
      (∀ v ∉ S, W₁.pointRes (τ (.inl v))
        (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology a) = 0) ∧
      (∀ w : InfinitePlace K, W₁.pointRes (τ (.inr w))
        (explicitCoeff1 _ _ (ofIsogeny φ).kerCoeffIncl continuous_of_discreteTopology a) = 0) := by
  rw [SelmerStructure.mem_selmerGroup_relaxedAt_iff]
  simp only [selmerStructure_localization, selmerStructure_localCondition,
    mem_localKummerCondition_iff, pointRes_kerCoeffIncl]
  refine ⟨fun h ↦ ⟨fun v hv ↦ h (.inl v) (by simpa using hv), fun w ↦ h (.inr w) (by simp)⟩, ?_⟩
  rintro ⟨hv, hw⟩ (v | w) hp
  · exact hv v (by simpa using hp)
  · exact hw w

/-- **Global Selmer reciprocity in `ℚ/ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer group
and `b` belongs to the `S`-relaxed `φ̂`-Selmer group (local conditions relaxed at the finite
places in `S` and kept outside `S` and at every infinite place), then the sum over `v ∈ S` of
their `ℚ/ℤ`-valued local Tate pairings vanishes. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup) :
    ∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 := by
  have ha' := (φ.mem_selmerGroup_relaxedAt_iff τ S).1 ha
  have hb' := (φ.dual.mem_selmerGroup_relaxedAt_iff τ S).1 hb
  let S' : Finset (GlobalNumberFields.Place K) := S.map ⟨Sum.inl, Sum.inl_injective⟩
  have h :=
    φ.sum_toRatAddCircle_localTateKerWeilPairing_add_sum_infiniteTateKerWeilPairing_eq_zero a b
      (fun v ↦ τ (.inl v)) (fun w ↦ τ (.inr w)) S'
      (fun v hv ↦ ha'.1 v (by simpa [S'] using hv))
      (fun v hv ↦ hb'.1 v (by simpa [S'] using hv))
      (fun w _ ↦ ha'.2 w) (fun w _ ↦ hb'.2 w)
  have hL : S'.toLeft = S := by ext v; simp [S']
  have hR : S'.toRight = ∅ := by ext w; simp [S']
  rwa [hL, hR, Finset.sum_empty, add_zero] at h

/-- **Global Selmer reciprocity in `ℚ/ℤ` against `Sel_φ̂`.** If `a` belongs to the `S`-relaxed
`φ`-Selmer group and `b ∈ φ.dual.selmerGroup τ`, then the sum over `v ∈ S` of their
`ℚ/ℤ`-valued local Tate pairings vanishes. -/
theorem
  sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_of_mem_selmerGroup
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    ∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 :=
  φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt τ S ha
    (φ.dual.selmerGroup_le_selmerGroup_relaxedAt τ _ hb)

/-- **Global Selmer reciprocity in `ℤ/(deg φ)ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer
group and `b` belongs to the `S`-relaxed `φ̂`-Selmer group, then the sum over `v ∈ S` of their
local Tate pairings in `ZMod φ.degree` vanishes. -/
theorem sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup) :
    ∑ v ∈ S,
      ZMod.ringEquivCongr (φ.degree_baseChange (K := v.adicCompletion K))
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 :=
  have ha' := (φ.mem_selmerGroup_relaxedAt_iff τ S).1 ha
  have hb' := (φ.dual.mem_selmerGroup_relaxedAt_iff τ S).1 hb
  φ.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero a b
    (fun v ↦ τ (.inl v)) (fun w ↦ τ (.inr w)) S ha'.1 hb'.1 ha'.2 hb'.2

/-- **Global Selmer reciprocity in `ℤ/(deg φ)ℤ` against `Sel_φ̂`.** If `a` belongs to the
`S`-relaxed `φ`-Selmer group and `b ∈ φ.dual.selmerGroup τ`, then the sum over `v ∈ S` of
their local Tate pairings in `ZMod φ.degree` vanishes. -/
theorem
  sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_of_mem_selmerGroup
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    ∑ v ∈ S,
      ZMod.ringEquivCongr (φ.degree_baseChange (K := v.adicCompletion K))
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v.adicCompletion K)).degree_ne_zero)
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 :=
  φ.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt τ S ha
    (φ.dual.selmerGroup_le_selmerGroup_relaxedAt τ _ hb)

/-- **Single-place Selmer orthogonality.** Two global classes `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])` satisfying their respective local Selmer conditions at every place except
possibly a single finite place `v₀` are locally orthogonal at `v₀`. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (v₀ : HeightOneSpectrum (𝓞 K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt {Sum.inl v₀}).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relaxedAt {Sum.inl v₀}).selmerGroup) :
    (φ.baseChange (v₀.adicCompletion K)).localTateKerWeilPairing
      (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v₀.adicCompletion K)).degree_ne_zero)
      (φ.kerRes (τ (.inl v₀)) a) (φ.dualKerRes (τ (.inl v₀)) b) = 0 := by
  have ha' : a ∈ ((φ.selmerStructure τ).relaxedAt
      (Sum.inl '' (({v₀} : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))))).selmerGroup := by
    simpa using ha
  have hb' : b ∈ ((φ.dual.selmerStructure τ).relaxedAt
      (Sum.inl '' (({v₀} : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))))).selmerGroup := by
    simpa using hb
  have hsum :=
    φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt τ {v₀}
      ha' hb'
  rw [Finset.sum_singleton] at hsum
  exact (ZMod.toRatAddCircle_eq_zero _).mp hsum

/-- **Single-place Selmer orthogonality against `Sel_φ̂`.** A global class
`a ∈ H¹(K, E₁[φ])` satisfying its local Selmer conditions everywhere except possibly at `v₀` is
locally orthogonal at `v₀` to every class `b ∈ φ.dual.selmerGroup τ`. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton_of_mem_selmerGroup
    (τ : ∀ p : GlobalNumberFields.Place K,
      SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (v₀ : HeightOneSpectrum (𝓞 K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relaxedAt {Sum.inl v₀}).selmerGroup)
    (hb : b ∈ φ.dual.selmerGroup τ) :
    (φ.baseChange (v₀.adicCompletion K)).localTateKerWeilPairing
      (isUnit_natCast_of_ne_zero ℚ (φ.baseChange (v₀.adicCompletion K)).degree_ne_zero)
      (φ.kerRes (τ (.inl v₀)) a) (φ.dualKerRes (τ (.inl v₀)) b) = 0 :=
  φ.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relaxedAt_singleton τ v₀ ha
    (φ.dual.selmerGroup_le_selmerGroup_relaxedAt τ _ hb)

end Global

end TauCeti.Isogeny

end
