/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Reciprocity

/-!
# Global reciprocity for isogeny Selmer groups

For an isogeny `φ : E₁ → E₂` of elliptic curves over a number field `K` and its dual `φ̂ : E₂ → E₁`,
global reciprocity for the isogeny Weil cup product
(`TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero`,
`TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero`) turns local orthogonality of
the Selmer conditions into global orthogonality between `S`-relaxed `φ`-Selmer classes and
`S`-relaxed `φ̂`-Selmer classes:

* Specialised to the `S`-relaxed `φ`- and `φ̂`-Selmer structures, every `S`-relaxed `φ`-Selmer
  class pairs to zero summed over `S` with every `S`-relaxed `φ̂`-Selmer class
  (`TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`),
  and in particular with every unrelaxed class in `Sel_φ̂(E₂/K)` via
  `SelmerStructure.selmerGroup_le_relax`. For a single finite place `v₀`, any `{Sum.inl v₀}`-relaxed
  `φ`-Selmer class is locally orthogonal at `v₀` to every `{Sum.inl v₀}`-relaxed `φ̂`-Selmer class
  (`TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton`).

This is the global reciprocity half of the Poitou–Tate / Greenberg–Wiles comparison between
`Sel_φ(E₁/K)` and `Sel_φ̂(E₂/K)` used in Cassels' theorem on the isogeny invariance of the
Birch–Swinnerton-Dyer quotient.

## Main results

* `TauCeti.Isogeny.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`,
  `TauCeti.Isogeny.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax`,
  and `TauCeti.Isogeny.localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton`: global
  orthogonality of `S`-relaxed `φ`- and `φ̂`-Selmer classes.

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

/-- An `S`-relaxed `φ`-Selmer class lies in the local `φ`-Selmer kernel at every finite place
outside `S` and at every infinite place. -/
private theorem kerRes_mem_ker_of_mem_selmerGroup_relax
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup) :
    (∀ v ∉ S, φ.kerRes (τ (.inl v)) a ∈
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange (v.adicCompletion K))).kerCoeffIncl
        continuous_of_discreteTopology).ker) ∧
    (∀ w : InfinitePlace K, φ.kerRes (τ (.inr w)) a ∈
      (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange w.Completion)).kerCoeffIncl
        continuous_of_discreteTopology).ker) := by
  rw [SelmerStructure.mem_selmerGroup_relax_iff] at ha
  exact ⟨fun v hv ↦ by simpa using ha (.inl v) (by simpa using hv),
    fun w ↦ by simpa using ha (.inr w) (by simp)⟩

/-- **Global Selmer reciprocity in `ℚ/ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer group
and `b` belongs to the `S`-relaxed `φ̂`-Selmer group (local conditions relaxed at the finite
places in `S` and kept outside `S` and at every infinite place), then the sum over `v ∈ S` of
their `ℚ/ℤ`-valued local Tate pairings vanishes. Unrelaxed classes in `Sel_φ(E₁/K)` or
`Sel_φ̂(E₂/K)` specialize via `SelmerStructure.selmerGroup_le_relax`. -/
theorem sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup) :
    ∑ v ∈ S,
      ZMod.toRatAddCircle (φ.baseChange (v.adicCompletion K)).degree
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 :=
  have ha' := φ.kerRes_mem_ker_of_mem_selmerGroup_relax τ S ha
  have hb' := φ.dual.kerRes_mem_ker_of_mem_selmerGroup_relax τ S hb
  φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero
    (fun v ↦ τ (.inl v)) (fun w ↦ τ (.inr w)) S
    (fun v hv ↦ ⟨ha'.1 v hv, hb'.1 v hv⟩) (fun w _ ↦ ⟨ha'.2 w, hb'.2 w⟩)

/-- **Global Selmer reciprocity in `ℤ/(deg φ)ℤ`.** If `a` belongs to the `S`-relaxed `φ`-Selmer
group and `b` belongs to the `S`-relaxed `φ̂`-Selmer group, then the sum over `v ∈ S` of their
local Tate pairings in `ZMod φ.degree` vanishes. -/
theorem sum_ringEquivCongr_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relax
      (Sum.inl '' (S : Set (HeightOneSpectrum (𝓞 K))))).selmerGroup) :
    ∑ v ∈ S,
      ZMod.ringEquivCongr (φ.degree_baseChange (v.adicCompletion K))
        ((φ.baseChange (v.adicCompletion K)).localTateKerWeilPairing
          (φ.isUnit_degree_baseChange (v.adicCompletion K))
          (φ.kerRes (τ (.inl v)) a) (φ.dualKerRes (τ (.inl v)) b)) = 0 :=
  have ha' := φ.kerRes_mem_ker_of_mem_selmerGroup_relax τ S ha
  have hb' := φ.dual.kerRes_mem_ker_of_mem_selmerGroup_relax τ S hb
  φ.sum_ringEquivCongr_localTateKerWeilPairing_eq_zero
    (fun v ↦ τ (.inl v)) (fun w ↦ τ (.inr w)) S
    (fun v hv ↦ ⟨ha'.1 v hv, hb'.1 v hv⟩) (fun w _ ↦ ⟨ha'.2 w, hb'.2 w⟩)

/-- **Single-place Selmer orthogonality.** Two global classes `a ∈ H¹(K, E₁[φ])` and
`b ∈ H¹(K, E₂[φ̂])` satisfying their respective local Selmer conditions at every place except
possibly a single finite place `v₀` are locally orthogonal at `v₀`. -/
theorem localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax_singleton
    (τ : ∀ p : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure p.Completion)
    (v₀ : HeightOneSpectrum (𝓞 K))
    {a : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff}
    {b : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ.dual).KerCoeff}
    (ha : a ∈ ((φ.selmerStructure τ).relax {Sum.inl v₀}).selmerGroup)
    (hb : b ∈ ((φ.dual.selmerStructure τ).relax {Sum.inl v₀}).selmerGroup) :
    (φ.baseChange (v₀.adicCompletion K)).localTateKerWeilPairing
      (φ.isUnit_degree_baseChange (v₀.adicCompletion K))
      (φ.kerRes (τ (.inl v₀)) a) (φ.dualKerRes (τ (.inl v₀)) b) = 0 := by
  have ha' : a ∈ ((φ.selmerStructure τ).relax
      (Sum.inl '' (({v₀} : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))))).selmerGroup := by
    simpa using ha
  have hb' : b ∈ ((φ.dual.selmerStructure τ).relax
      (Sum.inl '' (({v₀} : Finset (HeightOneSpectrum (𝓞 K))) :
        Set (HeightOneSpectrum (𝓞 K))))).selmerGroup := by
    simpa using hb
  have hsum :=
    φ.sum_toRatAddCircle_localTateKerWeilPairing_eq_zero_of_mem_selmerGroup_relax τ {v₀} ha' hb'
  rw [Finset.sum_singleton] at hsum
  exact (ZMod.toRatAddCircle_eq_zero _).mp hsum

end Global

end TauCeti.Isogeny

end
