/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Gluing
public import TauCeti.Analysis.Distribution.Mass.Measure

/-!
# Locality and gluing of locally finite mass

A real-linear functional on vector-valued tests has locally finite mass if and only if
it has finite local mass on some open neighbourhood of each point of its domain.
Consequently, locally finite mass can be checked after restriction to any open cover.
The cover need not be countable or locally finite, and the local mass bounds need not
be uniform across its members.

Compatible continuous linear maps of locally finite mass therefore glue uniquely to
one of locally finite mass. Applied to alternating-form-valued tests, this is the
gluing property for currents of locally finite mass. No finite *global* mass assertion
is made, even when all the members of the cover have finite mass.

The quantitative input is the existing finite partition-of-unity mass estimate:
on a compact testing set, finitely many neighbourhoods with finite local mass suffice.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.5 (locally representable currents).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.2
  (localization and gluing of distributions).
-/

public section

open Set TopologicalSpace TestFunction
open scoped Distributions ENNReal

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens E} {n : ℕ∞}
  {𝓕 : Type*} [FunLike 𝓕 𝓓^{n}(Ω, F) V] [LinearMapClass 𝓕 ℝ 𝓓^{n}(Ω, F) V]

/-- Locally finite mass is equivalent to finite local mass on an open neighbourhood
of every point. The neighbourhoods need not have a common mass bound. -/
theorem hasLocallyFiniteMass_iff_exists_open_localMass_ne_top (T : 𝓕) :
    HasLocallyFiniteMass T ↔ ∀ x ∈ Ω, ∃ U : Opens E, x ∈ U ∧ localMass T U ≠ ⊤ := by
  classical
  refine ⟨fun hT x hx => ?_, fun hT => ?_⟩
  · obtain ⟨U, hU, hTU⟩ := hT.exists_open_localMass_ne_top isCompact_singleton
      (singleton_subset_iff.2 hx)
    exact ⟨U, hU (mem_singleton x), hTU⟩
  · refine (hasLocallyFiniteMass_iff_localMass_ne_top T).2 fun K hK hKΩ => ?_
    choose U hxU hTU using fun x : K => hT x (hKΩ x.property)
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (U x : Set E))
      (fun x => (U x).isOpen) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
    have hbound : localMass T K ≤ ∑ i : s, localMass T (U i) := by
      refine localMass_le_iff.2 fun φ hφK hφ => ?_
      have hcover : tsupport φ ⊆ ⋃ i : s, (U i : Set E) := by
        intro x hx
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (hs (hφK hx))
        exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
      simpa using enorm_apply_le_sum_localMass_mul T (fun i : s => (U i).isOpen)
        hcover (c := fun _ => 1) (fun _ x _ => by
          simpa only [← ofReal_norm, ENNReal.ofReal_le_one] using hφ x)
    exact ne_top_of_le_ne_top (by simp [hTU]) hbound

/-- Locally finite mass can be checked on the members of an arbitrary open cover. -/
theorem hasLocallyFiniteMass_iff_forall_comp_monoCLM (T : 𝓕)
    {ι : Type*} {U : ι → Opens E} (hU : ⨆ i, U i = Ω) :
    HasLocallyFiniteMass T ↔ ∀ i, HasLocallyFiniteMass
      (T ∘ (monoCLM ℝ : 𝓓^{n}(U i, F) →L[ℝ] 𝓓^{n}(Ω, F))) := by
  have hUΩ (i : ι) : U i ≤ Ω := hU ▸ le_iSup U i
  refine ⟨fun hT i => hT.comp_monoCLM, fun hT => ?_⟩
  refine (hasLocallyFiniteMass_iff_exists_open_localMass_ne_top T).2 fun x hx => ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ U i := by
    simpa [← SetLike.mem_coe, ← hU, Opens.coe_iSup] using hx
  obtain ⟨W, hxW, hW⟩ :=
    (hasLocallyFiniteMass_iff_exists_open_localMass_ne_top
      ((T : 𝓓^{n}(Ω, F) →ₗ[ℝ] V).comp (monoCLM ℝ).toLinearMap)).1 (hT i) x hi
  refine ⟨W ⊓ U i, ⟨hxW, hi⟩, ?_⟩
  rw [Opens.coe_inf, ← localMass_comp_monoCLM T (hUΩ i) W]
  simpa only [LinearMap.coe_comp, LinearMap.coe_ofClass, ContinuousLinearMap.coe_coe] using hW

/-- Compatible continuous linear maps of locally finite mass on an arbitrary open cover
glue uniquely to a continuous linear map of locally finite mass on its union. -/
theorem existsUnique_gluing_hasLocallyFiniteMass {ι : Type*} {U : ι → Opens E}
    {T : ∀ i, 𝓓^{n}(U i, F) →L[ℝ] V} (hU : ⨆ i, U i = Ω)
    (hT : ∀ i j (φ : 𝓓^{n}(U i ⊓ U j, F)), T i (monoCLM ℝ φ) = T j (monoCLM ℝ φ))
    (hTf : ∀ i, HasLocallyFiniteMass (T i)) :
    ∃! S : 𝓓^{n}(Ω, F) →L[ℝ] V,
      HasLocallyFiniteMass S ∧ ∀ i, S ∘L monoCLM ℝ = T i := by
  obtain ⟨S, hS, huniq⟩ := existsUnique_gluing hU hT
  have hSf : HasLocallyFiniteMass S := by
    refine (hasLocallyFiniteMass_iff_forall_comp_monoCLM S hU).2 fun i => ?_
    have hi := hTf i
    rw [← hS i] at hi
    simpa only [ContinuousLinearMap.coe_comp] using hi
  exact ⟨S, ⟨hSf, hS⟩, fun S' hS' => huniq S' hS'.2⟩

end Distribution
