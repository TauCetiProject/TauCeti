/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Elements of spectral radius zero, and closed sets avoiding the spectrum

The spectral radius of an element vanishes exactly when its quasispectrum, or in a unital
algebra its spectrum, is contained in `{0}`. In a complex Banach algebra these are the
quasinilpotent elements, by Gelfand's formula. Both statements are algebraic: they need a
norm only on the scalars, and no completeness.

For the same reason a nonunital algebra homomorphism, with no continuity assumption, does not
increase spectral radii: it can only shrink quasispectra.

Finally, in a complete normed algebra a closed set avoiding the spectrum of an element also avoids
the spectra of all nearby elements (`spectrum.eventually_disjoint_of_isClosed`), a consequence of
the upper hemicontinuity of the spectrum; and the spectrum of any linear isometric automorphism of
a Banach space lies in the unit sphere (`LinearIsometryEquiv.spectrum_subset_sphere`).
-/

public section

namespace TauCeti

variable {𝕜 A : Type*} [NormedField 𝕜]

/-- The spectral radius of an element vanishes exactly when its quasispectrum is contained
in `{0}`. -/
theorem spectralRadius_eq_zero_iff [NonUnitalRing A] [Module 𝕜 A] {a : A} :
    spectralRadius 𝕜 a = 0 ↔ quasispectrum 𝕜 a ⊆ {0} := by
  simp [spectralRadius, Set.subset_def]

/-- In a unital algebra, the spectral radius of an element vanishes exactly when its spectrum
is contained in `{0}`. -/
theorem spectralRadius_eq_zero_iff_spectrum_subset_singleton_zero [Ring A] [Algebra 𝕜 A]
    {a : A} :
    spectralRadius 𝕜 a = 0 ↔ spectrum 𝕜 a ⊆ {0} := by
  rw [spectralRadius_eq_zero_iff, quasispectrum_eq_spectrum_union_zero, Set.union_subset_iff,
    and_iff_left subset_rfl]

end TauCeti

/-- A nonunital algebra homomorphism, not assumed continuous, does not increase spectral radii,
since it can only shrink quasispectra. -/
theorem NonUnitalAlgHom.spectralRadius_apply_le {F 𝕜 A B : Type*} [NormedField 𝕜]
    [NonUnitalRing A] [NonUnitalRing B] [Module 𝕜 A] [Module 𝕜 B] [FunLike F A B]
    [NonUnitalAlgHomClass F 𝕜 A B] (φ : F) (a : A) :
    spectralRadius 𝕜 (φ a) ≤ spectralRadius 𝕜 a :=
  biSup_mono fun _ hk ↦ NonUnitalAlgHom.quasispectrum_apply_subset φ a hk

open Topology in
/-- If a closed set avoids the spectrum of an element of a complete normed algebra, it avoids the
spectra of all nearby elements: the spectrum is upper hemicontinuous. -/
theorem spectrum.eventually_disjoint_of_isClosed {𝕜 A : Type*} [NormedField 𝕜] [ProperSpace 𝕜]
    [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] {F : Set 𝕜} (hF : IsClosed F) {a : A}
    (h : Disjoint F (spectrum 𝕜 a)) : ∀ᶠ b in 𝓝 a, Disjoint F (spectrum 𝕜 b) := by
  have hmem : Fᶜ ∈ 𝓝ˢ (spectrum 𝕜 a) := hF.isOpen_compl.mem_nhdsSet.2 h.subset_compl_left
  filter_upwards [(upperHemicontinuous_spectrum 𝕜 A).upperHemicontinuousAt a _ hmem] with b hb
  exact Set.subset_compl_iff_disjoint_left.mp (subset_of_mem_nhdsSet hb)

/-- Every spectral value of a linear isometric equivalence of a Banach space has norm `1`. -/
theorem LinearIsometryEquiv.spectrum_subset_sphere {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] (e : E ≃ₗᵢ[𝕜] E) :
    spectrum 𝕜 (e : E →L[𝕜] E) ⊆ Metric.sphere 0 1 := by
  intro z hz
  have h1 : ‖(1 : E →L[𝕜] E)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have he : (e : E →L[𝕜] E) = e.toLinearIsometry.toContinuousLinearMap := rfl
  have hle : ‖z‖ ≤ 1 := (spectrum.norm_le_norm_mul_of_mem hz).trans <| by
    rw [he]
    simpa using mul_le_mul e.toLinearIsometry.norm_toContinuousLinearMap_le h1 (norm_nonneg _)
      zero_le_one
  let u : (E →L[𝕜] E)ˣ := (e : E ≃L[𝕜] E).toUnit
  have hzu : z ∈ spectrum 𝕜 (u : E →L[𝕜] E) := hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact u.zero_notMem_spectrum 𝕜 hzu
  have hinv : ((Units.mk0 z hz0)⁻¹ : 𝕜) ∈ spectrum 𝕜 (↑u⁻¹ : E →L[𝕜] E) :=
    (spectrum.inv_mem_iff (r := Units.mk0 z hz0) (a := u)).1 hzu
  have hinv_le : ‖z‖⁻¹ ≤ 1 := by
    have h : ‖((Units.mk0 z hz0)⁻¹ : 𝕜)‖ ≤ 1 := (spectrum.norm_le_norm_mul_of_mem hinv).trans <| by
      have hu_inv : (↑u⁻¹ : E →L[𝕜] E) = e.symm.toLinearIsometry.toContinuousLinearMap := rfl
      rw [hu_inv]
      simpa using mul_le_mul e.symm.toLinearIsometry.norm_toContinuousLinearMap_le h1
        (norm_nonneg _) zero_le_one
    simpa using h
  have hge : 1 ≤ ‖z‖ := (inv_le_one₀ (norm_pos_iff.2 hz0)).1 hinv_le
  exact mem_sphere_zero_iff_norm.2 (le_antisymm hle hge)
