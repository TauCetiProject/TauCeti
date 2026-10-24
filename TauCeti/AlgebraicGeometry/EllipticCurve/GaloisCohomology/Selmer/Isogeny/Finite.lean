/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
-- Proof-only: finiteness of the Selmer group with conditions at the finite completions.
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Finite

/-!
# Isogeny invariance of finiteness of the Shafarevich–Tate group

For elliptic curves over a number field, an isogeny induces a map on Shafarevich–Tate groups
with finite kernel. Consequently one group is finite if and only if the other is finite.
The results cover local triviality at finite places alone as well as at every place,
including the real and complex places.

The dual composite kills the kernel by the degree. Degree-torsion in the group defined using
only finite places is already finite: it is a quotient of the finite degree-Selmer group.
The all-place kernel embeds in this finite group, without omitting any archimedean condition.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, X.4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. reine angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve ContCohomology GlobalNumberFields IsDedekindDomain
open scoped NumberField

variable {K : Type*} [Field K] [NumberField K] {W₁ W₂ : WeierstrassCurve K}
  [W₁.IsElliptic] [W₂.IsElliptic]

section FinitePlaces

variable (τ : ∀ v : HeightOneSpectrum (𝓞 K),
  SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))

/-- The torsion in Sha defined using the finite places is finite for every nonzero degree. -/
theorem finite_torsionBy_shafarevichTateGroup_finitePlaces (n : ℕ) [NeZero n] :
    Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) n) := by
  have := W₁.finite_selmerGroup n τ
  exact Finite.of_surjective (W₁.selmerShaMap τ n)
    (W₁.selmerShaMap_surjective τ (isUnit_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (NeZero.ne n))))

/-- A nonzero morphism has finite kernel on Sha defined using the finite places. -/
theorem finite_ker_shafarevichTateMap_finitePlaces
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (f.shafarevichTateMap τ).ker := by
  have : NeZero f.degree := ⟨fun h ↦ hf ((degree_eq_zero_iff f).mp h)⟩
  have := finite_torsionBy_shafarevichTateGroup_finitePlaces (W₁ := W₁) τ f.degree
  exact Finite.of_injective
    (AddSubgroup.inclusion (f.ker_shafarevichTateMap_le_torsionBy τ))
    (AddSubgroup.inclusion_injective _)

/-- If the target Sha defined using finite places is finite, so is the source Sha of a
nonzero morphism over a number field. -/
theorem finite_shafarevichTateGroup_of_finite_finitePlaces
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    [Finite (W₂.shafarevichTateGroup τ)] : Finite (W₁.shafarevichTateGroup τ) := by
  have := f.finite_ker_shafarevichTateMap_finitePlaces τ hf
  exact (f.shafarevichTateMap τ).finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

variable {τ} in
/-- Finiteness of Sha defined using the finite places is invariant under a nonzero isogeny. -/
theorem finite_shafarevichTateGroup_iff_finitePlaces
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (W₁.shafarevichTateGroup τ) ↔ Finite (W₂.shafarevichTateGroup τ) := by
  constructor
  · intro h
    exact f.dual.finite_shafarevichTateGroup_of_finite_finitePlaces τ
      (dual_eq_zero_iff.not.mpr hf)
  · intro h
    exact f.finite_shafarevichTateGroup_of_finite_finitePlaces τ hf

end FinitePlaces

variable
  (τ : ∀ v : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

/-- Over a number field the map on Shafarevich–Tate groups induced by a nonzero morphism
has finite kernel. Local conditions are taken at all finite and infinite places. -/
theorem finite_ker_shafarevichTateMap (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (f.shafarevichTateMap τ).ker := by
  have : NeZero f.degree := ⟨fun h ↦ hf ((degree_eq_zero_iff f).mp h)⟩
  have := finite_torsionBy_shafarevichTateGroup_finitePlaces (W₁ := W₁)
    (fun v ↦ τ (.inl v)) f.degree
  have : Finite (AddSubgroup.torsionBy (W₁.shafarevichTateGroup τ) f.degree) :=
    Finite.of_injective (shafarevichTateTorsionInclusion (W := W₁) τ Sum.inl f.degree)
      (shafarevichTateTorsionInclusion_injective (W := W₁) τ Sum.inl f.degree)
  exact Finite.of_injective
    (AddSubgroup.inclusion (f.ker_shafarevichTateMap_le_torsionBy τ))
    (AddSubgroup.inclusion_injective _)

/-- If the target Shafarevich–Tate group is finite, so is the source group of a nonzero
morphism over a number field, with local triviality required at every place. -/
theorem finite_shafarevichTateGroup_of_finite (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    [Finite (W₂.shafarevichTateGroup τ)] : Finite (W₁.shafarevichTateGroup τ) := by
  have := f.finite_ker_shafarevichTateMap τ hf
  exact (f.shafarevichTateMap τ).finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩

variable {τ} in
/-- **Isogeny invariance of finiteness of the Shafarevich–Tate group** over a number field,
with local triviality required at every place. -/
theorem finite_shafarevichTateGroup_iff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite (W₁.shafarevichTateGroup τ) ↔ Finite (W₂.shafarevichTateGroup τ) := by
  constructor
  · intro h
    exact f.dual.finite_shafarevichTateGroup_of_finite τ (dual_eq_zero_iff.not.mpr hf)
  · intro h
    exact f.finite_shafarevichTateGroup_of_finite τ hf

end TauCeti.Isogeny.Hom

end
