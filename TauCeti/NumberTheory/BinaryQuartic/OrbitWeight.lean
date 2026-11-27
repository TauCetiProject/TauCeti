/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Projective
public import TauCeti.GroupTheory.GroupAction.Orbit.Weight
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ProjGenLinGroup.ProjectiveImage

/-!
# Integral orbit weights of binary quartics

For a coefficient inclusion such as `ℤ → ℚ` or `ℤ_p → ℚ_p`, the integral orbit weight
counts right cosets of the integral projective group whose translate has integral coefficients.
These are the global and local weights in Bhargava and Shankar's count of two-coverings.

## References

* M. Bhargava and A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), §3.2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti.BinaryQuartic

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Quartics over `S` that arise by mapping the coefficients of a quartic over `R`. -/
def coefficientRange (φ : R →+* S) : Set (BinaryQuartic S) :=
  Set.range (Pi.map fun _ : Fin 5 ↦ (φ : R → S))

/-- The coefficient range is the image of the coefficientwise map on quartics. -/
theorem coefficientRange_eq_range (φ : R →+* S) :
    coefficientRange φ = Set.range (fun f : BinaryQuartic R ↦ φ ∘ f) :=
  (rfl)

/-- A quartic lies in the coefficient range exactly when each coefficient lifts. -/
theorem mem_coefficientRange {φ : R →+* S} {f : BinaryQuartic S} :
    f ∈ coefficientRange φ ↔ ∀ i, f i ∈ Set.range φ := by
  simp [coefficientRange, Set.range_piMap]

/-- Mapping a quartic coefficientwise produces a member of the coefficient range. -/
@[simp] theorem comp_mem_coefficientRange (φ : R →+* S) (f : BinaryQuartic R) :
    φ ∘ f ∈ coefficientRange φ :=
  ⟨f, rfl⟩

/-- Projective transformations coming from the source ring preserve the coefficient range. -/
@[simp] theorem smul_mem_coefficientRange_iff {φ : R →+* S} {g : PGL(2, S)}
    (hg : g ∈ (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage) (f : BinaryQuartic S) :
    g • f ∈ coefficientRange φ ↔ f ∈ coefficientRange φ := by
  have stable : ∀ {h : PGL(2, S)}, h ∈ (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage →
      ∀ {q : BinaryQuartic S}, q ∈ coefficientRange φ → h • q ∈ coefficientRange φ := by
    intro h hh q hq
    obtain ⟨g, rfl⟩ := (MonoidHom.mem_projectiveImage _).mp hh
    rw [coefficientRange_eq_range] at hq
    obtain ⟨f, rfl⟩ := hq
    rw [← ProjGenLinGroup.map_mk, projGenLinGroup_map_smul_comp]
    exact comp_mem_coefficientRange _ _
  exact ⟨fun h ↦ by simpa using stable (Subgroup.inv_mem _ hg) h, stable hg⟩

/-- The integral orbit weight relative to a coefficient map. For `ℤ → ℚ` it is the global
weight, and for `ℤ_p → ℚ_p` it is the local weight. An infinite coset set has weight zero. -/
noncomputable def integralOrbitWeight (f : BinaryQuartic S) (φ : R →+* S) : ℕ :=
  (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage.orbitWeight (coefficientRange φ) f

/-- The integral orbit weight counts right cosets carrying the quartic into the coefficient
range. -/
theorem integralOrbitWeight_def (f : BinaryQuartic S) (φ : R →+* S) :
    f.integralOrbitWeight φ =
      (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage.orbitWeight (coefficientRange φ) f :=
  (rfl)

/-- Integral orbit weights are constant on projective orbits over the target ring. -/
@[simp] theorem integralOrbitWeight_smul (f : BinaryQuartic S) (φ : R →+* S)
    (g : PGL(2, S)) : (g • f).integralOrbitWeight φ = f.integralOrbitWeight φ := by
  simp only [integralOrbitWeight_def, Subgroup.orbitWeight_smul]

/-- The weight of an integral form is one exactly when all its integral translates
come from the source projective group. -/
theorem integralOrbitWeight_eq_one_iff {φ : R →+* S} {f : BinaryQuartic S}
    (hf : f ∈ coefficientRange φ) :
    f.integralOrbitWeight φ = 1 ↔
      {g : PGL(2, S) | g • f ∈ coefficientRange φ} =
        (GeneralLinearGroup.map (n := Fin 2) φ).projectiveImage := by
  rw [integralOrbitWeight_def, Subgroup.orbitWeight_eq_one_iff_eq
    (fun g hg f hf ↦ (smul_mem_coefficientRange_iff hg f).mpr hf) hf]

end TauCeti.BinaryQuartic
