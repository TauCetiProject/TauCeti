/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.Basic
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ProjectiveLine
import Mathlib.RingTheory.Polynomial.Ideal

/-!
# The projective compactification of the affine line

The standard chart `D₊(X₀)` realizes `Spec R[X]` as a schematically dense open subscheme of
`ℙ¹_R` for every commutative ring `R`. Together with the proper structure morphism this gives
`projectiveLine.denseCompactification`, retaining the scheme structure over nonreduced bases.

The complement is the image of the infinity section `Spec R ⟶ ℙ¹_R`, obtained by setting the
coordinate of the other chart to zero. Over a field it consists of the single point `infinity`.

The construction uses the polynomial chart equivalences of
`TauCeti.AlgebraicGeometry.projectiveLine` and the homogeneous-nonzerodivisor criterion
`AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
-/

public section

open CategoryTheory AlgebraicGeometry Polynomial

universe u

namespace TauCeti.AlgebraicGeometry.projectiveLine

variable (R : Type u) [CommRing R]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule R (Fin 2 → R)

/-- The projective line compactifies the affine line over any commutative base ring. -/
-- The selected ambient carrier must reduce to use its two maps without transports.
@[expose, implicit_reducible]
noncomputable def denseCompactification :
    DenseCompactification (Spec.map (CommRingCat.ofHom (algebraMap R R[X]))) :=
  ⟨Compactification.ofHom (polynomialChartι R 0) (projectiveLine R ↘ Spec (.of R))
    (polynomialChartι_over R 0), (denseCompactificationProperty_iff _ _).mpr inferInstance⟩

/-- The ambient scheme of the affine-line compactification is the projective line. -/
@[simp]
theorem denseCompactification_Xbar : (denseCompactification R).obj.Xbar = projectiveLine R :=
  (rfl)

/-- The interior map of the affine-line compactification is the zeroth polynomial chart. -/
@[simp]
theorem denseCompactification_j :
    (denseCompactification R).obj.j = polynomialChartι R 0 :=
  (rfl)

/-- The proper map of the affine-line compactification is the projective structure map. -/
@[simp]
theorem denseCompactification_p :
    (denseCompactification R).obj.p = (projectiveLine R ↘ Spec (.of R)) :=
  (rfl)

/-- The infinity section of the projective line, given by the zero point of the chart
`D₊(X₁)`, with homogeneous coordinates `[0 : 1]`. -/
noncomputable def infinitySection : Spec (.of R) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ polynomialChartι R 1

/-- The infinity section factors through the zero section of the opposite polynomial chart. -/
theorem infinitySection_eq : infinitySection R =
    Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) ≫ polynomialChartι R 1 :=
  (rfl)

/-- The point at infinity is a section over the base ring. -/
@[simp]
theorem infinitySection_over :
    infinitySection R ≫ (projectiveLine R ↘ Spec (.of R)) = 𝟙 _ := by
  rw [infinitySection, Category.assoc, polynomialChartι_over, ← Spec.map_comp]
  rw [← Spec.map_id (.of R)]
  congr 1
  ext c
  simp

instance : IsClosedImmersion (infinitySection R) := by
  have : IsClosedImmersion (infinitySection R ≫ (projectiveLine R ↘ Spec (.of R))) := by
    rw [infinitySection_over]
    infer_instance
  exact IsClosedImmersion.of_comp _ (projectiveLine R ↘ Spec (.of R))

/-- The boundary of the affine-line chart is precisely the infinity section, over any base ring. -/
theorem range_infinitySection :
    Set.range (infinitySection R) = (Set.range (polynomialChartι R 0))ᶜ := by
  have hz : Set.range (Spec.map (CommRingCat.ofHom (evalRingHom (0 : R)))) =
      {q : Spec (.of R[X]) | X ∈ q.asIdeal} := by
    -- On affine spectra the scheme map is the prime-ideal comap.
    change Set.range (PrimeSpectrum.comap (evalRingHom (0 : R))) = _
    rw [range_comap_of_surjective _ _ (eval_surjective (0 : R)), ker_evalRingHom]
    ext q
    simp [PrimeSpectrum.mem_zeroLocus]
    rfl
  have hpre : polynomialChartι R 1 ⁻¹ᵁ Proj.basicOpen 𝒜 (coord R 0) =
      PrimeSpectrum.basicOpen (X : R[X]) :=
    polynomialChartι_preimage_basicOpen_rev R 1
  have hi (q : Spec (.of R[X])) :
      polynomialChartι R 1 q ∈ Set.range (polynomialChartι R 0) ↔ X ∉ q.asIdeal := by
    -- Membership in the image of an open immersion is membership in its open range.
    change polynomialChartι R 1 q ∈ (polynomialChartι R 0).opensRange ↔ _
    rw [opensRange_polynomialChartι]
    -- Pull back the projective basic open to use the chart-overlap equation.
    change q ∈ polynomialChartι R 1 ⁻¹ᵁ Proj.basicOpen 𝒜 (coord R 0) ↔ _
    rw [hpre]
    rfl
  have hc (p : projectiveLine R) :
      p ∈ Set.range (polynomialChartι R 0) ∨ p ∈ Set.range (polynomialChartι R 1) := by
    -- Express the two set-theoretic ranges as opens to apply the chart covering equation.
    change p ∈ (polynomialChartι R 0).opensRange ∨ p ∈ (polynomialChartι R 1).opensRange
    rw [opensRange_polynomialChartι, opensRange_polynomialChartι]
    have hp : p ∈ (⊤ : (projectiveLine R).Opens) := trivial
    rwa [← basicOpen_coord_sup_eq_top R, TopologicalSpace.Opens.mem_sup] at hp
  ext p
  constructor
  · rintro ⟨q, rfl⟩ hp
    have hq : X ∈ (Spec.map (CommRingCat.ofHom (evalRingHom (0 : R))) q).asIdeal := by
      exact ((Set.ext_iff.mp hz) _).mp ⟨q, rfl⟩
    apply (hi _).mp ?_ hq
    simpa only [infinitySection, Scheme.Hom.comp_apply] using hp
  · intro hp
    obtain ⟨q, rfl⟩ := (hc p).resolve_left hp
    have hq : X ∈ q.asIdeal := not_not.mp (fun hn ↦ hp ((hi q).mpr hn))
    obtain ⟨r, hr⟩ := ((Set.ext_iff.mp hz) q).mpr hq
    exact ⟨r, by simp only [infinitySection, Scheme.Hom.comp_apply, hr]⟩

variable (K : Type u) [Field K]

/-- The point `[0 : 1]` at infinity on the projective line over a field. -/
noncomputable def infinity : projectiveLine K := infinitySection K default

/-- Over a field the affine-line compactification has exactly one boundary point. -/
theorem compl_range_polynomialChartι :
    (Set.range (polynomialChartι K 0))ᶜ = {infinity K} := by
  rw [← range_infinitySection]
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact congrArg (infinitySection K) (Subsingleton.elim q default)
  · rintro rfl
    exact ⟨default, rfl⟩

/-- The affine-line chart misses the point at infinity. -/
@[simp↓]
theorem infinity_not_mem_range_polynomialChartι :
    infinity K ∉ Set.range (polynomialChartι K 0) := by
  have : infinity K ∈ (Set.range (polynomialChartι K 0))ᶜ := by
    rw [compl_range_polynomialChartι]
    exact Set.mem_singleton _
  exact this

end TauCeti.AlgebraicGeometry.projectiveLine
