/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.Basic
public import TauCeti.Geometry.Manifold.Instances.Quotient
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Manifolds from varying period lattices

A family `P : Y → (Λ →ₗ[ℤ] E)` of full discrete lattices in a finite-dimensional real
normed space `E`, indexed by a finite free lattice `Λ`, acts on `Y × E` by
`l +ᵥ (y, v) = (y, v + P y l)`. Coordinatewise continuity and injectivity make this a free,
properly discontinuous action. The standard orbit quotient carries Mathlib's quotient atlas,
packaged here as `TauCeti.torusFamilyChartedSpace` so that callers can install it using the
direct hypotheses on `P`.

If the individual periods are `C^n`, the total quotient is a `C^n` manifold and the orbit map
is a `C^n` local diffeomorphism and a covering map. The family projection to `Y` is `C^n`, as
is its zero section. In particular, over the complex numbers with `n = ∞`, the orbit map is
a local biholomorphism and the family projection and zero section are holomorphic. The family
projection and the orbit map are distinct maps: the latter has discrete fibres, whereas the
former has torus fibres.

The real normed-space structure on `E` supplies the full-lattice estimates and local compactness.
The regularity statements allow any normed scalar field on `E`; in particular a complex
normed space carries its usual restricted real structure.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Chapter 8 (families of complex tori given by period matrices).

The quotient atlas and its regularity are those of Mathlib's
`AddAction.instChartedSpaceQuotient` and `TauCeti.instIsManifoldAddQuotient`.
-/

public section

open Function
open scoped Manifold ContDiff

namespace TauCeti

section Translation

variable {𝕜 EY H Y Λ E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 EY H} [TopologicalSpace Y] [ChartedSpace H Y]
  [AddCommGroup Λ] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) {n : ℕ∞ω}

/-- Coordinatewise `C^n` periods give `C^n` period translations. No lattice or freeness
hypothesis is needed for this regularity statement. -/
theorem contMDiffConstVAdd_periodAddAction
    (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l) :
    letI := periodAddAction P
    ContMDiffConstVAdd (I.prod 𝓘(𝕜, E)) n Λ (Y × E) := by
  let _ := periodAddAction P
  refine ⟨fun l ↦ ?_⟩
  simp only [periodAddAction_vadd]
  exact contMDiff_fst.prodMk (contMDiff_snd.add ((hP l).comp contMDiff_fst))

end Translation

section Quotient

variable {Y Λ E : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y))

include hcont hinj in
/-- The period orbit map is a covering map. This conclusion uses uniform separation of periods
on compact parameter sets through `properlyDiscontinuousVAdd_periodAddAction`. -/
theorem isCoveringMap_torusFamilyQuotientMk :
    letI := periodAddAction P
    IsCoveringMap (Quotient.mk (AddAction.orbitRel Λ (Y × E))) := by
  let _ := periodAddAction P
  let _ := continuousConstVAdd_periodAddAction P hcont
  let _ := properlyDiscontinuousVAdd_periodAddAction P hcont hinj
  let _ := isCancelVAdd_periodAddAction P hinj
  exact (isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd
    (G := Λ) (E := Y × E)).isCoveringMap

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H Y]

/-- Mathlib's installed quotient atlas for a family of full period lattices. Install this
charted-space structure locally to use the regularity results for the family. -/
@[instance_reducible]
noncomputable def torusFamilyChartedSpace :
    letI := periodAddAction P
    ChartedSpace (ModelProd H E) (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := continuousConstVAdd_periodAddAction P hcont
  let _ := properlyDiscontinuousVAdd_periodAddAction P hcont hinj
  let _ := isCancelVAdd_periodAddAction P hinj
  exact AddAction.instChartedSpaceQuotient

end Quotient

section Regularity

variable {𝕜 EY H Y Λ E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EY] [NormedSpace 𝕜 EY] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 EY H} [TopologicalSpace Y] [ChartedSpace H Y]
  [T2Space Y] [LocallyCompactSpace Y]
  [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace 𝕜 E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]
  (hinj : ∀ y, Injective (P y)) {n : ℕ∞ω} [IsManifold I n Y]
  (hP : ∀ l, ContMDiff I 𝓘(𝕜, E) n fun y ↦ P y l)

/-- A `C^n` family of full discrete period lattices gives a `C^n` manifold on its standard
orbit quotient, with `torusFamilyChartedSpace` as its atlas. -/
theorem isManifold_torusFamilyQuotient :
    letI := periodAddAction P
    let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    IsManifold (I.prod 𝓘(𝕜, E)) n (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  let _ := continuousConstVAdd_periodAddAction P (fun l ↦ (hP l).continuous)
  let _ := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  let _ := isCancelVAdd_periodAddAction P hinj
  let _ := contMDiffConstVAdd_periodAddAction P hP
  exact instIsManifoldAddQuotient

/-- The orbit map of a `C^n` full period family is a `C^n` local diffeomorphism. Over `ℂ` at
order `∞` this is a local biholomorphism. -/
theorem isLocalDiffeomorph_torusFamilyQuotientMk :
    letI := periodAddAction P
    let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    IsLocalDiffeomorph (I.prod 𝓘(𝕜, E)) (I.prod 𝓘(𝕜, E)) n
      (Quotient.mk (AddAction.orbitRel Λ (Y × E))) := by
  let _ := periodAddAction P
  let _ := continuousConstVAdd_periodAddAction P (fun l ↦ (hP l).continuous)
  let _ := properlyDiscontinuousVAdd_periodAddAction P (fun l ↦ (hP l).continuous) hinj
  let _ := isCancelVAdd_periodAddAction P hinj
  let _ := contMDiffConstVAdd_periodAddAction P hP
  exact isLocalDiffeomorph_addQuotientMk

/-- The family projection is `C^n` because its pullback along the orbit covering is `Prod.fst`.
For holomorphic periods this gives a holomorphic map to the base. -/
theorem contMDiff_torusFamilyProjection :
    letI := periodAddAction P
    let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff (I.prod 𝓘(𝕜, E)) I n (torusFamilyProjection P) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  apply ((isLocalDiffeomorph_torusFamilyQuotientMk P hinj hP).contMDiff_comp_iff
    Quotient.mk_surjective le_rfl).mp
  simpa only [comp_def, torusFamilyProjection_mk] using
    (contMDiff_fst : ContMDiff (I.prod 𝓘(𝕜, E)) I n (Prod.fst : Y × E → Y))

/-- The zero section of the period family is `C^n`, and hence holomorphic for holomorphic
periods: it sends `y` to the orbit of `(y, 0)`. -/
theorem contMDiff_torusFamilyZeroSection :
    letI := periodAddAction P
    let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
    ContMDiff I (I.prod 𝓘(𝕜, E)) n
      (fun y : Y ↦ Quotient.mk (AddAction.orbitRel Λ (Y × E)) (y, (0 : E))) := by
  let _ := periodAddAction P
  let _ := torusFamilyChartedSpace (H := H) P (fun l ↦ (hP l).continuous) hinj
  exact (isLocalDiffeomorph_torusFamilyQuotientMk P hinj hP).contMDiff.comp
    (contMDiff_id.prodMk contMDiff_const)

end Regularity

end TauCeti
