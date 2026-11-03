/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Sphere
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel

/-!
# Smooth closed disc bundles

The closed disc bundle of a positive smooth radius in a real Riemannian vector bundle
is a manifold with boundary. Its manifold boundary consists exactly of the vectors whose
length equals the radius, and its manifold interior consists of the shorter vectors.
This supplies the intrinsic manifold-with-boundary structure on normal discs used in
removing tubular neighbourhoods.

The atlas is transported from the regular sublevel of `sphereBundleEquation`, using the
original topology and smooth structure of the total space. No orthonormal frame,
compactness, or triviality of the bundle is required. The total dimension is written as
`d + 1` to specify the half-space model; zero-dimensional total spaces are not covered.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Proposition 5.47
  (regular domains) and Theorem 6.24 (tubular neighbourhoods).
* M. W. Hirsch, *Differential Topology*, Chapter 4, Theorem 6.3.
-/

public noncomputable section

open Bundle Function Set Manifold
open scoped Manifold ContDiff

namespace TauCeti

variable {B : Type*} {V : B → Type*} {F : Type*}
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [TopologicalSpace B]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [ChartedSpace H B] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [I.Boundaryless] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {n : ℕ∞ω} [IsManifold I n B] [ContMDiffVectorBundle n F V I]
  [IsContMDiffRiemannianBundle I n F V]
  {r : B → ℝ} {d : ℕ}

/-- Identify the closed disc bundle with the regular sublevel, without changing points. -/
private def discSublevelHomeomorph (hrpos : ∀ b, 0 < r b) :
    {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} ≃ₜ
      {p : TotalSpace F V // sphereBundleEquation r p ≤ 0} :=
  Homeomorph.setCongr
    (s := {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj})
    (t := {p : TotalSpace F V | sphereBundleEquation r p ≤ 0})
    (Set.ext fun p => (sphereBundleEquation_le_zero_iff r p (hrpos p.proj).le).symm)

/-- The closed disc bundle with positive `C^n` radius, endowed with its regular-sublevel atlas.
Install this atlas locally. The half-space model has the same dimension as the total space. -/
@[instance_reducible]
def discBundleChartedSpace (hr : ContMDiff I 𝓘(ℝ) n r) (hn : 1 ≤ n)
    (hrpos : ∀ b, 0 < r b) (hdim : Module.finrank ℝ (E × F) = d + 1) :
    ChartedSpace (EuclideanHalfSpace (d + 1))
      {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let := scalarRegularSublevelChartedSpace
    ((contMDiff_sphereBundleEquation hr).of_le hn) hreg hdim
  exact (discSublevelHomeomorph (F := F) (V := V) hrpos).pullbackChartedSpace

omit [IsManifold I n B] [ContMDiffVectorBundle n F V I] in
/-- Preferred disc-bundle charts are the regular-sublevel charts, with the norm inequality
replaced by the equivalent squared-norm inequality. The set congruence preserves points.
Use this with `rw`: the general pullback-chart simp lemma rewrites the left-hand side first. -/
theorem discBundleChartedSpace_chartAt (hr : ContMDiff I 𝓘(ℝ) n r) (hn : 1 ≤ n)
    (hrpos : ∀ b, 0 < r b) (hdim : Module.finrank ℝ (E × F) = d + 1)
    (p : {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj}) :
    letI : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
    let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
      (hr.of_le hn) (fun b => (hrpos b).ne')
    let e := Homeomorph.setCongr
      (s := {p : TotalSpace F V | ‖p.2‖ ≤ r p.proj})
      (t := {p : TotalSpace F V | sphereBundleEquation r p ≤ 0})
      (Set.ext fun p => (sphereBundleEquation_le_zero_iff r p (hrpos p.proj).le).symm)
    @chartAt (EuclideanHalfSpace (d + 1)) _ _ _
      (discBundleChartedSpace hr hn hrpos hdim) p =
      e.transOpenPartialHomeomorph (scalarRegularSublevelChartAt
        ((contMDiff_sphereBundleEquation hr).of_le hn) hreg hdim (e p)) := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let := scalarRegularSublevelChartedSpace
    ((contMDiff_sphereBundleEquation hr).of_le hn) hreg hdim
  unfold discBundleChartedSpace
  rw [Homeomorph.pullbackChartedSpace_chartAt, scalarRegularSublevelChartedSpace_chartAt]
  -- The private homeomorphism is precisely this set congruence.
  rfl

/-- A positive-radius closed disc bundle is a manifold with boundary of the total dimension. -/
theorem isManifold_discBundle (hr : ContMDiff I 𝓘(ℝ) n r) (hn : 1 ≤ n)
    (hrpos : ∀ b, 0 < r b) (hdim : Module.finrank ℝ (E × F) = d + 1) :
    letI := discBundleChartedSpace (F := F) (V := V) hr hn hrpos hdim
    IsManifold (𝓡∂ (d + 1)) n {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let := scalarRegularSublevelChartedSpace
    ((contMDiff_sphereBundleEquation hr).of_le hn) hreg hdim
  have := isManifold_scalarRegularSublevel hreg hdim hn (contMDiff_sphereBundleEquation hr)
  exact (discSublevelHomeomorph (F := F) (V := V) hrpos).pullback_isManifold _ n

/-- The manifold boundary of the closed disc bundle is exactly its sphere bundle. -/
theorem boundary_discBundle (hr : ContMDiff I 𝓘(ℝ) n r) (hn : 1 ≤ n)
    (hrpos : ∀ b, 0 < r b) (hdim : Module.finrank ℝ (E × F) = d + 1) :
    letI := discBundleChartedSpace (F := F) (V := V) hr hn hrpos hdim
    (𝓡∂ (d + 1)).boundary {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} =
      {p : {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} | ‖p.1.2‖ = r p.1.proj} := by
  let : IsContMDiffRiemannianBundle I 1 F V := .of_le hn
  let hreg := isRegularValue_sphereBundleEquation (F := F) (V := V)
    (hr.of_le hn) (fun b => (hrpos b).ne')
  let := scalarRegularSublevelChartedSpace
    ((contMDiff_sphereBundleEquation hr).of_le hn) hreg hdim
  have := isManifold_scalarRegularSublevel hreg hdim hn (contMDiff_sphereBundleEquation hr)
  let e := discSublevelHomeomorph (F := F) (V := V) hrpos
  let := e.pullbackChartedSpace (H := EuclideanHalfSpace (d + 1))
  have := e.pullback_isManifold (𝓡∂ (d + 1)) n
  rw [← (e.pullbackDiffeomorph (𝓡∂ (d + 1)) n).preimage_boundary
    (ENat.one_le_iff_ne_zero_withTop.mp hn)]
  -- Restate the sublevel boundary using the explicit subtype in the homeomorphism's codomain.
  have hb : (𝓡∂ (d + 1)).boundary
      {p : TotalSpace F V // sphereBundleEquation r p ≤ 0} =
      {p : {p : TotalSpace F V // sphereBundleEquation r p ≤ 0} |
        sphereBundleEquation r p.1 = 0} :=
    boundary_scalarRegularSublevel hreg hdim hn (contMDiff_sphereBundleEquation hr)
  rw [hb, Homeomorph.coe_pullbackDiffeomorph]
  ext p
  -- Set congruence preserves the total-space point; only its sublevel proof changes.
  exact sphereBundleEquation_eq_zero_iff r p.1 (hrpos p.1.proj).le

/-- The manifold interior of the closed disc bundle is exactly its open disc bundle. -/
theorem interior_discBundle (hr : ContMDiff I 𝓘(ℝ) n r) (hn : 1 ≤ n)
    (hrpos : ∀ b, 0 < r b) (hdim : Module.finrank ℝ (E × F) = d + 1) :
    letI := discBundleChartedSpace (F := F) (V := V) hr hn hrpos hdim
    (𝓡∂ (d + 1)).interior {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} =
      {p : {p : TotalSpace F V // ‖p.2‖ ≤ r p.proj} | ‖p.1.2‖ < r p.1.proj} := by
  let := discBundleChartedSpace (F := F) (V := V) hr hn hrpos hdim
  rw [← ModelWithCorners.compl_boundary, boundary_discBundle hr hn hrpos hdim]
  ext p
  have hp : ‖p.1.2‖ ≤ r p.1.proj := p.2
  simp only [mem_compl_iff, mem_ofPred_eq]
  exact ⟨hp.lt_of_ne, ne_of_lt⟩

end TauCeti
