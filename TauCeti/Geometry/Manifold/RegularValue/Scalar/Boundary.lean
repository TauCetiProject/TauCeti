/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Diffeomorph.ChartLinear
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel

/-!
# The boundary of a regular sublevel is the regular level

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. The sublevel `{f ≤ a}` is a manifold with
boundary for its atlas `TauCeti.scalarRegularSublevelChartedSpace`, and its manifold boundary is
the level `f⁻¹(a)` as a set (`TauCeti.boundary_scalarRegularSublevel`). The boundary therefore
carries two manifold structures on the same points: the boundary atlas
`TauCeti.boundaryChartedSpace`, modelled on `EuclideanSpace ℝ (Fin n)`, and the atlas
`TauCeti.regularLevelChartedSpace` of the regular level `{x // f x = a}`, modelled on
`Fin n → ℝ`. This file shows that they agree.

The identity of points is a homeomorphism `TauCeti.scalarRegularSublevelBoundaryHomeomorph`
between the boundary and the level. Both atlases are read from the same coordinates: the face
chart of the sublevel at a point `p` of the level has the tangential coordinates of the level chart
at `p` in its slots `1, …, n`, and the boundary chart at `p` is the face chart with slot `0`
deleted. So, on the source of the boundary chart at `p`, the boundary chart and the level chart
differ only by the identification `EuclideanSpace.equiv` of `EuclideanSpace ℝ (Fin n)` with
`Fin n → ℝ`
(`TauCeti.euclideanSpaceEquiv_chartAt_scalarRegularSublevelBoundary_eq_regularLevelChartAt`). In
particular, the homeomorphism is a diffeomorphism for the two atlases
(`TauCeti.scalarRegularSublevelBoundaryDiffeomorph`). Since it reads as a linear map in the
preferred charts, it is `C^k` for every `k` in the sense of these atlases; both are `C^m` manifolds
when `f` is `C^m`.

The same holds for a band `f⁻¹([a, b])` between regular values `a < b`: its manifold boundary,
for the atlas `TauCeti.scalarRegularBandChartedSpace`, is diffeomorphic to the disjoint union of
the levels `f⁻¹(a)` and `f⁻¹(b)` (`TauCeti.scalarRegularBandBoundaryDiffeomorph`).

No compactness and no assumption on the critical points of `f` away from the levels are used.

## Main declarations

* `TauCeti.scalarRegularSublevelBoundaryHomeomorph`: the boundary of the sublevel `{f ≤ a}` is
  homeomorphic to the level `f⁻¹(a)`, by the identity of points.
* `TauCeti.euclideanSpaceEquiv_chartAt_scalarRegularSublevelBoundary_eq_regularLevelChartAt`: the
  boundary charts are the level charts, read through `EuclideanSpace.equiv`.
* `TauCeti.scalarRegularSublevelBoundaryDiffeomorph`: the boundary of the sublevel is
  diffeomorphic to the level.
* `TauCeti.scalarRegularBandBoundaryHomeomorph`,
  `TauCeti.euclideanSpaceEquiv_chartAt_scalarRegularBandBoundary_eq_chartAt` and
  `TauCeti.scalarRegularBandBoundaryDiffeomorph`: the same for the boundary of a band and the
  disjoint union of its two levels.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains, with boundary the
  level).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
-/

public section

open Function Module Set Topology
open scoped ContDiff Manifold Topology

namespace TauCeti

/-- The dimension of the levels of a real function on a model space `E` of dimension `n + 1`. -/
theorem finrank_sub_finrank_real_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {n : ℕ}
    (hn : finrank ℝ E = n + 1) : finrank ℝ E - finrank ℝ ℝ = n := by
  rw [finrank_self]
  omega

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a : ℝ}
  {n : ℕ} [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I 1 M]

section Sublevel

variable (hf : ContMDiff I 𝓘(ℝ) 1 f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
  (hn : finrank ℝ E = n + 1)

/-- The manifold boundary of the sublevel `{f ≤ a}` at a regular value `a`, for its preferred atlas
`TauCeti.scalarRegularSublevelChartedSpace`, is homeomorphic to the level `f⁻¹(a)` by the identity
of points. -/
noncomputable def scalarRegularSublevelBoundaryHomeomorph :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}) ≃ₜ {x : M // f x = a} := by
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  have hB := boundary_scalarRegularSublevel hreg hn le_rfl hf
  have h₁ (q : ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a})) : f q.1.1 = a := by simpa [hB] using q.2
  have h₂ (y : {x : M // f x = a}) :
      (⟨y.1, le_of_eq y.2⟩ : {x | f x ≤ a}) ∈ (𝓡∂ (n + 1)).boundary {x | f x ≤ a} := by
    rw [hB]
    exact y.2
  exact
  { toFun q := ⟨q.1.1, h₁ q⟩
    invFun y := ⟨⟨y.1, le_of_eq y.2⟩, h₂ y⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk h₁
    continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk h₂ }

/-- `TauCeti.scalarRegularSublevelBoundaryHomeomorph` is the identity on underlying points. -/
@[simp]
theorem coe_scalarRegularSublevelBoundaryHomeomorph_apply
    (q : letI := scalarRegularSublevelChartedSpace hf hreg hn
      ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a})) :
    (scalarRegularSublevelBoundaryHomeomorph hf hreg hn q : M) = q.1.1 :=
  (rfl)

/-- The inverse of `TauCeti.scalarRegularSublevelBoundaryHomeomorph` is the identity on underlying
points. -/
@[simp]
theorem coe_scalarRegularSublevelBoundaryHomeomorph_symm_apply (y : {x : M // f x = a}) :
    ((scalarRegularSublevelBoundaryHomeomorph hf hreg hn).symm y).1.1 = y.1 :=
  (rfl)

/-- **The boundary charts of a regular sublevel are the level charts.** On the source of the
preferred boundary chart at a point `p` of the boundary of the sublevel `{f ≤ a}`, that chart, read
in `Fin n → ℝ` through `EuclideanSpace.equiv`, is the preferred chart
`TauCeti.regularLevelChartAt` of the level `f⁻¹(a)` at `p`. -/
theorem euclideanSpaceEquiv_chartAt_scalarRegularSublevelBoundary_eq_regularLevelChartAt
    (p q : letI := scalarRegularSublevelChartedSpace hf hreg hn
      ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}))
    (hq : letI := scalarRegularSublevelChartedSpace hf hreg hn
      haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
      q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) =
      regularLevelChartAt (fun _ _ ↦ hf.contMDiffAt) hreg (finrank_sub_finrank_real_eq hn)
        (scalarRegularSublevelBoundaryHomeomorph hf hreg hn p)
        (scalarRegularSublevelBoundaryHomeomorph hf hreg hn q) := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  have hp : f p.1.1 = a := (scalarRegularSublevelBoundaryHomeomorph hf hreg hn p).2
  have hqa : f q.1.1 = a := (scalarRegularSublevelBoundaryHomeomorph hf hreg hn q).2
  rw [boundaryChartedSpace_chartAt_source, mem_preimage,
    scalarRegularSublevelChartedSpace_chartAt] at hq
  -- The face chart lemma reads the level chart in dimension `dim E - 1`; identify `n` with it.
  obtain rfl : n = finrank ℝ E - 1 := by omega
  ext i
  rw [boundaryChartedSpace_chartAt_apply, scalarRegularSublevelChartedSpace_chartAt]
  simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply,
    EuclideanHalfSpace.boundaryProj_apply]
  rw [scalarRegularSublevelChartAt_apply_succ_eq_regularLevelChartAt hf hreg hn hp hq hqa i,
    Fin.cast_eq_self]
  -- By construction, the homeomorphism sends `q` to `⟨q.1.1, hqa⟩`.
  rfl

/-- **The boundary of a regular sublevel is diffeomorphic to the level.** The identity of points
`TauCeti.scalarRegularSublevelBoundaryHomeomorph` is a diffeomorphism of every smoothness `k`
between the manifold boundary of the sublevel `{f ≤ a}`, with its boundary atlas modelled on
`EuclideanSpace ℝ (Fin n)`, and the level `f⁻¹(a)`, with its atlas
`TauCeti.regularLevelChartedSpace` modelled on `Fin n → ℝ`. In the preferred charts it is the
linear identification `EuclideanSpace.equiv`. -/
noncomputable def scalarRegularSublevelBoundaryDiffeomorph (k : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hreg
      (finrank_sub_finrank_real_eq hn)
    ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}) ≃ₘ^k⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, Fin n → ℝ)⟯
      {x : M // f x = a} :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hreg (finrank_sub_finrank_real_eq hn)
  (scalarRegularSublevelBoundaryHomeomorph hf hreg hn).toDiffeomorphOfChartAt
    (EuclideanSpace.equiv (Fin n) ℝ) (fun p ↦ Filter.eventually_of_mem
      ((chartAt _ p).open_source.mem_nhds (mem_chart_source _ p)) fun q hq ↦ by
        rw [regularLevelChartedSpace_chartAt,
          euclideanSpaceEquiv_chartAt_scalarRegularSublevelBoundary_eq_regularLevelChartAt hf hreg
            hn p q hq]) k

/-- The underlying map of `TauCeti.scalarRegularSublevelBoundaryDiffeomorph` is
`TauCeti.scalarRegularSublevelBoundaryHomeomorph`. -/
@[simp]
theorem coe_scalarRegularSublevelBoundaryDiffeomorph (k : ℕ∞ω) :
    ⇑(scalarRegularSublevelBoundaryDiffeomorph hf hreg hn k) =
      scalarRegularSublevelBoundaryHomeomorph hf hreg hn := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hreg (finrank_sub_finrank_real_eq hn)
  exact Homeomorph.coe_toDiffeomorphOfChartAt _ _ _ k

/-- The underlying homeomorphism of `TauCeti.scalarRegularSublevelBoundaryDiffeomorph` is
`TauCeti.scalarRegularSublevelBoundaryHomeomorph`. -/
@[simp]
theorem toHomeomorph_scalarRegularSublevelBoundaryDiffeomorph (k : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    haveI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hreg
      (finrank_sub_finrank_real_eq hn)
    (scalarRegularSublevelBoundaryDiffeomorph hf hreg hn k).toHomeomorph =
      scalarRegularSublevelBoundaryHomeomorph hf hreg hn := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  have := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hreg (finrank_sub_finrank_real_eq hn)
  exact Homeomorph.toHomeomorph_toDiffeomorphOfChartAt _ _ _ k

end Sublevel

section Band

variable {b : ℝ} (hf : ContMDiff I 𝓘(ℝ) 1 f) (hn : finrank ℝ E = n + 1)
  (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- The manifold boundary of the band `f⁻¹([a, b])` between regular values `a < b`, for its
preferred atlas `TauCeti.scalarRegularBandChartedSpace`, is homeomorphic to the disjoint union of
the levels `f⁻¹(a)` and `f⁻¹(b)`, by the identity of points. -/
noncomputable def scalarRegularBandBoundaryHomeomorph :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ≃ₜ {x : M // f x = a} ⊕ {x : M // f x = b} := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  have hB := boundary_scalarRegularBand hn ha hb le_rfl hf hab
  have hmem (q : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) : f q.1.1 = a ∨ f q.1.1 = b := by
    simpa [hB] using q.2
  have hIa (y : {x : M // f x = a}) : y.1 ∈ f ⁻¹' Icc a b := by
    simp [y.2, hab.le]
  have hIb (y : {x : M // f x = b}) : y.1 ∈ f ⁻¹' Icc a b := by
    simp [y.2, hab.le]
  have hBa (y : {x : M // f x = a}) :
      (⟨y.1, hIa y⟩ : f ⁻¹' Icc a b) ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [hB]
    exact Or.inl y.2
  have hBb (y : {x : M // f x = b}) :
      (⟨y.1, hIb y⟩ : f ⁻¹' Icc a b) ∈ (𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b) := by
    rw [hB]
    exact Or.inr y.2
  -- The inclusion of the boundary into `M` is a closed embedding, and so are the inclusions of the
  -- two levels into the boundary.
  have hg : IsClosedEmbedding fun q : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ↦ q.1.1 :=
    (isClosed_Icc.preimage hf.continuous).isClosedEmbedding_subtypeVal.comp
      ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal
  have hia : IsClosedEmbedding fun y : {x : M // f x = a} ↦
      (⟨⟨y.1, hIa y⟩, hBa y⟩ : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) :=
    (IsClosedEmbedding.of_comp_iff hg).1
      (isClosed_eq hf.continuous continuous_const).isClosedEmbedding_subtypeVal
  have hib : IsClosedEmbedding fun y : {x : M // f x = b} ↦
      (⟨⟨y.1, hIb y⟩, hBb y⟩ : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) :=
    (IsClosedEmbedding.of_comp_iff hg).1
      (isClosed_eq hf.continuous continuous_const).isClosedEmbedding_subtypeVal
  refine (Equiv.toHomeomorphOfContinuousClosed
    { toFun := Sum.elim (fun y ↦ ⟨⟨y.1, hIa y⟩, hBa y⟩) (fun y ↦ ⟨⟨y.1, hIb y⟩, hBb y⟩)
      invFun q := if h : f q.1.1 = a then .inl ⟨q.1.1, h⟩
        else .inr ⟨q.1.1, (hmem q).resolve_left h⟩
      left_inv := ?_
      right_inv := ?_ }
    (hia.continuous.sumElim hib.continuous) (hia.isClosedMap.sumElim hib.isClosedMap)).symm
  · rintro (y | y)
    · simp [y.2]
    · simp [y.2, hab.ne']
  · intro q
    by_cases h : f q.1.1 = a <;> simp [h]

/-- A point of the boundary of the band on the lower level `f⁻¹(a)` is sent to itself in the
copy of `f⁻¹(a)`. -/
@[simp]
theorem scalarRegularBandBoundaryHomeomorph_apply_of_eq_left
    (q : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hq : f q.1.1 = a) :
    scalarRegularBandBoundaryHomeomorph hf hn ha hb hab q = .inl ⟨q.1.1, hq⟩ := by
  simp [scalarRegularBandBoundaryHomeomorph, hq]

/-- A point of the boundary of the band on the upper level `f⁻¹(b)` is sent to itself in the
copy of `f⁻¹(b)`. -/
@[simp]
theorem scalarRegularBandBoundaryHomeomorph_apply_of_eq_right
    (q : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hq : f q.1.1 = b) :
    scalarRegularBandBoundaryHomeomorph hf hn ha hb hab q = .inr ⟨q.1.1, hq⟩ := by
  simp [scalarRegularBandBoundaryHomeomorph, hq, hab.ne']

/-- The inverse of `TauCeti.scalarRegularBandBoundaryHomeomorph` is the identity on the underlying
points of `f⁻¹(a)`. -/
@[simp]
theorem coe_scalarRegularBandBoundaryHomeomorph_symm_apply_inl (y : {x : M // f x = a}) :
    ((scalarRegularBandBoundaryHomeomorph hf hn ha hb hab).symm (.inl y)).1.1 = y.1 := by
  simp [scalarRegularBandBoundaryHomeomorph]

/-- The inverse of `TauCeti.scalarRegularBandBoundaryHomeomorph` is the identity on the underlying
points of `f⁻¹(b)`. -/
@[simp]
theorem coe_scalarRegularBandBoundaryHomeomorph_symm_apply_inr (y : {x : M // f x = b}) :
    ((scalarRegularBandBoundaryHomeomorph hf hn ha hb hab).symm (.inr y)).1.1 = y.1 := by
  simp [scalarRegularBandBoundaryHomeomorph]

/-- **The boundary charts of a band are the level charts.** On the source of the preferred boundary
chart at a point `p` of the boundary of the band `f⁻¹([a, b])`, that chart, read in `Fin n → ℝ`
through `EuclideanSpace.equiv`, is the preferred chart at `p` of the disjoint union of the levels
`f⁻¹(a)` and `f⁻¹(b)`, that is, the level chart `TauCeti.regularLevelChartAt` of the level
containing `p`. -/
theorem euclideanSpaceEquiv_chartAt_scalarRegularBandBoundary_eq_chartAt
    (p q : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)))
    (hq : letI := scalarRegularBandChartedSpace hf hn ha hb hab
      haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
      q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
    EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) =
      chartAt (Fin n → ℝ) (scalarRegularBandBoundaryHomeomorph hf hn ha hb hab p)
        (scalarRegularBandBoundaryHomeomorph hf hn ha hb hab q) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
  have hmem (q : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) : f q.1.1 = a ∨ f q.1.1 = b := by
    simpa [boundary_scalarRegularBand hn ha hb le_rfl hf hab] using q.2
  rw [boundaryChartedSpace_chartAt_source, mem_preimage,
    scalarRegularBandChartedSpace_chartAt] at hq
  rw [boundaryChartedSpace_chartAt_apply, scalarRegularBandChartedSpace_chartAt]
  rcases hmem p with hp | hp
  · -- On the lower level, the face chart only sees points of the lower level.
    have hqa : f q.1.1 = a := (hmem q).resolve_right fun hqb ↦ by
      have := hq
      rw [scalarRegularBandChartAt_source_of_eq_left hf hn ha hb hp] at this
      exact (mem_Iio.1 this.2).ne hqb
    rw [scalarRegularBandBoundaryHomeomorph_apply_of_eq_left hf hn ha hb hab p hp,
      scalarRegularBandBoundaryHomeomorph_apply_of_eq_left hf hn ha hb hab q hqa,
      sum_chartAt_inl_apply, regularLevelChartedSpace_chartAt]
    obtain rfl : n = finrank ℝ E - 1 := by omega
    ext i
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply,
      EuclideanHalfSpace.boundaryProj_apply]
    rw [scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_left hf hn ha hb hp hq hqa,
      Fin.cast_eq_self]
  · -- On the upper level, the face chart only sees points of the upper level.
    have hqb : f q.1.1 = b := (hmem q).resolve_left fun hqa ↦ by
      have := hq
      rw [scalarRegularBandChartAt_source_of_eq_right hf hn ha hb hab hp] at this
      exact (mem_Ioi.1 this.2).ne' hqa
    rw [scalarRegularBandBoundaryHomeomorph_apply_of_eq_right hf hn ha hb hab p hp,
      scalarRegularBandBoundaryHomeomorph_apply_of_eq_right hf hn ha hb hab q hqb,
      sum_chartAt_inr_apply, regularLevelChartedSpace_chartAt]
    obtain rfl : n = finrank ℝ E - 1 := by omega
    ext i
    simp only [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply,
      EuclideanHalfSpace.boundaryProj_apply]
    rw [scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_right hf hn ha hb hab hp hq
      hqb, Fin.cast_eq_self]

/-- **The boundary of a band is diffeomorphic to the disjoint union of its levels.** The identity
of points `TauCeti.scalarRegularBandBoundaryHomeomorph` is a diffeomorphism of every smoothness `k`
between the manifold boundary of the band `f⁻¹([a, b])` between regular values `a < b`, with its
boundary atlas modelled on `EuclideanSpace ℝ (Fin n)`, and the disjoint union of the levels
`f⁻¹(a)` and `f⁻¹(b)`, each with its atlas `TauCeti.regularLevelChartedSpace` modelled on
`Fin n → ℝ`. In the preferred charts it is the linear identification `EuclideanSpace.equiv`. -/
noncomputable def scalarRegularBandBoundaryDiffeomorph (k : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
    ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ≃ₘ^k⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, Fin n → ℝ)⟯
      {x : M // f x = a} ⊕ {x : M // f x = b} :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
  letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
  (scalarRegularBandBoundaryHomeomorph hf hn ha hb hab).toDiffeomorphOfChartAt
    (EuclideanSpace.equiv (Fin n) ℝ) (fun p ↦ Filter.eventually_of_mem
      ((chartAt _ p).open_source.mem_nhds (mem_chart_source _ p)) fun q hq ↦
        (euclideanSpaceEquiv_chartAt_scalarRegularBandBoundary_eq_chartAt hf hn ha hb hab p q
          hq).symm) k

/-- The underlying map of `TauCeti.scalarRegularBandBoundaryDiffeomorph` is
`TauCeti.scalarRegularBandBoundaryHomeomorph`. -/
@[simp]
theorem coe_scalarRegularBandBoundaryDiffeomorph (k : ℕ∞ω) :
    ⇑(scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab k) =
      scalarRegularBandBoundaryHomeomorph hf hn ha hb hab := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
  exact Homeomorph.coe_toDiffeomorphOfChartAt _ _ _ k

/-- The underlying homeomorphism of `TauCeti.scalarRegularBandBoundaryDiffeomorph` is
`TauCeti.scalarRegularBandBoundaryHomeomorph`. -/
@[simp]
theorem toHomeomorph_scalarRegularBandBoundaryDiffeomorph (k : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    haveI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
    letI := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
    (scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab k).toHomeomorph =
      scalarRegularBandBoundaryHomeomorph hf hn ha hb hab := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) ha (finrank_sub_finrank_real_eq hn)
  let := regularLevelChartedSpace (fun _ _ ↦ hf.contMDiffAt) hb (finrank_sub_finrank_real_eq hn)
  exact Homeomorph.toHomeomorph_toDiffeomorphOfChartAt _ _ _ k

end Band

end TauCeti
