/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Chart.Linear
public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Sublevel

/-!
# The boundary of a regular sublevel is the regular level

Let `f : M → ℝ` be a `C¹` function on a boundaryless manifold modelled on a real space `E` of
dimension `n + 1`, and let `a` be a regular value of `f`. The sublevel `M_a = {x | f x ≤ a}` is a
manifold with boundary for its atlas `TauCeti.scalarRegularSublevelChartedSpace`, modelled on the
half-space `EuclideanHalfSpace (n + 1)`, and its manifold boundary `∂M_a` is the level `f⁻¹(a)`
(`TauCeti.boundary_scalarRegularSublevel`). That boundary is itself a manifold, modelled on
`EuclideanSpace ℝ (Fin n)`, for the atlas `TauCeti.boundaryChartedSpace` read off the charts of
`M_a`; and the level `f⁻¹(a)` is a manifold, modelled on `Fin n → ℝ`, for its own atlas
`TauCeti.regularLevelChartedSpace`. This file identifies the two:
`TauCeti.scalarRegularSublevelBoundaryDiffeomorph` is a diffeomorphism

`∂M_a ≃ f⁻¹(a)`

which is the identity on points of `M`.

The comparison is exact in charts. At a point `p` of the level, the face chart of `M_a` has the
inward coordinate `a - f` in slot `0` and the coordinates of the level chart at `p` in slots
`1, …, n`; the boundary chart deletes slot `0`. Hence on the source of the boundary chart at `p`,
the level chart at `p` is the boundary chart at `p` followed by the coordinate identification
`EuclideanSpace.equiv (Fin n) ℝ : EuclideanSpace ℝ (Fin n) ≃ (Fin n → ℝ)`
(`TauCeti.regularLevelChartAt_scalarRegularSublevelBoundaryDiffeomorph`). So the identification is
linear in preferred charts, and it is smooth of every order in both directions
(`Homeomorph.toDiffeomorphOfChartAt`).

The same holds for the band `f⁻¹([a, b])` between regular values `a < b`, whose manifold boundary
is the union of the two levels (`TauCeti.boundary_scalarRegularBand`): the diffeomorphism
`TauCeti.scalarRegularBandBoundaryDiffeomorph` identifies it with the disjoint union
`f⁻¹(a) ⊕ f⁻¹(b)`, sending a point of the lower level to the left summand and a point of the upper
level to the right summand.

## Main declarations

* `TauCeti.scalarRegularSublevelBoundaryDiffeomorph`: the boundary of the sublevel `{f ≤ a}` at a
  regular value is diffeomorphic to the level `f⁻¹(a)`, by the identity on points.
* `TauCeti.regularLevelChartAt_scalarRegularSublevelBoundaryDiffeomorph`: the level charts are the
  boundary charts read through `EuclideanSpace.equiv (Fin n) ℝ`.
* `TauCeti.scalarRegularBandBoundaryDiffeomorph`: the boundary of the band `f⁻¹([a, b])` between
  regular values is diffeomorphic to `f⁻¹(a) ⊕ f⁻¹(b)`, with the placement laws
  `TauCeti.scalarRegularBandBoundaryDiffeomorph_of_eq_left` and
  `TauCeti.scalarRegularBandBoundaryDiffeomorph_of_eq_right`.
* `TauCeti.chartAt_scalarRegularBandBoundaryDiffeomorph`: on both faces of the band, the level
  charts are the boundary charts read through `EuclideanSpace.equiv (Fin n) ℝ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Proposition 5.47 (regular sublevel sets are regular domains, with boundary the
  level).
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3.
-/

public section

open Function Module Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {f : M → ℝ} {a b : ℝ}
  {n : ℕ} [I.Boundaryless] [FiniteDimensional ℝ E]

section Sublevel

variable [IsManifold I 1 M] (hf : ContMDiff I 𝓘(ℝ) 1 f) (hreg : IsRegularValue I 𝓘(ℝ) f a)
  (hn : finrank ℝ E = n + 1)

/-- The boundary of the sublevel `{f ≤ a}` at a regular value is homeomorphic to the level
`f⁻¹(a)`, by the identity on points of `M`. -/
private noncomputable def sublevelBoundaryHomeomorph :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}) ≃ₜ {x : M // f x = a} :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  have hb := boundary_scalarRegularSublevel hreg hn le_rfl hf
  { toFun p := ⟨p.1.1, by simpa only [hb, mem_ofPred_eq] using p.2⟩
    invFun x := ⟨⟨x.1, x.2.le⟩, by simpa only [hb, mem_ofPred_eq] using x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- On the source of the preferred boundary chart at `p`, the preferred level chart at `p`, applied
to the point `q` regarded on the level, is the boundary chart read through
`EuclideanSpace.equiv (Fin n) ℝ`. -/
private theorem regularLevelChartAt_sublevelBoundaryHomeomorph :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    ∀ p, ∀ q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source,
      regularLevelChartAt (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
          (sublevelBoundaryHomeomorph hf hreg hn p) (sublevelBoundaryHomeomorph hf hreg hn q) =
        EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) := by
  let := scalarRegularSublevelChartedSpace hf hreg hn
  let := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  intro p q hq
  have hpa := (sublevelBoundaryHomeomorph hf hreg hn p).2
  have hqa := (sublevelBoundaryHomeomorph hf hreg hn q).2
  rw [boundaryChartedSpace_chartAt_source, mem_preimage,
    scalarRegularSublevelChartedSpace_chartAt] at hq
  ext i
  rw [PiLp.coe_continuousLinearEquiv, boundaryChartedSpace_chartAt_apply,
    EuclideanHalfSpace.boundaryProj_apply, scalarRegularSublevelChartedSpace_chartAt,
    scalarRegularSublevelChartAt_apply_succ_eq_regularLevelChartAt hf hreg hn hpa hq hqa]
  exact (regularLevelChartAt_apply_cast _ hreg _ _ _ _ _ i).symm

/-- **The boundary of a regular sublevel is the level.** If `f` is `C¹` and `a` is a regular
value of `f`, the manifold boundary of the sublevel `{f ≤ a}`, with its boundary atlas, is
diffeomorphic to the level `f⁻¹(a)`, with its atlas `TauCeti.regularLevelChartedSpace`, by the
identity on points of `M`. In preferred charts the identification is the linear map
`EuclideanSpace.equiv (Fin n) ℝ`, so it is a diffeomorphism of every order `m`. -/
noncomputable def scalarRegularSublevelBoundaryDiffeomorph (m : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin n → ℝ)
      ↥((𝓡∂ (n + 1)).boundary {x | f x ≤ a}) {x : M // f x = a} m :=
  letI := scalarRegularSublevelChartedSpace hf hreg hn
  letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
  letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
  (sublevelBoundaryHomeomorph hf hreg hn).toDiffeomorphOfChartAt (EuclideanSpace.equiv (Fin n) ℝ)
    (fun p q hq ↦ by
      rw [regularLevelChartedSpace_chartAt]
      exact regularLevelChartAt_sublevelBoundaryHomeomorph hf hreg hn p q hq) m

/-- The diffeomorphism `TauCeti.scalarRegularSublevelBoundaryDiffeomorph` is the identity on points
of `M`. -/
@[simp]
theorem coe_scalarRegularSublevelBoundaryDiffeomorph_apply (m : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
    ∀ p, (scalarRegularSublevelBoundaryDiffeomorph hf hreg hn m p : M) = p := by
  simp only [scalarRegularSublevelBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt]
  exact fun _ ↦ rfl

/-- The inverse of `TauCeti.scalarRegularSublevelBoundaryDiffeomorph` is the identity on points of
`M`. -/
@[simp]
theorem coe_scalarRegularSublevelBoundaryDiffeomorph_symm_apply (m : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
    ∀ x, (((scalarRegularSublevelBoundaryDiffeomorph hf hreg hn m).symm x :
      {x | f x ≤ a}) : M) = x := by
  simp only [scalarRegularSublevelBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt_symm]
  exact fun _ ↦ rfl

/-- **Level charts are boundary charts.** On the source of the preferred boundary chart of the
sublevel `{f ≤ a}` at `p`, the preferred level chart at `p` is the boundary chart at `p` read
through `EuclideanSpace.equiv (Fin n) ℝ`: the tangential coordinates of the face chart of the
sublevel are the coordinates of the level chart. -/
theorem regularLevelChartAt_scalarRegularSublevelBoundaryDiffeomorph (m : ℕ∞ω) :
    letI := scalarRegularSublevelChartedSpace hf hreg hn
    letI := isManifold_scalarRegularSublevel hreg hn le_rfl hf
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
    ∀ p, ∀ q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source,
      regularLevelChartAt (n := n) (fun x _ ↦ hf.contMDiffAt) hreg (by simp [hn])
          (scalarRegularSublevelBoundaryDiffeomorph hf hreg hn m p)
          (scalarRegularSublevelBoundaryDiffeomorph hf hreg hn m q) =
        EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) := by
  simp only [scalarRegularSublevelBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt]
  exact regularLevelChartAt_sublevelBoundaryHomeomorph hf hreg hn

end Sublevel

section Band

variable [IsManifold I 1 M] (hf : ContMDiff I 𝓘(ℝ) 1 f) (hn : finrank ℝ E = n + 1)
  (ha : IsRegularValue I 𝓘(ℝ) f a) (hb : IsRegularValue I 𝓘(ℝ) f b) (hab : a < b)

/-- The inclusion of the level `f⁻¹(c)`, for `c = a` or `c = b`, into the boundary of the band
`f⁻¹([a, b])`. -/
private def bandBoundaryIncl {c : ℝ} (hc : c = a ∨ c = b) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    {x : M // f x = c} → ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  fun x ↦ ⟨⟨x.1, by rcases hc with rfl | rfl <;> simp [x.2, hab.le]⟩, by
    rw [boundary_scalarRegularBand hn ha hb le_rfl hf hab, mem_ofPred_eq, x.2]
    exact hc⟩

/-- A point of the boundary of the band lies on the lower or the upper level. -/
private theorem eq_or_eq_of_mem_bandBoundary :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ∀ p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)), f p = a ∨ f p = b := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  intro p
  simpa only [boundary_scalarRegularBand hn ha hb le_rfl hf hab, mem_ofPred_eq] using p.2

/-- The levels `f⁻¹(a)` and `f⁻¹(b)` are open in the boundary of the band, and their inclusions are
open embeddings. -/
private theorem isOpenEmbedding_bandBoundaryIncl {c : ℝ} (hc : c = a ∨ c = b) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    Topology.IsOpenEmbedding (bandBoundaryIncl hf hn ha hb hab hc) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  have hcont : Continuous fun p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ↦ f p :=
    hf.continuous.comp (by fun_prop)
  refine ⟨(Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal.comp
    Topology.IsEmbedding.subtypeVal)).1 Topology.IsEmbedding.subtypeVal, ?_⟩
  have hrange : range (bandBoundaryIncl hf hn ha hb hab hc) =
      {p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) | f p = c} := by
    ext p
    refine ⟨?_, fun hp ↦ ⟨⟨p, hp⟩, rfl⟩⟩
    rintro ⟨x, rfl⟩
    exact x.2
  rw [hrange]
  rcases hc with rfl | rfl
  · convert isOpen_lt hcont (continuous_const (y := b)) using 1
    ext p
    rcases eq_or_eq_of_mem_bandBoundary hf hn ha hb hab p with hp | hp <;>
      simp [hp, hab, hab.ne']
  · convert isOpen_lt (continuous_const (y := a)) hcont using 1
    ext p
    rcases eq_or_eq_of_mem_bandBoundary hf hn ha hb hab p with hp | hp <;>
      simp [hp, hab, hab.ne]

/-- The boundary of the band `f⁻¹([a, b])` is homeomorphic to `f⁻¹(a) ⊕ f⁻¹(b)`, by the identity
on points of `M`. -/
private noncomputable def bandBoundaryHomeomorph :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ≃ₜ {x : M // f x = a} ⊕ {x : M // f x = b} :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  (Equiv.toHomeomorphOfContinuousOpen
    { toFun := Sum.elim (bandBoundaryIncl hf hn ha hb hab (Or.inl rfl))
        (bandBoundaryIncl hf hn ha hb hab (Or.inr rfl))
      invFun p := if hp : f p = a then .inl ⟨p, hp⟩ else
        .inr ⟨p, (eq_or_eq_of_mem_bandBoundary hf hn ha hb hab p).resolve_left hp⟩
      left_inv := by
        rintro (x | x)
        · simp [bandBoundaryIncl, x.2]
        · simp [bandBoundaryIncl, x.2, hab.ne']
      right_inv p := by
        by_cases hp : f p = a <;> simp [hp, bandBoundaryIncl] }
    ((isOpenEmbedding_bandBoundaryIncl hf hn ha hb hab _).continuous.sumElim
      (isOpenEmbedding_bandBoundaryIncl hf hn ha hb hab _).continuous)
    ((isOpenEmbedding_bandBoundaryIncl hf hn ha hb hab _).isOpenMap.sumElim
      (isOpenEmbedding_bandBoundaryIncl hf hn ha hb hab _).isOpenMap)).symm

private theorem bandBoundaryHomeomorph_of_eq_left :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ∀ (p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hp : f p = a),
      bandBoundaryHomeomorph hf hn ha hb hab p = .inl ⟨p, hp⟩ := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  intro p hp
  simp [bandBoundaryHomeomorph, hp]

private theorem bandBoundaryHomeomorph_of_eq_right :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    ∀ (p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hp : f p = b),
      bandBoundaryHomeomorph hf hn ha hb hab p = .inr ⟨p, hp⟩ := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  intro p hp
  simp [bandBoundaryHomeomorph, hp, hab.ne']

/-- On the source of the preferred boundary chart of the band at `p`, the preferred chart of
`f⁻¹(a) ⊕ f⁻¹(b)` at the image of `p` is the boundary chart read through
`EuclideanSpace.equiv (Fin n) ℝ`. -/
private theorem chartAt_bandBoundaryHomeomorph :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ p, ∀ q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source,
      chartAt (Fin n → ℝ) (bandBoundaryHomeomorph hf hn ha hb hab p)
          (bandBoundaryHomeomorph hf hn ha hb hab q) =
        EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) := by
  let := scalarRegularBandChartedSpace hf hn ha hb hab
  let := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  let := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
  let := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
  intro p q hq
  rw [boundaryChartedSpace_chartAt_source, mem_preimage,
    scalarRegularBandChartedSpace_chartAt] at hq
  rcases eq_or_eq_of_mem_bandBoundary hf hn ha hb hab p with hp | hp
  · -- On the lower face the chart source lies in `{f < b}`, so `q` is on the lower level too.
    have hqa : f q = a := by
      have hlt := (scalarRegularBandChartAt_source_of_eq_left hf hn ha hb hp ▸ hq).2
      exact (eq_or_eq_of_mem_bandBoundary hf hn ha hb hab q).resolve_right
        (ne_of_lt (mem_Iio.1 hlt))
    rw [bandBoundaryHomeomorph_of_eq_left hf hn ha hb hab p hp,
      bandBoundaryHomeomorph_of_eq_left hf hn ha hb hab q hqa, sum_chartAt_inl_apply,
      regularLevelChartedSpace_chartAt]
    ext i
    rw [PiLp.coe_continuousLinearEquiv, boundaryChartedSpace_chartAt_apply,
      EuclideanHalfSpace.boundaryProj_apply, scalarRegularBandChartedSpace_chartAt,
      scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_left hf hn ha hb hp hq hqa]
    exact (regularLevelChartAt_apply_cast _ ha _ _ _ _ _ i).symm
  · -- On the upper face the chart source lies in `{a < f}`, so `q` is on the upper level too.
    have hqb : f q = b := by
      have hlt := (scalarRegularBandChartAt_source_of_eq_right hf hn ha hb hab hp ▸ hq).2
      exact (eq_or_eq_of_mem_bandBoundary hf hn ha hb hab q).resolve_left
        (ne_of_gt (mem_Ioi.1 hlt))
    rw [bandBoundaryHomeomorph_of_eq_right hf hn ha hb hab p hp,
      bandBoundaryHomeomorph_of_eq_right hf hn ha hb hab q hqb, sum_chartAt_inr_apply,
      regularLevelChartedSpace_chartAt]
    ext i
    rw [PiLp.coe_continuousLinearEquiv, boundaryChartedSpace_chartAt_apply,
      EuclideanHalfSpace.boundaryProj_apply, scalarRegularBandChartedSpace_chartAt,
      scalarRegularBandChartAt_apply_succ_eq_regularLevelChartAt_of_eq_right hf hn ha hb hab hp
        hq hqb]
    exact (regularLevelChartAt_apply_cast _ hb _ _ _ _ _ i).symm

/-- **The boundary of a regular band is the disjoint union of its two levels.** If `f` is `C¹` and
`a < b` are regular values of `f`, the manifold boundary of the band `f⁻¹([a, b])`, with its
boundary atlas, is diffeomorphic to the disjoint union `f⁻¹(a) ⊕ f⁻¹(b)` of the levels with their
atlases `TauCeti.regularLevelChartedSpace`. A point of the lower level goes to the left summand and
a point of the upper level to the right summand, unchanged as a point of `M`. In preferred charts
the identification is the linear map `EuclideanSpace.equiv (Fin n) ℝ`, so it is a diffeomorphism
of every order `m`. -/
noncomputable def scalarRegularBandBoundaryDiffeomorph (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    Diffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin n → ℝ)
      ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b)) ({x : M // f x = a} ⊕ {x : M // f x = b}) m :=
  letI := scalarRegularBandChartedSpace hf hn ha hb hab
  letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
  letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
  letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
  (bandBoundaryHomeomorph hf hn ha hb hab).toDiffeomorphOfChartAt (EuclideanSpace.equiv (Fin n) ℝ)
    (chartAt_bandBoundaryHomeomorph hf hn ha hb hab) m

/-- `TauCeti.scalarRegularBandBoundaryDiffeomorph` sends a point of the lower level to the left
summand. -/
@[simp]
theorem scalarRegularBandBoundaryDiffeomorph_of_eq_left (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ (p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hp : f p = a),
      scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m p = .inl ⟨p, hp⟩ := by
  simp only [scalarRegularBandBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt]
  exact bandBoundaryHomeomorph_of_eq_left hf hn ha hb hab

/-- `TauCeti.scalarRegularBandBoundaryDiffeomorph` sends a point of the upper level to the right
summand. -/
@[simp]
theorem scalarRegularBandBoundaryDiffeomorph_of_eq_right (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ (p : ↥((𝓡∂ (n + 1)).boundary (f ⁻¹' Icc a b))) (hp : f p = b),
      scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m p = .inr ⟨p, hp⟩ := by
  simp only [scalarRegularBandBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt]
  exact bandBoundaryHomeomorph_of_eq_right hf hn ha hb hab

/-- The inverse of `TauCeti.scalarRegularBandBoundaryDiffeomorph` is the identity on points of the
lower level. -/
@[simp]
theorem coe_scalarRegularBandBoundaryDiffeomorph_symm_inl (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ x : {x : M // f x = a}, (((scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m).symm
      (.inl x) : f ⁻¹' Icc a b) : M) = x := by
  simp only [scalarRegularBandBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt_symm]
  exact fun _ ↦ rfl

/-- The inverse of `TauCeti.scalarRegularBandBoundaryDiffeomorph` is the identity on points of the
upper level. -/
@[simp]
theorem coe_scalarRegularBandBoundaryDiffeomorph_symm_inr (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ x : {x : M // f x = b}, (((scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m).symm
      (.inr x) : f ⁻¹' Icc a b) : M) = x := by
  simp only [scalarRegularBandBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt_symm]
  exact fun _ ↦ rfl

/-- **Level charts are boundary charts on both faces.** On the source of the preferred boundary
chart of the band `f⁻¹([a, b])` at `p`, the preferred chart of `f⁻¹(a) ⊕ f⁻¹(b)` at the image of
`p`, which is the level chart of the level containing `p`, is the boundary chart at `p` read
through `EuclideanSpace.equiv (Fin n) ℝ`. -/
theorem chartAt_scalarRegularBandBoundaryDiffeomorph (m : ℕ∞ω) :
    letI := scalarRegularBandChartedSpace hf hn ha hb hab
    letI := isManifold_scalarRegularBand hn ha hb le_rfl hf hab
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) ha (by simp [hn])
    letI := regularLevelChartedSpace (n := n) (fun x _ ↦ hf.contMDiffAt) hb (by simp [hn])
    ∀ p, ∀ q ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source,
      chartAt (Fin n → ℝ) (scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m p)
          (scalarRegularBandBoundaryDiffeomorph hf hn ha hb hab m q) =
        EuclideanSpace.equiv (Fin n) ℝ (chartAt (EuclideanSpace ℝ (Fin n)) p q) := by
  simp only [scalarRegularBandBoundaryDiffeomorph, Homeomorph.coe_toDiffeomorphOfChartAt]
  exact chartAt_bandBoundaryHomeomorph hf hn ha hb hab

end Band

end TauCeti
