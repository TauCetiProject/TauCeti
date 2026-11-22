/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.PositiveCohomologyAssignment
import TauCeti.Topology.Compactness.Compact

/-!
# Continuity of the charges along a family of discs

Taubes reconstructs a pseudoholomorphic curve from a positive cohomology assignment `I` to a
closed set `Z` in an almost complex manifold `(Y, J)` (`TauCeti.PositiveCohomologyAssignment`).
Near a point of `Z` he foliates a neighbourhood by discs `σ_w`, indexed by a transverse parameter
`w`, and reads the curve off the intersection points of `Z` with the leaves, weighted by their
local charges. This file proves that these weighted intersections move continuously with `w`: the
analogue, for positive cohomology assignments, of Hurwitz's theorem on the zeros of a convergent
sequence of holomorphic functions.

The family is a continuous map `u : P × 𝔻 → Y`, with leaves `σ_w = u (w, ·)`
(`ContinuousMap.curry`), and the hypothesis is that near a parameter `w₀` the leaves meet `Z` only
inside a fixed compact set `K ⊆ 𝔻`, the open-disc form of a boundary staying away from `Z`. Then,
as `w` tends to `w₀`:

* **The intersection points converge.** `σ_w⁻¹(Z)` lies in any prescribed open neighbourhood of
  `σ_{w₀}⁻¹(Z)`: this is `IsClosed.eventually_preimage_prodMk_subset` for the closed set `u⁻¹(Z)`,
  and only uses that `Z` is closed.
* **The integer is locally constant.** Two leaves joined by a path of leaves meeting `Z` inside `K`
  have the same integer, by the homotopy law
  (`TauCeti.PositiveCohomologyAssignment.charge_eq_of_path`). So when `P` is locally path
  connected, `I(σ_w) = I(σ_{w₀})` for `w` near `w₀`
  (`TauCeti.PositiveCohomologyAssignment.eventually_charge_eq`).
* **Local charges are conserved.** Let `z₀` be an isolated point of `σ_{w₀}⁻¹(Z)`, alone in its
  disc `B(z₀, R)`, and let `0 < r < R`. For `w` near `w₀` the integer of `σ_w` on the round disc
  `B(z₀, r)` is the local charge of `σ_{w₀}` at `z₀`
  (`TauCeti.PositiveCohomologyAssignment.eventually_exists_charge_comp_subdisc_eq_localCharge`).
  When `σ_w⁻¹(Z)` is finite, this says that the local charges of `σ_w` at its points inside
  `B(z₀, r)` add up to the local charge of `σ_{w₀}` at `z₀`
  (`TauCeti.PositiveCohomologyAssignment.eventually_sum_localCharge_eq`).
* **Zeros are retained.** If that local charge is nonzero, every leaf near `σ_{w₀}` meets `Z` in
  `B(z₀, r)`
  (`TauCeti.PositiveCohomologyAssignment.eventually_exists_mem_ball_of_localCharge_ne_zero`).
  By `TauCeti.PositiveCohomologyAssignment.localCharge_pos`, this applies when `σ_{w₀}` extends to
  a map `ℂ → Y` that is `J`-holomorphic on the unit disc, and `σ_{w₀}` is not constant near `z₀`.
* **Counting.** If moreover the leaf `σ_w` is `J`-holomorphic and constant near none of the
  finitely many points of `σ_w⁻¹(Z)`, it meets `Z` inside `B(z₀, r)` in at most as many points as
  the local charge of `σ_{w₀}` at `z₀`
  (`TauCeti.PositiveCohomologyAssignment.eventually_card_le_localCharge`).

Applied at each point of a finite `σ_{w₀}⁻¹(Z)`, these statements say that the intersection
points of `σ_w` with `Z`, weighted by their local charges, converge to those of `σ_{w₀}` as `w`
tends to `w₀`. This is how the leaves of a foliation assemble into the branches of the
reconstructed curve.

## Main results

* `TauCeti.PositiveCohomologyAssignment.charge_eq_of_path`,
  `TauCeti.PositiveCohomologyAssignment.eventually_charge_eq`: the integer of the leaves is
  constant along paths and near `w₀`.
* `TauCeti.PositiveCohomologyAssignment.eventually_exists_charge_comp_subdisc_eq_localCharge`,
  `TauCeti.PositiveCohomologyAssignment.eventually_sum_localCharge_eq`: conservation of local
  charges.
* `TauCeti.PositiveCohomologyAssignment.eventually_exists_mem_ball_of_localCharge_ne_zero`:
  retention of charged intersection points.
* `TauCeti.PositiveCohomologyAssignment.eventually_card_le_localCharge`: the counting bound for
  `J`-holomorphic leaves.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
-/

public section

open Filter Metric Set Topology
open Complex.UnitDisc TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff

variable {P : Type*} [TopologicalSpace P]

namespace TauCeti.PositiveCohomologyAssignment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {Z : Set Y}
  (A : PositiveCohomologyAssignment J Z) (u : C(P × 𝔻, Y))

/-- A leaf of a continuous family of discs that meets the closed set `Z` only inside a compact set
`K` has compact preimage of `Z`. -/
private theorem isCompact_curry_preimage (hZ : IsClosed Z) {K : Set 𝔻} (hK : IsCompact K) {w : P}
    (hw : ∀ z, u (w, z) ∈ Z → z ∈ K) : IsCompact (u.curry w ⁻¹' Z) :=
  hK.of_isClosed_subset (hZ.preimage (u.curry w).continuous) hw

/-- **The integer is constant along paths of leaves.** If `γ` is a path from `w` to `w'` in the
parameter space of a continuous family of discs `u`, and every leaf `u (γ t, ·)` meets the closed
set `Z` only inside a fixed compact set `K ⊆ 𝔻`, then the leaves over `w` and `w'` have the same
integer. -/
theorem charge_eq_of_path (hZ : IsClosed Z) {K : Set 𝔻} (hK : IsCompact K) {w w' : P}
    (γ : Path w w') (hγ : ∀ t z, u (γ t, z) ∈ Z → z ∈ K) (h : IsCompact (u.curry w ⁻¹' Z))
    (h' : IsCompact (u.curry w' ⁻¹' Z)) : A.charge (u.curry w) h = A.charge (u.curry w') h' := by
  let F : (u.curry w).Homotopy (u.curry w') :=
    { toFun := fun p ↦ u (γ p.1, p.2)
      continuous_toFun := u.continuous.comp ((γ.continuous.comp continuous_fst).prodMk
        continuous_snd)
      map_zero_left := fun z ↦ by simp
      map_one_left := fun z ↦ by simp }
  refine A.charge_eq_of_homotopy F ?_ h h'
  exact (isCompact_univ.prod hK).of_isClosed_subset (hZ.preimage F.continuous)
    fun p hp ↦ ⟨trivial, hγ p.1 p.2 hp⟩

/-- **The integer is locally constant.** Let `u` be a continuous family of discs over a locally
path connected parameter space, and suppose that for `w` near `w₀` the leaf `u (w, ·)` meets the
closed set `Z` only inside a fixed compact set `K ⊆ 𝔻`. Then for `w` near `w₀` the leaf over `w`
has the same integer as the leaf over `w₀`. -/
theorem eventually_charge_eq [LocallyPathConnectedSpace P] (hZ : IsClosed Z) {K : Set 𝔻}
    (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K)
    (h₀ : IsCompact (u.curry w₀ ⁻¹' Z)) :
    ∀ᶠ w in 𝓝 w₀, ∃ h : IsCompact (u.curry w ⁻¹' Z), A.charge _ h = A.charge _ h₀ := by
  obtain ⟨V, ⟨hV, hVpc⟩, hVK⟩ := (LocallyPathConnectedSpace.path_connected_basis w₀).mem_iff.1 hKZ
  filter_upwards [hV] with w hw
  have hγ := hVpc.joinedIn w₀ (mem_of_mem_nhds hV) w hw
  have h := isCompact_curry_preimage u hZ hK (hVK hw)
  exact ⟨h, (A.charge_eq_of_path u hZ hK hγ.somePath (fun t ↦ hVK (hγ.somePath_mem t)) h₀ h).symm⟩

/-- **Conservation of local charges.** Let `u` be a continuous family of discs over a locally path
connected parameter space, and suppose that for `w` near `w₀` the leaf `u (w, ·)` meets the closed
set `Z` only inside a fixed compact set `K ⊆ 𝔻`. Let `z₀` be a point which is alone in its disc
`B(z₀, R)` among the points of the leaf over `w₀` lying in `Z`, and let `0 < r < R` with
`B(z₀, r) ⊆ 𝔻`. Then for `w` near `w₀`, the restriction of the leaf over `w` to `B(z₀, r)` has
compact preimage of `Z`, and its integer is the local charge at `z₀` of the leaf over `w₀`. -/
theorem eventually_exists_charge_comp_subdisc_eq_localCharge [LocallyPathConnectedSpace P]
    (hZ : IsClosed Z) {K : Set 𝔻} (hK : IsCompact K) {w₀ : P}
    (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K) {z₀ : 𝔻} {r R : ℝ}
    (hc : ‖(z₀ : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ z, u (w₀, z) ∈ Z → (z : ℂ) ∈ ball (z₀ : ℂ) R → z = z₀) :
    ∀ᶠ w in 𝓝 w₀, ∃ h : IsCompact ((u.curry w).comp (subdisc z₀ r hc hr) ⁻¹' Z),
      A.charge _ h = A.localCharge (u.curry w₀) z₀ := by
  -- The restrictions of the leaves to `B(z₀, r)` form a continuous family `v`, whose leaves near
  -- `w₀` meet `Z` only in the compact set `‖ζ‖ ≤ 1 / 2`.
  set v : C(P × 𝔻, Y) := u.comp ((ContinuousMap.id P).prodMap (subdisc z₀ r hc hr))
  have hv (w : P) : v.curry w = (u.curry w).comp (subdisc z₀ r hc hr) := rfl
  have hK' : IsCompact {ζ : 𝔻 | ‖(ζ : ℂ)‖ ≤ 1 / 2} := isCompact_setOf_norm_le (by norm_num)
  -- The leaf over `w₀` meets `Z` near `z₀` only at `z₀`, so in the open set `U` of points at
  -- distance less than `r / 2` or more than `r` from `z₀`; hence so do nearby leaves.
  set U : Set 𝔻 := (↑) ⁻¹' (ball (z₀ : ℂ) (r / 2) ∪ (closedBall (z₀ : ℂ) r)ᶜ)
  have hU : IsOpen U :=
    (isOpen_ball.union isClosed_closedBall.isOpen_compl).preimage continuous_coe
  have hσU : Prod.mk w₀ ⁻¹' (u ⁻¹' Z) ⊆ U := fun z hz ↦ by
    by_cases hzR : (z : ℂ) ∈ ball (z₀ : ℂ) R
    · obtain rfl := hiso z hz hzR
      exact Or.inl (mem_ball_self (half_pos hr))
    · exact Or.inr fun hzr ↦ hzR (closedBall_subset_ball hrR hzr)
  have hKZ' : ∀ᶠ w in 𝓝 w₀, ∀ ζ, v (w, ζ) ∈ Z → ζ ∈ {ζ : 𝔻 | ‖(ζ : ℂ)‖ ≤ 1 / 2} := by
    filter_upwards [(hZ.preimage u.continuous).eventually_preimage_prodMk_subset hK hKZ hU hσU]
      with w hw ζ hζ
    have hζr : dist (subdisc z₀ r hc hr ζ : ℂ) z₀ < r := mem_range_subdisc.1 ⟨ζ, rfl⟩
    rcases (mem_union _ _ _).1 (@hw (subdisc z₀ r hc hr ζ) hζ) with hlt | hgt
    · have hlt : r * ‖(ζ : ℂ)‖ < r / 2 := by
        simpa [dist_eq_norm, norm_mul, abs_of_pos hr] using mem_ball.1 hlt
      exact (lt_of_mul_lt_mul_left (by linarith) hr.le).le
    · exact absurd (ball_subset_closedBall (mem_ball.2 hζr)) hgt
  have hσ₀ := isCompact_curry_preimage u hZ hK hKZ.self_of_nhds
  have h₀ := isCompact_curry_preimage v hZ hK' hKZ'.self_of_nhds
  filter_upwards [A.eventually_charge_eq v hZ hK' hKZ' h₀] with w ⟨h, hw⟩
  refine ⟨hv w ▸ h, (A.charge_congr (hv w) h _).symm.trans (hw.trans ?_)⟩
  exact (A.charge_congr (hv w₀) h₀ _).trans
    (A.localCharge_eq_charge_comp_subdisc hσ₀ hc hr hrR hiso).symm

open Classical in
/-- **Conservation of local charges, in terms of the local charges of nearby leaves.** Under the
hypotheses of `eventually_exists_charge_comp_subdisc_eq_localCharge`, for every `w` near `w₀`
whose leaf meets `Z` in a finite set `s`, the local charges of the leaf over `w` at the points of
`s` inside `B(z₀, r)` add up to the local charge at `z₀` of the leaf over `w₀`. -/
theorem eventually_sum_localCharge_eq [LocallyPathConnectedSpace P] (hZ : IsClosed Z) {K : Set 𝔻}
    (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K) {z₀ : 𝔻}
    {r R : ℝ} (hc : ‖(z₀ : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ z, u (w₀, z) ∈ Z → (z : ℂ) ∈ ball (z₀ : ℂ) R → z = z₀) :
    ∀ᶠ w in 𝓝 w₀, ∀ s : Finset 𝔻, (∀ z, u (w, z) ∈ Z ↔ z ∈ s) →
      ∑ z ∈ s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) r, A.localCharge (u.curry w) z =
        A.localCharge (u.curry w₀) z₀ := by
  filter_upwards [A.eventually_exists_charge_comp_subdisc_eq_localCharge u hZ hK hKZ hc hr hrR
    hiso, hKZ] with w ⟨h', hw⟩ hwK s hs
  rw [← hw, A.charge_comp_subdisc_eq_sum_localCharge (isCompact_curry_preimage u hZ hK hwK) s hs
    hc hr h']

/-- **Retention of charged intersection points.** Under the hypotheses of
`eventually_exists_charge_comp_subdisc_eq_localCharge`, if the leaf over `w₀` has nonzero local
charge at `z₀`, then every leaf near it meets `Z` inside the disc `B(z₀, r)`. -/
theorem eventually_exists_mem_ball_of_localCharge_ne_zero [LocallyPathConnectedSpace P]
    (hZ : IsClosed Z) {K : Set 𝔻} (hK : IsCompact K) {w₀ : P}
    (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K) {z₀ : 𝔻} {r R : ℝ}
    (hc : ‖(z₀ : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ z, u (w₀, z) ∈ Z → (z : ℂ) ∈ ball (z₀ : ℂ) R → z = z₀)
    (h0 : A.localCharge (u.curry w₀) z₀ ≠ 0) :
    ∀ᶠ w in 𝓝 w₀, ∃ z, u (w, z) ∈ Z ∧ (z : ℂ) ∈ ball (z₀ : ℂ) r := by
  filter_upwards [A.eventually_exists_charge_comp_subdisc_eq_localCharge u hZ hK hKZ hc hr hrR
    hiso] with w ⟨h', hw⟩
  by_contra hmiss
  simp only [not_exists, not_and] at hmiss
  refine h0 ?_
  rw [← hw]
  exact A.charge_eq_zero _ h' fun ζ hζ ↦ hmiss _ hζ (mem_range_subdisc.1 ⟨ζ, rfl⟩)

open Classical in
/-- **Counting bound near a charged point.** Under the hypotheses of
`eventually_exists_charge_comp_subdisc_eq_localCharge`, let `v w : ℂ → Y` extend the leaf over `w`.
For every `w` near `w₀` such that `v w` is `J`-holomorphic on the unit disc, the leaf over `w`
meets `Z` in a finite set `s`, and the leaf is constant near no point of `s`, the leaf meets `Z`
inside `B(z₀, r)` in at most as many points as the local charge at `z₀` of the leaf over `w₀`. -/
theorem eventually_card_le_localCharge [LocallyPathConnectedSpace P] (hZ : IsClosed Z) {K : Set 𝔻}
    (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K) {z₀ : 𝔻}
    {r R : ℝ} (hc : ‖(z₀ : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ z, u (w₀, z) ∈ Z → (z : ℂ) ∈ ball (z₀ : ℂ) R → z = z₀) (v : P → ℂ → Y)
    (hv : ∀ w (z : 𝔻), v w z = u (w, z)) :
    ∀ᶠ w in 𝓝 w₀,
      IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J (v w)
        (ball 0 1) →
      ∀ s : Finset 𝔻, (∀ z, u (w, z) ∈ Z ↔ z ∈ s) →
      (∀ z ∈ s, ∀ ε > 0, ∃ z' : 𝔻, dist (z' : ℂ) z < ε ∧ u (w, z') ≠ u (w, z)) →
      ((s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) r).card : ℤ) ≤
        A.localCharge (u.curry w₀) z₀ := by
  filter_upwards [A.eventually_sum_localCharge_eq u hZ hK hKZ hc hr hrR hiso, hKZ] with
    w hw hwK hhol s hs hnc
  have h := isCompact_curry_preimage u hZ hK hwK
  rw [← hw s hs, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun z hz ↦ ?_
  have hzs := (Finset.mem_filter.1 hz).1
  obtain ⟨R', hR', hiso'⟩ := z.exists_pos_forall_mem_ball_eq s
  have hpos := A.localCharge_pos h (v w) (hv w) hhol ((hs z).2 hzs) hR'
    (fun z' hz' ↦ hiso' z' ((hs z').1 hz')) (hnc z hzs)
  omega

end TauCeti.PositiveCohomologyAssignment
