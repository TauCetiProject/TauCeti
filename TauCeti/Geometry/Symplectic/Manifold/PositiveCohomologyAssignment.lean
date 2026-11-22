/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Degree
public import TauCeti.Analysis.Complex.UnitDisc.Manifold
public import TauCeti.Analysis.Complex.UnitDisc.Subdisc
public import TauCeti.Geometry.Symplectic.JHolomorphic.ComplexDifferentiable
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Restriction
public import TauCeti.Geometry.Symplectic.Manifold.JHolomorphic
import TauCeti.Analysis.Normed.Module.Ball

/-!
# Positive cohomology assignments

Let `Y` be a manifold with an almost complex structure `J` and let `Z ⊆ Y`. Taubes reconstructs
a pseudoholomorphic curve with support `Z` from integer intersection numbers of `Z` with discs.
A **positive cohomology assignment** to `Z` (`TauCeti.PositiveCohomologyAssignment`) gives an
integer `I(σ)` to every continuous disc `σ : 𝔻 → Y` whose preimage `σ⁻¹(Z)` is compact, the
open-disc substitute for a disc whose boundary stays away from `Z`, subject to the following laws.

* **Vacuum.** `I(σ) = 0` when `σ` misses `Z`.
* **Homotopy.** `I` is constant along a homotopy whose total preimage of `Z` in `[0, 1] × 𝔻` is
  compact.
* **Degree.** `I(σ ∘ θ) = deg(θ) I(σ)` for every proper continuous `θ : 𝔻 → 𝔻`, with the
  homological degree `TauCeti.HomologicalOrientation.degree` of `θ`.
* **Additivity.** If finitely many disjoint round discs `B(cᵢ, rᵢ) ⊆ 𝔻` contain `σ⁻¹(Z)`, then
  `I(σ) = ∑ᵢ I(σ ∘ sᵢ)`, where `sᵢ = TauCeti.Complex.UnitDisc.subdisc cᵢ rᵢ` parametrizes
  `B(cᵢ, rᵢ)`. The family may be empty.
* **Positivity.** `I(σ) > 0` when `σ` is a nonconstant `J`-holomorphic disc meeting `Z`.

The disc `𝔻` is open; compactness of `σ⁻¹(Z)` replaces the condition that the boundary of a closed
disc misses `Z`. Additivity is required for round subdiscs, which is how it is used below and in
the reconstruction argument; it is implied by additivity over disjoint subdiscs parametrized by
arbitrary orientation-preserving embeddings.

The integers of a positive cohomology assignment are local. If `z` is an isolated point of
`σ⁻¹(Z)`, the integer of `σ` restricted to a small round disc about `z` does not depend on the
radius (`TauCeti.PositiveCohomologyAssignment.charge_comp_subdisc_eq_of_le`); this is the
**local charge** `TauCeti.PositiveCohomologyAssignment.localCharge` of `σ` at `z`, and, when
`σ⁻¹(Z)` is compact, it vanishes off `σ⁻¹(Z)`. When `σ⁻¹(Z)` is finite, `I(σ)` is the sum of
the local charges over `σ⁻¹(Z)`
(`TauCeti.PositiveCohomologyAssignment.charge_eq_sum_localCharge`). For a `J`-holomorphic disc
that is constant near none of the points of a finite `σ⁻¹(Z)`, every local charge is positive
(`TauCeti.PositiveCohomologyAssignment.localCharge_pos`), so `I(σ)` bounds the number of points of
`σ⁻¹(Z)` (`TauCeti.PositiveCohomologyAssignment.card_le_charge`) and vanishes only when `σ` misses
`Z` (`TauCeti.PositiveCohomologyAssignment.charge_eq_zero_iff`). These are the multiplicities that
the reconstruction attaches to the components of the curve.

Positive cohomology assignments are natural. An injective pseudoholomorphic map
`f : (Y', J') → (Y, J)` pulls a positive cohomology assignment to `Z` back to one to `f⁻¹(Z)`,
giving a disc `σ` in `Y'` the integer of `f ∘ σ`
(`TauCeti.PositiveCohomologyAssignment.comap`); pseudoholomorphicity of `f` preserves positivity,
and injectivity preserves nonconstancy. In particular a positive cohomology assignment restricts
to every open subset `U ⊆ Y` with the restricted almost complex structure
(`TauCeti.PositiveCohomologyAssignment.restrictOpen`), and is transported by every diffeomorphism
`h : Y' → Y` to `h⁻¹(Z)` with the pulled-back structure `h^* J`
(`TauCeti.PositiveCohomologyAssignment.pullback`). The integers and local charges are unchanged.
This is how the reconstruction, which is local, moves to a chart, where the curve near a point is
built.

## Main definitions

* `TauCeti.PositiveCohomologyAssignment J Z`: a positive cohomology assignment to `Z`.
* `TauCeti.PositiveCohomologyAssignment.localCharge`: the local charge of a disc at a point.
* `TauCeti.PositiveCohomologyAssignment.comap`: pullback along an injective pseudoholomorphic map.
* `TauCeti.PositiveCohomologyAssignment.restrictOpen`: restriction to an open subset.
* `TauCeti.PositiveCohomologyAssignment.pullback`: transport by a diffeomorphism.

## Main results

* `TauCeti.PositiveCohomologyAssignment.localCharge_eq_charge_comp_subdisc`: if `σ⁻¹(Z)` is
  compact and meets the disc `B(z, R)` only in `z`, the local charge of `σ` at `z` is the integer
  of `σ` on every round disc `B(z, r) ⊆ 𝔻` with `0 < r < R`.
* `TauCeti.PositiveCohomologyAssignment.charge_eq_sum_localCharge`: for finite `σ⁻¹(Z)`, `I(σ)` is
  the sum of the local charges.
* `TauCeti.PositiveCohomologyAssignment.card_le_charge`,
  `TauCeti.PositiveCohomologyAssignment.charge_eq_zero_iff`: for a `J`-holomorphic disc that is
  nowhere locally constant on a finite `σ⁻¹(Z)`, `I(σ)` is at least the number of its points, and
  is zero exactly when `σ` misses `Z`.
* `TauCeti.PositiveCohomologyAssignment.charge_restrictOpen`,
  `TauCeti.PositiveCohomologyAssignment.localCharge_restrictOpen`: a disc in an open subset `U` has
  the same integer and the same local charges for the restricted assignment as in `Y`.
* `TauCeti.PositiveCohomologyAssignment.charge_pullback`,
  `TauCeti.PositiveCohomologyAssignment.localCharge_pullback`: the same for transport by a
  diffeomorphism.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
-/

public section

noncomputable section

open Filter Metric Set Topology
open Complex.UnitDisc TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y]

/-- A **positive cohomology assignment** to a subset `Z` of an almost complex manifold `(Y, J)`:
an integer `charge σ h` for every continuous disc `σ : 𝔻 → Y` with compact preimage `σ⁻¹(Z)`,
which vanishes on discs missing `Z`, is invariant under homotopies with compact total preimage of
`Z`, multiplies by the degree under proper reparametrizations, is additive over disjoint round
subdiscs containing `σ⁻¹(Z)`, and is positive on nonconstant `J`-holomorphic discs meeting `Z`. -/
structure PositiveCohomologyAssignment (J : SmoothAlmostComplexStructure I Y) (Z : Set Y) where
  /-- The integer assigned to a disc whose preimage of `Z` is compact. -/
  charge (σ : C(𝔻, Y)) : IsCompact (σ ⁻¹' Z) → ℤ
  /-- A disc missing `Z` has integer zero. -/
  charge_eq_zero (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' Z)) (hZ : ∀ z, σ z ∉ Z) : charge σ h = 0
  /-- The integer is invariant under homotopies with compact total preimage of `Z`. -/
  charge_eq_of_homotopy {σ₀ σ₁ : C(𝔻, Y)} (F : σ₀.Homotopy σ₁)
    (hF : IsCompact ((F : unitInterval × 𝔻 → Y) ⁻¹' Z)) (h₀ : IsCompact (σ₀ ⁻¹' Z))
    (h₁ : IsCompact (σ₁ ⁻¹' Z)) : charge σ₀ h₀ = charge σ₁ h₁
  /-- The integer multiplies by the degree under a proper reparametrization of the disc. -/
  charge_comp (o : HomologicalOrientation 𝔻 ℂ 2) (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' Z))
    (θ : C(𝔻, 𝔻)) (hθ : IsProperMap θ) (h' : IsCompact ((σ.comp θ) ⁻¹' Z)) :
    charge (σ.comp θ) h' = o.degree o Complex.finrank_real_complex θ * charge σ h
  /-- The integer is additive over finitely many disjoint round subdiscs containing `σ⁻¹(Z)`. -/
  charge_eq_sum {ι : Type} [Fintype ι] (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' Z)) (c : ι → ℂ)
    (r : ι → ℝ) (hc : ∀ i, ‖c i‖ + r i ≤ 1) (hr : ∀ i, 0 < r i)
    (hdisj : Pairwise fun i j ↦ Disjoint (ball (c i) (r i)) (ball (c j) (r j)))
    (hcov : ∀ z, σ z ∈ Z → ∃ i, (z : ℂ) ∈ ball (c i) (r i))
    (h' : ∀ i, IsCompact ((σ.comp (subdisc (c i) (r i) (hc i) (hr i))) ⁻¹' Z)) :
    charge σ h = ∑ i, charge _ (h' i)
  /-- A nonconstant `J`-holomorphic disc meeting `Z` has positive integer. -/
  charge_pos (σ : C(𝔻, Y)) (h : IsCompact (σ ⁻¹' Z)) (u : ℂ → Y) (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1))
    (hnc : ∃ z w, σ z ≠ σ w) (hZ : ∃ z, σ z ∈ Z) : 0 < charge σ h

namespace PositiveCohomologyAssignment

variable {J : SmoothAlmostComplexStructure I Y} {Z : Set Y} (A : PositiveCohomologyAssignment J Z)

/-- A positive cohomology assignment is determined by its integers. -/
@[ext]
theorem ext {A B : PositiveCohomologyAssignment J Z}
    (h : ∀ σ hσ, A.charge σ hσ = B.charge σ hσ) : A = B := by
  cases A
  cases B
  congr
  funext σ hσ
  exact h σ hσ

/-- The integer of a disc depends only on the disc. -/
theorem charge_congr {σ σ' : C(𝔻, Y)} (hσ : σ = σ') (h : IsCompact (σ ⁻¹' Z))
    (h' : IsCompact (σ' ⁻¹' Z)) : A.charge σ h = A.charge σ' h' := by
  subst hσ
  rfl

/-! ### Restriction to round subdiscs -/

/-- If every point of `σ⁻¹(Z)` in the disc `B(c, r')` lies in the smaller disc `B(c, r)`, the
integers of `σ` on the round subdiscs `B(c, r)` and `B(c, r')` agree for `0 < r ≤ r'`. -/
theorem charge_comp_subdisc_eq_of_le {σ : C(𝔻, Y)} {c : ℂ} {r r' : ℝ} (hc : ‖c‖ + r ≤ 1)
    (hc' : ‖c‖ + r' ≤ 1) (hr : 0 < r) (hrr' : r ≤ r')
    (hsub : ∀ z, σ z ∈ Z → (z : ℂ) ∈ ball c r' → (z : ℂ) ∈ ball c r)
    (h : IsCompact ((σ.comp (subdisc c r hc hr)) ⁻¹' Z))
    (h' : IsCompact ((σ.comp (subdisc c r' hc' (hr.trans_le hrr'))) ⁻¹' Z)) :
    A.charge _ h = A.charge _ h' := by
  have hr' : 0 < r' := hr.trans_le hrr'
  set τ := σ.comp (subdisc c r' hc' hr')
  have h0 : ‖(0 : ℂ)‖ + r / r' ≤ 1 := by
    rw [norm_zero, zero_add]
    exact (div_le_one hr').2 hrr'
  have hpos : 0 < r / r' := div_pos hr hr'
  have hr0 : (r' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr'.ne'
  have heq : τ.comp (subdisc 0 (r / r') h0 hpos) = σ.comp (subdisc c r hc hr) := by
    ext z
    simp only [τ, ContinuousMap.comp_apply]
    congr 1
    apply coe_injective
    simp only [coe_subdisc_apply, Complex.ofReal_div]
    field_simp
    ring
  have hcov : ∀ z, τ z ∈ Z → ∃ _ : Unit, (z : ℂ) ∈ ball 0 (r / r') := by
    intro z hz
    refine ⟨(), ?_⟩
    have hmem := hsub _ hz (mem_range_subdisc.1 ⟨z, rfl⟩)
    rw [mem_ball_zero_iff, lt_div_iff₀ hr']
    simpa [dist_eq_norm, abs_of_pos hr', mul_comm] using hmem
  have h'' : IsCompact ((τ.comp (subdisc 0 (r / r') h0 hpos)) ⁻¹' Z) := heq ▸ h
  rw [A.charge_eq_sum τ h' (fun _ ↦ 0) (fun _ ↦ r / r') (fun _ ↦ h0) (fun _ ↦ hpos)
    (Subsingleton.pairwise) hcov (fun _ ↦ h''), Fintype.sum_unique]
  exact (A.charge_congr heq _ _).symm

/-- If `σ⁻¹(Z)` is compact and meets the disc `B(z, R)` only in `z`, then the restriction of `σ`
to the round subdisc `B(z, r)` has compact preimage of `Z` for every `0 < r < R`: no point of
`σ⁻¹(Z)` lies on the circle `‖w - z‖ = r`. -/
theorem isCompact_preimage_comp_subdisc_of_isolated {σ : C(𝔻, Y)} (hσ : IsCompact (σ ⁻¹' Z))
    {z : 𝔻} {r R : ℝ} (hc : ‖(z : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ w, σ w ∈ Z → (w : ℂ) ∈ ball (z : ℂ) R → w = z) :
    IsCompact ((σ.comp (subdisc z r hc hr)) ⁻¹' Z) := by
  rw [ContinuousMap.coe_comp, preimage_comp]
  refine isCompact_subdisc_preimage hσ fun w hw hwr ↦ ?_
  have hwz := hiso w hw (by rwa [mem_ball, dist_eq_norm, hwr])
  rw [hwz, sub_self, norm_zero] at hwr
  exact hr.ne hwr

/-! ### Local charges -/

open Classical in
/-- The **local charge** of a disc `σ` at `z ∈ 𝔻`: the limit, as the radius `r` tends to `0`, of
the integer of `σ` on the round disc `B(z, r)`, with value `0` for a radius at which that disc is
not defined or the restriction of `σ` does not have compact preimage of `Z`. It is meaningful when
these integers are eventually constant, which holds at an isolated point of a compact `σ⁻¹(Z)`:
there it is the integer of `σ` on every small enough round disc about `z`
(`TauCeti.PositiveCohomologyAssignment.localCharge_eq_charge_comp_subdisc`). Otherwise, for
instance at a non-isolated point of `σ⁻¹(Z)`, it is an unspecified junk value. -/
def localCharge (σ : C(𝔻, Y)) (z : 𝔻) : ℤ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r ↦
    if h : ∃ (hc : ‖(z : ℂ)‖ + r ≤ 1) (hr : 0 < r),
        IsCompact ((σ.comp (subdisc z r hc hr)) ⁻¹' Z) then
      A.charge _ h.choose_spec.choose_spec
    else 0

/-- **The local charge at an isolated point.** If `σ⁻¹(Z)` is compact and meets the disc
`B(z, R)` only in `z`, then the local charge of `σ` at `z` is the integer of `σ` on the round
disc `B(z, r)` for every `0 < r < R` with `B(z, r) ⊆ 𝔻`. -/
theorem localCharge_eq_charge_comp_subdisc {σ : C(𝔻, Y)} (hσ : IsCompact (σ ⁻¹' Z)) {z : 𝔻}
    {r R : ℝ} (hc : ‖(z : ℂ)‖ + r ≤ 1) (hr : 0 < r) (hrR : r < R)
    (hiso : ∀ w, σ w ∈ Z → (w : ℂ) ∈ ball (z : ℂ) R → w = z) :
    A.localCharge σ z =
      A.charge _ (isCompact_preimage_comp_subdisc_of_isolated hσ hc hr hrR hiso) := by
  refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
  filter_upwards [Ioc_mem_nhdsGT hr] with r' ⟨hr', hr'r⟩
  have hc' : ‖(z : ℂ)‖ + r' ≤ 1 := by linarith
  have h' := isCompact_preimage_comp_subdisc_of_isolated hσ hc' hr' (hr'r.trans_lt hrR) hiso
  rw [dite_eq_left ⟨hc', hr', h'⟩]
  refine (A.charge_comp_subdisc_eq_of_le hc' hc hr' hr'r (fun w hw hwb ↦ ?_) _ _).symm
  rw [hiso w hw (ball_subset_ball hrR.le hwb)]
  exact mem_ball_self hr'

/-- The local charge vanishes at points that `σ` does not send into `Z`. -/
theorem localCharge_eq_zero {σ : C(𝔻, Y)} (hσ : IsCompact (σ ⁻¹' Z)) {z : 𝔻} (hz : σ z ∉ Z) :
    A.localCharge σ z = 0 := by
  -- The compact set `σ⁻¹(Z)` stays a positive distance `ε` away from `z`.
  obtain ⟨ε, hε, hmiss⟩ := exists_pos_forall_notMem_ball (hσ.image continuous_coe).isClosed hz
  obtain ⟨r, hr, hrε, hc⟩ := exists_pos_lt_and_norm_add_le_one z hε
  have hiso : ∀ w, σ w ∈ Z → (w : ℂ) ∈ ball (z : ℂ) ε → w = z :=
    fun w hw hwb ↦ (hmiss w hw hwb).elim
  rw [A.localCharge_eq_charge_comp_subdisc hσ hc hr hrε hiso]
  refine A.charge_eq_zero _ _ fun w hw ↦ hmiss _ hw ?_
  exact ball_subset_ball hrε.le (mem_range_subdisc.1 ⟨w, rfl⟩)

/-- **Additivity of local charges.** If `σ⁻¹(Z)` is the finite set `s`, the integer of `σ` is the
sum of its local charges at the points of `s`. -/
theorem charge_eq_sum_localCharge {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' Z)) (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) : A.charge σ h = ∑ z ∈ s, A.localCharge σ z := by
  -- Choose one radius `r` small enough that the discs `B(z, r)`, `z ∈ s`, lie in `𝔻` and are
  -- pairwise at distance more than `r`.
  have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioi 0 ∧ (∀ z ∈ s, r < 1 - ‖(z : ℂ)‖) ∧
      ∀ z ∈ s, ∀ w ∈ s, w ≠ z → 2 * r < dist (w : ℂ) z := by
    refine eventually_mem_nhdsWithin.and (((Finset.eventually_all s).2 fun z _ ↦ ?_).and
      ((Finset.eventually_all s).2 fun z _ ↦ (Finset.eventually_all s).2 fun w _ ↦ ?_))
    · exact (eventually_lt_nhds (by linarith [z.norm_lt_one])).filter_mono nhdsWithin_le_nhds
    · by_cases hwz : w = z
      · exact Eventually.of_forall fun _ h ↦ (h hwz).elim
      · have hd : 0 < dist (w : ℂ) z / 2 := half_pos (dist_pos.2 fun h ↦ hwz (coe_injective h))
        exact ((eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds).mono
          fun r hr _ ↦ by linarith
  obtain ⟨r, hr, hrs, hsep⟩ := hev.exists
  replace hr : 0 < r := mem_Ioi.1 hr
  have hc : ∀ z : s, ‖((z : 𝔻) : ℂ)‖ + r ≤ 1 := fun z ↦ by linarith [hrs z z.property]
  have hdisj : Pairwise fun z w : s ↦
      Disjoint (ball ((z : 𝔻) : ℂ) r) (ball ((w : 𝔻) : ℂ) r) := by
    intro z w hzw
    refine ball_disjoint_ball ?_
    have := hsep z z.property w w.property fun h ↦ hzw (Subtype.ext h.symm)
    rw [dist_comm] at this
    linarith
  have hcov : ∀ z, σ z ∈ Z → ∃ w : s, (z : ℂ) ∈ ball ((w : 𝔻) : ℂ) r :=
    fun z hz ↦ ⟨⟨z, (hs z).1 hz⟩, mem_ball_self hr⟩
  have hadm : ∀ z : s, IsCompact ((σ.comp (subdisc _ r (hc z) hr)) ⁻¹' Z) := fun z ↦ by
    rw [ContinuousMap.coe_comp, preimage_comp]
    -- No point of `σ⁻¹(Z)` lies on the circle `‖w - z‖ = r`: it lies in one of the discs.
    refine isCompact_subdisc_preimage h fun w hw ↦ ?_
    obtain ⟨y, hy⟩ := hcov w hw
    obtain rfl | hzy := eq_or_ne z y
    · exact (mem_ball_iff_norm.1 hy).ne
    · exact norm_sub_ne_of_disjoint_ball hr.ne' (hdisj hzy) hy
  rw [A.charge_eq_sum σ h (fun z : s ↦ ((z : 𝔻) : ℂ)) (fun _ ↦ r) hc (fun _ ↦ hr) hdisj hcov hadm,
    ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun z _ ↦ (A.localCharge_eq_charge_comp_subdisc h (hc z) hr
    (by linarith : r < 2 * r) (fun w hw hwb ↦ ?_)).symm
  by_contra hwz
  have := hsep z z.property w ((hs w).1 hw) hwz
  rw [mem_ball] at hwb
  linarith

/-! ### Positivity -/

/-- **Positivity of local charges.** Let `σ` be the restriction to `𝔻` of a map `u` that is
`J`-holomorphic on the unit disc, with `σ⁻¹(Z)` compact. At an isolated point `z` of `σ⁻¹(Z)` near
which `σ` is not constant, the local charge of `σ` is positive. -/
theorem localCharge_pos {σ : C(𝔻, Y)} (hσ : IsCompact (σ ⁻¹' Z)) (u : ℂ → Y)
    (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1))
    {z : 𝔻} (hz : σ z ∈ Z) {R : ℝ} (hR : 0 < R)
    (hiso : ∀ w, σ w ∈ Z → (w : ℂ) ∈ ball (z : ℂ) R → w = z)
    (hnc : ∀ ε > 0, ∃ w : 𝔻, dist (w : ℂ) z < ε ∧ σ w ≠ σ z) :
    0 < A.localCharge σ z := by
  obtain ⟨r, hr, hrR, hc⟩ := exists_pos_lt_and_norm_add_le_one z hR
  have h := isCompact_preimage_comp_subdisc_of_isolated hσ hc hr hrR hiso
  rw [A.localCharge_eq_charge_comp_subdisc hσ hc hr hrR hiso]
  set s := subdisc (z : ℂ) r hc hr
  have hs0 : s 0 = z := coe_injective (by simp [s])
  refine A.charge_pos _ h (fun w ↦ u (z + r * w)) (fun w ↦ ?_) ?_ ?_ ⟨0, ?_⟩
  · rw [ContinuousMap.comp_apply, ← hu, coe_subdisc_apply]
  · refine hhol.comp ((isPseudoholomorphicOn_constSmooth_iff _ _ _ _).2
      (DifferentiableOn.isConstStructureJHolomorphicOn_ofComplexModule (by fun_prop)))
      fun w hw ↦ ?_
    simpa using norm_add_mul_lt_one hc hr (Complex.UnitDisc.mk w (mem_ball_zero_iff.1 hw))
  · obtain ⟨w, hwz, hσw⟩ := hnc r hr
    obtain ⟨w', rfl⟩ := (mem_range_subdisc (hc := hc) (hr := hr)).2 (mem_ball.2 hwz)
    exact ⟨w', 0, by simpa [hs0] using hσw⟩
  · simpa [hs0] using hz

/-- **Counting bound.** If `σ` is the restriction to `𝔻` of a map that is `J`-holomorphic on the
unit disc, `σ⁻¹(Z)` is the finite set `s`, and `σ` is constant near no point of `s`, then the
integer of `σ` is at least the number of points of `s`. -/
theorem card_le_charge {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' Z)) (u : ℂ → Y)
    (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1))
    (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s)
    (hnc : ∀ z ∈ s, ∀ ε > 0, ∃ w : 𝔻, dist (w : ℂ) z < ε ∧ σ w ≠ σ z) :
    (s.card : ℤ) ≤ A.charge σ h := by
  rw [A.charge_eq_sum_localCharge h s hs, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine Finset.sum_le_sum fun z hz ↦ ?_
  -- The other points of the finite set `s` form a closed set missing `z`.
  classical
  obtain ⟨R, hR, hRs⟩ := exists_pos_forall_notMem_ball
    ((s.erase z).finite_toSet.image ((↑) : 𝔻 → ℂ)).isClosed (z := z) (by simp)
  refine A.localCharge_pos h u hu hhol ((hs z).2 hz) hR (fun w hw hwb ↦ ?_) (hnc z hz)
  by_contra hwz
  exact hRs w (Finset.mem_erase.2 ⟨hwz, (hs w).1 hw⟩) hwb

/-- Under the hypotheses of `TauCeti.PositiveCohomologyAssignment.card_le_charge`, the integer of
`σ` vanishes exactly when `σ` misses `Z`. -/
theorem charge_eq_zero_iff {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' Z)) (u : ℂ → Y)
    (hu : ∀ z : 𝔻, u z = σ z)
    (hhol : IsPseudoholomorphicOn (AlmostComplexStructure.ofComplexModule ℂ).constSmooth J u
      (ball 0 1))
    (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s)
    (hnc : ∀ z ∈ s, ∀ ε > 0, ∃ w : 𝔻, dist (w : ℂ) z < ε ∧ σ w ≠ σ z) :
    A.charge σ h = 0 ↔ ∀ z, σ z ∉ Z := by
  refine ⟨fun h0 z hz ↦ ?_, A.charge_eq_zero σ h⟩
  have := A.card_le_charge h u hu hhol s hs hnc
  rw [h0, Nat.cast_nonpos, Finset.card_eq_zero] at this
  simpa [this] using (hs z).1 hz

/-! ### Naturality -/

section Naturality

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {Y' : Type*} [TopologicalSpace Y']
  [ChartedSpace H' Y'] [IsManifold I' ∞ Y'] {J' : SmoothAlmostComplexStructure I' Y'}
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] {H'' : Type*}
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {Y'' : Type*} [TopologicalSpace Y'']
  [ChartedSpace H'' Y''] [IsManifold I'' ∞ Y''] {J'' : SmoothAlmostComplexStructure I'' Y''}

/-- **Pullback of a positive cohomology assignment** along an injective pseudoholomorphic map
`f : (Y', J') → (Y, J)`: the integer of a disc `σ` in `Y'` whose preimage of `f⁻¹(Z)` is compact is
the integer of `f ∘ σ`. Injectivity keeps nonconstant discs nonconstant, and pseudoholomorphicity
keeps `J'`-holomorphic discs `J`-holomorphic. -/
def comap (f : C(Y', Y)) (hf : IsPseudoholomorphic J' J f) (hinj : Function.Injective f) :
    PositiveCohomologyAssignment J' (f ⁻¹' Z) where
  charge σ h := A.charge (f.comp σ) h
  charge_eq_zero σ h hZ := A.charge_eq_zero _ h hZ
  charge_eq_of_homotopy F hF h₀ h₁ :=
    A.charge_eq_of_homotopy ((ContinuousMap.Homotopy.refl f).comp F) hF h₀ h₁
  charge_comp o σ h θ hθ h' := A.charge_comp o (f.comp σ) h θ hθ h'
  charge_eq_sum σ h c r hc hr hdisj hcov h' := A.charge_eq_sum (f.comp σ) h c r hc hr hdisj hcov h'
  charge_pos σ h u hu hhol hnc hZ := by
    obtain ⟨z, w, hzw⟩ := hnc
    exact A.charge_pos (f.comp σ) h (f ∘ u) (fun z ↦ congrArg f (hu z))
      ((hf.isPseudoholomorphicOn univ).comp hhol (mapsTo_univ _ _)) ⟨z, w, hinj.ne hzw⟩ hZ

variable (f : C(Y', Y)) (hf : IsPseudoholomorphic J' J f) (hinj : Function.Injective f)

/-- The integer of a disc for the pulled-back assignment is the integer of its image. -/
@[simp]
theorem charge_comap (σ : C(𝔻, Y')) (h : IsCompact (σ ⁻¹' (f ⁻¹' Z))) :
    (A.comap f hf hinj).charge σ h = A.charge (f.comp σ) h :=
  (rfl)

/-- If `σ = f ∘ σ'`, the integer of `σ'` for the pulled-back assignment is the integer of `σ`. -/
theorem charge_comap_of_comp_eq {σ' : C(𝔻, Y')} {σ : C(𝔻, Y)} (hσ : f.comp σ' = σ)
    (h' : IsCompact (σ' ⁻¹' (f ⁻¹' Z))) (h : IsCompact (σ ⁻¹' Z)) :
    (A.comap f hf hinj).charge σ' h' = A.charge σ h :=
  A.charge_congr hσ _ _

/-- The local charges of the pulled-back assignment are the local charges of the image discs. -/
@[simp]
theorem localCharge_comap (σ : C(𝔻, Y')) (z : 𝔻) :
    (A.comap f hf hinj).localCharge σ z = A.localCharge (f.comp σ) z :=
  -- Both sides test compactness of the same set and evaluate the same integer: `(σ ∘ τ)⁻¹'
  -- (f⁻¹' Z)` and `((f ∘ σ) ∘ τ)⁻¹' Z` agree definitionally because `ContinuousMap.comp` and
  -- `Set.preimage` unfold to function composition, so `ContinuousMap.comp_assoc` is `rfl`.
  (rfl)

/-- If `σ = f ∘ σ'`, the local charges of `σ'` for the pulled-back assignment are those of `σ`. -/
theorem localCharge_comap_of_comp_eq {σ' : C(𝔻, Y')} {σ : C(𝔻, Y)} (hσ : f.comp σ' = σ)
    (z : 𝔻) : (A.comap f hf hinj).localCharge σ' z = A.localCharge σ z := by
  rw [localCharge_comap, hσ]

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem comap_id :
    A.comap (ContinuousMap.id Y) (isPseudoholomorphic_id J) Function.injective_id = A :=
  -- `(ContinuousMap.id Y).comp σ` reduces to `σ` by structure eta (`ContinuousMap.id_comp` is
  -- `rfl`), so every field of the pulled-back assignment is that of `A`.
  (rfl)

/-- Pulling back is functorial: pulling back along `f` and then along `g` is pulling back along
`f ∘ g`. -/
theorem comap_comap (g : C(Y'', Y')) (hg : IsPseudoholomorphic J'' J' g)
    (hginj : Function.Injective g) :
    (A.comap f hf hinj).comap g hg hginj = A.comap (f.comp g) (hf.comp hg) (hinj.comp hginj) :=
  -- The `charge` fields agree because `ContinuousMap.comp_assoc` and `Set.preimage_comp` hold by
  -- `rfl`; the remaining fields are proofs, which agree by proof irrelevance.
  (rfl)

end Naturality

/-! ### Restriction to open subsets and transport by diffeomorphisms -/

/-- **Restriction of a positive cohomology assignment** to an open subset `U ⊆ Y`, with the
restricted almost complex structure: the integer of a disc in `U` is its integer as a disc in
`Y`. -/
def restrictOpen (U : TopologicalSpace.Opens Y) :
    PositiveCohomologyAssignment (J.restrictOpen U) ((Subtype.val : U → Y) ⁻¹' Z) :=
  A.comap ⟨Subtype.val, continuous_subtypeVal⟩ (J.isPseudoholomorphic_subtype_val U)
    Subtype.val_injective

/-- The restricted assignment is the pullback along the inclusion `U → Y`. -/
theorem restrictOpen_def (U : TopologicalSpace.Opens Y) :
    A.restrictOpen U = A.comap ⟨Subtype.val, continuous_subtypeVal⟩
      (J.isPseudoholomorphic_subtype_val U) Subtype.val_injective :=
  (rfl)

/-- The integer of a disc `σ'` in an open subset `U` for the restricted assignment is the integer
of any disc `σ` in `Y` that agrees with `σ'`. -/
theorem charge_restrictOpen (U : TopologicalSpace.Opens Y) {σ' : C(𝔻, U)} {σ : C(𝔻, Y)}
    (hσ : ∀ z, (σ' z : Y) = σ z) (h' : IsCompact (σ' ⁻¹' ((Subtype.val : U → Y) ⁻¹' Z)))
    (h : IsCompact (σ ⁻¹' Z)) : (A.restrictOpen U).charge σ' h' = A.charge σ h :=
  A.charge_comap_of_comp_eq ⟨Subtype.val, continuous_subtypeVal⟩ _ _ (ContinuousMap.ext hσ) h' h

/-- The local charges of the restricted assignment are those of the discs in `Y`. -/
theorem localCharge_restrictOpen (U : TopologicalSpace.Opens Y) {σ' : C(𝔻, U)} {σ : C(𝔻, Y)}
    (hσ : ∀ z, (σ' z : Y) = σ z) (z : 𝔻) :
    (A.restrictOpen U).localCharge σ' z = A.localCharge σ z :=
  A.localCharge_comap_of_comp_eq ⟨Subtype.val, continuous_subtypeVal⟩ _ _ (ContinuousMap.ext hσ) z

section Pullback

variable [FiniteDimensional ℝ E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] {H' : Type*}
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} {Y' : Type*} [TopologicalSpace Y']
  [ChartedSpace H' Y'] [IsManifold I' ∞ Y']

/-- **Transport of a positive cohomology assignment by a diffeomorphism** `h : Y' → Y`, to
`h⁻¹(Z)` with the pulled-back almost complex structure `h^* J`: the integer of a disc `σ` in `Y'` is
the integer of `h ∘ σ`. -/
def pullback (h : Y' ≃ₘ⟮I', I⟯ Y) :
    PositiveCohomologyAssignment (J.pullback h) (h ⁻¹' Z) :=
  A.comap ⟨h, h.continuous⟩ (SmoothAlmostComplexStructure.isPseudoholomorphic_pullback h J)
    h.injective

/-- The transported assignment is the pullback along the underlying map of `h`. -/
theorem pullback_def (h : Y' ≃ₘ⟮I', I⟯ Y) :
    A.pullback h = A.comap ⟨h, h.continuous⟩
      (SmoothAlmostComplexStructure.isPseudoholomorphic_pullback h J) h.injective :=
  (rfl)

/-- The integer of a disc for the transported assignment is the integer of its image. -/
theorem charge_pullback (h : Y' ≃ₘ⟮I', I⟯ Y) {σ' : C(𝔻, Y')} {σ : C(𝔻, Y)}
    (hσ : ∀ z, h (σ' z) = σ z) (h' : IsCompact (σ' ⁻¹' (h ⁻¹' Z))) (hc : IsCompact (σ ⁻¹' Z)) :
    (A.pullback h).charge σ' h' = A.charge σ hc :=
  A.charge_comap_of_comp_eq ⟨h, h.continuous⟩ _ _ (ContinuousMap.ext hσ) h' hc

/-- The local charges of the transported assignment are those of the image discs. -/
theorem localCharge_pullback (h : Y' ≃ₘ⟮I', I⟯ Y) {σ' : C(𝔻, Y')} {σ : C(𝔻, Y)}
    (hσ : ∀ z, h (σ' z) = σ z) (z : 𝔻) :
    (A.pullback h).localCharge σ' z = A.localCharge σ z :=
  A.localCharge_comap_of_comp_eq ⟨h, h.continuous⟩ _ _ (ContinuousMap.ext hσ) z

end Pullback

end PositiveCohomologyAssignment

end TauCeti
