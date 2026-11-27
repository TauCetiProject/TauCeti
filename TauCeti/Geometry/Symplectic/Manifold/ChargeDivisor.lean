/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.DiscFamilyCharge
public import TauCeti.RingTheory.Polynomial.PrescribedPowerSums
import TauCeti.Topology.Compactness.Compact

/-!
# The charge divisor of a disc and its continuity along a family of discs

Let `I` be a positive cohomology assignment to a closed set `Z` in an almost complex manifold
`(Y, J)` (`TauCeti.PositiveCohomologyAssignment`), and let `σ : 𝔻 → Y` be a disc meeting `Z` in a
finite set. Weighting each point `z` of `σ⁻¹(Z)` by its local charge `I_z(σ)` gives the
**charge divisor** `∑_z I_z(σ) [z]` of `σ`. This file records it in two forms:

* the **charge-weighted sum** `∑_z I_z(σ) g(z)` of a function `g` on the disc
  (`TauCeti.PositiveCohomologyAssignment.chargeSum`), the pairing of the divisor with `g`;
* the **charge multiset** containing each `z` with multiplicity `I_z(σ)`
  (`TauCeti.PositiveCohomologyAssignment.chargeMultiset`). When the local charges are
  nonnegative, as for a `J`-holomorphic disc
  (`TauCeti.PositiveCohomologyAssignment.localCharge_nonneg_of_finite`), its cardinality is the
  integer `I(σ)` and summing a function over it gives the charge-weighted sum.

In Taubes's reconstruction of a pseudoholomorphic curve from a positive cohomology assignment, a
neighbourhood of a point of `Z` is foliated by `J`-holomorphic discs `σ_w`, and the curve is read
off the charge divisors of the leaves. The main result is that these divisors move continuously
with the leaf. Let `u : P × 𝔻 → Y` be a continuous family of discs whose leaves `σ_w = u (w, ·)`
meet `Z` only inside a fixed compact set for `w` near `w₀`, with `σ_{w₀}⁻¹(Z)` finite. Along a
filter `l ≤ 𝓝 w₀` on which the leaves meet `Z` in finite sets with nonnegative local charges,

`∑_z I_z(σ_w) g(z) → ∑_z I_z(σ_{w₀}) g(z)`

for every function `g` continuous at the points of `σ_{w₀}⁻¹(Z)`
(`TauCeti.PositiveCohomologyAssignment.tendsto_chargeSum`). This is the quantitative form of the
conservation of local charges
(`TauCeti.PositiveCohomologyAssignment.eventually_sum_localCharge_eq`): near each point `z₀` of
`σ_{w₀}⁻¹(Z)` the local charges of a nearby leaf add up to `I_{z₀}(σ_{w₀})`, and since they are
nonnegative their total stays bounded. For `J`-holomorphic leaves, `l` can be the restriction of
`𝓝 w₀` to the parameters whose leaves meet `Z` finitely, the nonnegativity then coming from
`TauCeti.PositiveCohomologyAssignment.localCharge_nonneg_of_finite`. When `P` is a
finite-dimensional real normed space with an additive Haar measure and `u⁻¹(Z)` has locally
finite `μH[dim P]`, almost every leaf with compact `σ_w⁻¹(Z)` meets `Z` in a finite set
(`TauCeti.PositiveCohomologyAssignment.ae_charge_eq_sum_localCharge`); this holds for instance
when `u` is a local diffeomorphism and `Z` has locally finite `μH[dim P]`.

Taking `g(z) = zᵏ`, the power sums of the charge multisets converge, and by Newton's identities so
do their elementary symmetric functions
(`TauCeti.PositiveCohomologyAssignment.tendsto_esymm_chargeMultiset`). Up to sign these are the
coefficients of the monic polynomial `∏_z (X - z)^{I_z(σ_w)}`, whose roots are the points of
positive charge, for a `J`-holomorphic leaf all the points where it meets `Z`. So, in the leaf
coordinate, the intersections of the leaves with `Z` are the roots of monic polynomials whose
coefficients depend continuously on the leaf.

## Main definitions

* `TauCeti.PositiveCohomologyAssignment.chargeSum A σ g`: the charge-weighted sum
  `∑_z I_z(σ) g(z)`.
* `TauCeti.PositiveCohomologyAssignment.chargeMultiset A σ`: the multiset of the points of
  `σ⁻¹(Z)`, each counted with its local charge.

## Main results

* `TauCeti.PositiveCohomologyAssignment.chargeSum_eq_sum`: the charge-weighted sum as a finite
  sum.
* `TauCeti.PositiveCohomologyAssignment.chargeSum_const`: for a constant function it is the
  integer of the disc times the constant.
* `TauCeti.PositiveCohomologyAssignment.count_chargeMultiset`,
  `TauCeti.PositiveCohomologyAssignment.card_chargeMultiset`,
  `TauCeti.PositiveCohomologyAssignment.sum_map_chargeMultiset`: multiplicities, cardinality and
  sums over the charge multiset.
* `TauCeti.PositiveCohomologyAssignment.tendsto_chargeSum`: continuity of the charge-weighted sums
  along a family of discs.
* `TauCeti.PositiveCohomologyAssignment.localCharge_nonneg_of_eventually`: nonnegative charges on
  the nearby leaves force nonnegative charges on the limit leaf.
* `TauCeti.PositiveCohomologyAssignment.tendsto_esymm_chargeMultiset`: continuity of the
  elementary symmetric functions of the charge multisets.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 6.
-/

public section

noncomputable section

open Filter Metric Set Topology
open Complex.UnitDisc TauCeti.Complex.UnitDisc
open scoped Complex.UnitDisc Manifold ContDiff

namespace TauCeti.PositiveCohomologyAssignment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H Y]
  [IsManifold I ∞ Y] {J : SmoothAlmostComplexStructure I Y} {Z : Set Y}
  (A : PositiveCohomologyAssignment J Z)

/-! ### The charge-weighted sum -/

section ChargeSum

variable {F : Type*} [AddCommGroup F]

/-- The **charge-weighted sum** `∑_z I_z(σ) g(z)` of a function `g` on the disc, over the points
`z` of `σ⁻¹(Z)` weighted by the local charges of `σ`: the pairing of `g` with the charge divisor of
`σ`. It is a finite sum when `σ⁻¹(Z)` is finite
(`TauCeti.PositiveCohomologyAssignment.chargeSum_eq_sum`), and `0` by convention when the sum has
infinitely many nonzero terms. -/
def chargeSum (σ : C(𝔻, Y)) (g : 𝔻 → F) : F :=
  ∑ᶠ z, A.localCharge σ z • g z

/-- The charge-weighted sum unfolds to the `finsum` of the local charges times the values of `g`,
whether or not `σ⁻¹(Z)` is finite. -/
theorem chargeSum_def (σ : C(𝔻, Y)) (g : 𝔻 → F) :
    A.chargeSum σ g = ∑ᶠ z, A.localCharge σ z • g z :=
  (rfl)

/-- If `σ⁻¹(Z)` is the finite set `s`, the charge-weighted sum is the sum over `s` of the local
charges times the values of `g`. -/
theorem chargeSum_eq_sum {σ : C(𝔻, Y)} (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (g : 𝔻 → F) :
    A.chargeSum σ g = ∑ z ∈ s, A.localCharge σ z • g z :=
  finsum_eq_sum_of_support_subset _ fun z hz ↦ by_contra fun hzs ↦
    hz (by simp [A.localCharge_eq_zero_of_notMem s hs hzs])

/-- For a constant function the charge-weighted sum is the integer of the disc times the constant,
when `σ⁻¹(Z)` is finite. -/
theorem chargeSum_const {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' Z)) (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (c : F) :
    A.chargeSum σ (fun _ ↦ c) = A.charge σ h • c := by
  rw [A.chargeSum_eq_sum s hs, ← Finset.sum_smul, A.charge_eq_sum_localCharge h s hs]

/-- The charge-weighted sum is additive in the function, when `σ⁻¹(Z)` is finite. -/
theorem chargeSum_add {σ : C(𝔻, Y)} (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (f g : 𝔻 → F) :
    A.chargeSum σ (f + g) = A.chargeSum σ f + A.chargeSum σ g := by
  simp only [A.chargeSum_eq_sum s hs, Pi.add_apply, smul_add, Finset.sum_add_distrib]

/-- The charge-weighted sum commutes with scalar multiplication of the function, when `σ⁻¹(Z)` is
finite. -/
theorem chargeSum_smul {R : Type*} [Semiring R] [Module R F] {σ : C(𝔻, Y)} (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (c : R) (g : 𝔻 → F) :
    A.chargeSum σ (c • g) = c • A.chargeSum σ g := by
  simp only [A.chargeSum_eq_sum s hs, Pi.smul_apply, smul_comm _ c, Finset.smul_sum]

end ChargeSum

/-! ### The charge multiset -/

section ChargeMultiset

/-- The **charge multiset** of a disc `σ`: the multiset of the points `z` of `σ⁻¹(Z)`, each with
multiplicity its local charge `I_z(σ)`, negative charges counting as zero. It is meaningful when
`σ⁻¹(Z)` is finite (`TauCeti.PositiveCohomologyAssignment.count_chargeMultiset`) and the local
charges are nonnegative, as for a `J`-holomorphic disc
(`TauCeti.PositiveCohomologyAssignment.localCharge_nonneg_of_finite`); its cardinality is then the
integer of `σ` (`TauCeti.PositiveCohomologyAssignment.card_chargeMultiset`). -/
def chargeMultiset (σ : C(𝔻, Y)) : Multiset 𝔻 :=
  ∑ᶠ z, (A.localCharge σ z).toNat • {z}

/-- The charge multiset unfolds to the `finsum` of the points with their local charges as
multiplicities, whether or not `σ⁻¹(Z)` is finite. -/
theorem chargeMultiset_def (σ : C(𝔻, Y)) :
    A.chargeMultiset σ = ∑ᶠ z, (A.localCharge σ z).toNat • {z} :=
  (rfl)

/-- If `σ⁻¹(Z)` is the finite set `s`, the charge multiset is the sum over `s` of the points with
their local charges as multiplicities. -/
theorem chargeMultiset_eq_sum {σ : C(𝔻, Y)} (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) :
    A.chargeMultiset σ = ∑ z ∈ s, (A.localCharge σ z).toNat • {z} :=
  finsum_eq_sum_of_support_subset _ fun z hz ↦ by_contra fun hzs ↦
    hz (by simp [A.localCharge_eq_zero_of_notMem s hs hzs])

/-- When `σ⁻¹(Z)` is finite, a point occurs in the charge multiset with multiplicity its local
charge, negative charges counting as zero. -/
theorem count_chargeMultiset [DecidableEq 𝔻] {σ : C(𝔻, Y)} (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (z : 𝔻) :
    (A.chargeMultiset σ).count z = (A.localCharge σ z).toNat := by
  rw [A.chargeMultiset_eq_sum s hs, Multiset.count_sum']
  simp_rw [Multiset.count_nsmul, Multiset.count_singleton, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hzs
  · rfl
  · rw [A.localCharge_eq_zero_of_notMem s hs hzs, Int.toNat_zero]

/-- When `σ⁻¹(Z)` is finite, the charge multiset contains exactly the points of positive local
charge. -/
theorem mem_chargeMultiset {σ : C(𝔻, Y)} (s : Finset 𝔻) (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (z : 𝔻) :
    z ∈ A.chargeMultiset σ ↔ 0 < A.localCharge σ z := by
  classical
  rw [← Multiset.count_pos, A.count_chargeMultiset s hs, Int.lt_toNat, Nat.cast_zero]

/-- When `σ⁻¹(Z)` is finite and the local charges are nonnegative, summing a function over the
charge multiset gives the charge-weighted sum. -/
theorem sum_map_chargeMultiset {F : Type*} [AddCommGroup F] {σ : C(𝔻, Y)} (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (hpos : ∀ z, σ z ∈ Z → 0 ≤ A.localCharge σ z) (g : 𝔻 → F) :
    ((A.chargeMultiset σ).map g).sum = A.chargeSum σ g := by
  classical
  rw [Finset.sum_multiset_map_count, A.chargeSum_eq_sum s hs]
  -- Both sides are sums of `I_z(σ) g(z)`: over the points of positive charge on the left, over
  -- `s` on the right, and the other points of `s` have charge zero.
  refine Finset.sum_subset (fun z hz ↦ ?_) (fun z _ hz ↦ ?_) |>.trans
    (Finset.sum_congr rfl fun z hz ↦ ?_)
  · rw [Multiset.mem_toFinset, A.mem_chargeMultiset s hs] at hz
    by_contra hzs
    exact hz.ne' (A.localCharge_eq_zero_of_notMem s hs hzs)
  · rw [Multiset.mem_toFinset, A.mem_chargeMultiset s hs, not_lt] at hz
    rw [A.count_chargeMultiset s hs, Int.toNat_eq_zero.2 hz, zero_smul]
  · rw [A.count_chargeMultiset s hs, ← natCast_zsmul, Int.toNat_of_nonneg (hpos z ((hs z).2 hz))]

/-- When `σ⁻¹(Z)` is finite and the local charges are nonnegative, the cardinality of the charge
multiset is the integer of `σ`. -/
theorem card_chargeMultiset {σ : C(𝔻, Y)} (h : IsCompact (σ ⁻¹' Z)) (s : Finset 𝔻)
    (hs : ∀ z, σ z ∈ Z ↔ z ∈ s) (hpos : ∀ z, σ z ∈ Z → 0 ≤ A.localCharge σ z) :
    (Multiset.card (A.chargeMultiset σ) : ℤ) = A.charge σ h := by
  have hsum := A.sum_map_chargeMultiset s hs hpos fun _ ↦ (1 : ℤ)
  rw [A.chargeSum_const h s hs, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one, nsmul_eq_mul, mul_one] at hsum
  exact hsum

end ChargeMultiset

/-! ### Continuity along a family of discs -/

section Family

variable {P : Type*} [TopologicalSpace P] (u : C(P × 𝔻, Y))

/-- A double sum of nonnegative integer multiples of differences `g z - g z₀` of norm at most `δ`
has norm at most `δ` times the sum of the multiplicities. -/
private theorem norm_sum_sum_zsmul_sub_le {F : Type*} [SeminormedAddCommGroup F]
    (s₀ : Finset 𝔻) (t : 𝔻 → Finset 𝔻) (c : 𝔻 → ℤ) (g : 𝔻 → F) {δ : ℝ}
    (hc : ∀ z₀ ∈ s₀, ∀ z ∈ t z₀, 0 ≤ c z) (hg : ∀ z₀ ∈ s₀, ∀ z ∈ t z₀, ‖g z - g z₀‖ ≤ δ) :
    ‖∑ z₀ ∈ s₀, ∑ z ∈ t z₀, c z • (g z - g z₀)‖ ≤ δ * ∑ z₀ ∈ s₀, ∑ z ∈ t z₀, (c z : ℝ) := by
  simp_rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z₀ hz₀ ↦
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz ↦ ?_))
  have hcz : (0 : ℝ) ≤ c z := Int.cast_nonneg (hc z₀ hz₀ z hz)
  refine (norm_zsmul_le _ _).trans ?_
  rw [Int.norm_eq_abs, abs_of_nonneg hcz, mul_comm δ]
  exact mul_le_mul_of_nonneg_left (hg z₀ hz₀ z hz) hcz

open Classical in
/-- The data of the convergence proof at `w₀`: if `σ_{w₀}⁻¹(Z)` is the finite set `s₀`, then for
every family of radii `r z` isolating the points `z ∈ s₀` in disjoint round discs `B(z, r z)`,
eventually the leaves meet `Z` only inside these discs, and on each of them their local charges add
up to the local charge of `σ_{w₀}` at the centre. -/
private theorem eventually_forall_mem_ball_and_sum_localCharge_eq [LocallyPathConnectedSpace P]
    (hZ : IsClosed Z) {K : Set 𝔻} (hK : IsCompact K) {w₀ : P}
    (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K) (s₀ : Finset 𝔻)
    (hs₀ : ∀ z, u (w₀, z) ∈ Z ↔ z ∈ s₀) (r : 𝔻 → ℝ) (hr : ∀ z, 0 < r z)
    (hc : ∀ z : 𝔻, ‖(z : ℂ)‖ + r z ≤ 1)
    (hiso : ∀ z : 𝔻, z ∈ s₀ → ∀ w : 𝔻, w ∈ s₀ → (w : ℂ) ∈ ball (z : ℂ) (2 * r z) → w = z) :
    ∀ᶠ w in 𝓝 w₀, (∀ z, u (w, z) ∈ Z → ∃ z₀ ∈ s₀, (z : ℂ) ∈ ball (z₀ : ℂ) (r z₀)) ∧
      ∀ z₀ ∈ s₀, ∀ s : Finset 𝔻, (∀ z, u (w, z) ∈ Z ↔ z ∈ s) →
        ∑ z ∈ s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) (r z₀), A.localCharge (u.curry w) z =
          A.localCharge (u.curry w₀) z₀ := by
  refine Eventually.and ?_ ((Finset.eventually_all s₀).2 fun z₀ hz₀ ↦ ?_)
  · -- The leaf over `w₀` meets `Z` inside the open union of the discs, hence so do nearby leaves.
    set U : Set 𝔻 := ⋃ z₀ ∈ s₀, (↑) ⁻¹' ball (z₀ : ℂ) (r z₀)
    have hU : IsOpen U := isOpen_biUnion fun z₀ _ ↦ isOpen_ball.preimage continuous_coe
    have hσU : Prod.mk w₀ ⁻¹' (u ⁻¹' Z) ⊆ U := fun z hz ↦
      mem_biUnion ((hs₀ z).1 hz) (mem_ball_self (hr z))
    filter_upwards [(hZ.preimage u.continuous).eventually_preimage_prodMk_subset hK hKZ hU hσU]
      with w hw z hz
    simpa [U] using hw hz
  · exact A.eventually_sum_localCharge_eq u hZ hK hKZ (hc z₀) (hr z₀)
      (by linarith [hr z₀] : r z₀ < 2 * r z₀) fun w hw hwb ↦ hiso z₀ hz₀ w ((hs₀ w).1 hw) hwb

/-- **Continuity of the charge-weighted sums along a family of discs.** Let `u` be a continuous
family of discs over a locally path connected parameter space, and suppose that for `w` near `w₀`
the leaf `σ_w = u (w, ·)` meets the closed set `Z` only inside a fixed compact set `K ⊆ 𝔻`, and
that `σ_{w₀}` meets `Z` in a finite set. Let `l ≤ 𝓝 w₀` be a filter along which the leaves
eventually meet `Z` in finite sets with nonnegative local charges. Then for every function `g`
continuous at the points of `σ_{w₀}⁻¹(Z)`, the charge-weighted sums `∑_z I_z(σ_w) g(z)` tend to
`∑_z I_z(σ_{w₀}) g(z)` along `l`. -/
theorem tendsto_chargeSum [LocallyPathConnectedSpace P] (hZ : IsClosed Z) {K : Set 𝔻}
    (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K)
    (h₀ : (u.curry w₀ ⁻¹' Z).Finite) {l : Filter P} (hl : l ≤ 𝓝 w₀)
    (hfin : ∀ᶠ w in l, (u.curry w ⁻¹' Z).Finite)
    (hpos : ∀ᶠ w in l, ∀ z, u (w, z) ∈ Z → 0 ≤ A.localCharge (u.curry w) z)
    {F : Type*} [SeminormedAddCommGroup F] {g : 𝔻 → F}
    (hg : ∀ z, u (w₀, z) ∈ Z → ContinuousAt g z) :
    Tendsto (fun w ↦ A.chargeSum (u.curry w) g) l (𝓝 (A.chargeSum (u.curry w₀) g)) := by
  classical
  set s₀ := h₀.toFinset
  have hs₀ : ∀ z, u (w₀, z) ∈ Z ↔ z ∈ s₀ := fun z ↦ by simp [s₀]
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  -- Choose the tolerance `δ` for `g` so that `δ` times the total charge is below `ε`.
  set m : ℝ := ∑ z ∈ s₀, |(A.localCharge (u.curry w₀) z : ℝ)|
  have hm : 0 ≤ m := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set δ := ε / (m + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  -- Isolate the points of `s₀` in disjoint round discs `B(z, r z)` on which `g` varies by less
  -- than `δ`.
  obtain ⟨r, hr, hc, hiso, hgr, huniq⟩ :=
    exists_isolating_radius s₀ (fun z hz ↦ hg z ((hs₀ z).2 hz)) hδ
  filter_upwards [hl (A.eventually_forall_mem_ball_and_sum_localCharge_eq u hZ hK hKZ s₀ hs₀ r hr
    hc fun z _ ↦ hiso z), hfin, hpos] with w ⟨hcov, hsum⟩ hw hwpos
  set s := hw.toFinset
  have hs : ∀ z, u (w, z) ∈ Z ↔ z ∈ s := fun z ↦ by simp [s]
  -- Both sums split along the discs `B(z₀, r z₀)`, and on each disc the local charges of the
  -- leaf over `w` add up to the local charge at `z₀`.
  have hsplit : ∑ z ∈ s, A.localCharge (u.curry w) z • g z = ∑ z₀ ∈ s₀,
      ∑ z ∈ s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) (r z₀),
        A.localCharge (u.curry w) z • g z := by
    rw [← Finset.sum_biUnion fun z₀ hz₀ z₁ hz₁ hne ↦ Finset.disjoint_filter.2
      fun z _ hz₀' hz₁' ↦ hne (huniq z z₀ hz₀ z₁ hz₁ hz₀' hz₁')]
    refine Finset.sum_congr (Finset.ext fun z ↦ ?_) fun _ _ ↦ rfl
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    exact ⟨fun hz ↦ (hcov z ((hs z).2 hz)).imp fun _ h ↦ ⟨h.1, hz, h.2⟩, fun ⟨_, _, hz, _⟩ ↦ hz⟩
  have hsum' : A.chargeSum (u.curry w₀) g = ∑ z₀ ∈ s₀,
      ∑ z ∈ s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) (r z₀),
        A.localCharge (u.curry w) z • g z₀ := by
    rw [A.chargeSum_eq_sum s₀ hs₀]
    refine Finset.sum_congr rfl fun z₀ hz₀ ↦ ?_
    rw [← Finset.sum_smul, hsum z₀ hz₀ s hs]
  rw [dist_eq_norm, A.chargeSum_eq_sum s hs, hsum', hsplit, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← smul_sub]
  -- Each term is at most `δ` times a nonnegative local charge, and these add up to `δ` times the
  -- total charge of `σ_{w₀}`.
  refine (norm_sum_sum_zsmul_sub_le (δ := δ) s₀ _ _ g (fun z₀ _ z hz ↦ hwpos z ((hs z).2
    (Finset.mem_filter.1 hz).1)) fun z₀ hz₀ z hz ↦ ?_).trans_lt ?_
  · exact (dist_eq_norm (g z) (g z₀)) ▸ (hgr z₀ hz₀ z (Finset.mem_filter.1 hz).2).le
  calc δ * ∑ z₀ ∈ s₀, ∑ z ∈ s.filter fun z : 𝔻 ↦ (z : ℂ) ∈ ball (z₀ : ℂ) (r z₀),
        (A.localCharge (u.curry w) z : ℝ)
      = δ * ∑ z₀ ∈ s₀, (A.localCharge (u.curry w₀) z₀ : ℝ) := by
        congr 1
        exact Finset.sum_congr rfl fun z₀ hz₀ ↦ by rw [← Int.cast_sum, hsum z₀ hz₀ s hs]
    _ ≤ δ * m := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun _ _ ↦ le_abs_self _) hδ.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

/-- Under the hypotheses of `TauCeti.PositiveCohomologyAssignment.tendsto_chargeSum`, if the leaves
are eventually nonnegatively charged along a nontrivial filter `l ≤ 𝓝 w₀`, so is the leaf over
`w₀`: its local charges are sums of local charges of nearby leaves. -/
theorem localCharge_nonneg_of_eventually [LocallyPathConnectedSpace P] (hZ : IsClosed Z)
    {K : Set 𝔻} (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K)
    (h₀ : (u.curry w₀ ⁻¹' Z).Finite) {l : Filter P} [l.NeBot] (hl : l ≤ 𝓝 w₀)
    (hfin : ∀ᶠ w in l, (u.curry w ⁻¹' Z).Finite)
    (hpos : ∀ᶠ w in l, ∀ z, u (w, z) ∈ Z → 0 ≤ A.localCharge (u.curry w) z) (z₀ : 𝔻) :
    0 ≤ A.localCharge (u.curry w₀) z₀ := by
  classical
  by_cases hz₀ : u (w₀, z₀) ∈ Z
  · obtain ⟨R, hR, hiso⟩ := z₀.exists_pos_forall_mem_ball_eq h₀.toFinset
    obtain ⟨r, hr, hrR, hc⟩ := exists_pos_lt_and_norm_add_le_one z₀ hR
    obtain ⟨w, hsum, hw, hwpos⟩ := (((A.eventually_sum_localCharge_eq u hZ hK hKZ hc hr hrR
      fun z hz hzb ↦ hiso z (by simpa using hz) hzb).filter_mono hl).and (hfin.and hpos)).exists
    rw [← hsum hw.toFinset fun z ↦ by simp]
    exact Finset.sum_nonneg fun z hz ↦ hwpos z (by simpa using (Finset.mem_filter.1 hz).1)
  · have h : IsCompact (u.curry w₀ ⁻¹' Z) := h₀.isCompact
    exact (A.localCharge_eq_zero h hz₀).ge

/-- **Continuity of the charge multisets along a family of discs.** Under the hypotheses of
`TauCeti.PositiveCohomologyAssignment.tendsto_chargeSum`, the elementary symmetric functions of the
points of the charge multisets of the leaves, read in the coordinate of `ℂ`, tend to those of the
leaf over `w₀`. Up to sign, these are the coefficients of the monic polynomials
`∏_z (X - z)^{I_z(σ_w)}` whose roots are the points of positive local charge of the leaves. -/
theorem tendsto_esymm_chargeMultiset [LocallyPathConnectedSpace P] (hZ : IsClosed Z) {K : Set 𝔻}
    (hK : IsCompact K) {w₀ : P} (hKZ : ∀ᶠ w in 𝓝 w₀, ∀ z, u (w, z) ∈ Z → z ∈ K)
    (h₀ : (u.curry w₀ ⁻¹' Z).Finite) {l : Filter P} (hl : l ≤ 𝓝 w₀)
    (hfin : ∀ᶠ w in l, (u.curry w ⁻¹' Z).Finite)
    (hpos : ∀ᶠ w in l, ∀ z, u (w, z) ∈ Z → 0 ≤ A.localCharge (u.curry w) z) (k : ℕ) :
    Tendsto (fun w ↦ ((A.chargeMultiset (u.curry w)).map ((↑) : 𝔻 → ℂ)).esymm k) l
      (𝓝 (((A.chargeMultiset (u.curry w₀)).map ((↑) : 𝔻 → ℂ)).esymm k)) := by
  classical
  rcases l.eq_or_neBot with rfl | hne
  · exact tendsto_bot
  -- The power sums of the charge multisets are the charge-weighted sums of the powers.
  have hpow : ∀ w, (u.curry w ⁻¹' Z).Finite →
      (∀ z, u (w, z) ∈ Z → 0 ≤ A.localCharge (u.curry w) z) →
      ((A.chargeMultiset (u.curry w)).map ((↑) : 𝔻 → ℂ)).esymm k =
        newtonCoeff (fun j ↦ A.chargeSum (u.curry w) fun z : 𝔻 ↦ (z : ℂ) ^ j) k := by
    intro w hw hwpos
    rw [← newtonCoeff_sum_map_pow]
    congr 1
    funext j
    rw [Multiset.map_map, Function.comp_def,
      ← A.sum_map_chargeMultiset hw.toFinset (fun z ↦ by simp) hwpos]
  have hpos₀ := A.localCharge_nonneg_of_eventually u hZ hK hKZ h₀ hl hfin hpos
  have hM : Tendsto (fun w j ↦ A.chargeSum (u.curry w) fun z : 𝔻 ↦ (z : ℂ) ^ j) l
      (𝓝 fun j ↦ A.chargeSum (u.curry w₀) fun z : 𝔻 ↦ (z : ℂ) ^ j) :=
    tendsto_pi_nhds.2 fun j ↦ A.tendsto_chargeSum u hZ hK hKZ h₀ hl hfin hpos fun z _ ↦
      (continuous_coe.pow j).continuousAt
  rw [hpow w₀ h₀ fun z _ ↦ hpos₀ z]
  refine (((continuous_newtonCoeff k).tendsto _).comp hM).congr' ?_
  filter_upwards [hfin, hpos] with w hw hwpos
  exact (hpow w hw hwpos).symm

end Family

end TauCeti.PositiveCohomologyAssignment
