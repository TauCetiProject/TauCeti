/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Uniform
public import TauCeti.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField
import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# Bounded and power-bounded elements of normed rings

In a seminormed ring the balls about zero form a neighbourhood basis of zero, so norm-bounded
sets are bounded in the sense of `TauCeti.Huber.IsBounded`. For a normed division ring
this identifies the power-bounded elements with the closed unit ball and shows that the ring is
uniform; for instance `ℚ_[p]` is uniform, and its power-bounded elements are those of `ℤ_[p]`.

In a seminormed ring with a pseudouniformiser the converse holds as well: bounded sets are
norm-bounded. If the norm is moreover power-multiplicative, `‖x ^ n‖ = ‖x‖ ^ n`, the power-bounded
elements are again the closed unit ball and the ring is uniform. This applies to rings normed by
the maximum of finitely many multiplicative norms, such as the interval rings `B^I` of the
Fargues–Fontaine curve, which are not division rings.

In a seminormed ring every unit of norm less than one is a pseudouniformiser. If the norm is
moreover ultrametric with `‖1‖ = 1`, the closed unit ball is an open bounded subring, so such
a ring with a unit of norm less than one is a Tate ring. In particular a nontrivially normed
field with an ultrametric norm is a Tate ring. This is the Tate structure of the complete
rank-one nonarchimedean fields over which rigid geometry takes place: their closed polydiscs are
the adic spectra of the Tate algebras `K⟨X₁, …, Xₙ⟩`.

## Main definitions

* `TauCeti.Huber.powerBoundedSubringEquivInteger`: the canonical ring isomorphism `K° ≃+* 𝒪[K]`
  for an ultrametric normed field `K`.
* `TauCeti.Huber.integerToPowerBounded`: the homomorphism `𝒪[K] →+* A°` for a nonarchimedean
  topological `K`-algebra `A` with continuous scalar multiplication over a nontrivially normed
  ultrametric field `K`.

## Main results

* `TauCeti.Huber.isBounded_closedBall_zero`: closed balls about zero are bounded.
* `TauCeti.Huber.isPowerBounded_map_mul_of_norm_le`: along a bounded monoid homomorphism `φ`, if
  `‖u‖ * c ≤ 1` and `‖b‖ ≤ c`, then `φ u * b` is power-bounded.
* `TauCeti.Huber.isPowerBounded_iff_norm_le_one`: in a normed division ring an element is
  power-bounded exactly when its norm is at most one.
* `TauCeti.Huber.IsUniform.of_normedDivisionRing`: normed division rings are uniform.
* `TauCeti.Huber.isPowerBounded_algebraMap_of_norm_le_one`: in a topological algebra over a
  nontrivially normed field, scalars of norm at most one are power-bounded.
* `TauCeti.Huber.IsPseudoUniformizer.isBounded_iff_forall_norm_le`: in a seminormed ring with a
  pseudouniformiser a set is bounded exactly when it is norm-bounded.
* `TauCeti.Huber.IsPseudoUniformizer.isPowerBounded_iff_norm_le_one` and
  `TauCeti.Huber.IsPseudoUniformizer.coe_powerBoundedSubring_eq_closedBall`: for a
  power-multiplicative norm and a pseudouniformiser, the power-bounded elements are the closed
  unit ball.
* `TauCeti.Huber.IsUniform.of_isPowMul`: such a ring is uniform.
* `TauCeti.Huber.IsPseudoUniformizer.of_norm_lt_one`: in a seminormed ring a unit of norm less
  than one is a pseudouniformiser.
* `TauCeti.Huber.isPseudoUniformizer_iff_norm_lt_one`: in a normed division ring the
  pseudouniformisers are the nonzero elements of norm less than one.
* `TauCeti.Huber.coe_powerBoundedSubring_eq_closedBall`,
  `TauCeti.Huber.isClosed_powerBoundedSubring`,
  `TauCeti.Huber.completeSpace_powerBoundedSubring`, and
  `TauCeti.Huber.powerBoundedSubring_eq_integer`: in an ultrametric normed field `K°` is the
  closed unit ball (hence closed, and complete when `K` is complete), equal as a subring to
  `𝒪[K]`.
* `TauCeti.Huber.powerBoundedSubring.dvd_iff_norm_le` and
  `TauCeti.Huber.powerBoundedSubring.isUnit_iff_norm_eq_one`: in an ultrametric normed field
  divisibility in `K°` is comparison of norms and units of `K°` are the elements of norm one.
* `TauCeti.Huber.isLocalRing_powerBoundedSubring`,
  `TauCeti.Huber.maximalIdeal_powerBoundedSubring`,
  `TauCeti.Huber.isMaximal_topologicallyNilpotentIdeal`, and
  `TauCeti.Huber.isOpen_topologicallyNilpotentIdeal`: `K°` is a local ring with open maximal
  ideal `K°°`.
* `TauCeti.Huber.exists_isOpen_isBounded_subring`: an ultrametric seminormed ring has an open
  bounded subring, even when `‖1‖ ≠ 1`.
* `TauCeti.Huber.IsTateRing.of_isUnit_norm_lt_one`: an ultrametric seminormed commutative ring
  with a unit of norm less than one is a Tate ring.
* `TauCeti.Huber.IsTateRing.of_nontriviallyNormedField`: a nontrivially normed field with an
  ultrametric norm is a Tate ring; for instance `ℚ_[p]`.
* `TauCeti.Huber.IsTateRing.of_normedAlgebra`: an ultrametric seminormed algebra over a
  nontrivially normed field is Tate, without requiring its norm at one to equal one.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27.
-/

public section

open Filter Topology IsLocalRing
open scoped NormedField Valued

namespace TauCeti.Huber

/-- **Closed balls about zero are bounded** in a seminormed ring. -/
@[simp]
theorem isBounded_closedBall_zero {R : Type*} [SeminormedRing R] (r : ℝ) :
    IsBounded (Metric.closedBall (0 : R) r) := by
  rw [isBounded_iff]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hr : 0 < |r| + 1 := by positivity
  refine ⟨Metric.ball 0 (ε / (|r| + 1)), Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro _ ⟨v, hv, s, hs, rfl⟩
  rw [mem_ball_zero_iff] at hv
  rw [mem_closedBall_zero_iff] at hs
  refine hεU (mem_ball_zero_iff.mpr ?_)
  calc ‖v * s‖ ≤ ‖v‖ * ‖s‖ := norm_mul_le v s
    _ ≤ ‖v‖ * (|r| + 1) := by gcongr; linarith [le_abs_self r]
    _ < ε / (|r| + 1) * (|r| + 1) := by gcongr
    _ = ε := div_mul_cancel₀ ε hr.ne'

/-- An element of norm at most one in a seminormed ring is power-bounded. -/
theorem IsPowerBounded.of_norm_le_one {R : Type*} [SeminormedRing R] {x : R}
    (hx : ‖x‖ ≤ 1) : IsPowerBounded x := by
  refine isPowerBounded_iff.mpr ((isBounded_closedBall_zero (R := R) (max 1 ‖(1 : R)‖)).subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [mem_closedBall_zero_iff]
  cases n with
  | zero => simp
  | succ n =>
    exact (norm_pow_le' x (Nat.succ_pos n)).trans
      ((pow_le_one₀ (norm_nonneg x) hx).trans (le_max_left 1 ‖(1 : R)‖))

/-- If `φ` is bounded by `C`, `‖u‖ * c ≤ 1`, and `‖b‖ ≤ c`, then `φ u * b` is power-bounded: its
positive powers have norm at most `max C 0`. -/
theorem isPowerBounded_map_mul_of_norm_le {R S F : Type*} [SeminormedRing R]
    [SeminormedCommRing S] [FunLike F R S] [MonoidHomClass F R S] {φ : F} {C c : ℝ}
    {u : R} {b : S} (hφ : ∀ r, ‖φ r‖ ≤ C * ‖r‖) (hu : ‖u‖ * c ≤ 1) (hb : ‖b‖ ≤ c) :
    IsPowerBounded (φ u * b) := by
  refine isPowerBounded_iff.mpr
    ((isBounded_closedBall_zero (R := S) (max ‖(1 : S)‖ (max C 0))).subset ?_)
  rintro _ ⟨n, rfl⟩
  rw [mem_closedBall_zero_iff]
  rcases n with _ | m
  · simp only [pow_zero]
    exact le_max_left _ _
  · refine le_trans ?_ (le_max_right _ _)
    have hc0 : 0 ≤ c := (norm_nonneg b).trans hb
    have hφu : ‖φ (u ^ (m + 1))‖ ≤ max C 0 * ‖u‖ ^ (m + 1) :=
      (hφ _).trans <| (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _)).trans <|
        mul_le_mul_of_nonneg_left (norm_pow_le' u m.succ_pos) (le_max_right C 0)
    have hbm : ‖b ^ (m + 1)‖ ≤ c ^ (m + 1) :=
      (norm_pow_le' b m.succ_pos).trans (pow_le_pow_left₀ (norm_nonneg b) hb _)
    calc ‖(φ u * b) ^ (m + 1)‖ = ‖φ (u ^ (m + 1)) * b ^ (m + 1)‖ := by rw [mul_pow, map_pow]
      _ ≤ ‖φ (u ^ (m + 1))‖ * ‖b ^ (m + 1)‖ := norm_mul_le _ _
      _ ≤ (max C 0 * ‖u‖ ^ (m + 1)) * c ^ (m + 1) :=
          mul_le_mul hφu hbm (norm_nonneg _) (mul_nonneg (le_max_right C 0) (by positivity))
      _ = max C 0 * (‖u‖ * c) ^ (m + 1) := by rw [mul_assoc, ← mul_pow]
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left
          (pow_le_one₀ (mul_nonneg (norm_nonneg u) hc0) hu) (le_max_right C 0)
      _ = max C 0 := mul_one _

/-- **In a seminormed ring a unit of norm less than one is a pseudouniformiser**: its powers tend
to zero. -/
theorem IsPseudoUniformizer.of_norm_lt_one {R : Type*} [SeminormedRing R] {ϖ : R}
    (hϖ : IsUnit ϖ) (hϖ1 : ‖ϖ‖ < 1) : IsPseudoUniformizer ϖ :=
  isPseudoUniformizer_iff.mpr ⟨hϖ, tendsto_pow_atTop_nhds_zero_of_norm_lt_one hϖ1⟩

section PowMul

variable {R : Type*} [SeminormedRing R] {ϖ : R}

/-- **In a seminormed ring with a pseudouniformiser the bounded sets are the norm-bounded sets.**
The pseudouniformiser is needed: the norm `‖f‖ = 2 ^ deg f` on `ℤ[X]` induces the discrete
topology, in which every set is bounded, but the powers of `X` are not norm-bounded. -/
theorem IsPseudoUniformizer.isBounded_iff_forall_norm_le (hϖ : IsPseudoUniformizer ϖ)
    {S : Set R} : IsBounded S ↔ ∃ C, ∀ x ∈ S, ‖x‖ ≤ C := by
  refine ⟨fun hS ↦ ?_, fun ⟨C, hC⟩ ↦ (isBounded_closedBall_zero C).subset fun x hx ↦
    mem_closedBall_zero_iff.mpr (hC x hx)⟩
  obtain ⟨m, hm⟩ := hS.exists_pow_mul_subset hϖ.isTopologicallyNilpotent
    (Metric.ball_mem_nhds 0 one_pos)
  obtain ⟨u, hu⟩ := hϖ.isUnit.pow m
  refine ⟨‖(↑u⁻¹ : R)‖, fun x hx ↦ ?_⟩
  have hlt : ‖ϖ ^ m * x‖ < 1 := mem_ball_zero_iff.mp (hm (Set.mul_mem_mul rfl hx))
  calc ‖x‖ = ‖(↑u⁻¹ : R) * (ϖ ^ m * x)‖ := by rw [← hu, Units.inv_mul_cancel_left]
    _ ≤ ‖(↑u⁻¹ : R)‖ * ‖ϖ ^ m * x‖ := norm_mul_le _ _
    _ ≤ ‖(↑u⁻¹ : R)‖ := mul_le_of_le_one_right (norm_nonneg _) hlt.le

/-- **For a power-multiplicative norm the power-bounded elements are the closed unit ball**, in a
seminormed ring with a pseudouniformiser. -/
theorem IsPseudoUniformizer.isPowerBounded_iff_norm_le_one (hϖ : IsPseudoUniformizer ϖ)
    (hR : IsPowMul (‖·‖ : R → ℝ)) {x : R} : IsPowerBounded x ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hx ↦ ?_, IsPowerBounded.of_norm_le_one⟩
  obtain ⟨C, hC⟩ := hϖ.isBounded_iff_forall_norm_le.mp (isPowerBounded_iff.mp hx)
  by_contra! h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have hle : ‖x‖ ^ (n + 1) ≤ C := hR x n.succ_pos ▸ hC _ ⟨n + 1, rfl⟩
  exact (hn.trans_le (pow_le_pow_right₀ h.le n.le_succ)).not_ge hle

/-- **A seminormed ring with a pseudouniformiser and a power-multiplicative norm is uniform**: its
power-bounded elements form the closed unit ball, which is bounded. -/
theorem IsUniform.of_isPowMul (hϖ : IsPseudoUniformizer ϖ) (hR : IsPowMul (‖·‖ : R → ℝ)) :
    IsUniform R :=
  ⟨(isBounded_closedBall_zero (R := R) 1).subset fun _ hx ↦
    mem_closedBall_zero_iff.mpr ((hϖ.isPowerBounded_iff_norm_le_one hR).mp hx)⟩

/-- **For a power-multiplicative norm the power-bounded subring `R°` is the closed unit ball**, in
a nonarchimedean seminormed commutative ring with a pseudouniformiser. -/
theorem IsPseudoUniformizer.coe_powerBoundedSubring_eq_closedBall {R : Type*}
    [SeminormedCommRing R] [NonarchimedeanAddGroup R] {ϖ : R} (hϖ : IsPseudoUniformizer ϖ)
    (hR : IsPowMul (‖·‖ : R → ℝ)) :
    (powerBoundedSubring R : Set R) = Metric.closedBall 0 1 := by
  ext x
  rw [SetLike.mem_coe, mem_powerBoundedSubring, mem_closedBall_zero_iff,
    hϖ.isPowerBounded_iff_norm_le_one hR]

end PowMul

section NormedDivisionRing

variable {K : Type*} [NormedDivisionRing K]

/-- **In a normed division ring the power-bounded elements are the closed unit ball.** -/
@[simp]
theorem isPowerBounded_iff_norm_le_one {x : K} : IsPowerBounded x ↔ ‖x‖ ≤ 1 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · by_contra! hlt
    have hx0 : x ≠ 0 := norm_pos_iff.mp (one_pos.trans hlt)
    have hinv : ‖x⁻¹‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ hlt
    obtain ⟨m, hm⟩ := (isPowerBounded_iff.mp hx).exists_pow_mul_subset
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hinv : IsTopologicallyNilpotent x⁻¹)
      (Metric.ball_mem_nhds 0 one_pos)
    have hone : x⁻¹ ^ m * x ^ m = 1 := by
      rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero m hx0)]
    have hmem := hm (Set.mul_mem_mul (Set.mem_singleton _) ⟨m, rfl⟩)
    rw [hone, mem_ball_zero_iff, norm_one] at hmem
    exact lt_irrefl _ hmem
  · exact IsPowerBounded.of_norm_le_one hx

/-- **Normed division rings are uniform.** -/
instance (priority := 100) IsUniform.of_normedDivisionRing : IsUniform K :=
  ⟨(isBounded_closedBall_zero (R := K) 1).subset fun _ hx ↦
    mem_closedBall_zero_iff.mpr (isPowerBounded_iff_norm_le_one.mp hx)⟩

/-- **In a normed division ring the pseudouniformisers are the nonzero elements of norm less than
one.** -/
theorem isPseudoUniformizer_iff_norm_lt_one {ϖ : K} :
    IsPseudoUniformizer ϖ ↔ ϖ ≠ 0 ∧ ‖ϖ‖ < 1 := by
  rw [isPseudoUniformizer_iff, isUnit_iff_ne_zero]
  exact and_congr_right fun _ ↦ tendsto_pow_atTop_nhds_zero_iff_norm_lt_one

end NormedDivisionRing

section UltrametricDvd

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **Divisibility in `K°` is comparison of norms**: in an ultrametric normed field, `b` divides
`a` in the power-bounded subring exactly when `‖a‖ ≤ ‖b‖`. This is the counterpart for `K°` of
`Valued.integer.dvd_iff_norm_le`, stated for the valuation ring `𝒪[K]`, which is a different
subring with the same carrier. -/
theorem powerBoundedSubring.dvd_iff_norm_le {a b : powerBoundedSubring K} :
    b ∣ a ↔ ‖(a : K)‖ ≤ ‖(b : K)‖ := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hc, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp c.property))
  · rcases eq_or_ne (b : K) 0 with hb | hb
    · have ha : (a : K) = 0 := norm_le_zero_iff.mp (by simpa [hb] using h)
      exact ⟨0, Subtype.ext (by simp [ha])⟩
    · refine ⟨⟨a / b, mem_powerBoundedSubring.mpr (isPowerBounded_iff_norm_le_one.mpr ?_)⟩,
        Subtype.ext ?_⟩
      · rw [norm_div]
        exact div_le_one_of_le₀ h (norm_nonneg _)
      · simp [mul_div_cancel₀ _ hb]

/-- In an ultrametric normed field, an element of `K°` is a unit of `K°` exactly when its norm in
`K` is one. -/
theorem powerBoundedSubring.isUnit_iff_norm_eq_one {x : powerBoundedSubring K} :
    IsUnit x ↔ ‖(x : K)‖ = 1 := by
  rw [isUnit_iff_dvd_one, powerBoundedSubring.dvd_iff_norm_le, OneMemClass.coe_one, norm_one]
  exact (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.property)).ge_iff_eq

/-- The power-bounded subring `K°` of an ultrametric normed field coincides as a subring of `K`
with its valuation ring `𝒪[K]`. -/
theorem powerBoundedSubring_eq_integer : powerBoundedSubring K = 𝒪[K] := by
  ext x
  rw [mem_powerBoundedSubring, isPowerBounded_iff_norm_le_one, Valuation.mem_integer_iff,
    TauCeti.NormedField.v_eq_valuation, NormedField.valuation_apply, ← NNReal.coe_le_coe,
    coe_nnNorm, NNReal.coe_one]

/-- The canonical ring isomorphism `K° ≃+* 𝒪[K]` between the power-bounded subring and the
valuation ring of an ultrametric normed field. -/
noncomputable def powerBoundedSubringEquivInteger : powerBoundedSubring K ≃+* 𝒪[K] :=
  RingEquiv.subringCongr powerBoundedSubring_eq_integer

@[simp]
theorem coe_powerBoundedSubringEquivInteger (x : powerBoundedSubring K) :
    (powerBoundedSubringEquivInteger x : K) = x :=
  RingEquiv.coe_subringCongr_apply _ x

@[simp]
theorem coe_powerBoundedSubringEquivInteger_symm (c : 𝒪[K]) :
    (powerBoundedSubringEquivInteger.symm c : K) = c := by
  rw [powerBoundedSubringEquivInteger, RingEquiv.subringCongr_symm,
    RingEquiv.coe_subringCongr_apply]

/-- The power-bounded subring `K°` of an ultrametric normed field is a local ring. -/
instance isLocalRing_powerBoundedSubring : IsLocalRing (powerBoundedSubring K) :=
  powerBoundedSubringEquivInteger.symm.isLocalRing

/-- The maximal ideal of `K°` is the ideal `K°°` of topologically nilpotent elements. -/
theorem maximalIdeal_powerBoundedSubring :
    maximalIdeal (powerBoundedSubring K) = topologicallyNilpotentIdeal K := by
  ext x
  rw [mem_maximalIdeal, mem_nonunits_iff, powerBoundedSubring.isUnit_iff_norm_eq_one,
    mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
    tendsto_pow_atTop_nhds_zero_iff_norm_lt_one,
    (isPowerBounded_iff_norm_le_one.mp (mem_powerBoundedSubring.mp x.property)).lt_iff_ne]

/-- For an ultrametric normed field `K`, `K°°` is a maximal ideal of `K°`. -/
instance isMaximal_topologicallyNilpotentIdeal : (topologicallyNilpotentIdeal K).IsMaximal :=
  maximalIdeal_powerBoundedSubring (K := K) ▸ maximalIdeal.isMaximal (powerBoundedSubring K)

/-- For an ultrametric normed field `K`, `K°°` is an open ideal of `K°`. -/
theorem isOpen_topologicallyNilpotentIdeal :
    IsOpen (topologicallyNilpotentIdeal K : Set (powerBoundedSubring K)) := by
  have hopen : (topologicallyNilpotentIdeal K : Set (powerBoundedSubring K)) =
      (Subtype.val : powerBoundedSubring K → K) ⁻¹' Metric.ball 0 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_topologicallyNilpotentIdeal, IsTopologicallyNilpotent,
      tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, Set.mem_preimage, mem_ball_zero_iff]
  rw [hopen]
  exact Metric.isOpen_ball.preimage continuous_subtypeVal

end UltrametricDvd

open Pointwise in
/-- **Scalars of norm at most one are power-bounded** in a topological algebra over a nontrivially
normed field. A neighbourhood `U` of zero contains `t • v` for all small scalars `t` and all `v`
in some neighbourhood `V` of zero, so for a scalar `d` of small norm the neighbourhood `d • V` is
carried into `U` by every power of `c`. -/
theorem isPowerBounded_algebraMap_of_norm_le_one {K : Type*} [NontriviallyNormedField K]
    {A : Type*} [Semiring A] [TopologicalSpace A] [Algebra K A] [ContinuousSMul K A] {c : K}
    (hc : ‖c‖ ≤ 1) : IsPowerBounded (algebraMap K A c) := by
  refine isPowerBounded_iff.mpr (isBounded_iff.mpr fun U hU ↦ ?_)
  have hsmul : Tendsto (fun p : K × A ↦ p.1 • p.2) (𝓝 0 ×ˢ 𝓝 0) (𝓝 0) := by
    simpa [nhds_prod_eq] using (continuous_smul (M := K) (X := A)).tendsto ((0 : K), (0 : A))
  obtain ⟨W, hW, V, hV, hWV⟩ := mem_prod_iff.mp (hsmul hU)
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW
  obtain ⟨d, hd₀, hdε⟩ := NormedField.exists_norm_lt K hε
  refine ⟨d • V, (set_smul_mem_nhds_zero_iff (norm_pos_iff.mp hd₀)).mpr hV, ?_⟩
  rintro _ ⟨_, ⟨v, hv, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
  have hmul : d • v * algebraMap K A c ^ n = (c ^ n * d) • v := by
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
  dsimp only
  rw [hmul]
  refine hWV (Set.mk_mem_prod (hεW (mem_ball_zero_iff.mpr ?_)) hv)
  calc ‖c ^ n * d‖ = ‖c‖ ^ n * ‖d‖ := by rw [norm_mul, norm_pow]
    _ ≤ 1 * ‖d‖ := by gcongr; exact pow_le_one₀ (norm_nonneg c) hc
    _ < ε := by rwa [one_mul]

section IntegerToPowerBounded

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanAddGroup A]
  [Algebra K A] [ContinuousSMul K A]

variable (K A) in
/-- Over a nontrivially normed ultrametric field `K`, scalars in the valuation ring `𝒪[K]` map
into the power-bounded subring `A°` of any nonarchimedean topological `K`-algebra with continuous
scalar multiplication. -/
noncomputable def integerToPowerBounded : 𝒪[K] →+* powerBoundedSubring A :=
  (algebraMap K A).comp (Subring.subtype 𝒪[K]) |>.codRestrict (powerBoundedSubring A) fun c ↦
    mem_powerBoundedSubring.mpr <| isPowerBounded_algebraMap_of_norm_le_one <|
      isPowerBounded_iff_norm_le_one.mp <| mem_powerBoundedSubring.mp <|
        (powerBoundedSubring_eq_integer (K := K)).ge c.property

@[simp]
theorem coe_integerToPowerBounded (c : 𝒪[K]) :
    (integerToPowerBounded K A c : A) = algebraMap K A c := (rfl)

end IntegerToPowerBounded

section Ultrametric

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

/-- **The power-bounded subring of an ultrametric normed field is its closed unit ball**, the ring
of integers `𝒪_K`. -/
theorem coe_powerBoundedSubring_eq_closedBall :
    (powerBoundedSubring K : Set K) = Metric.closedBall 0 1 := by
  ext x
  simp

/-- The power-bounded subring `K°` of an ultrametric normed field is closed in `K`. -/
theorem isClosed_powerBoundedSubring :
    IsClosed (powerBoundedSubring K : Set K) :=
  (coe_powerBoundedSubring_eq_closedBall K).symm ▸ Metric.isClosed_closedBall

/-- The power-bounded subring `K°` of a complete ultrametric normed field is complete. -/
instance completeSpace_powerBoundedSubring [CompleteSpace K] :
    CompleteSpace (powerBoundedSubring K) :=
  (isClosed_powerBoundedSubring K).completeSpace_coe

end Ultrametric

/-- **An ultrametric seminormed ring has an open bounded subring**: the elements
acting contractively by multiplication. This is the closed unit ball when `‖1‖ = 1`, and it is
still a subring when the norm has `‖1‖ > 1`. -/
theorem exists_isOpen_isBounded_subring (R : Type*) [SeminormedRing R] [IsUltrametricDist R] :
    ∃ R₀ : Subring R, IsOpen (R₀ : Set R) ∧ IsBounded (R₀ : Set R) := by
  let R₀ : Subring R :=
    { carrier := {a | ∀ x : R, ‖a * x‖ ≤ ‖x‖}
      zero_mem' := by simp
      one_mem' := by simp
      add_mem' := fun ha hb x ↦ by
        rw [add_mul]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha x) (hb x))
      neg_mem' := fun ha x ↦ by simpa using ha x
      mul_mem' := fun ha hb x ↦ by
        rw [mul_assoc]
        exact (ha _).trans (hb x) }
  have hball : Metric.ball (0 : R) 1 ⊆ R₀ := by
    intro a ha x
    exact (norm_mul_le a x).trans
      (mul_le_of_le_one_left (norm_nonneg x) (mem_ball_zero_iff.mp ha).le)
  refine ⟨R₀, R₀.toAddSubgroup.isOpen_of_mem_nhds
    (Filter.mem_of_superset (Metric.ball_mem_nhds 0 zero_lt_one) hball),
    (isBounded_closedBall_zero ‖(1 : R)‖).subset fun a ha ↦ mem_closedBall_zero_iff.mpr ?_⟩
  simpa using ha 1

/-- **An ultrametric seminormed commutative ring with a unit of norm less than one is a Tate
ring.** The subring of elements acting contractively (`exists_isOpen_isBounded_subring`) is open
and bounded, and the unit is a pseudouniformiser (`IsPseudoUniformizer.of_norm_lt_one`). -/
theorem IsTateRing.of_isUnit_norm_lt_one {R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]
    {ϖ : R} (hϖ : IsUnit ϖ) (hϖ1 : ‖ϖ‖ < 1) : IsTateRing R :=
  let ⟨R₀, hopen, hb⟩ := exists_isOpen_isBounded_subring R
  IsTateRing.of_isOpen_isBounded R₀ hopen hb (IsPseudoUniformizer.of_norm_lt_one hϖ hϖ1)

/-- **A nontrivially normed field with an ultrametric norm is a Tate ring**, by
`IsTateRing.of_isUnit_norm_lt_one` applied to any `ϖ` with `0 < ‖ϖ‖ < 1`. Its ring of integers
`𝒪_K` is the closed unit ball. -/
instance IsTateRing.of_nontriviallyNormedField (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] : IsTateRing K := by
  obtain ⟨ϖ, h0, h1⟩ := NormedField.exists_norm_lt_one K
  exact IsTateRing.of_isUnit_norm_lt_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp h0)) h1

/-- An ultrametric seminormed algebra over a nontrivially normed field is a Tate ring.
No normalisation of the algebra norm at one is required. -/
theorem IsTateRing.of_normedAlgebra (K : Type*) [NontriviallyNormedField K]
    (A : Type*) [SeminormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] : IsTateRing A := by
  obtain ⟨A₀, hopen, hb⟩ := exists_isOpen_isBounded_subring A
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ := IsPseudoUniformizer.of_norm_lt_one
    (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)) hϖ1
  exact IsTateRing.of_isOpen_isBounded A₀ hopen hb (hϖ.map (continuous_algebraMap K A))

end TauCeti.Huber
