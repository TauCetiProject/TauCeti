/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.MulUnit
public import TauCeti.Analysis.Normed.Ring.Ultra
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

import Mathlib.Analysis.Real.Sqrt
import TauCeti.Analysis.Normed.Field.Basic

/-!
# The open-ball ideal, Neumann estimates, and noetherianity in ultrametric normed rings

Let `R` be an ultrametric seminormed ring with `‖1‖ = 1`, and let `R⁰ = Subring.unitClosedBall R`
be its closed unit ball. The elements of `R⁰` of norm less than one form an ideal
`R⁰⁰ = TauCeti.unitBallIdeal R` of `R⁰`. Its elements are topologically nilpotent in `R` (this is
Mathlib's `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`); conversely, for a power-multiplicative
norm every topologically nilpotent element has norm less than one. Without
power-multiplicativity the converse fails (in the dual numbers over `ℚ_[p]` with the maximum
norm, `ε` is nilpotent of norm one), which is why the ideal is described by the norm.

If `R` is moreover a normed ring in which geometric series converge (for instance a complete
one), the inverse of `1 - x` for `‖x‖ < 1` is controlled exactly by the ultrametric inequality:
`‖(1 - x)⁻¹‖ = 1` and `‖(1 - x)⁻¹ - 1‖ = ‖x‖`. Consequently elements of `R⁰` within distance
less than one of `1` are units of `R⁰`, the ideal `R⁰⁰` lies in the Jacobson radical of `R⁰`
when `R` is commutative, and units of the reduction `R⁰ ⧸ R⁰⁰` lift to units of `R⁰`. When the
norm of `R` is multiplicative, the units of `R⁰` are exactly the units of `R` of norm one. For an
ultrametric normed field `K` the ring `K⁰` is local with maximal ideal `K⁰⁰`, so its reduction
is the residue field. These are the facts about the unit ball that underlie reduction arguments
for Banach modules over nonarchimedean Banach rings.

Over an ultrametric normed field `K`, divisibility in `K⁰` is comparison of norms
(`Subring.unitClosedBall.dvd_iff_norm_le`). The closed unit ball `K⁰` is noetherian if and only if
`K⁰⁰` is finitely generated, if and only if there is a strict norm gap `ρ < 1` above `{‖a‖ < 1}`;
in that case `K⁰` is a principal ideal ring, and when `K` is nontrivially normed it is a discrete
valuation ring. Without a norm gap below `1`, `K⁰⁰` is not finitely generated, but for every
`0 < ε < 1` there is a single `d ∈ K⁰` with `√ε < ‖d‖ < 1` that divides every scalar `c ∈ K⁰`
of norm at most `ε`, with quotient norm at most `√ε`
(`TauCeti.exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le`), and every ideal of
`K⁰` is *almost principal* (`Ideal.exists_mem_forall_smul_mem_span_singleton_unitClosedBall`).

Conversely, a ring homomorphism into the closed unit ball of a seminormed ring with `‖1‖ = 1`
maps units to elements of norm one. If its source is a local ring and it maps the maximal ideal
into the open unit ball, it maps exactly the units to elements of norm one, and the maximal ideal
is the preimage of the open unit ball. This needs no ultrametric hypothesis; the model case is
the valuation ring of a nonarchimedean field.

## Main definitions

* `TauCeti.unitBallIdeal R`: the ideal of elements of norm less than one in the closed unit ball.

## Main results

* `TauCeti.exists_norm_lt_one_forall_norm_le_of_fg`: if the open-ball ideal is finitely
  generated, some element has the largest norm less than one.
* `Ideal.eq_bot_or_exists_mem_forall_mul_norm_le_unitClosedBall`: every nonzero ideal of
  `Subring.unitClosedBall R` has an element exceeding any `r < 1` times the supremum of its norms.
* `TauCeti.isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul`: for a power-multiplicative
  norm, topological nilpotence is equivalent to norm less than one.
* `TauCeti.norm_inverse_one_sub` and `TauCeti.norm_inverse_one_sub_sub_one`: the ultrametric
  Neumann estimates `‖(1 - x)⁻¹‖ = 1` and `‖(1 - x)⁻¹ - 1‖ = ‖x‖` for `‖x‖ < 1`.
* `TauCeti.isUnit_unitClosedBall_of_norm_sub_one_lt`: perturbations of one are units of the
  unit ball.
* `TauCeti.unitBallIdeal_le_jacobson_bot`: the open-ball ideal lies in the Jacobson radical of
  the unit ball, so the reduction map is a local homomorphism
  (`TauCeti.isLocalHom_quotientMk_unitBallIdeal`).
* `TauCeti.isUnit_unitClosedBall_iff`: for a multiplicative norm, the units of the unit ball are
  the units of norm one.
* `TauCeti.isUnit_unitClosedBall_iff_norm_eq_one`, `TauCeti.isLocalRing_unitClosedBall`,
  `Subring.unitClosedBall.dvd_iff_norm_le`, and `TauCeti.maximalIdeal_unitClosedBall`: over an
  ultrametric normed division ring the unit ball is a local ring in which divisibility is norm
  comparison, and over an ultrametric normed field its maximal ideal is the open-ball ideal.
* `TauCeti.isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow`,
  `TauCeti.isPrincipalIdealRing_unitClosedBall_of_forall_norm_le`,
  `TauCeti.fg_unitBallIdeal_iff_exists_forall_norm_le`,
  `TauCeti.isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal`,
  `TauCeti.isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le`, and
  `TauCeti.isDiscreteValuationRing_unitClosedBall_iff_isNoetherianRing`: characterizations of
  discrete norms, noetherianity, and the discrete valuation ring property for `K⁰`.
* `TauCeti.exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le`,
  `Ideal.exists_mem_forall_smul_mem_span_singleton_unitClosedBall`, and
  `Subring.unitClosedBall.smul_mem_span_singleton_of_norm_le`: scalar factorization in dense norm
  groups and almost-principality of ideals of `K⁰`.
* `TauCeti.norm_map_eq_one_of_isUnit`: a ring homomorphism into the closed unit ball maps units
  to elements of norm one.
* `TauCeti.norm_map_eq_one_iff_isUnit` and `TauCeti.norm_map_lt_one_iff_mem_maximalIdeal`: a
  ring homomorphism from a local ring into the closed unit ball, mapping the maximal ideal into the
  open unit ball, maps exactly the units to norm one and pulls the open unit ball back to the
  maximal ideal.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Springer, 1984, §1.2.
* C. Johansson and J. Newton, *Extended eigenvarieties for overconvergent cohomology*,
  arXiv:1604.07739, §2.1.
* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Inventiones Mathematicae 2 (1967), 191–214, §5, Satz 5.1.
-/

public section

open Filter Topology

namespace TauCeti

section UnitBallIdeal

variable (R : Type*) [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R]

/-- **The open-ball ideal.** In an ultrametric seminormed ring with `‖1‖ = 1`, the elements of
norm less than one form an ideal of the closed unit ball `Subring.unitClosedBall R`. -/
def unitBallIdeal : Ideal (Subring.unitClosedBall R) where
  carrier := {x | ‖(x : R)‖ < 1}
  add_mem' hx hy := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
  zero_mem' := by simp
  smul_mem' a x hx := (norm_mul_le (a : R) x).trans_lt
    ((mul_le_of_le_one_left (norm_nonneg _) (Subring.mem_unitClosedBall.mp a.property)).trans_lt hx)

variable {R} in
/-- An element of the closed unit ball lies in the open-ball ideal exactly when its norm is less
than one. -/
@[simp]
theorem mem_unitBallIdeal {x : Subring.unitClosedBall R} :
    x ∈ unitBallIdeal R ↔ ‖(x : R)‖ < 1 :=
  Iff.rfl

/-- The open-ball ideal is proper, since `‖1‖ = 1`. -/
theorem unitBallIdeal_ne_top : unitBallIdeal R ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one, mem_unitBallIdeal]
  simp

variable {R} in
/-- **A largest norm below one.** If the open-ball ideal is finitely generated, for instance when
the closed unit ball is noetherian, some `π` has the largest norm less than one: the generator of
largest norm bounds every combination of the generators, by the ultrametric inequality. -/
theorem exists_norm_lt_one_forall_norm_le_of_fg (h : (unitBallIdeal R).FG) :
    ∃ π : R, ‖π‖ < 1 ∧ ∀ a : R, ‖a‖ < 1 → ‖a‖ ≤ ‖π‖ := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Subring.unitClosedBall R),
      Submodule.span (Subring.unitClosedBall R) (S : Set _) = unitBallIdeal R := h
  obtain ⟨π, hπ, hπS⟩ : ∃ π ∈ unitBallIdeal R, ∀ b ∈ S, ‖(b : R)‖ ≤ ‖(π : R)‖ := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, zero_mem _, by simp⟩
    · obtain ⟨π, hπ, hmax⟩ := S.exists_max_image (fun b ↦ ‖(b : R)‖) hne
      exact ⟨π, hS ▸ Ideal.subset_span hπ, hmax⟩
  refine ⟨π, mem_unitBallIdeal.1 hπ, fun a ha ↦ ?_⟩
  have haS : (⟨a, Subring.mem_unitClosedBall.2 ha.le⟩ : Subring.unitClosedBall R) ∈
      Submodule.span (Subring.unitClosedBall R) (S : Set (Subring.unitClosedBall R)) :=
    hS ▸ mem_unitBallIdeal.2 ha
  refine Submodule.span_induction
    (p := fun (x : Subring.unitClosedBall R) _ ↦ ‖(x : R)‖ ≤ ‖(π : R)‖) hπS (by simp)
    (fun x y _ _ hx hy ↦ ?_) (fun b x _ hx ↦ ?_) haS
  · simpa using (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  · simpa using (norm_mul_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (Subring.mem_unitClosedBall.1 b.property)).trans hx)

end UnitBallIdeal

/-- **Supremum-norm approximation dichotomy for ideals of the closed unit ball.** For every ideal
`I` of `Subring.unitClosedBall R` and every `r < 1`, either `I = ⊥` or there is an element `g ∈ I`
with `0 < ‖(g : R)‖` such that `‖(g : R)‖` approximates `sup_{f ∈ I} ‖(f : R)‖` within factor
`r`, meaning `r * ‖(f : R)‖ ≤ ‖(g : R)‖` for all `f ∈ I`. -/
theorem _root_.Ideal.eq_bot_or_exists_mem_forall_mul_norm_le_unitClosedBall
    {R : Type*} [NormedRing R] [IsUltrametricDist R] [NormOneClass R]
    (I : Ideal (Subring.unitClosedBall R)) {r : ℝ} (hr1 : r < 1) :
    I = ⊥ ∨ ∃ g ∈ I, 0 < ‖(g : R)‖ ∧ ∀ f ∈ I, r * ‖(f : R)‖ ≤ ‖(g : R)‖ := by
  set S : Set ℝ := (fun f : Subring.unitClosedBall R ↦ ‖(f : R)‖) '' (I : Set _)
  have hSne : S.Nonempty := ⟨0, 0, I.zero_mem, by simp⟩
  have hSbdd : BddAbove S :=
    ⟨1, by rintro _ ⟨f, -, rfl⟩; exact Subring.mem_unitClosedBall.mp f.property⟩
  set α := sSup S
  have hα0 : 0 ≤ α := le_csSup_of_le hSbdd ⟨0, I.zero_mem, rfl⟩ (by simp)
  rcases hα0.eq_or_lt with hα | hα
  · refine Or.inl ((Submodule.eq_bot_iff I).mpr fun f hf ↦ ?_)
    have hf0 : ‖(f : R)‖ ≤ 0 := hα ▸ le_csSup hSbdd ⟨f, hf, rfl⟩
    exact Subtype.ext (norm_le_zero_iff.mp hf0)
  · have hlt : max r 0 * α < α := mul_lt_of_lt_one_left hα (max_lt hr1 zero_lt_one)
    obtain ⟨_, ⟨g, hgI, rfl⟩, hgt⟩ := (lt_csSup_iff hSbdd hSne).mp hlt
    refine Or.inr ⟨g, hgI, (mul_nonneg (le_max_right r 0) hα.le).trans_lt hgt, fun f hf ↦ ?_⟩
    have hfα : ‖(f : R)‖ ≤ α := le_csSup hSbdd ⟨f, hf, rfl⟩
    calc r * ‖(f : R)‖ ≤ max r 0 * ‖(f : R)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left r 0) (norm_nonneg _)
      _ ≤ max r 0 * α := mul_le_mul_of_nonneg_left hfα (le_max_right r 0)
      _ ≤ ‖(g : R)‖ := hgt.le

/-- **Topological nilpotence for power-multiplicative norms.** If `‖x ^ n‖ = ‖x‖ ^ n` for all
`n ≥ 1`, then `x` is topologically nilpotent exactly when `‖x‖ < 1`. The implication from right
to left holds for every seminormed ring (`tendsto_pow_atTop_nhds_zero_of_norm_lt_one`). -/
theorem isTopologicallyNilpotent_iff_norm_lt_one_of_isPowMul {R : Type*} [SeminormedRing R]
    (hR : IsPowMul (‖·‖ : R → ℝ)) {x : R} : IsTopologicallyNilpotent x ↔ ‖x‖ < 1 := by
  refine ⟨fun hx ↦ ?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  have hpow : Tendsto (fun n : ℕ ↦ ‖x‖ ^ n) atTop (𝓝 0) := by
    refine (tendsto_norm_zero.comp hx).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn using hR x hn
  rwa [← abs_of_nonneg (norm_nonneg x), ← tendsto_pow_atTop_nhds_zero_iff]

section Neumann

variable {R : Type*} [NormedRing R] [NormOneClass R] [HasSummableGeomSeries R]
  [IsUltrametricDist R] {x : R}

/-- For `‖x‖ < 1`, the element `1 - x` is a multiplicative unit of norm one. -/
private theorem isNormMulUnit_one_sub (hx : ‖x‖ < 1) : IsNormMulUnit (1 - x) := by
  simpa [← sub_eq_add_neg] using isNormMulUnit_one_add (a := -x) (by simpa using hx)

/-- **Ultrametric Neumann estimate.** In a normed ring with `‖1‖ = 1`, convergent geometric
series and an ultrametric norm, the inverse of `1 - x` has norm one whenever `‖x‖ < 1`. -/
@[simp]
theorem norm_inverse_one_sub (hx : ‖x‖ < 1) : ‖Ring.inverse (1 - x)‖ = 1 := by
  obtain ⟨u, hu⟩ := (isNormMulUnit_one_sub hx).isUnit
  have h1 : ‖(u : R)‖ = 1 := by
    rw [hu, IsUltrametricDist.norm_sub_eq_max_of_norm_sub_ne_norm_sub 1 0 x (by simpa using
      hx.ne'), sub_zero, zero_sub, norm_one, norm_neg, max_eq_left hx.le]
  have hinv := (Units.isNormMulUnit_iff_norm_inv u).mp (hu ▸ isNormMulUnit_one_sub hx)
  rw [← hu, Ring.inverse_unit, hinv, h1, inv_one]

omit [NormOneClass R] in
/-- **Ultrametric Neumann estimate.** In a normed ring with convergent geometric series and an
ultrametric norm, `‖(1 - x)⁻¹ - 1‖ = ‖x‖` whenever `‖x‖ < 1`. -/
@[simp]
theorem norm_inverse_one_sub_sub_one (hx : ‖x‖ < 1) : ‖Ring.inverse (1 - x) - 1‖ = ‖x‖ := by
  -- multiplication by `1 - x` preserves norms
  have key (w : R) : ‖(1 - x) * w‖ = ‖w‖ := by
    simpa [sub_eq_add_neg] using norm_one_add_mul_of_norm_lt_one (a := -x) (by simpa using hx) w
  obtain ⟨u, hu⟩ := IsUnit.one_sub_of_norm_lt_one hx
  rw [← hu, Ring.inverse_unit]
  -- `u⁻¹ - 1 = u⁻¹ - u⁻¹ * (1 - x) = u⁻¹ * x`
  have hsub : ((u⁻¹ : Rˣ) : R) - 1 = ((u⁻¹ : Rˣ) : R) * x := by
    rw [← Units.inv_mul u, hu, mul_sub, mul_one, sub_sub_cancel]
  rw [hsub, ← key (((u⁻¹ : Rˣ) : R) * x), ← mul_assoc, ← hu, Units.mul_inv, one_mul]

/-- **Units of the unit ball.** In a normed ring with `‖1‖ = 1`, convergent geometric series and
an ultrametric norm, an element of the closed unit ball within distance less than one of `1` is
a unit of the closed unit ball: its inverse again has norm one. -/
theorem isUnit_unitClosedBall_of_norm_sub_one_lt {x : Subring.unitClosedBall R}
    (hx : ‖(x : R) - 1‖ < 1) : IsUnit x := by
  have hx' : ‖1 - (x : R)‖ < 1 := by rwa [norm_sub_rev]
  have hinv := norm_inverse_one_sub hx'
  obtain ⟨u, hu⟩ := (isNormMulUnit_one_sub hx').isUnit
  rw [sub_sub_cancel] at hu hinv
  rw [← hu, Ring.inverse_unit] at hinv
  exact ⟨⟨x, ⟨_, Subring.mem_unitClosedBall.mpr hinv.le⟩, Subtype.ext (by simp [← hu]),
    Subtype.ext (by simp [← hu])⟩, rfl⟩

end Neumann

section Jacobson

variable (R : Type*) [NormedCommRing R] [NormOneClass R] [HasSummableGeomSeries R]
  [IsUltrametricDist R]

/-- **The open-ball ideal lies in the Jacobson radical of the unit ball.** In a commutative
normed ring with `‖1‖ = 1`, convergent geometric series and an ultrametric norm, every element
`x` of norm less than one makes `x * y + 1` a unit of the unit ball for each `y` in it. -/
theorem unitBallIdeal_le_jacobson_bot : unitBallIdeal R ≤ Ideal.jacobson ⊥ := by
  intro x hx
  rw [Ideal.jacobson_bot]
  refine Ring.mem_jacobson_iff.mpr fun y ↦ isUnit_unitClosedBall_of_norm_sub_one_lt ?_
  rw [mem_unitBallIdeal] at hx
  simpa using (norm_mul_le (x : R) y).trans_lt
    ((mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp y.property)).trans_lt
        hx)

/-- **Unit lifting.** The reduction map from the unit ball to its quotient by the open-ball ideal
is a local homomorphism: an element of the unit ball whose reduction is a unit is itself a unit
of the unit ball. -/
instance isLocalHom_quotientMk_unitBallIdeal :
    IsLocalHom (Ideal.Quotient.mk (unitBallIdeal R)) :=
  _root_.isLocalHom_of_le_jacobson (by
    simpa only [Ideal.jacobson_bot] using unitBallIdeal_le_jacobson_bot R)

end Jacobson

section NormMulClass

variable {R : Type*} [SeminormedRing R] [IsUltrametricDist R] [NormOneClass R] [NormMulClass R]

/-- **Units of the unit ball for a multiplicative norm.** An element of the closed unit ball is a
unit of the unit ball exactly when it is a unit of the ambient ring and has norm one. A unit of
norm less than one, such as a nonzero scalar of small norm, is therefore not a unit of the unit
ball. -/
theorem isUnit_unitClosedBall_iff {x : Subring.unitClosedBall R} :
    IsUnit x ↔ IsUnit (x : R) ∧ ‖(x : R)‖ = 1 := by
  have hx1 : ‖(x : R)‖ ≤ 1 := Subring.mem_unitClosedBall.mp x.property
  constructor
  · rintro ⟨v, rfl⟩
    have hb1 : ‖((v⁻¹ : (Subring.unitClosedBall R)ˣ) : R)‖ ≤ 1 :=
      Subring.mem_unitClosedBall.mp (v⁻¹ : (Subring.unitClosedBall R)ˣ).val.property
    have hmul : ‖(v : R)‖ * ‖((v⁻¹ : (Subring.unitClosedBall R)ˣ) : R)‖ = 1 := by
      rw [← norm_mul, ← Subring.coe_mul, v.mul_inv, Subring.coe_one, norm_one]
    exact ⟨v.isUnit.map (Subring.unitClosedBall R).subtype,
      by nlinarith [norm_nonneg (v : R), norm_nonneg ((v⁻¹ : (Subring.unitClosedBall R)ˣ) : R)]⟩
  · rintro ⟨⟨u, hu⟩, hx⟩
    have hinv : ‖((u⁻¹ : Rˣ) : R)‖ = 1 := by
      have h := congrArg norm u.mul_inv
      rwa [norm_mul, hu, hx, one_mul, norm_one] at h
    refine isUnit_iff_exists.mpr
      ⟨⟨_, Subring.mem_unitClosedBall.mpr hinv.le⟩, Subtype.ext ?_, Subtype.ext ?_⟩ <;>
    simp only [Subring.coe_mul, Subring.coe_one, ← hu, u.mul_inv, u.inv_mul]

end NormMulClass

section DivisionRing

variable {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]

/-- Over an ultrametric normed division ring, an element of the closed unit ball is a unit of the
unit ball exactly when its norm is one. -/
theorem isUnit_unitClosedBall_iff_norm_eq_one {x : Subring.unitClosedBall K} :
    IsUnit x ↔ ‖(x : K)‖ = 1 :=
  isUnit_unitClosedBall_iff.trans <| and_iff_right_of_imp fun hx ↦
    isUnit_iff_ne_zero.mpr <| norm_ne_zero_iff.mp (by simp [hx])

/-- **The unit ball of an ultrametric normed division ring is a local ring.** For `x` in the unit
ball, either `‖x‖ = 1` or `‖1 - x‖ = 1`, so `x` or `1 - x` is a unit. -/
instance isLocalRing_unitClosedBall : IsLocalRing (Subring.unitClosedBall K) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
  simp only [isUnit_unitClosedBall_iff_norm_eq_one]
  push_cast
  have hx1 : ‖(x : K)‖ ≤ 1 := Subring.mem_unitClosedBall.mp x.property
  rcases hx1.eq_or_lt with hx | hx
  · exact .inl hx
  · exact .inr (norm_one_sub_of_norm_lt_one hx)

/-- **Divisibility in `K⁰` is comparison of norms**: in an ultrametric normed division ring, `b`
divides `a` in `Subring.unitClosedBall K` exactly when `‖(a : K)‖ ≤ ‖(b : K)‖`. -/
theorem _root_.Subring.unitClosedBall.dvd_iff_norm_le {a b : Subring.unitClosedBall K} :
    b ∣ a ↔ ‖(a : K)‖ ≤ ‖(b : K)‖ := by
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [hc, Subring.coe_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp c.property)
  · rcases eq_or_ne (b : K) 0 with hb | hb
    · have ha : (a : K) = 0 := norm_le_zero_iff.mp (by simpa [hb] using h)
      exact ⟨0, Subtype.ext (by simp [ha])⟩
    · refine ⟨⟨(b : K)⁻¹ * (a : K), Subring.mem_unitClosedBall.mpr ?_⟩, Subtype.ext ?_⟩
      · rw [norm_mul, norm_inv]
        exact (inv_mul_le_one₀ (norm_pos_iff.mpr hb)).mpr h
      · simp [mul_inv_cancel_left₀ hb]

end DivisionRing

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- **The residue ring of an ultrametric normed field.** The maximal ideal of the unit ball is
the open-ball ideal, so the reduction `K⁰ ⧸ K⁰⁰` is the residue field of `K⁰`. -/
theorem maximalIdeal_unitClosedBall :
    IsLocalRing.maximalIdeal (Subring.unitClosedBall K) = unitBallIdeal K := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_unitClosedBall_iff_norm_eq_one,
    mem_unitBallIdeal, (Subring.mem_unitClosedBall.mp x.property).lt_iff_ne]

/-- Over an ultrametric normed field the open-ball ideal is maximal, so the reduction
`K⁰ ⧸ K⁰⁰` is a field (`Ideal.Quotient.field`). -/
instance isMaximal_unitBallIdeal : (unitBallIdeal K).IsMaximal :=
  maximalIdeal_unitClosedBall (K := K) ▸ IsLocalRing.maximalIdeal.isMaximal _

/-- **Discretely valued fields.** If every nonzero norm of `K` is an integer power of `‖π‖` for
some `0 < ‖π‖ < 1`, then the unit ball `K⁰` is a principal ideal ring, hence noetherian: a nonzero
ideal is generated by any of its elements of largest norm. -/
theorem isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow {π : K} (hπ0 : 0 < ‖π‖)
    (hπ1 : ‖π‖ < 1) (hdisc : ∀ x : K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) :
    IsPrincipalIdealRing (Subring.unitClosedBall K) := by
  -- Nonzero elements of `K⁰` have norm `‖π‖ ^ n` for a natural number `n`.
  have hnat (x : Subring.unitClosedBall K) (hx : x ≠ 0) : ∃ n : ℕ, ‖(x : K)‖ = ‖π‖ ^ n := by
    obtain ⟨k, hk⟩ := hdisc x fun h ↦ hx (Subtype.ext h)
    have hk0 : 0 ≤ k := (zpow_le_one_iff_right_of_lt_one₀ hπ0 hπ1).1
      (hk ▸ Subring.mem_unitClosedBall.1 x.property)
    exact ⟨k.toNat, by rw [hk, ← zpow_natCast, Int.toNat_of_nonneg hk0]⟩
  refine ⟨fun I ↦ ⟨?_⟩⟩
  classical
  by_cases hI : I = ⊥
  · exact ⟨0, by rw [hI, Submodule.span_zero_singleton]⟩
  have hex : ∃ n : ℕ, ∃ x ∈ I, x ≠ 0 ∧ ‖(x : K)‖ = ‖π‖ ^ n := by
    obtain ⟨x, hxI, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨n, hn⟩ := hnat x hx
    exact ⟨n, x, hxI, hx, hn⟩
  obtain ⟨x, hxI, -, hxn⟩ := Nat.find_spec hex
  refine ⟨x, le_antisymm (fun y hy ↦ ?_) ((Ideal.span_singleton_le_iff_mem _).2 hxI)⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨m, hm⟩ := hnat y hy0
  have hle : ‖(y : K)‖ ≤ ‖(x : K)‖ := by
    rw [hm, hxn]
    exact pow_le_pow_of_le_one hπ0.le hπ1.le (Nat.find_min' hex ⟨y, hy, hy0, hm⟩)
  exact Ideal.mem_span_singleton.mpr (Subring.unitClosedBall.dvd_iff_norm_le.mpr hle)

/-- **Principal ideal property from a norm gap.** If some `ρ < 1` bounds every norm strictly below
`1` in an ultrametric normed field `K`, then `Subring.unitClosedBall K` is a principal ideal ring:
either `K` is trivially normed and `K⁰` is a field, or `K` is discretely valued. -/
theorem isPrincipalIdealRing_unitClosedBall_of_forall_norm_le {ρ : ℝ} (hρ1 : ρ < 1)
    (hρ : ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) :
    IsPrincipalIdealRing (Subring.unitClosedBall K) := by
  by_cases hex : ∃ c : K, 0 < ‖c‖ ∧ ‖c‖ < 1
  · obtain ⟨c, hc0, hc1⟩ := hex
    obtain ⟨π, hπ0, hπ1, -, hdisc⟩ :=
      exists_norm_lt_one_forall_exists_norm_eq_zpow_of_forall_norm_le_of_norm_lt_one hρ1 hρ hc0 hc1
    exact isPrincipalIdealRing_unitClosedBall_of_norm_eq_zpow hπ0 hπ1 hdisc
  · push Not at hex
    -- Every nonzero element of `K⁰` has norm `1`, hence is a unit, so `K⁰` is a field.
    have hfield : IsField (Subring.unitClosedBall K) := by
      refine IsLocalRing.isField_iff_maximalIdeal_eq.mpr ?_
      rw [maximalIdeal_unitClosedBall, Submodule.eq_bot_iff]
      intro x hx
      rw [mem_unitBallIdeal] at hx
      ext
      by_contra hx0
      exact (hex x (norm_pos_iff.mpr hx0)).not_gt hx
    let := hfield.toField
    infer_instance

/-- **Finite generation of the open-ball ideal is equivalent to a norm gap below `1`.** -/
theorem fg_unitBallIdeal_iff_exists_forall_norm_le :
    (unitBallIdeal K).FG ↔ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ := by
  refine ⟨fun hfg ↦ ?_, fun ⟨ρ, hρ1, hρ⟩ ↦ ?_⟩
  · obtain ⟨π, hπ1, hπ⟩ := exists_norm_lt_one_forall_norm_le_of_fg hfg
    exact ⟨‖π‖, hπ1, hπ⟩
  · have := isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
    exact IsNoetherian.noetherian _

/-- **The closed unit ball of an ultrametric normed field is noetherian if and only if its
open-ball ideal is finitely generated.** -/
theorem isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal :
    IsNoetherianRing (Subring.unitClosedBall K) ↔ (unitBallIdeal K).FG := by
  refine ⟨fun _ ↦ IsNoetherian.noetherian _, fun hfg ↦ ?_⟩
  obtain ⟨ρ, hρ1, hρ⟩ := fg_unitBallIdeal_iff_exists_forall_norm_le.mp hfg
  have := isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
  infer_instance

/-- **The closed unit ball of an ultrametric normed field is noetherian if and only if some
`ρ < 1` bounds all norms strictly below `1`.** -/
theorem isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le :
    IsNoetherianRing (Subring.unitClosedBall K) ↔
      ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ :=
  isNoetherianRing_unitClosedBall_iff_fg_unitBallIdeal.trans
    fg_unitBallIdeal_iff_exists_forall_norm_le

/-- **Uniform scalar division in dense norm groups.** When `K⁰` has no strict norm gap below `1`,
for each `0 < ε < 1` there is a single `d ∈ K⁰` with `√ε < ‖d‖ < 1` that divides every scalar
`c ∈ K⁰` of norm at most `ε`, with quotient norm at most `√ε`. -/
theorem exists_forall_exists_eq_mul_and_norm_le_of_not_exists_forall_norm_le
    (hdense : ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ a : K, ‖a‖ < 1 → ‖a‖ ≤ ρ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ (δ : ℝ) (d : Subring.unitClosedBall K),
      0 < δ ∧ δ < 1 ∧ 0 < ‖(d : K)‖ ∧ ‖(d : K)‖ < 1 ∧ δ < ‖(d : K)‖ ∧
      ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε →
        ∃ c' : Subring.unitClosedBall K, c = c' * d ∧ ‖(c' : K)‖ ≤ δ := by
  set δ := Real.sqrt ε
  have hδ0 : 0 < δ := Real.sqrt_pos.mpr hε0
  have hδ1 : δ < 1 := (Real.sqrt_lt_sqrt hε0.le hε1).trans_eq Real.sqrt_one
  have hδ_sq : δ * δ = ε := Real.mul_self_sqrt hε0.le
  push Not at hdense
  obtain ⟨a, ha1, hδa⟩ := hdense δ hδ1
  let d : Subring.unitClosedBall K := ⟨a, Subring.mem_unitClosedBall.mpr ha1.le⟩
  have hd_pos : 0 < ‖(d : K)‖ := hδ0.trans hδa
  refine ⟨δ, d, hδ0, hδ1, hd_pos, ha1, hδa, fun c hc ↦ ?_⟩
  have hcd : ‖(c : K)‖ ≤ ‖(d : K)‖ :=
    hc.trans (hδ_sq ▸ (mul_le_of_le_one_left hδ0.le hδ1.le).trans hδa.le)
  obtain ⟨c', hc'⟩ := Subring.unitClosedBall.dvd_iff_norm_le.mpr hcd
  refine ⟨c', by rw [hc', mul_comm], ?_⟩
  have hc'_norm : ‖(d : K)‖ * ‖(c' : K)‖ ≤ ‖(d : K)‖ * δ := by
    rw [← norm_mul, ← Subring.coe_mul, ← hc']
    exact hc.trans (hδ_sq ▸ mul_comm δ ‖(d : K)‖ ▸ mul_le_mul_of_nonneg_left hδa.le hδ0.le)
  exact le_of_mul_le_mul_left hc'_norm hd_pos

/-- **Ideals of `K⁰` are almost principal.** For every ideal `I` of `Subring.unitClosedBall K` and
every `ε < 1`, there is an element `x ∈ I` such that `c • y ∈ Ideal.span {x}` for all
`c ∈ Subring.unitClosedBall K` with `‖(c : K)‖ ≤ ε` and all `y ∈ I`. -/
theorem _root_.Ideal.exists_mem_forall_smul_mem_span_singleton_unitClosedBall
    (I : Ideal (Subring.unitClosedBall K)) {ε : ℝ} (hε1 : ε < 1) :
    ∃ x ∈ I, ∀ c : Subring.unitClosedBall K, ‖(c : K)‖ ≤ ε →
      ∀ y ∈ I, c • y ∈ Ideal.span {x} := by
  rcases I.eq_bot_or_exists_mem_forall_mul_norm_le_unitClosedBall hε1 with rfl | ⟨x, hxI, -, hle⟩
  · exact ⟨0, zero_mem _, fun _ _ _ hy ↦ by simp [Ideal.mem_bot.mp hy]⟩
  · refine ⟨x, hxI, fun c hc y hy ↦ Ideal.mem_span_singleton.mpr <|
      Subring.unitClosedBall.dvd_iff_norm_le.mpr ?_⟩
    simpa only [smul_eq_mul, Subring.coe_mul, norm_mul] using
      (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (hle y hy)

/-- **Principal ideal containment from norm comparison in `K⁰`.** For `x, c, y ∈ K⁰`, if
`‖(c : K)‖ ≤ ‖(x : K)‖` then `c • y ∈ Ideal.span {x}`. -/
theorem _root_.Subring.unitClosedBall.smul_mem_span_singleton_of_norm_le
    {x c y : Subring.unitClosedBall K} (hc : ‖(c : K)‖ ≤ ‖(x : K)‖) :
    c • y ∈ Ideal.span {x} :=
  Ideal.mem_span_singleton.mpr <| Subring.unitClosedBall.dvd_iff_norm_le.mpr <| by
    simpa only [smul_eq_mul, Subring.coe_mul, norm_mul] using
      (mul_le_of_le_one_right (norm_nonneg _) (Subring.mem_unitClosedBall.mp y.property)).trans hc

end Field

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Over a nontrivially normed ultrametric field, `Subring.unitClosedBall K` is a discrete
valuation ring if and only if it is noetherian.** -/
theorem isDiscreteValuationRing_unitClosedBall_iff_isNoetherianRing :
    IsDiscreteValuationRing (Subring.unitClosedBall K) ↔
      IsNoetherianRing (Subring.unitClosedBall K) := by
  refine ⟨fun _ ↦ inferInstance, fun hnoeth ↦ ?_⟩
  obtain ⟨ρ, hρ1, hρ⟩ := isNoetherianRing_unitClosedBall_iff_exists_forall_norm_le.mp hnoeth
  have : IsPrincipalIdealRing (Subring.unitClosedBall K) :=
    isPrincipalIdealRing_unitClosedBall_of_forall_norm_le hρ1 hρ
  refine { not_a_field' := ?_ }
  rw [maximalIdeal_unitClosedBall]
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  intro hbot
  have hc : (⟨c, Subring.mem_unitClosedBall.mpr hc1.le⟩ : Subring.unitClosedBall K) ∈
      unitBallIdeal K := mem_unitBallIdeal.mpr hc1
  rw [hbot, Ideal.mem_bot] at hc
  exact hc0.ne' (by simpa using congrArg (fun x : Subring.unitClosedBall K ↦ ‖(x : K)‖) hc)

end NontriviallyNormedField

section Map

variable {O R : Type*} [Semiring O] [SeminormedRing R] [NormOneClass R] {φ : O →+* R}

/-- A ring homomorphism into the closed unit ball of a normed ring maps units to elements of norm
one. -/
theorem norm_map_eq_one_of_isUnit (hφ : ∀ x, ‖φ x‖ ≤ 1) {x : O} (hx : IsUnit x) : ‖φ x‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  refine le_antisymm (hφ _) ?_
  calc (1 : ℝ) = ‖φ ↑u * φ ↑u⁻¹‖ := by rw [← map_mul, Units.mul_inv, map_one, norm_one]
    _ ≤ ‖φ ↑u‖ * ‖φ ↑u⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖φ ↑u‖ * 1 := mul_le_mul_of_nonneg_left (hφ _) (norm_nonneg _)
    _ = ‖φ ↑u‖ := mul_one _

end Map

section LocalRing

open IsLocalRing

variable {O R : Type*} [CommRing O] [IsLocalRing O] [SeminormedRing R] [NormOneClass R]
  {φ : O →+* R}

/-- A ring homomorphism from a local ring into the closed unit ball of a normed ring, mapping the
maximal ideal into the open unit ball, maps exactly the units to elements of norm one. -/
theorem norm_map_eq_one_iff_isUnit (hφ : ∀ x, ‖φ x‖ ≤ 1) (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1)
    {x : O} : ‖φ x‖ = 1 ↔ IsUnit x :=
  ⟨fun h ↦ by_contra fun hx ↦ (hm x (by rwa [mem_maximalIdeal, mem_nonunits_iff])).ne h,
    norm_map_eq_one_of_isUnit hφ⟩

/-- A ring homomorphism from a local ring into the closed unit ball of a normed ring, mapping the
maximal ideal into the open unit ball, pulls the open unit ball back to the maximal ideal. -/
theorem norm_map_lt_one_iff_mem_maximalIdeal (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (hm : ∀ x ∈ maximalIdeal O, ‖φ x‖ < 1) {x : O} : ‖φ x‖ < 1 ↔ x ∈ maximalIdeal O := by
  refine ⟨fun h ↦ ?_, hm x⟩
  rw [mem_maximalIdeal, mem_nonunits_iff, ← norm_map_eq_one_iff_isUnit hφ hm]
  exact h.ne

end LocalRing

end TauCeti
