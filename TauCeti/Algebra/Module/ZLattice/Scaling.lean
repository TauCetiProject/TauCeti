/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.Algebra.Module.ZLattice.Determinant

/-!
# Scaling a lattice

For a `ℤ`-submodule `L` of a real vector space `E` and `c : ℝ`, the *scaled lattice* `c • L` is the
image of `L` under multiplication by `c`, Mathlib's pointwise action of `ℝ` on `Submodule ℤ E`.
This file records how the dual, the covolume, the determinant and the integrality, evenness and
unimodularity of a lattice in a real inner product space behave under scaling.

For `c ≠ 0` the lattice `c • L` is the pullback of `L` along the linear automorphism `c⁻¹ • ·`
(`ZLattice.smul_eq_comap`), so a full lattice scales to a full lattice, with dual
`(c • L)^∨ = c⁻¹ • L^∨`, covolume `|c|ⁿ covolume L` and determinant `c²ⁿ det L` in dimension `n`.
A negative scalar gives the same lattice as its absolute value (`Submodule.neg_smul_eq_smul`).

Scaling is not an invariance of any of the three predicates. The lattice `c • L` is integral
exactly when `c² ⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L` (`ZLattice.isIntegral_smul_iff`), and even exactly
when `c² ‖x‖² ∈ 2ℤ` for all `x ∈ L` (`ZLattice.isEven_smul_iff`). In particular, scaling by `√m`
for a natural number `m` preserves integrality: `√m • L` is integral when `L` is, and even when `L`
is even or when `L` is integral and `m` is even, with `det (√m • L) = mⁿ det L`. Thus `√2 • E₈` is
even and integral.

In positive dimension, scaling an integral lattice by `|c| > 1` never produces a unimodular
lattice, since its determinant is `c²ⁿ det L ≥ c²ⁿ > 1`; in particular `√m • L` is not unimodular
for `m > 1`, so `√2 • E₈` is not unimodular. A unimodular lattice scaled by `|c| ≠ 1` is never
unimodular. Positive dimension is needed: the zero lattice of the zero space is even, unimodular
and fixed by every scaling. Scaling *down* can create unimodularity, `(1/√2) • (√2 ℤ) = ℤ`, so the
first statement does not extend to `|c| < 1`.

## Main statements

* `ZLattice.smul_eq_comap`: for `c ≠ 0`, `c • L` is the pullback of `L` along `c⁻¹ • ·`, for real
  scalars and for any division ring of scalars commuting with them, such as `ℂ`.
* `ZLattice.basisSmul`: for `c ≠ 0`, a `ℤ`-basis `b` of `L` gives the `ℤ`-basis `c • b` of `c • L`.
* `ZLattice.exists_forall_ne_zero_lt_norm`: scaling up the integer span of a basis gives full
  lattices all of whose nonzero vectors are longer than a prescribed bound.
* `ZLattice.exists_forall_add_mem_eq_zero_of_isBounded`: a bounded set meets none of its
  translates by the nonzero vectors of such a lattice.
* `ZLattice.dual_smul`: `(c • L)^∨ = c⁻¹ • L^∨` for `c ≠ 0`.
* `ZLattice.covolume_smul`, `ZLattice.det_smul`: `covolume (c • L) = |c|ⁿ covolume L` and
  `det (c • L) = c²ⁿ det L` (for `c = 0` in positive dimension both sides vanish).
* `ZLattice.covolume_natCast_smul`: `covolume (c • L) = cⁿ covolume L` for a natural number `c`.
* `ZLattice.isIntegral_smul_iff`, `ZLattice.isEven_smul_iff`: the exact criteria for `c • L` to be
  integral or even.
* `ZLattice.IsIntegral.sqrt_smul`, `ZLattice.IsEven.sqrt_smul`,
  `ZLattice.IsIntegral.isEven_sqrt_smul`, `ZLattice.IsIntegral.natCast_smul`,
  `ZLattice.IsEven.natCast_smul`, `ZLattice.IsIntegral.isEven_natCast_smul_iff`: `√m • L` and
  `m • L` are integral when `L` is, and `m • L` (for integral `L`) is even if and only if `m` is
  even or `L` is even.
* `ZLattice.det_sqrt_smul`, `ZLattice.IsIntegral.card_discriminantGroup_sqrt_smul`:
  `det (√m • L) = mⁿ det L` (and `|A_{√m • L}| = mⁿ |A_L|` for integral `L` and `m ≠ 0`), and
  `ZLattice.det_sqrt_smul_span_orthonormalBasis`: `det (√m • ℤⁿ) = mⁿ`.
* `ZLattice.IsIntegral.not_isUnimodular_smul`, `ZLattice.IsIntegral.not_isUnimodular_sqrt_smul`,
  `ZLattice.IsUnimodular.not_isUnimodular_smul`: in positive dimension, scaling an integral lattice
  by `|c| > 1`, or a unimodular lattice by `|c| ≠ 1`, does not give a unimodular lattice.
* `ZLattice.dual_inv_natCast_smul`, `ZLattice.IsUnimodular.dual_inv_natCast_smul_lt`,
  `ZLattice.IsUnimodular.not_isIntegral_inv_natCast_smul`: for a unimodular lattice `L` in positive
  dimension and `m > 1`, the down-scaled lattice `m⁻¹ • L` has dual `m • L < m⁻¹ • L`, trivial
  discriminant group, determinant `m⁻²ⁿ < 1`, and is neither integral, even, nor unimodular (for
  `L = ℤ` and `m = 2`, this is the half-integer lattice `½ ℤ ⊆ ℝ` with dual `2 ℤ`).

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 1.
* J. H. Conway, N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed., Springer, 1999,
  Chapter 2, §2.

## Source note

The statements and proofs of this file adapt the Tau Ceti formalization in
[TauCeti PR #20860](https://github.com/TauCetiProject/TauCeti/pull/20860) by
@tauceti-ai-for-science.
-/

public section

open Module Submodule MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (L : Submodule ℤ E)

/-- Dividing a `ℤ`-submodule by a nonzero natural number `m` enlarges it: `L ≤ (m : ℝ)⁻¹ • L`. -/
theorem le_inv_natCast_smul {m : ℕ} (hm : m ≠ 0) : L ≤ (m : ℝ)⁻¹ • L := fun x hx ↦
  (mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨(m : ℝ) • x, by simpa [Nat.cast_smul_eq_nsmul] using L.nsmul_mem hx m,
      inv_smul_smul₀ (Nat.cast_ne_zero.mpr hm) x⟩

end Module

/-! ### Evenness -/

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

/-- The scaled lattice `c • L` is even exactly when `c² ‖x‖² ∈ 2ℤ` for every `x ∈ L`. -/
theorem isEven_smul_iff (c : ℝ) :
    IsEven (c • L) ↔ ∀ x ∈ L, ∃ m : ℤ, c ^ 2 * ‖x‖ ^ 2 = 2 * m := by
  simp only [isEven_iff, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

variable {L}

/-- Scaling an even lattice by the square root of a natural number gives an even lattice. -/
theorem IsEven.sqrt_smul (h : IsEven L) (m : ℕ) : IsEven (√(m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := isEven_iff.mp h x hx
  exact ⟨m * a, by rw [Real.sq_sqrt m.cast_nonneg, ha]; push_cast; ring⟩

/-- Scaling an even lattice by a natural number gives an even lattice. -/
theorem IsEven.natCast_smul (h : IsEven L) (m : ℕ) : IsEven ((m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := isEven_iff.mp h x hx
  exact ⟨m ^ 2 * a, by rw [ha]; push_cast; ring⟩

end Seminormed

/-! ### Scaling as a change of variables -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

section Scalar

variable {𝕜 : Type*} [DivisionRing 𝕜] [Module 𝕜 E] [ContinuousConstSMul 𝕜 E] [SMulCommClass 𝕜 ℝ E]

/-- For `c ≠ 0`, the scaled lattice `c • L` is the pullback of `L` along the real-linear
automorphism `x ↦ c⁻¹ • x`. The scalar `c` may lie in any division ring acting continuously on `E`
and commuting with the real scalars, such as `ℝ` itself or `ℂ` acting on a complex space. -/
theorem smul_eq_comap {c : 𝕜} (hc : c ≠ 0) :
    c • L = ZLattice.comap ℝ L
      (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E).toLinearMap := by
  ext x
  rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set_iff_inv_smul_mem₀ hc,
    ← SetLike.mem_coe, coe_comap]
  simp [Units.smul_def]

/-- Scaling a discrete lattice by a nonzero scalar gives a discrete lattice. -/
instance [DiscreteTopology L] (c : 𝕜) [NeZero c] : DiscreteTopology (c • L : Submodule ℤ E) := by
  rw [smul_eq_comap L (NeZero.ne c)]
  infer_instance

/-- Scaling a full lattice by a nonzero scalar gives a full lattice. -/
instance [DiscreteTopology L] [IsZLattice ℝ L] (c : 𝕜) [NeZero c] :
    IsZLattice ℝ (c • L : Submodule ℤ E) where
  span_top := by
    rw [smul_eq_comap L (NeZero.ne c)]
    exact IsZLattice.span_top

end Scalar

section Basis

variable {L} {ι : Type*}

/-- For `c ≠ 0`, a `ℤ`-basis `b` of `L` scales to the `ℤ`-basis `c • b` of `c • L`. -/
noncomputable def basisSmul (b : Basis ι ℤ L) {c : ℝ} (hc : c ≠ 0) :
    Basis ι ℤ (c • L : Submodule ℤ E) :=
  b.map ((L.equivMapOfInjective _ (smul_right_injective E hc)).trans
    (LinearEquiv.ofEq _ _ pointwise_smul_def.symm))

/-- The `i`-th vector of the scaled basis `basisSmul b hc` is `c • b i`. -/
@[simp]
theorem coe_basisSmul_apply (b : Basis ι ℤ L) {c : ℝ} (hc : c ≠ 0) (i : ι) :
    (basisSmul b hc i : E) = c • (b i : E) := by
  simp only [basisSmul, Basis.map_apply, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]
  -- `c • L` is by definition the image of `L` under `c • ·` (`Submodule.pointwise_smul_def`).
  exact coe_equivMapOfInjective_apply _ _ _ _

end Basis

/-! ### Lattices with long nonzero vectors -/

/-- A finite-dimensional real normed space has full lattices whose nonzero vectors are all longer
than any prescribed `R`. -/
theorem exists_forall_ne_zero_lt_norm [FiniteDimensional ℝ E] (R : ℝ) :
    ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∀ ℓ ∈ L, ℓ ≠ 0 → R < ‖ℓ‖ := by
  -- Scale up the integer span of a basis, whose nonzero vectors have norm at least some `δ`.
  set L₀ := span ℤ (Set.range (Module.finBasis ℝ E))
  obtain ⟨δ, hδ, hL₀⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set L₀))
  set c : ℝ := (|R| + 1) / δ
  have hc : 0 < c := by positivity
  have : NeZero c := ⟨hc.ne'⟩
  refine ⟨c • L₀, inferInstance, inferInstance, fun ℓ hℓ hne ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).1 hℓ
  have hδy : δ ≤ ‖y‖ := by
    by_contra! h
    have h0 := hL₀ ⟨y, hy⟩ (by simpa [dist_eq_norm] using h)
    exact hne (by rw [show y = 0 from congrArg Subtype.val h0, smul_zero])
  rw [norm_smul, Real.norm_of_nonneg hc.le]
  calc R < |R| + 1 := by linarith [le_abs_self R]
    _ = c * δ := (div_mul_cancel₀ _ hδ.ne').symm
    _ ≤ c * ‖y‖ := by gcongr

/-- A bounded subset `s` of a finite-dimensional real normed space meets none of its translates by
the nonzero vectors of some full lattice `L`. -/
theorem exists_forall_add_mem_eq_zero_of_isBounded [FiniteDimensional ℝ E] {s : Set E}
    (hs : Bornology.IsBounded s) :
    ∃ (L : Submodule ℤ E) (_ : DiscreteTopology L) (_ : IsZLattice ℝ L),
      ∀ x ∈ s, ∀ ℓ ∈ L, x + ℓ ∈ s → ℓ = 0 := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  obtain ⟨L, hd, hz, hL⟩ := exists_forall_ne_zero_lt_norm (E := E) (2 * R)
  refine ⟨L, hd, hz, fun x hx ℓ hℓ hxℓ ↦ by_contra fun hne ↦ ?_⟩
  have hx' := mem_closedBall_zero_iff.1 (hR hx)
  have hxℓ' := mem_closedBall_zero_iff.1 (hR hxℓ)
  have h := norm_sub_le (x + ℓ) x
  rw [add_sub_cancel_left] at h
  linarith [hL ℓ hℓ hne]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- Scaling a full lattice by `c` multiplies its covolume by `|c|ⁿ`, where `n` is the dimension of
the space, for any Haar measure. For `c = 0` in positive dimension both sides vanish: the zero
lattice has the whole space as a fundamental domain, of infinite measure. -/
@[simp]
theorem covolume_smul {c : ℝ} (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    covolume (c • L) μ = |c| ^ finrank ℝ E * covolume L μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, abs_zero]
    rcases (finrank ℝ E).eq_zero_or_pos with hE | hE
    · have : Subsingleton E := finrank_zero_iff.mp hE
      rw [hE, pow_zero, one_mul, Subsingleton.elim L 0]
    · have : Nontrivial E := Module.nontrivial_of_finrank_pos hE
      have h : IsAddFundamentalDomain (⊥ : Submodule ℤ E) (Set.univ : Set E) μ :=
        { nullMeasurableSet := .univ
          ae_covers := .of_forall fun x ↦ ⟨0, Set.mem_univ _⟩
          aedisjoint := fun g g' hgg' ↦ (hgg' (Subsingleton.elim g g')).elim }
      have : VAddInvariantMeasure (⊥ : Submodule ℤ E) E μ :=
        (inferInstance : VAddInvariantMeasure (⊥ : Submodule ℤ E).toAddSubgroup E μ)
      rw [zero_pow hE.ne', zero_mul, zero_eq_bot, covolume, h.covolume_eq_volume,
        measure_univ_of_isAddLeftInvariant, ENNReal.toReal_top]
  have hA : ((ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
      c⁻¹ • LinearMap.id := by
    ext x
    simp [Units.smul_def]
  rw [smul_eq_comap L hc, covolume_comap_continuousLinearEquiv L _ μ, hA, LinearMap.det_smul,
    LinearMap.det_id, mul_one, abs_pow, abs_inv, inv_pow, inv_inv]

/-- Scaling a full lattice by a natural number `c` multiplies its covolume by `cⁿ`, where `n` is
the dimension of the space, for any Haar measure. -/
theorem covolume_natCast_smul (c : ℕ) (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    covolume ((c : ℝ) • L) μ = (c : ℝ) ^ finrank ℝ E * covolume L μ := by
  rw [covolume_smul L μ, Nat.abs_cast]

/-- Dividing a full lattice by a natural number `c` divides its covolume by `cⁿ`, where `n` is the
dimension of the space, for any Haar measure (for `c = 0` in positive dimension both sides
vanish). -/
theorem covolume_inv_natCast_smul (c : ℕ) (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure] :
    covolume ((c : ℝ)⁻¹ • L) μ = ((c : ℝ) ^ finrank ℝ E)⁻¹ * covolume L μ := by
  rw [covolume_smul L μ, abs_inv, Nat.abs_cast, inv_pow]

end Normed

/-! ### Duality, integrality and the determinant -/

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (L : Submodule ℤ E)

/-- The dual of the scaled lattice `c • L` is `c⁻¹ • L^∨`, for `c ≠ 0`. -/
@[simp]
theorem dual_smul {c : ℝ} (hc : c ≠ 0) : dual (c • L) = c⁻¹ • dual L := by
  ext x
  refine Iff.trans ?_ (Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hc) (dual L : Set E) x).symm
  rw [inv_inv, SetLike.mem_coe]
  simp only [mem_dual, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, real_inner_smul_left, real_inner_smul_right]

/-- The scaled lattice `c • L` is integral exactly when `c² ⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L`. -/
theorem isIntegral_smul_iff (c : ℝ) :
    IsIntegral (c • L) ↔ ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, c ^ 2 * ⟪x, y⟫ = m := by
  simp only [isIntegral_iff, mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, sq]

variable {L}

/-- Scaling an integral lattice by the square root of a natural number gives an integral
lattice. -/
theorem IsIntegral.sqrt_smul (h : IsIntegral L) (m : ℕ) : IsIntegral (√(m : ℝ) • L) := by
  refine (isIntegral_smul_iff L _).mpr fun x hx y hy ↦ ?_
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx y hy
  exact ⟨m * a, by rw [Real.sq_sqrt m.cast_nonneg, ha]; push_cast; ring⟩

/-- Scaling an integral lattice by the square root of an even natural number gives an even
lattice. -/
theorem IsIntegral.isEven_sqrt_smul (h : IsIntegral L) {m : ℕ} (hm : Even m) :
    IsEven (√(m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx x hx
  rw [real_inner_self_eq_norm_sq] at ha
  exact ⟨k * a, by rw [Real.sq_sqrt (k + k).cast_nonneg, ha]; push_cast; ring⟩

/-- Scaling an integral lattice by a natural number gives an integral lattice. -/
theorem IsIntegral.natCast_smul (h : IsIntegral L) (m : ℕ) : IsIntegral ((m : ℝ) • L) := by
  refine (isIntegral_smul_iff L _).mpr fun x hx y hy ↦ ?_
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx y hy
  exact ⟨m ^ 2 * a, by rw [ha]; push_cast; ring⟩

/-- Scaling an integral lattice by an even natural number gives an even lattice. -/
theorem IsIntegral.isEven_natCast_smul (h : IsIntegral L) {m : ℕ} (hm : Even m) :
    IsEven ((m : ℝ) • L) := by
  refine (isEven_smul_iff L _).mpr fun x hx ↦ ?_
  obtain ⟨k, rfl⟩ := hm
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx x hx
  rw [real_inner_self_eq_norm_sq] at ha
  exact ⟨2 * k ^ 2 * a, by rw [ha]; push_cast; ring⟩

/-- For an integral lattice `L` and a natural number `m`, the scaled lattice `m • L` is even if
and only if `m` is even or `L` is even. -/
theorem IsIntegral.isEven_natCast_smul_iff (h : IsIntegral L) {m : ℕ} :
    IsEven ((m : ℝ) • L) ↔ Even m ∨ IsEven L := by
  refine ⟨fun hmL ↦ or_iff_not_imp_left.mpr fun hm ↦ isEven_iff.mpr fun x hx ↦ ?_,
    fun h' ↦ h'.elim h.isEven_natCast_smul fun hL ↦ hL.natCast_smul m⟩
  obtain ⟨q, rfl⟩ : Odd m := Nat.not_even_iff_odd.mp hm
  obtain ⟨a, ha⟩ := isIntegral_iff.mp h x hx x hx
  rw [real_inner_self_eq_norm_sq] at ha
  obtain ⟨b, hb⟩ := (isEven_smul_iff L (2 * q + 1 : ℕ)).mp hmL x hx
  refine ⟨b - (2 * (q : ℤ) ^ 2 + 2 * q) * a, ?_⟩
  push_cast at hb ⊢
  linear_combination hb - (4 * (q : ℝ) ^ 2 + 4 * q) * ha

/-- The dual of the down-scaled lattice `m⁻¹ • L` (`m ≠ 0`) is `m • L^∨`. -/
theorem dual_inv_natCast_smul (L : Submodule ℤ E) {m : ℕ} (hm : m ≠ 0) :
    dual ((m : ℝ)⁻¹ • L) = (m : ℝ) • dual L := by
  rw [dual_smul L (inv_ne_zero (Nat.cast_ne_zero.mpr hm)), inv_inv]

/-- When `dual L ≤ L` and `m ≠ 0`, the dual of `m⁻¹ • L` is contained in `m⁻¹ • L`:
`(m⁻¹ • L)^∨ = m • L^∨ ≤ m • L ≤ L ≤ m⁻¹ • L`. -/
theorem dual_inv_natCast_smul_le_of_dual_le (h : dual L ≤ L) {m : ℕ} (hm : m ≠ 0) :
    dual ((m : ℝ)⁻¹ • L) ≤ (m : ℝ)⁻¹ • L := by
  rw [dual_inv_natCast_smul L hm]
  exact (smul_mono_right (m : ℝ) h).trans ((natCast_smul_le L m).trans (le_inv_natCast_smul L hm))

/-- When `dual L ≤ L` and `m ≠ 0`, the down-scaled lattice `m⁻¹ • L` has trivial discriminant
group. -/
theorem subsingleton_discriminantGroup_inv_natCast_smul_of_dual_le (h : dual L ≤ L) {m : ℕ}
    (hm : m ≠ 0) : Subsingleton (DiscriminantGroup ((m : ℝ)⁻¹ • L)) :=
  subsingleton_discriminantGroup_iff.mpr (dual_inv_natCast_smul_le_of_dual_le h hm)

/-- When `dual L ≤ L` and `m ≠ 0`, the discriminant group of `m⁻¹ • L` has order `1`. -/
theorem card_discriminantGroup_inv_natCast_smul_of_dual_le (h : dual L ≤ L) {m : ℕ}
    (hm : m ≠ 0) : Nat.card (DiscriminantGroup ((m : ℝ)⁻¹ • L)) = 1 :=
  have := subsingleton_discriminantGroup_inv_natCast_smul_of_dual_le h hm
  Nat.card_unique

/-- For a unimodular lattice `L` and `m ≠ 0`, the dual of `m⁻¹ • L` is `m • L`. -/
theorem IsUnimodular.dual_inv_natCast_smul (h : IsUnimodular L) {m : ℕ} (hm : m ≠ 0) :
    dual ((m : ℝ)⁻¹ • L) = (m : ℝ) • L := by
  rw [ZLattice.dual_inv_natCast_smul L hm, h.dual_eq]

/-- For a unimodular lattice `L` and `m ≠ 0`, the dual of `m⁻¹ • L` is contained in `m⁻¹ • L`. -/
theorem IsUnimodular.dual_inv_natCast_smul_le (h : IsUnimodular L) {m : ℕ} (hm : m ≠ 0) :
    dual ((m : ℝ)⁻¹ • L) ≤ (m : ℝ)⁻¹ • L :=
  dual_inv_natCast_smul_le_of_dual_le h.dual_eq.le hm

/-- For a unimodular lattice `L` and `m ≠ 0`, the discriminant group of `m⁻¹ • L` is trivial. -/
theorem IsUnimodular.subsingleton_discriminantGroup_inv_natCast_smul (h : IsUnimodular L) {m : ℕ}
    (hm : m ≠ 0) : Subsingleton (DiscriminantGroup ((m : ℝ)⁻¹ • L)) :=
  subsingleton_discriminantGroup_inv_natCast_smul_of_dual_le h.dual_eq.le hm

/-- For a unimodular lattice `L` and `m ≠ 0`, the discriminant group of `m⁻¹ • L` has order `1`. -/
theorem IsUnimodular.card_discriminantGroup_inv_natCast_smul (h : IsUnimodular L) {m : ℕ}
    (hm : m ≠ 0) : Nat.card (DiscriminantGroup ((m : ℝ)⁻¹ • L)) = 1 :=
  card_discriminantGroup_inv_natCast_smul_of_dual_le h.dual_eq.le hm

variable (L) [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- Scaling a full lattice by `c` multiplies its determinant by `c²ⁿ`, where `n` is the dimension
of the space. -/
@[simp]
theorem det_smul {c : ℝ} : det (c • L) = c ^ (2 * finrank ℝ E) * det L := by
  rw [det_def, det_def, covolume_smul L volume, mul_pow, ← pow_mul, mul_comm (finrank ℝ E),
    pow_mul, pow_mul, sq_abs]

/-- Dividing a full lattice by a natural number `m` divides its determinant by `m²ⁿ`, where `n` is
the dimension of the space. -/
theorem det_inv_natCast_smul {m : ℕ} :
    det ((m : ℝ)⁻¹ • L) = ((m : ℝ) ^ (2 * finrank ℝ E))⁻¹ * det L := by
  rw [det_smul L, inv_pow]

/-- Scaling a full lattice by `√m`, for a natural number `m`, multiplies its determinant by `mⁿ`,
where `n` is the dimension of the space. -/
theorem det_sqrt_smul {m : ℕ} : det (√(m : ℝ) • L) = m ^ finrank ℝ E * det L := by
  rw [det_smul L, pow_mul, Real.sq_sqrt m.cast_nonneg]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- For an orthonormal basis `b` and a natural number `m`, the scaled cubic lattice `√m • ℤ b` has
determinant `mⁿ`, where `n` is the dimension of the space. For instance `√2 ℤ²` has determinant
`4`. -/
theorem det_sqrt_smul_span_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {m : ℕ} : det (√(m : ℝ) • span ℤ (Set.range b)) = m ^ finrank ℝ E := by
  have hu := isUnimodular_span_orthonormalBasis b
  -- The lattice instances of `span ℤ (Set.range b)` are those of the `ℤ`-span of a basis.
  rw [← b.coe_toBasis] at hu ⊢
  rw [det_sqrt_smul, hu.det_eq_one, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/-- For an orthonormal basis `b` and a natural number `m`, the discriminant group of the scaled
cubic lattice `√m • ℤ b` has `Nat.card` equal to `mⁿ`, where `n` is the dimension of the space,
which for `m ≠ 0` is `det (√m • ℤ b)`. For `m = 0` the lattice is `0` and its discriminant group is
the whole space: for `n > 0` it is infinite, so `Nat.card` returns the junk value `0 = 0 ^ n`, and
for `n = 0` it is trivial and `Nat.card` returns `1 = 0 ^ 0`. For instance the discriminant group
`(ℤ/2)²` of `√2 ℤ²` has order `4`. -/
theorem natCard_discriminantGroup_sqrt_smul_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {m : ℕ} :
    Nat.card (DiscriminantGroup (√(m : ℝ) • span ℤ (Set.range b))) = m ^ finrank ℝ E := by
  have := b.toBasis.finiteDimensional_of_finite
  rcases eq_or_ne m 0 with rfl | hm
  · -- The lattice is `0`, so its discriminant group is the whole space.
    rw [Nat.cast_zero, Real.sqrt_zero, zero_smul]
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · have hE : finrank ℝ E = 0 := by
        rw [Module.finrank_eq_card_basis b.toBasis, Fintype.card_eq_zero]
      have : Subsingleton E := finrank_zero_iff.mp hE
      have : Unique (DiscriminantGroup (⊥ : Submodule ℤ E)) :=
        ⟨⟨0⟩, fun x ↦ Subsingleton.elim _ _⟩
      rw [hE, Nat.card_unique, pow_zero]
    · have hE : 0 < finrank ℝ E := by
        rw [Module.finrank_eq_card_basis b.toBasis]
        exact Fintype.card_pos_iff.mpr ⟨i⟩
      have hx (t : ℝ) : t • b i ∈ dual (⊥ : Submodule ℤ E) := mem_dual.2 fun y hy ↦ by
        rw [Submodule.mem_bot] at hy
        exact ⟨0, by simp [hy]⟩
      have : Infinite (DiscriminantGroup (⊥ : Submodule ℤ E)) :=
        Infinite.of_injective (fun t : ℝ ↦ (Submodule.Quotient.mk ⟨t • b i, hx t⟩ :
          DiscriminantGroup (⊥ : Submodule ℤ E))) fun t u htu ↦ by
          rw [discriminantGroup_mk_eq_mk_iff, Submodule.mem_bot, ← sub_smul] at htu
          exact sub_eq_zero.mp ((smul_eq_zero.mp htu).resolve_right (b.orthonormal.ne_zero i))
      rw [Nat.card_eq_zero_of_infinite, zero_pow hE.ne']
  borelize E
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (by positivity)⟩
  have h :=
    ((isUnimodular_span_orthonormalBasis b).isIntegral.sqrt_smul m).det_eq_card_discriminantGroup
  rw [det_sqrt_smul_span_orthonormalBasis b] at h
  exact_mod_cast h.symm

variable {L}

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- Dividing a unimodular lattice `L` by a natural number `m` gives determinant `m⁻²ⁿ`, where `n`
is the dimension of the space. -/
theorem IsUnimodular.det_inv_natCast_smul (h : IsUnimodular L) (m : ℕ) :
    det ((m : ℝ)⁻¹ • L) = ((m : ℝ) ^ (2 * finrank ℝ E))⁻¹ := by
  have := h.isIntegral.discreteTopology
  have : IsZLattice ℝ L := ⟨h.span_eq_top⟩
  rw [ZLattice.det_inv_natCast_smul L, h.det_eq_one, mul_one]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Scaling an integral full lattice `L` of rank `n` by `√m` (`m ≠ 0`) multiplies the order of its
discriminant group by `mⁿ`. -/
theorem IsIntegral.card_discriminantGroup_sqrt_smul (h : IsIntegral L) {m : ℕ} (hm : m ≠ 0) :
    Nat.card (DiscriminantGroup (√(m : ℝ) • L)) =
      m ^ finrank ℝ E * Nat.card (DiscriminantGroup L) := by
  borelize E
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))⟩
  refine Nat.cast_injective (R := ℝ) ?_
  rw [← (h.sqrt_smul m).det_eq_card_discriminantGroup, det_sqrt_smul L,
    h.det_eq_card_discriminantGroup, Nat.cast_mul, Nat.cast_pow]

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, scaling an integral lattice by `c` with `1 < |c|` never gives a
unimodular lattice: if `c • L` is unimodular then `L` is full, and the determinant becomes
`c²ⁿ det L > 1`. -/
theorem IsIntegral.not_isUnimodular_smul [Nontrivial E] (h : IsIntegral L) {c : ℝ}
    (hc : 1 < |c|) : ¬ IsUnimodular (c • L) := by
  borelize E
  have := h.discreteTopology
  have hc0 : c ≠ 0 := abs_pos.mp (one_pos.trans hc)
  have : NeZero c := ⟨hc0⟩
  intro hu
  -- A unimodular lattice spans the space, and `c • L` spans no more than `L` does.
  have : IsZLattice ℝ L := ⟨top_unique <| by
    rw [← hu.span_eq_top, coe_pointwise_smul]
    exact Submodule.span_smul_le _ c⟩
  have hdet := hu.det_eq_one
  rw [det_smul L, pow_mul, ← sq_abs, ← pow_mul] at hdet
  have hlt : 1 < |c| ^ (2 * finrank ℝ E) :=
    one_lt_pow₀ hc (mul_ne_zero two_ne_zero finrank_pos.ne')
  nlinarith [h.one_le_det]

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, scaling an integral lattice by `√m` for a natural number `m > 1`
never gives a unimodular lattice. For instance `√2 • E₈` is even and integral but not
unimodular. -/
theorem IsIntegral.not_isUnimodular_sqrt_smul [Nontrivial E] (h : IsIntegral L) {m : ℕ}
    (hm : 1 < m) : ¬ IsUnimodular (√(m : ℝ) • L) :=
  h.not_isUnimodular_smul <| by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.lt_sqrt zero_le_one, one_pow]
    exact_mod_cast hm

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, scaling a unimodular lattice by `c` with `|c| ≠ 1` never gives a
unimodular lattice. -/
theorem IsUnimodular.not_isUnimodular_smul [Nontrivial E] (h : IsUnimodular L) {c : ℝ}
    (hc : |c| ≠ 1) : ¬ IsUnimodular (c • L) := by
  borelize E
  have := h.isIntegral.discreteTopology
  have : IsZLattice ℝ L := ⟨h.span_eq_top⟩
  intro hu
  rcases eq_or_ne c 0 with rfl | hc0
  · -- The lattice `0 • L` is zero, and the dual of the zero lattice is the whole space.
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hxd : x ∈ dual ((0 : ℝ) • L) := mem_dual.mpr fun y hy ↦ ⟨0, by simp_all⟩
    rw [← isUnimodular_iff_eq_dual.mp hu, zero_smul, zero_eq_bot, mem_bot] at hxd
    exact hx hxd
  · have : NeZero c := ⟨hc0⟩
    have hdet := hu.det_eq_one
    rw [det_smul L, h.det_eq_one, mul_one, pow_mul, ← sq_abs, ← pow_mul,
      pow_eq_one_iff_of_nonneg (abs_nonneg c) (mul_ne_zero two_ne_zero finrank_pos.ne')] at hdet
    exact hc hdet

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, dividing a unimodular lattice by a natural number `m > 1` never gives a
unimodular lattice. -/
theorem IsUnimodular.not_isUnimodular_inv_natCast_smul [Nontrivial E] (h : IsUnimodular L)
    {m : ℕ} (hm : 1 < m) : ¬ IsUnimodular ((m : ℝ)⁻¹ • L) := by
  refine h.not_isUnimodular_smul ?_
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  rw [abs_of_nonneg (inv_nonneg.mpr (zero_le_one.trans hm1.le))]
  exact (inv_lt_one_of_one_lt₀ hm1).ne

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, dividing a unimodular lattice by a natural number `m > 1` produces a
non-integral lattice: its dual `m • L` lies inside `m⁻¹ • L`, so integrality would force
unimodularity. -/
theorem IsUnimodular.not_isIntegral_inv_natCast_smul [Nontrivial E] (h : IsUnimodular L)
    {m : ℕ} (hm : 1 < m) : ¬ IsIntegral ((m : ℝ)⁻¹ • L) := by
  rw [isIntegral_iff_isUnimodular_of_dual_le (h.dual_inv_natCast_smul_le (by omega))]
  exact h.not_isUnimodular_inv_natCast_smul hm

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, dividing a unimodular lattice by a natural number `m > 1` never gives an
even lattice. -/
theorem IsUnimodular.not_isEven_inv_natCast_smul [Nontrivial E] (h : IsUnimodular L)
    {m : ℕ} (hm : 1 < m) : ¬ IsEven ((m : ℝ)⁻¹ • L) :=
  fun he ↦ h.not_isIntegral_inv_natCast_smul hm he.isIntegral

omit [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, for a unimodular lattice `L` and `m > 1`, the dual `m • L` is strictly
contained in `m⁻¹ • L`. -/
theorem IsUnimodular.dual_inv_natCast_smul_lt [Nontrivial E] (h : IsUnimodular L) {m : ℕ}
    (hm : 1 < m) : dual ((m : ℝ)⁻¹ • L) < (m : ℝ)⁻¹ • L :=
  (dual_lt_iff_not_isUnimodular_of_dual_le (h.dual_inv_natCast_smul_le (by omega))).mpr
    (h.not_isUnimodular_inv_natCast_smul hm)

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, dividing a unimodular lattice by a natural number `m > 1` gives a
lattice of determinant strictly less than `1`. -/
theorem IsUnimodular.det_inv_natCast_smul_lt_one [Nontrivial E] (h : IsUnimodular L) {m : ℕ}
    (hm : 1 < m) : det ((m : ℝ)⁻¹ • L) < 1 := by
  rw [h.det_inv_natCast_smul]
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hm1 (mul_ne_zero two_ne_zero finrank_pos.ne'))

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- In positive dimension, for a unimodular lattice `L` and `m > 1`, `det (m⁻¹ • L) = m⁻²ⁿ < 1`
differs from the order `1` of `DiscriminantGroup (m⁻¹ • L)`, showing that `IsIntegral` is needed in
`IsIntegral.det_eq_card_discriminantGroup`. -/
theorem IsUnimodular.det_inv_natCast_smul_ne_card_discriminantGroup [Nontrivial E]
    (h : IsUnimodular L) {m : ℕ} (hm : 1 < m) :
    det ((m : ℝ)⁻¹ • L) ≠ Nat.card (DiscriminantGroup ((m : ℝ)⁻¹ • L)) := by
  rw [h.card_discriminantGroup_inv_natCast_smul (by omega), Nat.cast_one]
  exact (h.det_inv_natCast_smul_lt_one hm).ne

end InnerProductSpace

/-! ### The half-integer lattice `½ ℤ` -/

section HalfInt

/-- The half-integer lattice `½ ℤ ⊆ ℝ` is the integer lattice `ℤ` scaled by `2⁻¹`. -/
theorem span_one_div_two_eq_inv_smul :
    (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) = ((2 : ℕ) : ℝ)⁻¹ • span ℤ {1} := by
  simp [smul_span]

/-- The dual of the half-integer lattice `½ ℤ ⊆ ℝ` is `2 ℤ`. -/
theorem dual_span_one_div_two :
    dual (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) = span ℤ {2} := by
  simpa using dual_span_singleton (c := (1 / 2 : ℝ)) (by norm_num)

/-- The dual `2 ℤ` of `½ ℤ ⊆ ℝ` is contained in `½ ℤ`. -/
theorem dual_span_one_div_two_le :
    dual (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) ≤ span ℤ {1 / 2} := by
  rw [span_one_div_two_eq_inv_smul]
  exact isUnimodular_span_one.dual_inv_natCast_smul_le two_ne_zero

/-- The dual `2 ℤ` of `½ ℤ ⊆ ℝ` is strictly contained in `½ ℤ`. -/
theorem dual_span_one_div_two_lt :
    dual (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) < span ℤ {1 / 2} := by
  rw [span_one_div_two_eq_inv_smul]
  exact isUnimodular_span_one.dual_inv_natCast_smul_lt one_lt_two

/-- The discriminant group `(½ ℤ)^∨ ⧸ ((½ ℤ) ∩ (½ ℤ)^∨) = 2ℤ ⧸ 2ℤ` of `½ ℤ ⊆ ℝ` is a
subsingleton. -/
instance instSubsingletonDiscriminantGroupSpanOneDivTwo :
    Subsingleton (DiscriminantGroup (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ)) :=
  subsingleton_discriminantGroup_iff.mpr dual_span_one_div_two_le

/-- The discriminant group `(½ ℤ)^∨ ⧸ ((½ ℤ) ∩ (½ ℤ)^∨) = 2ℤ ⧸ 2ℤ` of `½ ℤ ⊆ ℝ` has `0` as its
unique element. -/
noncomputable instance instUniqueDiscriminantGroupSpanOneDivTwo :
    Unique (DiscriminantGroup (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ)) where
  toInhabited := inferInstance
  uniq x := Subsingleton.elim x default

/-- The discriminant group of `½ ℤ ⊆ ℝ` has order `1`. -/
theorem card_discriminantGroup_span_one_div_two :
    Nat.card (DiscriminantGroup (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ)) = 1 :=
  Nat.card_unique

/-- The half-integer lattice `½ ℤ ⊆ ℝ` is not integral: `⟪1/2, 1/2⟫ = 1/4 ∉ ℤ`. -/
theorem not_isIntegral_span_one_div_two :
    ¬ IsIntegral (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) := by
  rw [span_one_div_two_eq_inv_smul]
  exact isUnimodular_span_one.not_isIntegral_inv_natCast_smul one_lt_two

/-- The half-integer lattice `½ ℤ ⊆ ℝ` is not even. -/
theorem not_isEven_span_one_div_two :
    ¬ IsEven (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) := by
  rw [span_one_div_two_eq_inv_smul]
  exact isUnimodular_span_one.not_isEven_inv_natCast_smul one_lt_two

/-- The half-integer lattice `½ ℤ ⊆ ℝ` is not unimodular. -/
theorem not_isUnimodular_span_one_div_two :
    ¬ IsUnimodular (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) := by
  rw [span_one_div_two_eq_inv_smul]
  exact isUnimodular_span_one.not_isUnimodular_inv_natCast_smul one_lt_two

/-- The half-integer lattice `½ ℤ ⊆ ℝ` has determinant `1 / 4`. -/
theorem det_span_one_div_two :
    det (span ℤ {(1 / 2 : ℝ)} : Submodule ℤ ℝ) = 1 / 4 := by
  rw [span_one_div_two_eq_inv_smul, isUnimodular_span_one.det_inv_natCast_smul, Module.finrank_self]
  norm_num

end HalfInt

end ZLattice
