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

* `ZLattice.smul_eq_comap`: for `c ≠ 0`, `c • L` is the pullback of `L` along `c⁻¹ • ·`.
* `ZLattice.basisSmul`: for `c ≠ 0`, a `ℤ`-basis `b` of `L` gives the `ℤ`-basis `c • b` of `c • L`.
* `ZLattice.exists_forall_ne_zero_lt_norm`: scaling up the integer span of a basis gives full
  lattices all of whose nonzero vectors are longer than a prescribed bound.
* `ZLattice.exists_forall_add_mem_eq_zero_of_isBounded`: a bounded set meets none of its
  translates by the nonzero vectors of such a lattice.
* `ZLattice.dual_smul`: `(c • L)^∨ = c⁻¹ • L^∨` for `c ≠ 0`.
* `ZLattice.covolume_smul`, `ZLattice.det_smul`: `covolume (c • L) = |c|ⁿ covolume L` and
  `det (c • L) = c²ⁿ det L` for `c ≠ 0`.
* `ZLattice.covolume_natCast_smul`: `covolume (c • L) = cⁿ covolume L` for a positive integer `c`.
* `ZLattice.isIntegral_smul_iff`, `ZLattice.isEven_smul_iff`: the exact criteria for `c • L` to be
  integral or even.
* `ZLattice.IsIntegral.sqrt_smul`, `ZLattice.IsEven.sqrt_smul`,
  `ZLattice.IsIntegral.isEven_sqrt_smul`: `√m • L` is integral when `L` is, and even when `L` is
  even or when `L` is integral and `m` is even.
* `ZLattice.det_sqrt_smul`, `ZLattice.IsIntegral.card_discriminantGroup_sqrt_smul`:
  `det (√m • L) = mⁿ det L` for `m ≠ 0` (and `|A_{√m • L}| = mⁿ |A_L|` for integral `L`), and
  `ZLattice.det_sqrt_smul_span_orthonormalBasis`: `det (√m • ℤⁿ) = mⁿ`.
* `ZLattice.IsIntegral.not_isUnimodular_smul`, `ZLattice.IsIntegral.not_isUnimodular_sqrt_smul`,
  `ZLattice.IsUnimodular.not_isUnimodular_smul`: in positive dimension, scaling an integral lattice
  by `|c| > 1`, or a unimodular lattice by `|c| ≠ 1`, does not give a unimodular lattice.

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

end Seminormed

/-! ### Scaling as a change of variables -/

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (L : Submodule ℤ E)

/-- For `c ≠ 0`, the scaled lattice `c • L` is the pullback of `L` along the linear automorphism
`x ↦ c⁻¹ • x`. -/
theorem smul_eq_comap {c : ℝ} (hc : c ≠ 0) :
    c • L = ZLattice.comap ℝ L
      (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E).toLinearMap := by
  ext x
  rw [← SetLike.mem_coe, coe_pointwise_smul, Set.mem_smul_set_iff_inv_smul_mem₀ hc,
    ← SetLike.mem_coe, coe_comap]
  simp [Units.smul_def]

/-- Scaling a discrete lattice by a nonzero scalar gives a discrete lattice. -/
instance [DiscreteTopology L] (c : ℝ) [NeZero c] : DiscreteTopology (c • L : Submodule ℤ E) := by
  rw [smul_eq_comap L (NeZero.ne c)]
  infer_instance

/-- Scaling a full lattice by a nonzero scalar gives a full lattice. -/
instance [DiscreteTopology L] [IsZLattice ℝ L] (c : ℝ) [NeZero c] : IsZLattice ℝ (c • L) where
  span_top := by
    rw [smul_eq_comap L (NeZero.ne c)]
    exact IsZLattice.span_top

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

/-- Scaling a full lattice by `c ≠ 0` multiplies its covolume by `|c|ⁿ`, where `n` is the dimension
of the space, for any Haar measure. -/
@[simp]
theorem covolume_smul {c : ℝ} (hc : c ≠ 0) (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    covolume (c • L) μ = |c| ^ finrank ℝ E * covolume L μ := by
  have hA : ((ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)⁻¹ : E ≃L[ℝ] E) : E →ₗ[ℝ] E) =
      c⁻¹ • LinearMap.id := by
    ext x
    simp [Units.smul_def]
  rw [smul_eq_comap L hc, covolume_comap_continuousLinearEquiv L _ μ, hA, LinearMap.det_smul,
    LinearMap.det_id, mul_one, abs_pow, abs_inv, inv_pow, inv_inv]

/-- Scaling a full lattice by a positive integer `c` multiplies its covolume by `cⁿ`, where `n` is
the dimension of the space, for any Haar measure. -/
theorem covolume_natCast_smul (c : ℕ) [NeZero c] (μ : Measure E := by volume_tac)
    [μ.IsAddHaarMeasure] :
    covolume ((c : ℝ) • L) μ = (c : ℝ) ^ finrank ℝ E * covolume L μ := by
  rw [covolume_smul L (NeZero.ne _) μ, Nat.abs_cast]

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

variable (L) [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L]

/-- Scaling a full lattice by `c ≠ 0` multiplies its determinant by `c²ⁿ`, where `n` is the
dimension of the space. -/
@[simp]
theorem det_smul {c : ℝ} (hc : c ≠ 0) : det (c • L) = c ^ (2 * finrank ℝ E) * det L := by
  rw [det_def, det_def, covolume_smul L hc volume, mul_pow, ← pow_mul, mul_comm (finrank ℝ E),
    pow_mul, pow_mul, sq_abs]

/-- Scaling a full lattice by `√m`, for a nonzero natural number `m`, multiplies its determinant by
`mⁿ`, where `n` is the dimension of the space. -/
theorem det_sqrt_smul {m : ℕ} (hm : m ≠ 0) : det (√(m : ℝ) • L) = m ^ finrank ℝ E * det L := by
  rw [det_smul L (Real.sqrt_ne_zero'.mpr (by positivity)), pow_mul, Real.sq_sqrt m.cast_nonneg]

omit [DiscreteTopology L] [IsZLattice ℝ L] in
/-- For an orthonormal basis `b` and a nonzero natural number `m`, the scaled cubic lattice
`√m • ℤ b` has determinant `mⁿ`, where `n` is the dimension of the space. For instance `√2 ℤ²` has
determinant `4`. -/
theorem det_sqrt_smul_span_orthonormalBasis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {m : ℕ} (hm : m ≠ 0) : det (√(m : ℝ) • span ℤ (Set.range b)) = m ^ finrank ℝ E := by
  have hu := isUnimodular_span_orthonormalBasis b
  -- The lattice instances of `span ℤ (Set.range b)` are those of the `ℤ`-span of a basis.
  rw [← b.coe_toBasis] at hu ⊢
  rw [det_sqrt_smul _ hm, hu.det_eq_one, mul_one]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [DiscreteTopology L]
  [IsZLattice ℝ L] in
/-- For an orthonormal basis `b` and a nonzero natural number `m`, the discriminant group of the
scaled cubic lattice `√m • ℤ b` has order `det (√m • ℤ b) = mⁿ`, where `n` is the dimension of the
space. For instance the discriminant group `(ℤ/2)²` of `√2 ℤ²` has order `4`. -/
theorem natCard_discriminantGroup_sqrt_smul_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {m : ℕ} (hm : m ≠ 0) :
    Nat.card (DiscriminantGroup (√(m : ℝ) • span ℤ (Set.range b))) = m ^ finrank ℝ E := by
  have := b.toBasis.finiteDimensional_of_finite
  borelize E
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (by positivity)⟩
  have h :=
    ((isUnimodular_span_orthonormalBasis b).isIntegral.sqrt_smul m).det_eq_card_discriminantGroup
  rw [det_sqrt_smul_span_orthonormalBasis b hm] at h
  exact_mod_cast h.symm

variable {L}

omit [MeasurableSpace E] [BorelSpace E] in
/-- Scaling an integral full lattice `L` of rank `n` by `√m` (`m ≠ 0`) multiplies the order of its
discriminant group by `mⁿ`. -/
theorem IsIntegral.card_discriminantGroup_sqrt_smul (h : IsIntegral L) {m : ℕ} (hm : m ≠ 0) :
    Nat.card (DiscriminantGroup (√(m : ℝ) • L)) =
      m ^ finrank ℝ E * Nat.card (DiscriminantGroup L) := by
  borelize E
  have : NeZero √(m : ℝ) := ⟨Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))⟩
  refine Nat.cast_injective (R := ℝ) ?_
  rw [← (h.sqrt_smul m).det_eq_card_discriminantGroup, det_sqrt_smul L hm,
    h.det_eq_card_discriminantGroup, Nat.cast_mul, Nat.cast_pow]

/-- In positive dimension, scaling a full integral lattice by `c` with `1 < |c|` never gives a
unimodular lattice: the determinant becomes `c²ⁿ det L > 1`. -/
theorem IsIntegral.not_isUnimodular_smul [Nontrivial E] (h : IsIntegral L) {c : ℝ}
    (hc : 1 < |c|) : ¬ IsUnimodular (c • L) := by
  have hc0 : c ≠ 0 := abs_pos.mp (one_pos.trans hc)
  have : NeZero c := ⟨hc0⟩
  intro hu
  have hdet := hu.det_eq_one
  rw [det_smul L hc0, pow_mul, ← sq_abs, ← pow_mul] at hdet
  have hlt : 1 < |c| ^ (2 * finrank ℝ E) :=
    one_lt_pow₀ hc (mul_ne_zero two_ne_zero finrank_pos.ne')
  nlinarith [h.one_le_det]

/-- In positive dimension, scaling a full integral lattice by `√m` for a natural number `m > 1`
never gives a unimodular lattice. For instance `√2 • E₈` is even and integral but not
unimodular. -/
theorem IsIntegral.not_isUnimodular_sqrt_smul [Nontrivial E] (h : IsIntegral L) {m : ℕ}
    (hm : 1 < m) : ¬ IsUnimodular (√(m : ℝ) • L) :=
  h.not_isUnimodular_smul <| by
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.lt_sqrt zero_le_one, one_pow]
    exact_mod_cast hm

/-- In positive dimension, scaling a unimodular lattice by `c` with `|c| ≠ 1` never gives a
unimodular lattice. -/
theorem IsUnimodular.not_isUnimodular_smul [Nontrivial E] (h : IsUnimodular L) {c : ℝ}
    (hc : |c| ≠ 1) : ¬ IsUnimodular (c • L) := by
  intro hu
  rcases eq_or_ne c 0 with rfl | hc0
  · -- The lattice `0 • L` is zero, and the dual of the zero lattice is the whole space.
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hxd : x ∈ dual ((0 : ℝ) • L) := mem_dual.mpr fun y hy ↦ ⟨0, by simp_all⟩
    rw [← isUnimodular_iff_eq_dual.mp hu, zero_smul, zero_eq_bot, mem_bot] at hxd
    exact hx hxd
  · have : NeZero c := ⟨hc0⟩
    have hdet := hu.det_eq_one
    rw [det_smul L hc0, h.det_eq_one, mul_one, pow_mul, ← sq_abs, ← pow_mul,
      pow_eq_one_iff_of_nonneg (abs_nonneg c) (mul_ne_zero two_ne_zero finrank_pos.ne')] at hdet
    exact hc hdet

end InnerProductSpace

end ZLattice
