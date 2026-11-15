/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Dual

/-!
# Integral, even and unimodular lattices in a real inner product space

A `ℤ`-submodule `L` of a real inner product space `E` is

* **integral** (`ZLattice.IsIntegral`) if `⟪x, y⟫ ∈ ℤ` for all `x, y ∈ L`, that is `L ≤ L^∨`, where
  `L^∨ = ZLattice.dual L` is the dual lattice;
* **even** (`ZLattice.IsEven`) if `‖x‖² ∈ 2ℤ` for every `x ∈ L`;
* **unimodular** (`ZLattice.IsUnimodular`) if it is self-dual, `L = L^∨`.

The inner product is positive definite, so these are the classical notions for positive-definite
lattices; no definiteness hypothesis appears. Evenness only involves the norm, so it is defined for
`ℤ`-submodules of any seminormed additive commutative group. Integrality is recorded as the
inclusion `L ≤ dual L`, with the elementwise form as `ZLattice.isIntegral_iff`.

In a real inner product space, an even lattice is integral, by polarization:
`2⟪x, y⟫ = ‖x + y‖² - ‖x‖² - ‖y‖²`
(`ZLattice.IsEven.isIntegral`). The converse fails: `ℤ ⊆ ℝ` is unimodular, hence integral, but not
even (`ZLattice.not_isEven_span_one`), while `√2 ℤ ⊆ ℝ` is even (`ZLattice.isEven_span_sqrt_two`).
More generally the `ℤ`-span of an orthonormal basis, the lattice `ℤⁿ ⊆ ℝⁿ`, is unimodular
(`ZLattice.isUnimodular_span_orthonormalBasis`).

All three predicates are invariant under linear isometry equivalences
(`ZLattice.isIntegral_comap_iff`, `ZLattice.isEven_comap_iff`, `ZLattice.isUnimodular_comap_iff`),
stated for the pull-back `ZLattice.comap` of Mathlib.

These are the hypotheses under which the theta series of a lattice is a modular form: an even
unimodular lattice has a theta series of level one.

## Main definitions

* `ZLattice.IsIntegral L`: the lattice `L` is integral, `L ≤ dual L`.
* `ZLattice.IsEven L`: every vector of `L` has even integral squared norm.
* `ZLattice.IsUnimodular L`: the lattice `L` is self-dual, `L = dual L`.
* `ZLattice.IsIntegral.integralForm`: the inner product of an integral lattice, as an
  integer-valued symmetric bilinear form on `L`.

## Main statements

* `ZLattice.isIntegral_iff`: `L` is integral if and only if all inner products on `L` are
  integers.
* `ZLattice.IsEven.isIntegral`: an even lattice is integral.
* `ZLattice.IsIntegral.discreteTopology`: an integral lattice is discrete.
* `ZLattice.IsUnimodular.span_eq_top`: a unimodular lattice in a finite-dimensional space spans it.
* `ZLattice.isEven_span_singleton_iff`, `ZLattice.isIntegral_span_singleton_iff`: the lattice `ℤ v`
  is even if and only if `‖v‖² ∈ 2ℤ`, and integral if and only if `‖v‖² ∈ ℤ`.
* `ZLattice.dual_le_iff_isIntegral_dual`, `ZLattice.dual_lt_iff_isIntegral_dual_and_not_isIntegral`,
  `ZLattice.dual_lt_iff_isIntegral_dual_and_not_isUnimodular`: for a discrete lattice `L` in a
  finite-dimensional space, `L^∨ ≤ L` if and only if `L^∨` is integral, and `L^∨ < L` if and only
  if `L^∨` is integral and `L` is not integral (equivalently, not unimodular); in particular
  `ZLattice.dual_span_inv_two` and `ZLattice.span_two_lt_span_inv_two` give `(½ ℤ)^∨ = 2ℤ < ½ ℤ`.
* `ZLattice.IsEven.exists_norm_add_sq_sub_norm_sq_eq`,
  `ZLattice.IsIntegral.exists_norm_add_sq_sub_norm_sq_eq`: for `γ ∈ L^∨` and `v ∈ L`,
  `‖γ + v‖² - ‖γ‖²` lies in `2ℤ` when `L` is even and in `ℤ` when `L` is integral, so `‖γ‖² / 2`
  is well defined modulo `ℤ` on `L^∨ / L` in the first case.
* `ZLattice.IsEven.exists_natCast_mul_norm_add_sq_eq`: for even `L`, `γ ∈ L^∨` and `N ‖γ‖² ∈ 2ℤ`,
  `N ‖γ + v‖² ∈ 2ℤ` for every `v ∈ L`.
-/

public section

open Submodule
open scoped RealInnerProductSpace

namespace ZLattice

/-! ### Even lattices -/

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A lattice is even if the squared norm of each of its vectors is an even integer. -/
def IsEven (L : Submodule ℤ E) : Prop :=
  ∀ x ∈ L, ∃ m : ℤ, ‖x‖ ^ 2 = 2 * m

theorem isEven_iff {L : Submodule ℤ E} : IsEven L ↔ ∀ x ∈ L, ∃ m : ℤ, ‖x‖ ^ 2 = 2 * m :=
  Iff.rfl

/-- A sublattice of an even lattice is even. -/
theorem IsEven.mono {L M : Submodule ℤ E} (hM : IsEven M) (h : L ≤ M) : IsEven L :=
  fun x hx ↦ hM x (h hx)

/-- The lattice spanned by a single vector `v` is even if and only if `‖v‖²` is an even
integer. -/
theorem isEven_span_singleton_iff [NormSMulClass ℤ E] {v : E} :
    IsEven (span ℤ {v}) ↔ ∃ m : ℤ, ‖v‖ ^ 2 = 2 * m := by
  refine ⟨fun h ↦ h v (mem_span_singleton_self v), fun ⟨m, hm⟩ x hx ↦ ?_⟩
  obtain ⟨n, rfl⟩ := mem_span_singleton.mp hx
  refine ⟨n ^ 2 * m, ?_⟩
  simp [norm_smul, mul_pow, Int.norm_eq_abs, hm]
  ring

end Seminormed

/-- The lattice `√2 ℤ ⊆ ℝ` is even. -/
theorem isEven_span_sqrt_two : IsEven (span ℤ {√2} : Submodule ℤ ℝ) :=
  isEven_span_singleton_iff.mpr ⟨1, by simp⟩

/-- The lattice `ℤ ⊆ ℝ` is not even: the vector `1` has squared norm `1`. -/
theorem not_isEven_span_one : ¬ IsEven (span ℤ {1} : Submodule ℤ ℝ) := by
  rw [isEven_span_singleton_iff]
  rintro ⟨m, hm⟩
  have : (1 : ℤ) = 2 * m := by exact_mod_cast (by simpa using hm : (1 : ℝ) = 2 * m)
  omega

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Evenness is invariant under linear isometry equivalences. -/
@[simp]
theorem isEven_comap_iff [NormedSpace ℝ E] [NormedSpace ℝ F] (L : Submodule ℤ E)
    (e : F ≃ₗᵢ[ℝ] E) : IsEven (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) ↔ IsEven L := by
  simp only [isEven_iff, mem_comap, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ e.norm_map x ▸ h _ hx⟩
  simpa using h (e.symm y) (by rwa [e.apply_symm_apply])

/-- An even lattice is discrete: a nonzero vector has squared norm at least `2`. -/
theorem IsEven.discreteTopology {L : Submodule ℤ E} (hL : IsEven L) : DiscreteTopology L :=
  discreteTopology_of_norm_sq_mem_int_mul (c := 2) (by norm_num) hL

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-! ### Integral lattices -/

/-- A lattice is integral if it is contained in its dual, that is, if the inner product of any
two of its vectors is an integer (`isIntegral_iff`). -/
def IsIntegral (L : Submodule ℤ E) : Prop :=
  L ≤ dual L

theorem isIntegral_iff_le_dual {L : Submodule ℤ E} : IsIntegral L ↔ L ≤ dual L :=
  Iff.rfl

/-- A lattice is integral exactly when the inner product of any two of its vectors is an
integer. -/
theorem isIntegral_iff {L : Submodule ℤ E} :
    IsIntegral L ↔ ∀ x ∈ L, ∀ y ∈ L, ∃ m : ℤ, ⟪x, y⟫ = m := by
  simp only [isIntegral_iff_le_dual, IsConcreteLE.le_iff, mem_dual]

/-- The lattice spanned by a single vector `v` in a real inner product space is integral if and
only if `‖v‖²` is an integer. -/
theorem isIntegral_span_singleton_iff {v : E} :
    IsIntegral (span ℤ {v}) ↔ ∃ m : ℤ, ‖v‖ ^ 2 = m := by
  refine ⟨fun h ↦ ?_, fun ⟨m, hm⟩ ↦ isIntegral_iff.mpr fun x hx y hy ↦ ?_⟩
  · simpa [real_inner_self_eq_norm_sq] using
      isIntegral_iff.mp h v (mem_span_singleton_self v) v (mem_span_singleton_self v)
  · obtain ⟨a, rfl⟩ := mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := mem_span_singleton.mp hy
    refine ⟨a * b * m, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ a, ← Int.cast_smul_eq_zsmul ℝ b, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq, hm]
    push_cast
    ring

/-- The lattice `½ ℤ ⊆ ℝ` is not integral: the generator `1 / 2` has squared norm `1 / 4`. -/
theorem not_isIntegral_span_inv_two : ¬ IsIntegral (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) := by
  rw [isIntegral_span_singleton_iff]
  rintro ⟨m, hm⟩
  have h4 : (1 : ℝ) = 4 * m := by
    norm_num at hm
    linarith
  have h4' : (1 : ℤ) = 4 * m := by exact_mod_cast h4
  omega

/-- A sublattice of an integral lattice is integral. -/
theorem IsIntegral.mono {L M : Submodule ℤ E} (hM : IsIntegral M) (h : L ≤ M) : IsIntegral L :=
  h.trans (hM.trans (dual_anti h))

/-- An integral lattice is discrete. -/
theorem IsIntegral.discreteTopology {L : Submodule ℤ E} (h : IsIntegral L) :
    DiscreteTopology L := by
  -- Nonzero vectors have a positive integer squared norm, hence norm at least one.
  refine discreteTopology_of_isOpen_singleton_zero ?_
  rw [Metric.isOpen_singleton_iff]
  refine ⟨1, one_pos, fun x hx ↦ ?_⟩
  have hx1 : ‖(x : E)‖ < 1 := by simpa using hx
  by_contra hx0
  obtain ⟨m, hm⟩ := isIntegral_iff.1 h x.1 x.2 x.1 x.2
  rw [real_inner_self_eq_norm_sq] at hm
  have hpos : (0 : ℝ) < ‖(x : E)‖ := norm_pos_iff.2 fun h0 ↦ hx0 (Subtype.ext h0)
  have hm0 : (0 : ℤ) < m := by exact_mod_cast hm ▸ pow_pos hpos 2
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
  nlinarith

/-- The integer-valued inner product on an integral lattice, as a `ℤ`-bilinear form on `L`. -/
noncomputable def IsIntegral.integralForm {L : Submodule ℤ E} (hL : IsIntegral L) :
    LinearMap.BilinForm ℤ L :=
  (LinearMap.BilinForm.dualSubmoduleToDual (innerₗ E) L).comp
    (Submodule.inclusion (hL.trans (dual_def L).le))

/-- The integer-valued inner product of an integral lattice is the inner product of `E`. -/
@[simp]
theorem IsIntegral.integralForm_cast {L : Submodule ℤ E} (hL : IsIntegral L) (x y : L) :
    (hL.integralForm x y : ℝ) = ⟪(x : E), (y : E)⟫ := by
  rw [integralForm, LinearMap.comp_apply, LinearMap.BilinForm.dualSubmoduleToDual_apply_apply]
  exact LinearMap.BilinForm.dualSubmodulePairing_spec (innerₗ E)
    (Submodule.inclusion (hL.trans (dual_def L).le) x) y

/-- The integer-valued inner product of an integral lattice is symmetric. -/
theorem IsIntegral.isSymm_integralForm {L : Submodule ℤ E} (hL : IsIntegral L) :
    hL.integralForm.IsSymm :=
  ⟨fun x y ↦ Int.cast_injective (α := ℝ) <| by simp [real_inner_comm]⟩

/-- For an integral lattice `L`, the squared norm `‖γ‖²` of a dual vector `γ ∈ L^∨` is well
defined modulo `ℤ` on the coset `γ + L`: `‖γ + v‖² - ‖γ‖² ∈ ℤ` for `v ∈ L`. -/
theorem IsIntegral.exists_norm_add_sq_sub_norm_sq_eq {L : Submodule ℤ E} (hL : IsIntegral L)
    {γ v : E} (hγ : γ ∈ dual L) (hv : v ∈ L) : ∃ m : ℤ, ‖γ + v‖ ^ 2 - ‖γ‖ ^ 2 = m := by
  obtain ⟨a, ha⟩ := mem_dual.mp hγ v hv
  obtain ⟨b, hb⟩ := isIntegral_iff.mp hL v hv v hv
  refine ⟨2 * a + b, ?_⟩
  rw [real_inner_self_eq_norm_sq] at hb
  push_cast
  linarith [norm_add_sq_real γ v]

/-- An even lattice is integral, by polarization. -/
theorem IsEven.isIntegral {L : Submodule ℤ E} (h : IsEven L) : IsIntegral L := by
  refine isIntegral_iff.mpr fun x hx y hy ↦ ?_
  obtain ⟨a, ha⟩ := h x hx
  obtain ⟨b, hb⟩ := h y hy
  obtain ⟨c, hc⟩ := h (x + y) (add_mem hx hy)
  refine ⟨c - a - b, ?_⟩
  have := norm_add_sq_real x y
  push_cast
  linarith

/-- The lattice `½ ℤ ⊆ ℝ` is not even. -/
theorem not_isEven_span_inv_two : ¬ IsEven (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) :=
  mt IsEven.isIntegral not_isIntegral_span_inv_two

/-- For an even lattice `L`, the half-norm `‖γ‖² / 2` of a dual vector `γ ∈ L^∨` is well defined
modulo `ℤ` on the coset `γ + L`: `‖γ + v‖² - ‖γ‖² ∈ 2ℤ` for `v ∈ L`. -/
theorem IsEven.exists_norm_add_sq_sub_norm_sq_eq {L : Submodule ℤ E} (hL : IsEven L)
    {γ v : E} (hγ : γ ∈ dual L) (hv : v ∈ L) : ∃ m : ℤ, ‖γ + v‖ ^ 2 - ‖γ‖ ^ 2 = 2 * m := by
  obtain ⟨a, ha⟩ := mem_dual.mp hγ v hv
  obtain ⟨b, hb⟩ := hL v hv
  refine ⟨a + b, ?_⟩
  push_cast
  linarith [norm_add_sq_real γ v]

/-- For an even lattice `L`, `γ ∈ L^∨` and `N ‖γ‖² ∈ 2ℤ`, the squared norms on the coset satisfy
`N ‖γ + v‖² ∈ 2ℤ` for every `v ∈ L`. -/
theorem IsEven.exists_natCast_mul_norm_add_sq_eq {L : Submodule ℤ E} (hL : IsEven L) {γ : E}
    (hγ : γ ∈ dual L) {N : ℕ} (hNγ : ∃ n : ℤ, N * ‖γ‖ ^ 2 = 2 * n) {v : E} (hv : v ∈ L) :
    ∃ m : ℤ, (N : ℝ) * ‖γ + v‖ ^ 2 = 2 * m := by
  obtain ⟨n, hn⟩ := hNγ
  obtain ⟨j, hj⟩ := hL.exists_norm_add_sq_sub_norm_sq_eq hγ hv
  exact ⟨n + N * j, by push_cast; linear_combination (N : ℝ) * hj + hn⟩

/-! ### Unimodular lattices -/

/-- A lattice is unimodular if it is equal to its dual. -/
def IsUnimodular (L : Submodule ℤ E) : Prop :=
  L = dual L

theorem isUnimodular_iff_eq_dual {L : Submodule ℤ E} : IsUnimodular L ↔ L = dual L :=
  Iff.rfl

theorem IsUnimodular.dual_eq {L : Submodule ℤ E} (h : IsUnimodular L) : dual L = L :=
  h.symm

/-- A unimodular lattice is integral. -/
theorem IsUnimodular.isIntegral {L : Submodule ℤ E} (h : IsUnimodular L) : IsIntegral L :=
  h.le

/-- A unimodular lattice in a finite-dimensional real inner product space spans the space over
`ℝ`; in particular it is a full lattice. -/
theorem IsUnimodular.span_eq_top [FiniteDimensional ℝ E] {L : Submodule ℤ E} (h : IsUnimodular L) :
    span ℝ (L : Set E) = ⊤ := by
  -- A nonzero vector `v` orthogonal to `L` lies in `L = L^∨`, and so do all its real multiples,
  -- including one of squared norm `1 / 2`, which is not an integer.
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (mt Submodule.orthogonal_eq_bot_iff.1 hne)
  have hmem (t : ℝ) : t • v ∈ L := by
    rw [← h.dual_eq, mem_dual]
    refine fun y hy ↦ ⟨0, ?_⟩
    rw [real_inner_smul_left, real_inner_comm,
      Submodule.inner_right_of_mem_orthogonal (subset_span hy) hv]
    simp
  obtain ⟨m, hm⟩ := isIntegral_iff.1 h.isIntegral _ (hmem (1 / (√2 * ‖v‖))) _
    (hmem (1 / (√2 * ‖v‖)))
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at hm
  have h2 : (1 / (√2 * ‖v‖)) * ((1 / (√2 * ‖v‖)) * ‖v‖ ^ 2) = 1 / 2 := by
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [h2] at hm
  have h3 : (2 : ℝ) * m = 1 := by linarith
  have h4 : (2 : ℤ) * m = 1 := by exact_mod_cast h3
  omega

/-- An integral lattice is unimodular as soon as its dual is contained in it. -/
theorem IsIntegral.isUnimodular_iff {L : Submodule ℤ E} (h : IsIntegral L) :
    IsUnimodular L ↔ dual L ≤ L :=
  ⟨fun hu ↦ hu.dual_eq.le, h.antisymm⟩

/-- For a discrete lattice `L` in a finite-dimensional real inner product space, `L^∨ ≤ L` if and
only if the dual lattice `L^∨` is integral: by biduality `L = (L^∨)^∨`. -/
theorem dual_le_iff_isIntegral_dual [FiniteDimensional ℝ E] {L : Submodule ℤ E}
    [DiscreteTopology L] : dual L ≤ L ↔ IsIntegral (dual L) := by
  rw [isIntegral_iff_le_dual, dual_dual]

/-- For a discrete lattice `L` in a finite-dimensional real inner product space, `L^∨ < L` if and
only if `L^∨` is integral and `L` is not integral. -/
theorem dual_lt_iff_isIntegral_dual_and_not_isIntegral [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] :
    dual L < L ↔ IsIntegral (dual L) ∧ ¬ IsIntegral L := by
  rw [lt_iff_le_not_ge, dual_le_iff_isIntegral_dual, ← isIntegral_iff_le_dual]

/-- For a discrete lattice `L` in a finite-dimensional real inner product space, `L^∨ < L` if and
only if `L^∨` is integral and `L` is not unimodular. -/
theorem dual_lt_iff_isIntegral_dual_and_not_isUnimodular [FiniteDimensional ℝ E]
    {L : Submodule ℤ E} [DiscreteTopology L] :
    dual L < L ↔ IsIntegral (dual L) ∧ ¬ IsUnimodular L := by
  rw [lt_iff_le_and_ne, dual_le_iff_isIntegral_dual, isUnimodular_iff_eq_dual, eq_comm]

/-- The `ℤ`-span of an orthonormal basis is unimodular. -/
theorem isUnimodular_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : IsUnimodular (span ℤ (Set.range b)) :=
  (dual_span_orthonormalBasis b).symm

/-- The lattice `ℤ ⊆ ℝ` is unimodular. -/
theorem isUnimodular_span_one : IsUnimodular (span ℤ {1} : Submodule ℤ ℝ) := by
  simpa using isUnimodular_span_orthonormalBasis (OrthonormalBasis.singleton Unit ℝ)

/-- The lattice `½ ℤ ⊆ ℝ` is not unimodular. -/
theorem not_isUnimodular_span_inv_two : ¬ IsUnimodular (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) :=
  mt IsUnimodular.isIntegral not_isIntegral_span_inv_two

/-- The dual of the lattice `½ ℤ ⊆ ℝ` is `2ℤ`. -/
@[simp]
theorem dual_span_inv_two :
    dual (span ℤ {(2 : ℝ)⁻¹} : Submodule ℤ ℝ) = span ℤ {(2 : ℝ)} := by
  rw [dual_span_singleton (inv_ne_zero two_ne_zero), inv_inv]

/-- The dual lattice `2ℤ` of `½ ℤ ⊆ ℝ` is strictly contained in `½ ℤ`. -/
theorem span_two_lt_span_inv_two :
    (span ℤ {(2 : ℝ)} : Submodule ℤ ℝ) < span ℤ {(2 : ℝ)⁻¹} := by
  rw [← dual_span_inv_two, dual_lt_iff_isIntegral_dual_and_not_isIntegral, dual_span_inv_two]
  exact ⟨isIntegral_span_singleton_iff.mpr ⟨4, by norm_num⟩, not_isIntegral_span_inv_two⟩

/-! ### Invariance under isometries -/

variable (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E)

/-- Integrality is invariant under linear isometry equivalences. -/
@[simp]
theorem isIntegral_comap_iff :
    IsIntegral (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) ↔ IsIntegral L := by
  rw [isIntegral_iff_le_dual, isIntegral_iff_le_dual, dual_comap]
  simp only [IsConcreteLE.le_iff, mem_comap, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  exact (e.surjective.forall (p := fun y ↦ y ∈ L → y ∈ dual L)).symm

/-- Unimodularity is invariant under linear isometry equivalences. -/
@[simp]
theorem isUnimodular_comap_iff :
    IsUnimodular (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) ↔ IsUnimodular L := by
  rw [isUnimodular_iff_eq_dual, isUnimodular_iff_eq_dual, dual_comap]
  simp only [SetLike.ext_iff, mem_comap, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv]
  exact (e.surjective.forall (p := fun y ↦ y ∈ L ↔ y ∈ dual L)).symm

end ZLattice
