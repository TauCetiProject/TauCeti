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

## Main statements

* `ZLattice.isIntegral_iff`: `L` is integral if and only if all inner products on `L` are
  integers.
* `ZLattice.IsEven.isIntegral`: an even lattice is integral.
* `ZLattice.isEven_span_singleton_iff`: the lattice `ℤ v` is even if and only if `‖v‖² ∈ 2ℤ`.
* `ZLattice.IsEven.exists_norm_add_sq_sub_norm_sq_eq`,
  `ZLattice.IsIntegral.exists_norm_add_sq_sub_norm_sq_eq`: for `γ ∈ L^∨` and `v ∈ L`,
  `‖γ + v‖² - ‖γ‖²` lies in `2ℤ` when `L` is even and in `ℤ` when `L` is integral, so `‖γ‖² / 2`
  is well defined modulo `ℤ` on `L^∨ / L` in the first case.
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

/-- A sublattice of an integral lattice is integral. -/
theorem IsIntegral.mono {L M : Submodule ℤ E} (hM : IsIntegral M) (h : L ≤ M) : IsIntegral L :=
  h.trans (hM.trans (dual_anti h))

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

/-- For an even lattice `L`, the half-norm `‖γ‖² / 2` of a dual vector `γ ∈ L^∨` is well defined
modulo `ℤ` on the coset `γ + L`: `‖γ + v‖² - ‖γ‖² ∈ 2ℤ` for `v ∈ L`. -/
theorem IsEven.exists_norm_add_sq_sub_norm_sq_eq {L : Submodule ℤ E} (hL : IsEven L)
    {γ v : E} (hγ : γ ∈ dual L) (hv : v ∈ L) : ∃ m : ℤ, ‖γ + v‖ ^ 2 - ‖γ‖ ^ 2 = 2 * m := by
  obtain ⟨a, ha⟩ := mem_dual.mp hγ v hv
  obtain ⟨b, hb⟩ := hL v hv
  refine ⟨a + b, ?_⟩
  push_cast
  linarith [norm_add_sq_real γ v]

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

/-- An integral lattice is unimodular as soon as its dual is contained in it. -/
theorem IsIntegral.isUnimodular_iff {L : Submodule ℤ E} (h : IsIntegral L) :
    IsUnimodular L ↔ dual L ≤ L :=
  ⟨fun hu ↦ hu.dual_eq.le, h.antisymm⟩

/-- The `ℤ`-span of an orthonormal basis is unimodular. -/
theorem isUnimodular_span_orthonormalBasis {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) : IsUnimodular (span ℤ (Set.range b)) :=
  (dual_span_orthonormalBasis b).symm

/-- The lattice `ℤ ⊆ ℝ` is unimodular. -/
theorem isUnimodular_span_one : IsUnimodular (span ℤ {1} : Submodule ℤ ℝ) := by
  simpa using isUnimodular_span_orthonormalBasis (OrthonormalBasis.singleton Unit ℝ)

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
