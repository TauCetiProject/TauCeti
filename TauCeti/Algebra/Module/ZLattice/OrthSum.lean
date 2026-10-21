/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Algebra.Module.ZLattice.Determinant

/-!
# The orthogonal direct sum of two lattices

For `ℤ`-submodules `L` of a real inner product space `E` and `M` of a real inner product space
`F`, the *orthogonal direct sum* `L ⊕ M` is the submodule `L × M` of the `L²` product
`WithLp 2 (E × F)`, whose inner product is `⟪(x, y), (x', y')⟫ = ⟪x, x'⟫ + ⟪y, y'⟫`
(`ZLattice.orthSum`).

The dual of an orthogonal direct sum is the orthogonal direct sum of the duals
(`ZLattice.dual_orthSum`). Consequently `L ⊕ M` is integral, even or unimodular exactly when both
`L` and `M` are; in particular each of the three predicates is preserved by orthogonal direct sums.

When `L` and `M` are full lattices in finite-dimensional spaces, so is `L ⊕ M`: the sum of the
`ℤ`-spans of two `ℝ`-bases is the `ℤ`-span of the product basis (`ZLattice.orthSum_span_basis`).
The Gram matrix of the product basis is block diagonal, so covolumes and determinants multiply:
`covolume (L ⊕ M) = covolume L * covolume M` and `det (L ⊕ M) = det L * det M`.

Orthogonal direct sums build integral, even or unimodular lattices of large rank from small ones,
for instance the even unimodular lattice `E₈ ⊕ E₈` of rank `16`.

## Main definitions

* `ZLattice.orthSum L M`: the orthogonal direct sum of `L` and `M`, in `WithLp 2 (E × F)`.

## Main statements

* `ZLattice.dual_orthSum`: `(L ⊕ M)^∨ = L^∨ ⊕ M^∨`.
* `ZLattice.isIntegral_orthSum_iff`, `ZLattice.isEven_orthSum_iff`,
  `ZLattice.isUnimodular_orthSum_iff`: `L ⊕ M` is integral, even or unimodular if and only if
  both `L` and `M` are.
* `ZLattice.covolume_orthSum`, `ZLattice.det_orthSum`: covolumes and determinants of full lattices
  multiply under orthogonal direct sums.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 1.
-/

public section

open Module Submodule MeasureTheory WithLp
open scoped RealInnerProductSpace

namespace ZLattice

section AddCommGroup

variable {E F : Type*} [AddCommGroup E] [AddCommGroup F]

/-- The orthogonal direct sum of lattices `L ⊆ E` and `M ⊆ F`: the vectors of the `L²` product
`WithLp 2 (E × F)` whose components lie in `L` and in `M` (`mem_orthSum`). -/
def orthSum (L : Submodule ℤ E) (M : Submodule ℤ F) : Submodule ℤ (WithLp 2 (E × F)) :=
  (L.prod M).comap (WithLp.linearEquiv 2 ℤ (E × F)).toLinearMap

variable {L L' : Submodule ℤ E} {M M' : Submodule ℤ F}

/-- A vector lies in the orthogonal direct sum exactly when its two components lie in the
summands. -/
@[simp]
theorem mem_orthSum {x : WithLp 2 (E × F)} : x ∈ orthSum L M ↔ x.fst ∈ L ∧ x.snd ∈ M :=
  (Iff.rfl)

/-- The orthogonal direct sum is monotone in each summand, and reflects inclusions. -/
theorem orthSum_le_orthSum_iff : orthSum L M ≤ orthSum L' M' ↔ L ≤ L' ∧ M ≤ M' := by
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩, fun ⟨hL, hM⟩ x hx ↦ ?_⟩
  · simpa using h (x := toLp 2 (x, 0)) (by simpa using hx)
  · simpa using h (x := toLp 2 (0, y)) (by simpa using hy)
  · rw [mem_orthSum] at hx ⊢
    exact ⟨hL hx.1, hM hx.2⟩

@[gcongr]
theorem orthSum_mono (hL : L ≤ L') (hM : M ≤ M') : orthSum L M ≤ orthSum L' M' :=
  orthSum_le_orthSum_iff.mpr ⟨hL, hM⟩

@[simp]
theorem orthSum_inj : orthSum L M = orthSum L' M' ↔ L = L' ∧ M = M' := by
  simp only [le_antisymm_iff, orthSum_le_orthSum_iff]
  tauto

end AddCommGroup

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The dual of an orthogonal direct sum is the orthogonal direct sum of the duals. -/
@[simp]
theorem dual_orthSum (L : Submodule ℤ E) (M : Submodule ℤ F) :
    dual (orthSum L M) = orthSum (dual L) (dual M) := by
  ext x
  simp only [mem_dual, mem_orthSum, prod_inner_apply, ofLp_fst, ofLp_snd, and_imp]
  refine ⟨fun h ↦ ⟨fun y hy ↦ ?_, fun z hz ↦ ?_⟩, fun ⟨hL, hM⟩ y hy hz ↦ ?_⟩
  · simpa using h (toLp 2 (y, 0)) (by simpa using hy) (by simp)
  · simpa using h (toLp 2 (0, z)) (by simp) (by simpa using hz)
  · obtain ⟨a, ha⟩ := hL _ hy
    obtain ⟨b, hb⟩ := hM _ hz
    exact ⟨a + b, by rw [ha, hb, Int.cast_add]⟩

/-! ### Integral, even and unimodular orthogonal direct sums -/

section Predicates

variable {L : Submodule ℤ E} {M : Submodule ℤ F}

/-- An orthogonal direct sum is integral if and only if both summands are. -/
@[simp]
theorem isIntegral_orthSum_iff : IsIntegral (orthSum L M) ↔ IsIntegral L ∧ IsIntegral M := by
  simp only [isIntegral_iff_le_dual, dual_orthSum, orthSum_le_orthSum_iff]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] in
/-- An orthogonal direct sum is even if and only if both summands are. -/
@[simp]
theorem isEven_orthSum_iff : IsEven (orthSum L M) ↔ IsEven L ∧ IsEven M := by
  simp only [isEven_iff]
  refine ⟨fun h ↦ ⟨fun x hx ↦ ?_, fun y hy ↦ ?_⟩, fun ⟨hL, hM⟩ x hx ↦ ?_⟩
  · simpa [prod_norm_sq_eq_of_L2] using h (toLp 2 (x, 0)) (by simpa using hx)
  · simpa [prod_norm_sq_eq_of_L2] using h (toLp 2 (0, y)) (by simpa using hy)
  · rw [mem_orthSum] at hx
    obtain ⟨a, ha⟩ := hL _ hx.1
    obtain ⟨b, hb⟩ := hM _ hx.2
    exact ⟨a + b, by rw [prod_norm_sq_eq_of_L2, ha, hb]; push_cast; ring⟩

/-- An orthogonal direct sum is unimodular if and only if both summands are. -/
@[simp]
theorem isUnimodular_orthSum_iff :
    IsUnimodular (orthSum L M) ↔ IsUnimodular L ∧ IsUnimodular M := by
  simp only [isUnimodular_iff_eq_dual, dual_orthSum, orthSum_inj]

end Predicates

/-! ### Full lattices -/

section FiniteDimensional

variable {ι κ : Type*}

/-- The orthogonal direct sum of the `ℤ`-spans of two bases is the `ℤ`-span of their product
basis of `WithLp 2 (E × F)`. -/
theorem orthSum_span_basis (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    orthSum (span ℤ (Set.range b)) (span ℤ (Set.range c)) =
      span ℤ (Set.range ((b.prod c).map (WithLp.linearEquiv 2 ℝ (E × F)).symm)) := by
  refine le_antisymm (fun x hx ↦ ?_) (span_le.mpr ?_)
  · -- Write `x = (x₁, 0) + (0, x₂)` and push each summand into the span along `inl` or `inr`.
    let e := (WithLp.linearEquiv 2 ℤ (E × F)).symm.toLinearMap
    have hx' : x = e (LinearMap.inl ℤ E F x.fst) + e (LinearMap.inr ℤ E F x.snd) := by
      simp [e, WithLp.ext_iff, Prod.ext_iff]
    rw [mem_orthSum] at hx
    rw [hx']
    refine add_mem ?_ ?_
    · have h := mem_map_of_mem (f := e ∘ₗ LinearMap.inl ℤ E F) hx.1
      rw [map_span] at h
      refine span_mono ?_ h
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inl i, by simp [e]⟩
    · have h := mem_map_of_mem (f := e ∘ₗ LinearMap.inr ℤ E F) hx.2
      rw [map_span] at h
      refine span_mono ?_ h
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Sum.inr i, by simp [e]⟩
  · rintro _ ⟨i | i, rfl⟩ <;> simpa using subset_span (Set.mem_range_self i)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  (L : Submodule ℤ E) (M : Submodule ℤ F) [DiscreteTopology L] [IsZLattice ℝ L]
  [DiscreteTopology M] [IsZLattice ℝ M]

instance : DiscreteTopology (orthSum L M) := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  obtain ⟨κ, _, _, c, rfl⟩ := exists_basis_span_eq ℝ M
  rw [orthSum_span_basis]
  infer_instance

instance : IsZLattice ℝ (orthSum L M) where
  span_top := by
    obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
    obtain ⟨κ, _, _, c, rfl⟩ := exists_basis_span_eq ℝ M
    rw [orthSum_span_basis]
    exact ZSpan.span_top _

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- The covolume of an orthogonal direct sum of full lattices is the product of the
covolumes. -/
theorem covolume_orthSum : covolume (orthSum L M) = covolume L * covolume M := by
  obtain ⟨ι, _, _, b, rfl⟩ := exists_basis_span_eq ℝ L
  obtain ⟨κ, _, _, c, rfl⟩ := exists_basis_span_eq ℝ M
  rw [orthSum_span_basis]
  -- The Gram matrix of the product basis is block diagonal, so the squared covolumes multiply.
  have hgram : Matrix.gram ℝ ((b.prod c).map (WithLp.linearEquiv 2 ℝ (E × F)).symm) =
      Matrix.fromBlocks (Matrix.gram ℝ b) 0 0 (Matrix.gram ℝ c) := by
    ext (i | i) (j | j) <;> simp [Matrix.gram_apply]
  refine (pow_left_inj₀ (covolume_pos _ volume).le
    (mul_pos (covolume_pos _ volume) (covolume_pos _ volume)).le two_ne_zero).mp ?_
  rw [mul_pow, covolume_span_sq_eq_det_gram, covolume_span_sq_eq_det_gram,
    covolume_span_sq_eq_det_gram, hgram, Matrix.det_fromBlocks_zero₂₁]

/-- The determinant of an orthogonal direct sum of full lattices is the product of the
determinants. -/
theorem det_orthSum : det (orthSum L M) = det L * det M := by
  rw [det_def, det_def, det_def, covolume_orthSum, mul_pow]

end FiniteDimensional

end ZLattice
