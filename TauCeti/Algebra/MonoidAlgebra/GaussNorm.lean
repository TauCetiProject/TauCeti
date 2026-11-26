/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
# The Gauss norm on a monoid algebra

For a function `v : R → ℝ`, the *Gauss norm* of `f ∈ R[M]` is the largest value of `v` on the
coefficients of `f`. For `v` a nonarchimedean absolute value on a field `K` and `M` the character
lattice of a torus, or the character monoid `σ^∨ ∩ M` of a toric cone, this is the coefficient
norm whose completion is the algebra of functions on the unit polydisc, the unit torus, or the
affinoid toric chart; with `M ⊆ ℚ ⊗ M` a monoid of `p`-power-divisible characters it is the norm
of the perfected charts.

The norm is ultrametric when `v` is, and submultiplicative when `v` is ultrametric and
submultiplicative, for an arbitrary exponent magma `M`. When `v` is a nonarchimedean absolute value
and `M` has unique sums (for instance a torsion-free cancellative commutative monoid, a submonoid
of one, or a linearly ordered cancellative monoid), it is multiplicative: the largest
coefficients of `f` and `g` sit on finite sets `A` and `B`, a sum `a₀ + b₀` with `a₀ ∈ A`,
`b₀ ∈ B` that arises in only one way from `A` and `B` has coefficient `f a₀ * g b₀` up to
strictly smaller terms, and the ultrametric inequality keeps those terms from cancelling it.
Without unique sums multiplicativity fails: in `R[ℤ/2]`, `(1 + χ) * (1 - χ) = 0`.

Reindexing the exponents along an injective map, and changing coefficients along a map that
preserves `v`, preserve the Gauss norm. For `M = ℕ` this is the Gauss norm of radius one of
Mathlib's `Polynomial.gaussNorm`, and for `M = σ →₀ ℕ` it is the Gauss norm of multivariate
polynomials. The definition and the layout of its API follow Mathlib's `Polynomial.gaussNorm`
(`Mathlib/RingTheory/Polynomial/GaussNorm.lean`).

## Main declarations

* `AddMonoidAlgebra.gaussNorm`: the largest value of `v` on the coefficients.
* `AddMonoidAlgebra.gaussNorm_le_iff`, `AddMonoidAlgebra.gaussNorm_lt_iff`: comparison with a
  bound is coefficientwise.
* `AddMonoidAlgebra.isNonarchimedean_gaussNorm`: the Gauss norm is ultrametric.
* `AddMonoidAlgebra.gaussNorm_mul_le`: the Gauss norm is submultiplicative.
* `AddMonoidAlgebra.gaussNorm_mul`: for a nonarchimedean absolute value `v` and exponents with
  unique sums, the Gauss norm is multiplicative.
* `AddMonoidAlgebra.gaussNorm_isAbsoluteValue`: for a nonarchimedean absolute value `v` and
  exponents with unique sums, the Gauss norm is an absolute value.
* `AddMonoidAlgebra.gaussNorm_mapDomain`, `AddMonoidAlgebra.gaussNorm_map`: invariance under
  injective reindexing of exponents and isometric coefficient change.
* `Polynomial.gaussNorm_one_right`: agreement with `Polynomial.gaussNorm` at radius one.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.2 (Gauss's lemma for
  the Gauss norm on polynomial rings).
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8 (the toric charts
  `K⟨σ^∨ ∩ M⟩` with their coefficient norm).
-/

public section

namespace AddMonoidAlgebra

open Finset

variable {R S M N F G : Type*}

section Semiring

variable [Semiring R] [FunLike F R ℝ] (v : F)

/-- The *Gauss norm* of `f ∈ R[M]` with respect to `v : R → ℝ`: the largest value of `v` on the
coefficients of `f`, and `0` for `f = 0`. -/
noncomputable def gaussNorm (f : R[M]) : ℝ :=
  if h : f.coeff.support.Nonempty then f.coeff.support.sup' h fun m ↦ v (f.coeff m) else 0

@[simp]
theorem gaussNorm_zero : gaussNorm v (0 : R[M]) = 0 := by
  simp [gaussNorm]

variable [ZeroHomClass F R ℝ]

omit [ZeroHomClass F R ℝ] in
/-- The Gauss norm of a nonzero element is attained at a coefficient in its support. -/
theorem exists_mem_support_eq_gaussNorm {f : R[M]} (hf : f ≠ 0) :
    ∃ m ∈ f.coeff.support, gaussNorm v f = v (f.coeff m) := by
  have h : f.coeff.support.Nonempty := by simpa using hf
  obtain ⟨m, hm, hm'⟩ := exists_mem_eq_sup' h fun m ↦ v (f.coeff m)
  exact ⟨m, hm, by simp only [gaussNorm, h, ↓reduceDIte, hm']⟩

/-- The Gauss norm is attained at some coefficient. -/
theorem exists_eq_gaussNorm [Nonempty M] (f : R[M]) : ∃ m, gaussNorm v f = v (f.coeff m) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨Classical.arbitrary M, by simp⟩
  · obtain ⟨m, -, hm⟩ := exists_mem_support_eq_gaussNorm v hf
    exact ⟨m, hm⟩

@[simp]
theorem gaussNorm_single (m : M) (r : R) : gaussNorm v (single m r) = v r := by
  by_cases hr : r = 0
  · simp [hr]
  · simp [gaussNorm, coeff_single, Finsupp.support_single, hr]

@[simp]
theorem gaussNorm_one [Zero M] : gaussNorm v (1 : R[M]) = v 1 :=
  gaussNorm_single v 0 1

variable [NonnegHomClass F R ℝ]

omit [ZeroHomClass F R ℝ] in
/-- The Gauss norm of a nonnegative function is nonnegative. -/
theorem gaussNorm_nonneg (f : R[M]) : 0 ≤ gaussNorm v f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · obtain ⟨m, -, hm⟩ := exists_mem_support_eq_gaussNorm v hf
    exact hm ▸ apply_nonneg v _

/-- Every coefficient is bounded by the Gauss norm. -/
theorem le_gaussNorm (f : R[M]) (m : M) : v (f.coeff m) ≤ gaussNorm v f := by
  by_cases hm : m ∈ f.coeff.support
  · have h : f.coeff.support.Nonempty := ⟨m, hm⟩
    simp only [gaussNorm, h, ↓reduceDIte]
    exact le_sup' (fun m ↦ v (f.coeff m)) hm
  · rw [Finsupp.notMem_support_iff.1 hm, map_zero]
    exact gaussNorm_nonneg v f

/-- The Gauss norm is the least common bound of the values of `v` on the coefficients. -/
theorem gaussNorm_le_iff {f : R[M]} {r : ℝ} (hr : 0 ≤ r) :
    gaussNorm v f ≤ r ↔ ∀ m, v (f.coeff m) ≤ r := by
  refine ⟨fun h m ↦ (le_gaussNorm v f m).trans h, fun h ↦ ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · simpa using hr
  · obtain ⟨m, -, hm⟩ := exists_mem_support_eq_gaussNorm v hf
    exact hm ▸ h m

/-- The Gauss norm is below a positive bound exactly when every coefficient is. -/
theorem gaussNorm_lt_iff {f : R[M]} {r : ℝ} (hr : 0 < r) :
    gaussNorm v f < r ↔ ∀ m, v (f.coeff m) < r := by
  refine ⟨fun h m ↦ (le_gaussNorm v f m).trans_lt h, fun h ↦ ?_⟩
  rcases eq_or_ne f 0 with rfl | hf
  · simpa using hr
  · obtain ⟨m, -, hm⟩ := exists_mem_support_eq_gaussNorm v hf
    exact hm ▸ h m

/-- Discarding coefficients does not increase the Gauss norm. -/
theorem gaussNorm_ofCoeff_filter_le (f : R[M]) (p : M → Prop) [DecidablePred p] :
    gaussNorm v (ofCoeff (f.coeff.filter p)) ≤ gaussNorm v f :=
  (gaussNorm_le_iff v (gaussNorm_nonneg v f)).2 fun m ↦ by
    rw [coeff_ofCoeff, Finsupp.filter_apply]
    split_ifs
    · exact le_gaussNorm v f m
    · simpa using gaussNorm_nonneg v f

/-- If `v` vanishes only at `0`, so does the Gauss norm. -/
@[simp]
theorem gaussNorm_eq_zero_iff (h : ∀ x : R, v x = 0 → x = 0) {f : R[M]} :
    gaussNorm v f = 0 ↔ f = 0 := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf ▸ gaussNorm_zero v⟩
  rw [← coeff_eq_zero]
  ext m
  exact h _ <| le_antisymm (hf ▸ le_gaussNorm v f m) (apply_nonneg v _)

/-- The Gauss norm is ultrametric when `v` is. -/
theorem isNonarchimedean_gaussNorm (hna : IsNonarchimedean v) :
    IsNonarchimedean (gaussNorm v : R[M] → ℝ) := fun f g ↦
  (gaussNorm_le_iff v (le_max_of_le_left (gaussNorm_nonneg v f))).2 fun m ↦ by
    rw [coeff_add, Finsupp.add_apply]
    exact (hna _ _).trans (max_le_max (le_gaussNorm v f m) (le_gaussNorm v g m))

/-- The Gauss norm is submultiplicative when `v` is ultrametric and submultiplicative. -/
theorem gaussNorm_mul_le [Add M] (hna : IsNonarchimedean v)
    (hmul : ∀ x y, v (x * y) ≤ v x * v y) (f g : R[M]) :
    gaussNorm v (f * g) ≤ gaussNorm v f * gaussNorm v g := by
  classical
  have hfg := mul_nonneg (gaussNorm_nonneg v f) (gaussNorm_nonneg v g)
  refine (gaussNorm_le_iff v hfg).2 fun m ↦ ?_
  rw [coeff_mul]
  simp only [Finsupp.sum]
  -- The coefficient is a double sum of products `f a * g b`, each bounded by the product norm.
  have hsum (s : Finset M) (x : M → R) (hx : ∀ i, v (x i) ≤ gaussNorm v f * gaussNorm v g) :
      v (∑ i ∈ s, x i) ≤ gaussNorm v f * gaussNorm v g := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hfg
    · obtain ⟨i, -, hi⟩ := hna.finset_image_add_of_nonempty x hs
      exact hi.trans (hx i)
  refine hsum _ _ fun a ↦ hsum _ _ fun b ↦ ?_
  split_ifs
  · exact (hmul _ _).trans <| mul_le_mul (le_gaussNorm v f a) (le_gaussNorm v g b)
      (apply_nonneg v _) (gaussNorm_nonneg v f)
  · simpa using hfg

end Semiring

section Multiplicative

variable [Ring R] {v : AbsoluteValue R ℝ}

/-- Discarding the coefficients at which `v` attains the Gauss norm lowers the Gauss norm. -/
private theorem gaussNorm_filter_lt (f : R[M]) (hf : 0 < gaussNorm v f) :
    gaussNorm v (ofCoeff (f.coeff.filter fun m ↦ v (f.coeff m) ≠ gaussNorm v f)) <
      gaussNorm v f :=
  (gaussNorm_lt_iff v hf).2 fun m ↦ by
    rw [coeff_ofCoeff, Finsupp.filter_apply]
    split_ifs with h
    · exact lt_of_le_of_ne (le_gaussNorm v f m) h
    · simpa using hf

/-- If `f` has positive Gauss norm, some coefficient of `f` attains it. -/
private theorem nonempty_support_filter_eq_gaussNorm (f : R[M]) (hf : 0 < gaussNorm v f) :
    (f.coeff.filter fun m ↦ v (f.coeff m) = gaussNorm v f).support.Nonempty := by
  obtain ⟨m, -, hm⟩ := exists_mem_support_eq_gaussNorm v (fun h ↦ hf.ne' (by simp [h]) : f ≠ 0)
  refine ⟨m, ?_⟩
  simp only [Finsupp.support_filter, mem_filter, Finsupp.mem_support_iff]
  exact ⟨fun h ↦ hf.ne' (by rw [hm, h, map_zero]), hm.symm⟩

/-- For a nonarchimedean absolute value `v` and exponents with unique sums, the Gauss norm is
multiplicative. -/
theorem gaussNorm_mul [Add M] [UniqueSums M] (hna : IsNonarchimedean v) (f g : R[M]) :
    gaussNorm v (f * g) = gaussNorm v f * gaussNorm v g := by
  classical
  have hmul (x y : R) : v (x * y) ≤ v x * v y := (map_mul v x y).le
  refine (gaussNorm_mul_le v hna hmul f g).antisymm ?_
  rcases (gaussNorm_nonneg v f).eq_or_lt with hf | hf
  · simp [← hf, gaussNorm_nonneg]
  rcases (gaussNorm_nonneg v g).eq_or_lt with hg | hg
  · simp [← hg, gaussNorm_nonneg]
  -- Split `f = f₁ + f₂` and `g = g₁ + g₂`, where `f₁` and `g₁` carry the coefficients at which
  -- the Gauss norm is attained, and `f₂` and `g₂` have strictly smaller Gauss norm.
  set f₁ := ofCoeff (f.coeff.filter fun m ↦ v (f.coeff m) = gaussNorm v f)
  set f₂ := ofCoeff (f.coeff.filter fun m ↦ v (f.coeff m) ≠ gaussNorm v f)
  set g₁ := ofCoeff (g.coeff.filter fun m ↦ v (g.coeff m) = gaussNorm v g)
  set g₂ := ofCoeff (g.coeff.filter fun m ↦ v (g.coeff m) ≠ gaussNorm v g)
  have hf₁₂ : f = f₁ + f₂ := by
    rw [← ofCoeff_add, Finsupp.filter_add_filter_not, ofCoeff_coeff]
  have hg₁₂ : g = g₁ + g₂ := by
    rw [← ofCoeff_add, Finsupp.filter_add_filter_not, ofCoeff_coeff]
  obtain ⟨a, ha, b, hb, huniq⟩ := UniqueSums.uniqueAdd_of_nonempty
    (nonempty_support_filter_eq_gaussNorm f hf) (nonempty_support_filter_eq_gaussNorm g hg)
  simp only [Finsupp.support_filter, mem_filter] at ha hb
  -- At `a + b`, the product `f₁ * g₁` has the single term `f a * g b`, of value `‖f‖ * ‖g‖`.
  have hmain : v ((f₁ * g₁).coeff (a + b)) = gaussNorm v f * gaussNorm v g := by
    rw [coeff_mul_add_of_uniqueAdd (f := f₁) (g := g₁) huniq, map_mul]
    simp [f₁, g₁, ha.2, hb.2]
  -- The remaining terms of `f * g` have strictly smaller Gauss norm.
  have hrest : gaussNorm v (f₁ * g₂ + f₂ * g) < gaussNorm v f * gaussNorm v g := by
    refine (isNonarchimedean_gaussNorm v hna _ _).trans_lt (max_lt ?_ ?_)
    · calc gaussNorm v (f₁ * g₂) ≤ gaussNorm v f₁ * gaussNorm v g₂ :=
            gaussNorm_mul_le v hna hmul _ _
        _ ≤ gaussNorm v f * gaussNorm v g₂ :=
            mul_le_mul_of_nonneg_right (gaussNorm_ofCoeff_filter_le v f _) (gaussNorm_nonneg v _)
        _ < gaussNorm v f * gaussNorm v g := mul_lt_mul_of_pos_left (gaussNorm_filter_lt g hg) hf
    · calc gaussNorm v (f₂ * g) ≤ gaussNorm v f₂ * gaussNorm v g :=
            gaussNorm_mul_le v hna hmul _ _
        _ < gaussNorm v f * gaussNorm v g := mul_lt_mul_of_pos_right (gaussNorm_filter_lt f hf) hg
  have hsplit : f * g = f₁ * g₁ + (f₁ * g₂ + f₂ * g) := by
    calc f * g = (f₁ + f₂) * g := by rw [← hf₁₂]
      _ = f₁ * (g₁ + g₂) + f₂ * g := by rw [add_mul, ← hg₁₂]
      _ = f₁ * g₁ + (f₁ * g₂ + f₂ * g) := by rw [mul_add, add_assoc]
  calc gaussNorm v f * gaussNorm v g = v ((f * g).coeff (a + b)) := by
        rw [hsplit, coeff_add, Finsupp.add_apply,
          hna.add_eq_left_of_lt v.map_neg
            (lt_of_le_of_lt (le_gaussNorm v _ _) (hmain ▸ hrest)), hmain]
    _ ≤ gaussNorm v (f * g) := le_gaussNorm v _ _

/-- For a nonarchimedean absolute value `v` and exponents with unique sums, the Gauss norm is an
absolute value on `R[M]`. -/
theorem gaussNorm_isAbsoluteValue [AddMonoid M] [UniqueSums M]
    (hna : IsNonarchimedean v) : IsAbsoluteValue (gaussNorm v : R[M] → ℝ) where
  abv_nonneg' := gaussNorm_nonneg v
  abv_eq_zero' := gaussNorm_eq_zero_iff v fun _ ↦ v.eq_zero.1
  abv_add' f g := (isNonarchimedean_gaussNorm v hna f g).trans <|
    max_le_add_of_nonneg (gaussNorm_nonneg v f) (gaussNorm_nonneg v g)
  abv_mul' := gaussNorm_mul hna

end Multiplicative

section Change

variable [Semiring R] [Semiring S] [FunLike F R ℝ] [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
  (v : F)

/-- Reindexing the exponents along an injective map preserves the Gauss norm. -/
@[simp]
theorem gaussNorm_mapDomain {e : M → N} (he : e.Injective) (f : R[M]) :
    gaussNorm v (mapDomain e f) = gaussNorm v f := by
  classical
  refine le_antisymm ((gaussNorm_le_iff v (gaussNorm_nonneg v f)).2 fun n ↦ ?_)
    ((gaussNorm_le_iff v (gaussNorm_nonneg v _)).2 fun m ↦ ?_)
  · by_cases hn : n ∈ Set.range e
    · obtain ⟨m, rfl⟩ := hn
      rw [coeff_mapDomain, Finsupp.mapDomain_apply_of_injective he]
      exact le_gaussNorm v f m
    · rw [coeff_mapDomain, Finsupp.mapDomain_of_notMem_range _ _ hn, map_zero]
      exact gaussNorm_nonneg v f
  · rw [← Finsupp.mapDomain_apply_of_injective he f.coeff m, ← coeff_mapDomain]
    exact le_gaussNorm v _ _

variable [FunLike G S ℝ] [ZeroHomClass G S ℝ] [NonnegHomClass G S ℝ] {v}

/-- Changing coefficients along an additive map `φ` with `w ∘ φ = v` preserves the Gauss norm. -/
theorem gaussNorm_map {w : G} {φ : R →+ S} (h : ∀ x, w (φ x) = v x) (f : R[M]) :
    gaussNorm w (map φ f) = gaussNorm v f := by
  refine le_antisymm ((gaussNorm_le_iff w (gaussNorm_nonneg v f)).2 fun m ↦ ?_)
    ((gaussNorm_le_iff v (gaussNorm_nonneg w _)).2 fun m ↦ ?_)
  · rw [coeff_map, Finsupp.mapRange_apply, h]
    exact le_gaussNorm v f m
  · rw [← h, ← Finsupp.mapRange_apply (hf := φ.map_zero), ← coeff_map]
    exact le_gaussNorm w _ m

end Change

end AddMonoidAlgebra

namespace Polynomial

/-- The Gauss norm of radius one of a polynomial is its Gauss norm as an element of `R[ℕ]`. -/
theorem gaussNorm_one_right {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (p : R[X]) :
    p.gaussNorm v 1 = AddMonoidAlgebra.gaussNorm v p := by
  simp [AddMonoidAlgebra.gaussNorm, gaussNorm, support]

end Polynomial
