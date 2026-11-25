/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.Analysis.Polynomial.Order
public import TauCeti.Geometry.Manifold.Instances.OnePoint.LineBundle.Sections
import TauCeti.Algebra.Polynomial.Roots
import TauCeti.RingTheory.Polynomial.DegreeLT

/-!
# Zeros and point evaluations of holomorphic sections of `𝒪(n)`

A nonzero holomorphic section of the line bundle `𝒪(n)` on the Riemann sphere `OnePoint ℂ` has
exactly `n` zeros, counted with multiplicity. Consequently a holomorphic section of `𝒪(n)` is
determined by its values at any `n + 1` distinct points, and evaluation at `n + 1` distinct points
is an isomorphism `H⁰(𝒪(n)) ≃ ℂⁿ⁺¹`. The holomorphic sections are the kernel of the standard
Cauchy–Riemann operator on `𝒪(n)`, and this is the zero-count argument for that kernel: zero
counting makes evaluation at `n + 1` distinct points injective, and the dimension `n + 1` of
`H⁰(𝒪(n))` makes it an isomorphism. In particular evaluation at a single point is onto for
`n ≥ 0`.

The **order of vanishing** `OnePoint.twistOrderAt k s x` of a section `s` of `𝒪(k)` at a point `x`
is read in the trivialization of `OnePoint.twistCore k` at `x`: at a finite point `z` it is the
analytic order at `z` of the affine coordinate `z ↦ s z`, and at `∞` the analytic order at `0` of
the inverted coordinate `OnePoint.twistInvCoeff k s`. It is `⊤` for the zero section, and finite
for every nonzero holomorphic section (`OnePoint.twistOrderAt_eq_top_iff`). Both charts
give the same order at the finite points other than `0`
(`OnePoint.twistOrderAt_coe_eq_analyticOrderAt_twistInvCoeff`), and for a holomorphic section the
order vanishes exactly where the section does not (`OnePoint.twistOrderAt_eq_zero_iff`).

For the polynomial section of `p ≠ 0` of degree at most `n`, the order at a finite point `z` is the
root multiplicity of `p` at `z`, and the order at `∞` is `n - p.natDegree`, the root multiplicity
at `0` of the reflected polynomial `wⁿ p(w⁻¹)`. Since `p` splits over `ℂ`, its root multiplicities
add up to its degree, which gives the zero count
`∑ᶠ x, twistOrderAt n s x = n` (`OnePoint.finsum_twistOrderAt_eq`) for every nonzero holomorphic
section `s` of `𝒪(n)`. In particular a nonzero holomorphic section has at most `n` zeros
(`OnePoint.ncard_setOf_eq_zero_le_of_mem_holomorphicTwistSections`).

For points `x : ι → OnePoint ℂ`, the evaluation map
`OnePoint.holomorphicTwistSectionsEval k x : H⁰(𝒪(k)) → (ι → ℂ)` sends `s` to `i ↦ s (x i)`.
For distinct points it is injective when there are at least `n + 1` of them
(`OnePoint.holomorphicTwistSectionsEval_injective`) and surjective when there are at most `n + 1`
(`OnePoint.holomorphicTwistSectionsEval_surjective`), so for exactly `n + 1` distinct points it is
a linear isomorphism (`OnePoint.holomorphicTwistSectionsEvalEquiv`).

## Main definitions

* `OnePoint.twistOrderAt k s x`: the order of vanishing of a section `s` of `𝒪(k)` at `x`.
* `OnePoint.holomorphicTwistSectionsEval k x`: evaluation of holomorphic sections of `𝒪(k)` at
  the points `x i`.
* `OnePoint.holomorphicTwistSectionsEvalEquiv`: for `n + 1` distinct points, the isomorphism
  `H⁰(𝒪(n)) ≃ ℂⁿ⁺¹` given by evaluation.

## Main results

* `OnePoint.twistOrderAt_polynomialSection_coe`, `OnePoint.twistOrderAt_polynomialSection_infty`:
  the orders of a polynomial section are the root multiplicities of the polynomial, and the
  degree drop at `∞`.
* `OnePoint.finsum_twistOrderAt_eq`: a nonzero holomorphic section of `𝒪(n)` has `n` zeros,
  counted with multiplicity.
* `OnePoint.ncard_setOf_eq_zero_le_of_mem_holomorphicTwistSections`: a nonzero holomorphic section
  of `𝒪(n)` vanishes at no more than `n` points.
* `OnePoint.holomorphicTwistSectionsEval_bijective`: evaluation at `n + 1` distinct points is
  bijective.
* `OnePoint.exists_mem_holomorphicTwistSections_apply_eq`: every value at every point is attained
  by a holomorphic section of `𝒪(n)`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §16 and §29.
* Dusa McDuff and Dietmar Salamon, *J-holomorphic Curves and Symplectic Topology*, second
  edition, AMS Colloquium Publications 52, 2012, Appendix C.
-/

public section

open Function Polynomial Set

noncomputable section

namespace OnePoint

/-- A nonzero holomorphic section of `𝒪(n)` is the polynomial section of a nonzero polynomial of
degree at most `n`. -/
private theorem exists_polynomialSection_eq {n : ℕ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections n) (hs0 : s ≠ 0) :
    ∃ p ∈ degreeLT ℂ (n + 1), p ≠ 0 ∧ polynomialSection n p = s := by
  rw [holomorphicTwistSections_natCast_eq_map] at hs
  obtain ⟨p, hp, rfl⟩ := hs
  exact ⟨p, hp, by rintro rfl; simp at hs0, rfl⟩

/-- A holomorphic section of `𝒪(k)` is either zero, or `k = n ≥ 0` and the section is the
polynomial section of a nonzero polynomial of degree at most `n`. -/
private theorem eq_zero_or_exists_polynomialSection_eq {k : ℤ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections k) :
    s = 0 ∨ ∃ n : ℕ, k = n ∧ ∃ p ∈ degreeLT ℂ (n + 1), p ≠ 0 ∧ polynomialSection n p = s := by
  rcases eq_or_ne s 0 with hs0 | hs0
  · exact .inl hs0
  rcases lt_or_ge k 0 with hk | hk
  · rw [holomorphicTwistSections_eq_bot hk, Submodule.mem_bot] at hs
    exact absurd hs hs0
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  exact .inr ⟨n, rfl, exists_polynomialSection_eq hs hs0⟩

/-! ### The order of vanishing of a section -/

/-- The **order of vanishing** of a section `s` of `𝒪(k)` at a point `x` of the Riemann sphere, read
in the trivialization of `𝒪(k)` at `x`: at a finite point `z` the analytic order at `z` of the
affine coordinate `z ↦ s z`, and at `∞` the analytic order at `0` of the inverted coordinate
`OnePoint.twistInvCoeff k s`. It is `⊤` exactly when `s` vanishes near `x`, and, following the
convention of `analyticOrderAt`, it is `0` where that coordinate is not analytic. -/
def twistOrderAt (k : ℤ) (s : OnePoint ℂ → ℂ) (x : OnePoint ℂ) : ℕ∞ :=
  x.elim (analyticOrderAt (twistInvCoeff k s) 0) (analyticOrderAt fun z : ℂ ↦ s z)

@[simp]
theorem twistOrderAt_coe (k : ℤ) (s : OnePoint ℂ → ℂ) (z : ℂ) :
    twistOrderAt k s z = analyticOrderAt (fun w : ℂ ↦ s w) z :=
  (rfl)

@[simp]
theorem twistOrderAt_infty (k : ℤ) (s : OnePoint ℂ → ℂ) :
    twistOrderAt k s ∞ = analyticOrderAt (twistInvCoeff k s) 0 :=
  (rfl)

/-- The order of vanishing of the zero section is `⊤` everywhere. -/
@[simp]
theorem twistOrderAt_zero (k : ℤ) (x : OnePoint ℂ) : twistOrderAt k 0 x = ⊤ := by
  induction x using OnePoint.rec with
  | infty => simp
  | coe z => simp

/-- A holomorphic section of `𝒪(k)` vanishes to order `0` exactly at the points where it does not
vanish. -/
theorem twistOrderAt_eq_zero_iff {k : ℤ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections k) (x : OnePoint ℂ) :
    twistOrderAt k s x = 0 ↔ s x ≠ 0 := by
  obtain rfl | ⟨n, rfl, p, hp, -, rfl⟩ := eq_zero_or_exists_polynomialSection_eq hs
  · simp
  -- Both coordinates of a polynomial section are polynomial functions, hence analytic.
  induction x using OnePoint.rec with
  | infty =>
    rw [twistOrderAt_infty, ← twistInvCoeff_zero (n : ℤ) (polynomialSection n p),
      twistInvCoeff_polynomialSection hp]
    exact ((AnalyticOnNhd.eval_polynomial (reflect n p)) 0 (mem_univ _)).analyticOrderAt_eq_zero
  | coe z =>
    simp only [twistOrderAt_coe, polynomialSection_coe]
    exact ((AnalyticOnNhd.eval_polynomial p) z (mem_univ _)).analyticOrderAt_eq_zero

/-- A holomorphic section of `𝒪(k)` has positive order of vanishing exactly at its zeros. -/
theorem twistOrderAt_ne_zero_iff {k : ℤ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections k) (x : OnePoint ℂ) :
    twistOrderAt k s x ≠ 0 ↔ s x = 0 := by
  rw [ne_eq, twistOrderAt_eq_zero_iff hs, not_not]

/-! ### Polynomial sections -/

/-- At a finite point `z`, the order of vanishing of the polynomial section of `p ≠ 0` is the root
multiplicity of `p` at `z`. -/
theorem twistOrderAt_polynomialSection_coe (n : ℕ) {p : ℂ[X]} (hp : p ≠ 0) (z : ℂ) :
    twistOrderAt n (polynomialSection n p) z = p.rootMultiplicity z := by
  simpa using analyticOrderAt_eval hp z

/-- At `∞`, the order of vanishing of the polynomial section of `p ≠ 0` of degree at most `n` is
the degree drop `n - p.natDegree`. -/
theorem twistOrderAt_polynomialSection_infty {n : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (n + 1))
    (hp0 : p ≠ 0) : twistOrderAt n (polynomialSection n p) ∞ = (n - p.natDegree : ℕ) := by
  rw [twistOrderAt_infty, twistInvCoeff_polynomialSection hp,
    analyticOrderAt_eval (reflect_eq_zero_iff.not.2 hp0),
    rootMultiplicity_reflect_zero p hp0 (mem_degreeLT_succ_iff_natDegree_le.1 hp)]

/-- A holomorphic section of `𝒪(k)` vanishes to infinite order at a point only if it is the zero
section. -/
theorem twistOrderAt_eq_top_iff {k : ℤ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections k) (x : OnePoint ℂ) :
    twistOrderAt k s x = ⊤ ↔ s = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ twistOrderAt_zero k x⟩
  obtain hs0 | ⟨n, rfl, p, hp, hp0, rfl⟩ := eq_zero_or_exists_polynomialSection_eq hs
  · exact hs0
  induction x using OnePoint.rec with
  | infty => simp [twistOrderAt_polynomialSection_infty hp hp0] at h
  | coe z => simp [twistOrderAt_polynomialSection_coe n hp0] at h

/-- **The order of vanishing does not depend on the chart.** At a finite point `z ≠ 0`, the order
of vanishing of a holomorphic section of `𝒪(k)` may also be computed from its inverted coordinate
at `z⁻¹`. -/
theorem twistOrderAt_coe_eq_analyticOrderAt_twistInvCoeff {k : ℤ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections k) {z : ℂ} (hz : z ≠ 0) :
    twistOrderAt k s z = analyticOrderAt (twistInvCoeff k s) z⁻¹ := by
  obtain rfl | ⟨n, rfl, p, hp, hp0, rfl⟩ := eq_zero_or_exists_polynomialSection_eq hs
  · simp
  rw [twistOrderAt_polynomialSection_coe n hp0, twistInvCoeff_polynomialSection hp,
    analyticOrderAt_eval (reflect_eq_zero_iff.not.2 hp0),
    rootMultiplicity_reflect_eq_inv p (mem_degreeLT_succ_iff_natDegree_le.1 hp) (inv_ne_zero hz),
    inv_inv]

/-! ### The zero count -/

/-- The finite set of points of the Riemann sphere consisting of `∞` and the roots of `p`. -/
private def rootsAndInfty (p : ℂ[X]) : Finset (OnePoint ℂ) :=
  Finset.cons ∞ (p.roots.toFinset.map ⟨((↑) : ℂ → OnePoint ℂ), coe_injective⟩) (by simp)

/-- The orders of vanishing of the polynomial section of a nonzero polynomial `p` of degree at
most `n` are supported on `∞` and the roots of `p`, and add up to `n`. -/
private theorem support_twistOrderAt_polynomialSection_subset_and_sum_eq {n : ℕ} {p : ℂ[X]}
    (hp : p ∈ degreeLT ℂ (n + 1)) (hp0 : p ≠ 0) :
    support (twistOrderAt n (polynomialSection n p)) ⊆ rootsAndInfty p ∧
      ∑ x ∈ rootsAndInfty p, twistOrderAt n (polynomialSection n p) x = n := by
  refine ⟨fun x hx ↦ ?_, ?_⟩
  · induction x using OnePoint.rec with
    | infty => simp [rootsAndInfty]
    | coe z =>
      rw [mem_support, twistOrderAt_polynomialSection_coe n hp0, ne_eq, Nat.cast_eq_zero,
        rootMultiplicity_eq_zero_iff, not_imp] at hx
      simpa [rootsAndInfty, hp0] using hx.1
  · rw [rootsAndInfty, Finset.sum_cons, Finset.sum_map, twistOrderAt_polynomialSection_infty hp hp0]
    simp only [Embedding.coeFn_mk, twistOrderAt_polynomialSection_coe n hp0]
    rw [← Nat.cast_sum, sum_rootMultiplicity_roots_toFinset_eq_card_roots,
      IsAlgClosed.card_roots_eq_natDegree, ← Nat.cast_add,
      Nat.sub_add_cancel (mem_degreeLT_succ_iff_natDegree_le.1 hp)]

/-- The zeros of a nonzero holomorphic section of `𝒪(n)` lie in a finite set on which its orders
of vanishing add up to `n`. -/
private theorem exists_finset_zeros_subset_and_sum_eq {n : ℕ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections n) (hs0 : s ≠ 0) :
    ∃ T : Finset (OnePoint ℂ), {x | s x = 0} ⊆ T ∧ ∑ x ∈ T, twistOrderAt n s x = n := by
  obtain ⟨p, hp, hp0, rfl⟩ := exists_polynomialSection_eq hs hs0
  obtain ⟨hsupp, hsum⟩ := support_twistOrderAt_polynomialSection_subset_and_sum_eq hp hp0
  exact ⟨rootsAndInfty p, fun x hx ↦ hsupp ((twistOrderAt_ne_zero_iff hs x).2 hx), hsum⟩

/-- **Zero count for `𝒪(n)`.** A nonzero holomorphic section of `𝒪(n)` on the Riemann sphere has
exactly `n` zeros, counted with multiplicity. -/
theorem finsum_twistOrderAt_eq {n : ℕ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections n) (hs0 : s ≠ 0) :
    ∑ᶠ x, twistOrderAt n s x = n := by
  obtain ⟨T, hT, hsum⟩ := exists_finset_zeros_subset_and_sum_eq hs hs0
  rw [finsum_eq_sum_of_support_subset _ fun x hx ↦ hT ((twistOrderAt_ne_zero_iff hs x).1 hx), hsum]

/-- The zeros of a nonzero holomorphic section of `𝒪(n)` form a finite set. -/
theorem finite_setOf_eq_zero_of_mem_holomorphicTwistSections {n : ℕ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections n) (hs0 : s ≠ 0) : {x | s x = 0}.Finite := by
  obtain ⟨T, hT, -⟩ := exists_finset_zeros_subset_and_sum_eq hs hs0
  exact T.finite_toSet.subset hT

/-- A nonzero holomorphic section of `𝒪(n)` vanishes at no more than `n` points. -/
theorem ncard_setOf_eq_zero_le_of_mem_holomorphicTwistSections {n : ℕ} {s : OnePoint ℂ → ℂ}
    (hs : s ∈ holomorphicTwistSections n) (hs0 : s ≠ 0) : {x | s x = 0}.ncard ≤ n := by
  classical
  obtain ⟨T, hT, hsum⟩ := exists_finset_zeros_subset_and_sum_eq hs hs0
  -- Each zero contributes at least `1` to the sum of the orders over `T`.
  have hZ : {x | s x = 0} = ↑(T.filter fun x ↦ s x = 0) := by
    ext x
    exact ⟨fun hx ↦ Finset.mem_filter.2 ⟨hT hx, hx⟩, fun hx ↦ (Finset.mem_filter.1 hx).2⟩
  rw [hZ, ncard_coe_finset, ← Nat.cast_le (α := ℕ∞), ← hsum, Finset.card_eq_sum_ones,
    Nat.cast_sum, Nat.cast_one, ← Finset.sum_filter_add_sum_filter_not T fun x ↦ s x = 0]
  refine le_add_right (Finset.sum_le_sum fun x hx ↦ ?_)
  exact Order.one_le_iff_ne_zero.2 ((twistOrderAt_ne_zero_iff hs x).2 (Finset.mem_filter.1 hx).2)

/-! ### Evaluation at points -/

variable {ι : Type*}

/-- Evaluation of the holomorphic sections of `𝒪(k)` at the points `x i`. -/
def holomorphicTwistSectionsEval (k : ℤ) (x : ι → OnePoint ℂ) :
    holomorphicTwistSections k →ₗ[ℂ] ι → ℂ :=
  LinearMap.funLeft ℂ ℂ x ∘ₗ (holomorphicTwistSections k).subtype

@[simp]
theorem holomorphicTwistSectionsEval_apply (k : ℤ) (x : ι → OnePoint ℂ)
    (s : holomorphicTwistSections k) (i : ι) :
    holomorphicTwistSectionsEval k x s i = (s : OnePoint ℂ → ℂ) (x i) :=
  (rfl)

/-- **Zero counting makes evaluation injective.** A holomorphic section of `𝒪(n)` is determined by
its values at any `n + 1` or more distinct points. -/
theorem holomorphicTwistSectionsEval_injective {n : ℕ} {x : ι → OnePoint ℂ}
    (hx : Injective x) (hcard : n + 1 ≤ ENat.card ι) :
    Injective (holomorphicTwistSectionsEval n x) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨s, hs⟩ hker
  by_contra hs0
  replace hs0 : s ≠ 0 := fun h ↦ hs0 (Subtype.ext h)
  have hsub : range x ⊆ {y | s y = 0} := by
    rintro _ ⟨i, rfl⟩
    exact congrFun hker i
  have hfin := finite_setOf_eq_zero_of_mem_holomorphicTwistSections hs hs0
  have h := encard_le_encard hsub
  rw [hx.encard_range, ← hfin.cast_ncard_eq] at h
  have := ncard_setOf_eq_zero_le_of_mem_holomorphicTwistSections hs hs0
  have := hcard.trans h
  norm_cast at this
  omega

/-- **Evaluation at `n + 1` distinct points is bijective.** -/
theorem holomorphicTwistSectionsEval_bijective [Finite ι] {n : ℕ} {x : ι → OnePoint ℂ}
    (hx : Injective x) (hcard : Nat.card ι = n + 1) :
    Bijective (holomorphicTwistSectionsEval n x) := by
  have hinj := holomorphicTwistSectionsEval_injective (n := n) hx
    (by rw [ENat.card_eq_coe_natCard, hcard, Nat.cast_add_one])
  have := Fintype.ofFinite ι
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj⟩
  rw [finrank_holomorphicTwistSections, Module.finrank_fintype_fun_eq_card,
    ← Nat.card_eq_fintype_card, hcard]

/-- **Evaluation at at most `n + 1` distinct points is onto.** Any values at no more than `n + 1`
distinct points of the Riemann sphere are those of a holomorphic section of `𝒪(n)`. -/
theorem holomorphicTwistSectionsEval_surjective [Finite ι] {n : ℕ} {x : ι → OnePoint ℂ}
    (hx : Injective x) (hcard : Nat.card ι ≤ n + 1) :
    Surjective (holomorphicTwistSectionsEval n x) := by
  classical
  have := Fintype.ofFinite ι
  -- Enlarge the set of points to a set `T` of exactly `n + 1` points, at which evaluation is
  -- bijective, and restrict from `T` to the given points.
  obtain ⟨T, hST, hT⟩ := Infinite.exists_superset_card_eq (Finset.univ.image x) (n + 1) (by
    rwa [Finset.card_image_of_injective _ hx, Finset.card_univ, ← Nat.card_eq_fintype_card])
  let e : ι → T := fun i ↦ ⟨x i, hST (Finset.mem_image_of_mem x (Finset.mem_univ i))⟩
  have he : Injective e := fun i j h ↦ hx (congrArg Subtype.val h)
  have hcomp : holomorphicTwistSectionsEval n x =
      LinearMap.funLeft ℂ ℂ e ∘ₗ holomorphicTwistSectionsEval n ((↑) : T → OnePoint ℂ) := by
    ext s i
    simp [LinearMap.funLeft_apply, e]
  rw [hcomp, LinearMap.coe_comp]
  exact (LinearMap.funLeft_surjective_of_injective _ _ e he).comp
    (holomorphicTwistSectionsEval_bijective Subtype.val_injective
      (by simp [hT])).2

/-- For `n + 1` distinct points, the **evaluation isomorphism** `H⁰(𝒪(n)) ≃ ℂⁿ⁺¹`. -/
def holomorphicTwistSectionsEvalEquiv [Finite ι] {n : ℕ} {x : ι → OnePoint ℂ}
    (hx : Injective x) (hcard : Nat.card ι = n + 1) :
    holomorphicTwistSections n ≃ₗ[ℂ] ι → ℂ :=
  LinearEquiv.ofBijective _ (holomorphicTwistSectionsEval_bijective hx hcard)

@[simp]
theorem holomorphicTwistSectionsEvalEquiv_apply [Finite ι] {n : ℕ} {x : ι → OnePoint ℂ}
    (hx : Injective x) (hcard : Nat.card ι = n + 1) (s : holomorphicTwistSections n) (i : ι) :
    holomorphicTwistSectionsEvalEquiv hx hcard s i = (s : OnePoint ℂ → ℂ) (x i) :=
  (rfl)

/-- **One-point evaluation is onto.** For `n ≥ 0`, every value at every point of the Riemann sphere
is attained by a holomorphic section of `𝒪(n)`. -/
theorem exists_mem_holomorphicTwistSections_apply_eq (n : ℕ) (x : OnePoint ℂ) (c : ℂ) :
    ∃ s ∈ holomorphicTwistSections n, s x = c := by
  obtain ⟨s, hs⟩ := holomorphicTwistSectionsEval_surjective (n := n) (x := fun _ : Unit ↦ x)
    (injective_of_subsingleton _) (by simp) fun _ ↦ c
  exact ⟨s, s.property, congrFun hs ()⟩

end OnePoint
