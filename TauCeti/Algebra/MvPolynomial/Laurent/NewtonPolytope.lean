/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Basic
public import TauCeti.Analysis.Convex.Gauge.Hull
public import TauCeti.Analysis.Convex.L1Ball
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.RingTheory.FilteredAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# The Newton polytope and the Newton filtration of a Laurent polynomial

Let `φ = ∑ a_m x^m` be a Laurent polynomial in the variables `K`, an element of
`TauCeti.LaurentRing R K`. Its exponents `m` are points of the lattice `ℤ^(K)`, which sits in the
real vector space `K → ℝ` through `TauCeti.LaurentRing.latticePoint`. The **Newton polytope at
the origin** is the lattice polytope
`Δ(φ) = conv({0} ∪ supp φ) ⊆ K → ℝ` (`TauCeti.LaurentRing.newtonPolytope`). It is a compact convex
set containing `0`, but `0` need not be an interior point, so `Δ(φ)` is in general not
absorbent.

The cone `C_Δ` over `Δ(φ)` is `ConvexCone.hull ℝ (newtonPolytope φ)`, and the **Newton height**
`h(m) = inf {a > 0 | m ∈ a Δ(φ)}` is the gauge `gauge (newtonPolytope φ)`, which is meaningful
on `C_Δ`. On `C_Δ` it is subadditive (`TauCeti.gauge_add_le_of_mem_hull`), positively
homogeneous (`gauge_smul_of_nonneg`), at most `1` on `Δ(φ)`, and its sublevel sets are the
dilates of the polytope: a point lies in `C_Δ` with height at most `a` exactly when `0 ≤ a` and it
lies in `a Δ(φ)` (`TauCeti.LaurentRing.mem_hull_newtonPolytope_and_gauge_le_iff`).

The **Newton filtration** `F_a`, for real `a`, is the span of the monomials `x^m` with `m ∈ C_Δ`
and `h(m) ≤ a` (`TauCeti.LaurentRing.newtonFiltration`). It is an increasing ring filtration
(`TauCeti.LaurentRing.newtonFiltration.isRingFiltration`): `F_a F_b ⊆ F_{a+b}`, because the
cone is closed under addition and the height is subadditive. It vanishes for `a < 0`, `F_0`
consists of the constants, `φ` itself lies in `F_1`, and the union of all `F_a` is the cone
algebra, spanned by the monomials with exponent in `C_Δ`.

The Newton filtration of the twisted de Rham complex `d + dφ ∧` of the torus, whose associated
graded complex Kouchnirenko's theorem computes, is built from this one: in degree `q` and index
`λ` it consists of the forms `∑_I f_I dlog x_I` with every `f_I ∈ F_{q-λ}`. That the
differential preserves it rests on `φ ∈ F_1` and `F_a F_b ⊆ F_{a+b}`, proved here, together with
the fact that the Euler derivations `x_i ∂/∂x_i` act diagonally on monomials.

For `φ = ∑ᵢ (x_i + x_i⁻¹)` with finitely many variables, the Newton polytope is the
cross-polytope `TauCeti.l1Ball K` (`TauCeti.LaurentRing.newtonPolytope_sum_X_add_inv`), the cone
is the whole space, and the Newton height of `m` is `∑ᵢ |m_i|`, so the Newton filtration is the
filtration by the ℓ¹ degree (`TauCeti.LaurentRing.mem_newtonFiltration_sum_X_add_inv_iff`).

## Main definitions

* `TauCeti.LaurentRing.latticePoint`: the inclusion of exponents `ℤ^(K) → (K → ℝ)`.
* `TauCeti.LaurentRing.newtonPolytope φ`: the Newton polytope `conv({0} ∪ supp φ)`.
* `TauCeti.LaurentRing.newtonFiltration φ a`: the span of the monomials `x^m` with `m` in the
  cone over the Newton polytope and of Newton height at most `a`.
* `TauCeti.LaurentRing.newtonFiltrationLT φ a`: the union `F_{<a}` of the `F_b` with `b < a`.

## Main results

* `TauCeti.LaurentRing.mem_hull_newtonPolytope_and_gauge_le_iff`: the sublevel sets of the
  Newton height on the cone are the dilates of the Newton polytope.
* `TauCeti.LaurentRing.mem_newtonFiltration_iff` and
  `TauCeti.LaurentRing.mem_newtonFiltration_iff_mem_smul`: membership in the Newton filtration,
  through the height and through the dilates of the polytope.
* `TauCeti.LaurentRing.mem_newtonFiltrationLT_iff`: membership in `F_{<a}`, through the strict
  sublevels of the height.
* `TauCeti.LaurentRing.mul_mem_newtonFiltration`: `F_a F_b ⊆ F_{a+b}`.
* `TauCeti.LaurentRing.newtonFiltration_eq_bot_of_neg`: `F_a = 0` for `a < 0`.
* `TauCeti.LaurentRing.self_mem_newtonFiltration_one`: `φ ∈ F_1`.
* `TauCeti.LaurentRing.newtonFiltration_zero`: `F_0` is spanned by `1`.
* `TauCeti.LaurentRing.iSup_newtonFiltration`: the filtration exhausts the cone algebra.
* `TauCeti.LaurentRing.newtonPolytope_sum_X_add_inv` and
  `TauCeti.LaurentRing.gauge_newtonPolytope_sum_X_add_inv`: the Newton polytope and the Newton
  height of `∑ᵢ (x_i + x_i⁻¹)`.

## References

* A. G. Kouchnirenko, *Polyèdres de Newton et nombres de Milnor*, Invent. Math. 32 (1976), §2.
* A. Adolphson and S. Sperber, *On twisted de Rham cohomology*, Nagoya Math. J. 146 (1997), for
  the Newton polytope at the origin, its cone and the weight function of a Laurent polynomial.
* J.-D. Yu, *Irregular Hodge filtration on twisted de Rham cohomology*, Manuscripta Math. 144
  (2014), §4(a), for the Newton filtration of the twisted de Rham complex of a torus.
-/

public section

open AddMonoidAlgebra
open scoped Pointwise

namespace TauCeti.LaurentRing

variable {R K : Type*}

/-- The point of `K → ℝ` underlying an exponent `m ∈ ℤ^(K)` of a Laurent monomial. -/
noncomputable def latticePoint : (K →₀ ℤ) →+ (K → ℝ) :=
  Finsupp.coeFnAddHom.comp (Finsupp.mapRange.addMonoidHom (Int.castAddHom ℝ))

@[simp]
theorem latticePoint_apply (m : K →₀ ℤ) (i : K) : latticePoint m i = m i := by
  simp [latticePoint]

theorem latticePoint_injective : Function.Injective (latticePoint (K := K)) := fun m m' h => by
  ext i
  simpa using congr_fun h i

/-- The lattice point of the exponent `n e_i` is `n e_i`. -/
@[simp]
theorem latticePoint_single [DecidableEq K] (i : K) (n : ℤ) :
    latticePoint (Finsupp.single i n) = Pi.single i (n : ℝ) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

@[simp]
theorem latticePoint_eq_zero_iff {m : K →₀ ℤ} : latticePoint m = 0 ↔ m = 0 :=
  latticePoint_injective.eq_iff' (map_zero _)

section Polytope

variable [Semiring R]

/-- The **Newton polytope at the origin** of a Laurent polynomial `φ`,
`Δ(φ) = conv({0} ∪ supp φ)`: the convex hull in `K → ℝ` of the origin and of the exponents of
the monomials occurring in `φ`. -/
noncomputable def newtonPolytope (φ : LaurentRing R K) : Set (K → ℝ) :=
  convexHull ℝ (insert 0 (latticePoint '' φ.coeff.support))

theorem newtonPolytope_def (φ : LaurentRing R K) :
    newtonPolytope φ = convexHull ℝ (insert 0 (latticePoint '' φ.coeff.support)) := (rfl)

theorem convex_newtonPolytope (φ : LaurentRing R K) : Convex ℝ (newtonPolytope φ) :=
  convex_convexHull ℝ _

theorem zero_mem_newtonPolytope (φ : LaurentRing R K) : (0 : K → ℝ) ∈ newtonPolytope φ :=
  subset_convexHull ℝ _ (Set.mem_insert _ _)

/-- Every exponent of `φ` lies in its Newton polytope. -/
theorem latticePoint_mem_newtonPolytope {φ : LaurentRing R K} {m : K →₀ ℤ}
    (hm : m ∈ φ.coeff.support) : latticePoint m ∈ newtonPolytope φ :=
  subset_convexHull ℝ _ (Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hm))

theorem isCompact_newtonPolytope (φ : LaurentRing R K) : IsCompact (newtonPolytope φ) :=
  ((φ.coeff.support.finite_toSet.image _).insert 0).isCompact_convexHull ℝ

theorem isClosed_newtonPolytope (φ : LaurentRing R K) : IsClosed (newtonPolytope φ) :=
  (isCompact_newtonPolytope φ).isClosed

@[simp]
theorem newtonPolytope_zero : newtonPolytope (0 : LaurentRing R K) = {0} := by
  simp [newtonPolytope_def]

/-- The Newton polytope of a monomial `r x^m` with `r ≠ 0` is the segment from `0` to `m`. -/
theorem newtonPolytope_single {m : K →₀ ℤ} {r : R} (hr : r ≠ 0) :
    newtonPolytope (single m r : LaurentRing R K) = segment ℝ 0 (latticePoint m) := by
  rw [newtonPolytope_def, coeff_single, Finsupp.support_single _ hr, Finset.coe_singleton,
    Set.image_singleton, convexHull_pair]

/-- On the cone over the Newton polytope, the sublevel sets of the Newton height
`gauge (newtonPolytope φ)` are the dilates of the polytope: a point lies in the cone and has
height at most `a` exactly when `0 ≤ a` and it lies in `a • newtonPolytope φ`. -/
theorem mem_hull_newtonPolytope_and_gauge_le_iff (φ : LaurentRing R K) {x : K → ℝ} {a : ℝ} :
    x ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧ gauge (newtonPolytope φ) x ≤ a ↔
      0 ≤ a ∧ x ∈ a • newtonPolytope φ :=
  mem_hull_and_gauge_le_iff (convex_newtonPolytope φ) (zero_mem_newtonPolytope φ)
    (isClosed_newtonPolytope φ) ((isCompact_newtonPolytope φ).isVonNBounded ℝ)

/-- The only point of the cone over the Newton polytope with Newton height `0` is the origin. -/
theorem eq_zero_of_mem_hull_newtonPolytope_of_gauge_le_zero {φ : LaurentRing R K} {x : K → ℝ}
    (hx : x ∈ ConvexCone.hull ℝ (newtonPolytope φ)) (h : gauge (newtonPolytope φ) x ≤ 0) :
    x = 0 := by
  have := ((mem_hull_newtonPolytope_and_gauge_le_iff φ).1 ⟨hx, h⟩).2
  rwa [Set.zero_smul_set ⟨0, zero_mem_newtonPolytope φ⟩, Set.mem_zero] at this

end Polytope

/-! ### The Newton filtration -/

section Filtration

variable [Semiring R]

/-- The **Newton filtration** of the Laurent ring attached to `φ`: for real `a`, the span of the
monomials `x^m` whose exponent `m` lies in the cone over the Newton polytope `Δ(φ)` and has Newton
height `gauge (newtonPolytope φ) m ≤ a`. -/
noncomputable def newtonFiltration (φ : LaurentRing R K) (a : ℝ) : Submodule R (LaurentRing R K) :=
  supported R R {m | latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧
    gauge (newtonPolytope φ) (latticePoint m) ≤ a}

theorem newtonFiltration_def (φ : LaurentRing R K) (a : ℝ) :
    newtonFiltration φ a = supported R R {m | latticePoint m ∈
      ConvexCone.hull ℝ (newtonPolytope φ) ∧ gauge (newtonPolytope φ) (latticePoint m) ≤ a} :=
  (rfl)

/-- The strict sublevels `F_{<a}` of the Newton filtration: the union of the `F_b` with `b < a`.
They form the second family of the `IsRingFiltration` instance, and `F_a / F_{<a}` is the
degree-`a` piece of the associated graded ring. -/
noncomputable def newtonFiltrationLT (φ : LaurentRing R K) (a : ℝ) :
    Submodule R (LaurentRing R K) :=
  ⨆ b < a, newtonFiltration φ b

theorem newtonFiltrationLT_def (φ : LaurentRing R K) (a : ℝ) :
    newtonFiltrationLT φ a = ⨆ b < a, newtonFiltration φ b := (rfl)

variable {φ f g : LaurentRing R K} {a b : ℝ}

/-- A Laurent polynomial lies in `F_a` exactly when each of its exponents lies in the cone over
the Newton polytope and has Newton height at most `a`. -/
theorem mem_newtonFiltration_iff :
    f ∈ newtonFiltration φ a ↔ ∀ m ∈ f.coeff.support,
      latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧
        gauge (newtonPolytope φ) (latticePoint m) ≤ a := by
  rw [newtonFiltration, mem_supported]
  exact ⟨fun h m hm => h hm, fun h m hm => h m hm⟩

/-- A Laurent polynomial lies in `F_a` exactly when each of its exponents `m` satisfies `0 ≤ a`
and lies in the dilate `a • Δ(φ)` of the Newton polytope. -/
theorem mem_newtonFiltration_iff_mem_smul :
    f ∈ newtonFiltration φ a ↔
      ∀ m ∈ f.coeff.support, 0 ≤ a ∧ latticePoint m ∈ a • newtonPolytope φ := by
  simp_rw [mem_newtonFiltration_iff, mem_hull_newtonPolytope_and_gauge_le_iff]

/-- A monomial `r x^m` with `r ≠ 0` lies in `F_a` exactly when `m` lies in the cone over the
Newton polytope and has Newton height at most `a`. -/
theorem single_mem_newtonFiltration_iff {m : K →₀ ℤ} {r : R} (hr : r ≠ 0) :
    single m r ∈ newtonFiltration φ a ↔
      latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧
        gauge (newtonPolytope φ) (latticePoint m) ≤ a := by
  simp [mem_newtonFiltration_iff, coeff_single, Finsupp.support_single _ hr]

/-- A Laurent polynomial lies in `F_{<a}` exactly when each of its exponents lies in the cone over
the Newton polytope and has Newton height less than `a`. -/
theorem mem_newtonFiltrationLT_iff :
    f ∈ newtonFiltrationLT φ a ↔ ∀ m ∈ f.coeff.support,
      latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ) ∧
        gauge (newtonPolytope φ) (latticePoint m) < a := by
  refine ⟨fun hf => ?_, fun h => ?_⟩
  · have hle : newtonFiltrationLT φ a ≤ supported R R {m | latticePoint m ∈
        ConvexCone.hull ℝ (newtonPolytope φ) ∧ gauge (newtonPolytope φ) (latticePoint m) < a} :=
      iSup₂_le fun b hb => supported_mono fun _ hm => ⟨hm.1, hm.2.trans_lt hb⟩
    exact fun m hm => mem_supported.1 (hle hf) hm
  · -- the support is finite, so the largest height `b` of an exponent is still less than `a`
    rw [newtonFiltrationLT_def]
    rcases f.coeff.support.eq_empty_or_nonempty with h₀ | hne
    · refine Submodule.mem_iSup_of_mem (a - 1) (Submodule.mem_iSup_of_mem (by linarith) ?_)
      simp [mem_newtonFiltration_iff, h₀]
    · let b := f.coeff.support.sup' hne fun m => gauge (newtonPolytope φ) (latticePoint m)
      refine Submodule.mem_iSup_of_mem b (Submodule.mem_iSup_of_mem
        ((Finset.sup'_lt_iff hne).2 fun m hm => (h m hm).2) ?_)
      exact mem_newtonFiltration_iff.2 fun m hm =>
        ⟨(h m hm).1, Finset.le_sup' (fun m => gauge (newtonPolytope φ) (latticePoint m)) hm⟩

theorem single_mem_newtonFiltration {m : K →₀ ℤ} (r : R)
    (hm : latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ))
    (ha : gauge (newtonPolytope φ) (latticePoint m) ≤ a) : single m r ∈ newtonFiltration φ a := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · exact (single_mem_newtonFiltration_iff hr).2 ⟨hm, ha⟩

theorem newtonFiltration_mono (φ : LaurentRing R K) : Monotone (newtonFiltration φ) :=
  fun _ _ hab => supported_mono fun _ hm => ⟨hm.1, hm.2.trans hab⟩

/-- `F_a = 0` for `a < 0`: the Newton height is nonnegative. -/
theorem newtonFiltration_eq_bot_of_neg (ha : a < 0) : newtonFiltration φ a = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  ext m
  by_contra hm
  exact ha.not_ge ((gauge_nonneg _).trans ((mem_newtonFiltration_iff.1 hf) m
    (Finsupp.mem_support_iff.2 hm)).2)

/-- `F_0` consists of the constants: the origin is the only point of the cone of height `0`. -/
theorem newtonFiltration_zero (φ : LaurentRing R K) :
    newtonFiltration φ 0 = supported R R {0} := by
  ext f
  rw [mem_newtonFiltration_iff, mem_supported]
  refine ⟨fun h m hm => ?_, fun h m hm => ?_⟩
  · obtain ⟨hc, hg⟩ := h m hm
    exact latticePoint_eq_zero_iff.1 (eq_zero_of_mem_hull_newtonPolytope_of_gauge_le_zero hc hg)
  · obtain rfl : m = 0 := h hm
    simpa using ConvexCone.subset_hull (zero_mem_newtonPolytope φ)

/-- `φ` lies in `F_1`: every exponent of `φ` lies in the Newton polytope, so it has Newton
height at most `1`. -/
theorem self_mem_newtonFiltration_one (φ : LaurentRing R K) : φ ∈ newtonFiltration φ 1 :=
  mem_newtonFiltration_iff.2 fun _ hm =>
    ⟨ConvexCone.subset_hull (latticePoint_mem_newtonPolytope hm),
      gauge_le_one_of_mem (latticePoint_mem_newtonPolytope hm)⟩

theorem one_mem_newtonFiltration_zero (φ : LaurentRing R K) : 1 ∈ newtonFiltration φ 0 := by
  rw [newtonFiltration_zero, mem_supported]
  exact (Finset.coe_subset.2 (support_coeff_one_subset (k := R) (G := K →₀ ℤ))).trans (by simp)

/-- The Newton filtration is multiplicative: `F_a F_b ⊆ F_{a+b}`. -/
theorem mul_mem_newtonFiltration (hf : f ∈ newtonFiltration φ a) (hg : g ∈ newtonFiltration φ b) :
    f * g ∈ newtonFiltration φ (a + b) := by
  classical
  rw [mem_newtonFiltration_iff] at hf hg ⊢
  intro m hm
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.1 (support_coeff_mul_subset f g hm)
  obtain ⟨hc₁, hg₁⟩ := hf m₁ hm₁
  obtain ⟨hc₂, hg₂⟩ := hg m₂ hm₂
  rw [map_add]
  exact ⟨add_mem hc₁ hc₂, (gauge_add_le_of_mem_hull (convex_newtonPolytope φ) hc₁ hc₂).trans
    (add_le_add hg₁ hg₂)⟩

/-- The Newton filtration is multiplicative and contains `1` in degree `0`. -/
instance newtonFiltration.gradedMonoid (φ : LaurentRing R K) :
    SetLike.GradedMonoid (newtonFiltration φ) where
  one_mem := one_mem_newtonFiltration_zero φ
  mul_mem _ _ _ _ := mul_mem_newtonFiltration

/-- The Newton filtration is an increasing ring filtration indexed by `ℝ`. -/
instance newtonFiltration.isRingFiltration (φ : LaurentRing R K) :
    IsRingFiltration (newtonFiltration φ) (newtonFiltrationLT φ) where
  mono := newtonFiltration_mono φ
  is_le hab := le_iSup₂_of_le _ hab le_rfl
  is_sup _ _ h := iSup₂_le h

/-- The Newton filtration exhausts the cone algebra: the union of the `F_a` is spanned by the
monomials whose exponent lies in the cone over the Newton polytope. -/
theorem iSup_newtonFiltration (φ : LaurentRing R K) :
    ⨆ a, newtonFiltration φ a =
      supported R R {m | latticePoint m ∈ ConvexCone.hull ℝ (newtonPolytope φ)} := by
  refine le_antisymm (iSup_le fun a => supported_mono fun _ hm => hm.1) fun f hf => ?_
  rw [mem_supported] at hf
  refine Submodule.mem_iSup_of_mem
    (∑ m ∈ f.coeff.support, gauge (newtonPolytope φ) (latticePoint m))
    (mem_newtonFiltration_iff.2 fun m hm => ⟨hf hm, ?_⟩)
  exact Finset.single_le_sum (f := fun m => gauge (newtonPolytope φ) (latticePoint m))
    (fun _ _ => gauge_nonneg _) hm

end Filtration

/-! ### The cross-polytope: `φ = ∑ᵢ (x_i + x_i⁻¹)` -/

section CrossPolytope

variable [Semiring R] [Fintype K]

private theorem coeff_support_sum_X_add_inv [DecidableEq K] [Nontrivial R] :
    (∑ i, (X i + (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)) :
      LaurentRing R K).coeff.support =
      Finset.univ.image (fun i => Finsupp.single i 1) ∪
        Finset.univ.image (fun i => -Finsupp.single i 1) := by
  have hne (i j : K) : -Finsupp.single i (1 : ℤ) ≠ Finsupp.single j 1 := fun h => by
    have := DFunLike.congr_fun h j
    by_cases hij : i = j <;> simp [hij] at this
  have hinj (i j : K) : Finsupp.single i (1 : ℤ) = Finsupp.single j 1 ↔ i = j :=
    Finsupp.single_left_inj one_ne_zero
  ext m
  simp only [coeff_sum, coeff_add, X_def, val_inv_unitX, coeff_single, Finsupp.single_neg,
    Finsupp.mem_support_iff, Finset.sum_apply', Finsupp.add_apply, Finsupp.single_apply,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  by_cases h₁ : ∃ j, Finsupp.single j 1 = m
  · obtain ⟨j, rfl⟩ := h₁
    simp [hne, hinj]
  by_cases h₂ : ∃ j, -Finsupp.single j 1 = m
  · obtain ⟨j, rfl⟩ := h₂
    simp [fun i => (hne j i).symm, hinj]
  push Not at h₁ h₂
  simp [h₁, h₂]

variable (R K) in
/-- The Newton polytope of `∑ᵢ (x_i + x_i⁻¹)` is the cross-polytope, the ℓ¹ unit ball. -/
theorem newtonPolytope_sum_X_add_inv [Nontrivial R] :
    newtonPolytope (∑ i, (X i + (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)) :
      LaurentRing R K) = l1Ball K := by
  classical
  rw [newtonPolytope_def, coeff_support_sum_X_add_inv, l1Ball_eq_convexHull]
  simp [Set.image_union, ← Set.range_comp, Function.comp_def, latticePoint_single]

variable (R) in
/-- The Newton height of `∑ᵢ (x_i + x_i⁻¹)` is the ℓ¹ norm of the exponent. -/
theorem gauge_newtonPolytope_sum_X_add_inv [Nontrivial R] (m : K →₀ ℤ) :
    gauge (newtonPolytope (∑ i, (X i + (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)) :
      LaurentRing R K)) (latticePoint m) = ∑ i, |(m i : ℝ)| := by
  rw [newtonPolytope_sum_X_add_inv, gauge_l1Ball]
  simp

variable (R K) in
/-- The polynomial `∑ᵢ (x_i + x_i⁻¹)` is convenient: the cone over its Newton polytope is the
whole space. -/
theorem hull_newtonPolytope_sum_X_add_inv [Nontrivial R] :
    ConvexCone.hull ℝ (newtonPolytope (∑ i, (X i +
      (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K)) : LaurentRing R K)) = ⊤ := by
  rw [newtonPolytope_sum_X_add_inv]
  refine eq_top_iff.2 fun x _ => ?_
  exact (ConvexCone.mem_hull_of_convex (convex_l1Ball K)).2 (absorbent_l1Ball K).gauge_set_nonempty

/-- For `φ = ∑ᵢ (x_i + x_i⁻¹)`, the Newton filtration is the filtration by the ℓ¹ degree: a
Laurent polynomial lies in `F_a` exactly when each of its exponents has ℓ¹ norm at most `a`. -/
theorem mem_newtonFiltration_sum_X_add_inv_iff [Nontrivial R] {f : LaurentRing R K} {a : ℝ} :
    f ∈ newtonFiltration (∑ i, (X i + (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K))) a ↔
      ∀ m ∈ f.coeff.support, ∑ i, |(m i : ℝ)| ≤ a := by
  rw [mem_newtonFiltration_iff, hull_newtonPolytope_sum_X_add_inv]
  simp only [gauge_newtonPolytope_sum_X_add_inv, ConvexCone.mem_top, true_and]

end CrossPolytope

end TauCeti.LaurentRing
