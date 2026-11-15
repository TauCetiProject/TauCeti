/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Geometry.Convex.ConvexSpace.Module
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Finitely supported functions and finitely supported probabilities in `ℓᵖ`

Every finitely supported function `f : ι →₀ E` into a normed group lies in `ℓᵖ(ι, E)` at every
exponent `0 ≤ p ≤ ∞`. Bundling this inclusion as an additive homomorphism `Finsupp.toLp p` (and a
linear map `Finsupp.toLpLinearMap p 𝕜` over a normed ring) identifies coordinate vectors
`Finsupp.single i a` with `lp.single p i a` and expresses the `ℓᵖ` norm of `f.toLp p` for finite
positive `p` as a finite sum over `f.support`; at `p = 1` its norm is `f.sum fun _ a ↦ ‖a‖`.

Specializing to Mathlib's finitely supported probability distributions `Convexity.StdSimplex ℝ X`
gives the inclusion `Convexity.StdSimplex.toLp p : StdSimplex ℝ X → lp (fun _ : X ↦ ℝ) p`. Its
elements are nonnegative, finitely supported, and sum to `1`, so in `ℓ¹(X)` they lie on the unit
sphere (`‖w.toLp 1‖ = 1`), and at every exponent their range is the convex hull of the point
masses `lp.single p x 1`.

## Main definitions

* `Finsupp.toLp p`: the additive inclusion `(ι →₀ E) →+ lp (fun _ : ι ↦ E) p`.
* `Finsupp.toLpLinearMap p 𝕜`: `Finsupp.toLp p` as a `𝕜`-linear map.
* `Convexity.StdSimplex.toLp p`: the inclusion of finitely supported real probability distributions
  `StdSimplex ℝ X` into `lp (fun _ : X ↦ ℝ) p`.

## Main results

* `Finsupp.norm_toLp_one`: `‖f.toLp 1‖ = f.sum fun _ a ↦ ‖a‖`.
* `Convexity.StdSimplex.norm_toLp_one`: `‖w.toLp 1‖ = 1`.
* `Convexity.StdSimplex.mem_range_toLp_iff`: `f ∈ Set.range (StdSimplex.toLp p)` if and only if `f`
  is nonnegative, finitely supported, and satisfies `∑' x, f x = 1`.
* `Convexity.StdSimplex.range_toLp_eq_convexHull_single`: the image of `StdSimplex ℝ X` in
  `lp (fun _ : X ↦ ℝ) p` is the convex hull of the point masses `lp.single p x 1`.
-/

public section

noncomputable section

open Convexity
open scoped ENNReal

/-- A function into a normed group with finite support lies in `ℓᵖ` for every exponent `p`. -/
theorem Function.HasFiniteSupport.memℓp {ι E : Type*} [NormedAddCommGroup E] {f : ι → E}
    (hf : f.HasFiniteSupport) (p : ℝ≥0∞) : Memℓp f p :=
  (memℓp_zero hf).of_exponent_ge zero_le

namespace Finsupp

variable {ι 𝕜 E : Type*} [NormedAddCommGroup E]

/-- Every finitely supported function into a normed group lies in `ℓᵖ` for every exponent `p`. -/
theorem memℓp (f : ι →₀ E) (p : ℝ≥0∞) : Memℓp (⇑f) p :=
  Function.HasFiniteSupport.memℓp
    (f.support.finite_toSet.subset fun _ hx ↦ mem_support_iff.mpr hx) p

/-- The inclusion of finitely supported functions `ι →₀ E` into `lp (fun _ : ι ↦ E) p`, as an
additive monoid homomorphism. -/
def toLp (p : ℝ≥0∞) : (ι →₀ E) →+ lp (fun _ : ι ↦ E) p where
  toFun f := ⟨⇑f, f.memℓp p⟩
  map_zero' := lp.ext rfl
  map_add' _ _ := lp.ext rfl

/-- Coercing `f.toLp p` back to a function recovers `f`. -/
@[simp]
theorem coeFn_toLp (p : ℝ≥0∞) (f : ι →₀ E) : ⇑(f.toLp p) = ⇑f :=
  (rfl)

/-- Evaluating `f.toLp p` at `i` gives `f i`. -/
theorem toLp_apply (p : ℝ≥0∞) (f : ι →₀ E) (i : ι) : f.toLp p i = f i :=
  (rfl)

/-- The inclusion `Finsupp.toLp p` is injective. -/
theorem toLp_injective (p : ℝ≥0∞) :
    Function.Injective (toLp p : (ι →₀ E) →+ lp (fun _ : ι ↦ E) p) := by
  intro f g h
  ext i
  exact congrArg (fun x : lp (fun _ : ι ↦ E) p ↦ x i) h

@[simp]
theorem toLp_inj {p : ℝ≥0∞} {f g : ι →₀ E} : f.toLp p = g.toLp p ↔ f = g :=
  (toLp_injective p).eq_iff

@[simp]
theorem toLp_eq_zero {p : ℝ≥0∞} {f : ι →₀ E} : f.toLp p = 0 ↔ f = 0 :=
  map_eq_zero_iff (toLp p) (toLp_injective p)

/-- `Finsupp.toLp` commutes with bounded scalar multiplication. -/
@[simp]
theorem toLp_smul [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) (c : 𝕜)
    (f : ι →₀ E) : (c • f).toLp p = c • f.toLp p :=
  lp.ext rfl

/-- The inclusion of finitely supported functions `ι →₀ E` into `lp (fun _ : ι ↦ E) p`, as a
`𝕜`-linear map. -/
def toLpLinearMap (p : ℝ≥0∞) (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    (ι →₀ E) →ₗ[𝕜] lp (fun _ : ι ↦ E) p where
  __ := toLp p
  map_smul' := toLp_smul p

@[simp]
theorem coe_toLpLinearMap [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞) :
    ⇑(toLpLinearMap p 𝕜 : (ι →₀ E) →ₗ[𝕜] lp (fun _ : ι ↦ E) p) = toLp p :=
  (rfl)

theorem toLpLinearMap_apply [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (p : ℝ≥0∞)
    (f : ι →₀ E) : toLpLinearMap p 𝕜 f = f.toLp p :=
  (rfl)

/-- `Finsupp.toLp` sends `Finsupp.single i a` to `lp.single p i a`. -/
@[simp]
theorem toLp_single [DecidableEq ι] (p : ℝ≥0∞) (i : ι) (a : E) :
    (single i a).toLp p = lp.single p i a := by
  ext j
  simp [single_apply, Pi.single_apply, eq_comm]

/-- Every `f.toLp p` expands as the finite sum over `f.support` of its coordinate vectors. -/
theorem toLp_eq_sum_single [DecidableEq ι] (p : ℝ≥0∞) (f : ι →₀ E) :
    f.toLp p = f.sum fun i a ↦ lp.single p i a := by
  conv_lhs => rw [← sum_single f]
  simp [Finsupp.sum, map_sum]

/-- The underlying function of `f.toLp p` has finite support. -/
theorem hasFiniteSupport_toLp (p : ℝ≥0∞) (f : ι →₀ E) : (⇑(f.toLp p)).HasFiniteSupport :=
  f.support.finite_toSet.subset fun _ hx ↦ mem_support_iff.mpr hx

/-- The coordinates of `f.toLp p` have `HasSum` equal to `f.sum fun _ a ↦ a`. -/
theorem hasSum_toLp (p : ℝ≥0∞) (f : ι →₀ E) :
    HasSum (fun i ↦ f.toLp p i) (f.sum fun _ a ↦ a) :=
  hasSum_sum_of_ne_finset_zero fun _ hi ↦ notMem_support_iff.mp hi

/-- The series of coordinates of `f.toLp p` equals the finite sum `f.sum fun _ a ↦ a`. -/
theorem tsum_toLp (p : ℝ≥0∞) (f : ι →₀ E) : ∑' i, f.toLp p i = f.sum fun _ a ↦ a :=
  (hasSum_toLp p f).tsum_eq

/-- For `0 < p.toReal`, the `p`-th power of `‖f.toLp p‖` is the finite sum of `‖f i‖ ^ p` over
the support of `f`. -/
theorem norm_toLp_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (f : ι →₀ E) :
    ‖f.toLp p‖ ^ p.toReal = f.sum fun _ a ↦ ‖a‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp]
  exact tsum_eq_sum fun i hi ↦ by simp [notMem_support_iff.mp hi, Real.zero_rpow hp.ne']

/-- For `0 < p.toReal`, `‖f.toLp p‖` is `(f.sum fun _ a ↦ ‖a‖ ^ p) ^ p⁻¹`. -/
theorem norm_toLp {p : ℝ≥0∞} (hp : 0 < p.toReal) (f : ι →₀ E) :
    ‖f.toLp p‖ = (f.sum fun _ a ↦ ‖a‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  rw [lp.norm_eq_tsum_rpow hp, one_div]
  congr 1
  exact tsum_eq_sum fun i hi ↦ by simp [notMem_support_iff.mp hi, Real.zero_rpow hp.ne']

/-- The `ℓ¹` norm of `f.toLp 1` is `f.sum fun _ a ↦ ‖a‖`. -/
@[simp]
theorem norm_toLp_one (f : ι →₀ E) : ‖f.toLp 1‖ = f.sum fun _ a ↦ ‖a‖ := by
  simpa using norm_toLp (p := 1) (by simp) f

end Finsupp

namespace Convexity.StdSimplex

variable {X : Type*}

/-- View a finitely supported real probability distribution `w : StdSimplex ℝ X` as an element of
`lp (fun _ : X ↦ ℝ) p`. -/
def toLp (p : ℝ≥0∞) (w : StdSimplex ℝ X) : lp (fun _ : X ↦ ℝ) p :=
  w.weights.toLp p

theorem toLp_def (p : ℝ≥0∞) (w : StdSimplex ℝ X) : w.toLp p = w.weights.toLp p :=
  (rfl)

@[simp]
theorem coeFn_toLp (p : ℝ≥0∞) (w : StdSimplex ℝ X) : ⇑(w.toLp p) = ⇑w.weights :=
  (rfl)

theorem toLp_apply (p : ℝ≥0∞) (w : StdSimplex ℝ X) (x : X) : w.toLp p x = w.weights x :=
  (rfl)

/-- The inclusion `StdSimplex.toLp p` is injective. -/
theorem toLp_injective (p : ℝ≥0∞) :
    Function.Injective (toLp p : StdSimplex ℝ X → lp (fun _ : X ↦ ℝ) p) := fun _ _ h ↦
  ext (Finsupp.toLp_injective p h)

@[simp]
theorem toLp_inj {p : ℝ≥0∞} {w w' : StdSimplex ℝ X} : w.toLp p = w'.toLp p ↔ w = w' :=
  (toLp_injective p).eq_iff

/-- Every coordinate of `w.toLp p` is nonnegative. -/
theorem toLp_nonneg (p : ℝ≥0∞) (w : StdSimplex ℝ X) (x : X) : 0 ≤ w.toLp p x :=
  w.weights_nonneg x

/-- Every coordinate of `w.toLp p` is at most `1`. -/
theorem toLp_le_one (p : ℝ≥0∞) (w : StdSimplex ℝ X) (x : X) : w.toLp p x ≤ 1 :=
  w.weights_apply_le_one x

/-- The underlying function of `w.toLp p` has finite support. -/
theorem hasFiniteSupport_toLp (p : ℝ≥0∞) (w : StdSimplex ℝ X) : (⇑(w.toLp p)).HasFiniteSupport :=
  w.weights.hasFiniteSupport_toLp p

/-- The coordinates of `w.toLp p` have `HasSum` equal to `1`. -/
theorem hasSum_toLp (p : ℝ≥0∞) (w : StdSimplex ℝ X) : HasSum (fun x ↦ w.toLp p x) 1 :=
  w.total ▸ w.weights.hasSum_toLp p

/-- The coordinates of `w.toLp p` sum to `1`. -/
theorem tsum_toLp (p : ℝ≥0∞) (w : StdSimplex ℝ X) : ∑' x, w.toLp p x = 1 :=
  (hasSum_toLp p w).tsum_eq

/-- Every finitely supported probability distribution has `ℓ¹` norm `1`. -/
@[simp]
theorem norm_toLp_one (w : StdSimplex ℝ X) : ‖w.toLp 1‖ = 1 := by
  rw [toLp_def, Finsupp.norm_toLp_one]
  refine (Finset.sum_congr rfl fun x _ ↦ ?_).trans w.total
  exact Real.norm_of_nonneg (w.weights_nonneg x)

/-- For `1 ≤ p`, a finitely supported probability distribution has `ℓᵖ` norm at most `1`. -/
theorem norm_toLp_le_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : StdSimplex ℝ X) : ‖w.toLp p‖ ≤ 1 :=
  (lp.norm_le_norm_of_exponent_le one_ne_zero Fact.out (g := w.toLp p) (f := w.toLp 1)
    fun _ ↦ rfl).trans_eq (norm_toLp_one w)

/-- Point masses `StdSimplex.single x` go to the unit coordinate vectors `lp.single p x 1`. -/
@[simp]
theorem toLp_single [DecidableEq X] (p : ℝ≥0∞) (x : X) :
    (single x : StdSimplex ℝ X).toLp p = lp.single p x 1 := by
  simp [toLp_def]

/-- Two-point distributions go to `s • δ_x + t • δ_y` in `ℓᵖ`. -/
theorem toLp_duple [DecidableEq X] (p : ℝ≥0∞) (x y : X) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : s + t = 1) :
    (duple x y hs ht h).toLp p = lp.single p x s + lp.single p y t := by
  simp [toLp_def, map_add]

/-- Every `w.toLp p` expands as a finite convex combination of unit coordinate vectors. -/
theorem toLp_eq_sum_single [DecidableEq X] (p : ℝ≥0∞) (w : StdSimplex ℝ X) :
    w.toLp p = w.weights.sum fun x r ↦ r • lp.single p x (1 : ℝ) := by
  rw [toLp_def, Finsupp.toLp_eq_sum_single]
  refine Finsupp.sum_congr fun x _ ↦ ?_
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- `StdSimplex.toLp p` preserves binary convex combinations. -/
@[simp]
theorem toLp_convexCombPair (p : ℝ≥0∞) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (w w' : StdSimplex ℝ X) :
    (convexCombPair s t hs ht hst w w').toLp p = s • w.toLp p + t • w'.toLp p := by
  simp [toLp_def]

/-- An element of `lp (fun _ : X ↦ ℝ) p` comes from `StdSimplex ℝ X` if and only if it is
nonnegative, finitely supported, and has coordinate sum `1`. -/
theorem mem_range_toLp_iff {p : ℝ≥0∞} {f : lp (fun _ : X ↦ ℝ) p} :
    f ∈ Set.range (toLp p : StdSimplex ℝ X → lp (fun _ : X ↦ ℝ) p) ↔
      (∀ x, 0 ≤ f x) ∧ (⇑f).HasFiniteSupport ∧ ∑' x, f x = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact ⟨toLp_nonneg p w, hasFiniteSupport_toLp p w, tsum_toLp p w⟩
  · rintro ⟨h0, hfin, hsum⟩
    let w : StdSimplex ℝ X :=
      { weights := Finsupp.ofSupportFinite (⇑f) hfin
        nonneg := fun x ↦ h0 x
        total := by
          rw [Finsupp.sum]
          refine (tsum_eq_sum fun x hx ↦ ?_).symm.trans hsum
          exact Finsupp.notMem_support_iff.mp hx }
    exact ⟨w, lp.ext rfl⟩

/-- The image of `StdSimplex ℝ X` in `lp (fun _ : X ↦ ℝ) p` is convex. -/
theorem convex_range_toLp (p : ℝ≥0∞) :
    Convex ℝ (Set.range (toLp p : StdSimplex ℝ X → lp (fun _ : X ↦ ℝ) p)) := by
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩ a b ha hb hab
  exact ⟨convexCombPair a b ha hb hab w w', toLp_convexCombPair p ha hb hab w w'⟩

/-- The image of `StdSimplex ℝ X` in `lp (fun _ : X ↦ ℝ) p` is the convex hull of the point masses
`lp.single p x 1`. -/
theorem range_toLp_eq_convexHull_single [DecidableEq X] (p : ℝ≥0∞) :
    Set.range (toLp p : StdSimplex ℝ X → lp (fun _ : X ↦ ℝ) p) =
      convexHull ℝ (Set.range fun x : X ↦ lp.single p x (1 : ℝ)) := by
  refine Set.Subset.antisymm ?_ (convexHull_min ?_ (convex_range_toLp p))
  · rintro _ ⟨w, rfl⟩
    rw [toLp_eq_sum_single, Finsupp.sum]
    exact (convex_convexHull ℝ _).sum_mem (fun x _ ↦ w.weights_nonneg x) w.total
      fun x _ ↦ subset_convexHull ℝ _ ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨single x, toLp_single p x⟩

end Convexity.StdSimplex
