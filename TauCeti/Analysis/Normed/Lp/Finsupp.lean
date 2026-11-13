/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Geometry.Convex.ConvexSpace.Module
public import TauCeti.Analysis.Normed.Lp.Reindex

/-!
# Finitely supported functions and standard simplices in `ℓᵖ`

Every finitely supported function `f : α → E` lies in `ℓᵖ(α, E)` for every exponent `p : ℝ≥0∞`:
it lies in `ℓ⁰` by finiteness of its support and therefore in `ℓᵖ` by monotonicity of `Memℓp`.
Bundling this gives the additive and `𝕜`-linear inclusions `Finsupp.toLpAddMonoidHom` and
`Finsupp.toLpLinearMap` from `α →₀ E` into `lp (fun _ : α ↦ E) p`, sending `Finsupp.single a v`
to `lp.single p a v` and turning the `ℓ¹` norm and series sum into finite sums over the support.

Applied to the weight function of a finitely supported probability `s : Convexity.StdSimplex ℝ α`,
this embeds `StdSimplex ℝ α` into `lp (fun _ : α ↦ ℝ) p` (`Convexity.StdSimplex.toLp`). Point
masses `StdSimplex.single x` map to the unit coordinate vectors `lp.single p x 1`, every image in
`ℓ¹` has norm `1` and total sum `1`, and the range of `StdSimplex.toLp` is the convex hull of the
unit coordinate vectors (`Convexity.StdSimplex.range_toLp_eq_convexHull`), characterized among all
elements of `ℓᵖ` as the nonnegative finitely supported sequences of sum `1`
(`Convexity.StdSimplex.mem_range_toLp_iff`).

## Main definitions

* `Finsupp.toLp`, `Finsupp.toLpAddMonoidHom`, `Finsupp.toLpLinearMap`: inclusion of `α →₀ E` into
  `lp (fun _ : α ↦ E) p`.
* `Convexity.StdSimplex.toLp`: inclusion of finitely supported probabilities `StdSimplex ℝ α` into
  `lp (fun _ : α ↦ ℝ) p`.

## Main results

* `Finsupp.norm_toLp_one`, `Finsupp.tsum_toLp`: the `ℓ¹` norm and series sum of `f.toLp` reduce to
  `Finsupp.sum`.
* `Convexity.StdSimplex.norm_toLp_one`, `Convexity.StdSimplex.tsum_toLp`: a finitely supported
  probability has `ℓ¹` norm `1` and series sum `1`.
* `Convexity.StdSimplex.range_toLp_eq_convexHull`: the finitely supported probabilities in `ℓᵖ`
  form the convex hull of `{lp.single p x 1 | x : α}`.
* `Convexity.StdSimplex.mem_range_toLp_iff`: an element of `ℓᵖ(α, ℝ)` comes from `StdSimplex ℝ α`
  iff it is nonnegative, finitely supported, and sums to `1`.
-/

public section

open scoped ENNReal

/-- Any finitely supported function into a normed group lies in `ℓᵖ` for every exponent `p`. -/
theorem Function.HasFiniteSupport.memℓp {α E : Type*} [NormedAddCommGroup E] {f : α → E}
    (hf : f.HasFiniteSupport) (p : ℝ≥0∞) : Memℓp f p :=
  (memℓp_zero hf).of_exponent_ge zero_le

namespace Finsupp

variable {α β E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

/-- Every `f : α →₀ E` lies in `ℓᵖ(α, E)` for every exponent `p`. -/
theorem memℓp (f : α →₀ E) (p : ℝ≥0∞) : Memℓp f p :=
  f.hasFiniteSupport.memℓp p

/-- View a finitely supported function `f : α →₀ E` as an element of `lp (fun _ : α ↦ E) p`. -/
def toLp (f : α →₀ E) (p : ℝ≥0∞) : lp (fun _ : α ↦ E) p :=
  ⟨⇑f, f.memℓp p⟩

@[simp]
theorem coeFn_toLp (f : α →₀ E) (p : ℝ≥0∞) : ⇑(f.toLp p) = ⇑f := by
  rfl

theorem toLp_apply (f : α →₀ E) (p : ℝ≥0∞) (a : α) : f.toLp p a = f a := by
  rfl

theorem toLp_injective (p : ℝ≥0∞) : Function.Injective (fun f : α →₀ E ↦ f.toLp p) :=
  fun _ _ h ↦ ext fun a ↦ by simpa using congrArg (fun u : lp (fun _ : α ↦ E) p ↦ u a) h

@[simp]
theorem toLp_inj {f g : α →₀ E} : f.toLp p = g.toLp p ↔ f = g :=
  (toLp_injective p).eq_iff

theorem hasFiniteSupport_toLp (f : α →₀ E) (p : ℝ≥0∞) : (⇑(f.toLp p)).HasFiniteSupport := by
  simpa using f.hasFiniteSupport

@[simp]
theorem toLp_zero (p : ℝ≥0∞) : (0 : α →₀ E).toLp p = 0 := by
  ext
  rfl

@[simp]
theorem toLp_add (f g : α →₀ E) (p : ℝ≥0∞) : (f + g).toLp p = f.toLp p + g.toLp p := by
  ext
  rfl

@[simp]
theorem toLp_neg (f : α →₀ E) (p : ℝ≥0∞) : (-f).toLp p = -f.toLp p := by
  ext
  rfl

@[simp]
theorem toLp_sub (f g : α →₀ E) (p : ℝ≥0∞) : (f - g).toLp p = f.toLp p - g.toLp p := by
  ext
  rfl

@[simp]
theorem toLp_smul {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c : 𝕜) (f : α →₀ E) (p : ℝ≥0∞) : (c • f).toLp p = c • f.toLp p := by
  ext
  rfl

/-- Inclusion of `α →₀ E` into `lp (fun _ : α ↦ E) p` as an additive monoid homomorphism. -/
def toLpAddMonoidHom (p : ℝ≥0∞) : (α →₀ E) →+ lp (fun _ : α ↦ E) p where
  toFun f := f.toLp p
  map_zero' := toLp_zero p
  map_add' f g := toLp_add f g p

@[simp]
theorem toLpAddMonoidHom_apply (p : ℝ≥0∞) (f : α →₀ E) :
    toLpAddMonoidHom p f = f.toLp p := by
  rfl

/-- Inclusion of `α →₀ E` into `lp (fun _ : α ↦ E) p` as a `𝕜`-linear map. -/
def toLpLinearMap (p : ℝ≥0∞) (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    (α →₀ E) →ₗ[𝕜] lp (fun _ : α ↦ E) p where
  __ := toLpAddMonoidHom p
  map_smul' c f := toLp_smul c f p

@[simp]
theorem toLpLinearMap_apply (p : ℝ≥0∞) {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (f : α →₀ E) : toLpLinearMap p 𝕜 f = f.toLp p := by
  rfl

@[simp]
theorem toLp_single [DecidableEq α] (a : α) (v : E) (p : ℝ≥0∞) :
    (Finsupp.single a v).toLp p = lp.single p a v := by
  ext b
  simp [lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- Every `f.toLp p` decomposes as a finite sum over `f.support` of coordinate vectors. -/
theorem toLp_eq_sum_single [DecidableEq α] (f : α →₀ E) (p : ℝ≥0∞) :
    f.toLp p = ∑ a ∈ f.support, lp.single p a (f a) := by
  conv_lhs => rw [← f.sum_single]
  rw [Finsupp.sum, ← toLpAddMonoidHom_apply p, map_sum]
  simp

/-- The series sum of `f.toLp p` equals the finite sum `f.sum`. -/
theorem tsum_toLp (f : α →₀ E) (p : ℝ≥0∞) :
    ∑' a, f.toLp p a = f.sum fun _ v ↦ v := by
  rw [Finsupp.sum]
  simp_rw [toLp_apply]
  exact tsum_eq_sum fun _ ha ↦ notMem_support_iff.mp ha

/-- The `ℓ¹` norm of `f.toLp 1` is the finite sum of the norms of its values. -/
theorem norm_toLp_one (f : α →₀ E) :
    ‖f.toLp 1‖ = f.sum fun _ v ↦ ‖v‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp), Finsupp.sum]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div_one, coeFn_toLp]
  exact tsum_eq_sum fun _ ha ↦ by simp [notMem_support_iff.mp ha]

/-- Reindexing `f : α →₀ E` along `e : α ≃ β` via `equivMapDomain` corresponds to
`AddEquiv.lpCongrLeft`. -/
@[simp]
theorem toLp_equivMapDomain (e : α ≃ β) (f : α →₀ E) (p : ℝ≥0∞) :
    (f.equivMapDomain e).toLp p = AddEquiv.lpCongrLeft p E e (f.toLp p) := by
  ext b
  simp

/-- Pushing `f : α →₀ E` forward along `e : α ≃ β` via `mapDomain` corresponds to
`AddEquiv.lpCongrLeft`. -/
theorem toLp_mapDomain_equiv (e : α ≃ β) (f : α →₀ E) (p : ℝ≥0∞) :
    (f.mapDomain e).toLp p = AddEquiv.lpCongrLeft p E e (f.toLp p) := by
  ext b
  conv_lhs => rw [coeFn_toLp, ← e.apply_symm_apply b, mapDomain_apply_of_injective e.injective]
  simp

end Finsupp

namespace Convexity.StdSimplex

variable {α β : Type*} {p : ℝ≥0∞}

/-- View a finitely supported probability `s : StdSimplex ℝ α` as an element of
`lp (fun _ : α ↦ ℝ) p`. -/
def toLp (s : StdSimplex ℝ α) (p : ℝ≥0∞) : lp (fun _ : α ↦ ℝ) p :=
  s.weights.toLp p

theorem toLp_def (s : StdSimplex ℝ α) (p : ℝ≥0∞) : s.toLp p = s.weights.toLp p := by
  rfl

@[simp]
theorem coeFn_toLp (s : StdSimplex ℝ α) (p : ℝ≥0∞) : ⇑(s.toLp p) = ⇑s.weights := by
  rfl

theorem toLp_apply (s : StdSimplex ℝ α) (p : ℝ≥0∞) (a : α) : s.toLp p a = s.weights a := by
  rfl

theorem toLp_injective (p : ℝ≥0∞) : Function.Injective (fun s : StdSimplex ℝ α ↦ s.toLp p) :=
  fun _ _ h ↦ ext (Finsupp.toLp_injective p h)

@[simp]
theorem toLp_inj {s t : StdSimplex ℝ α} : s.toLp p = t.toLp p ↔ s = t :=
  (toLp_injective p).eq_iff

theorem toLp_apply_nonneg (s : StdSimplex ℝ α) (p : ℝ≥0∞) (a : α) : 0 ≤ s.toLp p a := by
  simp

theorem nonneg_coeFn_toLp (s : StdSimplex ℝ α) (p : ℝ≥0∞) : 0 ≤ ⇑(s.toLp p) := by
  intro a
  simp

theorem hasFiniteSupport_toLp (s : StdSimplex ℝ α) (p : ℝ≥0∞) :
    (⇑(s.toLp p)).HasFiniteSupport := by
  simpa using s.weights.hasFiniteSupport

/-- The point mass `StdSimplex.single x` embeds as the unit coordinate vector `lp.single p x 1`. -/
@[simp]
theorem toLp_single [DecidableEq α] (x : α) (p : ℝ≥0∞) :
    (single x : StdSimplex ℝ α).toLp p = lp.single p x 1 := by
  simp [toLp]

/-- Every finitely supported probability in `ℓᵖ` is a weighted sum of unit coordinate vectors over
its support. -/
theorem toLp_eq_sum_single [DecidableEq α] (s : StdSimplex ℝ α) (p : ℝ≥0∞) :
    s.toLp p = ∑ x ∈ s.weights.support, s.weights x • lp.single p x 1 := by
  rw [toLp, s.weights.toLp_eq_sum_single p]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [← lp.single_smul, smul_eq_mul, mul_one]

/-- Inclusion into `ℓᵖ` preserves binary convex combinations in `StdSimplex ℝ α`. -/
@[simp]
theorem toLp_convexCombPair {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (s t : StdSimplex ℝ α) (p : ℝ≥0∞) :
    (convexCombPair a b ha hb hab s t).toLp p = a • s.toLp p + b • t.toLp p := by
  have hw := (isAffineMap_weights ℝ α).map_convexCombPair ha hb hab s t
  simp [toLp, hw]

/-- Inclusion into `ℓᵖ` preserves indexed convex combinations in `StdSimplex ℝ α`. -/
theorem toLp_iConvexComb {ι : Type*} (w : StdSimplex ℝ ι) (f : ι → StdSimplex ℝ α) (p : ℝ≥0∞) :
    (w.iConvexComb f).toLp p = w.weights.sum fun i r ↦ r • (f i).toLp p := by
  have hw := (isAffineMap_weights ℝ α).map_iConvexComb w f
  rw [toLp, hw, iConvexComb_eq_sum, ← Finsupp.toLpLinearMap_apply p (𝕜 := ℝ), map_finsuppSum]
  rfl

/-- The weights of a finitely supported probability have series sum `1`. -/
@[simp]
theorem tsum_weights (s : StdSimplex ℝ α) : ∑' a, s.weights a = 1 := by
  refine (tsum_eq_sum fun _ ha ↦ Finsupp.notMem_support_iff.mp ha).trans ?_
  exact s.total

/-- The coordinates of a finitely supported probability sum to `1`. -/
theorem tsum_toLp (s : StdSimplex ℝ α) (p : ℝ≥0∞) : ∑' a, s.toLp p a = 1 := by
  simp

/-- `lp.tsumCLM` evaluates to `1` on any finitely supported probability in `ℓ¹`. -/
theorem tsumCLM_toLp (s : StdSimplex ℝ α) : lp.tsumCLM ℝ α ℝ (s.toLp 1) = 1 := by
  simp

/-- Every finitely supported probability has `ℓ¹` norm equal to `1`. -/
@[simp]
theorem norm_toLp_one (s : StdSimplex ℝ α) : ‖s.toLp 1‖ = 1 := by
  rw [toLp, s.weights.norm_toLp_one, Finsupp.sum]
  refine (Finset.sum_congr rfl fun a _ ↦ Real.norm_of_nonneg (s.nonneg a)).trans ?_
  exact s.total

/-- Pushing a finitely supported probability forward along `e : α ≃ β` corresponds to
`AddEquiv.lpCongrLeft`. -/
theorem toLp_map_equiv (e : α ≃ β) (s : StdSimplex ℝ α) (p : ℝ≥0∞) :
    (s.map e).toLp p = AddEquiv.lpCongrLeft p ℝ e (s.toLp p) := by
  simpa [toLp] using s.weights.toLp_mapDomain_equiv e p

/-- The image of `StdSimplex ℝ α` in `lp (fun _ : α ↦ ℝ) p` is convex. -/
theorem convex_range_toLp (p : ℝ≥0∞) : Convex ℝ (Set.range fun s : StdSimplex ℝ α ↦ s.toLp p) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ a b ha hb hab
  exact ⟨convexCombPair a b ha hb hab s t, toLp_convexCombPair ha hb hab s t p⟩

/-- In `lp (fun _ : α ↦ ℝ) p`, the finitely supported probabilities form the convex hull of the
unit coordinate vectors `lp.single p x 1`. -/
theorem range_toLp_eq_convexHull [DecidableEq α] (p : ℝ≥0∞) :
    (Set.range fun s : StdSimplex ℝ α ↦ s.toLp p) =
      convexHull ℝ (Set.range fun x : α ↦ lp.single p x (1 : ℝ)) := by
  refine Set.Subset.antisymm ?_ (convexHull_min ?_ (convex_range_toLp p))
  · rintro _ ⟨s, rfl⟩
    dsimp only
    rw [s.toLp_eq_sum_single p]
    exact (convex_convexHull ℝ _).sum_mem (fun x _ ↦ s.nonneg x) s.total
      fun x _ ↦ subset_convexHull ℝ _ ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨single x, toLp_single x p⟩

/-- An element of `lp (fun _ : α ↦ ℝ) p` comes from `StdSimplex ℝ α` if and only if it is
nonnegative, finitely supported, and sums to `1`. -/
theorem mem_range_toLp_iff {u : lp (fun _ : α ↦ ℝ) p} :
    u ∈ (Set.range fun s : StdSimplex ℝ α ↦ s.toLp p) ↔
      0 ≤ ⇑u ∧ (⇑u).HasFiniteSupport ∧ ∑' x, u x = 1 := by
  refine ⟨?_, fun ⟨h0, hfin, hsum⟩ ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.nonneg_coeFn_toLp p, s.hasFiniteSupport_toLp p, s.tsum_toLp p⟩
  · refine ⟨{
      weights := Finsupp.ofSupportFinite ⇑u hfin
      nonneg := h0
      total := by
        rw [← hsum, Finsupp.sum]
        symm
        refine (tsum_eq_sum fun x hx ↦ ?_).trans (Finset.sum_congr rfl fun _ _ ↦ rfl)
        exact Finsupp.notMem_support_iff.mp hx },
      by ext; rfl⟩

end Convexity.StdSimplex
