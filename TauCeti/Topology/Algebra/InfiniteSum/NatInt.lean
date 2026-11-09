/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Reindexing infinite sums between the integers and natural numbers

This file supplements Mathlib's results on infinite sums over `ℕ` and `ℤ` with a reindexing
lemma for an integer-indexed family whose support is bounded below, with the splitting of a
summable integer-indexed family into its residue classes modulo `M`, and with the grouping of an
integer-indexed sum, or of a product or sum indexed by the natural numbers, into blocks of `M`
consecutive terms.

## Main results

* `TauCeti.hasSum_int_iff_natCast_sub`: reindex a family supported in `[-k, ∞)` by `n ↦ n - k`.
* `TauCeti.hasSum_mul_zpow_natCast_sub_iff`: move an integer-power shift between the summands and
  their sum.
* `TauCeti.tsum_int_eq_sum_fin_tsum`: a summable family on `ℤ` sums to the sum over the residues
  `r < M` of its sums over the classes `qM + r`.
* `HasProd.prod_fiberwise_of_fintype`: a family on `β × γ` for a finite type `γ` has the same
  product as the products of its finite fibers, with no hypothesis on the topology of the target.
* `HasSum.sum_fin_mul_add`: a family on `ℤ` has the same sum as its sums over the blocks
  `qM + r`, `r < M`.
* `HasSum.sum_zmod_val_sub`: the same, with the blocks `a - N y` indexed by the least
  nonnegative representatives `a` of the residues modulo `N`.
* `HasProd.prod_fin_mul_add_nat`, `HasSum.sum_fin_mul_add_nat`: the grouping of
  `HasSum.sum_fin_mul_add` into blocks `qM + r`, `r < M`, for a product or sum over the natural
  numbers.
-/

public section

namespace TauCeti

/-- A sum over the integers whose terms vanish below `-k` can be reindexed over the natural
numbers by `n ↦ n - k`. -/
theorem hasSum_int_iff_natCast_sub {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {k : ℤ} {f : ℤ → E} (hf : ∀ j < -k, f j = 0) {s : E} :
    HasSum f s ↔ HasSum (fun n : ℕ ↦ f ((n : ℤ) - k)) s := by
  let g : ℕ → ℤ := fun n ↦ (n : ℤ) - k
  have hg : Function.Injective g := by
    intro m n hmn
    simp only [g] at hmn
    omega
  have hoff : ∀ j ∉ Set.range g, f j = 0 := by
    intro j hj
    apply hf j
    by_contra hjlt
    apply hj
    use (j + k).toNat
    simp only [g]
    omega
  simpa only [Function.comp_def, g] using (hg.hasSum_iff hoff).symm

/-- Multiplication by `q ^ k` converts a sum with powers `q ^ (n - k)` into one with powers
`q ^ n`. -/
theorem hasSum_mul_zpow_natCast_sub_iff {K : Type*} [Semifield K] [TopologicalSpace K]
    [IsTopologicalSemiring K] {a : ℕ → K} {q s : K}
    (hq : q ≠ 0) (k : ℤ) :
    HasSum (fun n : ℕ ↦ a n * q ^ ((n : ℤ) - k)) s ↔
      HasSum (fun n : ℕ ↦ a n * q ^ n) (q ^ k * s) := by
  have hpow (n : ℕ) : q ^ k * (a n * q ^ ((n : ℤ) - k)) = a n * q ^ n := by
    rw [mul_left_comm, ← zpow_natCast, ← zpow_add₀ hq, add_sub_cancel]
  exact (hasSum_mul_left_iff (zpow_ne_zero k hq)).symm.trans (by simp only [hpow])

/-- **A sum over the integers splits into its residue classes modulo `M`**: for a summable family,
`∑ n, f n = ∑_{r < M} ∑ q, f (q * M + r)`. -/
theorem tsum_int_eq_sum_fin_tsum {E : Type*} [AddCommGroup E] [UniformSpace E]
    [IsUniformAddGroup E] [CompleteSpace E] [T0Space E] {f : ℤ → E} (hf : Summable f) (M : ℕ)
    [NeZero M] :
    ∑' n, f n = ∑ r : Fin M, ∑' q : ℤ, f (q * M + r) := by
  have hs : Summable (f ∘ (Int.divModEquiv M).symm) := (Equiv.summable_iff _).2 hf
  have h := hs.tsum_prod' fun _ ↦ .of_finite
  simp only [Function.comp_apply, tsum_fintype, Int.divModEquiv_symm_apply] at h
  rw [← (Int.divModEquiv M).symm.tsum_eq f]
  simp only [Int.divModEquiv_symm_apply]
  rw [h]
  refine Summable.tsum_finsetSum fun r _ ↦ hf.comp_injective fun a b h ↦ ?_
  simpa [NeZero.ne M] using h

end TauCeti

/-- **Summing over the finite fibers of a product**: if a family `f` on `β × γ`, for a finite type
`γ`, has product `a`, then so does the family of products `b ↦ ∏_c f (b, c)` over the fibers. No
continuity of the multiplication and no separation axiom is needed, since the fibers are finite. -/
@[to_additive /-- **Summing over the finite fibers of a product**: if a family `f` on `β × γ`, for
a finite type `γ`, has sum `a`, then so does the family of sums `b ↦ ∑_c f (b, c)` over the fibers.
No continuity of the addition and no separation axiom is needed, since the fibers are finite. -/]
theorem HasProd.prod_fiberwise_of_fintype {β γ E : Type*} [CommMonoid E] [TopologicalSpace E]
    [Fintype γ] {f : β × γ → E} {a : E} (hf : HasProd f a) :
    HasProd (fun b ↦ ∏ c, f (b, c)) a := by
  classical
  have h : Filter.Tendsto (fun T : Finset β ↦ T ×ˢ (Finset.univ : Finset γ)) Filter.atTop
      Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun S ↦ ⟨S.image Prod.fst, fun T hT x hx ↦ ?_⟩
    exact Finset.mem_product.2 ⟨hT (Finset.mem_image_of_mem _ hx), Finset.mem_univ _⟩
  rw [HasProd, SummationFilter.unconditional_filter] at hf ⊢
  exact (hf.comp h).congr fun T ↦ by simp [Finset.prod_product]

/-- **A sum over the integers grouped into blocks of `M` consecutive terms**: if `f` has sum `s`,
then so does the family of block sums `q ↦ ∑_{r < M} f (q * M + r)`. -/
theorem HasSum.sum_fin_mul_add {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℤ → E} {s : E} (hf : HasSum f s) (M : ℕ)
    [NeZero M] : HasSum (fun q : ℤ ↦ ∑ r : Fin M, f (q * M + r)) s := by
  simpa [Function.comp_def] using
    ((Int.divModEquiv M).symm.hasSum_iff.mpr hf).sum_fiberwise_of_fintype

/-- **A product over the natural numbers grouped into blocks of `M` consecutive factors**: if `f`
has product `a`, then so does the family of block products `n ↦ ∏_{r < M} f (n * M + r)`. -/
@[to_additive /-- **A sum over the natural numbers grouped into blocks of `M` consecutive terms**:
if `f` has sum `s`, then so does the family of block sums `n ↦ ∑_{r < M} f (n * M + r)`. -/]
theorem HasProd.prod_fin_mul_add_nat {E : Type*} [CommMonoid E] [TopologicalSpace E]
    {f : ℕ → E} {a : E} (hf : HasProd f a) (M : ℕ)
    [NeZero M] : HasProd (fun n : ℕ ↦ ∏ r : Fin M, f (n * M + r)) a := by
  simpa [Function.comp_def] using
    ((Nat.divModEquiv M).symm.hasProd_iff.mpr hf).prod_fiberwise_of_fintype

/-- **A sum over the integers grouped into blocks of `N` consecutive terms**: if `f` has sum `s`,
then so does the family of block sums `y ↦ ∑_a f (a - N y)`, where `a` runs over the least
nonnegative representatives of the residues modulo `N`. -/
theorem HasSum.sum_zmod_val_sub {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    {f : ℤ → E} {s : E} (hf : HasSum f s) (N : ℕ)
    [NeZero N] : HasSum (fun y : ℤ ↦ ∑ a : ZMod N, f ((a.val : ℤ) - N * y)) s := by
  have hbij : Function.Bijective fun r : Fin N ↦ ((r : ℕ) : ZMod N) :=
    (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fun j ↦ ⟨⟨j.val, j.val_lt⟩, by simp⟩, by simp [ZMod.card]⟩
  refine ((Equiv.neg ℤ).hasSum_iff.mpr (hf.sum_fin_mul_add N)).congr_fun fun y ↦ ?_
  rw [Function.comp_apply, Equiv.neg_apply,
    ← Fintype.sum_bijective _ hbij (fun r : Fin N ↦ _) _ fun _ ↦ rfl]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [ZMod.val_cast_of_lt r.isLt]
  rw [sub_eq_neg_add, neg_mul, mul_comm]
