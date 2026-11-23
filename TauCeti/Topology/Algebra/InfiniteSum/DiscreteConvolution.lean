/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Single-point families, associativity and group reindexing of discrete convolution

Mathlib's `DiscreteConvolution.single_convolution` says that `Pi.single 1 e` is a unit for
convolution when `e` acts as one. More generally, the convolution of two families supported at one
point each is supported at the product of the points, with the bilinear map applied to the values.

Mathlib has no associativity for `DiscreteConvolution.ringConvolution`. Both bracketings of
`f ⋆ᵣ g ⋆ᵣ h` are sums of `f a * g b * h c` over the triples with `a * b * c = x`, grouped in two
ways; when that triple family is summable and each inner convolution sum converges, the two
groupings agree.

On a group, the fibre of multiplication at `x` is parametrised by either coordinate, which turns
convolution into the familiar sums `∑' y, L (f (x / y)) (g y)` and `∑' y, L (f y) (g (y⁻¹ * x))`.

## Main results

* `DiscreteConvolution.single_convolution_single` and its additive version
  `DiscreteConvolution.single_addConvolution_single`:
  `Pi.single m a ⋆[L] Pi.single n b = Pi.single (m * n) (L a b)`.
* `DiscreteConvolution.single_ringConvolution_single` and its additive version
  `DiscreteConvolution.single_addRingConvolution_single`:
  `Pi.single m a ⋆ᵣ Pi.single n b = Pi.single (m * n) (a * b)`.
* `DiscreteConvolution.ringConvolution_assoc` and its additive version
  `DiscreteConvolution.addRingConvolution_assoc`: ring convolution is associative when the triple
  family and the inner convolutions are summable.
* `DiscreteConvolution.mulFiberEquivDiv` and its additive version
  `DiscreteConvolution.addFiberEquivSub`: on a group, `y ↦ (x / y, y)` identifies `M` with the
  fibre `mulFiber x` of multiplication at `x`.
* `DiscreteConvolution.convolution_eq_tsum_div` and its ring version
  `DiscreteConvolution.ringConvolution_eq_tsum_div`: on a group,
  `(f ⋆[L] g) x = ∑' y, L (f (x / y)) (g y)`; additively
  `DiscreteConvolution.addConvolution_eq_tsum_sub` and
  `DiscreteConvolution.addRingConvolution_eq_tsum_sub`.
* `DiscreteConvolution.ConvolutionExistsAt.hasSum_div` and its additive version
  `DiscreteConvolution.AddConvolutionExistsAt.hasSum_sub`: when the convolution exists at `x`,
  the series `∑' y, L (f (x / y)) (g y)` converges to `(f ⋆[L] g) x`.
* `DiscreteConvolution.convolution_eq_tsum_inv_mul` and its ring version
  `DiscreteConvolution.ringConvolution_eq_tsum_inv_mul`: on a group,
  `(f ⋆[L] g) x = ∑' y, L (f y) (g (y⁻¹ * x))`; additively
  `DiscreteConvolution.addConvolution_eq_tsum_neg_add` and
  `DiscreteConvolution.addRingConvolution_eq_tsum_neg_add`.
* `DiscreteConvolution.norm_ringConvolution_apply_le` and its additive version
  `DiscreteConvolution.norm_addRingConvolution_apply_le`: on a group, over an ultrametric ring, if
  the coefficient norms of `f` and `g` are bounded by `A` and `B`, those of `f ⋆ᵣ g` are bounded by
  `A B`.
* `DiscreteConvolution.hasSum_tsum_mul_div` and its additive version
  `DiscreteConvolution.hasSum_tsum_mul_sub`: on a group, for two absolutely summable families
  in a complete normed ring, `x ↦ ∑' y, f y * g (x / y)` (their convolution when the group is
  commutative) sums to `(∑ f) (∑ g)`.
* `DiscreteConvolution.tsum_mul_sub_eq_sum_antidiagonal`,
  `DiscreteConvolution.tsum_mul_sub_eq_zero_of_neg`: the convolution `∑' i, f i * g (m - i)` of
  two families on `ℤ` supported in nonnegative degrees is the finite antidiagonal sum at a
  natural number `m`, and vanishes at negative `m`.
-/

public section

open scoped DiscreteConvolution

namespace DiscreteConvolution

section Single

variable {M S E E' F R : Type*} [Monoid M] [DecidableEq M]

/-- **The convolution of two single-point families is a single-point family**, at the product of
the points and with the bilinear map applied to the values. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) single_addConvolution_single]
theorem single_convolution_single [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E']
    [AddCommMonoid F] [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (m n : M) (a : E) (b : E') :
    Pi.single m a ⋆[L] Pi.single n b = Pi.single (m * n) (L a b) := by
  ext p
  simp only [convolution, Pi.single_apply]
  split_ifs with hp
  · rw [tsum_eq_single ⟨(m, n), mem_mulFiber.mpr hp.symm⟩
      fun _ _ ↦ by grind [LinearMap.zero_apply]]
    simp
  · exact (tsum_congr fun _ ↦ by grind [LinearMap.zero_apply]).trans tsum_zero

/-- **The ring convolution of two single-point families is a single-point family**, at the product
of the points and with the product of the values. -/
@[to_additive (dont_translate := R) (attr := simp) single_addRingConvolution_single]
theorem single_ringConvolution_single [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (m n : M) (a b : R) :
    Pi.single m a ⋆ᵣ Pi.single n b = Pi.single (m * n) (a * b) := by
  simpa only [ringConvolution, LinearMap.mul_apply'] using
    single_convolution_single (.mul ℕ R) m n a b

end Single

section Assoc

variable {M R : Type*} [Monoid M]

-- The two groupings of the triples multiplying to `x`, as nested fibres: `((a, b), c)` with
-- `a * b = m` and `m * c = x` corresponds to `(a, (b, c))` with `b * c = k` and `a * k = x`.
@[to_additive]
private def mulFiberSigmaAssoc (x : M) :
    (Σ p : mulFiber x, mulFiber p.val.1) ≃ Σ p : mulFiber x, mulFiber p.val.2 where
  toFun σ := ⟨⟨(σ.2.val.1, σ.2.val.2 * σ.1.val.2), by
      rw [mem_mulFiber, ← mul_assoc, mem_mulFiber.mp σ.2.property, mem_mulFiber.mp σ.1.property]⟩,
    ⟨(σ.2.val.2, σ.1.val.2), mem_mulFiber.mpr rfl⟩⟩
  invFun τ := ⟨⟨(τ.1.val.1 * τ.2.val.1, τ.2.val.2), by
      rw [mem_mulFiber, mul_assoc, mem_mulFiber.mp τ.2.property, mem_mulFiber.mp τ.1.property]⟩,
    ⟨(τ.1.val.1, τ.2.val.1), mem_mulFiber.mpr rfl⟩⟩
  left_inv := by
    rintro ⟨⟨⟨m, c⟩, hm⟩, ⟨⟨a, b⟩, hab⟩⟩
    obtain rfl := mem_mulFiber.mp hab
    rfl
  right_inv := by
    rintro ⟨⟨⟨a, k⟩, hk⟩, ⟨⟨b, c⟩, hbc⟩⟩
    obtain rfl := mem_mulFiber.mp hbc
    rfl

variable [NonUnitalSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R] [T3Space R]

/-- **Ring convolution is associative** when the family `f a * g b * h c` over the triples with
`a * b * c = x` is summable for every `x`, and so are the convolution sums of `f` with `g` and of
`g` with `h`. The triples are indexed as pairs `((a, b), c)` with `a * b = m` and `m * c = x`. -/
@[to_additive (dont_translate := R) addRingConvolution_assoc
  /-- **Additive ring convolution is associative** when the family `f a * g b * h c` over the
  triples with `a + b + c = x` is summable for every `x`, and so are the convolution sums of `f`
  with `g` and of `g` with `h`. The triples are indexed as pairs `((a, b), c)` with `a + b = m`
  and `m + c = x`. -/]
theorem ringConvolution_assoc {f g h : M → R} (hfg : ConvolutionExists (.mul ℕ R) f g)
    (hgh : ConvolutionExists (.mul ℕ R) g h)
    (hfgh : ∀ x, Summable fun σ : Σ p : mulFiber x, mulFiber p.val.1 ↦
      f σ.2.val.1 * g σ.2.val.2 * h σ.1.val.2) :
    (f ⋆ᵣ g) ⋆ᵣ h = f ⋆ᵣ (g ⋆ᵣ h) := by
  ext x
  -- regroup the triple family by `a * (b * c)` instead of `(a * b) * c`
  have hs := (hfgh x).hasSum
  have hs' : HasSum (fun τ : Σ p : mulFiber x, mulFiber p.val.2 ↦ f τ.1.val.1 *
      (g τ.2.val.1 * h τ.2.val.2))
      (∑' σ : Σ p : mulFiber x, mulFiber p.val.1, f σ.2.val.1 * g σ.2.val.2 * h σ.1.val.2) :=
    (mulFiberSigmaAssoc x).hasSum_iff.mp <| hs.congr_fun fun _ ↦ (mul_assoc _ _ _).symm
  refine (hs.sigma fun p ↦ ?_).tsum_eq.trans (hs'.sigma fun p ↦ ?_).tsum_eq.symm
  exacts [(hfg p.val.1).hasSum.mul_right (h p.val.2), (hgh p.val.2).hasSum.mul_left (f p.val.1)]

end Assoc

section Group

variable {M S E E' F R : Type*} [Group M]

/-- On a group, the fibre of multiplication at `x` is parametrised by its second coordinate. -/
@[to_additive
  /-- On an additive group, the fibre of addition at `x` is parametrised by its second
  coordinate. -/]
def mulFiberEquivDiv (x : M) : M ≃ mulFiber x where
  toFun y := ⟨(x / y, y), mem_mulFiber.2 (div_mul_cancel x y)⟩
  invFun ab := ab.val.2
  left_inv _ := rfl
  right_inv ab := Subtype.ext <| Prod.ext (eq_div_of_mul_eq' (mem_mulFiber.1 ab.property)).symm rfl

@[to_additive (attr := simp)]
theorem coe_mulFiberEquivDiv_apply (x y : M) : (mulFiberEquivDiv x y : M × M) = (x / y, y) :=
  (rfl)

@[to_additive (attr := simp)]
theorem mulFiberEquivDiv_symm_apply (x : M) (ab : mulFiber x) :
    (mulFiberEquivDiv x).symm ab = ab.val.2 :=
  (rfl)

section Bilinear

variable [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F] [Module S E]
  [Module S E'] [Module S F] [TopologicalSpace F]

/-- On a group, the fibre of multiplication at `x` is parametrised by its second coordinate, so
convolution is the sum `(f ⋆[L] g) x = ∑' y, L (f (x / y)) (g y)`. -/
@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_eq_tsum_sub
  /-- On an additive group, the fibre of addition at `x` is parametrised by its second
  coordinate, so additive convolution is the familiar sum
  `(f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y)`. -/]
theorem convolution_eq_tsum_div (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' y, L (f (x / y)) (g y) := by
  rw [convolution]
  exact ((mulFiberEquivDiv x).tsum_eq fun ab ↦ L (f ab.val.1) (g ab.val.2)).symm

/-- On a group, when the convolution of `f` and `g` exists at `x`, the series
`∑' y, L (f (x / y)) (g y)` converges to `(f ⋆[L] g) x`. -/
@[to_additive (dont_translate := S E E' F)
  /-- On an additive group, when the convolution of `f` and `g` exists at `x`, the series
  `∑' y, L (f (x - y)) (g y)` converges to `(f ⋆₊[L] g) x`. -/]
theorem ConvolutionExistsAt.hasSum_div {L : E →ₗ[S] E' →ₗ[S] F} {f : M → E} {g : M → E'}
    {x : M} (hfg : ConvolutionExistsAt L f g x) :
    HasSum (fun y ↦ L (f (x / y)) (g y)) ((f ⋆[L] g) x) := by
  rw [convolution_eq_tsum_div]
  exact ((mulFiberEquivDiv x).summable_iff.2 hfg).hasSum

/-- On a group, the fibre of multiplication at `x` is also parametrised by its first coordinate,
so `(f ⋆[L] g) x = ∑' y, L (f y) (g (y⁻¹ * x))`. -/
@[to_additive (dont_translate := S E E' F) addConvolution_eq_tsum_neg_add
  /-- On an additive group, the fibre of addition at `x` is also parametrised by its first
  coordinate, so `(f ⋆₊[L] g) x = ∑' y, L (f y) (g (-y + x))`. -/]
theorem convolution_eq_tsum_inv_mul (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆[L] g) x = ∑' y, L (f y) (g (y⁻¹ * x)) := by
  let e : M ≃ mulFiber x :=
    { toFun y := ⟨(y, y⁻¹ * x), mem_mulFiber.2 (mul_inv_cancel_left y x)⟩
      invFun ab := ab.val.1
      left_inv _ := rfl
      right_inv ab :=
        Subtype.ext <| Prod.ext rfl (eq_inv_mul_of_mul_eq (mem_mulFiber.1 ab.property)).symm }
  rw [convolution]
  exact (e.tsum_eq fun ab ↦ L (f ab.val.1) (g ab.val.2)).symm

end Bilinear

/-- On a group, `(f ⋆ᵣ g) x = ∑' y, f (x / y) * g y`. -/
@[to_additive (dont_translate := R) addRingConvolution_eq_tsum_sub
  /-- On an additive group, `(f ⋆ᵣ₊ g) x = ∑' y, f (x - y) * g y`. -/]
theorem ringConvolution_eq_tsum_div [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑' y, f (x / y) * g y :=
  convolution_eq_tsum_div _ f g x

/-- On a group, `(f ⋆ᵣ g) x = ∑' y, f y * g (y⁻¹ * x)`. -/
@[to_additive (dont_translate := R) addRingConvolution_eq_tsum_neg_add
  /-- On an additive group, `(f ⋆ᵣ₊ g) x = ∑' y, f y * g (-y + x)`. -/]
theorem ringConvolution_eq_tsum_inv_mul [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (f g : M → R) (x : M) :
    (f ⋆ᵣ g) x = ∑' y, f y * g (y⁻¹ * x) :=
  convolution_eq_tsum_inv_mul _ f g x

/-- On a group, over an ultrametric ring, if the coefficient norms of `f` and `g` are bounded by
`A` and `B`, those of `f ⋆ᵣ g` are bounded by `A B`. -/
@[to_additive (dont_translate := R) norm_addRingConvolution_apply_le
  /-- On an additive group, over an ultrametric ring, if the coefficient norms of `f` and `g` are
  bounded by `A` and `B`, those of `f ⋆ᵣ₊ g` are bounded by `A B`. -/]
theorem norm_ringConvolution_apply_le [SeminormedRing R] [IsUltrametricDist R] {f g : M → R}
    {A B : ℝ} (hf : ∀ x, ‖f x‖ ≤ A) (hg : ∀ x, ‖g x‖ ≤ B) (x : M) : ‖(f ⋆ᵣ g) x‖ ≤ A * B := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf 1)
  rw [ringConvolution_eq_tsum_div]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hA ((norm_nonneg _).trans (hg 1))) fun y ↦
      (norm_mul_le _ _).trans (mul_le_mul (hf _) (hg _) (norm_nonneg _) hA)

/-- On a group, for two absolutely summable families `f`, `g` in a complete normed ring, the
family `x ↦ ∑' y, f y * g (x / y)` (the convolution of `f` and `g` when `M` is commutative) sums
to `(∑ f) (∑ g)`. -/
@[to_additive (dont_translate := R) hasSum_tsum_mul_sub
  /-- On an additive group, for two absolutely summable families `f`, `g` in a complete normed
  ring, the family `x ↦ ∑' y, f y * g (x - y)` (the convolution of `f` and `g` when `M` is
  commutative) sums to `(∑ f) (∑ g)`. -/]
theorem hasSum_tsum_mul_div [NormedRing R] [CompleteSpace R] {f g : M → R}
    (hf : Summable fun y ↦ ‖f y‖) (hg : Summable fun z ↦ ‖g z‖) :
    HasSum (fun x ↦ ∑' y, f y * g (x / y)) ((∑' y, f y) * ∑' z, g z) := by
  -- reindex the product `∑ (y, z), f y g z` by `(x, y) = (z * y, y)`
  let e : M × M ≃ M × M :=
    { toFun p := (p.2 * p.1, p.1)
      invFun q := (q.2, q.1 / q.2)
      left_inv p := by simp
      right_inv q := by simp }
  have hF : HasSum (fun p : M × M ↦ f p.2 * g (p.1 / p.2)) ((∑' y, f y) * ∑' z, g z) := by
    rw [← e.hasSum_iff]
    convert hf.of_norm.hasSum.mul hg.of_norm.hasSum (summable_mul_of_summable_norm hf hg) using 1
    ext p
    simp [e]
  exact hF.prod_fiberwise fun x ↦ (hF.summable.prod_factor x).hasSum

end Group

section Int

variable {R : Type*} [NonUnitalNonAssocSemiring R] [TopologicalSpace R]

/-- The convolution `∑' i, f i * g (n - i)` of two families on `ℤ` supported in nonnegative
degrees is, at a natural number `n`, the finite sum over the antidiagonal of `n`. -/
theorem tsum_mul_sub_eq_sum_antidiagonal {f g : ℤ → R} (hf : ∀ i < 0, f i = 0)
    (hg : ∀ i < 0, g i = 0) (n : ℕ) :
    ∑' i, f i * g (n - i) = ∑ ij ∈ Finset.antidiagonal n, f ij.1 * g ij.2 := by
  rw [tsum_eq_sum (s := (Finset.range (n + 1)).map Nat.castEmbedding) fun i hi ↦ ?_,
    Finset.sum_map, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  · refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [Nat.castEmbedding_apply, Nat.cast_sub (Finset.mem_range_succ_iff.1 hk)]
  · simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, not_exists,
      not_and] at hi
    rcases lt_or_ge i 0 with h | h
    · rw [hf i h, zero_mul]
    · lift i to ℕ using h
      rw [hg _ (by have := hi i; omega), mul_zero]

/-- The convolution `∑' i, f i * g (m - i)` of two families on `ℤ` supported in nonnegative
degrees vanishes in negative degrees. -/
theorem tsum_mul_sub_eq_zero_of_neg {f g : ℤ → R} (hf : ∀ i < 0, f i = 0)
    (hg : ∀ i < 0, g i = 0) {m : ℤ} (hm : m < 0) : ∑' i, f i * g (m - i) = 0 := by
  refine (tsum_congr fun i ↦ ?_).trans tsum_zero
  rcases lt_or_ge i 0 with h | h
  · rw [hf i h, zero_mul]
  · rw [hg _ (by omega), mul_zero]

end Int

end DiscreteConvolution
