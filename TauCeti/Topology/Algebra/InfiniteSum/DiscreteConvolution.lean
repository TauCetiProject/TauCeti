/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.DiscreteConvolution
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Single-point families and associativity of discrete convolution

Mathlib's `DiscreteConvolution.single_convolution` says that `Pi.single 1 e` is a unit for
convolution when `e` acts as one. More generally, the convolution of two families supported at one
point each is supported at the product of the points, with the bilinear map applied to the values.

Mathlib has no associativity for `DiscreteConvolution.ringConvolution`. Both bracketings of
`f ⋆ᵣ g ⋆ᵣ h` are sums of `f a * g b * h c` over the triples with `a * b * c = x`, grouped in two
ways; when that triple family is summable and each inner convolution sum converges, the two
groupings agree.

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
* `DiscreteConvolution.addFiberEquivSub`: on an additive group, `y ↦ (x - y, y)` identifies `M`
  with the fibre `addFiber x` of addition at `x`.
* `DiscreteConvolution.addConvolution_eq_tsum_sub` and its ring version
  `DiscreteConvolution.addRingConvolution_eq_tsum_sub`: on an additive group,
  `(f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y)`.
* `DiscreteConvolution.AddConvolutionExistsAt.hasSum_sub`: when the convolution exists at `x`,
  the series `∑' y, L (f (x - y)) (g y)` converges to `(f ⋆₊[L] g) x`.
* `DiscreteConvolution.addConvolution_eq_tsum_neg_add` and its ring version
  `DiscreteConvolution.addRingConvolution_eq_tsum_neg_add`: on an additive group,
  `(f ⋆₊[L] g) x = ∑' y, L (f y) (g (-y + x))`.
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
    (Σ p : mulFiber x, mulFiber p.1.1) ≃ Σ p : mulFiber x, mulFiber p.1.2 where
  toFun σ := ⟨⟨(σ.2.1.1, σ.2.1.2 * σ.1.1.2), by
      rw [mem_mulFiber, ← mul_assoc, mem_mulFiber.mp σ.2.2, mem_mulFiber.mp σ.1.2]⟩,
    ⟨(σ.2.1.2, σ.1.1.2), mem_mulFiber.mpr rfl⟩⟩
  invFun τ := ⟨⟨(τ.1.1.1 * τ.2.1.1, τ.2.1.2), by
      rw [mem_mulFiber, mul_assoc, mem_mulFiber.mp τ.2.2, mem_mulFiber.mp τ.1.2]⟩,
    ⟨(τ.1.1.1, τ.2.1.1), mem_mulFiber.mpr rfl⟩⟩
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
    (hfgh : ∀ x, Summable fun σ : Σ p : mulFiber x, mulFiber p.1.1 ↦
      f σ.2.1.1 * g σ.2.1.2 * h σ.1.1.2) :
    (f ⋆ᵣ g) ⋆ᵣ h = f ⋆ᵣ (g ⋆ᵣ h) := by
  ext x
  -- regroup the triple family by `a * (b * c)` instead of `(a * b) * c`
  have hs := (hfgh x).hasSum
  have hs' : HasSum (fun τ : Σ p : mulFiber x, mulFiber p.1.2 ↦ f τ.1.1.1 * (g τ.2.1.1 * h τ.2.1.2))
      (∑' σ : Σ p : mulFiber x, mulFiber p.1.1, f σ.2.1.1 * g σ.2.1.2 * h σ.1.1.2) :=
    (mulFiberSigmaAssoc x).hasSum_iff.mp <| hs.congr_fun fun _ ↦ (mul_assoc _ _ _).symm
  refine (hs.sigma fun p ↦ ?_).tsum_eq.trans (hs'.sigma fun p ↦ ?_).tsum_eq.symm
  exacts [(hfg p.1.1).hasSum.mul_right (h p.1.2), (hgh p.1.2).hasSum.mul_left (f p.1.1)]

end Assoc

section AddGroup

variable {M S E E' F R : Type*} [AddGroup M]

/-- On an additive group, the fibre of addition at `x` is parametrised by its second
coordinate. -/
def addFiberEquivSub (x : M) : M ≃ addFiber x where
  toFun y := ⟨(x - y, y), mem_addFiber.2 (sub_add_cancel x y)⟩
  invFun ab := ab.1.2
  left_inv _ := rfl
  right_inv ab := Subtype.ext <| Prod.ext (eq_sub_of_add_eq (mem_addFiber.1 ab.2)).symm rfl

@[simp]
theorem coe_addFiberEquivSub_apply (x y : M) : (addFiberEquivSub x y : M × M) = (x - y, y) :=
  (rfl)

@[simp]
theorem addFiberEquivSub_symm_apply (x : M) (ab : addFiber x) :
    (addFiberEquivSub x).symm ab = ab.1.2 :=
  (rfl)

/-- On an additive group, the fibre of addition at `x` is parametrised by its second coordinate,
so additive convolution is the familiar sum `(f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y)`. -/
@[simp]
theorem addConvolution_eq_tsum_sub [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E']
    [AddCommMonoid F] [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆₊[L] g) x = ∑' y, L (f (x - y)) (g y) := by
  rw [addConvolution]
  exact ((addFiberEquivSub x).tsum_eq fun ab ↦ L (f ab.1.1) (g ab.1.2)).symm

/-- On an additive group, when the convolution of `f` and `g` exists at `x`, the series
`∑' y, L (f (x - y)) (g y)` converges to `(f ⋆₊[L] g) x`. -/
theorem AddConvolutionExistsAt.hasSum_sub [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E']
    [AddCommMonoid F] [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    {L : E →ₗ[S] E' →ₗ[S] F} {f : M → E} {g : M → E'} {x : M}
    (hfg : AddConvolutionExistsAt L f g x) :
    HasSum (fun y ↦ L (f (x - y)) (g y)) ((f ⋆₊[L] g) x) := by
  rw [addConvolution_eq_tsum_sub]
  exact ((addFiberEquivSub x).summable_iff.2 hfg).hasSum

/-- On an additive group, `(f ⋆ᵣ₊ g) x = ∑' y, f (x - y) * g y`. -/
theorem addRingConvolution_eq_tsum_sub [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (f g : M → R) (x : M) :
    (f ⋆ᵣ₊ g) x = ∑' y, f (x - y) * g y :=
  addConvolution_eq_tsum_sub _ f g x

/-- On an additive group, the fibre of addition at `x` is also parametrised by its first
coordinate, so `(f ⋆₊[L] g) x = ∑' y, L (f y) (g (-y + x))`. -/
theorem addConvolution_eq_tsum_neg_add [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E']
    [AddCommMonoid F] [Module S E] [Module S E'] [Module S F] [TopologicalSpace F]
    (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) :
    (f ⋆₊[L] g) x = ∑' y, L (f y) (g (-y + x)) := by
  let e : M ≃ addFiber x :=
    { toFun y := ⟨(y, -y + x), mem_addFiber.2 (add_neg_cancel_left y x)⟩
      invFun ab := ab.1.1
      left_inv _ := rfl
      right_inv ab :=
        Subtype.ext <| Prod.ext rfl (eq_neg_add_of_add_eq (mem_addFiber.1 ab.2)).symm }
  rw [addConvolution]
  exact (e.tsum_eq fun ab ↦ L (f ab.1.1) (g ab.1.2)).symm

/-- On an additive group, `(f ⋆ᵣ₊ g) x = ∑' y, f y * g (-y + x)`. -/
theorem addRingConvolution_eq_tsum_neg_add [NonUnitalNonAssocSemiring R] [TopologicalSpace R]
    (f g : M → R) (x : M) :
    (f ⋆ᵣ₊ g) x = ∑' y, f y * g (-y + x) :=
  addConvolution_eq_tsum_neg_add _ f g x

end AddGroup

end DiscreteConvolution
