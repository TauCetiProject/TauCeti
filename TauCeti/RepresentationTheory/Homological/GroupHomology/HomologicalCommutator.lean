/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Homological commutators of commuting elements

For commuting elements `x, y` of a group `G`, the inhomogeneous chain `[x | y] - [y | x]` is a
`2`-cycle with trivial coefficients `k`. Its class `⟨x, y⟩ ∈ H₂(G, k)` is the *homological
commutator* of `x` and `y`. Over `k = ℤ` these are the classes in the Schur multiplier
`H₂(G, ℤ)` that the commutator of lifts in a central extension of `G` detects; quotienting
`H₂(G, ℤ)` by the classes `⟨x, y⟩` with `x` in a conjugacy-invariant subset gives the reduced
Schur multiplier.

The homological commutator is antisymmetric, natural in the group, and additive in each variable
separately on the elements commuting with the other one. The additivity is witnessed by an
explicit boundary: if `a` and `b` both commute with `y`, the `3`-chain
`[a | b | y] - [a | y | b] + [y | a | b]` has boundary
`([a | y] - [y | a]) + ([b | y] - [y | b]) - ([ab | y] - [y | ab])`. Note that `a` and `b` need
not commute with each other. As a consequence `⟨xⁿ, y⟩ = n • ⟨x, y⟩` for every integer `n`, so
`⟨x, y⟩` is killed by the order of `x`; for instance `2 • ⟨x, y⟩ = 0` when `x` is an involution.

## Main definitions

* `TauCeti.groupHomology.homologicalCommutator`: the class `⟨x, y⟩ ∈ H₂(G, k)` of the cycle
  `[x | y] - [y | x]` for commuting `x, y`.

## Main results

* `TauCeti.groupHomology.homologicalCommutator_symm`: `⟨y, x⟩ = -⟨x, y⟩`.
* `TauCeti.groupHomology.map_homologicalCommutator`: naturality, `f_*⟨x, y⟩ = ⟨f x, f y⟩` up to
  the induced map on coefficients.
* `TauCeti.groupHomology.homologicalCommutator_mul_left`: `⟨ab, y⟩ = ⟨a, y⟩ + ⟨b, y⟩` when `a`
  and `b` commute with `y`, and its mirror image `homologicalCommutator_mul_right`.
* `TauCeti.groupHomology.homologicalCommutator_zpow_left`: `⟨xⁿ, y⟩ = n • ⟨x, y⟩`.
* `TauCeti.groupHomology.nsmul_homologicalCommutator_eq_zero_of_pow_eq_one_left`: if `xⁿ = 1`,
  then `n • ⟨x, y⟩ = 0`.

## References

* M. M. Wood, *An algebraic lifting invariant of Ellenberg, Venkatesh, and Westerland*, Res.
  Math. Sci. 8 (2021), §2.1, for the oriented cycle `[x | y] - [y | x]` representing `⟨x, y⟩`.
-/

public section

universe u

namespace TauCeti.groupHomology

open _root_.groupHomology Finsupp

variable {k G : Type u} [CommRing k] [Group G]

section Chains

variable {A : Rep k G} [A.IsTrivial]

/-- For commuting `x, y`, the oriented chain `a·[x | y] - a·[y | x]` with trivial coefficients is a
`2`-cycle. -/
theorem single_sub_single_mem_cycles₂ {x y : G} (h : Commute x y) (a : A) :
    single (x, y) a - single (y, x) a ∈ cycles₂ A := by
  simp only [cycles₂, LinearMap.mem_ker, map_sub, d₂₁_single (G := G),
    Representation.isTrivial_apply, h.eq]
  abel

/-- If `a` and `b` commute with `y`, then the `3`-chain `[a | b | y] - [a | y | b] + [y | a | b]`
bounds the defect of additivity of `[- | y] - [y | -]`. -/
private theorem d₃₂_single_sub_single_add_single {a b y : G} (ha : Commute a y)
    (hb : Commute b y) (c : A) :
    d₃₂ A (single (a, b, y) c - single (a, y, b) c + single (y, a, b) c) =
      (single (a, y) c - single (y, a) c) + (single (b, y) c - single (y, b) c) -
        (single (a * b, y) c - single (y, a * b) c) := by
  simp only [map_add, map_sub, d₃₂_single (G := G), Representation.isTrivial_apply, ha.eq, hb.eq]
  abel

end Chains

variable (k) in
/-- The **homological commutator** `⟨x, y⟩ ∈ H₂(G, k)` of commuting elements `x, y`: the class of
the `2`-cycle `[x | y] - [y | x]` with trivial coefficients. Over `k = ℤ` this is a class in the
Schur multiplier `H₂(G, ℤ)`. -/
noncomputable def homologicalCommutator {x y : G} (h : Commute x y) :
    H2 (Rep.trivial k G k) :=
  H2π _ ⟨single (x, y) 1 - single (y, x) 1, single_sub_single_mem_cycles₂ h 1⟩

/-- The class of any `2`-cycle equal to `[x | y] - [y | x]` is the homological commutator
`⟨x, y⟩`. -/
theorem H2π_eq_homologicalCommutator {x y : G} (h : Commute x y)
    (z : cycles₂ (Rep.trivial k G k)) (hz : (z : G × G →₀ k) = single (x, y) 1 - single (y, x) 1) :
    H2π _ z = homologicalCommutator k h := by
  rw [homologicalCommutator]
  exact congrArg _ (Subtype.ext hz)

/-- The homological commutator depends only on the two elements, not on how the proof that they
commute is phrased; this rewrites along equalities of the elements. -/
theorem homologicalCommutator_congr {x x' y y' : G} (h : Commute x y) (h' : Commute x' y')
    (hx : x = x') (hy : y = y') : homologicalCommutator k h = homologicalCommutator k h' := by
  subst hx hy
  rfl

/-- Reversing the pair negates the homological commutator: `⟨y, x⟩ = -⟨x, y⟩`. -/
theorem homologicalCommutator_symm {x y : G} (h : Commute x y) :
    homologicalCommutator k h.symm = -homologicalCommutator k h := by
  rw [homologicalCommutator, homologicalCommutator, ← map_neg]
  congr 1
  ext : 1
  simp

/-- `⟨x, x⟩ = 0`: the defining cycle `[x | x] - [x | x]` is zero. -/
@[simp]
theorem homologicalCommutator_self (x : G) : homologicalCommutator k (Commute.refl x) = 0 := by
  rw [homologicalCommutator, ← map_zero (H2π (Rep.trivial k G k)).hom]
  congr 1
  ext : 1
  simp

/-- **Naturality** of the homological commutator: the map induced by `f : G →* H` and a map `φ`
of trivial coefficients sends `⟨x, y⟩` to `φ(1) • ⟨f x, f y⟩`. For the identity of coefficients
this is `f_*⟨x, y⟩ = ⟨f x, f y⟩`. -/
theorem map_homologicalCommutator {H : Type u} [Group H] (f : G →* H)
    (φ : Rep.trivial k G k ⟶ Rep.res f (Rep.trivial k H k)) {x y : G} (h : Commute x y) :
    map f φ 2 (homologicalCommutator k h) = φ.hom (1 : k) • homologicalCommutator k (h.map f) := by
  rw [homologicalCommutator, homologicalCommutator, ← map_smul, H2π_comp_map_apply]
  congr 1
  ext : 1
  rw [coe_mapCycles₂]
  simp [chainsMap₂, mapDomain_sub, mapRange_sub, smul_sub]

/-- **Additivity in the first variable**: if `a` and `b` both commute with `y`, then
`⟨ab, y⟩ = ⟨a, y⟩ + ⟨b, y⟩`. The elements `a` and `b` need not commute with each other. -/
theorem homologicalCommutator_mul_left {a b y : G} (ha : Commute a y) (hb : Commute b y) :
    homologicalCommutator k (ha.mul_left hb) =
      homologicalCommutator k ha + homologicalCommutator k hb := by
  rw [homologicalCommutator, homologicalCommutator, homologicalCommutator, ← map_add, eq_comm,
    H2π_eq_iff]
  exact ⟨single (a, b, y) 1 - single (a, y, b) 1 + single (y, a, b) 1,
    d₃₂_single_sub_single_add_single ha hb 1⟩

/-- **Additivity in the second variable**: if `x` commutes with both `a` and `b`, then
`⟨x, ab⟩ = ⟨x, a⟩ + ⟨x, b⟩`. -/
theorem homologicalCommutator_mul_right {x a b : G} (ha : Commute x a) (hb : Commute x b) :
    homologicalCommutator k (ha.mul_right hb) =
      homologicalCommutator k ha + homologicalCommutator k hb := by
  rw [← neg_neg (homologicalCommutator k (ha.mul_right hb)), ← homologicalCommutator_symm,
    homologicalCommutator_congr _ (ha.symm.mul_left hb.symm) rfl rfl,
    homologicalCommutator_mul_left ha.symm hb.symm, neg_add, ← homologicalCommutator_symm,
    ← homologicalCommutator_symm]

/-- `⟨1, y⟩ = 0`. -/
@[simp]
theorem homologicalCommutator_one_left (y : G) :
    homologicalCommutator k (Commute.one_left y) = 0 := by
  have h := homologicalCommutator_mul_left (k := k) (Commute.one_left y) (Commute.one_left y)
  rwa [homologicalCommutator_congr _ (Commute.one_left y) (one_mul 1) rfl, left_eq_add] at h

/-- `⟨x, 1⟩ = 0`. -/
@[simp]
theorem homologicalCommutator_one_right (x : G) :
    homologicalCommutator k (Commute.one_right x) = 0 := by
  rw [← neg_eq_zero, ← homologicalCommutator_symm]
  exact homologicalCommutator_one_left x

/-- `⟨x⁻¹, y⟩ = -⟨x, y⟩`. -/
theorem homologicalCommutator_inv_left {x y : G} (h : Commute x y) :
    homologicalCommutator k h.inv_left = -homologicalCommutator k h := by
  rw [eq_neg_iff_add_eq_zero, ← homologicalCommutator_mul_left,
    homologicalCommutator_congr _ (Commute.one_left y) (inv_mul_cancel x) rfl,
    homologicalCommutator_one_left]

/-- `⟨x, y⁻¹⟩ = -⟨x, y⟩`. -/
theorem homologicalCommutator_inv_right {x y : G} (h : Commute x y) :
    homologicalCommutator k h.inv_right = -homologicalCommutator k h := by
  rw [eq_neg_iff_add_eq_zero, ← homologicalCommutator_mul_right,
    homologicalCommutator_congr _ (Commute.one_right x) rfl (inv_mul_cancel y),
    homologicalCommutator_one_right]

/-- **The power law** in the first variable: `⟨xⁿ, y⟩ = n • ⟨x, y⟩` for natural `n`. -/
theorem homologicalCommutator_pow_left {x y : G} (h : Commute x y) (n : ℕ) :
    homologicalCommutator k (h.pow_left n) = n • homologicalCommutator k h := by
  induction n with
  | zero =>
    rw [homologicalCommutator_congr _ (Commute.one_left y) (pow_zero x) rfl,
      homologicalCommutator_one_left, zero_smul]
  | succ n ih =>
    rw [homologicalCommutator_congr _ ((h.pow_left n).mul_left h) (pow_succ x n) rfl,
      homologicalCommutator_mul_left (h.pow_left n) h, ih, succ_nsmul]

/-- **The power law** in the second variable: `⟨x, yⁿ⟩ = n • ⟨x, y⟩` for natural `n`. -/
theorem homologicalCommutator_pow_right {x y : G} (h : Commute x y) (n : ℕ) :
    homologicalCommutator k (h.pow_right n) = n • homologicalCommutator k h := by
  rw [← neg_neg (homologicalCommutator k (h.pow_right n)), ← homologicalCommutator_symm,
    homologicalCommutator_congr _ (h.symm.pow_left n) rfl rfl,
    homologicalCommutator_pow_left h.symm n,
    homologicalCommutator_symm h, smul_neg, neg_neg]

/-- **The power law** in the first variable: `⟨xⁿ, y⟩ = n • ⟨x, y⟩` for integer `n`. -/
theorem homologicalCommutator_zpow_left {x y : G} (h : Commute x y) (n : ℤ) :
    homologicalCommutator k (h.zpow_left n) = n • homologicalCommutator k h := by
  cases n with
  | ofNat n =>
    rw [homologicalCommutator_congr _ (h.pow_left n) (zpow_natCast x n) rfl,
      homologicalCommutator_pow_left, Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc n =>
    rw [homologicalCommutator_congr _ (h.pow_left (n + 1)).inv_left (zpow_negSucc x n) rfl,
      homologicalCommutator_inv_left (h.pow_left (n + 1)), homologicalCommutator_pow_left,
      negSucc_zsmul]

/-- **The power law** in the second variable: `⟨x, yⁿ⟩ = n • ⟨x, y⟩` for integer `n`. -/
theorem homologicalCommutator_zpow_right {x y : G} (h : Commute x y) (n : ℤ) :
    homologicalCommutator k (h.zpow_right n) = n • homologicalCommutator k h := by
  rw [← neg_neg (homologicalCommutator k (h.zpow_right n)), ← homologicalCommutator_symm,
    homologicalCommutator_congr _ (h.symm.zpow_left n) rfl rfl,
    homologicalCommutator_zpow_left h.symm n,
    homologicalCommutator_symm h, smul_neg, neg_neg]

/-- Homological commutators respect orders: if `xⁿ = 1`, then `n • ⟨x, y⟩ = 0`. In particular
`2 • ⟨x, y⟩ = 0` for an involution `x`. -/
theorem nsmul_homologicalCommutator_eq_zero_of_pow_eq_one_left {x y : G} (h : Commute x y)
    {n : ℕ} (hx : x ^ n = 1) : n • homologicalCommutator k h = 0 := by
  rw [← homologicalCommutator_pow_left,
    homologicalCommutator_congr _ (Commute.one_left y) hx rfl, homologicalCommutator_one_left]

/-- Homological commutators respect orders: if `yⁿ = 1`, then `n • ⟨x, y⟩ = 0`. -/
theorem nsmul_homologicalCommutator_eq_zero_of_pow_eq_one_right {x y : G} (h : Commute x y)
    {n : ℕ} (hy : y ^ n = 1) : n • homologicalCommutator k h = 0 := by
  rw [← homologicalCommutator_pow_right,
    homologicalCommutator_congr _ (Commute.one_right x) rfl hy, homologicalCommutator_one_right]

/-- The order of `x` kills `⟨x, y⟩`. -/
theorem orderOf_nsmul_homologicalCommutator_left {x y : G} (h : Commute x y) :
    orderOf x • homologicalCommutator k h = 0 :=
  nsmul_homologicalCommutator_eq_zero_of_pow_eq_one_left h (pow_orderOf_eq_one x)

/-- The order of `y` kills `⟨x, y⟩`. -/
theorem orderOf_nsmul_homologicalCommutator_right {x y : G} (h : Commute x y) :
    orderOf y • homologicalCommutator k h = 0 :=
  nsmul_homologicalCommutator_eq_zero_of_pow_eq_one_right h (pow_orderOf_eq_one y)

end TauCeti.groupHomology
