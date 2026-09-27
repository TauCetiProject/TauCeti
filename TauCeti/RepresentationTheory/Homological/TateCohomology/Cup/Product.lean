/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Ring.NegOnePow
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Cup.ZeroLeft
public import TauCeti.RepresentationTheory.Homological.TateCohomology.DimensionShift

/-!
# The Tate cup product in all bidegrees

For a finite group `G` and representations `M`, `N`, this file constructs the cup product

`tateCohomology M p × tateCohomology N q → tateCohomology (M ⊗ N) r`, `r = p + q`,

for all integers `p` and `q`, as a `k`-bilinear map. It extends the product `cupH0` with a
degree-zero class by dimension shifting in the second variable (Cassels–Fröhlich, Chapter IV, §7;
Brown, Chapter VI, §5). Writing `δ` for the connecting maps of the dimension-shifting sequences
`0 → N → Coind_⊥^G N → dimensionShiftUp N → 0` and `0 → dimensionShiftDown N → Ind_⊥^G N → N → 0`,
which are isomorphisms on Tate cohomology, and also for the connecting maps of the same sequences
tensored on the left with `M`, the product is determined by its value `cupH0` on degree-zero
classes and by the rule

`x ∪ δ y = (-1)^p δ (x ∪ y)` for `x` of degree `p`.

The sign is the standard one for a bigraded product compatible with connecting homomorphisms in
the second variable. For `q ≥ 0` the rule is applied upwards, with the upward shift of `N`, and for
`q < 0` downwards, with the downward shift of `N`; in each range the rule holds by construction
(`cup_dimensionShiftUpIso_hom`, `cup_dimensionShiftDownIso_hom`). That the rule holds for every
`k`-split short exact sequence in the second variable, the compatibility with connecting maps in
the first variable, associativity, graded commutativity and the compatibility with restriction are
the further properties of the product; they are not proved here.

The target degree of `cup` is a parameter `r` together with a proof of `p + q = r`, in the style of
Mathlib's `ShortComplex.ShortExact.δ`. The definition transports the degree produced by its
recursion to `r` along this proof, once, so that consumers can supply the target degree they need
together with the equality of degrees and never transport classes themselves.

In bidegree `(0, q)` the product is the existing product `cup0H` with a degree-zero class in the
first factor (`cup_zero_left`), because both satisfy the same rule for the dimension shifts.

## Main definitions

* `TauCeti.TateCohomology.cup`: the cup product
  `tateCohomology M p →ₗ[k] tateCohomology N q →ₗ[k] tateCohomology (M ⊗ N) r` for `p + q = r`.

## Main statements

* `TauCeti.TateCohomology.cup_zero_right`: in bidegree `(p, 0)` the product is `cupH0`.
* `TauCeti.TateCohomology.cup_zero_left`: in bidegree `(0, q)` the product is `cup0H`.
* `TauCeti.TateCohomology.cup_dimensionShiftUpIso_hom`,
  `TauCeti.TateCohomology.cup_dimensionShiftDownIso_hom`: the defining rule
  `x ∪ δ y = (-1)^p δ (x ∪ y)` for the upward shift when the second degree is nonnegative, and for
  the downward shift when it is negative.
* `TauCeti.TateCohomology.cup_map_left`: naturality in the first coefficient representation.

## References

* J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory*, Chapter IV (Atiyah–Wall),
  §7.
* K. S. Brown, *Cohomology of Groups*, Chapter VI, §5.
-/

public noncomputable section

universe u

open CategoryTheory MonoidalCategory Rep

namespace TauCeti.TateCohomology

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- `addNat p n = p + n`, by recursion on `n`, so that `addNat p 0` is `p` and `addNat p (n + 1)` is
`addNat p n + 1` definitionally. It indexes the target degrees of the recursion defining the cup
product with a class of nonnegative degree, whose base case is `cupH0`, landing in degree `p`. -/
private def addNat (p : ℤ) : ℕ → ℤ
  | 0 => p
  | n + 1 => addNat p n + 1

private theorem addNat_succ (p : ℤ) (n : ℕ) : addNat p (n + 1) = addNat p n + 1 :=
  rfl

private theorem addNat_eq (p : ℤ) (n : ℕ) : addNat p n = p + n := by
  induction n with
  | zero => simp [addNat]
  | succ n ih => simp [addNat, ih, add_assoc]

variable (M : Rep k G)

/-- The cup product with a class of nonnegative second degree `n`, by recursion on `n`: for `n = 0`
it is `cupH0`, and for `y` of degree `n + 1` it is `x ∪ y = (-1)^p δ (x ∪ δ⁻¹ y)`, with `δ⁻¹ y` in
degree `n` of the upward shift of `N`. -/
private def cupNonneg (p : ℤ) : (n : ℕ) → (N : Rep k G) →
    tateCohomology M p →ₗ[k] tateCohomology N n →ₗ[k] tateCohomology (M ⊗ N) (addNat p n)
  | 0, N => cupH0 M N p
  | n + 1, N => p.negOnePow •
      (((cupNonneg p n (dimensionShiftUp N)).compr₂
        (tensorDimensionShiftUpIso N M (addNat p n) (addNat p (n + 1))
          (addNat_succ p n).symm).hom.hom).compl₂ (dimensionShiftUpIso N n).inv.hom)

/-- The cup product with a class of negative second degree `-(n + 1)`, by recursion on `n`: for `y`
of degree `-(n + 1)` it is `x ∪ y = (-1)^p δ⁻¹ (x ∪ δ y)`, with `δ y` in degree `-n` of the
downward shift of `N`. -/
private def cupNeg (p : ℤ) : (n : ℕ) → (N : Rep k G) →
    tateCohomology M p →ₗ[k] tateCohomology N (Int.negSucc n) →ₗ[k]
      tateCohomology (M ⊗ N) (p - (n + 1 : ℕ))
  | 0, N => p.negOnePow •
      (((cupH0 M (dimensionShiftDown N) p).compr₂
        (tensorDimensionShiftDownIso N M (p - ((0 + 1 : ℕ) : ℤ)) p (by simp)).inv.hom).compl₂
          (dimensionShiftDownIso N (Int.negSucc 0)).hom.hom)
  | n + 1, N => p.negOnePow •
      (((cupNeg p n (dimensionShiftDown N)).compr₂
        (tensorDimensionShiftDownIso N M (p - ((n + 1 + 1 : ℕ) : ℤ)) (p - ((n + 1 : ℕ) : ℤ))
          (by push_cast; ring)).inv.hom).compl₂
            (dimensionShiftDownIso N (Int.negSucc (n + 1))).hom.hom)

variable (N : Rep k G)

/-- **The Tate cup product** `H^p(G, M) × H^q(G, N) → H^r(G, M ⊗ N)` for `p + q = r`, in all integer
bidegrees, as a `k`-bilinear map. In bidegree `(p, 0)` it is `cupH0` (`cup_zero_right`), and it is
determined from there by the rule `x ∪ δ y = (-1)^p δ (x ∪ y)` for the connecting maps of the
dimension-shifting sequences of `N` and of their tensor products with `M`
(`cup_dimensionShiftUpIso_hom`, `cup_dimensionShiftDownIso_hom`). -/
def cup (p q r : ℤ) (h : p + q = r) :
    tateCohomology M p →ₗ[k] tateCohomology N q →ₗ[k] tateCohomology (M ⊗ N) r :=
  match q, h with
  | .ofNat n, h => (cupNonneg M p n N).compr₂
      (eqToHom (congrArg (tateCohomology (M ⊗ N)) ((addNat_eq p n).trans h))).hom
  | .negSucc n, h => (cupNeg M p n N).compr₂
      (eqToHom (congrArg (tateCohomology (M ⊗ N)) (by rw [Int.negSucc_eq] at h; omega))).hom

/-!
The unfolding lemmas below are stated with the target degree in the form in which the recursion
produces it, so that the transport along an equality of degrees in the definition of `cup` is
along a reflexivity proof and disappears definitionally. Where a proof needs them at a second
degree such as `(n : ℤ) + 1` or `Int.negSucc n + 1`, which is of the form the recursion matches on
by definition but not syntactically, they are applied as terms through `LinearMap.congr_fun₂`,
which unifies up to definitional equality, rather than by `rw`.
-/

private theorem cup_natCast (p : ℤ) (n : ℕ) (h : p + n = addNat p n) :
    cup M N p n (addNat p n) h = cupNonneg M p n N :=
  rfl

private theorem cup_negSucc (p : ℤ) (n : ℕ) (h : p + Int.negSucc n = p - (n + 1 : ℕ)) :
    cup M N p (Int.negSucc n) (p - (n + 1 : ℕ)) h = cupNeg M p n N :=
  rfl

private theorem cupNonneg_succ_apply (p : ℤ) (n : ℕ) (x : tateCohomology M p)
    (y : tateCohomology N (n + 1 : ℕ)) :
    cupNonneg M p (n + 1) N x y =
      p.negOnePow • (tensorDimensionShiftUpIso N M (addNat p n) (addNat p (n + 1))
        (addNat_succ p n).symm).hom
          (cupNonneg M p n (dimensionShiftUp N) x ((dimensionShiftUpIso N n).inv y)) :=
  rfl

private theorem cupNeg_zero_apply (p : ℤ) (x : tateCohomology M p)
    (y : tateCohomology N (Int.negSucc 0)) :
    cupNeg M p 0 N x y =
      p.negOnePow • (tensorDimensionShiftDownIso N M (p - ((0 + 1 : ℕ) : ℤ)) p (by simp)).inv
        (cupH0 M (dimensionShiftDown N) p x ((dimensionShiftDownIso N (Int.negSucc 0)).hom y)) :=
  rfl

private theorem cupNeg_succ_apply (p : ℤ) (n : ℕ) (x : tateCohomology M p)
    (y : tateCohomology N (Int.negSucc (n + 1))) :
    cupNeg M p (n + 1) N x y =
      p.negOnePow • (tensorDimensionShiftDownIso N M (p - ((n + 1 + 1 : ℕ) : ℤ))
        (p - ((n + 1 : ℕ) : ℤ)) (by push_cast; ring)).inv
          (cupNeg M p n (dimensionShiftDown N) x
            ((dimensionShiftDownIso N (Int.negSucc (n + 1))).hom y)) :=
  rfl

-- This is the case `n = 0` of `cup_natCast`: `((0 : ℕ) : ℤ)` is `0`, `addNat p 0` is `p` and
-- `cupNonneg M p 0 N` is `cupH0 M N p`, each by definition.
/-- In bidegree `(p, 0)` the cup product is the product `cupH0` with a degree-zero class. -/
@[simp]
theorem cup_zero_right (p : ℤ) (h : p + 0 = p) : cup M N p 0 p h = cupH0 M N p :=
  cup_natCast M N p 0 h

/-- **The defining rule of the cup product for the upward dimension shift**: for `x` of degree `p`
and `y` of nonnegative degree `q` in `dimensionShiftUp N`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the
first `δ` is the shift `H^q(G, dimensionShiftUp N) ≅ H^(q+1)(G, N)` and the second is its tensor
product with `M`. -/
theorem cup_dimensionShiftUpIso_hom {p q r' r : ℤ} (hq : 0 ≤ q) (h' : p + q = r')
    (h : r' + 1 = r) (x : tateCohomology M p) (y : tateCohomology (dimensionShiftUp N) q) :
    cup M N p (q + 1) r (by omega) x ((dimensionShiftUpIso N q).hom y) =
      p.negOnePow • (tensorDimensionShiftUpIso N M r' r h).hom
        (cup M (dimensionShiftUp N) p q r' h' x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  obtain rfl : r' = addNat p n := by rw [addNat_eq]; omega
  obtain rfl : r = addNat p (n + 1) := by rw [addNat_eq]; push_cast; omega
  rw [cup_natCast M (dimensionShiftUp N) p n]
  refine (LinearMap.congr_fun₂ (cup_natCast M N p (n + 1) _) x _).trans ?_
  rw [cupNonneg_succ_apply, Iso.hom_inv_id_apply]

/-- **The defining rule of the cup product for the downward dimension shift**: for `x` of degree
`p` and `y` of negative degree `q` in `N`, `x ∪ δ y = (-1)^p δ (x ∪ y)`, where the first `δ` is the
shift `H^q(G, N) ≅ H^(q+1)(G, dimensionShiftDown N)` and the second is its tensor product with
`M`. -/
theorem cup_dimensionShiftDownIso_hom {p q r' r : ℤ} (hq : q < 0) (h' : p + q = r')
    (h : r' + 1 = r) (x : tateCohomology M p) (y : tateCohomology N q) :
    cup M (dimensionShiftDown N) p (q + 1) r (by omega) x ((dimensionShiftDownIso N q).hom y) =
      p.negOnePow • (tensorDimensionShiftDownIso N M r' r h).hom (cup M N p q r' h' x y) := by
  obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
  obtain rfl : r' = p - (n + 1 : ℕ) := by rw [Int.negSucc_eq] at h'; omega
  rw [cup_negSucc M N p n]
  cases n with
  | zero =>
    obtain rfl : p = r := by simp at h; omega
    rw [cupNeg_zero_apply, map_zsmul_unit, negOnePow_smul_negOnePow_smul,
      Iso.inv_hom_id_apply]
    -- `Int.negSucc 0 + 1` is `0` by definition, so the left-hand side is `cup` in bidegree
    -- `(p, 0)`.
    exact LinearMap.congr_fun₂ (cup_zero_right M (dimensionShiftDown N) p _) x _
  | succ n =>
    obtain rfl : r = p - (n + 1 : ℕ) := by push_cast at h ⊢; omega
    rw [cupNeg_succ_apply, map_zsmul_unit, negOnePow_smul_negOnePow_smul,
      Iso.inv_hom_id_apply]
    exact LinearMap.congr_fun₂ (cup_negSucc M (dimensionShiftDown N) p n _) x _

/-- The upward step in the proof of `cup_zero_left`: if `cup` agrees with `cup0H` in bidegree
`(0, q)` for the upward shift of `N`, where `0 ≤ q`, then it does in bidegree `(0, q + 1)` for
`N`. -/
private theorem cup_zero_left_add_one {q : ℤ} (hq : 0 ≤ q) (h : 0 + (q + 1) = q + 1)
    (ih : ∀ h : 0 + q = q,
      cup M (dimensionShiftUp N) 0 q q h = cup0H M (dimensionShiftUp N) q) :
    cup M N 0 (q + 1) (q + 1) h = cup0H M N (q + 1) := by
  ext x y
  obtain ⟨y, rfl⟩ : ∃ y', (dimensionShiftUpIso N q).hom y' = y :=
    ⟨(dimensionShiftUpIso N q).inv y, Iso.inv_hom_id_apply _ _⟩
  -- `δ_cup0H` for the upward dimension-shifting sequence of `N`, with the terms of the sequence
  -- and of its tensor product with `M` spelled out.
  have hδ := δ_cup0H M (S := ShortComplex.mk (coindBotUnit N) (dimensionShiftUpπ N)
      (coindBotUnit_comp_dimensionShiftUpπ N))
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_shortExact N)
    (by simpa only [dimensionShiftUpSES_def] using dimensionShiftUpSES_tensorLeft_shortExact N M)
    q x y
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
  rw [cup_dimensionShiftUpIso_hom M N hq (zero_add q) rfl, ih, Int.negOnePow_zero, one_smul,
    tensorDimensionShiftUpIso_hom, dimensionShiftUpIso_hom]
  exact hδ

/-- The downward step in the proof of `cup_zero_left`: if `cup` agrees with `cup0H` in bidegree
`(0, q + 1)` for the downward shift of `N`, where `q < 0`, then it does in bidegree `(0, q)` for
`N`. -/
private theorem cup_zero_left_of_add_one {q : ℤ} (hq : q < 0) (h : 0 + q = q)
    (ih : ∀ h : 0 + (q + 1) = q + 1,
      cup M (dimensionShiftDown N) 0 (q + 1) (q + 1) h = cup0H M (dimensionShiftDown N) (q + 1)) :
    cup M N 0 q q h = cup0H M N q := by
  ext x y
  refine (tensorDimensionShiftDownIso N M q (q + 1) rfl).toLinearEquiv.injective ?_
  have key := cup_dimensionShiftDownIso_hom M N hq h rfl x y
  rw [ih, Int.negOnePow_zero, one_smul] at key
  -- `δ_cup0H` for the downward dimension-shifting sequence of `N`, with the terms of the sequence
  -- and of its tensor product with `M` spelled out.
  have hδ := δ_cup0H M (S := ShortComplex.mk (dimensionShiftDownι N) (indBotCounit N)
      (dimensionShiftDownι_comp_indBotCounit N))
    (by simpa only [dimensionShiftDownSES_def] using dimensionShiftDownSES_shortExact N)
    (by simpa only [dimensionShiftDownSES_def] using
      dimensionShiftDownSES_tensorLeft_shortExact N M) q x y
  dsimp only [ShortComplex.map_X₁, ShortComplex.map_X₃] at hδ
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply, ← key, tensorDimensionShiftDownIso_hom,
    dimensionShiftDownIso_hom]
  exact hδ.symm

/-- In bidegree `(0, q)` the cup product is the product `cup0H` with a degree-zero class in the
first factor: both are `cupH0` in bidegree `(0, 0)` and both satisfy `x ∪ δ y = δ (x ∪ y)` for the
dimension shifts of the second variable. -/
@[simp]
theorem cup_zero_left (q : ℤ) (h : 0 + q = q) : cup M N 0 q q h = cup0H M N q := by
  rcases le_or_gt 0 q with hq | hq
  · induction q, hq using Int.leInduction generalizing N with
    | base => rw [cup_zero_right, cup0H_zero]
    | succ q hq ih => exact cup_zero_left_add_one M N hq h (ih (dimensionShiftUp N))
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    clear hq
    induction n generalizing N with
    | zero =>
      -- `Int.negSucc 0 + 1` is `0` by definition, so the hypothesis of the step is the bidegree
      -- `(0, 0)` case.
      exact cup_zero_left_of_add_one M N (Int.negSucc_lt_zero 0) h fun h ↦
        (cup_zero_right M (dimensionShiftDown N) 0 h).trans
          (cup0H_zero M (dimensionShiftDown N)).symm
    | succ n ih =>
      exact cup_zero_left_of_add_one M N (Int.negSucc_lt_zero _) h (ih (dimensionShiftDown N))

variable {M N}

/-- The cup product is natural in the first coefficient representation. -/
theorem cup_map_left {M' : Rep k G} (f : M ⟶ M') (p q r : ℤ) (h : p + q = r)
    (x : tateCohomology M p) (y : tateCohomology N q) :
    cup M' N p q r h ((tateCohomologyFunctor p).map f x) y =
      (tateCohomologyFunctor r).map (f ▷ N) (cup M N p q r h x y) := by
  rcases le_or_gt 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    obtain rfl : r = addNat p n := by rw [addNat_eq]; omega
    rw [cup_natCast, cup_natCast]
    clear h hq
    induction n generalizing N with
    | zero => exact cupH0_map_left f p x y
    | succ n ih =>
      rw [cupNonneg_succ_apply, cupNonneg_succ_apply, ih, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftUpIso_hom_naturality]
  · obtain ⟨n, rfl⟩ := Int.eq_negSucc_of_lt_zero hq
    obtain rfl : r = p - (n + 1 : ℕ) := by rw [Int.negSucc_eq] at h; omega
    rw [cup_negSucc, cup_negSucc]
    clear h hq
    induction n generalizing N with
    | zero =>
      rw [cupNeg_zero_apply, cupNeg_zero_apply, cupH0_map_left, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftDownIso_inv_naturality]
    | succ n ih =>
      rw [cupNeg_succ_apply, cupNeg_succ_apply, ih, Units.smul_def, Units.smul_def,
        map_zsmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
        tensorDimensionShiftDownIso_inv_naturality]

end TauCeti.TateCohomology
