/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries

/-!
# The graded pieces of the lower `p`-series

For a topological group `G` and `p : ℕ`, the lower `p`-series
`λ_k = TauCeti.pLowerCentralSeries p G k` is a descending chain of closed normal subgroups with
`λ_kᵖ ≤ λ_{k+1}` and `⁅λ_j, λ_k⁆ ≤ λ_{j+k+1}`. This file studies its successive quotients

  `gr_k(G) = λ_k ⧸ λ_{k+1}`,

written additively as `TauCeti.gradedPiece p G k`. Each `gr_k(G)` is an abelian group killed by
`p`, hence a `ZMod p`-module. The group commutator induces a biadditive bracket
`[·, ·] : gr_j(G) × gr_k(G) → gr_{j+k+1}(G)`, alternating and satisfying the Jacobi identity; the
degree shifts by one because the series is `0`-based. The `p`-th power induces the operator
`π : gr_k(G) → gr_{k+1}(G)`. Away from degree zero the operator `π` is additive and commutes with
the bracket, because the correction terms of the Hall–Petrescu formula land in higher degree; in
degree zero its defect of additivity is `(p choose 2) • [y, x]`, which vanishes for odd `p` and is
the bracket `[x, y]` for `p = 2`. A continuous homomorphism induces maps on the graded pieces that
are compatible with the bracket and with `π`.

For a prime `p`, the graded pieces of a topologically finitely generated profinite group are
finite; this is proved in `TauCeti.Topology.Algebra.Group.Profinite.ProP.LowerCentralSeries`.

## Main definitions

* `TauCeti.gradedPiece`: the graded piece `gr_k(G) = λ_k ⧸ λ_{k+1}`, written additively, with its
  `ZMod p`-module structure.
* `TauCeti.gradedMk`: the class in `gr_k(G)` of an element of `λ_k`.
* `TauCeti.gradedPieceInclusion`: the injection of `gr_k(G)` into `G ⧸ λ_{k+1}`, an isomorphism in
  degree zero (`TauCeti.gradedPieceZeroEquiv`).
* `TauCeti.gradedBracket`: the bracket `gr_j(G) →+ gr_k(G) →+ gr_{j+k+1}(G)`, and its
  `ZMod p`-bilinear form `TauCeti.gradedBracketLinear`.
* `TauCeti.gradedPow`: the `p`-power operator `π : gr_k(G) → gr_{k+1}(G)`, and its iterate
  `TauCeti.gradedPowIter` `π^j : gr_0(G) → gr_j(G)` on degree-zero classes.
* `TauCeti.gradedPowIterBracket`: the iterated `p`-power `π^m [ξ_g, ξ_h] ∈ gr_{m+1}(G)` of the
  bracket of two degree-zero classes, the class of `⁅g, h⁆ ^ (p ^ m)`.
* `TauCeti.gradedMap`: the map on graded pieces induced by a continuous homomorphism.

## Main results

* `TauCeti.quotientPLowerCentralSeriesSuccMulEquiv`: `λ_k ⧸ λ_{k+1}` is the quotient
  `λ_k ⧸ λ_kᵖ[λ_k, G]` of `λ_k` by one step of the lower `p`-series, through which `gr_k(G)`
  inherits its commutativity and its exponent.
* `TauCeti.natCard_quotient_pLowerCentralStep_eq_natCard_gradedPiece`: for a subgroup
  `R = λ_k`, the quotient `R ⧸ Rᵖ[R, G]` has as many elements as `gr_k(G)`.
* `TauCeti.gradedBracket_self`, `TauCeti.gradedBracket_jacobi`: the bracket is alternating and
  satisfies the Jacobi identity.
* `TauCeti.gradedPow_add_of_one_le`: `π` is additive in every degree `k ≥ 1`.
* `TauCeti.gradedPow_add_zero`, `TauCeti.gradedPow_add_zero_of_odd`,
  `TauCeti.gradedPow_add_zero_of_two`: in degree zero
  `π (x + y) = π x + π y + (p choose 2) • [y, x]`, so `π` is additive for odd `p`, and
  `π (x + y) = π x + π y + [x, y]` for `p = 2`.
* `TauCeti.gradedPow_gradedBracket_left`, `TauCeti.gradedPow_gradedBracket_right`:
  `π [x, y] = [π x, y] = [x, π y]` away from degree zero.
* `TauCeti.gradedMap_gradedBracket`, `TauCeti.gradedMap_gradedPow`: naturality of the bracket and
  of `π`.
* `TauCeti.gradedMap_symm_gradedMap`: the graded map of the inverse of a topological isomorphism
  inverts the graded map of the isomorphism.
* `MulEquiv.gradedPowIter_gradedMkZero_ne_zero_multiplicative_zmod_pow`: in a discrete group
  isomorphic to `ℤ/pⁿ⁺¹` with `1 < p`, `π^n` of the class of the generator is nonzero.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Congruences modulo the next term

The image of `λ_k` in `G ⧸ λ_{k+1}` is central, so conjugation acts trivially on it and the
commutator is bimultiplicative modulo `λ_{j+k+2}`. Computations combining congruences of different
degrees need these statements modulo an arbitrary coarser term `λ_{n'}`, `n' ≤ n`, as well. -/

/-- A congruence `mk a = mk b * mk c` modulo `λ_n` holds modulo every `λ_{n'}` with `n' ≤ n`. -/
theorem mk_eq_mk_mul_mk_of_le {a b c : G} {n : ℕ} (n' : ℕ) (h : n' ≤ n)
    (habc : ((a : G) : G ⧸ pLowerCentralSeries p G n) = (b : G ⧸ _) * (c : G ⧸ _)) :
    ((a : G) : G ⧸ pLowerCentralSeries p G n') = (b : G ⧸ _) * (c : G ⧸ _) := by
  rw [← QuotientGroup.mk_mul] at habc ⊢
  exact QuotientGroup.eq.mpr (pLowerCentralSeries_antitone h (QuotientGroup.eq.mp habc))

/-- The class in `G ⧸ λ_{n'}` of an element of `λ_n` is trivial as soon as `n' ≤ n`. -/
theorem mk_eq_one_of_mem_pLowerCentralSeries_of_le {n : ℕ} (n' : ℕ) {c : G}
    (hc : c ∈ pLowerCentralSeries p G n) (h : n' ≤ n) :
    ((c : G) : G ⧸ pLowerCentralSeries p G n') = 1 :=
  (QuotientGroup.eq_one_iff c).mpr (pLowerCentralSeries_antitone h hc)

/-- The class of an element of `λ_n` in `G ⧸ λ_{n'}` is central as soon as `n' ≤ n + 1`. -/
theorem commute_mk_of_mem_pLowerCentralSeries_of_le {n : ℕ} (n' : ℕ) {c : G}
    (hc : c ∈ pLowerCentralSeries p G n) (h : n' ≤ n + 1) (g : G) :
    Commute (g : G ⧸ pLowerCentralSeries p G n') (c : G ⧸ _) :=
  QuotientGroup.commute_mk_iff.mpr <| commutatorElement_inv c g ▸
    inv_mem (pLowerCentralSeries_antitone h (commutator_mem_pLowerCentralSeries_succ hc g))

/-- The class of an element of `λ_k` in `G ⧸ λ_{k+1}` commutes with every class. -/
theorem commute_mk_of_mem_pLowerCentralSeries {k : ℕ} {c : G} (hc : c ∈ pLowerCentralSeries p G k)
    (g : G) : Commute (g : G ⧸ pLowerCentralSeries p G (k + 1)) (c : G ⧸ _) :=
  commute_mk_of_mem_pLowerCentralSeries_of_le _ hc le_rfl g

/-- Conjugation acts trivially on the image of `λ_k` in `G ⧸ λ_{k+1}`. -/
theorem mk_conj_of_mem_pLowerCentralSeries {k : ℕ} {c : G} (hc : c ∈ pLowerCentralSeries p G k)
    (g : G) : ((g * c * g⁻¹ : G) : G ⧸ pLowerCentralSeries p G (k + 1)) = (c : G ⧸ _) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    (commute_mk_of_mem_pLowerCentralSeries hc g).eq, mul_inv_cancel_right]

/-- Modulo `λ_{j+k+2}`, the commutator `⁅x, ·⁆` of an element `x ∈ λ_j` is multiplicative on
`λ_k`. Only the second factor has to lie in `λ_k`. -/
theorem mk_commutatorElement_mul_right {j k : ℕ} {x y' : G} (hx : x ∈ pLowerCentralSeries p G j)
    (hy' : y' ∈ pLowerCentralSeries p G k) (y : G) :
    ((⁅x, y * y'⁆ : G) : G ⧸ pLowerCentralSeries p G (j + k + 1 + 1)) =
      ((⁅x, y⁆ : G) : G ⧸ _) * ((⁅x, y'⁆ : G) : G ⧸ _) := by
  have h : ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    rw [commutatorElement_mul_right_eq_mul_conj]; group
  rw [h, QuotientGroup.mk_mul,
    mk_conj_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries hx hy') y]

/-- Modulo `λ_{j+k+2}`, the commutator `⁅·, y⁆` of an element `y ∈ λ_k` is multiplicative on
`λ_j`. Only the second factor has to lie in `λ_j`. -/
theorem mk_commutatorElement_mul_left {j k : ℕ} {x' y : G} (hx' : x' ∈ pLowerCentralSeries p G j)
    (hy : y ∈ pLowerCentralSeries p G k) (x : G) :
    ((⁅x * x', y⁆ : G) : G ⧸ pLowerCentralSeries p G (j + k + 1 + 1)) =
      ((⁅x, y⁆ : G) : G ⧸ _) * ((⁅x', y⁆ : G) : G ⧸ _) := by
  have h : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul]
  rw [h, QuotientGroup.mk_mul,
    mk_conj_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries hx' hy) x,
    (commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries hx' hy) _).eq]

/-- The **Jacobi identity modulo `λ_{i+j+k+3}`**: for `a ∈ λ_i`, `b ∈ λ_j` and `c ∈ λ_k`, the
product of the three cyclic iterated commutators lies in `λ_{i+j+k+3}`. It is the Hall–Witt
identity, read modulo `λ_{i+j+k+3}`, where the conjugations it carries act trivially. -/
theorem commutatorElement_jacobi_mem_pLowerCentralSeries {i j k : ℕ} {a b c : G}
    (ha : a ∈ pLowerCentralSeries p G i) (hb : b ∈ pLowerCentralSeries p G j)
    (hc : c ∈ pLowerCentralSeries p G k) :
    ⁅⁅a, b⁆, c⁆ * ⁅⁅b, c⁆, a⁆ * ⁅⁅c, a⁆, b⁆ ∈ pLowerCentralSeries p G (i + j + k + 2 + 1) := by
  -- `⁅⁅u, v⁆, v * w * v⁻¹⁆ ≡ ⁅⁅u, v⁆, w⁆` modulo `λ_{i+j+k+3}`, for each cyclic permutation.
  have e {i' j' k' : ℕ} {u v w : G} (hs : i' + j' + k' = i + j + k)
      (hu : u ∈ pLowerCentralSeries p G i') (hv : v ∈ pLowerCentralSeries p G j')
      (hw : w ∈ pLowerCentralSeries p G k') :
      ((⁅⁅u, v⁆, v * w * v⁻¹⁆ : G) : G ⧸ pLowerCentralSeries p G (i + j + k + 2 + 1)) =
        ⁅⁅u, v⁆, w⁆ := by
    have huv := commutator_mem_pLowerCentralSeries hu hv
    rw [show v * w * v⁻¹ = ⁅v, w⁆ * w by group, mk_eq_mk_mul_mk_of_le (i + j + k + 2 + 1)
      (by omega) (mk_commutatorElement_mul_right huv hw _),
      mk_eq_one_of_mem_pLowerCentralSeries_of_le (i + j + k + 2 + 1)
        (commutator_mem_pLowerCentralSeries huv (commutator_mem_pLowerCentralSeries hv hw))
        (by omega), one_mul]
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    ← e (by omega) ha hb hc, ← e (by omega) hb hc ha, ← e (by omega) hc ha hb,
    ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, commutatorElement_commutatorElement_conj_mul,
    QuotientGroup.mk_one]

/-! ### The graded pieces -/

variable (p G) in
/-- **The graded piece** `gr_k(G) = λ_k ⧸ λ_{k+1}` of the lower `p`-series, written additively.
It is an abelian group killed by `p`, hence a `ZMod p`-module; for a prime `p` it is finite when
`G` is a topologically finitely generated profinite group, and not in general. -/
abbrev gradedPiece (k : ℕ) : Type u :=
  Additive (pLowerCentralSeries p G k ⧸
    (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k))

variable (p G) in
/-- The class in `gr_k(G)` of an element of `λ_k`. -/
def gradedMk (k : ℕ) (x : pLowerCentralSeries p G k) : gradedPiece p G k :=
  Additive.ofMul (QuotientGroup.mk x)

/-- The class of `x ∈ λ_k` in `gr_k(G)` is its class in the quotient `λ_k ⧸ λ_{k+1}`, read
additively: the unfolding equation of `TauCeti.gradedMk`, whose definition is sealed outside this
module. -/
theorem gradedMk_def (k : ℕ) (x : pLowerCentralSeries p G k) :
    gradedMk p G k x = Additive.ofMul (QuotientGroup.mk x) :=
  (rfl)

theorem gradedMk_surjective (k : ℕ) : Function.Surjective (gradedMk p G k) := fun x => by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x.toMul
  exact ⟨y, (congrArg Additive.ofMul hy).trans (ofMul_toMul x)⟩

/-- Two elements of `λ_k` have the same class in `gr_k(G)` if and only if they have the same class
in `G ⧸ λ_{k+1}`. -/
theorem gradedMk_eq_gradedMk_iff {k : ℕ} {x y : pLowerCentralSeries p G k} :
    gradedMk p G k x = gradedMk p G k y ↔
      ((x : G) : G ⧸ pLowerCentralSeries p G (k + 1)) = ((y : G) : G ⧸ _) := by
  rw [gradedMk, gradedMk, Additive.ofMul.apply_eq_iff_eq, QuotientGroup.eq_subgroupOf]

/-- The class of an element of `λ_k` in `gr_k(G)` vanishes if and only if the element lies in
`λ_{k+1}`. -/
@[simp]
theorem gradedMk_eq_zero_iff {k : ℕ} {x : pLowerCentralSeries p G k} :
    gradedMk p G k x = 0 ↔ (x : G) ∈ pLowerCentralSeries p G (k + 1) := by
  rw [gradedMk, ofMul_eq_zero, QuotientGroup.eq_one_iff, mem_subgroupOf]

@[simp]
theorem gradedMk_mul {k : ℕ} (x y : pLowerCentralSeries p G k) :
    gradedMk p G k (x * y) = gradedMk p G k x + gradedMk p G k y := by
  rw [gradedMk, gradedMk, gradedMk, QuotientGroup.mk_mul, ofMul_mul]

@[simp]
theorem gradedMk_one (k : ℕ) : gradedMk p G k 1 = 0 := by
  rw [gradedMk, QuotientGroup.mk_one, ofMul_one]

@[simp]
theorem gradedMk_inv {k : ℕ} (x : pLowerCentralSeries p G k) :
    gradedMk p G k x⁻¹ = -gradedMk p G k x := by
  rw [gradedMk, gradedMk, QuotientGroup.mk_inv, ofMul_inv]

@[simp]
theorem gradedMk_pow {k : ℕ} (x : pLowerCentralSeries p G k) (n : ℕ) :
    gradedMk p G k (x ^ n) = n • gradedMk p G k x := by
  rw [gradedMk, gradedMk, QuotientGroup.mk_pow, ofMul_pow]

@[simp]
theorem gradedMk_zpow {k : ℕ} (x : pLowerCentralSeries p G k) (n : ℤ) :
    gradedMk p G k (x ^ n) = n • gradedMk p G k x := by
  rw [gradedMk, gradedMk, QuotientGroup.mk_zpow, ofMul_zpow]

/-- The class of a product of elements of `λ_k` is the sum of their classes. -/
@[simp]
theorem gradedMk_list_prod {k : ℕ} (l : List (pLowerCentralSeries p G k)) :
    gradedMk p G k l.prod = (l.map (gradedMk p G k)).sum := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.sum_nil, gradedMk_one]
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.sum_cons, gradedMk_mul, ih]

variable (p G) in
/-- The quotient `λ_k ⧸ λ_{k+1}` is the quotient `λ_k ⧸ λ_kᵖ[λ_k, G]` of `λ_k` by one step of
the lower `p`-series, since `λ_{k+1} = λ_kᵖ[λ_k, G]`: the identity of `λ_k` descends to a group
isomorphism. Through it `gr_k(G)` inherits the commutativity and the exponent of `N ⧸ Nᵖ[N, G]`
(`TauCeti.instIsMulCommutativeQuotientPLowerCentralStep`,
`TauCeti.exponent_quotient_pLowerCentralStep_subgroupOf_dvd`). -/
def quotientPLowerCentralSeriesSuccMulEquiv (k : ℕ) :
    (pLowerCentralSeries p G k ⧸
        (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k)) ≃*
      (pLowerCentralSeries p G k ⧸
        (pLowerCentralStep p (pLowerCentralSeries p G k)).subgroupOf (pLowerCentralSeries p G k)) :=
  QuotientGroup.quotientMulEquivOfEq
    (congrArg (Subgroup.subgroupOf · _) (pLowerCentralSeries_succ p G k))

@[simp]
theorem quotientPLowerCentralSeriesSuccMulEquiv_mk (k : ℕ) (x : pLowerCentralSeries p G k) :
    quotientPLowerCentralSeriesSuccMulEquiv p G k (QuotientGroup.mk x) = QuotientGroup.mk x :=
  (rfl)

open scoped IsMulCommutative in
/-- The quotient `λ_k ⧸ λ_{k+1}` is an abelian group, with its existing quotient operations: it is
the commutative quotient `λ_k ⧸ λ_kᵖ[λ_k, G]`. -/
instance instCommGroupQuotientPLowerCentralSeries (k : ℕ) :
    CommGroup (pLowerCentralSeries p G k ⧸
      (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k)) where
  mul_comm a b :=
    (quotientPLowerCentralSeriesSuccMulEquiv p G k).injective <| by
      rw [map_mul, map_mul]
      exact mul_comm _ _

/-- **The graded pieces are killed by `p`**: the exponent of `λ_k ⧸ λ_kᵖ[λ_k, G]` divides `p`. -/
@[simp]
theorem nsmul_gradedPiece_eq_zero {k : ℕ} (x : gradedPiece p G k) : p • x = 0 := by
  rw [← ofMul_toMul x, ← ofMul_pow, ofMul_eq_zero]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    ((Monoid.exponent_eq_of_mulEquiv (quotientPLowerCentralSeriesSuccMulEquiv p G k)).dvd.trans
      (exponent_quotient_pLowerCentralStep_subgroupOf_dvd _)) _

/-- For odd `p`, the graded pieces are killed by `p choose 2 = p * ((p - 1) / 2)`. -/
theorem choose_two_nsmul_gradedPiece_eq_zero_of_odd (hp : Odd p) {k : ℕ}
    (x : gradedPiece p G k) : p.choose 2 • x = 0 := by
  rw [Nat.choose_two_right, Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd, mul_nsmul,
    nsmul_gradedPiece_eq_zero, nsmul_zero]

/-- The graded pieces are `ZMod p`-modules, with the canonical action on an abelian group killed
by `p`. -/
instance instModuleZModGradedPiece (k : ℕ) : Module (ZMod p) (gradedPiece p G k) :=
  AddCommGroup.zmodModule fun x => nsmul_gradedPiece_eq_zero x

/-- For a subgroup `R` equal to the term `λ_k` of the lower `p`-series, the quotient
`R ⧸ Rᵖ[R, G]` is the graded piece `gr_k(G) = λ_k ⧸ λ_{k+1}`, up to the additive notation; in
particular they have the same cardinality. The equation `R = λ_k` is a hypothesis rather than a
substitution, so that the statement applies to the relation subgroup of a presentation, whose
quotient type depends on it. -/
theorem natCard_quotient_pLowerCentralStep_eq_natCard_gradedPiece {R : Subgroup G}
    {k : ℕ} (hR : R = pLowerCentralSeries p G k) :
    Nat.card (R ⧸ (pLowerCentralStep p R).subgroupOf R) = Nat.card (gradedPiece p G k) := by
  subst hR
  exact Nat.card_congr
    ((quotientPLowerCentralSeriesSuccMulEquiv p G k).symm.toEquiv.trans Additive.ofMul)

/-! ### The inclusion into `G ⧸ λ_{k+1}` -/

variable (p G) in
/-- The injection of `gr_k(G) = λ_k ⧸ λ_{k+1}` into `G ⧸ λ_{k+1}`. -/
def gradedPieceInclusion (k : ℕ) :
    gradedPiece p G k →+ Additive (G ⧸ pLowerCentralSeries p G (k + 1)) :=
  MonoidHom.toAdditive (QuotientGroup.map _ _ (pLowerCentralSeries p G k).subtype
    fun _ hx => mem_comap.mpr (mem_subgroupOf.mp hx))

@[simp]
theorem gradedPieceInclusion_gradedMk {k : ℕ} (x : pLowerCentralSeries p G k) :
    gradedPieceInclusion p G k (gradedMk p G k x) =
      Additive.ofMul ((x : G) : G ⧸ pLowerCentralSeries p G (k + 1)) := by
  rw [gradedPieceInclusion, gradedMk, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.map_mk, coe_subtype]

theorem gradedPieceInclusion_injective (k : ℕ) :
    Function.Injective (gradedPieceInclusion p G k) := by
  rw [gradedPieceInclusion, MonoidHom.coe_toAdditive]
  exact (Additive.ofMul.injective.comp (TauCeti.QuotientGroup.map_injective_of_eq_comap _ _
    (comap_subtype _ _).symm)).comp Additive.toMul.injective

theorem gradedPieceInclusion_zero_surjective :
    Function.Surjective (gradedPieceInclusion p G 0) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.toMul
  refine ⟨gradedMk p G 0 ⟨g, mem_pLowerCentralSeries_zero p g⟩, ?_⟩
  rw [gradedPieceInclusion_gradedMk, coe_mk, hg, ofMul_toMul]

variable (p G) in
/-- **The degree-zero piece is `G ⧸ λ_1`.** For a profinite group and a prime `p`, `λ_1` is the
pro-`p` Frattini subgroup, so `gr_0(G)` is the Frattini quotient. -/
noncomputable def gradedPieceZeroEquiv :
    gradedPiece p G 0 ≃+ Additive (G ⧸ pLowerCentralSeries p G 1) :=
  AddEquiv.ofBijective (gradedPieceInclusion p G 0)
    ⟨gradedPieceInclusion_injective 0, gradedPieceInclusion_zero_surjective⟩

-- Not `@[simp]`: `gradedMk_zero` rewrites the argument to a `gradedMkZero`, after which
-- `gradedPieceZeroEquiv_gradedMkZero` applies, so `simp` proves this lemma.
theorem gradedPieceZeroEquiv_gradedMk (x : pLowerCentralSeries p G 0) :
    gradedPieceZeroEquiv p G (gradedMk p G 0 x) =
      Additive.ofMul ((x : G) : G ⧸ pLowerCentralSeries p G 1) :=
  gradedPieceInclusion_gradedMk x

/-! ### The class of an element of `G` in degree zero -/

variable (p G) in
/-- **The class in degree zero** of an element of `G`: every element lies in `λ_0 = G`, and
`gradedMkZero p G g` is its class in `gr_0(G) = G ⧸ λ_1`. -/
def gradedMkZero (g : G) : gradedPiece p G 0 :=
  gradedMk p G 0 ⟨g, mem_pLowerCentralSeries_zero p g⟩

/-- The class map from a topological group to degree zero of its lower `p`-series is continuous. -/
theorem continuous_gradedMkZero : Continuous (gradedMkZero p G) := by
  unfold gradedMkZero gradedMk
  exact continuous_quotient_mk'.comp (continuous_id.subtype_mk _)

/-- The class in degree zero of an element of `λ_0` is the class of the underlying element. -/
@[simp]
theorem gradedMk_zero (x : pLowerCentralSeries p G 0) :
    gradedMk p G 0 x = gradedMkZero p G x := by
  rw [gradedMkZero]

theorem gradedMkZero_surjective : Function.Surjective (gradedMkZero p G) := fun x => by
  obtain ⟨y, rfl⟩ := gradedMk_surjective 0 x
  exact ⟨y, (gradedMk_zero y).symm⟩

/-- Two elements of `G` have the same class in `gr_0(G)` if and only if they have the same class
in `G ⧸ λ_1`. -/
theorem gradedMkZero_eq_gradedMkZero_iff {g h : G} :
    gradedMkZero p G g = gradedMkZero p G h ↔
      (g : G ⧸ pLowerCentralSeries p G 1) = (h : G ⧸ pLowerCentralSeries p G 1) := by
  rw [gradedMkZero, gradedMkZero, gradedMk_eq_gradedMk_iff]

/-- The class of an element in `gr_0(G)` vanishes if and only if the element lies in `λ_1`. -/
@[simp]
theorem gradedMkZero_eq_zero_iff {g : G} :
    gradedMkZero p G g = 0 ↔ g ∈ pLowerCentralSeries p G 1 := by
  rw [gradedMkZero, gradedMk_eq_zero_iff]

@[simp]
theorem gradedMkZero_mul (g h : G) :
    gradedMkZero p G (g * h) = gradedMkZero p G g + gradedMkZero p G h := by
  rw [← gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero p g⟩,
    ← gradedMk_zero ⟨h, mem_pLowerCentralSeries_zero p h⟩, ← gradedMk_mul]
  exact gradedMk_zero _

@[simp]
theorem gradedMkZero_one : gradedMkZero p G 1 = 0 := by
  rw [gradedMkZero_eq_zero_iff]
  exact one_mem _

@[simp]
theorem gradedMkZero_inv (g : G) : gradedMkZero p G g⁻¹ = -gradedMkZero p G g := by
  rw [← gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero p g⟩, ← gradedMk_inv]
  exact gradedMk_zero _

@[simp]
theorem gradedMkZero_pow (g : G) (n : ℕ) : gradedMkZero p G (g ^ n) = n • gradedMkZero p G g := by
  rw [← gradedMk_zero ⟨g, mem_pLowerCentralSeries_zero p g⟩, ← gradedMk_pow]
  exact gradedMk_zero _

/-- The degree-zero class of a product of elements of `G` is the sum of their classes. -/
@[simp]
theorem gradedMkZero_list_prod (l : List G) :
    gradedMkZero p G l.prod = (l.map (gradedMkZero p G)).sum := by
  induction l with
  | nil => rw [List.prod_nil, List.map_nil, List.sum_nil, gradedMkZero_one]
  | cons a l ih => rw [List.prod_cons, List.map_cons, List.sum_cons, gradedMkZero_mul, ih]

-- Not `@[simp]`: `gradedMkZero_mul` and `gradedMkZero_inv` already rewrite the left-hand side.
/-- The degree-zero class is invariant under conjugation, since `gr_0(G)` is abelian. -/
theorem gradedMkZero_conj (c g : G) : gradedMkZero p G (c⁻¹ * g * c) = gradedMkZero p G g := by
  simp only [gradedMkZero_mul, gradedMkZero_inv, neg_add_cancel_comm]

@[simp]
theorem gradedPieceZeroEquiv_gradedMkZero (g : G) :
    gradedPieceZeroEquiv p G (gradedMkZero p G g) =
      Additive.ofMul (g : G ⧸ pLowerCentralSeries p G 1) := by
  rw [gradedMkZero, gradedPieceZeroEquiv_gradedMk]

/-! ### Transport along an equality of degrees -/

variable (p G) in
/-- Transport along an equality of degrees. The bracket and the `p`-power operator compose into
different but equal degree expressions, so the Jacobi identity and the identities relating `π` to
the bracket are stated through this map. -/
def gradedCast {j k : ℕ} (h : j = k) : gradedPiece p G j → gradedPiece p G k := fun x => h ▸ x

@[simp]
theorem gradedCast_rfl {k : ℕ} (x : gradedPiece p G k) : gradedCast p G rfl x = x := by
  rw [gradedCast]

@[simp]
theorem gradedCast_gradedMk {j k : ℕ} (h : j = k) (x : pLowerCentralSeries p G j) :
    gradedCast p G h (gradedMk p G j x) = gradedMk p G k ⟨x, h ▸ x.2⟩ := by
  subst h; rfl

@[simp]
theorem gradedCast_add {j k : ℕ} (h : j = k) (x y : gradedPiece p G j) :
    gradedCast p G h (x + y) = gradedCast p G h x + gradedCast p G h y := by
  subst h; rfl

@[simp]
theorem gradedCast_neg {j k : ℕ} (h : j = k) (x : gradedPiece p G j) :
    gradedCast p G h (-x) = -gradedCast p G h x := by
  subst h; rfl

@[simp]
theorem gradedCast_zero {j k : ℕ} (h : j = k) : gradedCast p G h (0 : gradedPiece p G j) = 0 := by
  subst h; rfl

/-! ### The bracket -/

section Bracket

variable (p G)

/-- The bracket with a fixed element of `λ_j`, on `λ_k`, before passing to the quotient. -/
private def bracketAux (j k : ℕ) (x : pLowerCentralSeries p G j) :
    pLowerCentralSeries p G k →*
      (pLowerCentralSeries p G (j + k + 1) ⧸
        (pLowerCentralSeries p G (j + k + 1 + 1)).subgroupOf
          (pLowerCentralSeries p G (j + k + 1))) where
  toFun y := QuotientGroup.mk ⟨⁅(x : G), (y : G)⁆, commutator_mem_pLowerCentralSeries x.2 y.2⟩
  map_one' := by
    rw [← QuotientGroup.mk_one]
    congr 1
    ext
    simp
  map_mul' y y' := by
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_subgroupOf]
    simp only [coe_mul, QuotientGroup.mk_mul]
    exact mk_commutatorElement_mul_right x.2 y'.2 y

private theorem bracketAux_apply (j k : ℕ) (x : pLowerCentralSeries p G j)
    (y : pLowerCentralSeries p G k) :
    bracketAux p G j k x y =
      QuotientGroup.mk ⟨⁅(x : G), (y : G)⁆, commutator_mem_pLowerCentralSeries x.2 y.2⟩ :=
  rfl

private theorem subgroupOf_le_ker_bracketAux (j k : ℕ) (x : pLowerCentralSeries p G j) :
    (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k) ≤
      (bracketAux p G j k x).ker := by
  intro y hy
  rw [MonoidHom.mem_ker, bracketAux_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, coe_mk]
  exact commutator_mem_pLowerCentralSeries (j := j) (k := k + 1) x.2 (mem_subgroupOf.mp hy)

/-- The bracket with a fixed element of `λ_j`, as an additive map `gr_k(G) →+ gr_{j+k+1}(G)`. -/
private def bracketRight (j k : ℕ) (x : pLowerCentralSeries p G j) :
    gradedPiece p G k →+ gradedPiece p G (j + k + 1) :=
  MonoidHom.toAdditive
    (QuotientGroup.lift _ (bracketAux p G j k x) (subgroupOf_le_ker_bracketAux p G j k x))

private theorem bracketRight_gradedMk (j k : ℕ) (x : pLowerCentralSeries p G j)
    (y : pLowerCentralSeries p G k) :
    bracketRight p G j k x (gradedMk p G k y) =
      gradedMk p G (j + k + 1)
        ⟨⁅(x : G), (y : G)⁆, commutator_mem_pLowerCentralSeries x.2 y.2⟩ := by
  rw [bracketRight, gradedMk, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.lift_mk, bracketAux_apply, gradedMk]

/-- The bracket as a homomorphism from `λ_j`, before passing to the quotient. -/
private def bracketLeftAux (j k : ℕ) :
    pLowerCentralSeries p G j →*
      Multiplicative (gradedPiece p G k →+ gradedPiece p G (j + k + 1)) where
  toFun x := Multiplicative.ofAdd (bracketRight p G j k x)
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    refine AddMonoidHom.ext fun y => ?_
    obtain ⟨y, rfl⟩ := gradedMk_surjective k y
    rw [bracketRight_gradedMk, AddMonoidHom.zero_apply, gradedMk_eq_zero_iff, coe_mk]
    simp
  map_mul' x x' := by
    rw [← ofAdd_add]
    congr 1
    refine AddMonoidHom.ext fun y => ?_
    obtain ⟨y, rfl⟩ := gradedMk_surjective k y
    rw [AddMonoidHom.add_apply, bracketRight_gradedMk, bracketRight_gradedMk,
      bracketRight_gradedMk, ← gradedMk_mul, gradedMk_eq_gradedMk_iff]
    simp only [coe_mul, QuotientGroup.mk_mul]
    exact mk_commutatorElement_mul_left x'.2 y.2 x

private theorem bracketLeftAux_apply (j k : ℕ) (x : pLowerCentralSeries p G j) :
    bracketLeftAux p G j k x = Multiplicative.ofAdd (bracketRight p G j k x) :=
  rfl

private theorem subgroupOf_le_ker_bracketLeftAux (j k : ℕ) :
    (pLowerCentralSeries p G (j + 1)).subgroupOf (pLowerCentralSeries p G j) ≤
      (bracketLeftAux p G j k).ker := by
  intro x hx
  rw [MonoidHom.mem_ker, bracketLeftAux_apply, ← ofAdd_zero]
  congr 1
  refine AddMonoidHom.ext fun y => ?_
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [bracketRight_gradedMk, AddMonoidHom.zero_apply, gradedMk_eq_zero_iff, coe_mk]
  exact pLowerCentralSeries_antitone (by omega)
    (commutator_mem_pLowerCentralSeries (mem_subgroupOf.mp hx) y.2)

/-- **The bracket** `[·, ·] : gr_j(G) →+ gr_k(G) →+ gr_{j+k+1}(G)`, induced by the group
commutator `⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`. The degree shifts by one because the series is
`0`-based. Its defining equation is `TauCeti.gradedBracket_gradedMk`. -/
def gradedBracket (j k : ℕ) :
    gradedPiece p G j →+ gradedPiece p G k →+ gradedPiece p G (j + k + 1) :=
  MonoidHom.toAdditiveLeft
    (QuotientGroup.lift _ (bracketLeftAux p G j k) (subgroupOf_le_ker_bracketLeftAux p G j k))

variable {p G}

/-- **The bracket on classes**: the defining equation of `TauCeti.gradedBracket`. -/
@[simp]
theorem gradedBracket_gradedMk {j k : ℕ} (x : pLowerCentralSeries p G j)
    (y : pLowerCentralSeries p G k) :
    gradedBracket p G j k (gradedMk p G j x) (gradedMk p G k y) =
      gradedMk p G (j + k + 1)
        ⟨⁅(x : G), (y : G)⁆, commutator_mem_pLowerCentralSeries x.2 y.2⟩ := by
  rw [gradedBracket, gradedMk, MonoidHom.toAdditiveLeft_apply_apply, toMul_ofMul,
    QuotientGroup.lift_mk]
  exact bracketRight_gradedMk p G j k x y

/-- **The bracket of two degree-zero classes**, as the class of the commutator in `gr_1(G)`. -/
@[simp]
theorem gradedBracket_gradedMkZero (g h : G) :
    gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G h) =
      gradedMk p G 1 ⟨⁅g, h⁆, commutator_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)
        (mem_pLowerCentralSeries_zero p h)⟩ := by
  rw [gradedMkZero, gradedMkZero, gradedBracket_gradedMk]

variable (p G) in
/-- **The bracket as a `ZMod p`-bilinear map**
`gr_j(G) →ₗ[ZMod p] gr_k(G) →ₗ[ZMod p] gr_{j+k+1}(G)`: the biadditive bracket
`TauCeti.gradedBracket` is automatically `ZMod p`-bilinear. -/
def gradedBracketLinear (j k : ℕ) :
    gradedPiece p G j →ₗ[ZMod p] gradedPiece p G k →ₗ[ZMod p] gradedPiece p G (j + k + 1) :=
  LinearMap.mk₂ (ZMod p) (fun x y => gradedBracket p G j k x y)
    (fun x₁ x₂ y => by rw [map_add, AddMonoidHom.add_apply])
    (fun c x y => map_smul (((gradedBracket p G j k).flip y).toZModLinearMap p) c x)
    (fun x y₁ y₂ => map_add _ y₁ y₂)
    (fun c x y => map_smul ((gradedBracket p G j k x).toZModLinearMap p) c y)

@[simp]
theorem gradedBracketLinear_apply {j k : ℕ} (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedBracketLinear p G j k x y = gradedBracket p G j k x y :=
  (rfl)

/-- **The bracket is alternating**: `[x, x] = 0` in every degree. -/
@[simp]
theorem gradedBracket_self {k : ℕ} (x : gradedPiece p G k) : gradedBracket p G k k x x = 0 := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedBracket_gradedMk, gradedMk_eq_zero_iff, coe_mk, commutatorElement_self]
  exact one_mem _

/-- **The bracket of a commutative group vanishes** in every degree, since it is the class of a
commutator. -/
@[simp]
theorem gradedBracket_eq_zero_of_isMulCommutative [IsMulCommutative G] {j k : ℕ}
    (x : gradedPiece p G j) (y : gradedPiece p G k) : gradedBracket p G j k x y = 0 := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk, gradedMk_eq_zero_iff, coe_mk,
    commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)]
  exact one_mem _

/-- **Skew-symmetry**: `[y, x] = -[x, y]`, transported to a common degree. -/
theorem gradedCast_gradedBracket_swap {j k : ℕ} (x : gradedPiece p G j) (y : gradedPiece p G k) :
    gradedCast p G (by omega) (gradedBracket p G k j y x) = -gradedBracket p G j k x y := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk, gradedBracket_gradedMk, gradedCast_gradedMk, ← gradedMk_inv,
    gradedMk_eq_gradedMk_iff, coe_mk, coe_inv, coe_mk, commutatorElement_inv]

/-- **The Jacobi identity**, with the three terms transported to the degree `i + j + k + 2`. -/
theorem gradedBracket_jacobi {i j k : ℕ} (x : gradedPiece p G i) (y : gradedPiece p G j)
    (z : gradedPiece p G k) :
    gradedCast p G (by omega)
        (gradedBracket p G (i + j + 1) k (gradedBracket p G i j x y) z) +
      gradedCast p G (by omega)
        (gradedBracket p G (j + k + 1) i (gradedBracket p G j k y z) x) +
      gradedCast p G (by omega)
        (gradedBracket p G (k + i + 1) j (gradedBracket p G k i z x) y) =
      (0 : gradedPiece p G (i + j + k + 2)) := by
  obtain ⟨a, rfl⟩ := gradedMk_surjective i x
  obtain ⟨b, rfl⟩ := gradedMk_surjective j y
  obtain ⟨c, rfl⟩ := gradedMk_surjective k z
  simp only [gradedBracket_gradedMk, gradedCast_gradedMk, ← gradedMk_mul, gradedMk_eq_zero_iff,
    coe_mul]
  exact commutatorElement_jacobi_mem_pLowerCentralSeries a.2 b.2 c.2

end Bracket

/-! ### The `p`-power operator -/

section Pow

variable (p G)

/-- **The `p`-power operator** `π : gr_k(G) → gr_{k+1}(G)`, induced by `x ↦ x ^ p`. It is
additive in every degree `k ≥ 1` (`TauCeti.gradedPow_add_of_one_le`); in degree zero its defect of
additivity is `(p choose 2) • [y, x]` (`TauCeti.gradedPow_add_zero`), which vanishes for odd `p`
(`TauCeti.gradedPow_add_zero_of_odd`) and is the bracket `[x, y]` for `p = 2`
(`TauCeti.gradedPow_add_zero_of_two`). Its defining equation is `TauCeti.gradedPow_gradedMk`. -/
def gradedPow (k : ℕ) : gradedPiece p G k → gradedPiece p G (k + 1) := fun x =>
  Additive.ofMul (Quotient.map'
    (fun y : pLowerCentralSeries p G k =>
      (⟨(y : G) ^ p, pow_mem_pLowerCentralSeries y.2⟩ : pLowerCentralSeries p G (k + 1)))
    (fun y y' h => by
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf, coe_mul, coe_inv] at h ⊢
      dsimp only
      obtain ⟨z, hz, hy'⟩ : ∃ z ∈ pLowerCentralSeries p G (k + 1), (y' : G) = y * z :=
        ⟨_, h, by group⟩
      rw [← QuotientGroup.eq, hy', QuotientGroup.mk_pow, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.commute_mk_iff.mpr (pLowerCentralSeries_antitone (by omega)
          (commutator_mem_pLowerCentralSeries y.2 hz))).mul_pow, ← QuotientGroup.mk_pow _ z,
        (QuotientGroup.eq_one_iff _).mpr (pow_mem_pLowerCentralSeries hz), mul_one])
    x.toMul)

variable {p G}

/-- **The `p`-power operator on classes**: the defining equation of `TauCeti.gradedPow`. -/
@[simp]
theorem gradedPow_gradedMk {k : ℕ} (x : pLowerCentralSeries p G k) :
    gradedPow p G k (gradedMk p G k x) =
      gradedMk p G (k + 1) ⟨(x : G) ^ p, pow_mem_pLowerCentralSeries x.2⟩ := by
  rw [gradedPow, gradedMk, toMul_ofMul, gradedMk]
  rfl

@[simp]
theorem gradedPow_zero (k : ℕ) : gradedPow p G k 0 = 0 := by
  rw [← gradedMk_one k, gradedPow_gradedMk, gradedMk_eq_zero_iff, coe_mk, OneMemClass.coe_one,
    one_pow]
  exact one_mem _

/-- **The `p`-power operator on a degree-zero class**, as the class of the `p`-th power in
`gr_1(G)`. -/
@[simp]
theorem gradedPow_gradedMkZero (g : G) :
    gradedPow p G 0 (gradedMkZero p G g) =
      gradedMk p G 1 ⟨g ^ p, pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)⟩ := by
  rw [gradedMkZero, gradedPow_gradedMk]

/-- **`π` commutes with integer multiples**, in every degree and for every `p`: on classes it is
`(x ^ n) ^ p = (x ^ p) ^ n`. -/
@[simp]
theorem gradedPow_zsmul {k : ℕ} (n : ℤ) (x : gradedPiece p G k) :
    gradedPow p G k (n • x) = n • gradedPow p G k x := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [← gradedMk_zpow, gradedPow_gradedMk, gradedPow_gradedMk, ← gradedMk_zpow]
  congr 1
  exact Subtype.ext (by simp only [SubgroupClass.coe_zpow, ← zpow_natCast, ← zpow_mul, mul_comm])

/-- **`π` commutes with natural multiples**, in every degree and for every `p`. -/
@[simp]
theorem gradedPow_nsmul {k : ℕ} (n : ℕ) (x : gradedPiece p G k) :
    gradedPow p G k (n • x) = n • gradedPow p G k x := by
  rw [← natCast_zsmul, gradedPow_zsmul, natCast_zsmul]

/-- **`π` commutes with negation**, in every degree and for every `p`. -/
@[simp]
theorem gradedPow_neg {k : ℕ} (x : gradedPiece p G k) :
    gradedPow p G k (-x) = -gradedPow p G k x := by
  rw [← neg_one_zsmul x, gradedPow_zsmul, neg_one_zsmul]

/-- **`π` commutes with scalars**, in every degree and for every `p`. -/
@[simp]
theorem gradedPow_smul {k : ℕ} (c : ZMod p) (x : gradedPiece p G k) :
    gradedPow p G k (c • x) = c • gradedPow p G k x := by
  rw [← ZMod.intCast_zmod_cast c, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, gradedPow_zsmul]

/-- **The class of a `p`-power in `gr_1(G)`**: the class of `g ^ (p * c)` is `c` times the
`p`-power class `π ⟦g⟧`. -/
theorem gradedMk_pow_mul (g : G) (c : ℕ) (h : g ^ (p * c) ∈ pLowerCentralSeries p G 1) :
    gradedMk p G 1 ⟨g ^ (p * c), h⟩ = c • gradedPow p G 0 (gradedMkZero p G g) := by
  have : (⟨g ^ (p * c), h⟩ : pLowerCentralSeries p G 1) =
      ⟨g ^ p, pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g)⟩ ^ c :=
    Subtype.ext (by simp [pow_mul])
  rw [this, gradedMk_pow, gradedPow_gradedMkZero]

/-- **`π` is additive above degree zero**, for every `p`: for `k ≥ 1` the image of `λ_k` in
`G ⧸ λ_{k+2}` is abelian, because `⁅λ_k, λ_k⁆ ≤ λ_{2k+1} ≤ λ_{k+2}`. -/
@[simp]
theorem gradedPow_add_of_one_le {k : ℕ} (hk : 1 ≤ k) (x y : gradedPiece p G k) :
    gradedPow p G k (x + y) = gradedPow p G k x + gradedPow p G k y := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [← gradedMk_mul, gradedPow_gradedMk, gradedPow_gradedMk, gradedPow_gradedMk, ← gradedMk_mul,
    gradedMk_eq_gradedMk_iff]
  simp only [coe_mul, QuotientGroup.mk_pow, QuotientGroup.mk_mul]
  exact (QuotientGroup.commute_mk_iff.mpr (pLowerCentralSeries_antitone (by omega)
    (commutator_mem_pLowerCentralSeries x.2 y.2))).mul_pow p

variable (p G) in
/-- **The `p`-power operator above degree zero, as an additive map** `gr_k(G) →+ gr_{k+1}(G)`, for
`k ≥ 1`, where `π` is additive (`TauCeti.gradedPow_add_of_one_le`). -/
def gradedPowAddMonoidHom {k : ℕ} (hk : 1 ≤ k) : gradedPiece p G k →+ gradedPiece p G (k + 1) :=
  AddMonoidHom.mk' (gradedPow p G k) (gradedPow_add_of_one_le hk)

@[simp]
theorem gradedPowAddMonoidHom_apply {k : ℕ} (hk : 1 ≤ k) (x : gradedPiece p G k) :
    gradedPowAddMonoidHom p G hk x = gradedPow p G k x :=
  (rfl)

/-- **The defect of additivity in degree zero**: `π (x + y) = π x + π y + (p choose 2) • [y, x]`
in `gr_1(G)`. This is the binomial formula `(x * y) ^ p = x ^ p * y ^ p * ⁅y, x⁆ ^ (p choose 2)` of
nilpotency class two, read in `G ⧸ λ_2`, where the image of `λ_1` is central. -/
theorem gradedPow_add_zero (x y : gradedPiece p G 0) :
    gradedPow p G 0 (x + y) =
      gradedPow p G 0 x + gradedPow p G 0 y + p.choose 2 • gradedBracket p G 0 0 y x := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective 0 x
  obtain ⟨y, rfl⟩ := gradedMk_surjective 0 y
  rw [← gradedMk_mul, gradedPow_gradedMk, gradedPow_gradedMk, gradedPow_gradedMk,
    gradedBracket_gradedMk, ← gradedMk_pow, ← gradedMk_mul, ← gradedMk_mul,
    gradedMk_eq_gradedMk_iff]
  simp only [coe_mul, coe_pow, ← QuotientGroup.mk'_apply, map_mul, map_pow, map_commutatorElement]
  exact Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two
    (commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries_succ y.2 x) x)
    (commute_mk_of_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries_succ y.2 x) y) p

/-- **`π` is additive in degree zero for odd `p`**: the defect `(p choose 2) • [y, x]` is a
multiple of `p • [y, x] = 0`. -/
@[simp]
theorem gradedPow_add_zero_of_odd (hp : Odd p) (x y : gradedPiece p G 0) :
    gradedPow p G 0 (x + y) = gradedPow p G 0 x + gradedPow p G 0 y := by
  rw [gradedPow_add_zero, choose_two_nsmul_gradedPiece_eq_zero_of_odd hp, add_zero]

/-- **The dyadic defect of additivity in degree zero.** For `p = 2`,
`π (x + y) = π x + π y + [x, y]` in `gr_1(G)`: the defect is the `binom(2, 2)` term of the
Hall–Petrescu formula itself. Whenever some bracket `[x, y]` in degree zero is nonzero, `π` is
therefore not additive on `gr_0(G)`, so `gr(G)` carries no `𝔽₂[π]`-module structure in which `π`
acts by `TauCeti.gradedPow`. -/
@[simp]
theorem gradedPow_add_zero_of_two (hp : p = 2) (x y : gradedPiece p G 0) :
    gradedPow p G 0 (x + y) =
      gradedPow p G 0 x + gradedPow p G 0 y + gradedBracket p G 0 0 x y := by
  subst hp
  rw [gradedPow_add_zero, Nat.choose_self, one_nsmul]
  congr 1
  -- Since `gr_1(G)` is killed by `2`, `[y, x] = -[x, y] = [x, y]`.
  have h := gradedCast_gradedBracket_swap x y
  rw [gradedCast_rfl] at h
  rw [h, neg_eq_iff_add_eq_zero]
  exact (two_nsmul _).symm.trans (nsmul_gradedPiece_eq_zero _)

/-- **`π` against the bracket on the left**, away from degree zero: `π [x, y] = [π x, y]` for
`x ∈ gr_j(G)` with `j ≥ 1`. The correction term `⁅x, ⁅x, y⁆⁆` has degree `2j + k + 2`, which is
above `j + k + 2` exactly when `j ≥ 1`. -/
theorem gradedPow_gradedBracket_left {j k : ℕ} (hj : 1 ≤ j) (x : gradedPiece p G j)
    (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G (j + 1) k (gradedPow p G j x) y) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk, gradedPow_gradedMk, gradedPow_gradedMk, gradedBracket_gradedMk,
    gradedCast_gradedMk, gradedMk_eq_gradedMk_iff]
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow]
  exact (QuotientGroup.commute_mk_iff.mpr (pLowerCentralSeries_antitone (by omega)
    (commutator_mem_pLowerCentralSeries x.2
      (commutator_mem_pLowerCentralSeries x.2 y.2)))).commutatorElement_pow_left p

/-- **`π` against the bracket on the right**, away from degree zero: `π [x, y] = [x, π y]` for
`y ∈ gr_k(G)` with `k ≥ 1`. -/
theorem gradedPow_gradedBracket_right {j k : ℕ} (hk : 1 ≤ k) (x : gradedPiece p G j)
    (y : gradedPiece p G k) :
    gradedPow p G (j + k + 1) (gradedBracket p G j k x y) =
      gradedCast p G (by omega) (gradedBracket p G j (k + 1) x (gradedPow p G k y)) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk, gradedPow_gradedMk, gradedPow_gradedMk, gradedBracket_gradedMk,
    gradedCast_gradedMk, gradedMk_eq_gradedMk_iff]
  simp only [← QuotientGroup.mk'_apply, map_commutatorElement, map_pow]
  exact (QuotientGroup.commute_mk_iff.mpr (pLowerCentralSeries_antitone (by omega)
    (commutator_mem_pLowerCentralSeries y.2
      (commutator_mem_pLowerCentralSeries x.2 y.2)))).commutatorElement_pow_right p

/-- **A class brackets trivially with its own `p`-power**: `[π x, x] = 0` in every degree, since
`x ^ p` commutes with `x`. -/
@[simp]
theorem gradedBracket_gradedPow_self {k : ℕ} (x : gradedPiece p G k) :
    gradedBracket p G (k + 1) k (gradedPow p G k x) x = 0 := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedPow_gradedMk, gradedBracket_gradedMk, gradedMk_eq_zero_iff, coe_mk,
    commutatorElement_eq_one_iff_commute.mpr (Commute.pow_self (x : G) p)]
  exact one_mem _

/-- **A class brackets trivially with its own `p`-power**: `[x, π x] = 0` in every degree, since
`x` commutes with `x ^ p`. -/
@[simp]
theorem gradedBracket_self_gradedPow {k : ℕ} (x : gradedPiece p G k) :
    gradedBracket p G k (k + 1) x (gradedPow p G k x) = 0 := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedPow_gradedMk, gradedBracket_gradedMk, gradedMk_eq_zero_iff, coe_mk,
    commutatorElement_eq_one_iff_commute.mpr (Commute.pow_self (x : G) p).symm]
  exact one_mem _

end Pow

/-! ### Functoriality -/

section Functoriality

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type w} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

variable (p) in
/-- **The graded map of a continuous homomorphism**: `f` carries `λ_k(G)` into `λ_k(H)`, so it
induces `gr_k(G) →+ gr_k(H)`. Its defining equation is `TauCeti.gradedMap_gradedMk`. -/
def gradedMap (f : G →* H) (hf : Continuous f) (k : ℕ) : gradedPiece p G k →+ gradedPiece p H k :=
  MonoidHom.toAdditive (QuotientGroup.map _ _
    ((f.comp (pLowerCentralSeries p G k).subtype).codRestrict (pLowerCentralSeries p H k)
      fun x => f.map_pLowerCentralSeries_le hf k ⟨x, x.2, rfl⟩)
    fun x hx => mem_comap.mpr (mem_subgroupOf.mpr
      (f.map_pLowerCentralSeries_le hf (k + 1) ⟨x, mem_subgroupOf.mp hx, rfl⟩)))

/-- **The graded map on classes**: the defining equation of `TauCeti.gradedMap`. -/
@[simp]
theorem gradedMap_gradedMk (f : G →* H) (hf : Continuous f) {k : ℕ}
    (x : pLowerCentralSeries p G k) :
    gradedMap p f hf k (gradedMk p G k x) =
      gradedMk p H k ⟨f x, f.map_pLowerCentralSeries_le hf k ⟨x, x.2, rfl⟩⟩ := by
  rw [gradedMap, gradedMk, MonoidHom.toAdditive_apply_apply, toMul_ofMul,
    QuotientGroup.map_mk, gradedMk]
  rfl

/-- **The graded map in degree zero**: the class of `g` goes to the class of `f g`. -/
@[simp]
theorem gradedMap_gradedMkZero (f : G →* H) (hf : Continuous f) (g : G) :
    gradedMap p f hf 0 (gradedMkZero p G g) = gradedMkZero p H (f g) := by
  rw [gradedMkZero, gradedMap_gradedMk, gradedMk_zero]

/-- The identity of `G` induces the identity on every graded piece. -/
@[simp]
theorem gradedMap_id (k : ℕ) :
    gradedMap p (MonoidHom.id G) continuous_id k = AddMonoidHom.id (gradedPiece p G k) := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedMap_gradedMk, AddMonoidHom.id_apply]
  rfl

/-- The graded map induced by a composite is the composite of the graded maps: `gr_k` is a
functor. -/
@[simp]
theorem gradedMap_comp (g : H →* K) (hg : Continuous g) (f : G →* H) (hf : Continuous f) (k : ℕ) :
    gradedMap p (g.comp f) (hg.comp hf) k = (gradedMap p g hg k).comp (gradedMap p f hf k) := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [AddMonoidHom.comp_apply, gradedMap_gradedMk, gradedMap_gradedMk, gradedMap_gradedMk]
  rfl

/-- The graded map of the inverse of a topological isomorphism inverts the graded map of the
isomorphism, in every degree. -/
@[simp]
theorem gradedMap_symm_gradedMap (e : G ≃ₜ* H) (k : ℕ) (x : gradedPiece p G k) :
    gradedMap p (e.symm : H →* G) (map_continuous e.symm) k
      (gradedMap p (e : G →* H) (map_continuous e) k x) = x := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedMap_gradedMk, gradedMap_gradedMk]
  congr 1
  exact Subtype.ext (e.symm_apply_apply x)

/-- A continuous closed surjection (for instance a continuous surjection from a compact group onto
a Hausdorff group, by `Continuous.isClosedMap`) induces a surjection in every degree. -/
theorem gradedMap_surjective (f : G →* H) (hf : Continuous f) (hfc : IsClosedMap f)
    (hsurj : Function.Surjective f) (k : ℕ) : Function.Surjective (gradedMap p f hf k) := by
  intro y
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  obtain ⟨x, hx, hxy⟩ : (y : H) ∈ (pLowerCentralSeries p G k).map f := by
    rw [f.map_pLowerCentralSeries_eq_of_surjective hf hfc hsurj]
    exact y.2
  refine ⟨gradedMk p G k ⟨x, hx⟩, ?_⟩
  rw [gradedMap_gradedMk]
  congr 1
  exact Subtype.ext hxy

/-- **Naturality of the bracket.** -/
@[simp]
theorem gradedMap_gradedBracket (f : G →* H) (hf : Continuous f) {j k : ℕ} (x : gradedPiece p G j)
    (y : gradedPiece p G k) :
    gradedMap p f hf (j + k + 1) (gradedBracket p G j k x y) =
      gradedBracket p H j k (gradedMap p f hf j x) (gradedMap p f hf k y) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective j x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedBracket_gradedMk, gradedMap_gradedMk, gradedMap_gradedMk, gradedMap_gradedMk,
    gradedBracket_gradedMk]
  congr 1
  exact Subtype.ext (map_commutatorElement f _ _)

/-- **Naturality of the `p`-power operator.** -/
@[simp]
theorem gradedMap_gradedPow (f : G →* H) (hf : Continuous f) {k : ℕ} (x : gradedPiece p G k) :
    gradedMap p f hf (k + 1) (gradedPow p G k x) = gradedPow p H k (gradedMap p f hf k x) := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedPow_gradedMk, gradedMap_gradedMk, gradedMap_gradedMk, gradedPow_gradedMk]
  congr 1
  exact Subtype.ext (map_pow f _ _)

end Functoriality

/-! ### Iterated `p`-powers of degree-zero classes -/

section PowIter

variable (p G) in
/-- **The iterated `p`-power operator** `π^j : gr_0(G) → gr_j(G)`, the `j`-fold composite
`π ∘ ⋯ ∘ π` of `TauCeti.gradedPow` starting in degree zero. On classes it is induced by
`g ↦ g ^ (p ^ j)` (`TauCeti.gradedPowIter_gradedMkZero`). It commutes with scalars
(`TauCeti.gradedPowIter_smul`), but for `p = 2` it need not be additive: already `π^1 = π` has
the defect `[x, y]` in degree zero (`TauCeti.gradedPow_add_zero_of_two`), which is nonzero for the
free pro-`2` group of rank two (`TauCeti.gradedPow_freeProP_two_not_additive`). -/
def gradedPowIter : (j : ℕ) → gradedPiece p G 0 → gradedPiece p G j
  | 0 => id
  | j + 1 => gradedPow p G j ∘ gradedPowIter j

@[simp]
theorem gradedPowIter_zero (x : gradedPiece p G 0) : gradedPowIter p G 0 x = x :=
  (rfl)

@[simp]
theorem gradedPowIter_succ (j : ℕ) (x : gradedPiece p G 0) :
    gradedPowIter p G (j + 1) x = gradedPow p G j (gradedPowIter p G j x) :=
  (rfl)

/-- **The iterated `p`-power operator on classes**: `π^j` sends the class of `g` to the class of
`g ^ (p ^ j)` in `gr_j(G)`. -/
@[simp]
theorem gradedPowIter_gradedMkZero (j : ℕ) (g : G) :
    gradedPowIter p G j (gradedMkZero p G g) =
      gradedMk p G j ⟨g ^ p ^ j, by
        simpa using pow_pow_mem_pLowerCentralSeries (mem_pLowerCentralSeries_zero p g) j⟩ := by
  induction j with
  | zero =>
    rw [gradedPowIter_zero, gradedMkZero]
    congr 1
    exact Subtype.ext (by simp)
  | succ j ih =>
    rw [gradedPowIter_succ, ih, gradedPow_gradedMk]
    congr 1
    exact Subtype.ext (by simp [pow_succ, pow_mul])

@[simp]
theorem gradedPowIter_zero_right (j : ℕ) : gradedPowIter p G j 0 = 0 := by
  rw [← gradedMkZero_one, gradedPowIter_gradedMkZero, gradedMk_eq_zero_iff, coe_mk, one_pow]
  exact one_mem _

/-- **The iterated `p`-power operator commutes with scalars**, since `π` does in every degree. -/
@[simp]
theorem gradedPowIter_smul (j : ℕ) (c : ZMod p) (x : gradedPiece p G 0) :
    gradedPowIter p G j (c • x) = c • gradedPowIter p G j x := by
  induction j with
  | zero => rw [gradedPowIter_zero, gradedPowIter_zero]
  | succ j ih => rw [gradedPowIter_succ, gradedPowIter_succ, ih, gradedPow_smul]

/-- **Naturality of the iterated `p`-power operator.** -/
@[simp]
theorem gradedMap_gradedPowIter {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (j : ℕ) (x : gradedPiece p G 0) :
    gradedMap p f hf j (gradedPowIter p G j x) = gradedPowIter p H j (gradedMap p f hf 0 x) := by
  induction j with
  | zero => rw [gradedPowIter_zero, gradedPowIter_zero]
  | succ j ih => rw [gradedPowIter_succ, gradedPowIter_succ, gradedMap_gradedPow, ih]

/-- **`π` carries the span of iterated `p`-powers to the next degree**: above degree zero, `π`
maps the span of the classes `π^j x_a` of a family `x : ι → gr_0(G)` into the span of the classes
`π^{j+1} x_a`. -/
theorem gradedPow_mem_span_range_gradedPowIter_succ {ι : Type*} (x : ι → gradedPiece p G 0)
    {j : ℕ} (hj : 1 ≤ j) {t : gradedPiece p G j}
    (ht : t ∈ Submodule.span (ZMod p) (Set.range fun a ↦ gradedPowIter p G j (x a))) :
    gradedPow p G j t ∈
      Submodule.span (ZMod p) (Set.range fun a ↦ gradedPowIter p G (j + 1) (x a)) := by
  have h := Submodule.mem_map_of_mem (f := (gradedPowAddMonoidHom p G hj).toZModLinearMap p) ht
  rw [Submodule.map_span, ← Set.range_comp] at h
  simpa only [Function.comp_def, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply,
    gradedPowIter_succ] using h

variable {H : Type u} [Group H] [TopologicalSpace H] [DiscreteTopology H] in
/-- In a discrete group isomorphic to `ℤ/pⁿ⁺¹` with `1 < p`, the iterated `p`-power class `π^n`
of the generator is nonzero in `gr_n`. -/
theorem _root_.MulEquiv.gradedPowIter_gradedMkZero_ne_zero_multiplicative_zmod_pow {n : ℕ}
    (e : H ≃* Multiplicative (ZMod (p ^ (n + 1)))) (hp : 1 < p) :
    gradedPowIter p H n (gradedMkZero p H (e.symm (Multiplicative.ofAdd 1))) ≠ 0 := by
  rw [gradedPowIter_gradedMkZero, ne_eq, gradedMk_eq_zero_iff, Subgroup.coe_mk,
    e.pLowerCentralSeries_eq_bot_multiplicative_zmod_pow, Subgroup.mem_bot, ← map_pow,
    e.symm.map_eq_one_iff]
  apply pow_ne_one_of_lt_orderOf (pow_ne_zero n (Nat.ne_zero_of_lt hp))
  rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  exact Nat.pow_lt_pow_right hp n.lt_succ_self

end PowIter

/-! ### Iterated `p`-powers of a bracket of degree-zero classes -/

section PowIterBracket

variable (p) in
/-- The `p ^ m`-th power of the commutator of two elements lies in `λ_{m+1}(G)`. -/
theorem commutatorElement_pow_pow_mem_pLowerCentralSeries (g h : G) (m : ℕ) :
    ⁅g, h⁆ ^ p ^ m ∈ pLowerCentralSeries p G (m + 1) := by
  rw [add_comm]
  exact pow_pow_mem_pLowerCentralSeries (commutator_mem_pLowerCentralSeries
    (mem_pLowerCentralSeries_zero p g) (mem_pLowerCentralSeries_zero p h)) m

variable (p G) in
/-- **The iterated `p`-power of the bracket of two degree-zero classes**: `π^m [ξ_g, ξ_h]`, the
class in `gr_{m+1}(G)` of `⁅g, h⁆ ^ (p ^ m)`. For `m = 0` it is the bracket of the classes of `g`
and `h` (`TauCeti.gradedPowIterBracket_zero`), and `π` raises `m` by one
(`TauCeti.gradedPow_gradedPowIterBracket`). At `p = 2`, `π [ξ_g, ξ_h]` differs from
`[π ξ_g, ξ_h]` by the correction `[[ξ_g, ξ_h], ξ_g]`, the bracket in `gr_2(G)` of the degree-one
class `[ξ_g, ξ_h]` with `ξ_g` (`TauCeti.gradedPow_gradedBracket_zero_zero`). -/
def gradedPowIterBracket (m : ℕ) (g h : G) : gradedPiece p G (m + 1) :=
  gradedMk p G (m + 1) ⟨⁅g, h⁆ ^ p ^ m, commutatorElement_pow_pow_mem_pLowerCentralSeries p g h m⟩

theorem gradedPowIterBracket_def (m : ℕ) (g h : G) :
    gradedPowIterBracket p G m g h =
      gradedMk p G (m + 1)
        ⟨⁅g, h⁆ ^ p ^ m, commutatorElement_pow_pow_mem_pLowerCentralSeries p g h m⟩ :=
  (rfl)

/-- For `m = 0`, that is without any `p`-power, `π^0 [ξ_g, ξ_h] ∈ gr_1(G)` is the bracket of the
classes of `g` and `h`. -/
@[simp]
theorem gradedPowIterBracket_zero (g h : G) :
    gradedPowIterBracket p G 0 g h =
      gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G h) := by
  rw [gradedBracket_gradedMkZero, gradedPowIterBracket_def]
  congr 1
  exact Subtype.ext (by simp)

/-- **`π` raises the iterated `p`-power of a bracket by one**:
`π (π^m [ξ_g, ξ_h]) = π^{m+1} [ξ_g, ξ_h]`. -/
@[simp]
theorem gradedPow_gradedPowIterBracket (m : ℕ) (g h : G) :
    gradedPow p G (m + 1) (gradedPowIterBracket p G m g h) =
      gradedPowIterBracket p G (m + 1) g h := by
  rw [gradedPowIterBracket_def, gradedPowIterBracket_def, gradedPow_gradedMk]
  congr 1
  exact Subtype.ext (by simp [pow_succ, pow_mul])

/-- The iterated `p`-powers of the bracket of a class with itself vanish. -/
@[simp]
theorem gradedPowIterBracket_self (m : ℕ) (g : G) : gradedPowIterBracket p G m g g = 0 := by
  rw [gradedPowIterBracket_def, gradedMk_eq_zero_iff, Subgroup.coe_mk, commutatorElement_self,
    one_pow]
  exact one_mem _

/-- **Skew-symmetry of the iterated `p`-powers of brackets**:
`π^m [ξ_h, ξ_g] = -π^m [ξ_g, ξ_h]`. -/
theorem gradedPowIterBracket_swap (m : ℕ) (g h : G) :
    gradedPowIterBracket p G m h g = -gradedPowIterBracket p G m g h := by
  rw [gradedPowIterBracket_def, gradedPowIterBracket_def, ← gradedMk_inv]
  congr 1
  exact Subtype.ext (by
    rw [Subgroup.coe_inv, Subgroup.coe_mk, Subgroup.coe_mk, ← inv_pow, commutatorElement_inv])

end PowIterBracket

end TauCeti
