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
* `TauCeti.gradedBracket`: the bracket `gr_j(G) →+ gr_k(G) →+ gr_{j+k+1}(G)`.
* `TauCeti.gradedPow`: the `p`-power operator `π : gr_k(G) → gr_{k+1}(G)`.
* `TauCeti.gradedMap`: the map on graded pieces induced by a continuous homomorphism.

## Main results

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

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §1,
  Propositions 1 and 2.
* J. D. Dixon, M. P. F. du Sautoy, A. Mann and D. Segal, *Analytic pro-`p` groups*, Section 1.2.
-/

public section

open Subgroup
open scoped commutatorElement

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Congruences modulo the next term

The image of `λ_k` in `G ⧸ λ_{k+1}` is central, so conjugation acts trivially on it and the
commutator is bimultiplicative modulo `λ_{j+k+2}`. -/

/-- The class of an element of `λ_k` in `G ⧸ λ_{k+1}` commutes with every class. -/
theorem commute_mk_of_mem_pLowerCentralSeries {k : ℕ} {c : G} (hc : c ∈ pLowerCentralSeries p G k)
    (g : G) : Commute (g : G ⧸ pLowerCentralSeries p G (k + 1)) (c : G ⧸ _) :=
  QuotientGroup.commute_mk_iff.mpr <|
    commutatorElement_inv c g ▸ inv_mem (commutator_mem_pLowerCentralSeries_succ hc g)

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
  -- Work in `Q = G ⧸ λ_{m+1}` with `m = i + j + k + 2`.
  set N := pLowerCentralSeries p G (i + j + k + 2 + 1) with hN
  -- `⁅u, v * w⁆ ≡ ⁅u, w⁆` when `⁅u, v⁆ ∈ λ_{m+1}` and `⁅u, w⁆ ∈ λ_m`.
  have key : ∀ {u v w : G}, ⁅u, v⁆ ∈ N → ⁅u, w⁆ ∈ pLowerCentralSeries p G (i + j + k + 2) →
      ((⁅u, v * w⁆ : G) : G ⧸ N) = ((⁅u, w⁆ : G) : G ⧸ N) := by
    intro u v w huv huw
    have h : ⁅u, v * w⁆ = ⁅u, v⁆ * (v * ⁅u, w⁆ * v⁻¹) := by
      rw [commutatorElement_mul_right_eq_mul_conj]; group
    rw [h, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr huv, one_mul,
      mk_conj_of_mem_pLowerCentralSeries huw]
  have hab := commutator_mem_pLowerCentralSeries ha hb
  have hbc := commutator_mem_pLowerCentralSeries hb hc
  have hca := commutator_mem_pLowerCentralSeries hc ha
  have e₁ : ((⁅⁅a, b⁆, b * c * b⁻¹⁆ : G) : G ⧸ N) = ((⁅⁅a, b⁆, c⁆ : G) : G ⧸ N) := by
    have h : b * c * b⁻¹ = ⁅b, c⁆ * c := by group
    rw [h]
    exact key (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hab hbc))
      (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hab hc))
  have e₂ : ((⁅⁅b, c⁆, c * a * c⁻¹⁆ : G) : G ⧸ N) = ((⁅⁅b, c⁆, a⁆ : G) : G ⧸ N) := by
    have h : c * a * c⁻¹ = ⁅c, a⁆ * a := by group
    rw [h]
    exact key (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hbc hca))
      (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hbc ha))
  have e₃ : ((⁅⁅c, a⁆, a * b * a⁻¹⁆ : G) : G ⧸ N) = ((⁅⁅c, a⁆, b⁆ : G) : G ⧸ N) := by
    have h : a * b * a⁻¹ = ⁅a, b⁆ * b := by group
    rw [h]
    exact key (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hca hab))
      (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries hca hb))
  rw [← QuotientGroup.eq_one_iff (N := N), QuotientGroup.mk_mul, QuotientGroup.mk_mul, ← e₁, ← e₂,
    ← e₃, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    commutatorElement_commutatorElement_conj_mul, QuotientGroup.mk_one]

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

/-- The quotient `λ_k ⧸ λ_{k+1}` is an abelian group, with its existing quotient operations:
`⁅λ_k, λ_k⁆ ≤ λ_{2k+1} ≤ λ_{k+1}`. -/
instance instCommGroupQuotientPLowerCentralSeries (k : ℕ) :
    CommGroup (pLowerCentralSeries p G k ⧸
      (pLowerCentralSeries p G (k + 1)).subgroupOf (pLowerCentralSeries p G k)) where
  mul_comm a b := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_subgroupOf, coe_mul,
      coe_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact (QuotientGroup.commute_mk_iff.mpr
      (pLowerCentralSeries_antitone (by omega) (commutator_mem_pLowerCentralSeries x.2 y.2))).eq

/-- **The graded pieces are killed by `p`.** -/
@[simp]
theorem nsmul_gradedPiece_eq_zero {k : ℕ} (x : gradedPiece p G k) : p • x = 0 := by
  obtain ⟨y, rfl⟩ := gradedMk_surjective k x
  rw [← gradedMk_pow, gradedMk_eq_zero_iff, coe_pow]
  exact pow_mem_pLowerCentralSeries y.2

/-- The graded pieces are `ZMod p`-modules, with the canonical action on an abelian group killed
by `p`. -/
instance instModuleZModGradedPiece (k : ℕ) : Module (ZMod p) (gradedPiece p G k) :=
  AddCommGroup.zmodModule fun x => nsmul_gradedPiece_eq_zero x

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
  intro x y h
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  obtain ⟨y, rfl⟩ := gradedMk_surjective k y
  rw [gradedPieceInclusion_gradedMk, gradedPieceInclusion_gradedMk,
    Additive.ofMul.apply_eq_iff_eq] at h
  exact gradedMk_eq_gradedMk_iff.mpr h

theorem gradedPieceInclusion_zero_surjective :
    Function.Surjective (gradedPieceInclusion p G 0) := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective x.toMul
  refine ⟨gradedMk p G 0 ⟨g, ?_⟩, ?_⟩
  · rw [pLowerCentralSeries_zero]; exact mem_top g
  · rw [gradedPieceInclusion_gradedMk, coe_mk, hg, ofMul_toMul]

variable (p G) in
/-- **The degree-zero piece is `G ⧸ λ_1`.** For a profinite group and a prime `p`, `λ_1` is the
pro-`p` Frattini subgroup, so `gr_0(G)` is the Frattini quotient. -/
noncomputable def gradedPieceZeroEquiv :
    gradedPiece p G 0 ≃+ Additive (G ⧸ pLowerCentralSeries p G 1) :=
  AddEquiv.ofBijective (gradedPieceInclusion p G 0)
    ⟨gradedPieceInclusion_injective 0, gradedPieceInclusion_zero_surjective⟩

@[simp]
theorem gradedPieceZeroEquiv_gradedMk (x : pLowerCentralSeries p G 0) :
    gradedPieceZeroEquiv p G (gradedMk p G 0 x) =
      Additive.ofMul ((x : G) : G ⧸ pLowerCentralSeries p G 1) :=
  gradedPieceInclusion_gradedMk x

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

/-- **The bracket is alternating**: `[x, x] = 0` in every degree. -/
@[simp]
theorem gradedBracket_self {k : ℕ} (x : gradedPiece p G k) : gradedBracket p G k k x x = 0 := by
  obtain ⟨x, rfl⟩ := gradedMk_surjective k x
  rw [gradedBracket_gradedMk, gradedMk_eq_zero_iff, coe_mk, commutatorElement_self]
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
  rw [gradedPow_add_zero, Nat.choose_two_right,
    Nat.mul_div_assoc _ (Nat.Odd.sub_odd hp odd_one).two_dvd, mul_nsmul,
    nsmul_gradedPiece_eq_zero, nsmul_zero, add_zero]

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

end Pow

/-! ### Functoriality -/

section Functoriality

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

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

end TauCeti
