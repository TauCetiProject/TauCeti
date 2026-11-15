/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Vertex.NormalOrder
public import TauCeti.Algebra.Vertex.ResidueProduct
import TauCeti.Algebra.Vertex.FormalDistribution
import Mathlib.Tactic.Abel

/-!
# Dong's lemma for residue and normal-ordered products

Mutually local families of fields on an `R`-module `V` are closed under nonnegative residue products
and normal ordering. If `A`, `B`, `C` are fields on `V` that are pairwise local of orders `r`, `s`,
`t` (for `(A, B)`, `(A, C)`, `(B, C)` respectively), then:

* every nonnegative residue product `Res_z (z - w)ⁿ [A(z), B(w)]` is local to `C` of order at
  most `r + s + t` (`VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`);
* the normal-ordered product `:AB:` is local to `C` of order at most `r + s + t + 1`
  (`VertexOperator.IsLocalOfOrder.normalOrder_left`).

Both results hold over an arbitrary commutative ring `R` with no characteristic or division
assumptions. Together with linear and derivative closure of locality, they imply closure under all
integer-indexed `n`-th products over a `ℚ`-algebra (`TauCeti.Algebra.Vertex.NthProduct`), which
drives the state–field correspondence and the vertex algebra reconstruction theorem.

## Main results

* `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_left`,
  `VertexOperator.IsLocalOfOrder.nonnegResidueProduct_right`: Dong's lemma for nonnegative residue
  products.
* `VertexOperator.IsLocalOfOrder.normalOrder_left`,
  `VertexOperator.IsLocalOfOrder.normalOrder_right`: Dong's lemma for normal-ordered products.

## References

* H. Li, *Local systems of vertex operators, vertex superalgebras and modules*, J. Pure Appl.
  Algebra 109 (1996), Lemma 3.2 (attributing the lemma to C. Dong).
* V. Kac, *Vertex Algebras for Beginners*, 2nd ed., §3.2, Lemma 3.2.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.3.2, Lemma 2.3.5.
-/

public section

noncomputable section

open scoped VertexOperator
open Finset TauCeti

namespace VertexOperator

-- Both forms of Dong's lemma are proved coefficientwise on three-variable formal distributions:
-- writing `z₂ - z₃ = (z₁ - z₃) - (z₁ - z₂)` reduces `(z₂ - z₃)^(r₀ + s + t)` by induction to high
-- powers of `z₁ - z₂` (which kill `[A(z₁), B(z₂)]` directly, or after one telescoping step on the
-- shifted normal-order halves) and high powers of `z₁ - z₃` and `z₂ - z₃` (which kill the `[A, C]`
-- and `[B, C]` factors after expanding nested commutators).
section Dist3

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- A three-variable formal distribution, indexed by normalized mode triples. -/
private abbrev Dist3 (M : Type*) := ℤ → ℤ → ℤ → M

private theorem end_mul_apply {A : Type*} [AddCommMonoid A] (f g : AddMonoid.End A) (x : A) :
    (f * g) x = f (g x) := rfl

/-- Swapping the first two variables of a three-variable distribution. -/
private def swap₁₂ : AddMonoid.End (Dist3 M) where
  toFun D a b c := D b a c
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
private theorem swap₁₂_apply (D : Dist3 M) (a b c : ℤ) : swap₁₂ D a b c = D b a c := rfl

@[simp]
private theorem swap₁₂_swap₁₂ (D : Dist3 M) : swap₁₂ (swap₁₂ D) = D := rfl

/-- Multiplication of a three-variable distribution by `z₁ - z₂`. -/
private def mulSub₁₂ : AddMonoid.End (Dist3 M) where
  toFun D a b c := D (a + 1) b c - D a (b + 1) c
  map_zero' := by ext a b c; simp
  map_add' D E := by ext a b c; simp; abel

@[simp]
private theorem mulSub₁₂_apply (D : Dist3 M) (a b c : ℤ) :
    mulSub₁₂ D a b c = D (a + 1) b c - D a (b + 1) c := rfl

/-- Multiplication of a three-variable distribution by `z₁ - z₃`. -/
private def mulSub₁₃ : AddMonoid.End (Dist3 M) where
  toFun D a b c := D (a + 1) b c - D a b (c + 1)
  map_zero' := by ext a b c; simp
  map_add' D E := by ext a b c; simp; abel

@[simp]
private theorem mulSub₁₃_apply (D : Dist3 M) (a b c : ℤ) :
    mulSub₁₃ D a b c = D (a + 1) b c - D a b (c + 1) := rfl

/-- Multiplication of a three-variable distribution by `z₂ - z₃`. -/
private def mulSub₂₃ : AddMonoid.End (Dist3 M) where
  toFun D a b c := D a (b + 1) c - D a b (c + 1)
  map_zero' := by ext a b c; simp
  map_add' D E := by ext a b c; simp; abel

@[simp]
private theorem mulSub₂₃_apply (D : Dist3 M) (a b c : ℤ) :
    mulSub₂₃ D a b c = D a (b + 1) c - D a b (c + 1) := rfl

private theorem mulSub₁₂_swap₁₂ (D : Dist3 M) :
    mulSub₁₂ (swap₁₂ D) = -swap₁₂ (mulSub₁₂ D) := by
  ext a b c
  simp only [mulSub₁₂_apply, swap₁₂_apply, Pi.neg_apply, neg_sub]

private theorem mulSub₂₃_pow_swap₁₂ (k : ℕ) (D : Dist3 M) :
    (mulSub₂₃ ^ k) (swap₁₂ D) = swap₁₂ ((mulSub₁₃ ^ k) D) := by
  induction k generalizing D with
  | zero => rfl
  | succ k ih =>
    have h1 (E : Dist3 M) : mulSub₂₃ (swap₁₂ E) = swap₁₂ (mulSub₁₃ E) := rfl
    rw [pow_succ', end_mul_apply, ih, h1, pow_succ', end_mul_apply]

private theorem mulSub₁₃_pow_swap₁₂ (k : ℕ) (D : Dist3 M) :
    (mulSub₁₃ ^ k) (swap₁₂ D) = swap₁₂ ((mulSub₂₃ ^ k) D) := by
  have h := congr_arg swap₁₂ (mulSub₂₃_pow_swap₁₂ k (swap₁₂ D))
  simpa only [swap₁₂_swap₁₂] using h.symm

private theorem mulSub₂₃_apply_eq_sub (D : Dist3 M) :
    mulSub₂₃ D = mulSub₁₃ D - mulSub₁₂ D := by
  ext a b c
  simp only [mulSub₂₃_apply, Pi.sub_apply, mulSub₁₃_apply, mulSub₁₂_apply]
  abel

private theorem commute_mulSub₁₃_mulSub₁₂ :
    Commute (mulSub₁₃ : AddMonoid.End (Dist3 M)) mulSub₁₂ := by
  ext D a b c
  simp only [end_mul_apply, mulSub₁₃_apply, mulSub₁₂_apply]
  abel

private theorem commute_mulSub₂₃_mulSub₁₂ :
    Commute (mulSub₂₃ : AddMonoid.End (Dist3 M)) mulSub₁₂ := by
  ext D a b c
  simp only [end_mul_apply, mulSub₂₃_apply, mulSub₁₂_apply]
  abel

private theorem commute_mulSub₂₃_mulSub₁₃ :
    Commute (mulSub₂₃ : AddMonoid.End (Dist3 M)) mulSub₁₃ := by
  ext D a b c
  simp only [end_mul_apply, mulSub₂₃_apply, mulSub₁₃_apply]
  abel

private theorem mulSub₁₂_pow_eval (k : ℕ) (D : Dist3 M) (a b c : ℤ) :
    ((mulSub₁₂ ^ k) D) a b c =
      ((FormalDistribution.mulSub ^ k) (fun a' b' ↦ D a' b' c)) a b := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', end_mul_apply, mulSub₁₂_apply, FormalDistribution.mulSub_apply, ih]

private theorem mulSub₁₃_pow_eval (k : ℕ) (D : Dist3 M) (a b c : ℤ) :
    ((mulSub₁₃ ^ k) D) a b c =
      ((FormalDistribution.mulSub ^ k) (fun a' c' ↦ D a' b c')) a c := by
  induction k generalizing a c with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', end_mul_apply, mulSub₁₃_apply, FormalDistribution.mulSub_apply, ih]

private theorem mulSub₂₃_pow_eval (k : ℕ) (D : Dist3 M) (a b c : ℤ) :
    ((mulSub₂₃ ^ k) D) a b c =
      ((FormalDistribution.mulSub ^ k) (fun b' c' ↦ D a b' c')) b c := by
  induction k generalizing b c with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', end_mul_apply, mulSub₂₃_apply, FormalDistribution.mulSub_apply, ih]

/-- Naturality of `FormalDistribution.mulSub ^ k` with respect to an additive map and a shift in
the first variable. -/
private theorem mulSub_pow_comp_shift (φ : M →+ N) (k : ℕ) (d : FormalDistribution M) (s m n : ℤ) :
    ((FormalDistribution.mulSub ^ k) (fun a b ↦ φ (d (a + s) b))) m n =
      φ (((FormalDistribution.mulSub ^ k) d) (m + s) n) := by
  induction k generalizing m n with
  | zero => rfl
  | succ k ih =>
    simp only [pow_succ', end_mul_apply, FormalDistribution.mulSub_apply]
    have h : m + 1 + s = m + s + 1 := by omega
    rw [ih, ih, h, ← map_sub]

private theorem mulSub_pow_comp (φ : M →+ N) (k : ℕ) (d : FormalDistribution M) (m n : ℤ) :
    ((FormalDistribution.mulSub ^ k) (fun a b ↦ φ (d a b))) m n =
      φ (((FormalDistribution.mulSub ^ k) d) m n) := by
  simpa only [add_zero] using mulSub_pow_comp_shift φ k d 0 m n

/-- Pointwise finite sums commute with `mulSub₂₃ ^ k`. -/
private theorem mulSub₂₃_pow_finsum (k : ℕ) (H : ℕ → Dist3 M)
    (hfin : ∀ a b c, (Function.support fun i ↦ H i a b c).Finite) :
    (mulSub₂₃ ^ k) (fun a b c ↦ ∑ᶠ i, H i a b c) =
      fun a b c ↦ ∑ᶠ i, ((mulSub₂₃ ^ k) (H i)) a b c := by
  induction k generalizing H with
  | zero => rfl
  | succ k ih =>
    have hfin' : ∀ a b c, (Function.support fun i ↦ (mulSub₂₃ (H i)) a b c).Finite := by
      intro a b c
      refine ((hfin a (b + 1) c).union (hfin a b (c + 1))).subset fun i hi ↦ ?_
      simp only [Function.mem_support, Set.mem_union, mulSub₂₃_apply] at hi ⊢
      by_contra! h
      exact hi (by simp [h.1, h.2])
    have hstep : mulSub₂₃ (fun a b c ↦ ∑ᶠ i, H i a b c) =
        fun a b c ↦ ∑ᶠ i, (mulSub₂₃ (H i)) a b c := by
      ext a b c
      exact (finsum_sub_distrib (hfin a (b + 1) c) (hfin a b (c + 1))).symm
    rw [pow_succ, end_mul_apply, hstep, ih _ hfin']
    ext a b c
    exact finsum_congr fun _ ↦ rfl

/-- Pointwise finite sums commute with `mulSub₁₃ ^ k`. -/
private theorem mulSub₁₃_pow_finsum (k : ℕ) (H : ℕ → Dist3 M)
    (hfin : ∀ a b c, (Function.support fun i ↦ H i a b c).Finite) :
    (mulSub₁₃ ^ k) (fun a b c ↦ ∑ᶠ i, H i a b c) =
      fun a b c ↦ ∑ᶠ i, ((mulSub₁₃ ^ k) (H i)) a b c := by
  have h := congr_arg swap₁₂
    (mulSub₂₃_pow_finsum k (fun i ↦ swap₁₂ (H i)) (fun a b c ↦ hfin b a c))
  have hid : (swap₁₂ fun a b c ↦ ∑ᶠ i, swap₁₂ (H i) a b c) = fun a b c ↦ ∑ᶠ i, H i a b c := rfl
  rw [← mulSub₁₃_pow_swap₁₂, hid] at h
  exact h.trans (by
    ext a b c
    simpa only [swap₁₂_apply] using
      finsum_congr fun i ↦ congrFun (congrFun (congrFun (mulSub₂₃_pow_swap₁₂ k (H i)) b) a) c)

/-- Core identity for Dong's lemma: if `E` is annihilated by `mulSub₁₂ ^ r₀` and admits a
decomposition `E = E₁ + E₂` with `(mulSub₂₃ ^ t) E₁ = 0` and `(mulSub₁₃ ^ s) E₂ = 0`, then
`(mulSub₂₃ ^ (r₀ + s + t)) E = 0`. -/
private theorem mulSub₂₃_pow_eq_zero_of_split :
    ∀ {r₀ s t : ℕ} {E E₁ E₂ : Dist3 M},
      (mulSub₁₂ ^ r₀) E = 0 →
      E = E₁ + E₂ →
      (mulSub₂₃ ^ t) E₁ = 0 →
      (mulSub₁₃ ^ s) E₂ = 0 →
      (mulSub₂₃ ^ (r₀ + s + t)) E = 0
  | 0, _, _, E, _, _, h₁₂, _, _, _ => by
    have hE : E = 0 := by simpa using h₁₂
    rw [hE, map_zero]
  | r₀ + 1, 0, t, E, E₁, E₂, _, hsplit, h₂₃, h₁₃ => by
    have hE₂ : E₂ = 0 := by simpa using h₁₃
    have hexp : r₀ + 1 + 0 + t = (r₀ + 1) + t := by omega
    rw [hexp, hsplit, hE₂, add_zero, pow_add, end_mul_apply, h₂₃, map_zero]
  | r₀ + 1, s + 1, t, E, E₁, E₂, h₁₂, hsplit, h₂₃, h₁₃ => by
    have hexp : r₀ + 1 + (s + 1) + t = (r₀ + 1 + s + t) + 1 := by omega
    rw [hexp, pow_succ, end_mul_apply, mulSub₂₃_apply_eq_sub, map_sub]
    have h₁ : (mulSub₂₃ ^ (r₀ + 1 + s + t)) (mulSub₁₃ E) = 0 :=
      mulSub₂₃_pow_eq_zero_of_split
        (E₁ := mulSub₁₃ E₁) (E₂ := mulSub₁₃ E₂)
        (by rw [← end_mul_apply, (commute_mulSub₁₃_mulSub₁₂.pow_right (r₀ + 1)).symm.eq,
              end_mul_apply, h₁₂, map_zero])
        (by rw [hsplit, map_add])
        (by rw [← end_mul_apply, (commute_mulSub₂₃_mulSub₁₃.pow_left t).eq,
              end_mul_apply, h₂₃, map_zero])
        (by rwa [← end_mul_apply, ← pow_succ])
    have h₂ : (mulSub₂₃ ^ (r₀ + 1 + s + t)) (mulSub₁₂ E) = 0 := by
      have hexp' : r₀ + 1 + s + t = r₀ + (s + 1) + t := by omega
      rw [hexp']
      exact mulSub₂₃_pow_eq_zero_of_split
        (E₁ := mulSub₁₂ E₁) (E₂ := mulSub₁₂ E₂)
        (by rwa [← end_mul_apply, ← pow_succ])
        (by rw [hsplit, map_add])
        (by rw [← end_mul_apply, (commute_mulSub₂₃_mulSub₁₂.pow_left t).eq,
              end_mul_apply, h₂₃, map_zero])
        (by rw [← end_mul_apply, (commute_mulSub₁₃_mulSub₁₂.pow_left (s + 1)).eq,
              end_mul_apply, h₁₃, map_zero])
    rw [h₁, h₂, sub_zero]

end Dist3

namespace IsLocalOfOrder

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-! ### Dong's lemma for nonnegative residue products -/

/-- The additive map `X ↦ X * Y - Y * X` on a ring `S`. -/
private def commutatorRightAddHom {S : Type*} [Ring S] (Y : S) : S →+ S where
  toFun X := X * Y - Y * X
  map_zero' := by simp
  map_add' X₁ X₂ := by simp [add_mul, mul_add]; abel

/-- **Dong's lemma for nonnegative residue products** (left argument). If `(A, B)`, `(A, C)`,
`(B, C)` are pairwise local of orders `r`, `s`, `t`, then `nonnegResidueProduct n A B` is local
to `C` of order `r + s + t`. -/
theorem nonnegResidueProduct_left {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C s) (hBC : B.IsLocalOfOrder C t)
    (n : ℕ) :
    (nonnegResidueProduct n A B).IsLocalOfOrder C (r + s + t) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  let D : Dist3 (Module.End R V) := fun a b c ↦
    commutatorRightAddHom (C[[c]]) (A.commutatorDistribution B a b)
  let D₁ : Dist3 (Module.End R V) := fun a b c ↦
    -commutatorRightAddHom (A[[a]]) (B.commutatorDistribution C b c)
  let D₂ : Dist3 (Module.End R V) := fun a b c ↦
    commutatorRightAddHom (B[[b]]) (A.commutatorDistribution C a c)
  have hAB0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero A B r).mp hAB
  have hAC0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C s).mp hAC
  have hBC0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C t).mp hBC
  have h₁₂ : (mulSub₁₂ ^ r) D = 0 := by
    funext a b c
    exact (mulSub₁₂_pow_eval r D a b c).trans
      ((mulSub_pow_comp (commutatorRightAddHom (C[[c]])) r (A.commutatorDistribution B) a b).trans
        (by simp [hAB0]))
  have h₂₃ : (mulSub₂₃ ^ t) D₁ = 0 := by
    funext a b c
    exact (mulSub₂₃_pow_eval t D₁ a b c).trans
      ((mulSub_pow_comp (-commutatorRightAddHom (A[[a]])) t (B.commutatorDistribution C) b c).trans
        (by simp [hBC0]))
  have h₁₃ : (mulSub₁₃ ^ s) D₂ = 0 := by
    funext a b c
    exact (mulSub₁₃_pow_eval s D₂ a b c).trans
      ((mulSub_pow_comp (commutatorRightAddHom (B[[b]])) s (A.commutatorDistribution C) a c).trans
        (by simp [hAC0]))
  have hjac : D = D₁ + D₂ := by
    funext a b c
    simp only [D, D₁, D₂, commutatorRightAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      Pi.add_apply, commutatorDistribution_apply, sub_mul, mul_sub, mul_assoc]
    abel_nf
  have hD0 : (mulSub₂₃ ^ (r + s + t)) D = 0 :=
    mulSub₂₃_pow_eq_zero_of_split h₁₂ hjac h₂₃ h₁₃
  have hDn : (mulSub₂₃ ^ (r + s + t)) ((mulSub₁₂ ^ n) D) = 0 := by
    rw [← end_mul_apply, ((commute_mulSub₂₃_mulSub₁₂.pow_left _).pow_right n).eq,
      end_mul_apply, hD0, map_zero]
  have hres : (fun b c ↦ ((mulSub₁₂ ^ n) D) 0 b c) =
      (nonnegResidueProduct n A B).commutatorDistribution C := by
    funext m c
    have hcoeff : ((FormalDistribution.mulSub ^ n) (A.commutatorDistribution B)) 0 m =
        (nonnegResidueProduct n A B)[[m]] := by
      simp [FormalDistribution.mulSub_pow_apply, ncoeff_nonnegResidueProduct]
    exact (mulSub₁₂_pow_eval n D 0 m c).trans
      ((mulSub_pow_comp (commutatorRightAddHom (C[[c]])) n (A.commutatorDistribution B) 0 m).trans
        (by rw [hcoeff, commutatorDistribution_apply]; rfl))
  funext m c
  have h0 := congrFun (congrFun (congrFun hDn 0) m) c
  rw [mulSub₂₃_pow_eval, hres] at h0
  exact h0

/-- **Dong's lemma for nonnegative residue products** (right argument). -/
theorem nonnegResidueProduct_right {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B s) (hAC : A.IsLocalOfOrder C t) (hBC : B.IsLocalOfOrder C r)
    (n : ℕ) :
    A.IsLocalOfOrder (nonnegResidueProduct n B C) (r + s + t) :=
  (hBC.nonnegResidueProduct_left hAB.symm hAC.symm n).symm

/-! ### Dong's lemma for normal-ordered products -/

/-- One half of the shifted normal-order commutator distribution on a fixed vector `v`:
`∑ᶠ i : ℕ, [A[[p - i - 1]] B[[b + i]], C[[c']]] v`. The complementary half is
`swap₁₂ (halfDist B A C v)`. -/
private def halfDist (A B C : VertexOperator R V) (v : V) : Dist3 V :=
  fun p b c' ↦ ∑ᶠ i : ℕ,
    ((A[[p - i - 1]] * B[[b + i]]) * C[[c']] - C[[c']] * (A[[p - i - 1]] * B[[b + i]])) v

/-- Multiplying `halfDist A B C v` by `z₁ - z₂` telescopes the sum to the boundary term `i = 0`. -/
private theorem mulSub₁₂_halfDist (A B C : VertexOperator R V) (v : V) (p b c' : ℤ) :
    mulSub₁₂ (halfDist A B C v) p b c' =
      ((A[[p]] * B[[b]]) * C[[c']] - C[[c']] * (A[[p]] * B[[b]])) v := by
  let H (i : ℕ) (p' b' : ℤ) : V :=
    ((A[[p' - i - 1]] * B[[b' + i]]) * C[[c']] - C[[c']] * (A[[p' - i - 1]] * B[[b' + i]])) v
  obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
  obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
  let P := max P₁ P₂ + b.natAbs
  have h1 : halfDist A B C v (p + 1) b c' = ∑ i ∈ range (P + 1), H i (p + 1) b := by
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by dsimp only [H]; simp [hP₁ (b + i) (by omega), hP₂ (b + i) (by omega)])
  have h2 : halfDist A B C v p (b + 1) c' = ∑ j ∈ range P, H j p (b + 1) := by
    refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hj (by dsimp only [H]; simp [hP₁ (b + 1 + j) (by omega), hP₂ (b + 1 + j) (by omega)])
  rw [mulSub₁₂_apply, h1, h2, sum_range_succ']
  have hcongr : ∑ j ∈ range P, H (j + 1) (p + 1) b = ∑ j ∈ range P, H j p (b + 1) := by
    refine sum_congr rfl fun j _ ↦ ?_
    have h₁ : p + 1 - ↑(j + 1) - 1 = p - j - 1 := by omega
    have h₂ : b + ↑(j + 1) = b + 1 + j := by omega
    dsimp only [H]
    rw [h₁, h₂]
  have h₀ : H 0 (p + 1) b = ((A[[p]] * B[[b]]) * C[[c']] - C[[c']] * (A[[p]] * B[[b]])) v := by
    have h₁ : p + 1 - ((0 : ℕ) : ℤ) - 1 = p := by omega
    have h₂ : b + ((0 : ℕ) : ℤ) = b := by omega
    dsimp only [H]
    rw [h₁, h₂]
  rw [hcongr, h₀, add_sub_cancel_left]

/-- Expanding `[X Y, Z] = X [Y, Z] + [X, Z] Y` splits `halfDist A B C v` into a term killed by
`mulSub₂₃ ^ t` and a term killed by `mulSub₁₃ ^ s`. -/
private theorem halfDist_exists_split {A B C : VertexOperator R V} {s t : ℕ}
    (hAC : A.IsLocalOfOrder C s) (hBC : B.IsLocalOfOrder C t) (v : V) :
    ∃ D₁ D₂ : Dist3 V,
      halfDist A B C v = D₁ + D₂ ∧ (mulSub₂₃ ^ t) D₁ = 0 ∧ (mulSub₁₃ ^ s) D₂ = 0 := by
  let F₁ : ℕ → Dist3 V := fun i p b c' ↦
    (A[[p - i - 1]]) ((B.commutatorDistribution C (b + i) c') v)
  let F₂ : ℕ → Dist3 V := fun i p b c' ↦
    (A.commutatorDistribution C (p - i - 1) c') ((B[[b + i]]) v)
  have hfinF₁ : ∀ p b c', (Function.support fun i ↦ F₁ i p b c').Finite := by
    intro p b c'
    obtain ⟨P₁, hP₁⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    obtain ⟨P₂, hP₂⟩ := B.exists_forall_ncoeff_apply_eq_zero ((C[[c']]) v)
    refine (finite_toSet (range (max P₁ P₂ + b.natAbs))).subset fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by dsimp only [F₁]; simp [commutatorDistribution_apply,
      hP₁ (b + i) (by omega), hP₂ (b + i) (by omega)])
  have hfinF₂ : ∀ p b c', (Function.support fun i ↦ F₂ i p b c').Finite := by
    intro p b c'
    obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero v
    refine (finite_toSet (range (P + b.natAbs))).subset fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by dsimp only [F₂]; simp [hP (b + i) (by omega)])
  have hBC0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero B C t).mp hBC
  have hAC0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero A C s).mp hAC
  refine ⟨fun p b c' ↦ ∑ᶠ i, F₁ i p b c', fun p b c' ↦ ∑ᶠ i, F₂ i p b c', ?_, ?_, ?_⟩
  · funext p b c'
    simp only [Pi.add_apply]
    rw [← finsum_add_distrib (hfinF₁ p b c') (hfinF₂ p b c')]
    refine finsum_congr fun i ↦ ?_
    simp only [F₁, F₂, commutatorDistribution_apply, LinearMap.sub_apply, mul_apply_eq_comp,
      map_sub]
    abel
  · rw [mulSub₂₃_pow_finsum t F₁ hfinF₁]
    funext p b c'
    have h₁ : ∀ i, ((mulSub₂₃ ^ t) (F₁ i)) p b c' = 0 := fun i ↦ by
      let φ : Module.End R V →+ V :=
        { toFun := fun X ↦ (A[[p - i - 1]]) (X v)
          map_zero' := by simp
          map_add' := fun _ _ ↦ by simp }
      exact (mulSub₂₃_pow_eval t (F₁ i) p b c').trans
        ((mulSub_pow_comp_shift φ t (B.commutatorDistribution C) i b c').trans
          (by simp [φ, hBC0]))
    simp [h₁]
  · rw [mulSub₁₃_pow_finsum s F₂ hfinF₂]
    funext p b c'
    have h₂ : ∀ i, ((mulSub₁₃ ^ s) (F₂ i)) p b c' = 0 := fun i ↦ by
      let φ : Module.End R V →+ V :=
        { toFun := fun X ↦ X ((B[[b + i]]) v)
          map_zero' := by simp
          map_add' := fun _ _ ↦ by simp }
      have hshift : (fun p' c'' ↦ F₂ i p' b c'') =
          fun p' c'' ↦ φ (A.commutatorDistribution C (p' + (-(i : ℤ) - 1)) c'') := by
        funext p' c''
        have : p' - (i : ℤ) - 1 = p' + (-(i : ℤ) - 1) := by omega
        simp [F₂, φ, this]
      rw [mulSub₁₃_pow_eval, hshift,
        mulSub_pow_comp_shift φ s (A.commutatorDistribution C) (-(i : ℤ) - 1) p c']
      simp [φ, hAC0]
    simp [h₂]

/-- Evaluating the sum of the two normal-order halves at `p = 0` recovers the commutator
distribution of `normalOrder A B` with `C`. -/
private theorem halfDist_zero_add_swap (A B C : VertexOperator R V) (v : V) (b c' : ℤ) :
    halfDist A B C v 0 b c' + halfDist B A C v b 0 c' =
      (((normalOrder A B).commutatorDistribution C) b c') v := by
  have hfinsum_comm {f : ℕ → Module.End R V}
      (hf : ∀ w : V, (Function.support fun i ↦ (f i) w).Finite) :
      (∑ᶠ i : ℕ, (f i * C[[c']] - C[[c']] * f i) v) =
        (∑ᶠ i : ℕ, (f i) ((C[[c']]) v)) - (C[[c']]) (∑ᶠ i : ℕ, (f i) v) := by
    have hf' : (Function.support fun i ↦ (C[[c']]) ((f i) v)).Finite :=
      (hf v).subset fun i hi h ↦ hi (by simp [h])
    rw [map_finsum _ (hf v), ← finsum_sub_distrib (hf ((C[[c']]) v)) hf']
    exact finsum_congr fun _ ↦ rfl
  have hL : ∀ w : V, (Function.support fun i : ℕ ↦
      (A[[(0 : ℤ) - i - 1]] * B[[b + i]]) w).Finite := fun w ↦ by
    obtain ⟨P, hP⟩ := B.exists_forall_ncoeff_apply_eq_zero w
    refine (finite_toSet (range (P + b.natAbs))).subset fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [hP (b + i) (by omega)])
  have hR : ∀ w : V, (Function.support fun i : ℕ ↦
      (B[[b - i - 1]] * A[[(0 : ℤ) + i]]) w).Finite := fun w ↦ by
    obtain ⟨Q, hQ⟩ := A.exists_forall_ncoeff_apply_eq_zero w
    refine (finite_toSet (range Q)).subset fun i hi ↦ ?_
    simp only [mem_coe, mem_range]
    by_contra! h
    exact hi (by simp [hQ i (by omega)])
  have h0L (i : ℕ) : (0 : ℤ) - i - 1 = -(i : ℤ) - 1 := by omega
  rw [halfDist, halfDist, hfinsum_comm hL, hfinsum_comm hR]
  simp only [h0L, zero_add, commutatorDistribution_apply, ncoeff_normalOrder,
    normalOrderCoeff_apply, LinearMap.sub_apply, mul_apply_eq_comp, map_add]
  abel

/-- **Dong's lemma for normal-ordered products** (left argument). If `(A, B)`, `(A, C)`,
`(B, C)` are pairwise local of orders `r`, `s`, `t`, then `normalOrder A B` is local to `C` of
order `r + s + t + 1`. -/
theorem normalOrder_left {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B r) (hAC : A.IsLocalOfOrder C s) (hBC : B.IsLocalOfOrder C t) :
    (normalOrder A B).IsLocalOfOrder C (r + s + t + 1) := by
  rw [isLocalOfOrder_iff_mulSub_pow_eq_zero]
  ext m c v
  let E : Dist3 V := halfDist A B C v + swap₁₂ (halfDist B A C v)
  -- Step 1: `mulSub₁₂ E` telescopes to `[[A[[p]], B[[b]]], C[[c']]] v`, so `mulSub₁₂ ^ (r + 1)`
  -- kills `E`.
  have htel : mulSub₁₂ E = fun p b c' ↦
      (commutatorRightAddHom (C[[c']]) (A.commutatorDistribution B p b)) v := by
    funext p b c'
    rw [map_add, mulSub₁₂_swap₁₂]
    simp only [commutatorRightAddHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
      Pi.neg_apply, swap₁₂_apply, mulSub₁₂_halfDist, commutatorDistribution_apply, sub_mul,
      mul_sub, LinearMap.sub_apply]
    abel
  have hAB0 := (isLocalOfOrder_iff_mulSub_pow_eq_zero A B r).mp hAB
  let ev : Module.End R V →+ V :=
    { toFun := fun X ↦ X v
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have h₁₂ : (mulSub₁₂ ^ (r + 1)) E = 0 := by
    rw [pow_succ, end_mul_apply, htel]
    funext p b c'
    exact (mulSub₁₂_pow_eval r _ p b c').trans
      ((mulSub_pow_comp (ev.comp (commutatorRightAddHom (C[[c']]))) r
        (A.commutatorDistribution B) p b).trans (by simp [ev, hAB0]))
  -- Step 2: Split both halves using `halfDist_exists_split` for `(A, B)` and `(B, A)`.
  obtain ⟨D₁, D₂, hAB_eq, hD₁, hD₂⟩ := halfDist_exists_split hAC hBC v
  obtain ⟨D'₁, D'₂, hBA_eq, hD'₁, hD'₂⟩ := halfDist_exists_split hBC hAC v
  have hsplit : E = (D₁ + swap₁₂ D'₂) + (D₂ + swap₁₂ D'₁) := by
    dsimp only [E]
    rw [hAB_eq, hBA_eq, map_add]
    abel
  have h₂₃ : (mulSub₂₃ ^ t) (D₁ + swap₁₂ D'₂) = 0 := by
    rw [map_add, hD₁, mulSub₂₃_pow_swap₁₂, hD'₂, map_zero, zero_add]
  have h₁₃ : (mulSub₁₃ ^ s) (D₂ + swap₁₂ D'₁) = 0 := by
    rw [map_add, hD₂, mulSub₁₃_pow_swap₁₂, hD'₁, map_zero, zero_add]
  -- Step 3: Apply the expansion lemma and evaluate at `p = 0`.
  have hord : r + s + t + 1 = (r + 1) + s + t := by omega
  have hE0 : (mulSub₂₃ ^ (r + s + t + 1)) E = 0 := by
    rw [hord]
    exact mulSub₂₃_pow_eq_zero_of_split h₁₂ hsplit h₂₃ h₁₃
  have hE0_eval : (fun b c' ↦ E 0 b c') =
      fun b c' ↦ (((normalOrder A B).commutatorDistribution C) b c') v := by
    funext b c'
    exact halfDist_zero_add_swap A B C v b c'
  have hev := (mulSub_pow_comp ev (r + s + t + 1)
    ((normalOrder A B).commutatorDistribution C) m c).symm
  dsimp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at hev
  rw [hev, ← hE0_eval, ← mulSub₂₃_pow_eval, hE0]
  rfl

/-- **Dong's lemma for normal-ordered products** (right argument). -/
theorem normalOrder_right {A B C : VertexOperator R V} {r s t : ℕ}
    (hAB : A.IsLocalOfOrder B s) (hAC : A.IsLocalOfOrder C t) (hBC : B.IsLocalOfOrder C r) :
    A.IsLocalOfOrder (normalOrder B C) (r + s + t + 1) :=
  (hBC.normalOrder_left hAB.symm hAC.symm).symm

end IsLocalOfOrder

end VertexOperator
