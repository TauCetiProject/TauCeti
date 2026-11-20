/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeDA.Basic
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Fin.StrictMono
import TauCeti.Data.Matrix.Block

/-!
# The box tensor product of a type `DA` bimodule with morphisms of type `D` structures

For a type `DA` bimodule `P = ^B P_A` with generators `Y` and type `D` structures `N` and `N'`
over `A` with generators `X` and `X'`, the box tensor products `P ⊠ N` and `P ⊠ N'` are type `D`
structures over `B` (`TauCeti.TypeDAStructure.boxTypeD`). This file makes `P ⊠ –` act on
morphisms. A morphism `F` from `N` to `N'`, a matrix of coefficients, induces the morphism `P ⊠ F`
from `P ⊠ N` to `P ⊠ N'` (`TauCeti.TypeDAStructure.boxMorphism`): its coefficient from `(y, x)` to
`(y', x')` is the sum, over the paths `x = x₀ → ⋯ → xᵢ` in `X` and `x'₀ → ⋯ → x'ⱼ = x'` in `X'`,
of the coefficient from `y` to `y'` of

`δ¹_{i+j+2}(y, δ x₀ x₁, …, δ xᵢ₋₁ xᵢ, F xᵢ x'₀, δ' x'₀ x'₁, …, δ' x'ⱼ₋₁ x'ⱼ)`,

where `δ` and `δ'` are the coefficient matrices of `N` and `N'`. In the definition the paths run in
`X ⊕ X'`, along the block-diagonal matrix `fromBlocks δ 0 0 δ'` with the block
`fromBlocks 0 F 0 0` inserted at one step `l`; such a path contributes only when it stays in `X` up
to step `l` and in `X'` after it. The sum is finite under either of the two boundedness conditions
used for `TauCeti.TypeDStructure.typeABoxMap`: the operations of `P` vanish from some arity on
(the results named `_of_coeff_eq_zero`), or heights on the generators of `N` and of `N'` strictly
increase along their nonzero coefficients (the results named `_of_lt`). Otherwise it is a `finsum`,
`0` by convention.

* **Associativity.** The map induced by `F` on the box tensor products of the type `A` module
  `M ⊠ P` (`TauCeti.TypeDAStructure.boxModule`) with `N` and `N'`
  (`TauCeti.TypeDStructure.typeABoxMap`) is the action of `P ⊠ F` on the box tensor products of
  `M` with `P ⊠ N` and `P ⊠ N'`: `(M ⊠ P) ⊠ F = M ⊠ (P ⊠ F)`
  (`TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_coeff_eq_zero`,
  `TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_lt`). This is the counterpart for
  morphisms of the associativity `(M ⊠ P) ⊠ N = M ⊠ (P ⊠ N)` of
  `TauCeti.TypeDAStructure.typeABoxDifferential_boxModule_apply`.
* **The differential.** The differential of morphisms commutes with `P ⊠ –`:
  `∂(P ⊠ F) = P ⊠ ∂F` (`TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_coeff_eq_zero`,
  `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_lt`). For the type `A` module
  `B ⊠ P` the induced maps satisfy `∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}`
  (`TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_act_eq_zero`,
  `TauCeti.TypeDStructure.typeABoxDifferential_typeABoxMap_of_lt`), and by associativity, for the
  map and for the differential, this identity evaluated at the generator `1 ⊗ (y, x)` is the row of
  `∂(P ⊠ F) = P ⊠ ∂F` at `(y, x)`.
* **Homomorphisms and homotopies.** Since `P ⊠ –` is additive under the same boundedness
  conditions and sends `0` to `0`, a homomorphism of type `D` structures (`∂F = 0`) induces a
  homomorphism, and homotopic homomorphisms (`∂H = F + G`) induce homotopic homomorphisms, with
  homotopy `P ⊠ H`.

The composite `(P ⊠ F) * (P ⊠ G)` agrees with `P ⊠ (F * G)` only up to homotopy, and `P ⊠ –`
sends the identity morphism to the identity only for strictly unital bimodules; neither is treated
here.

## Main definitions

* `TauCeti.TypeDAStructure.boxMorphism`: the morphism `P ⊠ F` from `P ⊠ N` to `P ⊠ N'`.

## Main results

* `TauCeti.TypeDAStructure.boxMorphism_mem_morphisms`: `P ⊠ F` is compatible with the idempotents
  of `P ⊠ N` and `P ⊠ N'`.
* `TauCeti.TypeDAStructure.boxMorphism_eq_sum_of_coeff_eq_zero` and
  `TauCeti.TypeDAStructure.boxMorphism_eq_sum_of_lt`: `P ⊠ F` as a finite sum over paths.
* `TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_coeff_eq_zero` and
  `TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_lt`: `(M ⊠ P) ⊠ F = M ⊠ (P ⊠ F)`.
* `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_coeff_eq_zero` and
  `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_lt`: `∂(P ⊠ F) = P ⊠ ∂F`.
* `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_eq_zero_of_coeff_eq_zero`,
  `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_eq_add_of_coeff_eq_zero` and their
  `_of_lt` forms: `P ⊠ –` sends homomorphisms to homomorphisms and homotopies to homotopies.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (morphisms of type `D` structures and the functoriality of box tensor products).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), Section 2
  (type `DA` bimodules, their box tensor products and the induced maps on morphisms).
-/

public section

open Finset MulOpposite

namespace TauCeti

namespace TypeDAStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]
  {T : Type*} {ιA : T → A} {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X']
  [DecidableEq X'] (P : TypeDAStructure dA dB ιB Y) (N : TypeDStructure dA ιA X)
  (N' : TypeDStructure dA ιA X')

/-- The **morphism `P ⊠ F`** from `P ⊠ N` to `P ⊠ N'` induced by a matrix `F` from `N` to `N'`:
the coefficient from `(y, x)` to `(y', x')` is the sum, over the lengths `n`, the steps `l < n` and
the paths `r` in `X ⊕ X'` from `x` to `x'`, of the coefficient from `y` to `y'` of `δ¹_{n+1}`
evaluated on the entries of `fromBlocks δ 0 0 δ'` along `r`, with the entry of `fromBlocks 0 F 0 0`
at step `l`. The sum over `n` is finite when the operations of `P` vanish from some arity on or
heights increase along the coefficients of `N` and `N'`; otherwise this `finsum` is `0` by
convention. -/
noncomputable def boxMorphism (F : Matrix X X' A) : Matrix (Y × X) (Y × X') B :=
  fun p q => ∑ᶠ n, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ X',
    if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr q.2 then
      P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
        (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
    else 0

/-- Unfolding `P ⊠ F` as a sum over lengths, steps and paths. -/
theorem boxMorphism_apply (F : Matrix X X' A) (p : Y × X) (q : Y × X') :
    P.boxMorphism N N' F p q = ∑ᶠ n, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ X',
      if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr q.2 then
        P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
          (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
      else 0 :=
  (rfl)

/-- When the terms of length at least `K` vanish, the coefficients of `P ⊠ F` are the sums over the
lengths `n < K`. -/
theorem boxMorphism_eq_sum (F : Matrix X X' A) {K : ℕ}
    (hK : ∀ n, K ≤ n → ∀ (l : Fin n) (r : Fin (n + 1) → X ⊕ X'),
      P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
        (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) = 0)
    (p : Y × X) (q : Y × X') :
    P.boxMorphism N N' F p q = ∑ n ∈ range K, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ X',
      if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr q.2 then
        P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
          (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
      else 0 := by
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  rw [Function.mem_support] at hn
  simp only [coe_range, Set.mem_Iio]
  by_contra hlt
  exact hn (sum_eq_zero fun l _ => sum_eq_zero fun r _ => by
    rw [hK n (not_lt.mp hlt) l r, Matrix.zero_apply, ite_self])

/-- `P ⊠ 0 = 0`: every term has an entry of the zero matrix. -/
@[simp]
theorem boxMorphism_zero : P.boxMorphism N N' 0 = 0 := by
  ext p q
  rw [boxMorphism_apply, Matrix.zero_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun n => sum_eq_zero fun l _ => sum_eq_zero fun r _ => ?_
  rw [MultilinearMap.map_coord_zero _ l (by simp), Matrix.zero_apply, ite_self]

omit [DecidableEq X] [DecidableEq X'] in
/-- If heights on the generators of `N` and of `N'` strictly increase along their nonzero
coefficients, the terms of `P ⊠ F` of length at least the sum of the largest heights plus two
vanish: such a path meets a zero entry of `δ`, `F` or `δ'`. -/
private theorem coeff_update_eq_zero_of_lt (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) {n : ℕ}
    (hn : univ.sup h + univ.sup h' + 2 ≤ n) (l : Fin n) (r : Fin (n + 1) → X ⊕ X') :
    P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
      (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) = 0 := by
  by_contra hne
  -- Every entry along `r` is nonzero, so `sumHeight h h'` rises at every step of the path.
  have hstep (t : Fin n) : sumHeight h h' (r t.castSucc) <
      sumHeight h h' (r t.succ) := by
    have ht : Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
        (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ) ≠ 0 := fun h0 =>
      hne ((P.coeff n).map_coord_zero t h0)
    rcases eq_or_ne t l with rfl | htl
    · rw [Function.update_self] at ht
      exact sumHeight_lt_of_fromBlocks h (by simp) h' (by simp) F ht
    · rw [Function.update_of_ne htl] at ht
      exact sumHeight_lt_of_fromBlocks h hh h' hh' 0 ht
  have hr : StrictMono (sumHeight h h' ∘ r) := Fin.strictMono_iff_lt_succ.mpr hstep
  have := hr.le_univ_sup_nat
  have := univ_sup_sumHeight_le h h'
  omega

/-- **`P ⊠ F` for a bounded bimodule as a finite sum.** If the operations of `P` vanish from arity
`K` on, the coefficients of `P ⊠ F` are the sums over the lengths `n < K`. -/
theorem boxMorphism_eq_sum_of_coeff_eq_zero {K : ℕ} (hP : ∀ k, K ≤ k → P.coeff k = 0)
    (F : Matrix X X' A) (p : Y × X) (q : Y × X') :
    P.boxMorphism N N' F p q = ∑ n ∈ range K, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ X',
      if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr q.2 then
        P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
          (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
      else 0 :=
  P.boxMorphism_eq_sum N N' F (fun n hn _ _ => by rw [hP n hn, zero_apply]) p q

/-- **`P ⊠ F` for bounded type `D` structures as a finite sum.** If heights on the generators of
`N` and of `N'` strictly increase along their nonzero coefficients, the coefficients of `P ⊠ F` are
the sums over the lengths `n` less than the sum of the largest heights plus two. -/
theorem boxMorphism_eq_sum_of_lt (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y)
    (h' : X' → ℕ) (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) (p : Y × X)
    (q : Y × X') :
    P.boxMorphism N N' F p q =
      ∑ n ∈ range (univ.sup h + univ.sup h' + 2), ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ X',
        if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr q.2 then
          P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
        else 0 :=
  P.boxMorphism_eq_sum N N' F
    (fun _ hn l r => P.coeff_update_eq_zero_of_lt N N' h hh h' hh' F hn l r) p q

/-- The core of `TauCeti.TypeDAStructure.boxMorphism_add_of_coeff_eq_zero` and
`TauCeti.TypeDAStructure.boxMorphism_add_of_lt`: `P ⊠ –` is additive when a single length bounds
the nonzero terms of `P ⊠ G` for every `G`. -/
private theorem boxMorphism_add_of_bound {K : ℕ}
    (hK : ∀ G : Matrix X X' A, ∀ n, K ≤ n → ∀ (l : Fin n) (r : Fin (n + 1) → X ⊕ X'),
      P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
        (Matrix.fromBlocks 0 G 0 0) t (r t.castSucc) (r t.succ)) = 0)
    (F G : Matrix X X' A) :
    P.boxMorphism N N' (F + G) = P.boxMorphism N N' F + P.boxMorphism N N' G := by
  -- The entries along a path are those of `δ` and `δ'`, with one entry of `F + G` at step `l`.
  have hupd (E : Matrix (X ⊕ X') (X ⊕ X') A) (n : ℕ) (l : Fin n) (r : Fin (n + 1) → X ⊕ X') :
      (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l E t
        (r t.castSucc) (r t.succ)) =
      Function.update (fun t => Matrix.fromBlocks N.coeff 0 0 N'.coeff (r t.castSucc) (r t.succ))
        l (E (r l.castSucc) (r l.succ)) :=
    funext (Function.apply_update (fun t (E' : Matrix (X ⊕ X') (X ⊕ X') A) =>
      E' (r t.castSucc) (r t.succ)) _ l E)
  have hE : Matrix.fromBlocks (0 : Matrix X X A) (F + G) (0 : Matrix X' X A) (0 : Matrix X' X' A) =
      Matrix.fromBlocks 0 F 0 0 + Matrix.fromBlocks 0 G 0 0 := by
    simp [Matrix.fromBlocks_add]
  ext p q
  simp only [Matrix.add_apply, P.boxMorphism_eq_sum N N' _ (hK _), hE, hupd,
    MultilinearMap.map_update_add, ite_add_zero, Finset.sum_add_distrib]

/-- **Additivity of `P ⊠ F` for a bounded bimodule.** -/
theorem boxMorphism_add_of_coeff_eq_zero {K : ℕ} (hP : ∀ k, K ≤ k → P.coeff k = 0)
    (F G : Matrix X X' A) :
    P.boxMorphism N N' (F + G) = P.boxMorphism N N' F + P.boxMorphism N N' G :=
  P.boxMorphism_add_of_bound N N' (fun _ n hn _ _ => by rw [hP n hn, zero_apply]) F G

/-- **Additivity of `P ⊠ F` for bounded type `D` structures.** -/
theorem boxMorphism_add_of_lt (h : X → ℕ) (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F G : Matrix X X' A) :
    P.boxMorphism N N' (F + G) = P.boxMorphism N N' F + P.boxMorphism N N' G :=
  P.boxMorphism_add_of_bound N N'
    (fun H _ hn l r => P.coeff_update_eq_zero_of_lt N N' h hh h' hh' H hn l r) F G

/-- The coefficients of `P ⊠ F` from `(y, x)` lie in the summand of the idempotent of `y` on the
left. -/
theorem idem_mul_boxMorphism (F : Matrix X X' A) (p : Y × X) (q : Y × X') :
    ιB (P.idem p.1) * P.boxMorphism N N' F p q = P.boxMorphism N N' F p q :=
  mul_finsum_of_forall fun n => by
    simp only [Finset.mul_sum, mul_ite, mul_zero, P.idem_mul_coeff]

/-- The coefficients of `P ⊠ F` to `(y', x')` lie in the summand of the idempotent of `y'` on the
right. -/
theorem boxMorphism_mul_idem (F : Matrix X X' A) (p : Y × X) (q : Y × X') :
    P.boxMorphism N N' F p q * ιB (P.idem q.1) = P.boxMorphism N N' F p q :=
  finsum_mul_of_forall fun n => by
    simp only [Finset.sum_mul, ite_mul, zero_mul, P.coeff_mul_idem]

/-- **`P ⊠ F` is a morphism** from `P ⊠ N` to `P ⊠ N'`: its coefficients are compatible with the
idempotents of the generators of `P`. -/
theorem boxMorphism_mem_morphisms [CharP R 2] (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A) :
    P.boxMorphism N N' F ∈
      TypeDStructure.morphisms (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN') :=
  TypeDStructure.mem_morphisms_iff.mpr fun p q => by
    simp only [boxTypeD_idem]
    exact ⟨P.idem_mul_boxMorphism N N' F p q, P.boxMorphism_mul_idem N N' F p q⟩

section Associativity

variable {M : Type*} [AddCommGroup M] [Module R M] [Module Bᵐᵒᵖ M] [SMulCommClass R Bᵐᵒᵖ M]
  [IsScalarTower R Bᵐᵒᵖ M] [CharP R 2] {dM : M →ₗ[R] M}

/-- The core of `TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_coeff_eq_zero` and
`TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_lt`: both sides are sums over the paths of
lengths `n < K`, the terms of the induced map are the operations `δ¹_{n+1}` of `P` acting on
`φ`, and only the paths starting in `X` contribute. -/
private theorem typeABoxMap_boxModule_apply_of_eq_sum (hM : IsUngradedDGRightModule dB dM)
    (F : Matrix X X' A) {K : ℕ}
    (hT : ∀ (φ : X → Y → M) (z : X'), TypeDStructure.typeABoxMap N N' (P.boxModule hM) F φ z =
      ∑ n ∈ range K, ∑ l : Fin n, ∑ x : Fin (n + 1) → X ⊕ X',
        if x (Fin.last n) = Sum.inr z then
          (P.boxModule hM).act n (fun t => Function.update
            (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t (x t.castSucc) (x t.succ)) (Sum.elim φ 0 (x 0))
        else 0)
    (hK : ∀ n, K ≤ n → ∀ (l : Fin n) (r : Fin (n + 1) → X ⊕ X'),
      P.coeff n (fun t => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
        (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) = 0)
    (φ : X → Y → M) (z : X') (y' : Y) :
    TypeDStructure.typeABoxMap N N' (P.boxModule hM) F φ z y' =
      continuationMap R M (P.boxMorphism N N' F) (fun p => φ p.2 p.1) (y', z) := by
  -- Each term of the induced map is an operation `δ¹_{n+1}` of `P`, with `n ≥ 1` since `F` occurs.
  have hterm (n : ℕ) (l : Fin n) (r : Fin (n + 1) → X ⊕ X') :
      (if r (Fin.last n) = Sum.inr z then
          (P.boxModule hM).act n (fun t => Function.update
            (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) (Sum.elim φ 0 (r 0))
        else 0) y' =
        ∑ p : Y × X, if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr z then
          op (P.coeff n (fun t => Function.update
            (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t (r t.castSucc) (r t.succ)) p.1 y') • φ p.2 p.1
        else 0 := by
    have hc (G : Matrix Y Y B) (ψ : Y → M) :
        continuationMap R M G ψ y' = ∑ y, op (G y y') • ψ y :=
      continuationMap_apply (R := R) (M := M) G ψ y'
    split_ifs with hz
    · rw [boxModule_act_apply, ite_eq_right l.pos.ne', zero_add]
      simp only [hc]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun y _ => ?_
      rcases r 0 with x₀ | x₀
      · simp [hz]
      · simp
    · simp [hz]
  rw [hT, Finset.sum_apply]
  simp only [Finset.sum_apply, hterm]
  rw [continuationMap_apply (R := R) (M := M) (P.boxMorphism N N' F)]
  simp only [P.boxMorphism_eq_sum N N' F hK, Finset.op_sum, Finset.sum_smul, apply_ite op, op_zero,
    ite_smul, zero_smul]
  -- Reorder `∑ p, ∑ n, ∑ l, ∑ r` into `∑ n, ∑ l, ∑ r, ∑ p`.
  rw [Finset.sum_comm (s := univ) (t := range K)]
  exact Finset.sum_congr rfl fun n _ =>
    (Finset.sum_congr rfl fun l _ => Finset.sum_comm).trans Finset.sum_comm

/-- **Associativity of the box tensor product with a morphism, for a bounded bimodule.** If the
operations `δ¹_{k+1}` of `P` vanish for `k ≥ K`, the map induced by a matrix `F` from `N` to `N'`
on the box tensor products of the type `A` module `M ⊠ P` is the action of `P ⊠ F` on the box
tensor products of `M` with `P ⊠ N` and `P ⊠ N'`: `(M ⊠ P) ⊠ F = M ⊠ (P ⊠ F)`, under the
identification of the row vectors `X → Y → M` with the row vectors `Y × X → M`. -/
theorem typeABoxMap_boxModule_apply_of_coeff_eq_zero (hM : IsUngradedDGRightModule dB dM) {K : ℕ}
    (hP : ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A) (φ : X → Y → M) (z : X') (y' : Y) :
    TypeDStructure.typeABoxMap N N' (P.boxModule hM) F φ z y' =
      continuationMap R M (P.boxMorphism N N' F) (fun p => φ p.2 p.1) (y', z) :=
  P.typeABoxMap_boxModule_apply_of_eq_sum N N' hM F (K := K + 1)
    (TypeDStructure.typeABoxMap_apply_eq_sum_of_act_eq_zero N N' _ F
      fun n hn => P.boxModule_act_eq_zero hM (by omega) (hP n (by omega)))
    (fun n hn l r => by rw [hP n (by omega), zero_apply]) φ z y'

/-- **Associativity of the box tensor product with a morphism, for bounded type `D`
structures.** If heights on the generators of `N` and of `N'` strictly increase along their
nonzero coefficients, `(M ⊠ P) ⊠ F = M ⊠ (P ⊠ F)` as in
`TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_coeff_eq_zero`, whatever the operations of
`P`. -/
theorem typeABoxMap_boxModule_apply_of_lt (hM : IsUngradedDGRightModule dB dM) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) (φ : X → Y → M) (z : X')
    (y' : Y) :
    TypeDStructure.typeABoxMap N N' (P.boxModule hM) F φ z y' =
      continuationMap R M (P.boxMorphism N N' F) (fun p => φ p.2 p.1) (y', z) :=
  P.typeABoxMap_boxModule_apply_of_eq_sum N N' hM F
    (TypeDStructure.typeABoxMap_apply_eq_sum_of_lt N N' _ h hh h' hh' F)
    (fun _ hn l r => P.coeff_update_eq_zero_of_lt N N' h hh h' hh' F hn l r) φ z y'

end Associativity

/-! ### The differential of `P ⊠ F` -/

section Differential

variable [CharP R 2]

/-- The core of `TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_coeff_eq_zero` and
`TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_of_lt`: the identity
`∂' ∘ T_F + T_F ∘ ∂ = T_{∂F}` for the type `A` module `B ⊠ P`, read on the generators `1 ⊗ p`
through associativity. -/
private theorem morphismDifferential_boxMorphism_of_assoc (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A)
    (hassoc : ∀ (G : Matrix X X' A) (φ : X → Y → B) (z : X') (y' : Y),
      TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule) G φ z y' =
        continuationMap R B (P.boxMorphism N N' G) (fun p => φ p.2 p.1) (y', z))
    (htypeA : ∀ φ : X → Y → B,
      N'.typeABoxDifferential (P.boxModule hdB.isUngradedDGRightModule)
          (TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule) F φ) +
        TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule) F
          (N.typeABoxDifferential (P.boxModule hdB.isUngradedDGRightModule) φ) =
      TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule)
        (TypeDStructure.morphismDifferential N N' F) φ) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
        (P.boxMorphism N N' F) =
      P.boxMorphism N N' (TypeDStructure.morphismDifferential N N' F) := by
  classical
  have hB := hdB.isUngradedDGRightModule
  ext p q
  -- The generator `1 ⊗ p` of `B ⊠ (P ⊠ N)`, as a row vector of `B ⊠ P` over `N`.
  set e : X → Y → B := fun x y => Pi.single (M := fun _ : Y × X => B) p 1 (y, x) with he
  have hsingle : (fun q : Y × X => e q.2 q.1) = Pi.single p 1 := by
    funext q
    simp [he]
  -- The map induced by `G` sends it to the row of `P ⊠ G` at `p`.
  have hmap (G : Matrix X X' A) :
      TypeDStructure.typeABoxMap N N' (P.boxModule hB) G e =
        fun z y' => P.boxMorphism N N' G p (y', z) := by
    funext z y'
    rw [hassoc, hsingle, continuationMap_single_apply (R := R) (M := B) (P.boxMorphism N N' G),
      op_smul_eq_mul, one_mul]
  -- The box tensor differential sends it to the row of `P ⊠ N` at `p`.
  have hrow : N.typeABoxDifferential (P.boxModule hB) e = fun x y => P.boxCoeff N p (y, x) := by
    funext x y
    rw [P.typeABoxDifferential_boxModule_apply N hB hN, hsingle,
      continuationMap_single_apply (R := R) (M := B) (P.boxCoeff N), op_smul_eq_mul, one_mul]
    simp only [he]
    rcases eq_or_ne (y, x) p with hp | hp
    · rw [hp, Pi.single_eq_same, hdB.map_one, zero_add]
    · rw [Pi.single_eq_of_ne hp, map_zero, zero_add]
  have h₀ := congrFun (congrFun (htypeA e) q.2) q.1
  rw [hmap, hrow, hmap, Pi.add_apply, Pi.add_apply,
    P.typeABoxDifferential_boxModule_apply N' hB hN', hassoc,
    continuationMap_apply (R := R) (M := B) (P.boxCoeff N'),
    continuationMap_apply (R := R) (M := B) (P.boxMorphism N N' F)] at h₀
  simp only [Prod.mk.eta, op_smul_eq_mul] at h₀
  rw [TypeDStructure.morphismDifferential_apply, boxTypeD_coeff, boxTypeD_coeff, ← h₀]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply]

/-- **`P ⊠ –` commutes with the differential of morphisms, for a bounded bimodule.** Over a ring
of characteristic two, if the operations `δ¹_{k+1}` of `P` vanish for `k ≥ K`, then for every
matrix `F` from `N` to `N'` the differential of the morphism `P ⊠ F` from `P ⊠ N` to `P ⊠ N'` is
`P ⊠ ∂F`. -/
theorem morphismDifferential_boxMorphism_of_coeff_eq_zero (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hP : ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
        (P.boxMorphism N N' F) =
      P.boxMorphism N N' (TypeDStructure.morphismDifferential N N' F) :=
  P.morphismDifferential_boxMorphism_of_assoc N N' hdB hN hN' F
    (fun G => P.typeABoxMap_boxModule_apply_of_coeff_eq_zero N N' _ hP G)
    (TypeDStructure.typeABoxDifferential_typeABoxMap_of_act_eq_zero N N' _ (K := K + 1)
      (fun n hn => P.boxModule_act_eq_zero _ (by omega) (hP n (by omega))) F)

/-- **`P ⊠ –` commutes with the differential of morphisms, for bounded type `D` structures.**
Over a ring of characteristic two, if heights on the generators of `N` and of `N'` strictly
increase along their nonzero coefficients, then for every matrix `F` from `N` to `N'` the
differential of the morphism `P ⊠ F` from `P ⊠ N` to `P ⊠ N'` is `P ⊠ ∂F`, whatever the operations
of `P`. -/
theorem morphismDifferential_boxMorphism_of_lt (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (F : Matrix X X' A) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
        (P.boxMorphism N N' F) =
      P.boxMorphism N N' (TypeDStructure.morphismDifferential N N' F) :=
  P.morphismDifferential_boxMorphism_of_assoc N N' hdB hN hN' F
    (fun G => P.typeABoxMap_boxModule_apply_of_lt N N' _ h hh h' hh' G)
    (TypeDStructure.typeABoxDifferential_typeABoxMap_of_lt N N' _ h hh h' hh' F)

/-- **A homomorphism tensored with a bounded bimodule is a homomorphism.** If `∂F = 0`, then
`∂(P ⊠ F) = 0`. -/
theorem morphismDifferential_boxMorphism_eq_zero_of_coeff_eq_zero (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hP : ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A}
    (hF : TypeDStructure.morphismDifferential N N' F = 0) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
      (P.boxMorphism N N' F) = 0 := by
  rw [P.morphismDifferential_boxMorphism_of_coeff_eq_zero N N' hdB hN hN' hP, hF, boxMorphism_zero]

/-- **A homomorphism of bounded type `D` structures tensored with a bimodule is a homomorphism.**
If `∂F = 0`, then `∂(P ⊠ F) = 0`. -/
theorem morphismDifferential_boxMorphism_eq_zero_of_lt (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F : Matrix X X' A}
    (hF : TypeDStructure.morphismDifferential N N' F = 0) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
      (P.boxMorphism N N' F) = 0 := by
  rw [P.morphismDifferential_boxMorphism_of_lt N N' hdB hN hN' h hh h' hh', hF, boxMorphism_zero]

/-- **Homotopic homomorphisms tensored with a bounded bimodule are homotopic.** If
`∂H = F + G`, then `∂(P ⊠ H) = P ⊠ F + P ⊠ G`. -/
theorem morphismDifferential_boxMorphism_eq_add_of_coeff_eq_zero (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hP : ∀ k, K ≤ k → P.coeff k = 0) {F G H : Matrix X X' A}
    (hH : TypeDStructure.morphismDifferential N N' H = F + G) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
      (P.boxMorphism N N' H) = P.boxMorphism N N' F + P.boxMorphism N N' G := by
  rw [P.morphismDifferential_boxMorphism_of_coeff_eq_zero N N' hdB hN hN' hP, hH,
    P.boxMorphism_add_of_coeff_eq_zero N N' hP]

/-- **Homotopic homomorphisms of bounded type `D` structures tensored with a bimodule are
homotopic.** If `∂H = F + G`, then `∂(P ⊠ H) = P ⊠ F + P ⊠ G`. -/
theorem morphismDifferential_boxMorphism_eq_add_of_lt (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F G H : Matrix X X' A}
    (hH : TypeDStructure.morphismDifferential N N' H = F + G) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
      (P.boxMorphism N N' H) = P.boxMorphism N N' F + P.boxMorphism N N' G := by
  rw [P.morphismDifferential_boxMorphism_of_lt N N' hdB hN hN' h hh h' hh', hH,
    P.boxMorphism_add_of_lt N N' h hh h' hh']

end Differential

end TypeDAStructure

end TauCeti
