/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeDA.Morphism
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Matrix.Block

/-!
# Composites of morphisms on box tensor products with a type `DA` bimodule

For a type `DA` bimodule `P = ^B P_A` with generators `Y`, a matrix `F` from a type `D` structure
`N` to `N'` over `A` induces the morphism `P ⊠ F` from `P ⊠ N` to `P ⊠ N'`
(`TauCeti.TypeDAStructure.boxMorphism`). This file compares the composite
`(P ⊠ F) * (P ⊠ G)` with `P ⊠ (F * G)` for a second matrix `G` from `N'` to `N''`. They differ in
general, since `P ⊠ (F * G)` feeds `F` and `G` to `P` as one entry `F * G`, while the composite
feeds them in two separate operations, but they are homotopic when `F` and `G` are homomorphisms.

The homotopy `P ⊠ (F, G)` (`TauCeti.TypeDAStructure.boxCompHomotopy`) has coefficient from
`(y, x)` to `(y', x'')` the sum, over the paths `x = x₀ → ⋯ → xᵢ` in `X`, `x'₀ → ⋯ → x'ⱼ` in `X'`
and `x''₀ → ⋯ → x''ₖ = x''` in `X''`, of the coefficient from `y` to `y'` of

`δ¹_{i+j+k+3}(y, δ x₀ x₁, …, F xᵢ x'₀, δ' x'₀ x'₁, …, G x'ⱼ x''₀, δ'' x''₀ x''₁, …)`,

where `δ`, `δ'` and `δ''` are the coefficient matrices of `N`, `N'` and `N''`. In the definition
the paths run in `X ⊕ (X' ⊕ X'')`: they follow the block matrix with diagonal blocks `δ` and
`fromBlocks δ' G 0 δ''`, the coefficient matrix of the mapping cone of `G`, with the block
`fromCols F 0` inserted at one step. So when `G` is a homomorphism, `P ⊠ (F, G)` is the
`N''`-component of the morphism `P ⊠ fromCols F 0` from `P ⊠ N` to the box tensor product of `P`
with the mapping cone of `G` (`TauCeti.TypeDAStructure.boxCompHomotopy_eq_boxMorphism`).

**Composites up to homotopy.** Over a ring of characteristic two, if `F` and `G` are
homomorphisms of type `D` structures, then

`∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)`,

when the operations of `P` vanish from some arity on
(`TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_coeff_eq_zero`) or heights on
the generators of `N`, `N'` and `N''` strictly increase along their nonzero coefficients
(`TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_lt`). The proof reads the
corresponding identity for the type `A` module `B ⊠ P`,
`T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂`
(`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero` and
`TauCeti.TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt`), on the generators
`1 ⊗ (y, x)`, through the associativity `(B ⊠ P) ⊠ F = B ⊠ (P ⊠ F)`
(`TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_coeff_eq_zero`,
`TauCeti.TypeDAStructure.typeABoxMap_boxModule_apply_of_lt`) applied to `F`, `G`, `F * G` and to
the morphism `fromCols F 0` into the mapping cone of `G`, whose induced map is the homotopy `K`
(`TauCeti.TypeDStructure.typeABoxCompHomotopy_apply_eq_typeABoxMap`).

Together with the action of `P ⊠ –` on homomorphisms and homotopies
(`TauCeti.TypeDAStructure.morphismDifferential_boxMorphism_eq_add_of_coeff_eq_zero` and its
`_of_lt` form), this shows that `P ⊠ –` respects composition of homomorphisms up to homotopy.

## Main definitions

* `TauCeti.TypeDAStructure.boxCompHomotopy`: the homotopy `P ⊠ (F, G)` from `P ⊠ N` to `P ⊠ N''`.

## Main results

* `TauCeti.TypeDAStructure.boxCompHomotopy_eq_boxMorphism`: for a homomorphism `G`, `P ⊠ (F, G)`
  is the `N''`-component of `P ⊠ fromCols F 0` into the box tensor product with the mapping cone
  of `G`.
* `TauCeti.TypeDAStructure.boxCompHomotopy_mem_morphisms`: `P ⊠ (F, G)` is compatible with the
  idempotents of `P ⊠ N` and `P ⊠ N''`.
* `TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_coeff_eq_zero` and
  `TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_lt`:
  `∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)` for homomorphisms `F` and `G`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (morphisms of type `D` structures, their composition, and the functoriality of box
  tensor products up to homotopy).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), Section 2
  (type `DA` bimodules and the maps they induce on morphisms of type `D` structures).
-/

public section

open Finset MulOpposite

namespace TauCeti

namespace TypeDAStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]
  {T : Type*} {ιA : T → A} {X X' X'' : Type*} [Fintype X] [DecidableEq X] [Fintype X']
  [DecidableEq X'] [Fintype X''] [DecidableEq X''] (P : TypeDAStructure dA dB ιB Y)
  (N : TypeDStructure dA ιA X) (N' : TypeDStructure dA ιA X') (N'' : TypeDStructure dA ιA X'')

/-- The **homotopy `P ⊠ (F, G)`** from `P ⊠ N` to `P ⊠ N''` between the composite
`(P ⊠ F) * (P ⊠ G)` and `P ⊠ (F * G)`, for matrices `F` from `N` to `N'` and `G` from `N'` to
`N''`: the coefficient from `(y, x)` to `(y', x'')` is the sum, over the lengths `n`, the steps
`l < n` and the paths `r` in `X ⊕ (X' ⊕ X'')` from `x` to `x''`, of the coefficient from `y` to
`y'` of `δ¹_{n+1}` evaluated on the entries along `r` of the block matrix with diagonal blocks `δ`
and `fromBlocks δ' G 0 δ''`, with the entry of the block `fromCols F 0` at step `l`. Such a path
stays in `X` up to step `l`, then steps through `F` into `X'` and later through `G` into `X''`.
As for `TauCeti.TypeDAStructure.boxMorphism`, the sum over `n` is finite when the operations of
`P` vanish from some arity on or heights increase along the coefficients of `N`, `N'` and `N''`;
otherwise this `finsum` is `0` by convention. -/
noncomputable def boxCompHomotopy (F : Matrix X X' A) (G : Matrix X' X'' A) :
    Matrix (Y × X) (Y × X'') B :=
  fun p q => ∑ᶠ n, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ (X' ⊕ X''),
    if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr (Sum.inr q.2) then
      P.coeff n (fun t => Function.update
        (fun _ => Matrix.fromBlocks N.coeff 0 0 (Matrix.fromBlocks N'.coeff G 0 N''.coeff)) l
        (Matrix.fromBlocks 0 (Matrix.fromCols F 0) 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
    else 0

/-- Unfolding `P ⊠ (F, G)` as a sum over lengths, steps and paths. -/
theorem boxCompHomotopy_apply (F : Matrix X X' A) (G : Matrix X' X'' A) (p : Y × X)
    (q : Y × X'') :
    P.boxCompHomotopy N N' N'' F G p q = ∑ᶠ n, ∑ l : Fin n, ∑ r : Fin (n + 1) → X ⊕ (X' ⊕ X''),
      if r 0 = Sum.inl p.2 ∧ r (Fin.last n) = Sum.inr (Sum.inr q.2) then
        P.coeff n (fun t => Function.update
          (fun _ => Matrix.fromBlocks N.coeff 0 0 (Matrix.fromBlocks N'.coeff G 0 N''.coeff)) l
          (Matrix.fromBlocks 0 (Matrix.fromCols F 0) 0 0) t (r t.castSucc) (r t.succ)) p.1 q.1
      else 0 :=
  (rfl)

variable {N' N''} in
/-- **`P ⊠ (F, G)` through the mapping cone.** For a homomorphism `G` from `N'` to `N''`, the
homotopy `P ⊠ (F, G)` is the `N''`-component of the morphism `P ⊠ fromCols F 0` from `P ⊠ N` to
the box tensor product of `P` with the mapping cone of `G`. -/
theorem boxCompHomotopy_eq_boxMorphism (F : Matrix X X' A) {G : Matrix X' X'' A}
    (hG : G ∈ TypeDStructure.morphisms N' N'')
    (hG' : TypeDStructure.morphismDifferential N' N'' G = 0) (p : Y × X) (q : Y × X'') :
    P.boxCompHomotopy N N' N'' F G p q =
      P.boxMorphism N (TypeDStructure.cone N' N'' G hG hG') (Matrix.fromCols F 0) p
        (q.1, Sum.inr q.2) := by
  rw [boxCompHomotopy_apply, boxMorphism_apply, TypeDStructure.cone_coeff]

/-- The coefficients of `P ⊠ (F, G)` from `(y, x)` lie in the summand of the idempotent of `y` on
the left. -/
theorem idem_mul_boxCompHomotopy (F : Matrix X X' A) (G : Matrix X' X'' A) (p : Y × X)
    (q : Y × X'') :
    ιB (P.idem p.1) * P.boxCompHomotopy N N' N'' F G p q = P.boxCompHomotopy N N' N'' F G p q :=
  mul_finsum_of_forall fun n => by
    simp only [Finset.mul_sum, mul_ite, mul_zero, P.idem_mul_coeff]

/-- The coefficients of `P ⊠ (F, G)` to `(y', x'')` lie in the summand of the idempotent of `y'`
on the right. -/
theorem boxCompHomotopy_mul_idem (F : Matrix X X' A) (G : Matrix X' X'' A) (p : Y × X)
    (q : Y × X'') :
    P.boxCompHomotopy N N' N'' F G p q * ιB (P.idem q.1) = P.boxCompHomotopy N N' N'' F G p q :=
  finsum_mul_of_forall fun n => by
    simp only [Finset.sum_mul, ite_mul, zero_mul, P.coeff_mul_idem]

/-- **`P ⊠ (F, G)` is a morphism** from `P ⊠ N` to `P ⊠ N''`: its coefficients are compatible
with the idempotents of the generators of `P`. -/
theorem boxCompHomotopy_mem_morphisms [CharP R 2] (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN'' : N''.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A)
    (G : Matrix X' X'' A) :
    P.boxCompHomotopy N N' N'' F G ∈
      TypeDStructure.morphisms (P.boxTypeD N hdB hN) (P.boxTypeD N'' hdB hN'') :=
  TypeDStructure.mem_morphisms_iff.mpr fun p q => by
    simp only [boxTypeD_idem]
    exact ⟨P.idem_mul_boxCompHomotopy N N' N'' F G p q,
      P.boxCompHomotopy_mul_idem N N' N'' F G p q⟩

/-! ### Composites up to homotopy -/

section Composite

variable [CharP R 2]

/-- The core of `TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_coeff_eq_zero`
and `TauCeti.TypeDAStructure.morphismDifferential_boxCompHomotopy_of_lt`: the identity
`T_G ∘ T_F + T_{F G} = ∂'' ∘ K + K ∘ ∂` for the type `A` module `B ⊠ P`, read on the generators
`1 ⊗ p` through associativity for `F`, `G`, `F * G` and `fromCols F 0`. -/
private theorem morphismDifferential_boxCompHomotopy_of_assoc (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN'' : N''.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A}
    {G : Matrix X' X'' A} (hG : G ∈ TypeDStructure.morphisms N' N'')
    (hG' : TypeDStructure.morphismDifferential N' N'' G = 0)
    (hF₁ : ∀ (φ : X → Y → B) (z : X') (y' : Y),
      TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule) F φ z y' =
        continuationMap R B (P.boxMorphism N N' F) (fun p => φ p.2 p.1) (y', z))
    (hG₁ : ∀ (φ : X' → Y → B) (z : X'') (y' : Y),
      TypeDStructure.typeABoxMap N' N'' (P.boxModule hdB.isUngradedDGRightModule) G φ z y' =
        continuationMap R B (P.boxMorphism N' N'' G) (fun p => φ p.2 p.1) (y', z))
    (hFG₁ : ∀ (φ : X → Y → B) (z : X'') (y' : Y),
      TypeDStructure.typeABoxMap N N'' (P.boxModule hdB.isUngradedDGRightModule) (F * G) φ z y' =
        continuationMap R B (P.boxMorphism N N'' (F * G)) (fun p => φ p.2 p.1) (y', z))
    (hcone : ∀ (φ : X → Y → B) (z : X' ⊕ X'') (y' : Y),
      TypeDStructure.typeABoxMap N (TypeDStructure.cone N' N'' G hG hG')
          (P.boxModule hdB.isUngradedDGRightModule) (Matrix.fromCols F 0) φ z y' =
        continuationMap R B
          (P.boxMorphism N (TypeDStructure.cone N' N'' G hG hG') (Matrix.fromCols F 0))
          (fun p => φ p.2 p.1) (y', z))
    (htypeA : ∀ φ : X → Y → B,
      TypeDStructure.typeABoxMap N' N'' (P.boxModule hdB.isUngradedDGRightModule) G
          (TypeDStructure.typeABoxMap N N' (P.boxModule hdB.isUngradedDGRightModule) F φ) +
        TypeDStructure.typeABoxMap N N'' (P.boxModule hdB.isUngradedDGRightModule) (F * G) φ =
      N''.typeABoxDifferential (P.boxModule hdB.isUngradedDGRightModule)
          (TypeDStructure.typeABoxCompHomotopy N N' N''
            (P.boxModule hdB.isUngradedDGRightModule) F G φ) +
        TypeDStructure.typeABoxCompHomotopy N N' N'' (P.boxModule hdB.isUngradedDGRightModule)
          F G (N.typeABoxDifferential (P.boxModule hdB.isUngradedDGRightModule) φ)) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N'' hdB hN'')
        (P.boxCompHomotopy N N' N'' F G) =
      P.boxMorphism N N' F * P.boxMorphism N' N'' G + P.boxMorphism N N'' (F * G) := by
  classical
  have hB := hdB.isUngradedDGRightModule
  ext p q
  -- The generator `1 ⊗ p` of `B ⊠ (P ⊠ N)`, as a row vector of `B ⊠ P` over `N`.
  set e : X → Y → B := fun x y => Pi.single (M := fun _ : Y × X => B) p 1 (y, x) with he
  -- The maps induced by `F` and `F * G` send `e` to the rows of `P ⊠ F` and `P ⊠ (F * G)` at `p`.
  have hmapF : TypeDStructure.typeABoxMap N N' (P.boxModule hB) F e =
      fun z y' => P.boxMorphism N N' F p (y', z) :=
    P.typeABoxMap_boxModule_single N N' hdB F hF₁ p
  have hmapFG : TypeDStructure.typeABoxMap N N'' (P.boxModule hB) (F * G) e =
      fun z y' => P.boxMorphism N N'' (F * G) p (y', z) :=
    P.typeABoxMap_boxModule_single N N'' hdB (F * G) hFG₁ p
  -- The homotopy of `B ⊠ P` is the map induced by `fromCols F 0` into the mapping cone of `G`.
  have hK (φ : X → Y → B) (z : X'') (y' : Y) :
      TypeDStructure.typeABoxCompHomotopy N N' N'' (P.boxModule hB) F G φ z y' =
        ∑ r : Y × X, φ r.2 r.1 * P.boxCompHomotopy N N' N'' F G r (y', z) := by
    rw [TypeDStructure.typeABoxCompHomotopy_apply_eq_typeABoxMap N _ F hG hG', hcone,
      continuationMap_apply (R := R) (M := B)
        (P.boxMorphism N (TypeDStructure.cone N' N'' G hG hG') (Matrix.fromCols F 0))]
    simp only [op_smul_eq_mul, P.boxCompHomotopy_eq_boxMorphism N F hG hG']
  have hKe : TypeDStructure.typeABoxCompHomotopy N N' N'' (P.boxModule hB) F G e =
      fun z y' => P.boxCompHomotopy N N' N'' F G p (y', z) := by
    funext z y'
    rw [hK]
    simp only [he]
    rw [Finset.sum_eq_single p (fun r _ hr => by rw [Prod.mk.eta, Pi.single_eq_of_ne hr, zero_mul])
      (by simp), Prod.mk.eta, Pi.single_eq_same, one_mul]
  -- The box tensor differential sends `e` to the row of `P ⊠ N` at `p`.
  have hrow : N.typeABoxDifferential (P.boxModule hB) e = fun x y => P.boxCoeff N p (y, x) :=
    P.typeABoxDifferential_boxModule_single N hdB hN p
  have h₀ := congrFun (congrFun (htypeA e) q.2) q.1
  rw [hmapF, hmapFG, hKe, hrow, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, hG₁,
    P.typeABoxDifferential_boxModule_apply N'' hB hN'', hK,
    continuationMap_apply (R := R) (M := B) (P.boxMorphism N' N'' G),
    continuationMap_apply (R := R) (M := B) (P.boxCoeff N'')] at h₀
  simp only [Prod.mk.eta, op_smul_eq_mul] at h₀
  rw [TypeDStructure.morphismDifferential_apply, boxTypeD_coeff, boxTypeD_coeff]
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply]
  rw [h₀]

/-- **`P ⊠ –` respects composites of homomorphisms up to homotopy, for a bounded bimodule.** Over a
ring of characteristic two, let the operations `δ¹_{k+1}` of `P` vanish for `k ≥ K`, and let `F`
from `N` to `N'` and `G` from `N'` to `N''` be homomorphisms of type `D` structures. Then the
composite `(P ⊠ F) * (P ⊠ G)` and `P ⊠ (F * G)` are homotopic, with homotopy `P ⊠ (F, G)`:
`∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)`. -/
theorem morphismDifferential_boxCompHomotopy_of_coeff_eq_zero (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN'' : N''.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hP : ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A} {G : Matrix X' X'' A}
    (hF : TypeDStructure.morphismDifferential N N' F = 0)
    (hG : G ∈ TypeDStructure.morphisms N' N'')
    (hG' : TypeDStructure.morphismDifferential N' N'' G = 0) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N'' hdB hN'')
        (P.boxCompHomotopy N N' N'' F G) =
      P.boxMorphism N N' F * P.boxMorphism N' N'' G + P.boxMorphism N N'' (F * G) :=
  P.morphismDifferential_boxCompHomotopy_of_assoc N N' N'' hdB hN hN'' hG hG'
    (P.typeABoxMap_boxModule_apply_of_coeff_eq_zero N N' _ hP F)
    (P.typeABoxMap_boxModule_apply_of_coeff_eq_zero N' N'' _ hP G)
    (P.typeABoxMap_boxModule_apply_of_coeff_eq_zero N N'' _ hP (F * G))
    (P.typeABoxMap_boxModule_apply_of_coeff_eq_zero N _ _ hP (Matrix.fromCols F 0))
    (TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_act_eq_zero N N' N'' _
      (K := K + 1) (fun n hn => P.boxModule_act_eq_zero _ (by omega) (hP n (by omega))) hF hG hG')

/-- **`P ⊠ –` respects composites of homomorphisms of bounded type `D` structures up to
homotopy.** Over a ring of characteristic two, let heights on the generators of `N`, `N'` and
`N''` strictly increase along their nonzero coefficients, and let `F` from `N` to `N'` and `G`
from `N'` to `N''` be homomorphisms of type `D` structures. Then, whatever the operations of `P`,
`∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)`. -/
theorem morphismDifferential_boxCompHomotopy_of_lt (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN'' : N''.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) (h'' : X'' → ℕ)
    (hh'' : ∀ x y, N''.coeff x y ≠ 0 → h'' x < h'' y) {F : Matrix X X' A} {G : Matrix X' X'' A}
    (hF : TypeDStructure.morphismDifferential N N' F = 0)
    (hG : G ∈ TypeDStructure.morphisms N' N'')
    (hG' : TypeDStructure.morphismDifferential N' N'' G = 0) :
    TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N'' hdB hN'')
        (P.boxCompHomotopy N N' N'' F G) =
      P.boxMorphism N N' F * P.boxMorphism N' N'' G + P.boxMorphism N N'' (F * G) :=
  P.morphismDifferential_boxCompHomotopy_of_assoc N N' N'' hdB hN hN'' hG hG'
    (P.typeABoxMap_boxModule_apply_of_lt N N' _ h hh h' hh' F)
    (P.typeABoxMap_boxModule_apply_of_lt N' N'' _ h' hh' h'' hh'' G)
    (P.typeABoxMap_boxModule_apply_of_lt N N'' _ h hh h'' hh'' (F * G))
    -- The coefficients of the mapping cone of `G` increase the height of `X''` shifted above `X'`.
    (P.typeABoxMap_boxModule_apply_of_lt N _ _ h hh (sumHeight h' h'')
      (fun _ _ hab => sumHeight_lt_of_fromBlocks h' hh' h'' hh'' G
        (by rwa [TypeDStructure.cone_coeff] at hab)) (Matrix.fromCols F 0))
    (TypeDStructure.typeABoxMap_typeABoxMap_add_typeABoxMap_mul_of_lt N N' N'' _ h hh h' hh' h''
      hh'' hF hG hG')

end Composite

end TypeDAStructure

end TauCeti
