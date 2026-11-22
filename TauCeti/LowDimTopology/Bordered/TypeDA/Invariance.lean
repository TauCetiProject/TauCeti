/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.TypeDA.Composition
import TauCeti.Algebra.BigOperators.Finprod
import TauCeti.Data.Matrix.Mul

/-!
# Homotopy invariance of the box tensor product with a type `DA` bimodule in the type `D` structure

For a type `DA` bimodule `P = ^B P_A` and type `D` structures `N` and `N'` over `A`, a matrix `F`
from `N` to `N'` induces the morphism `P ⊠ F` from `P ⊠ N` to `P ⊠ N'`
(`TauCeti.TypeDAStructure.boxMorphism`), which commutes with the differential of morphisms
(`TauCeti.LowDimTopology.Bordered.TypeDA.Morphism`) and respects composites of homomorphisms up to
the homotopy `P ⊠ (F, G)` (`TauCeti.LowDimTopology.Bordered.TypeDA.Composition`). This file adds
the last ingredient, strict units, and deduces that the box tensor product `P ⊠_I N` over the
idempotents (`TauCeti.TypeDAStructure.boxTensorTypeD`) is invariant under homotopy equivalences of
`N`.

* **Strict units.** A type `DA` bimodule compatible with right idempotents `idemA`
  (`TauCeti.TypeDAStructure.IsRightIdemCompatible`) is **strictly unital**
  (`TauCeti.TypeDAStructure.IsStrictlyUnital`, in `TauCeti.LowDimTopology.Bordered.TypeDA.Basic`)
  when `δ¹₂(y, ι s) = ι (idem y) ⊗ y` if `s` is the right idempotent `idemA y` of `y`, and `0`
  otherwise, and the operations `δ¹_{n+1}` with `n ≥ 2` vanish as soon as one input is an
  idempotent `ι s`. This is the condition `δ¹₂(y, 1) = 1 ⊗ y`, `δ¹_{n+1}(y, …, 1, …) = 0` for
  `n ≥ 2` of Lipshitz, Ozsváth and Thurston, stated over the ring of idempotents. The identity
  bimodule `[I]` is strictly unital (`TauCeti.TypeDAStructure.isStrictlyUnital_identity`).
* **`P ⊠ id = id`.** For a strictly unital bimodule, the only path contributing to `P ⊠ id` is the
  single step through the identity morphism `id x x = ι (idem x)`, so `P ⊠ id` is the diagonal
  matrix of the idempotents `ι (idem y)` on the generators `(y, x)` with `idemA y = idem x`, and
  zero on the others (`TauCeti.TypeDAStructure.IsStrictlyUnital.boxMorphism_idMorphism_apply`). No
  boundedness is needed.
* **Restriction to `P ⊠_I N`.** For a morphism `F`, the morphism `P ⊠ F` never leads to a generator
  `(y', x')` with `idemA y' ≠ idem x'`: the last entry along each path ends at `x'`, and right
  linearity over the idempotents makes it act through `ι (idem x') * ι (idemA y') = 0`
  (`TauCeti.TypeDAStructure.boxMorphism_eq_zero_of_isRightIdemCompatible`). So `P ⊠ F` restricts to
  a morphism `P ⊠_I F` from `P ⊠_I N` to `P ⊠_I N'`
  (`TauCeti.TypeDAStructure.boxTensorMorphism`, `TauCeti.TypeDStructure.submatrix_mem_morphisms`),
  products of such morphisms only pass through generators with matching idempotents
  (`TauCeti.TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism`), restriction commutes with
  the differential of morphisms (`TauCeti.TypeDStructure.morphismDifferential_submatrix`), and so
  `∂(P ⊠_I F) = P ⊠_I ∂F`. For a strictly unital bimodule, `P ⊠_I id` is the identity morphism of
  `P ⊠_I N` (`TauCeti.TypeDAStructure.IsStrictlyUnital.boxTensorMorphism_idMorphism`).
* **Homotopy invariance.** Let `F` from `N` to `N'` and `G` from `N'` to `N` be homomorphisms with
  `∂H = F * G + id`. Adding the relations `∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)` and
  `∂(P ⊠ H) = P ⊠ (F * G) + P ⊠ id` cancels `P ⊠ (F * G)` in characteristic two, and restricting
  to the generators with matching idempotents gives

  `(P ⊠_I F) * (P ⊠_I G) + id = ∂ (P ⊠ (F, G)|_I + P ⊠_I H)`

  (`TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_coeff_eq_zero`,
  `TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_lt`), where the
  restriction `P ⊠ (F, G)|_I` is a morphism of `P ⊠_I N`
  (`TauCeti.TypeDAStructure.submatrix_boxCompHomotopy_mem_morphisms`), as `P ⊠_I H` is
  (`TauCeti.TypeDAStructure.boxTensorMorphism_mem_morphisms`).
  Applied also with the roles of `N` and `N'` exchanged, a homotopy equivalence from `N` to `N'`
  induces a homotopy equivalence from `P ⊠_I N` to `P ⊠_I N'`.

## Main definitions

* `TauCeti.TypeDAStructure.boxTensorMorphism`: the morphism `P ⊠_I F` from `P ⊠_I N` to
  `P ⊠_I N'`.

## Main results

* `TauCeti.TypeDAStructure.IsStrictlyUnital.boxMorphism_idMorphism_apply` and
  `TauCeti.TypeDAStructure.IsStrictlyUnital.boxTensorMorphism_idMorphism`: `P ⊠ id = id`.
* `TauCeti.TypeDAStructure.boxMorphism_eq_zero_of_isRightIdemCompatible`: `P ⊠ F` does not lead to
  generators with mismatched idempotents.
* `TauCeti.TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism`: `(P ⊠_I F) * (P ⊠_I G)` is the
  restriction of `(P ⊠ F) * (P ⊠ G)`.
* `TauCeti.TypeDAStructure.morphismDifferential_boxTensorMorphism_of_coeff_eq_zero` and
  `TauCeti.TypeDAStructure.morphismDifferential_boxTensorMorphism_of_lt`: `∂(P ⊠_I F) = P ⊠_I ∂F`.
* `TauCeti.TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_coeff_eq_zero`
  and `TauCeti.TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_lt`:
  homotopy invariance of `P ⊠_I N` in `N`.

## References

* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer.
  Math. Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687),
  Chapter 2 (strictly unital type `DA` bimodules over `𝔽₂`, and the invariance of box tensor
  products under homotopy equivalences).
* R. Lipshitz, P. S. Ozsváth and D. P. Thurston, *Bimodules in bordered Heegaard Floer homology*,
  Geom. Topol. **19** (2015), [arXiv:1003.0598](https://arxiv.org/abs/1003.0598), Section 2
  (strictly unital type `DA` bimodules and the functoriality of their box tensor products).
-/

public section

open Finset

namespace TauCeti

namespace TypeDAStructure

variable {R A B : Type*} [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
  {dA : A →ₗ[R] A} {dB : B →ₗ[R] B} {S : Type*} {ιB : S → B} {Y : Type*} [Fintype Y]
  {T : Type*} {ιA : T → A} {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X']
  [DecidableEq X'] (P : TypeDAStructure dA dB ιB Y)

/-! ### `P ⊠ id` for strictly unital bimodules -/

section StrictUnit

variable {P} [DecidableEq Y] [DecidableEq T] {idemA : Y → T}

/-- **`P ⊠ id = id` for a strictly unital bimodule.** The coefficient of `P ⊠ id` from `(y, x)` to
`(y', x')` is `ιB (idem y)` when the two generators agree and `idemA y = idem x`, and `0`
otherwise: every path through the identity morphism `id x x = ιA (idem x)` carries an idempotent
input, so only the single step `δ¹₂(y, ιA (idem x))` survives. -/
theorem IsStrictlyUnital.boxMorphism_idMorphism_apply (hPu : P.IsStrictlyUnital ιA idemA)
    (N : TypeDStructure dA ιA X) (p q : Y × X) :
    P.boxMorphism N N N.idMorphism p q =
      if p = q ∧ idemA p.1 = N.idem p.2 then ιB (P.idem p.1) else 0 := by
  -- Each entry of `fromBlocks 0 id 0 0` is `0` or an idempotent.
  have hentry (u v : X ⊕ X) : Matrix.fromBlocks 0 N.idMorphism 0 0 u v = 0 ∨
      ∃ s, Matrix.fromBlocks 0 N.idMorphism 0 0 u v = ιA s := by
    rcases u with u | u <;> rcases v with v | v <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, true_or, TypeDStructure.idMorphism_apply]
    split_ifs
    exacts [Or.inr ⟨_, rfl⟩, Or.inl rfl]
  rw [boxMorphism_apply, finsum_eq_single _ 1 fun n hn => ?_]
  · -- The single step from `x` to `x'`, through `id x x'`.
    set v : Fin 2 → X ⊕ X := ![Sum.inl p.2, Sum.inr q.2]
    have hv (r : Fin 2 → X ⊕ X) (hr : r ≠ v) :
        ¬(r 0 = Sum.inl p.2 ∧ r (Fin.last 1) = Sum.inr q.2) := fun h => hr <| funext fun t => by
      fin_cases t
      exacts [h.1, h.2]
    rw [Fin.sum_univ_one, Fintype.sum_eq_single v fun r hr => ite_eq_right (hv r hr),
      ite_eq_left ⟨rfl, rfl⟩]
    have hstep : (fun t : Fin 1 => Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N.coeff)
        0 (Matrix.fromBlocks 0 N.idMorphism 0 0) t (v t.castSucc) (v t.succ)) =
        fun _ => N.idMorphism p.2 q.2 := by
      funext t
      rw [Fin.fin_one_eq_zero t, Function.update_self]
      simp [v]
    rw [hstep, TypeDStructure.idMorphism_apply]
    by_cases hx : p.2 = q.2
    · rw [ite_eq_left hx, hPu.coeff_one_apply]
      simp only [Prod.ext_iff, hx, and_true]
    · rw [ite_eq_right hx, MultilinearMap.map_coord_zero _ 0 rfl, Matrix.zero_apply,
        ite_eq_right fun h => hx (congrArg Prod.snd h.1)]
  · -- Paths of length `0` have no step, and longer ones an idempotent input to `δ¹_{n+1}`.
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 0 := by omega
      simp
    · refine sum_eq_zero fun l _ => sum_eq_zero fun r _ => ?_
      split_ifs
      · rcases hentry (r l.castSucc) (r l.succ) with h0 | ⟨s, hs⟩
        · rw [MultilinearMap.map_coord_zero _ l (by simp only [Function.update_self]; exact h0),
            Matrix.zero_apply]
        · rw [hPu.coeff_eq_zero hn2 _ l s (by simp only [Function.update_self]; exact hs),
            Matrix.zero_apply]
      · rfl

end StrictUnit

/-! ### The box tensor product of morphisms over the idempotents -/

section BoxTensor

variable {X'' : Type*} [Fintype X''] [DecidableEq X''] {P} {idemA : Y → T}

/-- **`P ⊠ F` does not lead to generators with mismatched idempotents.** If `P` is compatible with
right idempotents `idemA`, the idempotents of `A` are orthogonal and `F` is a morphism from `N` to
`N'`, the coefficient of `P ⊠ F` to a generator `(y', x')` with `idemA y' ≠ idem x'` vanishes: the
last entry along each path is a coefficient of `F` or of `N'` into `x'`, which `ιA (idemA y')`
annihilates on the right. -/
theorem boxMorphism_eq_zero_of_isRightIdemCompatible (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (N : TypeDStructure dA ιA X)
    {N' : TypeDStructure dA ιA X'} {F : Matrix X X' A} (hF : F ∈ TypeDStructure.morphisms N N')
    (p : Y × X) {q : Y × X'} (hq : idemA q.1 ≠ N'.idem q.2) : P.boxMorphism N N' F p q = 0 := by
  rw [boxMorphism_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun n => sum_eq_zero fun l _ => sum_eq_zero fun r _ => ?_
  split_ifs with hr
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := l.pos; omega⟩
    -- Each entry into `x'` absorbs `ιA (idem x')` on the right.
    have hlast (t : Fin (m + 1)) (u : X ⊕ X') :
        Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t u (Sum.inr q.2) * ιA (N'.idem q.2) =
          Function.update (fun _ => Matrix.fromBlocks N.coeff 0 0 N'.coeff) l
            (Matrix.fromBlocks 0 F 0 0) t u (Sum.inr q.2) := by
      rcases eq_or_ne t l with rfl | htl
      · rw [Function.update_self]
        rcases u with u | u
        · simp [(TypeDStructure.mem_morphisms_iff.mp hF u q.2).2]
        · simp
      · rw [Function.update_of_ne htl]
        rcases u with u | u <;> simp [N'.coeff_mul_idem]
    rw [← hP.coeff_update_last_mul, MultilinearMap.map_coord_zero _ (Fin.last m),
      Matrix.zero_apply]
    simp only [Function.update_self, Fin.succ_last, hr.2]
    rw [← hlast, mul_assoc, hιA _ _ (Ne.symm hq), mul_zero]
  · rfl

/-- **`P ⊠ (F, G)` does not lead to generators with mismatched idempotents**, for a morphism `F`
and a homomorphism `G`: it is a component of the morphism `P ⊠ fromCols F 0` into the box tensor
product with the mapping cone of `G`
(`TauCeti.TypeDAStructure.boxCompHomotopy_eq_boxMorphism`). -/
theorem boxCompHomotopy_eq_zero_of_isRightIdemCompatible (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (N : TypeDStructure dA ιA X)
    {N' : TypeDStructure dA ιA X'} {N'' : TypeDStructure dA ιA X''} {F : Matrix X X' A}
    (hF : F ∈ TypeDStructure.morphisms N N') {G : Matrix X' X'' A}
    (hG : G ∈ TypeDStructure.morphisms N' N'')
    (hG' : TypeDStructure.morphismDifferential N' N'' G = 0) (p : Y × X) {q : Y × X''}
    (hq : idemA q.1 ≠ N''.idem q.2) : P.boxCompHomotopy N N' N'' F G p q = 0 := by
  rw [P.boxCompHomotopy_eq_boxMorphism N F hG hG']
  refine boxMorphism_eq_zero_of_isRightIdemCompatible hP hιA N
    (TypeDStructure.mem_morphisms_iff.mpr fun x z => ?_) p (by simpa using hq)
  rcases z with z | z
  · simp [TypeDStructure.mem_morphisms_iff.mp hF x z]
  · simp

variable (N : TypeDStructure dA ιA X) (N' : TypeDStructure dA ιA X') (idemA) in
/-- The **morphism `P ⊠_I F`** from `P ⊠_I N` to `P ⊠_I N'` induced by a matrix `F` from `N` to
`N'`: the morphism `P ⊠ F` (`TauCeti.TypeDAStructure.boxMorphism`) restricted to the generators
`(y, x)` with matching idempotents `idemA y = idem x`. -/
noncomputable def boxTensorMorphism (F : Matrix X X' A) :
    Matrix {p : Y × X // idemA p.1 = N.idem p.2} {q : Y × X' // idemA q.1 = N'.idem q.2} B :=
  (P.boxMorphism N N' F).submatrix Subtype.val Subtype.val

variable {N : TypeDStructure dA ιA X} {N' : TypeDStructure dA ιA X'}
  {N'' : TypeDStructure dA ιA X''}

@[simp]
theorem boxTensorMorphism_apply (F : Matrix X X' A) (p : {p : Y × X // idemA p.1 = N.idem p.2})
    (q : {q : Y × X' // idemA q.1 = N'.idem q.2}) :
    P.boxTensorMorphism idemA N N' F p q = P.boxMorphism N N' F p q :=
  (rfl)

variable [DecidableEq T]

/-- **Products of the morphisms `P ⊠_I F`.** If `P` is compatible with right idempotents `idemA`,
the idempotents of `A` are orthogonal and `F` is a morphism from `N` to `N'`, then
`(P ⊠_I F) * (P ⊠_I G)` is the restriction of `(P ⊠ F) * (P ⊠ G)` to the generators with matching
idempotents: the product only passes through such generators, since `P ⊠ F` does not lead to the
others (`TauCeti.TypeDAStructure.boxMorphism_eq_zero_of_isRightIdemCompatible`). -/
theorem boxTensorMorphism_mul_boxTensorMorphism (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) {F : Matrix X X' A}
    (hF : F ∈ TypeDStructure.morphisms N N') (G : Matrix X' X'' A) :
    P.boxTensorMorphism idemA N N' F * P.boxTensorMorphism idemA N' N'' G =
      (P.boxMorphism N N' F * P.boxMorphism N' N'' G).submatrix Subtype.val Subtype.val :=
  (Matrix.submatrix_val_mul_of_forall (r := fun p : Y × X => idemA p.1 = N.idem p.2)
    (s := fun q : Y × X' => idemA q.1 = N'.idem q.2) (P.boxMorphism N N' F)
    (P.boxMorphism N' N'' G)
    (Subtype.val : {q : Y × X'' // idemA q.1 = N''.idem q.2} → Y × X'')
    fun p _ _ hq => boxMorphism_eq_zero_of_isRightIdemCompatible hP hιA N hF p hq).symm

variable [CharP R 2]

/-- **`P ⊠_I F` is a morphism** from `P ⊠_I N` to `P ⊠_I N'`. -/
theorem boxTensorMorphism_mem_morphisms (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A) :
    P.boxTensorMorphism idemA N N' F ∈
      TypeDStructure.morphisms (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N' hP hιA hdB hN') := by
  rw [boxTensorTypeD_eq_restrict, boxTensorTypeD_eq_restrict, boxTensorMorphism]
  exact TypeDStructure.submatrix_mem_morphisms (P.boxMorphism_mem_morphisms N N' hdB hN hN' F)

/-- **The restriction of `P ⊠ (F, G)` is a morphism** from `P ⊠_I N` to `P ⊠_I N''`. -/
theorem submatrix_boxCompHomotopy_mem_morphisms (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN'' : N''.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (F : Matrix X X' A)
    (G : Matrix X' X'' A) :
    (P.boxCompHomotopy N N' N'' F G).submatrix Subtype.val Subtype.val ∈
      TypeDStructure.morphisms (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N'' hP hιA hdB hN'') := by
  rw [boxTensorTypeD_eq_restrict, boxTensorTypeD_eq_restrict]
  exact TypeDStructure.submatrix_mem_morphisms
    (P.boxCompHomotopy_mem_morphisms N N' N'' hdB hN hN'' F G)

/-- **`P ⊠_I id = id` for a strictly unital bimodule**: the morphism induced by the identity
morphism of `N` is the identity morphism of `P ⊠_I N`. -/
theorem IsStrictlyUnital.boxTensorMorphism_idMorphism [DecidableEq Y]
    (hPu : P.IsStrictlyUnital ιA idemA) (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) :
    P.boxTensorMorphism idemA N N N.idMorphism =
      (P.boxTensorTypeD N hP hιA hdB hN).idMorphism := by
  ext p q
  rw [boxTensorMorphism_apply, hPu.boxMorphism_idMorphism_apply, TypeDStructure.idMorphism_apply,
    boxTensorTypeD_idem]
  by_cases hpq : p = q
  · rw [ite_eq_left ⟨congrArg Subtype.val hpq, p.property⟩, ite_eq_left hpq]
  · rw [ite_eq_right fun h => hpq (Subtype.ext h.1), ite_eq_right hpq]

/-- The core of `TauCeti.TypeDAStructure.morphismDifferential_boxTensorMorphism_of_coeff_eq_zero`
and `TauCeti.TypeDAStructure.morphismDifferential_boxTensorMorphism_of_lt`: restricting
`∂(P ⊠ F) = P ⊠ ∂F` to the generators with matching idempotents. -/
private theorem morphismDifferential_boxTensorMorphism_of_eq
    (hP : P.IsRightIdemCompatible ιA idemA) (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0)
    (hdB : IsUngradedDGAlgebra dB) (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A}
    (hF : F ∈ TypeDStructure.morphisms N N')
    (h : TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N' hdB hN')
        (P.boxMorphism N N' F) =
      P.boxMorphism N N' (TypeDStructure.morphismDifferential N N' F)) :
    TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N' hP hιA hdB hN') (P.boxTensorMorphism idemA N N' F) =
      P.boxTensorMorphism idemA N N' (TypeDStructure.morphismDifferential N N' F) := by
  rw [boxTensorTypeD_eq_restrict, boxTensorTypeD_eq_restrict, boxTensorMorphism, boxTensorMorphism,
    TypeDStructure.morphismDifferential_submatrix _ (F := P.boxMorphism N N' F)
      (hF := fun p q _ hq => boxMorphism_eq_zero_of_isRightIdemCompatible hP hιA N hF p hq), h]

/-- **`P ⊠_I –` commutes with the differential of morphisms, for a bounded bimodule.** Over a ring
of characteristic two, if the operations `δ¹_{k+1}` of `P` vanish for `k ≥ K`, then for every
morphism `F` from `N` to `N'` the differential of `P ⊠_I F` is `P ⊠_I ∂F`. -/
theorem morphismDifferential_boxTensorMorphism_of_coeff_eq_zero
    (hP : P.IsRightIdemCompatible ιA idemA) (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0)
    (hdB : IsUngradedDGAlgebra dB) (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hPK : ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A}
    (hF : F ∈ TypeDStructure.morphisms N N') :
    TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N' hP hιA hdB hN') (P.boxTensorMorphism idemA N N' F) =
      P.boxTensorMorphism idemA N N' (TypeDStructure.morphismDifferential N N' F) :=
  morphismDifferential_boxTensorMorphism_of_eq hP hιA hdB hN hN' hF
    (P.morphismDifferential_boxMorphism_of_coeff_eq_zero N N' hdB hN hN' hPK F)

/-- **`P ⊠_I –` commutes with the differential of morphisms, for bounded type `D` structures.**
Over a ring of characteristic two, if heights on the generators of `N` and of `N'` strictly increase
along their nonzero coefficients, then for every morphism `F` from `N` to `N'` the differential of
`P ⊠_I F` is `P ⊠_I ∂F`. -/
theorem morphismDifferential_boxTensorMorphism_of_lt (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0)
    (hN' : N'.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F : Matrix X X' A}
    (hF : F ∈ TypeDStructure.morphisms N N') :
    TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N' hP hιA hdB hN') (P.boxTensorMorphism idemA N N' F) =
      P.boxTensorMorphism idemA N N' (TypeDStructure.morphismDifferential N N' F) :=
  morphismDifferential_boxTensorMorphism_of_eq hP hιA hdB hN hN' hF
    (P.morphismDifferential_boxMorphism_of_lt N N' hdB hN hN' h hh h' hh' F)

/-! ### Homotopy invariance -/

/-- The core of the homotopy invariance theorems: the relations
`∂(P ⊠ (F, G)) = (P ⊠ F) * (P ⊠ G) + P ⊠ (F * G)` and `∂(P ⊠ H) = P ⊠ (F * G) + P ⊠ id` add up, in
characteristic two, to `(P ⊠ F) * (P ⊠ G) + P ⊠ id = ∂(P ⊠ (F, G) + P ⊠ H)`, which restricts to the
generators with matching idempotents. -/
private theorem boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_eq [DecidableEq Y]
    (hPu : P.IsStrictlyUnital ιA idemA) (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A}
    {G : Matrix X' X A} {H : Matrix X X A} (hF : F ∈ TypeDStructure.morphisms N N')
    (hG : G ∈ TypeDStructure.morphisms N' N)
    (hG' : TypeDStructure.morphismDifferential N' N G = 0)
    (hH : H ∈ TypeDStructure.morphisms N N)
    (h₁ : TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N hdB hN)
        (P.boxCompHomotopy N N' N F G) =
      P.boxMorphism N N' F * P.boxMorphism N' N G + P.boxMorphism N N (F * G))
    (h₂ : TypeDStructure.morphismDifferential (P.boxTypeD N hdB hN) (P.boxTypeD N hdB hN)
        (P.boxMorphism N N H) = P.boxMorphism N N (F * G) + P.boxMorphism N N N.idMorphism) :
    P.boxTensorMorphism idemA N N' F * P.boxTensorMorphism idemA N' N G +
        (P.boxTensorTypeD N hP hιA hdB hN).idMorphism =
      TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N hP hιA hdB hN)
        ((P.boxCompHomotopy N N' N F G).submatrix Subtype.val Subtype.val +
          P.boxTensorMorphism idemA N N H) := by
  -- The homotopy does not lead to generators with mismatched idempotents.
  have hvan (p : Y × X) (q : Y × X) (hq : ¬idemA q.1 = N.idem q.2) :
      (P.boxCompHomotopy N N' N F G + P.boxMorphism N N H) p q = 0 := by
    rw [Matrix.add_apply, boxCompHomotopy_eq_zero_of_isRightIdemCompatible hP hιA N hF hG hG' p hq,
      boxMorphism_eq_zero_of_isRightIdemCompatible hP hιA N hH p hq, add_zero]
  have hsub : (P.boxCompHomotopy N N' N F G).submatrix Subtype.val Subtype.val +
      P.boxTensorMorphism idemA N N H =
        (P.boxCompHomotopy N N' N F G + P.boxMorphism N N H).submatrix Subtype.val Subtype.val := by
    ext p q
    simp only [Matrix.add_apply, Matrix.submatrix_apply, boxTensorMorphism_apply]
  rw [hsub, ← hPu.boxTensorMorphism_idMorphism hP hιA hdB hN,
    boxTensorMorphism_mul_boxTensorMorphism hP hιA hF, boxTensorTypeD_eq_restrict,
    TypeDStructure.morphismDifferential_submatrix _
      (F := P.boxCompHomotopy N N' N F G + P.boxMorphism N N H) (hF := fun p q _ hq => hvan p q hq),
    map_add, h₁, h₂,
    add_assoc (P.boxMorphism N N' F * P.boxMorphism N' N G),
    ← add_assoc (P.boxMorphism N N (F * G)),
    add_self_eq_zero_of_charTwo R, zero_add]
  ext p q
  simp only [Matrix.add_apply, Matrix.submatrix_apply, boxTensorMorphism_apply]

/-- **Homotopy invariance of the box tensor product with a bounded type `DA` bimodule, in the type
`D` structure.** Over a ring of characteristic two, let `P` be strictly unital and compatible with
right idempotents `idemA`, the idempotents of `A` orthogonal, and the operations `δ¹_{k+1}` of `P`
vanish for `k ≥ K`. Let `F` from `N` to `N'` and `G` from `N'` to `N` be homomorphisms, and `H` a
morphism with `∂H = F * G + id`. Then on the box tensor products over the idempotents

`(P ⊠_I F) * (P ⊠_I G) + id = ∂ (P ⊠ (F, G)|_I + P ⊠_I H)`,

so `(P ⊠_I F) * (P ⊠_I G)` is homotopic to the identity of `P ⊠_I N`, the homotopy being a morphism
(`TauCeti.TypeDAStructure.submatrix_boxCompHomotopy_mem_morphisms`,
`TauCeti.TypeDAStructure.boxTensorMorphism_mem_morphisms`). Together with the same
statement for `G * F`, a homotopy equivalence from `N` to `N'` induces one from `P ⊠_I N` to
`P ⊠_I N'`. -/
theorem boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_coeff_eq_zero [DecidableEq Y]
    (hPu : P.IsStrictlyUnital ιA idemA) (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) {K : ℕ}
    (hPK : ∀ k, K ≤ k → P.coeff k = 0) {F : Matrix X X' A} {G : Matrix X' X A}
    {H : Matrix X X A} (hF : F ∈ TypeDStructure.morphisms N N')
    (hF' : TypeDStructure.morphismDifferential N N' F = 0)
    (hG : G ∈ TypeDStructure.morphisms N' N)
    (hG' : TypeDStructure.morphismDifferential N' N G = 0)
    (hH : H ∈ TypeDStructure.morphisms N N)
    (hH' : TypeDStructure.morphismDifferential N N H = F * G + N.idMorphism) :
    P.boxTensorMorphism idemA N N' F * P.boxTensorMorphism idemA N' N G +
        (P.boxTensorTypeD N hP hιA hdB hN).idMorphism =
      TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N hP hιA hdB hN)
        ((P.boxCompHomotopy N N' N F G).submatrix Subtype.val Subtype.val +
          P.boxTensorMorphism idemA N N H) :=
  boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_eq hPu hP hιA hdB hN hF hG hG' hH
    (P.morphismDifferential_boxCompHomotopy_of_coeff_eq_zero N N' N hdB hN hN hPK hF' hG hG')
    (P.morphismDifferential_boxMorphism_eq_add_of_coeff_eq_zero N N hdB hN hN hPK hH')

/-- **Homotopy invariance of the box tensor product of bounded type `D` structures with a type `DA`
bimodule, in the type `D` structure.** Over a ring of characteristic two, let `P` be strictly
unital and compatible with right idempotents `idemA`, the idempotents of `A` orthogonal, and heights
on the generators of `N` and of `N'` strictly increase along their nonzero coefficients. Let `F`
from `N` to `N'` and `G` from `N'` to `N` be homomorphisms, and `H` a morphism with
`∂H = F * G + id`. Then on the box tensor products over the idempotents

`(P ⊠_I F) * (P ⊠_I G) + id = ∂ (P ⊠ (F, G)|_I + P ⊠_I H)`,

whatever the operations of `P`; see
`TypeDAStructure.boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_coeff_eq_zero`. -/
theorem boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_lt [DecidableEq Y]
    (hPu : P.IsStrictlyUnital ιA idemA) (hP : P.IsRightIdemCompatible ιA idemA)
    (hιA : ∀ s t, s ≠ t → ιA s * ιA t = 0) (hdB : IsUngradedDGAlgebra dB)
    (hN : N.IsBounded ∨ ∃ K, ∀ k, K ≤ k → P.coeff k = 0) (h : X → ℕ)
    (hh : ∀ x y, N.coeff x y ≠ 0 → h x < h y) (h' : X' → ℕ)
    (hh' : ∀ x y, N'.coeff x y ≠ 0 → h' x < h' y) {F : Matrix X X' A} {G : Matrix X' X A}
    {H : Matrix X X A} (hF : F ∈ TypeDStructure.morphisms N N')
    (hF' : TypeDStructure.morphismDifferential N N' F = 0)
    (hG : G ∈ TypeDStructure.morphisms N' N)
    (hG' : TypeDStructure.morphismDifferential N' N G = 0)
    (hH : H ∈ TypeDStructure.morphisms N N)
    (hH' : TypeDStructure.morphismDifferential N N H = F * G + N.idMorphism) :
    P.boxTensorMorphism idemA N N' F * P.boxTensorMorphism idemA N' N G +
        (P.boxTensorTypeD N hP hιA hdB hN).idMorphism =
      TypeDStructure.morphismDifferential (P.boxTensorTypeD N hP hιA hdB hN)
        (P.boxTensorTypeD N hP hιA hdB hN)
        ((P.boxCompHomotopy N N' N F G).submatrix Subtype.val Subtype.val +
          P.boxTensorMorphism idemA N N H) :=
  boxTensorMorphism_mul_boxTensorMorphism_add_idMorphism_of_eq hPu hP hιA hdB hN hF hG hG' hH
    (P.morphismDifferential_boxCompHomotopy_of_lt N N' N hdB hN hN h hh h' hh' h hh hF' hG hG')
    (P.morphismDifferential_boxMorphism_eq_add_of_lt N N hdB hN hN h hh h hh hH')

end BoxTensor

end TypeDAStructure

end TauCeti
