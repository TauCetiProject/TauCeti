/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Associativity and symmetry of product orientations on `WithLp`

For finite-dimensional modules over an ordered commutative ring `R` (or `ℝ`), the canonical product
orientation `Orientation.prod` transported along `(WithLp.linearEquiv p R (· × ·)).symm` inherits
the associativity and Koszul-signed symmetry laws of `Orientation.map_prodAssoc_prod` and
`Orientation.map_prodComm_prod`:

* `Orientation.map_withLpProdAssoc_prod`: `LinearEquiv.withLpProdAssoc p R U V W` carries
  `(o₁ × o₂) × o₃` to `o₁ × (o₂ × o₃)` reindexed along `n₁ + n₂ + n₃ = n₁ + (n₂ + n₃)`.
* `Orientation.map_withLpProdComm_prod`: `(LinearEquiv.prodComm R V W).withLpCongr p` multiplies
  `o₁ × o₂` by `(-1 : Rˣ) ^ (n * m)` after swapping the factors and reindexing along
  `m + n = n + m`.
* `Orientation.map_withLpProdComm_prod_of_even`: when `Even (n * m)`, the swap preserves the
  product orientation.
-/

public section

noncomputable section

open Module
open scoped ENNReal

namespace Orientation

section Assoc

variable {p : ℝ≥0∞} {R U V W : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup U] [Module R U] [Module.Free R U] [Module.Finite R U]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
  {n₁ n₂ n₃ : ℕ}
  [Fact (finrank R U = n₁)] [Fact (finrank R V = n₂)] [Fact (finrank R W = n₃)]
  [Fact (finrank R (WithLp p (U × V)) = n₁ + n₂)]
  [Fact (finrank R (WithLp p (V × W)) = n₂ + n₃)]
  (o₁ : Orientation R U (Fin n₁)) (o₂ : Orientation R V (Fin n₂)) (o₃ : Orientation R W (Fin n₃))

/-- **Associativity of `WithLp` product orientations**: `LinearEquiv.withLpProdAssoc p R U V W`
transports the left-iterated product orientation `(o₁ × o₂) × o₃` to the right-iterated product
orientation `o₁ × (o₂ × o₃)`, reindexed along `n₁ + n₂ + n₃ = n₁ + (n₂ + n₃)`. -/
theorem map_withLpProdAssoc_prod
    {o₁₂ : Orientation R (WithLp p (U × V)) (Fin (n₁ + n₂))}
    (ho₁₂ : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
      (WithLp.linearEquiv p R (U × V)).symm = o₁₂)
    {o₂₃ : Orientation R (WithLp p (V × W)) (Fin (n₂ + n₃))}
    (ho₂₃ : (Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n₂ + n₃))
      (WithLp.linearEquiv p R (V × W)).symm = o₂₃)
    {o_L : Orientation R (WithLp p (WithLp p (U × V) × W)) (Fin (n₁ + n₂ + n₃))}
    (ho_L : (Orientation.prod o₁₂ o₃ Fact.out Fact.out).map (Fin (n₁ + n₂ + n₃))
      (WithLp.linearEquiv p R (WithLp p (U × V) × W)).symm = o_L)
    {o_R : Orientation R (WithLp p (U × WithLp p (V × W))) (Fin (n₁ + (n₂ + n₃)))}
    (ho_R : (Orientation.prod o₁ o₂₃ Fact.out Fact.out).map (Fin (n₁ + (n₂ + n₃)))
      (WithLp.linearEquiv p R (U × WithLp p (V × W))).symm = o_R) :
    Orientation.map (Fin (n₁ + n₂ + n₃)) (LinearEquiv.withLpProdAssoc p R U V W) o_L =
      Orientation.reindex R (WithLp p (U × WithLp p (V × W)))
        (finCongr (add_assoc n₁ n₂ n₃).symm) o_R := by
  subst ho₁₂ ho₂₃ ho_L ho_R
  have hUV : finrank R (U × V) = n₁ + n₂ := by
    rw [Module.finrank_prod, Fact.out (p := finrank R U = n₁), Fact.out (p := finrank R V = n₂)]
  have hVW : finrank R (V × W) = n₂ + n₃ := by
    rw [Module.finrank_prod, Fact.out (p := finrank R V = n₂), Fact.out (p := finrank R W = n₃)]
  have hL : Orientation.prod
      ((Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n₁ + n₂))
        (WithLp.linearEquiv p R (U × V)).symm) o₃ Fact.out Fact.out =
      Orientation.map (Fin (n₁ + n₂ + n₃))
        (((WithLp.linearEquiv p R (U × V)).symm).prodCongr (LinearEquiv.refl R W))
        (Orientation.prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out) := by
    simpa using (Orientation.map_prod (Orientation.prod o₁ o₂ Fact.out Fact.out) o₃ hUV Fact.out
      (WithLp.linearEquiv p R (U × V)).symm (LinearEquiv.refl R W)).symm
  have hR : Orientation.prod o₁
      ((Orientation.prod o₂ o₃ Fact.out Fact.out).map (Fin (n₂ + n₃))
        (WithLp.linearEquiv p R (V × W)).symm) Fact.out Fact.out =
      Orientation.map (Fin (n₁ + (n₂ + n₃)))
        ((LinearEquiv.refl R U).prodCongr (WithLp.linearEquiv p R (V × W)).symm)
        (Orientation.prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW) := by
    simpa using (Orientation.map_prod o₁ (Orientation.prod o₂ o₃ Fact.out Fact.out) Fact.out hVW
      (LinearEquiv.refl R U) (WithLp.linearEquiv p R (V × W)).symm).symm
  rw [hL, hR, ← Orientation.map_trans, ← Orientation.map_trans, ← Orientation.map_trans,
    ← Orientation.map_reindex, ← Orientation.map_prodAssoc_prod o₁ o₂ o₃ Fact.out Fact.out Fact.out,
    ← Orientation.map_trans]
  have heq :
      (((WithLp.linearEquiv p R (U × V)).symm.prodCongr (LinearEquiv.refl R W)).trans
        ((WithLp.linearEquiv p R (WithLp p (U × V) × W)).symm.trans
          (LinearEquiv.withLpProdAssoc p R U V W))) =
      (LinearEquiv.prodAssoc R U V W).trans
        (((LinearEquiv.refl R U).prodCongr (WithLp.linearEquiv p R (V × W)).symm).trans
          (WithLp.linearEquiv p R (U × WithLp p (V × W))).symm) := by
    ext x
    simp
  rw [heq]

end Assoc

section Comm

variable {p : ℝ≥0∞} {R V W : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
  {n m : ℕ} [Fact (finrank R V = n)] [Fact (finrank R W = m)]
  (o₁ : Orientation R V (Fin n)) (o₂ : Orientation R W (Fin m))

/-- **Signed symmetry of `WithLp` product orientations**: swapping the factors of `WithLp p (V × W)`
multiplies the canonical product orientation by `(-1 : Rˣ) ^ (n * m)`, reindexed along
`m + n = n + m`. -/
theorem map_withLpProdComm_prod
    {o_VW : Orientation R (WithLp p (V × W)) (Fin (n + m))}
    (ho_VW : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv p R (V × W)).symm = o_VW)
    {o_WV : Orientation R (WithLp p (W × V)) (Fin (m + n))}
    (ho_WV : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv p R (W × V)).symm = o_WV) :
    Orientation.map (Fin (n + m)) ((LinearEquiv.prodComm R V W).withLpCongr p) o_VW =
      (-1 : Rˣ) ^ (n * m) •
        Orientation.reindex R (WithLp p (W × V)) (finCongr (add_comm m n)) o_WV := by
  subst ho_VW ho_WV
  rw [← Orientation.map_trans, ← Orientation.map_reindex, ← Orientation.map_units_smul,
    ← Orientation.map_prodComm_prod o₁ o₂ Fact.out Fact.out, ← Orientation.map_trans]
  have heq : (WithLp.linearEquiv p R (V × W)).symm.trans
      ((LinearEquiv.prodComm R V W).withLpCongr p) =
    (LinearEquiv.prodComm R V W).trans (WithLp.linearEquiv p R (W × V)).symm := by
    ext x
    simp
  rw [heq]

/-- **Even-product orientation preservation on `WithLp`**: when `n * m` is even, swapping the
factors of `WithLp p (V × W)` preserves the canonical product orientation up to
`finCongr (add_comm m n)`. -/
theorem map_withLpProdComm_prod_of_even (hnm : Even (n * m))
    {o_VW : Orientation R (WithLp p (V × W)) (Fin (n + m))}
    (ho_VW : (Orientation.prod o₁ o₂ Fact.out Fact.out).map (Fin (n + m))
      (WithLp.linearEquiv p R (V × W)).symm = o_VW)
    {o_WV : Orientation R (WithLp p (W × V)) (Fin (m + n))}
    (ho_WV : (Orientation.prod o₂ o₁ Fact.out Fact.out).map (Fin (m + n))
      (WithLp.linearEquiv p R (W × V)).symm = o_WV) :
    Orientation.map (Fin (n + m)) ((LinearEquiv.prodComm R V W).withLpCongr p) o_VW =
      Orientation.reindex R (WithLp p (W × V)) (finCongr (add_comm m n)) o_WV := by
  rw [map_withLpProdComm_prod o₁ o₂ ho_VW ho_WV, hnm.neg_one_pow, one_smul]

end Comm

end Orientation
