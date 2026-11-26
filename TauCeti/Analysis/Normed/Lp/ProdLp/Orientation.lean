/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import TauCeti.Analysis.Normed.Lp.WithLp
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Product orientations on `WithLp` products

This file transports ordered product orientations (`Orientation.prod`) along the structural
`Lᵖ`-product isometries `LinearIsometryEquiv.withLpProdComm` and
`LinearIsometryEquiv.withLpProdAssoc`:

* `Orientation.map_withLpProdComm` and `Orientation.map_withLpProdComm_of_even`: swapping the
  factors of `WithLp p (V × W)` multiplies the ordered product orientation by `(-1) ^ (n * m)`
  (hence preserves it when `n * m` is even), reindexed along `add_comm m n`.
* `Orientation.map_withLpProdAssoc`: reassociating `((U × V) × W) ≃ (U × (V × W))` on `WithLp`
  products carries the left-associated ordered product orientation to the right-associated one,
  reindexed along `(add_assoc n m k).symm`.
-/

public section

noncomputable section

open Module
open scoped ENNReal

namespace Orientation

section Comm

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R V W : Type*} [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R] [SeminormedAddCommGroup V] [Module R V] [Module.Free R V]
  [Module.Finite R V] [SeminormedAddCommGroup W] [Module R W] [Module.Free R W]
  [Module.Finite R W] {n m : ℕ}
  (o₁ : Orientation R V (Fin n)) (o₂ : Orientation R W (Fin m))
  (o : Orientation R (WithLp p (V × W)) (Fin (n + m)))
  (o' : Orientation R (WithLp p (W × V)) (Fin (m + n)))

/-- Exchanging the factors of `WithLp p (V × W)` via `LinearIsometryEquiv.withLpProdComm`
multiplies the ordered product orientation by `(-1) ^ (n * m)`, reindexed along `add_comm m n`. -/
theorem map_withLpProdComm (hn : finrank R V = n) (hm : finrank R W = m)
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv p R (V × W)) = o₁.prod o₂ hn hm)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv p R (W × V)) = o₂.prod o₁ hm hn) :
    o.map (Fin (n + m)) (LinearIsometryEquiv.withLpProdComm p R V W).toLinearEquiv =
      (-1 : Rˣ) ^ (n * m) • Orientation.reindex R _ (finCongr (add_comm m n)) o' := by
  have hcomm : (LinearIsometryEquiv.withLpProdComm p R V W).toLinearEquiv.trans
      (WithLp.linearEquiv p R (W × V)) =
      (WithLp.linearEquiv p R (V × W)).trans (LinearEquiv.prodComm R V W) := by ext x <;> simp
  refine (Orientation.map (Fin (n + m)) (WithLp.linearEquiv p R (W × V))).injective ?_
  rw [← Orientation.map_trans, hcomm, Orientation.map_trans, ho,
    Orientation.map_prodComm_prod o₁ o₂ hn hm, Orientation.map_units_smul,
    Orientation.map_reindex, ho']

/-- When `n * m` is even, `LinearIsometryEquiv.withLpProdComm` carries the ordered product
orientation of `WithLp p (V × W)` to that of `WithLp p (W × V)`, reindexed along `add_comm m n`. -/
theorem map_withLpProdComm_of_even (hn : finrank R V = n) (hm : finrank R W = m)
    (heven : Even (n * m))
    (ho : o.map (Fin (n + m)) (WithLp.linearEquiv p R (V × W)) = o₁.prod o₂ hn hm)
    (ho' : o'.map (Fin (m + n)) (WithLp.linearEquiv p R (W × V)) = o₂.prod o₁ hm hn) :
    o.map (Fin (n + m)) (LinearIsometryEquiv.withLpProdComm p R V W).toLinearEquiv =
      Orientation.reindex R _ (finCongr (add_comm m n)) o' := by
  rw [map_withLpProdComm o₁ o₂ o o' hn hm ho ho', heven.neg_one_pow, one_smul]

end Comm

section Assoc

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {R U V W : Type*} [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R]
  [SeminormedAddCommGroup U] [Module R U] [Module.Free R U] [Module.Finite R U]
  [SeminormedAddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [SeminormedAddCommGroup W] [Module R W] [Module.Free R W] [Module.Finite R W]
  {n m k : ℕ}
  (o₁ : Orientation R U (Fin n)) (o₂ : Orientation R V (Fin m)) (o₃ : Orientation R W (Fin k))
  (o₁₂ : Orientation R (WithLp p (U × V)) (Fin (n + m)))
  (o₂₃ : Orientation R (WithLp p (V × W)) (Fin (m + k)))
  (o₁₂_₃ : Orientation R (WithLp p (WithLp p (U × V) × W)) (Fin (n + m + k)))
  (o₁_₂₃ : Orientation R (WithLp p (U × WithLp p (V × W))) (Fin (n + (m + k))))

/-- `LinearIsometryEquiv.withLpProdAssoc` carries the left-associated ordered product orientation
to the right-associated one, reindexed along `(add_assoc n m k).symm`. -/
theorem map_withLpProdAssoc (hn : finrank R U = n) (hm : finrank R V = m) (hk : finrank R W = k)
    (ho₁₂ : o₁₂.map (Fin (n + m)) (WithLp.linearEquiv p R (U × V)) = o₁.prod o₂ hn hm)
    (ho₂₃ : o₂₃.map (Fin (m + k)) (WithLp.linearEquiv p R (V × W)) = o₂.prod o₃ hm hk)
    (ho₁₂_₃ : o₁₂_₃.map (Fin (n + m + k))
      (WithLp.linearEquiv p R (WithLp p (U × V) × W)) =
      o₁₂.prod o₃
        (by rw [(WithLp.linearEquiv p R (U × V)).finrank_eq, Module.finrank_prod, hn, hm]) hk)
    (ho₁_₂₃ : o₁_₂₃.map (Fin (n + (m + k)))
      (WithLp.linearEquiv p R (U × WithLp p (V × W))) =
      o₁.prod o₂₃ hn
        (by rw [(WithLp.linearEquiv p R (V × W)).finrank_eq, Module.finrank_prod, hm, hk])) :
    o₁₂_₃.map (Fin (n + m + k)) (LinearIsometryEquiv.withLpProdAssoc p R U V W).toLinearEquiv =
      Orientation.reindex R _ (finCongr (add_assoc n m k).symm) o₁_₂₃ := by
  let eL := (WithLp.linearEquiv p R (WithLp p (U × V) × W)).trans
    ((WithLp.linearEquiv p R (U × V)).prodCongr (LinearEquiv.refl R W))
  let eR := (WithLp.linearEquiv p R (U × WithLp p (V × W))).trans
    ((LinearEquiv.refl R U).prodCongr (WithLp.linearEquiv p R (V × W)))
  have hcomm : (LinearIsometryEquiv.withLpProdAssoc p R U V W).toLinearEquiv.trans eR =
      eL.trans (LinearEquiv.prodAssoc R U V W) := by ext x <;> simp [eL, eR]
  have hL : o₁₂_₃.map (Fin (n + m + k)) eL =
      (o₁.prod o₂ hn hm).prod o₃ (by rw [Module.finrank_prod, hn, hm]) hk := by
    rw [Orientation.map_trans, ho₁₂_₃, Orientation.map_prod, ho₁₂, Orientation.map_refl,
      Equiv.refl_apply]
  have hR : o₁_₂₃.map (Fin (n + (m + k))) eR =
      o₁.prod (o₂.prod o₃ hm hk) hn (by rw [Module.finrank_prod, hm, hk]) := by
    rw [Orientation.map_trans, ho₁_₂₃, Orientation.map_prod, ho₂₃, Orientation.map_refl,
      Equiv.refl_apply]
  refine (Orientation.map (Fin (n + m + k)) eR).injective ?_
  rw [← Orientation.map_trans, hcomm, Orientation.map_trans, hL, Orientation.map_prodAssoc_prod,
    Orientation.map_reindex, hR]

end Assoc

end Orientation
