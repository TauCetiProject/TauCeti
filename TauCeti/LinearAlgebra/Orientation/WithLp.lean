/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.WithLp
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Symmetry and associativity of product orientations on `WithLp`

For finite free modules over a strict ordered commutative ring `R`, transporting the canonical
product orientation `Orientation.prod o₁ o₂` along `(WithLp.linearEquiv p R (E × F)).symm` equips
`WithLp p (E × F)` with an ordered product orientation. This file lifts the Koszul swap sign
`Orientation.map_prodComm_prod` and the associativity law `Orientation.map_prodAssoc_prod` from
bare Cartesian products to `WithLp p`, with no metric or seminorm assumptions on the summands.

## Main results

* `Orientation.map_withLpProdComm_prod`: swapping `WithLp p (E × F)` and `WithLp p (F × E)` along
  `(LinearEquiv.prodComm R E F).withLpCongr p` multiplies the product orientation by
  `(-1) ^ (m * n)`.
* `Orientation.map_withLpProdComm_prod_of_even`: when `Even (m * n)`, the `WithLp` swap preserves
  the ordered product orientation.
* `Orientation.map_withLpProdAssoc_prod`: `LinearEquiv.withLpProdAssoc p R E F G` carries the
  left-associated `WithLp` product orientation to the right-associated one.
-/

public section

noncomputable section

open Module
open scoped ENNReal

namespace Orientation

variable {p : ℝ≥0∞} {R E F G : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Module.Free R E] [Module.Finite R E]
  [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
  {m n : ℕ}

/-- Exchanging the factors of `WithLp p (E × F)` multiplies the ordered product orientation by
`(-1) ^ (m * n)`. When `E` and `F` are seminormed modules and `1 ≤ p`,
`(LinearEquiv.prodComm R E F).withLpCongr p` is `(LinearIsometryEquiv.withLpProdComm p R E F)` as a
linear equivalence. -/
theorem map_withLpProdComm_prod (o₁ : Orientation R E (Fin m)) (o₂ : Orientation R F (Fin n))
    (hm : Module.finrank R E = m) (hn : Module.finrank R F = n) :
    ((o₁.prod o₂ hm hn).map (Fin (m + n)) (WithLp.linearEquiv p R (E × F)).symm).map (Fin (m + n))
        ((LinearEquiv.prodComm R E F).withLpCongr p) =
      (-1 : Rˣ) ^ (m * n) • Orientation.reindex R (WithLp p (F × E)) (finCongr (add_comm n m))
        ((o₂.prod o₁ hn hm).map (Fin (n + m)) (WithLp.linearEquiv p R (F × E)).symm) := by
  have heq : (WithLp.linearEquiv p R (E × F)).symm.trans
        ((LinearEquiv.prodComm R E F).withLpCongr p) =
      (LinearEquiv.prodComm R E F).trans (WithLp.linearEquiv p R (F × E)).symm := by
    ext x
    rfl
  rw [← Orientation.map_trans, heq, Orientation.map_trans,
    Orientation.map_prodComm_prod o₁ o₂ hm hn, Orientation.map_units_smul, Orientation.map_reindex]

/-- Whenever `Even (m * n)` (in particular when `m` or `n` is even), exchanging the factors of
`WithLp p (E × F)` preserves the ordered product orientation. -/
theorem map_withLpProdComm_prod_of_even (o₁ : Orientation R E (Fin m))
    (o₂ : Orientation R F (Fin n)) (hm : Module.finrank R E = m) (hn : Module.finrank R F = n)
    (h : Even (m * n)) :
    ((o₁.prod o₂ hm hn).map (Fin (m + n)) (WithLp.linearEquiv p R (E × F)).symm).map (Fin (m + n))
        ((LinearEquiv.prodComm R E F).withLpCongr p) =
      Orientation.reindex R (WithLp p (F × E)) (finCongr (add_comm n m))
        ((o₂.prod o₁ hn hm).map (Fin (n + m)) (WithLp.linearEquiv p R (F × E)).symm) := by
  rw [map_withLpProdComm_prod, h.neg_one_pow, one_smul]

/-- **Associativity of `WithLp` product orientations.** `LinearEquiv.withLpProdAssoc` carries the
left-associated product orientation `((o₁ × o₂) × o₃)` on `WithLp p (WithLp p (E × F) × G)` to the
right-associated product orientation `(o₁ × (o₂ × o₃))` on `WithLp p (E × WithLp p (F × G))`,
reindexed along `add_assoc`. -/
theorem map_withLpProdAssoc_prod [AddCommGroup G] [Module R G] [Module.Free R G] [Module.Finite R G]
    {k : ℕ} (o₁ : Orientation R E (Fin k)) (o₂ : Orientation R F (Fin m))
    (o₃ : Orientation R G (Fin n)) (hk : Module.finrank R E = k) (hm : Module.finrank R F = m)
    (hn : Module.finrank R G = n) :
    let o₁₂ := (o₁.prod o₂ hk hm).map (Fin (k + m)) (WithLp.linearEquiv p R (E × F)).symm
    let o₂₃ := (o₂.prod o₃ hm hn).map (Fin (m + n)) (WithLp.linearEquiv p R (F × G)).symm
    ((o₁₂.prod o₃ (by rw [WithLp.finrank_eq, Module.finrank_prod, hk, hm]) hn).map
        (Fin (k + m + n)) (WithLp.linearEquiv p R (WithLp p (E × F) × G)).symm).map
        (Fin (k + m + n)) (LinearEquiv.withLpProdAssoc p R E F G) =
      Orientation.reindex R (WithLp p (E × WithLp p (F × G))) (finCongr (add_assoc k m n).symm)
        ((o₁.prod o₂₃ hk (by rw [WithLp.finrank_eq, Module.finrank_prod, hm, hn])).map
          (Fin (k + (m + n))) (WithLp.linearEquiv p R (E × WithLp p (F × G))).symm) := by
  intro o₁₂ o₂₃
  let eEF := (WithLp.linearEquiv p R (E × F)).symm
  let eFG := (WithLp.linearEquiv p R (F × G)).symm
  let eR := (WithLp.linearEquiv p R (E × WithLp p (F × G))).symm
  have ho₁₂' : o₁₂.prod o₃ (by rw [WithLp.finrank_eq, Module.finrank_prod, hk, hm]) hn =
      ((o₁.prod o₂ hk hm).prod o₃ (by rw [Module.finrank_prod, hk, hm]) hn).map (Fin (k + m + n))
        (eEF.prodCongr (.refl R G)) := by
    have h := (Orientation.map_prod (o₁.prod o₂ hk hm) o₃
      (by rw [Module.finrank_prod, hk, hm]) hn eEF (.refl R G)).symm
    simpa [o₁₂, eEF] using h
  have ho₂₃' : o₁.prod o₂₃ hk (by rw [WithLp.finrank_eq, Module.finrank_prod, hm, hn]) =
      (o₁.prod (o₂.prod o₃ hm hn) hk (by rw [Module.finrank_prod, hm, hn])).map
        (Fin (k + (m + n))) ((LinearEquiv.refl R E).prodCongr eFG) := by
    have h := (Orientation.map_prod o₁ (o₂.prod o₃ hm hn)
      hk (by rw [Module.finrank_prod, hm, hn]) (.refl R E) eFG).symm
    simpa [o₂₃, eFG] using h
  have heq : (eEF.prodCongr (.refl R G)).trans
        ((WithLp.linearEquiv p R (WithLp p (E × F) × G)).symm.trans
          (LinearEquiv.withLpProdAssoc p R E F G)) =
      (LinearEquiv.prodAssoc R E F G).trans (((LinearEquiv.refl R E).prodCongr eFG).trans eR) := by
    ext x
    simp [eEF, eFG, eR]
  rw [ho₁₂', ← Orientation.map_trans, ← Orientation.map_trans, heq,
    Orientation.map_trans, Orientation.map_prodAssoc_prod,
    Orientation.map_reindex, ho₂₃', ← Orientation.map_trans]

end Orientation
