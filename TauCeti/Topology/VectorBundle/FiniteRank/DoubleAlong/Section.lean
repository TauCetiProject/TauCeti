/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.DoubleAlong

/-!
# Doubling sections real along the glued set

Let `C` be a complex core over `X`, real along `A ⊆ X`, so that it encodes a pair `(C, F)` with `F`
the real coordinate subbundle over `A`. A section of `C` is presented as a bundle map
`σ : trivial ℂ X 1 ⟶ C` from the trivial line core, the section being the image of the constant
vector `1`. It is *real along `A`* when its fibre maps over `A` commute with coordinatewise
conjugation, that is, when its values over `A` lie in `F`.

Such a section doubles to a section of the doubled core over `DoubleAlong A`
(`FiniteRankBundleCore.doubleAlongSection`): `σ` on the first sheet and its conjugate on the
second sheet (`fiberMap_doubleAlongSection_inl`, `fiberMap_doubleAlongSection_inr`). The two agree
over `A` because the values there are real. It is `doubleAlongMap σ` composed with the
identification of the double of the trivial line core with the trivial line core
(`doubleAlongTrivialIso`), so it is continuous by construction. Its zeros are the points of the
double over the zeros of `σ` (`doubleAlongSection_eq_zero_iff`); in particular it has finitely many
zeros when `σ` has (`finite_setOf_doubleAlongSection_eq_zero`).

Counting the zeros of doubled sections computes the first Chern class of the doubled bundle, hence
the Maslov index of a bundle pair over a Riemann surface with boundary.
-/

public section

noncomputable section

open Bundle CategoryTheory Set WithConv

namespace TauCeti.FiniteRankBundleCore

universe u

variable {X : Type u} [TopologicalSpace X] {A : Set X} {C : FiniteRankBundleCore ℂ X}
  (hC : C.IsRealAlong A) (σ : trivial ℂ X 1 ⟶ C)
  (hσ : ∀ a ∈ A, ∀ v, σ.fiberMap a (star v) = star (σ.fiberMap a v))

/-- **The double of a section real along `A`**: the section `σ` of `C`, presented as a bundle map
from the trivial line core, on the first sheet, and its conjugate on the second sheet, as a section
of the doubled core. -/
def doubleAlongSection : trivial ℂ (DoubleAlong A) 1 ⟶ C.doubleAlong hC :=
  (doubleAlongTrivialIso 1).inv ≫ doubleAlongMap (isRealAlong_trivial 1 A) hC σ hσ

/-- On the first sheet the doubled section is `σ`. -/
@[simp] theorem fiberMap_doubleAlongSection_inl (x : X) :
    (doubleAlongSection hC σ hσ).fiberMap (DoubleAlong.inl A x) = σ.fiberMap x := by
  rw [doubleAlongSection, fiberMap_comp, fiberMap_doubleAlongTrivialIso_inv,
    fiberMap_doubleAlongMap_inl]
  -- The identification of the trivial double is the identity of `Fin 1 → ℂ`.
  exact (σ.fiberMap x).comp_id

/-- On the second sheet the doubled section is the conjugate of `σ`. -/
@[simp] theorem fiberMap_doubleAlongSection_inr (x : X) :
    (doubleAlongSection hC σ hσ).fiberMap (DoubleAlong.inr A x) =
      (star (toConv (σ.fiberMap x))).ofConv := by
  rw [doubleAlongSection, fiberMap_comp, fiberMap_doubleAlongTrivialIso_inv,
    fiberMap_doubleAlongMap_inr]
  -- The identification of the trivial double is the identity of `Fin 1 → ℂ`.
  exact (star (toConv (σ.fiberMap x))).ofConv.comp_id

/-- The doubled section vanishes exactly over the zeros of `σ`. -/
theorem doubleAlongSection_eq_zero_iff (y : DoubleAlong A) :
    (doubleAlongSection hC σ hσ).fiberMap y = 0 ↔ σ.fiberMap (DoubleAlong.fold A y) = 0 := by
  induction y using DoubleAlong.induction_on with
  | hl x =>
    rw [fiberMap_doubleAlongSection_inl, DoubleAlong.fold_inl]
    -- The two zero maps are those of `Fin 1 → ℂ` written through the ranks of `trivial ℂ X 1`
    -- and of its double, equal by definition (`rank_trivial`, `rank_doubleAlong`).
    exact Iff.rfl
  | hr x =>
    rw [fiberMap_doubleAlongSection_inr, DoubleAlong.fold_inr]
    constructor
    · intro h
      have h' : star (toConv (σ.fiberMap x)) = 0 := congrArg toConv h
      rw [star_eq_zero] at h'
      exact congrArg ofConv h'
    · intro h
      rw [h, toConv_zero, star_zero, ofConv_zero]
      -- As on the first sheet, the two zero maps differ only in how the rank is written.
      exact rfl

/-- A section real along `A` with finitely many zeros doubles to a section with finitely many
zeros. -/
theorem finite_setOf_doubleAlongSection_eq_zero (h : {x | σ.fiberMap x = 0}.Finite) :
    {y | (doubleAlongSection hC σ hσ).fiberMap y = 0}.Finite := by
  have hsub : {y | (doubleAlongSection hC σ hσ).fiberMap y = 0} ⊆
      DoubleAlong.inl A '' {x | σ.fiberMap x = 0} ∪
        DoubleAlong.inr A '' {x | σ.fiberMap x = 0} := by
    intro y hy
    induction y using DoubleAlong.induction_on with
    | hl x => exact .inl ⟨x, by simpa [doubleAlongSection_eq_zero_iff] using hy, rfl⟩
    | hr x => exact .inr ⟨x, by simpa [doubleAlongSection_eq_zero_iff] using hy, rfl⟩
  exact ((h.image _).union (h.image _)).subset hsub

end TauCeti.FiniteRankBundleCore
