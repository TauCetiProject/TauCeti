/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.BelyiPair
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Automorphism, deck, and regularity comparisons for analytic Belyi pairs and dessins

Identifies the automorphism and deck groups of `P` with the automorphism group of the ribbon
graph of its monodromy triple, and characterizes regularity in terms of its dessin.
-/

public noncomputable section

namespace TauCeti.AnalyticBelyiPair

open ThricePuncturedSphere RiemannSurface BipartiteRibbonGraph

universe u

section RibbonAut

variable (P : AnalyticBelyiPair.{u}) {n : ℕ} (ν : P.restrict ⁻¹' {basePt} ≃ Fin n)

/-- **The automorphism group of `P` is the automorphism group of its dessin.** -/
def isoMulEquivRibbonGraphAut :
    P.Iso P ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  (P.isoMulEquivAutomorphismGroup ν).trans
    (P.isCoveringMap_restrict.monodromyTriple ν).automorphismGroupMulEquivRibbonGraphAut

/-- On edges (`Fin n`), `isoMulEquivRibbonGraphAut` sends `i` to `ν (e • ν.symm i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_apply_edge (e : P.Iso P) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν e).edge i = ν (e • ν.symm i) :=
  (Equiv.congr_fun (PermutationTriple.automorphismGroupMulEquivRibbonGraphAut_edge _ _) i).trans
    (P.coe_isoMulEquivAutomorphismGroup_apply ν e i)

/-- The automorphism of `P` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem isoMulEquivRibbonGraphAut_symm_smul
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    (P.isoMulEquivRibbonGraphAut ν).symm f • ν.symm i = ν.symm (f.edge i) := by
  simp [isoMulEquivRibbonGraphAut]; rfl

/-- **The deck group of `P.β` is the automorphism group of its dessin.** -/
def deckMulEquivRibbonGraphAut :
    deck P.β ≃* (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut :=
  P.isoMulEquivDeck.symm.trans (P.isoMulEquivRibbonGraphAut ν)

/-- On edges (`Fin n`), `deckMulEquivRibbonGraphAut` acts via `isoMulEquivDeck.symm` on the fibre
over `1/2`. -/
@[simp] theorem deckMulEquivRibbonGraphAut_apply_edge (φ : deck P.β) (i : Fin n) :
    (P.deckMulEquivRibbonGraphAut ν φ).edge i = ν (P.isoMulEquivDeck.symm φ • ν.symm i) :=
  P.isoMulEquivRibbonGraphAut_apply_edge ν (P.isoMulEquivDeck.symm φ) i

/-- The deck transformation of `P.β` attached to `f` sends `ν.symm i` to `ν.symm (f.edge i)`. -/
@[simp] theorem coe_deckMulEquivRibbonGraphAut_symm_apply
    (f : (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.Aut) (i : Fin n) :
    ((P.deckMulEquivRibbonGraphAut ν).symm f : P.X ≃ₜ P.X) (ν.symm i) =
      (ν.symm (f.edge i) : P.X) := by
  simp [deckMulEquivRibbonGraphAut, ← Iso.coe_smul]

end RibbonAut

/-- `P` is regular if and only if the ribbon graph of its monodromy triple is regular. -/
theorem isRegular_iff_ribbonGraph {P : AnalyticBelyiPair.{u}} {n : ℕ}
    (ν : P.restrict ⁻¹' {basePt} ≃ Fin n) :
    P.IsRegular ↔ (P.isCoveringMap_restrict.monodromyTriple ν).ribbonGraph.IsRegular := by
  rw [isRegular_iff_monodromyTriple ν, PermutationTriple.isRegular_ribbonGraph]

end TauCeti.AnalyticBelyiPair
