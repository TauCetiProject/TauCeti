/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.DenseGraphLimits.HomDensity.Finite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

/-!
# Regression examples: edge and triangle densities of small graphs

These examples compute the homomorphism density `t(F, G)`, normalized by `|V(G)| ^ |V(F)|`, and
the injective density `t₀(F, G)`, normalized by the falling factorial `(|V(G)|)_{|V(F)|}`, for the
edge `K₂` and the triangle `K₃` in the complete graph `K₄` and the path `P₃` on three vertices:

* in `K₄`: `t(K₂, K₄) = 3/4`, `t(K₃, K₄) = 3/8`, and both injective densities are `1`;
* in `P₃`, with two edges and no triangle: `t(K₂, P₃) = 4/9`, `t₀(K₂, P₃) = 2/3`, and
  `t(K₃, P₃) = t₀(K₃, P₃) = 0`;
* the edgeless pattern on three vertices has density `1` in `P₃`.
-/

open Finset SimpleGraph TauCeti.DenseGraphLimits

/-! ### The complete graph `K₄` -/

example : homDensityFin (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 4)) = 3 / 4 := by
  have h : #(⊤ : SimpleGraph (Fin 4)).edgeFinset = 6 := by decide
  rw [homDensityFin_top_fin_two, h, Fintype.card_fin]
  norm_num

example : homDensityFin (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 4)) = 3 / 8 := by
  have h : #((⊤ : SimpleGraph (Fin 4)).cliqueFinset 3) = 4 := by decide
  rw [homDensityFin_top_fin_three, h, Fintype.card_fin]
  norm_num

example : injHomDensity (⊤ : SimpleGraph (Fin 2)) (⊤ : SimpleGraph (Fin 4)) = 1 :=
  injHomDensity_top_right _ (by simp)

example : injHomDensity (⊤ : SimpleGraph (Fin 3)) (⊤ : SimpleGraph (Fin 4)) = 1 :=
  injHomDensity_top_right _ (by simp)

/-! ### The path `P₃` -/

example : homDensityFin (⊤ : SimpleGraph (Fin 2)) (pathGraph 3) = 4 / 9 := by
  have h : #(pathGraph 3).edgeFinset = 2 := by decide
  rw [homDensityFin_top_fin_two, h, Fintype.card_fin]
  norm_num

example : injHomDensity (⊤ : SimpleGraph (Fin 2)) (pathGraph 3) = 2 / 3 := by
  have h : #(pathGraph 3).edgeFinset = 2 := by decide
  rw [injHomDensity_top_fin_two, h, Fintype.card_fin]
  norm_num [Nat.choose]

example : homDensityFin (⊤ : SimpleGraph (Fin 3)) (pathGraph 3) = 0 := by
  have h : #((pathGraph 3).cliqueFinset 3) = 0 := by decide
  rw [homDensityFin_top_fin_three, h, Fintype.card_fin]
  norm_num

example : injHomDensity (⊤ : SimpleGraph (Fin 3)) (pathGraph 3) = 0 := by
  have h : #((pathGraph 3).cliqueFinset 3) = 0 := by decide
  rw [injHomDensity_top_fin_three, h, Fintype.card_fin]
  norm_num

example : homDensityFin (⊥ : SimpleGraph (Fin 3)) (pathGraph 3) = 1 :=
  homDensityFin_bot_left _
