/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Defs
import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Basic

/-!
# Products in small strands algebras

Two products in the strands algebras `A(4, 2)` and `A(3, 1)` of Lipshitz, Ozsváth and Thurston
over `𝔽₂`, with points `1, …, n` written `0, …, n - 1`.

* In `A(4, 2)` the diagrams `φ = (1 ↦ 3, 2 ↦ 2)` and `ψ = (2 ↦ 4, 3 ↦ 3)` each have one
  crossing, and their composite `(1 ↦ 3, 2 ↦ 4)` has none. Since `0 ≠ 1 + 1` the concatenation
  has a double crossing and the product `φ ψ` is zero, although the target of `φ` is the source of
  `ψ`.
* In `A(3, 1)` the product of `(1 ↦ 2)` and `(2 ↦ 3)` is `(1 ↦ 3)`: no diagram has a crossing.
-/

open TauCeti StrandsAlgebra

example :
    let φ : StrandDiagram (Fin 4) :=
      ⟨(PEquiv.ofSet ({0, 1} : Finset (Fin 4))).trans (Equiv.swap 0 2).toPEquiv, by decide⟩
    let ψ : StrandDiagram (Fin 4) :=
      ⟨(PEquiv.ofSet ({1, 2} : Finset (Fin 4))).trans (Equiv.swap 1 3).toPEquiv, by decide⟩
    φ.inversionCount = 1 ∧ ψ.inversionCount = 1 ∧ (φ.trans ψ).inversionCount = 0 ∧
      φ.target = ψ.source ∧ (of φ * of ψ : StrandsAlgebra (ZMod 2) (Fin 4)) = 0 := by
  intro φ ψ
  have h : ¬φ.Composable ψ := by decide
  refine ⟨by decide, by decide, by decide, by decide,
    of_mul_of_of_not_composable h⟩

example :
    let single (i j : Fin 3) (h : i ≤ j) : StrandDiagram (Fin 3) :=
      ⟨PEquiv.single i j, fun _ _ hk ↦ by
        obtain ⟨rfl, rfl⟩ := (PEquiv.mem_single_iff _ _ _ _).1 hk
        exact h⟩
    (of (single 0 1 (by decide)) * of (single 1 2 (by decide)) :
      StrandsAlgebra (ZMod 2) (Fin 3)) = of (single 0 2 (by decide)) := by
  intro single
  rw [of_mul_of_of_composable (by decide)]
  congr 1
  exact StrandDiagram.toPEquiv_injective (PEquiv.single_trans_single _ _ _)
