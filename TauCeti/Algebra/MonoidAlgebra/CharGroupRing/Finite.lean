/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Basic

/-!
# Finiteness and Noetherianity of character group rings

For a Noetherian coefficient ring `O`, the character group ring `R_Ψ ⊆ ∏_{ψ ∈ Ψ} O` of any finite
set `Ψ` of characters is a finitely generated `O`-module (even when the group `G` is infinite), and
any module-finite character group ring `R_Ψ` over a Noetherian ring `O` is itself Noetherian.

## Main results

* `Set.charGroupRing.instModuleFinite`: for a Noetherian coefficient ring `O` and a finite set
  `Ψ` of characters, `R_Ψ` is module-finite over `O`.
* `Set.charGroupRing.instIsNoetherianRing`: over a Noetherian ring `O`, any module-finite
  character group ring `R_Ψ` is a Noetherian ring.
-/

public section

namespace Set.charGroupRing

/-- Over a Noetherian coefficient ring `O`, the character group ring of any finite set `Ψ` of
characters is a finite `O`-module (even when `G` is infinite), as an `O`-submodule of `Ψ → O`. -/
instance instModuleFinite {O G : Type*} [CommRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)}
    [Finite Ψ] [IsNoetherianRing O] : Module.Finite O Ψ.charGroupRing :=
  Module.Finite.of_injective Ψ.charGroupRing.toSubmodule.subtype Subtype.val_injective

/-- Over a Noetherian ring `O`, any module-finite character group ring `R_Ψ` is a Noetherian ring
(in particular whenever `G` is finite or `Ψ` is finite). -/
instance instIsNoetherianRing {O G : Type*} [CommRing O] [CommGroup G] {Ψ : Set (G →* Oˣ)}
    [IsNoetherianRing O] [Module.Finite O Ψ.charGroupRing] : IsNoetherianRing Ψ.charGroupRing :=
  IsNoetherianRing.of_finite O Ψ.charGroupRing

end Set.charGroupRing
