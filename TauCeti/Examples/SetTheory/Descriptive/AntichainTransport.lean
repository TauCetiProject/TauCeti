/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.AntichainTransport

/-!
# Regression examples: transporting antichains along measurable embeddings

These examples exercise the transport from a downstream module, through public statements only:

* along any measurable equivalence of Polish spaces, which need not be continuous, thinness of a
  set for a relation is thinness of its image for the transported relation;
* for equality the compatibility hypothesis holds for every measurable embedding, by injectivity,
  so a set carries a Cantor antichain for equality exactly when its image does.
-/

open MeasureTheory

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

-- A measurable equivalence transports thinness, with no continuity assumed.
example (e : X ≃ᵐ Y) (E : Setoid X) (A : Set X) :
    (E.comap e.symm).IsThinOn (e '' A) ↔ E.IsThinOn A :=
  Setoid.isThinOn_image_iff e.measurableEmbedding (fun x y => by simp [Setoid.comap_rel]) A

-- For equality, any measurable embedding transports Cantor antichains.
example {g : X → Y} (hg : MeasurableEmbedding g) (A : Set X) :
    (⊥ : Setoid Y).HasCantorAntichainOn (g '' A) ↔ (⊥ : Setoid X).HasCantorAntichainOn A :=
  Setoid.hasCantorAntichainOn_image_iff hg
    (fun x y => by simpa [Setoid.bot_def] using hg.injective.eq_iff) A
