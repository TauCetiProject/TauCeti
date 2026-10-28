/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Lindelof
public import TauCeti.Topology.Category.TopCat.Normal
public import TauCeti.Topology.Compactness.Paracompact

/-!
# Paracompact sequential colimits

A sequence of normal T1 Lindelöf spaces joined by closed embeddings has a paracompact
colimit in `TopCat`. The colimit carries the actual final topology, with no change of topology
or local compactness assumption. This supplies paracompactness for spaces constructed by
successive closed attachments once their stages are known to be normal T1 and Lindelöf.

The normality and Lindelöf colimit theorems supply the hypotheses of the regular Lindelöf
paracompactness theorem; T1 is inherited from the stages and makes the normal colimit regular.
-/

public section

open CategoryTheory Limits Topology

namespace TauCeti.TopCat

/-- A sequential colimit of normal T1 Lindelöf spaces along closed embeddings is paracompact
for its final topology. It suffices to check closed embeddings on successor maps. -/
theorem paracompactSpace_of_isColimit {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}
    (hF : ∀ n : ℕ, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n)))) (hc : IsColimit c)
    [∀ n, NormalSpace (F.obj n)] [∀ n, T1Space (F.obj n)] [∀ n, LindelofSpace (F.obj n)] :
    ParacompactSpace c.pt := by
  have hmap {i j : ℕ} (hij : i ≤ j) : IsClosedEmbedding (F.map (homOfLE hij)) :=
    isClosedEmbedding_map_of_isWellOrderContinuous F (fun n _ ↦ hF n) hij
  let := t1Space_of_isColimit (fun _ _ hij ↦ (hmap hij).injective) hc
  let := normalSpace_of_isColimit hF hc
  let := lindelofSpace_of_isColimit hc
  exact paracompactSpace_of_regularSpace_lindelofSpace c.pt

end TauCeti.TopCat
