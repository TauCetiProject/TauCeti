/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic

/-!
# Fibre homotopy equivalences and pairs

A fibre homotopy equivalence over `B` induces maps and inverse homotopies of pairs of
total spaces relative to the preimage of any subset of `B`. The homotopies stay over
the base and hence preserve these preimages at every time.
-/

public noncomputable section

open CategoryTheory ContinuousMap

namespace TauCeti.FiberHomotopyEquiv

universe u v

variable {E E' : Type u} {B : Type v}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  {p : C(E, B)} {q : C(E', B)} (Φ : FiberHomotopyEquiv p q) (S : Set B)

/-- The map of pairs of total spaces relative to the preimages of a base subset. -/
def preimagePairMap :
    TopPair.ofSubset (X := TopCat.of E) (p ⁻¹' S) ⟶
      TopPair.ofSubset (X := TopCat.of E') (q ⁻¹' S) :=
  TopPair.ofSubsetMap (TopCat.ofHom Φ.toFun) fun x hx ↦ by
    simpa only [TopCat.hom_ofHom, Set.mem_preimage, ← ContinuousMap.comp_apply,
      Φ.comp_toFun] using hx

@[simp]
theorem preimagePairMap_fst :
    TopPair.Hom.fst (Φ.preimagePairMap S) = TopCat.ofHom Φ.toFun := by
  rw [preimagePairMap]
  exact TopPair.ofSubsetMap_fst (X := TopCat.of E) _ _

/-- The composite of the induced pair maps is homotopic to the identity as a map of pairs.
The homotopy is chosen from the fibre homotopy equivalence, so it preserves the preimage
of every base subset at every time. -/
def preimagePairCompHomotopy :
    TopPair.Homotopy (Φ.preimagePairMap S ≫ Φ.symm.preimagePairMap S) (𝟙 _) := by
  let H := Φ.left_inv.some
  have hS (t : unitInterval) (x : E) (hx : x ∈ p ⁻¹' S) :
      H (t, x) ∈ p ⁻¹' S := by
    simpa only [Set.mem_preimage, apply_homotopyWith H t x] using hx
  have hstart (h : Set.MapsTo (TopCat.ofHom (Φ.invFun.comp Φ.toFun))
      (p ⁻¹' S) (p ⁻¹' S)) :
      Φ.preimagePairMap S ≫ Φ.symm.preimagePairMap S =
        TopPair.ofSubsetMap (TopCat.ofHom (Φ.invFun.comp Φ.toFun)) h := by
    simp only [preimagePairMap, symm_toFun]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ h rfl
  -- ofSubsetHomotopy has induced subset maps as endpoints, not a composite and an
  -- identity in TopPair. Identify these endpoints explicitly before using it.
  rw [hstart (fun x hx ↦ H.apply_zero x ▸ hS 0 x hx),
    ← TopPair.ofSubsetMap_id (fun x hx ↦ H.apply_one x ▸ hS 1 x hx)]
  exact TopPair.ofSubsetHomotopy
    (g₀ := TopCat.ofHom (Φ.invFun.comp Φ.toFun)) (g₁ := 𝟙 (TopCat.of E))
    H.toHomotopy hS

end TauCeti.FiberHomotopyEquiv
