/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Topology.Subpath
public import TauCeti.Topology.ContinuousMap.Subdivision

/-!
# Rectangular subdivisions of a homotopy square

A rectangular cell of a continuous square can be reparameterized as a unit square, and its two
boundary routes from the lower-left to the upper-right corner are homotopic. These facts are used
with the existing grid-subdivision theorem to turn path homotopies into local relations for an
open-cover fundamental-groupoid calculation.

The boundary argument follows Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped unitInterval

universe u v

namespace TauCeti.HomotopySquare

/-- Every point of a subpath of the identity path lies between its endpoints. -/
lemma subpath_id_mem_uIcc (s t u : unitInterval) : Path.id.subpath s t u ∈ uIcc s t := by
  have hr := Set.mem_range_self u (f := Path.id.subpath s t)
  rw [Path.range_subpath] at hr
  simpa using hr

end TauCeti.HomotopySquare

namespace TauCeti

variable {X : Type v} [TopologicalSpace X]

/-- Reparameterize a rectangular cell of a homotopy square as a unit square. -/
def squareCell (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) : C(unitInterval × unitInterval, X) :=
  H.comp ((Path.id.subpath a b).toContinuousMap.prodMap
    (Path.id.subpath c d).toContinuousMap)

@[simp]
lemma squareCell_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (z : unitInterval × unitInterval) :
    squareCell H a b c d z = H ((Path.id.subpath a b) z.1, (Path.id.subpath c d) z.2) :=
  by simp [squareCell, Prod.map_apply']

/-- A cell whose image lies in `V`, regarded as a map with codomain `V`. -/
def squareCellIn (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    C(unitInterval × unitInterval, V) :=
  ⟨fun z ↦ ⟨squareCell H a b c d z,
      hV ⟨HomotopySquare.subpath_id_mem_uIcc a b z.1,
        HomotopySquare.subpath_id_mem_uIcc c d z.2⟩⟩,
    (squareCell H a b c d).continuous.subtype_mk _⟩

@[simp]
lemma coe_squareCellIn_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V)
    (z : unitInterval × unitInterval) :
    (squareCellIn H a b c d V hV z).1 = squareCell H a b c d z :=
  by simp [squareCellIn]

/-- The bottom edge of a cell, valued in the cover member containing it. -/
def squareCellBottom (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    Path (squareCellIn H a b c d V hV (0, 0))
      (squareCellIn H a b c d V hV (1, 0)) :=
  (Path.id.prod (Path.refl (0 : unitInterval))).map
    (squareCellIn H a b c d V hV).continuous

/-- The right edge of a cell, valued in the cover member containing it. -/
def squareCellRight (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    Path (squareCellIn H a b c d V hV (1, 0))
      (squareCellIn H a b c d V hV (1, 1)) :=
  ((Path.refl (1 : unitInterval)).prod Path.id).map
    (squareCellIn H a b c d V hV).continuous

/-- The left edge of a cell, valued in the cover member containing it. -/
def squareCellLeft (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    Path (squareCellIn H a b c d V hV (0, 0))
      (squareCellIn H a b c d V hV (0, 1)) :=
  ((Path.refl (0 : unitInterval)).prod Path.id).map
    (squareCellIn H a b c d V hV).continuous

/-- The top edge of a cell, valued in the cover member containing it. -/
def squareCellTop (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    Path (squareCellIn H a b c d V hV (0, 1))
      (squareCellIn H a b c d V hV (1, 1)) :=
  (Path.id.prod (Path.refl (1 : unitInterval))).map
    (squareCellIn H a b c d V hV).continuous

/-- The bottom edge of a cell, viewed in the ambient space. -/
@[simp]
lemma coe_squareCellBottom_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X)
    (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) (t : unitInterval) :
    (squareCellBottom H a b c d V hV t).1 =
      H ((Path.id.subpath a b) t, c) := by
  -- `simp` does not unfold the subtype-valued mapped path; expose its cell subpaths first.
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 0) = _
  simp

/-- The right edge of a cell, viewed in the ambient space. -/
@[simp]
lemma coe_squareCellRight_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X)
    (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) (t : unitInterval) :
    (squareCellRight H a b c d V hV t).1 =
      H (b, (Path.id.subpath c d) t) := by
  -- `simp` does not unfold the subtype-valued mapped path; expose its cell subpaths first.
  change H ((Path.id.subpath a b) 1, (Path.id.subpath c d) t) = _
  simp

/-- The left edge of a cell, viewed in the ambient space. -/
@[simp]
lemma coe_squareCellLeft_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X)
    (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) (t : unitInterval) :
    (squareCellLeft H a b c d V hV t).1 =
      H (a, (Path.id.subpath c d) t) := by
  -- `simp` does not unfold the subtype-valued mapped path; expose its cell subpaths first.
  change H ((Path.id.subpath a b) 0, (Path.id.subpath c d) t) = _
  simp

/-- The top edge of a cell, viewed in the ambient space. -/
@[simp]
lemma coe_squareCellTop_apply (H : C(unitInterval × unitInterval, X))
    (a b c d : unitInterval) (V : Set X)
    (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) (t : unitInterval) :
    (squareCellTop H a b c d V hV t).1 =
      H ((Path.id.subpath a b) t, d) := by
  -- `simp` does not unfold the subtype-valued mapped path; expose its cell subpaths first.
  change H ((Path.id.subpath a b) t, (Path.id.subpath c d) 1) = _
  simp

/-- The two boundary routes of a cell agree in the path-homotopy quotient of its cover member. -/
theorem squareCellBottom_trans_right_eq_left_trans_top
    (H : C(unitInterval × unitInterval, X)) (a b c d : unitInterval)
    (V : Set X) (hV : MapsTo H (uIcc a b ×ˢ uIcc c d) V) :
    (Path.Homotopic.Quotient.mk (squareCellBottom H a b c d V hV)).trans
        (Path.Homotopic.Quotient.mk (squareCellRight H a b c d V hV)) =
      (Path.Homotopic.Quotient.mk (squareCellLeft H a b c d V hV)).trans
        (Path.Homotopic.Quotient.mk (squareCellTop H a b c d V hV)) := by
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
  let F := squareCellIn H a b c d V hV
  let G := F.comp (ContinuousMap.prodSwap : C(unitInterval × unitInterval,
    unitInterval × unitInterval))
  let K : (G.curry 0).Homotopy (G.curry 1) :=
    { toContinuousMap := G, map_zero_left := fun _ ↦ rfl, map_one_left := fun _ ↦ rfl }
  have h := Path.Homotopic.map_trans_evalAt K (Path.id : Path (0 : unitInterval) 1)
  apply Path.Homotopic.Quotient.eq.mpr
  -- These identifications unfold the mapped product paths and `Homotopy.evalAt`;
  -- `Path.map_coe`, `Path.prod_coe`, and `ContinuousMap.curry_apply` are definitional here.
  have hb : squareCellBottom H a b c d V hV =
      Path.id.map (map_continuous (G.curry 0)) := by ext t; rfl
  have hr : squareCellRight H a b c d V hV = K.evalAt 1 := by ext t; rfl
  have hl : squareCellLeft H a b c d V hV = K.evalAt 0 := by ext t; rfl
  have ht : squareCellTop H a b c d V hV =
      Path.id.map (map_continuous (G.curry 1)) := by ext t; rfl
  rw [hb, hr, hl, ht]
  exact h

/-- A neighbourhood cover of a square gives a finite grid whose cell boundary routes agree
within one cover member. -/
theorem exists_grid_subdivision_squareCell_eq {ι : Sort u} {U : ι → Set X}
    (H : C(unitInterval × unitInterval, X))
    (hU : ∀ z : unitInterval × unitInterval, ∃ i, U i ∈ 𝓝 (H z)) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
        ∀ j k : Fin n, ∃ (i : ι)
          (hV : MapsTo H (uIcc (t j.castSucc) (t j.succ) ×ˢ
            uIcc (t k.castSucc) (t k.succ)) (U i)),
            (Path.Homotopic.Quotient.mk
                (squareCellBottom H _ _ _ _ (U i) hV)).trans
                (Path.Homotopic.Quotient.mk
                  (squareCellRight H _ _ _ _ (U i) hV)) =
              (Path.Homotopic.Quotient.mk
                (squareCellLeft H _ _ _ _ (U i) hV)).trans
                (Path.Homotopic.Quotient.mk
                  (squareCellTop H _ _ _ _ (U i) hV)) := by
  obtain ⟨n, t, ht0, ht1, htmono, htcover⟩ :=
    ContinuousMap.exists_grid_subdivision H U hU
  refine ⟨n, t, ht0, ht1, htmono, ?_⟩
  intro j k
  obtain ⟨i, hV⟩ := htcover j k
  have hj : t j.castSucc ≤ t j.succ := htmono j.castSucc_le_succ
  have hk : t k.castSucc ≤ t k.succ := htmono k.castSucc_le_succ
  have hV' : MapsTo H (uIcc (t j.castSucc) (t j.succ) ×ˢ
      uIcc (t k.castSucc) (t k.succ)) (U i) := by
    simpa only [uIcc_of_le hj, uIcc_of_le hk] using hV
  exact ⟨i, hV', squareCellBottom_trans_right_eq_left_trans_top H _ _ _ _ (U i) hV'⟩

end TauCeti
