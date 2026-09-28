/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.SquareGrid
public import TauCeti.Topology.ContinuousMap.Subdivision

/-!
# Local square relations in the fundamental groupoid

A homotopy square whose image lies in a cover member identifies the two routes around its
boundary already in the fundamental groupoid of that member. Rectangular subdivisions turn
this into a finite family of local relations, one per cell. These are the relations used in
the groupoid van Kampen colimit theorem.

The boundary argument follows Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory Set Topology TauCeti.HomotopySquare
open scoped unitInterval

universe u v

namespace TauCeti.FundamentalGroupoid

variable {X : Type v} [TopologicalSpace X]

/-- The bottom-right and left-top routes across a subordinate rectangular cell agree in the
fundamental groupoid of its cover member. -/
theorem squareCell_lowerRight_eq_leftUpper_in_subset
    (H : C(unitInterval × unitInterval, X)) (a b c d : unitInterval)
    (hab : a ≤ b) (hcd : c ≤ d) (V : Set X)
    (hV : MapsTo H (Icc a b ×ˢ Icc c d) V) :
    Path.Homotopic.Quotient.mk
        (lowerRight.map (squareCellIn H a b c d hab hcd V hV).continuous) =
      Path.Homotopic.Quotient.mk
        (leftUpper.map (squareCellIn H a b c d hab hcd V hV).continuous) :=
  Path.Homotopic.Quotient.eq.mpr
    (lowerRight_homotopic_leftUpper (squareCellIn H a b c d hab hcd V hV))

/-- A neighbourhood cover of the image of a homotopy square gives a finite grid in which each
cell's two boundary routes agree within one cover member. These are the local relations used by
the Čech van Kampen argument. -/
theorem exists_subordinate_homotopy_grid_relations {ι : Sort u} {U : ι → Set X}
    (H : C(unitInterval × unitInterval, X))
    (hU : ∀ z : unitInterval × unitInterval, ∃ i, U i ∈ 𝓝 (H z)) :
    ∃ (n : ℕ) (t : Fin (n + 1) → unitInterval),
      t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
        ∀ j k : Fin n, ∃ (i : ι)
          (hab : t j.castSucc ≤ t j.succ) (hcd : t k.castSucc ≤ t k.succ)
          (hV : MapsTo H (Icc (t j.castSucc) (t j.succ) ×ˢ
            Icc (t k.castSucc) (t k.succ)) (U i)),
            Path.Homotopic.Quotient.mk
                (lowerRight.map (squareCellIn H _ _ _ _ hab hcd (U i) hV).continuous) =
              Path.Homotopic.Quotient.mk
                (leftUpper.map (squareCellIn H _ _ _ _ hab hcd (U i) hV).continuous) := by
  obtain ⟨n, t, ht0, htmono, ht1, htcover⟩ :=
    ContinuousMap.exists_grid_subdivision H (fun i ↦ interior (U i))
      (fun _ ↦ isOpen_interior) (fun z ↦ by
        obtain ⟨i, hi⟩ := hU z
        exact ⟨i, mem_interior_iff_mem_nhds.mpr hi⟩)
  refine ⟨n, fun k ↦ t k, by simpa using ht0, by simpa using ht1 n le_rfl,
    fun a b hab ↦ htmono (by simpa using hab), ?_⟩
  intro j k
  obtain ⟨i, hi⟩ := htcover j k
  have hV : MapsTo H (Icc (t j.castSucc) (t j.succ) ×ˢ
      Icc (t k.castSucc) (t k.succ)) (U i) :=
    fun z hz ↦ interior_subset (hi hz)
  have hj : t j.castSucc ≤ t j.succ := htmono j.castSucc_le_succ
  have hk : t k.castSucc ≤ t k.succ := htmono k.castSucc_le_succ
  exact ⟨i, hj, hk, hV,
    squareCell_lowerRight_eq_leftUpper_in_subset H _ _ _ _ hj hk (U i) hV⟩

end TauCeti.FundamentalGroupoid
