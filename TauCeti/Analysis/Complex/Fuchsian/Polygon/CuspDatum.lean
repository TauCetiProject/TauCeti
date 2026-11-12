/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.Polygon.Convex

/-!
# Cusp data at ideal vertices of a convex polygon

For a polygon whose ideal vertices are cusp points of a discrete subgroup, choose normalized
cusp data at each ideal vertex. Their scalings extend to a family indexed by all vertices and
carry each ideal vertex to infinity.
-/

public section

open UpperHalfPlane
open scoped MatrixGroups OnePoint

namespace TauCeti.UpperHalfPlane.ConvexPolygon

variable {n : ℕ} [NeZero n] (P : ConvexPolygon n) {Γ : Subgroup PSL(2, ℝ)}

/-- Cusp data at the ideal vertices, together with scalings sending those vertices to infinity.
The scalings agree with the chosen cusp data at ideal vertices; finite vertices require no data.
-/
theorem exists_cuspDatum_scaling [DiscreteTopology Γ]
    (hcusp : ∀ i c, P.vertex i = .inr c → Γ.IsCuspPoint c) :
    ∃ D : {i : Fin n // (P.vertex i).isRight} → Γ.CuspDatum,
      (∀ i : {i : Fin n // (P.vertex i).isRight}, P.vertex i = .inr (D i).cusp) ∧
      ∃ g : Fin n → PSL(2, ℝ),
        (∀ i (hi : (P.vertex i).isRight), g i = (D ⟨i, hi⟩).scaling) ∧
        ∀ i c, P.vertex i = .inr c → g i • c = ∞ := by
  classical
  have hex (i : {i : Fin n // (P.vertex i).isRight}) :
      ∃ D : Γ.CuspDatum, P.vertex i = .inr D.cusp := by
    obtain ⟨c, hc⟩ := Sum.isRight_iff.mp i.property
    obtain ⟨D, hD⟩ := (hcusp i c hc).exists_cuspDatum_cusp_eq
    exact ⟨D, by rw [hD]; exact hc⟩
  choose D hD using hex
  let g (i : Fin n) : PSL(2, ℝ) :=
    if hi : (P.vertex i).isRight then (D ⟨i, hi⟩).scaling else 1
  refine ⟨D, hD, g, fun i hi ↦ dite_eq_left hi, ?_⟩
  intro i c hi
  have hright : (P.vertex i).isRight := by simp [hi]
  have heq : (D ⟨i, hright⟩).cusp = c := Sum.inr.inj ((hD ⟨i, hright⟩).symm.trans hi)
  simpa only [g, dite_eq_left hright, heq] using (D ⟨i, hright⟩).scaling_smul_cusp

end TauCeti.UpperHalfPlane.ConvexPolygon
