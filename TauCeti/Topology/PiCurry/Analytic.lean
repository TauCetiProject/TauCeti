/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import TauCeti.Topology.PiCurry
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-!
# Analytic regrouping of finite families

The regrouping homeomorphisms from `TauCeti.Topology.PiCurry` are coordinate projections and
finite products, so they and their inverses are analytic. These facts are kept here, beside the
homeomorphisms, so applications can reuse them without importing a root or polynomial development.
-/

public section

open Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] {m : ι → ℕ} {n : ℕ}

/-- Regrouping a finite family of tuples is analytic. -/
theorem analyticAt_piSigmaConstHomeomorph
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : ∀ i, Fin (m i) → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e) c := by
  refine AnalyticAt.pi fun j => ?_
  have hblock : AnalyticAt 𝕜 (fun p : (∀ i, Fin (m i) → 𝕜) => p (e.symm j).1) c :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun i => Fin (m i) → 𝕜)
      (e.symm j).1).analyticAt c
  have hcoord : AnalyticAt 𝕜
      (fun p : Fin (m (e.symm j).1) → 𝕜 => p (e.symm j).2)
      (c (e.symm j).1) :=
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin (m (e.symm j).1) => 𝕜)
      (e.symm j).2).analyticAt _
  convert hcoord.comp hblock using 1
  ext x
  exact piSigmaConstHomeomorph_apply 𝕜 e x j

/-- The inverse regrouping from one tuple to a finite family of tuples is analytic. -/
theorem analyticAt_piSigmaConstHomeomorph_symm
    (e : (Σ i, Fin (m i)) ≃ Fin n) (c : Fin n → 𝕜) :
    AnalyticAt 𝕜 (piSigmaConstHomeomorph 𝕜 e).symm c := by
  refine AnalyticAt.pi fun i => AnalyticAt.pi fun j => ?_
  convert (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin n => 𝕜)
    (e ⟨i, j⟩)).analyticAt c using 1
  ext x
  exact piSigmaConstHomeomorph_symm_apply 𝕜 e x i j

end TauCeti

end
