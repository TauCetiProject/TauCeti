/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.Gluing.OpenSubsets
import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Examples: complex manifolds from two-chart gluings

The compatible-gluing theorem `TopCat.GlueData.IsCompatible.isManifold` makes two-chart gluings
of open subsets of `ℂ` into complex analytic manifolds. These examples show that open gluing
produces non-Hausdorff complex manifolds and recovers the Riemann sphere:

* the plane with a doubled origin, the double `TauCeti.doubleGlueData ℂ U` with `U = {0}ᶜ`, is a
  complex analytic manifold whose two copies of `ℂ` include by local biholomorphisms, although it
  is not Hausdorff;
* gluing the two chart domains `OnePoint ℂ \ {∞}` and `OnePoint ℂ \ {0}` of the Riemann sphere
  along their intersection gives a complex analytic manifold biholomorphic to `OnePoint ℂ` by the
  canonical map.
-/

open Set Topology TopologicalSpace TauCeti TopCat.GlueData
open scoped Manifold ContDiff OnePoint

-- The plane with a doubled origin is a complex analytic manifold.
example :
    letI := (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartedSpace ℂ
    IsManifold 𝓘(ℂ) ω (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued :=
  (isCompatible_doubleGlueData _).isManifold

-- Both copies of `ℂ` include into the plane with a doubled origin by local biholomorphisms.
example (i : (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).J) :
    letI := (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartedSpace ℂ
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω
      ((doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι i) :=
  (isCompatible_doubleGlueData _).isLocalDiffeomorph_ι i

-- A function on the plane with a doubled origin is holomorphic exactly when it is holomorphic on
-- both copies of `ℂ`.
example (g : (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued → ℂ) :
    letI := (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).chartedSpace ℂ
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g ↔ ∀ i, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (g ∘ (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.ι i) :=
  (isCompatible_doubleGlueData _).contMDiff_iff le_rfl

-- The plane with a doubled origin is nevertheless not Hausdorff.
example : ¬ T2Space (doubleGlueData ℂ ⟨{0}ᶜ, isOpen_compl_singleton⟩).toGlueData.glued := by
  simpa [t2Space_doubleGlueData_iff] using fun _ ↦ not_isOpen_singleton (0 : ℂ)

-- Gluing the two chart domains `OnePoint ℂ \ {∞}` and `OnePoint ℂ \ {0}` of the Riemann sphere
-- gives a complex analytic manifold.
example :
    letI := (ofOpenSubsets fun i : Bool ↦ (⟨{(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ,
      isOpen_compl_singleton⟩ : Opens (OnePoint ℂ))).chartedSpace ℂ
    IsManifold 𝓘(ℂ) ω (ofOpenSubsets fun i : Bool ↦ (⟨{(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ,
      isOpen_compl_singleton⟩ : Opens (OnePoint ℂ))).toGlueData.glued :=
  (isCompatible_ofOpenSubsets _).isManifold

-- It is biholomorphic to the Riemann sphere by the canonical map.
example :
    letI := (ofOpenSubsets fun i : Bool ↦ (⟨{(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ,
      isOpen_compl_singleton⟩ : Opens (OnePoint ℂ))).chartedSpace ℂ
    ∃ Φ : (ofOpenSubsets fun i : Bool ↦ (⟨{(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ,
        isOpen_compl_singleton⟩ : Opens (OnePoint ℂ))).toGlueData.glued ≃ₘ^ω⟮𝓘(ℂ), 𝓘(ℂ)⟯
      OnePoint ℂ, ⇑Φ = fromOpenSubsetsGlue fun i : Bool ↦
        (⟨{(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ, isOpen_compl_singleton⟩ :
          Opens (OnePoint ℂ)) :=
  have h : ⋃ i : Bool, {(if i then (0 : ℂ) else ∞ : OnePoint ℂ)}ᶜ = univ := by
    refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : x = (∞ : OnePoint ℂ)
    · exact ⟨true, by simp [hx]⟩
    · exact ⟨false, by simpa using hx⟩
  ⟨openCoverGlueDiffeomorph _ h, coe_openCoverGlueDiffeomorph _ h⟩
