/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.Gluing.Double
import TauCeti.Geometry.Manifold.Gluing.OpenSubsets
import TauCeti.Geometry.Manifold.Gluing.Star
import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic

/-!
# Examples: complex manifolds from two-chart and finite-star gluings

The compatible-gluing theorem `TopCat.GlueData.IsCompatible.isManifold` makes two-chart and
finite-star gluings of open subsets of `ℂ` into complex analytic manifolds. These examples show
that open gluing produces non-Hausdorff complex manifolds and recovers the Riemann sphere:

* the plane with a doubled origin, the double `TauCeti.doubleGlueData ℂ U` with `U = {0}ᶜ`, is a
  complex analytic manifold whose two copies of `ℂ` include by local biholomorphisms, although it
  is not Hausdorff;
* gluing the two chart domains `OnePoint ℂ \ {∞}` and `OnePoint ℂ \ {0}` of the Riemann sphere
  along their intersection gives a complex analytic manifold biholomorphic to `OnePoint ℂ` by the
  canonical map;
* the finite star `TauCeti.starGlueData` with a hub `ℂ` and `n` arms `ℂ`, the arm `k` attached
  by the identity along the disc of radius `1` about `4 k`, is a complex analytic manifold whose
  hub and arms include by local biholomorphisms. Every arm meets the hub, and distinct arms do not
  meet: the overlap graph is a star.
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

-- The finite star with hub `ℂ` and `n` arms `ℂ`, the arm `k` attached by the identity along the
-- disc of radius `1` about `4 k`, is a complex analytic manifold.
example (n : ℕ) :
    letI := (starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).chartedSpace ℂ
    IsManifold 𝓘(ℂ) ω (starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).toGlueData.glued :=
  (isCompatible_starGlueData fun _ ↦ (Diffeomorph.refl 𝓘(ℂ) _ ω).isLocalDiffeomorph).isManifold

-- The hub and the arms include into the finite star by local biholomorphisms.
example (n : ℕ) (i : (starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).J) :
    letI := (starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).chartedSpace ℂ
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ((starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).toGlueData.ι i) :=
  (isCompatible_starGlueData fun _ ↦
    (Diffeomorph.refl 𝓘(ℂ) _ ω).isLocalDiffeomorph).isLocalDiffeomorph_ι i

-- Every arm of the finite star meets the hub.
example (n : ℕ) (k : Fin n) :
    Nonempty ((starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).V (none, some k)) := by
  rw [nonempty_starGlueData_V_iff (by simp)]
  exact ⟨4 * (k : ℕ), by simp⟩

-- Distinct arms of the finite star do not meet: their discs are disjoint.
example (n : ℕ) {k l : Fin n} (hkl : k ≠ l) :
    IsEmpty ((starGlueData (U := fun _ : Option (Fin n) ↦ ℂ)
      (W := fun i ↦ Option.elim i ⊤ fun k ↦ ⟨Metric.ball (4 * ((k : ℕ) : ℂ)) 1, Metric.isOpen_ball⟩)
      fun _ ↦ Homeomorph.refl _).V (some k, some l)) := by
  rw [← not_nonempty_iff, nonempty_starGlueData_V_iff (by simpa using hkl),
    not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty]
  refine Metric.ball_disjoint_ball ?_
  -- Distinct natural numbers are at distance at least `1`.
  have h : (1 : ℝ) ≤ ‖((((k : ℕ) : ℤ) - (l : ℕ) : ℤ) : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs (sub_ne_zero.2 (Int.ofNat_inj.not.2 (Fin.val_ne_of_ne hkl)))
  push_cast at h
  simp [dist_eq_norm, ← mul_sub]
  linarith
