/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Cone

/-!
# Quasi-isomorphisms of periodic complexes

A morphism of cyclic cochain complexes is a quasi-isomorphism exactly when its mapping cone is
acyclic. This identifies the homology-based weak equivalences with the cone criterion used for
the Verdier quotient of the periodic homotopy category by acyclic complexes.

The proof compares the cone sequence of a morphism with the cone sequence of an identity. The
identity cone is contractible, and two-out-of-three in the resulting morphism of short exact
sequences detects the original morphism.

No positivity hypothesis on the period is needed; at period zero this applies to integer-indexed
cochain complexes.

## References

* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199--236, Section 3.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {n : ℕ}
  {X Y : CochainComplex C (ZMod n)}

private theorem coneSequence_shortExact (f : X ⟶ Y) : (coneSequence f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i ↦
    (coneSequenceSplitting f i).shortExact

private theorem homotopyCofiber_id_acyclic (X : CochainComplex C (ZMod n)) :
    (homotopyCofiber (𝟙 X)).Acyclic := by
  intro i
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  simpa only [homologyMap_id, homologyMap_zero] using
    (homotopyCofiber.homotopyToZeroOfId X (fun j ↦ ⟨j - 1, by simp⟩)).homologyMap_eq i

/-- A morphism of cyclic cochain complexes is a quasi-isomorphism if and only if its mapping
cone is acyclic. -/
theorem quasiIso_iff_acyclic_homotopyCofiber (f : X ⟶ Y) :
    QuasiIso f ↔ (homotopyCofiber f).Acyclic := by
  let α : Arrow.mk (𝟙 X) ⟶ Arrow.mk f := Arrow.homMk (𝟙 X) f (by simp)
  let coneMap := homotopyCofiber.mapArrowHom (𝟙 X) f
    (fun j ↦ ⟨j - 1, by simp⟩) α
  have hId : (homotopyCofiber (𝟙 X)).Acyclic := homotopyCofiber_id_acyclic X
  constructor
  · intro hf
    let _ : QuasiIso f := hf
    let _ : QuasiIso α.left := by
      -- The local arrow abbreviation hides that its left component is the identity.
      change QuasiIso (𝟙 X)
      infer_instance
    let _ : QuasiIso α.right := by
      -- The local arrow abbreviation similarly hides its right component from typeclass search.
      change QuasiIso f
      exact hf
    have hConeMap : QuasiIso coneMap :=
      homotopyCofiber.quasiIso_mapArrowHom (𝟙 X) f (fun j ↦ ⟨j - 1, by simp⟩) α
    intro i
    exact (exactAt_iff_of_quasiIsoAt coneMap i).mp (hId i)
  · intro hCone
    have hConeMap : QuasiIso coneMap := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt coneMap i (hId i)).mpr (hCone i)
    have hConeMap' : QuasiIso (coneSequenceMap (𝟙 X) f α).τ₂ := by
      simpa only [coneSequenceMap_τ₂] using hConeMap
    have hShiftId' : QuasiIso (coneSequenceMap (𝟙 X) f α).τ₃ := by
      rw [coneSequenceMap_τ₃]
      let _ : IsIso α.left := by
        -- Expose the identity component so its shifted image is recognized as an isomorphism.
        change IsIso (𝟙 X)
        infer_instance
      infer_instance
    have h := HomologySequence.quasiIso_τ₁
      (coneSequenceMap (𝟙 X) f α)
      (coneSequence_shortExact (𝟙 X)) (coneSequence_shortExact f) hConeMap' hShiftId'
    rw [coneSequenceMap_τ₁] at h
    exact h

end TauCeti.PeriodicComplex
