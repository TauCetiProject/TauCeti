/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Finite étale covers of a punctured local spectrum

For a local ring, the punctured spectrum is the complement of the closed point. Pullback along
its inclusion restricts finite étale schemes. Purity of the local ring means that this functor is
essentially surjective.

## References

* The Stacks Project, Section 58.20 (Tag 0BM7).
* Ported from Taylor Dupuy, Thomas Tucker and Zhuoran Wang, pcfawd-formalization at commit
  `9a20b3f` (Apache 2.0), `Pcf/Stacks/Purity/PuncturedSpectrum.lean` and
  `Pcf/Stacks/Purity/Hartogs.lean`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Pullback of finite étale schemes along the punctured-spectrum inclusion. -/
noncomputable def restrictPunctured :
    TauCeti.FiniteEtaleScheme (Spec (.of R)) ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme :=
  (TauCeti.finiteEtaleSchemeProperty _).lift
    ((TauCeti.finiteEtaleSchemeProperty _).ι ⋙ Over.pullback (puncturedSpectrum R).ι)
    (fun X ↦ by
      rw [TauCeti.finiteEtaleSchemeProperty_iff]
      -- `Over.pullback` defines the over-object map as the second pullback projection,
      -- so `change` exposes exactly the map on which finiteness and étaleness are inferred.
      change IsFinite (Limits.pullback.snd X.obj.hom (puncturedSpectrum R).ι) ∧
        Etale (Limits.pullback.snd X.obj.hom (puncturedSpectrum R).ι)
      exact ⟨inferInstance, inferInstance⟩)

/-- Forgetting finite étaleness identifies restriction with pullback along the puncture. -/
@[simp]
theorem restrictPunctured_comp_ι :
    restrictPunctured R ⋙ (TauCeti.finiteEtaleSchemeProperty _).ι =
      (TauCeti.finiteEtaleSchemeProperty _).ι ⋙ Over.pullback (puncturedSpectrum R).ι :=
  by
    unfold restrictPunctured
    rfl

/-- Purity holds if every finite étale cover of the punctured spectrum extends across the
closed point. -/
@[stacks 0BM7 "definition of purity"]
def PurityHolds : Prop := (restrictPunctured R).EssSurj

/-- Purity is equivalent to the extension of every finite étale cover of the puncture. -/
theorem purityHolds_iff :
    PurityHolds R ↔
      ∀ cover : TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme,
        ∃ extension : TauCeti.FiniteEtaleScheme (Spec (.of R)),
          Nonempty ((restrictPunctured R).obj extension ≅ cover) := by
  constructor
  · intro h cover
    let : (restrictPunctured R).EssSurj := h
    exact Functor.EssSurj.mem_essImage (restrictPunctured R) cover
  · intro h
    exact ⟨h⟩

end IsLocalRing
