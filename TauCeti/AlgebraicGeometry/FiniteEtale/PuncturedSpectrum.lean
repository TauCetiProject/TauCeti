/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Fiber
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

/-- Pullback of finite étale schemes along the punctured-spectrum inclusion. Its underlying
functor is `Over.pullback` by `TauCeti.FiniteEtaleScheme.pullback_comp_ι`. -/
noncomputable abbrev restrictPunctured :
    TauCeti.FiniteEtaleScheme (Spec (.of R)) ⥤
      TauCeti.FiniteEtaleScheme (puncturedSpectrum R).toScheme :=
  TauCeti.FiniteEtaleScheme.pullback (puncturedSpectrum R).ι

/-- Purity holds if every finite étale cover of the punctured spectrum extends across the
closed point. -/
@[stacks 0BM7 "definition of purity"]
def PurityHolds : Prop := (restrictPunctured R).EssSurj

/-- Purity is, by definition, essential surjectivity of the restriction functor. -/
theorem purityHolds_iff_essSurj : PurityHolds R ↔ (restrictPunctured R).EssSurj :=
  Iff.rfl

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
