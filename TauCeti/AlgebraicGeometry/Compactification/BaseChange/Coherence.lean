/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Compactification.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.Compactification.Transport

/-!
# Identity and composition comparisons for base change of compactifications

Base change along the identity and successive base changes agree with the original
compactification and the composite base change, after transporting their sources along
the canonical pullback isomorphisms. The comparisons are natural in refinement maps.
Their ambient maps are Mathlib's pullback projections and pasting isomorphisms, so the
interior and the proper structure map are preserved, including nonreduced interiors.

## References

* The Stacks Project, Section 38.32, *Compactifications* (tag 0ATT).
* The comparisons use `CategoryTheory.Limits.pullbackLeftPullbackSndIso`.
-/

public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace TauCeti.Compactification

noncomputable section

variable {X S T U : Scheme.{u}} {f : X ⟶ S}

/-- Identity base change, with its source identified with the original source. -/
def baseChangeIdIso (C : Compactification f) :
    (C.baseChange (𝟙 S)).sourceIso (asIso (pullback.fst f (𝟙 S))).symm
      (by simp) ≅ C :=
  isoMk (asIso (pullback.fst C.p (𝟙 S)))
    (by simp [Category.assoc])
    (by simpa using (pullback.condition (f := C.p) (g := 𝟙 S)))

@[simp]
theorem baseChangeIdIso_hom_hom_h (C : Compactification f) :
    (baseChangeIdIso C).hom.hom.h = pullback.fst C.p (𝟙 S) := by
  simp [baseChangeIdIso]

@[simp]
theorem baseChangeIdIso_inv_hom_h (C : Compactification f) :
    (baseChangeIdIso C).inv.hom.h = inv (pullback.fst C.p (𝟙 S)) := by
  simp [baseChangeIdIso]

/-- The identity comparison is natural in all refinement maps, without density hypotheses. -/
def baseChangeIdNatIso :
    baseChangeFunctor (f := f) (𝟙 S) ⋙
      sourceIsoFunctor (asIso (pullback.fst f (𝟙 S))).symm (by simp) ≅
        𝟭 (Compactification f) :=
  NatIso.ofComponents (fun C ↦ by simpa using baseChangeIdIso C) (fun h ↦ by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    simp)

@[simp]
theorem baseChangeIdNatIso_hom_app (C : Compactification f) :
    (baseChangeIdNatIso (f := f)).hom.app C = (baseChangeIdIso C).hom := by
  simp [baseChangeIdNatIso]

@[simp]
theorem baseChangeIdNatIso_inv_app (C : Compactification f) :
    (baseChangeIdNatIso (f := f)).inv.app C = (baseChangeIdIso C).inv := by
  simp [baseChangeIdNatIso]

/-- Two successive base changes agree with the composite base change, with the source
transported by the canonical pullback-pasting isomorphism. -/
def baseChangeCompIso (C : Compactification f) (g : T ⟶ S) (h : U ⟶ T) :
    (C.baseChange g).baseChange h ≅
      (C.baseChange (h ≫ g)).sourceIso (pullbackLeftPullbackSndIso f g h) (by simp) :=
  isoMk (pullbackLeftPullbackSndIso C.p g h)
    (by
      -- Normalize dependent pullback endpoints before applying their projection equations.
      dsimp only [baseChange, sourceIso, ofHom, j, p, Xbar]
      apply pullback.hom_ext <;> simp [Category.assoc])
    (by
      dsimp only [baseChange, sourceIso, ofHom, p]
      simp)

@[simp]
theorem baseChangeCompIso_hom_hom_h (C : Compactification f) (g : T ⟶ S) (h : U ⟶ T) :
    (baseChangeCompIso C g h).hom.hom.h = (pullbackLeftPullbackSndIso C.p g h).hom := by
  simp [baseChangeCompIso]

@[simp]
theorem baseChangeCompIso_inv_hom_h (C : Compactification f) (g : T ⟶ S) (h : U ⟶ T) :
    (baseChangeCompIso C g h).inv.hom.h = (pullbackLeftPullbackSndIso C.p g h).inv := by
  simp [baseChangeCompIso]

/-- The composition comparison is natural in refinement maps. -/
def baseChangeCompNatIso (g : T ⟶ S) (h : U ⟶ T) :
    baseChangeFunctor (f := f) g ⋙ baseChangeFunctor h ≅
      baseChangeFunctor (h ≫ g) ⋙
        sourceIsoFunctor (pullbackLeftPullbackSndIso f g h) (by simp) :=
  NatIso.ofComponents (fun C ↦ by simpa using baseChangeCompIso C g h) (fun k ↦ by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    -- Iteration presents the same pullback endpoint through two compactification wrappers.
    dsimp only [Functor.comp_map, sourceIsoFunctor, baseChangeFunctor, baseChangeMap,
      baseChange, sourceIso, ofHom]
    apply pullback.hom_ext <;> simp [Category.assoc])

@[simp]
theorem baseChangeCompNatIso_hom_app (g : T ⟶ S) (h : U ⟶ T) (C : Compactification f) :
    (baseChangeCompNatIso (f := f) g h).hom.app C = (baseChangeCompIso C g h).hom := by
  simp [baseChangeCompNatIso]

@[simp]
theorem baseChangeCompNatIso_inv_app (g : T ⟶ S) (h : U ⟶ T) (C : Compactification f) :
    (baseChangeCompNatIso (f := f) g h).inv.app C = (baseChangeCompIso C g h).inv := by
  simp [baseChangeCompNatIso]

end

end TauCeti.Compactification
