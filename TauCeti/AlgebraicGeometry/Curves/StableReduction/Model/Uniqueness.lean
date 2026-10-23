/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Fibers.SchematicDensity

/-!
# Uniqueness of morphisms to separated models

Between two models with a fixed generic-fibre identification, there is at most one morphism
if the target is separated over the DVR. In particular an isomorphism extending that
identification, when it exists, is unique. This does not assert existence of an extension.

Flatness makes the generic fibre schematically dense, so the total spaces need not be reduced.
Proper models are separated and hence satisfy the uniqueness statement. This is the separatedness
argument for morphisms of models in Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Chapter 10.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.Model

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}
variable {M N : Model R K C toK}

attribute [instance] Model.flat

/-- Morphisms between models with a fixed generic-fibre identification are unique when the
target is separated over the DVR. No properness or reducedness assumption on the source is needed.
-/
instance subsingleton_hom [IsSeparated N.toBase] : Subsingleton (M ⟶ N) where
  allEq f g := by
    apply Hom.ext
    apply ext_of_genericFiberι_eq R K (IsFractionRing.injective R K) M.toBase N.toBase
    · simp
    · rw [← cancel_epi M.genericFiberIso.inv.left]
      simpa only [genericι_def, Category.assoc] using (genericι_hom f).trans (genericι_hom g).symm

/-- There is at most one isomorphism of models extending their fixed generic-fibre
identification when the target is separated. Existence is a separate assertion. -/
instance subsingleton_iso [IsSeparated N.toBase] : Subsingleton (M ≅ N) where
  allEq e e' := Iso.ext (Subsingleton.elim e.hom e'.hom)

end TauCeti.Model
