/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.ConnectedComponents.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Restriction

/-!
# Relative-differential cohomology on connected components

Relative differentials commute with restriction to each open connected component. On a locally
connected scheme with finitely many components, their cohomology is therefore the product of the
relative-differential cohomologies of the component schemes, linearly over the base ring. This
allows componentwise linear forms, such as traces, to be summed.
-/

public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} [LocallyConnectedSpace X] [Finite (ConnectedComponents X)]

/-- Relative-differential cohomology decomposes into the cohomologies of the relative
differentials of the connected component schemes, over the same base ring. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyDifferentialsConnectedComponentsLinearEquiv
    (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (n : ℕ) :
    Cohomology (X.relativeDifferentials R) n ≃ₗ[R] ∀ C : ConnectedComponents X,
      Cohomology ((Scheme.Opens.toScheme C.opens).relativeDifferentials R) n :=
  (cohomologyConnectedComponentsLinearEquiv R (X.relativeDifferentials R) n).trans
    (LinearEquiv.piCongrRight fun C ↦
      cohomologyBaseLinearEquivOfIso R (relativeDifferentialsRestrictIso R
        (Scheme.Opens.ι C.opens)) n)

/-- The differential component comparison first restricts the cohomology class, then uses the
canonical restriction isomorphism for relative differentials over the same base. -/
@[simp]
theorem
TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyDifferentialsConnectedComponentsLinearEquiv_apply
    (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (n : ℕ) (x : Cohomology (X.relativeDifferentials R) n)
    (C : ConnectedComponents X) :
    cohomologyDifferentialsConnectedComponentsLinearEquiv R n x C =
      cohomologyBaseLinearEquivOfIso R
        (relativeDifferentialsRestrictIso R (Scheme.Opens.ι C.opens)) n
        (cohomologyConnectedComponentsLinearEquiv R (X.relativeDifferentials R) n x C) := by
  simp only [cohomologyDifferentialsConnectedComponentsLinearEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
