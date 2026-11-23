/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Clopen
public import TauCeti.AlgebraicGeometry.Scheme.Connected.Component

/-!
# Cohomology on connected components

On a locally connected scheme with finitely many connected components, those components form a
finite clopen partition. In particular this applies to every Noetherian scheme. The comparison
below expresses cohomology as the product of cohomology on those component schemes, naturally in
the coefficients and linearly over the base ring. It also records the sum of the component
cohomology dimensions and truncated Euler characteristics.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open TauCeti TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} [LocallyConnectedSpace X] [Finite (ConnectedComponents X)]

/-- Cohomology of a finite clopen component partition is the finite product of the cohomologies
of the restrictions to its connected components, linearly over every base ring. -/
def TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyConnectedComponentsLinearEquiv
    (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (M : X.Modules) (n : ℕ) :
    Cohomology M n ≃ₗ[R] ∀ C : ConnectedComponents X,
      Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n := by
  let := Fintype.ofFinite (ConnectedComponents X)
  exact cohomologyClopenCoverLinearEquiv ConnectedComponents.opens R
    ConnectedComponents.iSup_opens ConnectedComponents.pairwise_disjoint_opens M n

/-- The component comparison evaluates by the cohomology of the restriction unit and the
closed-immersion comparison for the component inclusion. -/
@[simp]
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyConnectedComponentsLinearEquiv_apply
    (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (M : X.Modules) (n : ℕ) (x : Cohomology M n)
    (C : ConnectedComponents X) :
    cohomologyConnectedComponentsLinearEquiv R M n x C =
      (Scheme.Opens.ι C.opens).cohomologyPushforwardBaseLinearEquiv R
        ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n
        (cohomologyMapBaseLinear R X
          ((restrictAdjunction (Scheme.Opens.ι C.opens)).unit.app M) n x) := by
  let := Fintype.ofFinite (ConnectedComponents X)
  exact cohomologyClopenCoverLinearEquiv_apply ConnectedComponents.opens R
    ConnectedComponents.iSup_opens ConnectedComponents.pairwise_disjoint_opens M n x C

/-- The component comparison commutes with arbitrary coefficient maps. -/
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyConnectedComponentsLinearEquiv_naturality
    (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] {M N : X.Modules} (f : M ⟶ N) (n : ℕ)
    (x : Cohomology M n) (C : ConnectedComponents X) :
    cohomologyConnectedComponentsLinearEquiv R N n (cohomologyMapBaseLinear R X f n x) C =
      cohomologyMapBaseLinear R (Scheme.Opens.toScheme C.opens)
        ((restrictFunctor (Scheme.Opens.ι C.opens)).map f) n
        (cohomologyConnectedComponentsLinearEquiv R M n x C) := by
  let := Fintype.ofFinite (ConnectedComponents X)
  exact cohomologyClopenCoverLinearEquiv_naturality ConnectedComponents.opens R
    ConnectedComponents.iSup_opens ConnectedComponents.pairwise_disjoint_opens f n x C

omit [Finite (ConnectedComponents X)] in
/-- When the component cohomologies are finite-dimensional, their dimensions sum to the
cohomology dimension of the whole scheme. -/
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.finrank_cohomology_eq_sum_connectedComponents
    (k : Type u) [Field k]
    [X.Over (Spec (.of k))] (M : X.Modules) (n : ℕ)
    [Fintype (ConnectedComponents X)] [∀ C : ConnectedComponents X, FiniteDimensional k
      (Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n)] :
    Module.finrank k (Cohomology M n) =
      ∑ C : ConnectedComponents X,
        Module.finrank k (Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n) :=
  finrank_cohomology_eq_sum_clopenCover ConnectedComponents.opens k
    ConnectedComponents.iSup_opens ConnectedComponents.pairwise_disjoint_opens M n

omit [Finite (ConnectedComponents X)] in
/-- Truncated Euler characteristic is the sum of the component truncated Euler
characteristics when all component cohomologies below the truncation are finite-dimensional. -/
theorem TauCeti.AlgebraicGeometry.Scheme.Modules.eulerCharBelow_eq_sum_connectedComponents
    (k : Type u) [Field k]
    [X.Over (Spec (.of k))] [Fintype (ConnectedComponents X)] (M : X.Modules) (n : ℕ)
    (hfin : ∀ i < n, ∀ C : ConnectedComponents X, FiniteDimensional k
      (Cohomology ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) i)) :
    eulerCharBelow k X M n = ∑ C : ConnectedComponents X,
      eulerCharBelow k (Scheme.Opens.toScheme C.opens)
        ((restrictFunctor (Scheme.Opens.ι C.opens)).obj M) n :=
  eulerCharBelow_eq_sum_clopenCover ConnectedComponents.opens k
    ConnectedComponents.iSup_opens ConnectedComponents.pairwise_disjoint_opens M n hfin
