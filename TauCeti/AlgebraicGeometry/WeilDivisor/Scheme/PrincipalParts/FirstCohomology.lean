/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Cohomology

/-!
# First cohomology as principal parts modulo rational functions

For a Weil divisor `D` on an integral Noetherian scheme, suppose that the codimension-one points
are closed and their local rings are discrete valuation rings. The principal-parts resolution

`0 ⟶ 𝒪_X(D) ⟶ 𝒦_X ⟶ 𝒦_X / 𝒪_X(D) ⟶ 0`

is then short exact, and the rational-function sheaf `𝒦_X` is flasque. This file records the
resulting concrete description

`H¹(X, 𝒪_X(D)) ≃ Γ(X, 𝒦_X / 𝒪_X(D)) / im(Γ(X, 𝒦_X))`.

Unlike the general short-exact-sequence result
`Scheme.Modules.cohomologyOneLinearEquivOfIsFlasque`, the source here is expressed directly in
global rational functions and global principal parts. This is the form used to pair cohomology
classes with rational differentials by summing residues: a functional on principal parts descends
to first cohomology precisely when it vanishes on the image of every global rational function.

## Main declarations

* `SchemeWeilDivisor.globalToPrincipalPartsBaseLinear` sends a global rational function to its
  family of principal parts, as a map linear over the base ring;
* `SchemeWeilDivisor.principalPartsBoundary` is the connecting map from global principal parts to
  `H¹(X, 𝒪_X(D))`;
* `SchemeWeilDivisor.principalPartsQuotientEquivCohomologyOne` is the displayed linear
  equivalence.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5.
* R. Hartshorne, *Algebraic Geometry*, Chapter III, Proposition 2.5 and Section 7.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace SchemeWeilDivisor

variable (R : Type u) [CommRing R] {X : Scheme.{u}} [X.Over (Spec (.of R))]
  [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- The map from global rational functions to global principal parts of `D`, linear over the base
ring of the scheme.

It is the degree-zero cohomology map of `toPrincipalParts D`, transported through the canonical
identifications of zeroth cohomology with global sections. -/
def globalToPrincipalPartsBaseLinear (D : SchemeWeilDivisor X) :
    Γ(Scheme.rationalFunctions X, ⊤) →ₗ[R] Γ(principalParts D, ⊤) :=
  (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X (principalParts D)).toLinearMap.comp
    ((Scheme.Modules.cohomologyMapBaseLinear R X (toPrincipalParts D) 0).comp
      (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X
        (Scheme.rationalFunctions X)).symm.toLinearMap)

/-- `globalToPrincipalPartsBaseLinear` is the global-sections map induced by
`toPrincipalParts D`. -/
@[simp]
lemma globalToPrincipalPartsBaseLinear_apply (D : SchemeWeilDivisor X)
    (f : Γ(Scheme.rationalFunctions X, ⊤)) :
    globalToPrincipalPartsBaseLinear R D f =
      Scheme.Modules.Hom.app (toPrincipalParts D) ⊤ f := by
  let q := (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X
    (Scheme.rationalFunctions X)).symm f
  rw [globalToPrincipalPartsBaseLinear, LinearMap.comp_apply, LinearMap.comp_apply]
  calc
    (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X (principalParts D))
        (Scheme.Modules.cohomologyMapBaseLinear R X (toPrincipalParts D) 0 q) =
        Scheme.Modules.cohomologyZeroEquiv (principalParts D)
          (Scheme.Modules.cohomologyMapBaseLinear R X (toPrincipalParts D) 0 q) :=
      Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply R X (principalParts D) _
    _ = Scheme.Modules.Hom.app (toPrincipalParts D) ⊤
        (Scheme.Modules.cohomologyZeroEquiv (Scheme.rationalFunctions X) q) := by
      rw [Scheme.Modules.cohomologyMapBaseLinear_apply]
      exact Scheme.Modules.cohomologyZeroEquiv_naturality (toPrincipalParts D) q
    _ = Scheme.Modules.Hom.app (toPrincipalParts D) ⊤ f := by
      rw [← Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply R X
          (Scheme.rationalFunctions X),
        (Scheme.Modules.cohomologyZeroBaseLinearEquiv R X
          (Scheme.rationalFunctions X)).apply_symm_apply]

variable (hclosed : ∀ x : CodimensionOnePoint X, IsClosed ({(x : X)} : Set X))

private lemma principalPartsSequence_shortExact
    (hclosed : ∀ x : CodimensionOnePoint X, IsClosed ({(x : X)} : Set X))
    (D : SchemeWeilDivisor X) :
    (ShortComplex.mk (sheafι D) (toPrincipalParts D)
      (sheafι_toPrincipalParts D)).ShortExact := by
  simpa only [principalPartsShortComplex_eq] using
    principalPartsShortComplex_shortExact hclosed D

private def globalPrincipalPartsQuotientEquiv (D : SchemeWeilDivisor X) :
    (Γ(principalParts D, ⊤) ⧸ LinearMap.range (globalToPrincipalPartsBaseLinear R D)) ≃ₗ[R]
      (Scheme.Modules.Cohomology (principalParts D) 0 ⧸
        LinearMap.range (Scheme.Modules.cohomologyMapBaseLinear R X
          (toPrincipalParts D) 0)) := by
  let e₂ := Scheme.Modules.cohomologyZeroBaseLinearEquiv R X (Scheme.rationalFunctions X)
  let e₃ := Scheme.Modules.cohomologyZeroBaseLinearEquiv R X (principalParts D)
  refine Submodule.Quotient.equiv _ _ e₃.symm ?_
  rw [← LinearMap.range_comp]
  have hcomp : e₃.symm.toLinearMap.comp (globalToPrincipalPartsBaseLinear R D) =
      (Scheme.Modules.cohomologyMapBaseLinear R X (toPrincipalParts D) 0).comp
        e₂.symm.toLinearMap := by
    ext f
    simp only [LinearMap.comp_apply]
    apply e₃.injective
    calc
      e₃ (e₃.symm (globalToPrincipalPartsBaseLinear R D f)) =
          globalToPrincipalPartsBaseLinear R D f := e₃.apply_symm_apply _
      _ = Scheme.Modules.Hom.app (toPrincipalParts D) ⊤ f :=
        globalToPrincipalPartsBaseLinear_apply R D f
      _ = e₃ (Scheme.Modules.cohomologyMapBaseLinear R X
          (toPrincipalParts D) 0 (e₂.symm f)) := by
        let q := e₂.symm f
        have hq : Scheme.Modules.cohomologyZeroEquiv (Scheme.rationalFunctions X) q = f :=
          (Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply R X
            (Scheme.rationalFunctions X) q).symm.trans (e₂.apply_symm_apply f)
        calc
          Scheme.Modules.Hom.app (toPrincipalParts D) ⊤ f =
              Scheme.Modules.Hom.app (toPrincipalParts D) ⊤
                (Scheme.Modules.cohomologyZeroEquiv (Scheme.rationalFunctions X) q) :=
            congrArg _ hq.symm
          _ = Scheme.Modules.cohomologyZeroEquiv (principalParts D)
              (Scheme.Modules.cohomologyMap (toPrincipalParts D) 0 q) :=
            (Scheme.Modules.cohomologyZeroEquiv_cohomologyMap (toPrincipalParts D) q).symm
          _ = e₃ (Scheme.Modules.cohomologyMapBaseLinear R X
              (toPrincipalParts D) 0 q) := by
            have hmap : Scheme.Modules.cohomologyMapBaseLinear R X
                (toPrincipalParts D) 0 q =
                Scheme.Modules.cohomologyMap (toPrincipalParts D) 0 q := by
              rw [Scheme.Modules.cohomologyMapBaseLinear_apply,
                Scheme.Modules.cohomologyFunctor_map]
              rfl
            have hb := Scheme.Modules.cohomologyZeroBaseLinearEquiv_apply R X
              (principalParts D)
              (Scheme.Modules.cohomologyMapBaseLinear R X (toPrincipalParts D) 0 q)
            exact (congrArg (Scheme.Modules.cohomologyZeroEquiv (principalParts D))
              hmap.symm).trans (by simpa only [e₃] using hb.symm)
  rw [hcomp]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range e₂.symm)

/-- **First cohomology as principal parts modulo rational functions.** The first cohomology of
`𝒪_X(D)` is linearly equivalent to global principal parts modulo the principal parts of global
rational functions. -/
def principalPartsQuotientEquivCohomologyOne (D : SchemeWeilDivisor X) :
    (Γ(principalParts D, ⊤) ⧸ LinearMap.range (globalToPrincipalPartsBaseLinear R D)) ≃ₗ[R]
      Scheme.Modules.Cohomology (sheaf D) 1 :=
  (globalPrincipalPartsQuotientEquiv R D).trans
    (Scheme.Modules.cohomologyOneLinearEquivOfIsFlasque R
      (principalPartsSequence_shortExact hclosed D))

/-- The connecting map from global principal parts of `D` to `H¹(X, 𝒪_X(D))`.

It is surjective because the middle term `𝒦_X` of the principal-parts resolution is
flasque. Its kernel is the image of `globalToPrincipalPartsBaseLinear`. -/
def principalPartsBoundary (D : SchemeWeilDivisor X) :
    Γ(principalParts D, ⊤) →ₗ[R] Scheme.Modules.Cohomology (sheaf D) 1 :=
  (principalPartsQuotientEquivCohomologyOne R hclosed D).toLinearMap.comp
    (LinearMap.range (globalToPrincipalPartsBaseLinear R D)).mkQ

/-- The cohomology class of a family of principal parts is its image under the boundary map. -/
@[simp]
lemma principalPartsQuotientEquivCohomologyOne_mk (D : SchemeWeilDivisor X)
    (p : Γ(principalParts D, ⊤)) :
    principalPartsQuotientEquivCohomologyOne R hclosed D (Submodule.Quotient.mk p) =
      principalPartsBoundary R hclosed D p := by
  rfl

/-- Every first-cohomology class of `𝒪_X(D)` is represented by a global family of principal
parts. -/
lemma principalPartsBoundary_surjective (D : SchemeWeilDivisor X) :
    Function.Surjective (principalPartsBoundary R hclosed D) := by
  intro z
  obtain ⟨q, rfl⟩ := (principalPartsQuotientEquivCohomologyOne R hclosed D).surjective z
  obtain ⟨p, rfl⟩ := (LinearMap.range
    (globalToPrincipalPartsBaseLinear R D)).mkQ_surjective q
  exact ⟨p, principalPartsQuotientEquivCohomologyOne_mk R hclosed D p |>.symm⟩

/-- A family of global principal parts has zero boundary exactly when it is the family of
principal parts of a global rational function. -/
lemma principalPartsBoundary_eq_zero_iff (D : SchemeWeilDivisor X)
    (p : Γ(principalParts D, ⊤)) :
    principalPartsBoundary R hclosed D p = 0 ↔
      ∃ f : Γ(Scheme.rationalFunctions X, ⊤),
        globalToPrincipalPartsBaseLinear R D f = p := by
  let Q := LinearMap.range (globalToPrincipalPartsBaseLinear R D)
  let e := principalPartsQuotientEquivCohomologyOne R hclosed D
  constructor
  · intro hp
    have hq : Q.mkQ p = 0 := by
      rw [principalPartsBoundary, LinearMap.comp_apply] at hp
      apply e.injective
      exact hp.trans (map_zero e).symm
    apply LinearMap.mem_range.mp
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact hq
  · intro hp
    have hp' : p ∈ Q := LinearMap.mem_range.mpr hp
    have hq : (Submodule.Quotient.mk p : Γ(principalParts D, ⊤) ⧸ Q) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      exact hp'
    rw [principalPartsBoundary, LinearMap.comp_apply, Submodule.mkQ_apply, hq, map_zero]

/-- The kernel of the principal-parts boundary is the image of global rational functions. -/
lemma ker_principalPartsBoundary (D : SchemeWeilDivisor X) :
    LinearMap.ker (principalPartsBoundary R hclosed D) =
      LinearMap.range (globalToPrincipalPartsBaseLinear R D) := by
  apply le_antisymm
  · intro p hp
    rw [LinearMap.mem_ker] at hp
    rw [LinearMap.mem_range]
    exact (principalPartsBoundary_eq_zero_iff R hclosed D p).mp hp
  · intro p hp
    rw [LinearMap.mem_range] at hp
    rw [LinearMap.mem_ker]
    exact (principalPartsBoundary_eq_zero_iff R hclosed D p).mpr hp

end SchemeWeilDivisor

end

end AlgebraicGeometry

end TauCeti
