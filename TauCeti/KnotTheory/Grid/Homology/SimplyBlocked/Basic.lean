/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.KnotTheory.Grid.Chain.Complex
public import TauCeti.KnotTheory.Grid.Diagram.Components
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars
import TauCeti.Algebra.Homology.SquareZero

/-!
# Simply blocked grid homology

This file defines the simply blocked grid homology of a knot grid as the homology of the
one-variable specialization of its unblocked grid complex.  Concretely, after choosing an
`O`-marking in column `i` to block, the coefficient ring is the polynomial ring in the remaining
columns and the differential counts empty rectangles avoiding all `X`-markings and the blocked
`O`-marking.

The public cycle-class API presents Mathlib's categorical homology as the explicit quotient of
the kernel of the differential by its image.  Every homology class has a cycle representative,
and two representatives determine the same class exactly when their difference is a boundary.
An explicit semilinear chain map intertwining the specialized differentials induces
maps on cycles and homology, with a cycle-class equation. This descent
is available for arbitrary grid diagrams, including diagrams of different sizes.

For a multi-component link, the standard simply blocked theory blocks one `O`-marking on every
component.  The construction here is therefore named simply blocked homology only under the
`GridDiagram.IsKnot` hypothesis; the underlying one-variable specialization remains available for
every grid diagram as `GridDiagram.simplyBlockedComplex`.

## Main definitions

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyClass`: the cycle-class map of the
  one-variable specialization for arbitrary grids.
* `TauCeti.GridDiagram.oneVariableSpecializationCyclesMapOfIntertwining` and
  `TauCeti.GridDiagram.oneVariableSpecializationHomologyMapOfIntertwining`: descent of an
  intertwining semilinear map on explicit chains.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomology`: the simply blocked homology `G-hat`.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedCycles`: its cycles as a kernel.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyQuotient`: the concrete cycles-modulo-boundaries
  model.
* `TauCeti.GridDiagram.IsKnot.simplyBlockedHomologyIsoQuotient`: its canonical identification with
  Mathlib's categorical homology.

## Main results

* `TauCeti.GridDiagram.oneVariableSpecializationHomologyClass_surjective`: every class has a cycle
  representative.
* `TauCeti.GridDiagram.oneVariableSpecializationHomologyClass_eq_iff`: two cycles represent the same
  class exactly when their difference is in the range of the differential.
* `TauCeti.GridDiagram.oneVariableSpecializationHomologyClass_eq_zero_iff`: a cycle represents zero
  exactly when it is a boundary.
* `TauCeti.GridDiagram.mem_ker_simplyBlockedComplex_d_iff` and
  `TauCeti.GridDiagram.mem_range_moduleCatToCycles_simplyBlockedComplex_iff`: under
  `simplyBlockedChainEquiv`, the cycles and boundaries of `simplyBlockedComplex` are the kernel and
  range of `simplyBlockedDifferential`.

## References

The construction and coefficient convention follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Section 4.6.
-/

public section

open CategoryTheory

namespace TauCeti.GridDiagram

variable {n : ℕ} (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2]

/-- The cycle-class map of the one-variable specialization `V_i = 0` for an arbitrary grid.
For links this need not be the simply blocked theory, which blocks one marking per component. -/
noncomputable abbrev oneVariableSpecializationHomologyClass (i : Fin n) :
    LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom
      →ₗ[MvPolynomial {c : Fin n // c ≠ i} R] (G.simplyBlockedComplex R i).homology () :=
  (G.simplyBlockedComplex R i).moduleCatKerHomologyClass rfl

/-- The class of a cycle `c` is the image of its quotient class `Submodule.Quotient.mk c`
under the inverses of `moduleCatHomologyIso` and `homologyIsoSc'`. -/
theorem oneVariableSpecializationHomologyClass_apply (i : Fin n)
    (c : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.oneVariableSpecializationHomologyClass R i c =
      ((G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl).inv
        (((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso.inv
          (Submodule.Quotient.mk c)) := by
  let K := G.simplyBlockedComplex R i
  let y : K.cycles () := (K.sc ()).moduleCatCyclesIso.inv c
  have hy : K.moduleCatCyclesToKer () () y = c := by
    apply Subtype.ext
    rw [K.coe_moduleCatCyclesToKer]
    exact (K.sc ()).moduleCatCyclesIso_inv_iCycles_apply c
  have hc := K.moduleCatKerHomologyClass_moduleCatCyclesToKer rfl y
  rw [hy] at hc
  rw [hc]
  have h := congrArg (fun f => f c) (K.sc ()).moduleCatCyclesIso_inv_π
  -- Pin the opaque grid complex to `K` so `homologyIsoSc'_eq_refl` matches its selected carrier.
  change K.homologyπ () y = (K.homologyIsoSc' () () () rfl rfl).inv
    ((K.sc ()).moduleCatHomologyIso.inv (Submodule.Quotient.mk c))
  rw [K.homologyIsoSc'_eq_refl ()]
  exact h

/-- Every homology class of the one-variable specialization has a cycle representative. -/
theorem oneVariableSpecializationHomologyClass_surjective (i : Fin n) :
    Function.Surjective (G.oneVariableSpecializationHomologyClass R i) := by
  intro x
  obtain ⟨y, rfl⟩ := (G.simplyBlockedComplex R i).moduleCat_homologyπ_surjective () x
  exact ⟨(G.simplyBlockedComplex R i).moduleCatCyclesToKer () () y,
    (G.simplyBlockedComplex R i).moduleCatKerHomologyClass_moduleCatCyclesToKer rfl y⟩

/-- Two cycles of the one-variable specialization represent the same homology class exactly
when their difference is a boundary. -/
theorem oneVariableSpecializationHomologyClass_eq_iff (i : Fin n)
    (c c' : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.oneVariableSpecializationHomologyClass R i c =
        G.oneVariableSpecializationHomologyClass R i c' ↔
      c - c' ∈ LinearMap.range
        ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles := by
  rw [G.oneVariableSpecializationHomologyClass_apply,
    G.oneVariableSpecializationHomologyClass_apply]
  exact ((ModuleCat.mono_iff_injective
      ((G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl).inv).1
        inferInstance).eq_iff.trans
    (((ModuleCat.mono_iff_injective
      ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso.inv).1
        inferInstance).eq_iff.trans (Submodule.Quotient.eq _))

/-- A cycle of the one-variable specialization represents zero exactly when it is a boundary. -/
@[simp]
theorem oneVariableSpecializationHomologyClass_eq_zero_iff (i : Fin n)
    (c : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    G.oneVariableSpecializationHomologyClass R i c = 0 ↔
      c ∈ LinearMap.range
        ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles := by
  simpa only [map_zero, sub_zero] using
    G.oneVariableSpecializationHomologyClass_eq_iff R i c 0

/-- The kernel of the one-variable specialization's cycle-class map is its boundary submodule. -/
@[simp]
theorem ker_oneVariableSpecializationHomologyClass (i : Fin n) :
    LinearMap.ker (G.oneVariableSpecializationHomologyClass R i) =
      LinearMap.range ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles := by
  ext c
  rw [LinearMap.mem_ker, G.oneVariableSpecializationHomologyClass_eq_zero_iff]

/-- Under the explicit chain identification, a cycle of the one-variable specialization is a chain
in the kernel of `simplyBlockedDifferential`. -/
theorem mem_ker_simplyBlockedComplex_d_iff (i : Fin n)
    (c : (G.simplyBlockedComplex R i).X ()) :
    c ∈ LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom ↔
      G.simplyBlockedDifferential R i (G.simplyBlockedChainEquiv R i c) = 0 := by
  rw [LinearMap.mem_ker, ← (G.simplyBlockedChainEquiv R i).injective.eq_iff, map_zero,
    G.simplyBlockedChainEquiv_d]

/-- Under the explicit chain identification, a cycle of the one-variable specialization lies in the
boundary submodule `range moduleCatToCycles` precisely when its underlying chain lies in the range
of `simplyBlockedDifferential`. -/
theorem mem_range_moduleCatToCycles_simplyBlockedComplex_iff (i : Fin n)
    (c : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    c ∈ LinearMap.range ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles ↔
      G.simplyBlockedChainEquiv R i c ∈ LinearMap.range (G.simplyBlockedDifferential R i) := by
  -- The boundary map is `ShortComplex.moduleCatToCycles`, the differential with its codomain
  -- restricted to the cycles, so its underlying chain is the differential by definition.
  have hd (w : (G.simplyBlockedComplex R i).X ()) :
      G.simplyBlockedChainEquiv R i
          (((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles w).1 =
        G.simplyBlockedDifferential R i (G.simplyBlockedChainEquiv R i w) :=
    G.simplyBlockedChainEquiv_d R i w
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨G.simplyBlockedChainEquiv R i w, (hd w).symm⟩
  · rintro ⟨w, hw⟩
    refine ⟨(G.simplyBlockedChainEquiv R i).symm w, Subtype.ext ?_⟩
    apply (G.simplyBlockedChainEquiv R i).injective
    rw [hd, LinearEquiv.apply_symm_apply, hw]

/-- The categorical homology isomorphism to the concrete quotient, used for descent. -/
private noncomputable def oneVariableSpecializationHomologyIsoQuotient (G : GridDiagram n)
    (R : Type*) [CommRing R] [CharP R 2] (i : Fin n) :
    (G.simplyBlockedComplex R i).homology () ≅
      ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R)
        (LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom ⧸
          LinearMap.range ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles) :=
  (G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl ≪≫
    ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso

private theorem oneVariableSpecializationHomologyIsoQuotient_hom_class
    (G : GridDiagram n) (R : Type*) [CommRing R] [CharP R 2] (i : Fin n)
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    (oneVariableSpecializationHomologyIsoQuotient G R i).hom
        (G.oneVariableSpecializationHomologyClass R i z) = Submodule.Quotient.mk z := by
  rw [G.oneVariableSpecializationHomologyClass_apply]
  -- Expose the composite isomorphism so the inverse laws match the selected module carriers.
  change ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso.hom
      (((G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl).hom
        (((G.simplyBlockedComplex R i).homologyIsoSc' () () () rfl rfl).inv
          (((G.simplyBlockedComplex R i).sc' () () ()).moduleCatHomologyIso.inv
            (Submodule.Quotient.mk z)))) = _
  rw [ModuleCat.hom_inv_apply]
  exact ModuleCat.hom_inv_apply _ _

section Intertwining

variable {n m : ℕ} {G : GridDiagram n} {H : GridDiagram m}
  (R : Type*) [CommRing R] [CharP R 2] (i : Fin n) (j : Fin m)
  (σ : MvPolynomial {c : Fin n // c ≠ i} R →+*
    MvPolynomial {c : Fin m // c ≠ j} R)
  (f : GridChainHat R n i →ₛₗ[σ] GridChainHat R m j)
  (h : ∀ z, f (G.simplyBlockedDifferential R i z) =
    H.simplyBlockedDifferential R j (f z))

/-- Transport an explicit chain map to the categorical chain carriers. -/
private noncomputable def oneVariableSpecializationChainMapOfIntertwining :
    (G.simplyBlockedComplex R i).X () →ₛₗ[σ]
      (H.simplyBlockedComplex R j).X () :=
  (H.simplyBlockedChainEquiv R j).symm.toLinearMap.comp
    (f.comp (G.simplyBlockedChainEquiv R i).toLinearMap)

include h in
private theorem oneVariableSpecializationChainMapOfIntertwining_d
    (z : (G.simplyBlockedComplex R i).X ()) :
    oneVariableSpecializationChainMapOfIntertwining R i j σ f
        ((G.simplyBlockedComplex R i).d () () z) =
      (H.simplyBlockedComplex R j).d () ()
        (oneVariableSpecializationChainMapOfIntertwining R i j σ f z) := by
  apply (H.simplyBlockedChainEquiv R j).injective
  simp only [oneVariableSpecializationChainMapOfIntertwining, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, simplyBlockedChainEquiv_d]
  exact h _

/-- An intertwining semilinear map of explicit one-variable chains restricts to cycles.
The diagrams may have different sizes and need not be knots. -/
noncomputable def oneVariableSpecializationCyclesMapOfIntertwining :
    LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom →ₛₗ[σ]
      LinearMap.ker ((H.simplyBlockedComplex R j).d () ()).hom :=
  (oneVariableSpecializationChainMapOfIntertwining R i j σ f).restrict fun z hz => by
    rw [LinearMap.mem_ker] at hz ⊢
    rw [← oneVariableSpecializationChainMapOfIntertwining_d R i j σ f h, hz, map_zero]

/-- Under the explicit chain identifications, the induced map on cycles is the given chain map. -/
@[simp]
theorem simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    H.simplyBlockedChainEquiv R j
        (oneVariableSpecializationCyclesMapOfIntertwining R i j σ f h z) =
      f (G.simplyBlockedChainEquiv R i z) := by
  simp only [oneVariableSpecializationCyclesMapOfIntertwining, LinearMap.coe_restrict_apply,
    oneVariableSpecializationChainMapOfIntertwining, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]

private theorem oneVariableSpecializationCyclesMapOfIntertwining_mem_boundariesInKer
    {z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom}
    (hz : z ∈ ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer) :
    oneVariableSpecializationCyclesMapOfIntertwining R i j σ f h z ∈
      ((H.simplyBlockedComplex R j).d () ()).hom.boundariesInKer := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨oneVariableSpecializationChainMapOfIntertwining R i j σ f w, ?_⟩
  simp only [Submodule.subtype_apply, oneVariableSpecializationCyclesMapOfIntertwining,
    LinearMap.coe_restrict_apply] at hw ⊢
  rw [← hw, oneVariableSpecializationChainMapOfIntertwining_d R i j σ f h]

/-- An intertwining semilinear chain map descends to the homology of the one-variable
specialization. Its value on cycle classes is specified by the induced cycle map. -/
noncomputable def oneVariableSpecializationHomologyMapOfIntertwining :
    (G.simplyBlockedComplex R i).homology () →ₛₗ[σ]
      (H.simplyBlockedComplex R j).homology () :=
  (H.simplyBlockedComplex R j).moduleCatHomologyIso.toLinearEquiv.symm.toLinearMap.comp
    ((Submodule.mapQ
      ((G.simplyBlockedComplex R i).d () ()).hom.boundariesInKer
      ((H.simplyBlockedComplex R j).d () ()).hom.boundariesInKer
      (oneVariableSpecializationCyclesMapOfIntertwining R i j σ f h)
      (fun _ hz =>
        oneVariableSpecializationCyclesMapOfIntertwining_mem_boundariesInKer R i j σ f h hz)).comp
          (G.simplyBlockedComplex R i).moduleCatHomologyIso.toLinearEquiv.toLinearMap)

/-- The descended homology map sends a cycle class to the class of its cycle image. -/
@[simp]
theorem oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass
    (z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) :
    oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h
        (G.oneVariableSpecializationHomologyClass R i z) =
      H.oneVariableSpecializationHomologyClass R j
        (oneVariableSpecializationCyclesMapOfIntertwining R i j σ f h z) := by
  simp only [oneVariableSpecializationHomologyMapOfIntertwining, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    HomologicalComplex.moduleCatHomologyIso_hom_moduleCatKerHomologyClass,
    LinearMap.homologyπ_apply, LinearMap.homologyπ_apply, Submodule.mapQ_apply]

/-- A chain map induces a bijection on homology if it detects boundaries among cycles and every
cycle in the target differs from the image of a cycle by a boundary. -/
theorem oneVariableSpecializationHomologyMapOfIntertwining_bijective
    (hinj : ∀ {x}, G.simplyBlockedDifferential R i x = 0 →
      f x ∈ LinearMap.range (H.simplyBlockedDifferential R j) →
      x ∈ LinearMap.range (G.simplyBlockedDifferential R i))
    (hsurj : ∀ {y}, H.simplyBlockedDifferential R j y = 0 →
      ∃ x, G.simplyBlockedDifferential R i x = 0 ∧
        y - f x ∈ LinearMap.range (H.simplyBlockedDifferential R j)) :
    Function.Bijective (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) := by
  refine ⟨(injective_iff_map_eq_zero _).mpr fun y hy => ?_, fun y => ?_⟩
  · obtain ⟨z, rfl⟩ := G.oneVariableSpecializationHomologyClass_surjective R i y
    rw [oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff,
      simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining] at hy
    rw [oneVariableSpecializationHomologyClass_eq_zero_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff]
    exact hinj ((G.mem_ker_simplyBlockedComplex_d_iff R i z.1).mp z.2) hy
  · obtain ⟨y, rfl⟩ := H.oneVariableSpecializationHomologyClass_surjective R j y
    obtain ⟨x, hx, hxy⟩ := hsurj ((H.mem_ker_simplyBlockedComplex_d_iff R j y.1).mp y.2)
    let z : LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom :=
      ⟨(G.simplyBlockedChainEquiv R i).symm x, by
        rw [mem_ker_simplyBlockedComplex_d_iff, LinearEquiv.apply_symm_apply]
        exact hx⟩
    refine ⟨G.oneVariableSpecializationHomologyClass R i z, ?_⟩
    rw [oneVariableSpecializationHomologyMapOfIntertwining_oneVariableSpecializationHomologyClass,
      oneVariableSpecializationHomologyClass_eq_iff,
      mem_range_moduleCatToCycles_simplyBlockedComplex_iff, Submodule.coe_sub, map_sub,
      simplyBlockedChainEquiv_oneVariableSpecializationCyclesMapOfIntertwining,
      LinearEquiv.apply_symm_apply, ← neg_sub]
    exact neg_mem hxy

/-- A bijective descended homology map is linear over the ground ring when the coefficient
homomorphism preserves constants. -/
noncomputable def oneVariableSpecializationHomologyLinearEquivOfIntertwining
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r)
    (hf : Function.Bijective (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h)) :
    (ModuleCat.restrictScalars (MvPolynomial.C : R →+* _)).obj
        ((G.simplyBlockedComplex R i).homology ()) ≃ₗ[R]
      (ModuleCat.restrictScalars (MvPolynomial.C : R →+* _)).obj
        ((H.simplyBlockedComplex R j).homology ()) :=
  LinearEquiv.ofBijective
    (ModuleCat.restrictScalarsLinearMap
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
      (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
      (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) hσ)
    (by
      constructor
      · intro x y hxy
        exact hf.1 ((ModuleCat.restrictScalarsLinearMap_apply
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
          (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) hσ x).symm.trans
          (hxy.trans (ModuleCat.restrictScalarsLinearMap_apply
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
          (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) hσ y)))
      · intro y
        obtain ⟨x, hx⟩ := hf.2 y
        exact ⟨x, (ModuleCat.restrictScalarsLinearMap_apply
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
          (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
          (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) hσ x).trans hx⟩)

/-- The coefficient-linear packaging preserves the descended homology map. -/
theorem oneVariableSpecializationHomologyLinearEquivOfIntertwining_apply
    (hσ : ∀ r, σ (MvPolynomial.C r) = MvPolynomial.C r)
    (hf : Function.Bijective (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h))
    (y : (ModuleCat.restrictScalars (MvPolynomial.C : R →+* _)).obj
      ((G.simplyBlockedComplex R i).homology ())) :
    oneVariableSpecializationHomologyLinearEquivOfIntertwining R i j σ f h hσ hf y =
      oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h y :=
  ModuleCat.restrictScalarsLinearMap_apply
    (MvPolynomial.C : R →+* MvPolynomial {c : Fin n // c ≠ i} R)
    (MvPolynomial.C : R →+* MvPolynomial {c : Fin m // c ≠ j} R)
    (oneVariableSpecializationHomologyMapOfIntertwining R i j σ f h) hσ y

end Intertwining

end TauCeti.GridDiagram

namespace TauCeti.GridDiagram.IsKnot

variable {n : ℕ} {G : GridDiagram n}
variable (R : Type*) [CommRing R] [CharP R 2]

/-- The simply blocked grid homology `G-hat` obtained by setting the variable of column `i` to
zero.

The knot hypothesis records when the one-variable specialization has its standard topological
meaning: a knot has one component, so blocking one `O`-marking blocks one marking on every
component. -/
noncomputable abbrev simplyBlockedHomology (hG : G.IsKnot) (i : Fin n) :
    ModuleCat (MvPolynomial {c : Fin n // c ≠ i} R) :=
  (fun _ : G.IsKnot => (G.simplyBlockedComplex R i).homology ()) hG

/-- The cycles of the simply blocked differential, as an explicit submodule of the chain module;
see `TauCeti.GridDiagram.mem_ker_simplyBlockedComplex_d_iff` for membership in terms of
`simplyBlockedDifferential`. -/
noncomputable abbrev simplyBlockedCycles (hG : G.IsKnot) (i : Fin n) :
    Submodule (MvPolynomial {c : Fin n // c ≠ i} R)
      ((G.simplyBlockedComplex R i).X ()) :=
  (fun _ : G.IsKnot => LinearMap.ker ((G.simplyBlockedComplex R i).d () ()).hom) hG

/-- The boundary map into the cycles of the simply blocked complex.  Its image is contained in the
cycles because the differential squares to zero. -/
noncomputable abbrev simplyBlockedBoundaryMap (hG : G.IsKnot) (i : Fin n) :
      (G.simplyBlockedComplex R i).X ()
      →ₗ[MvPolynomial {c : Fin n // c ≠ i} R]
      hG.simplyBlockedCycles R i :=
  ((G.simplyBlockedComplex R i).sc' () () ()).moduleCatToCycles

/-- The boundaries of the simply blocked complex, regarded as a submodule of its cycles; see
`TauCeti.GridDiagram.mem_range_moduleCatToCycles_simplyBlockedComplex_iff` for membership in terms
of `simplyBlockedDifferential`. -/
noncomputable abbrev simplyBlockedBoundaries (hG : G.IsKnot) (i : Fin n) :
    Submodule (MvPolynomial {c : Fin n // c ≠ i} R)
      (hG.simplyBlockedCycles R i) :=
  LinearMap.range (hG.simplyBlockedBoundaryMap R i)

/-- The concrete cycles-modulo-boundaries model of simply blocked grid homology. -/
noncomputable abbrev simplyBlockedHomologyQuotient (hG : G.IsKnot) (i : Fin n) : Type _ :=
  let C := hG.simplyBlockedCycles R i
  let B : Submodule (MvPolynomial {c : Fin n // c ≠ i} R) C :=
    hG.simplyBlockedBoundaries R i
  C ⧸ B

/-- Mathlib's categorical homology of the simply blocked complex is canonically isomorphic to the
concrete quotient of cycles by boundaries. -/
noncomputable def simplyBlockedHomologyIsoQuotient (hG : G.IsKnot) (i : Fin n) :
    hG.simplyBlockedHomology R i ≅
      ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R)
        (hG.simplyBlockedHomologyQuotient R i) :=
  oneVariableSpecializationHomologyIsoQuotient G R i

/-- Under the concrete cycles-modulo-boundaries identification, the class of a cycle is its
quotient class. -/
@[simp]
theorem simplyBlockedHomologyIsoQuotient_hom_class (hG : G.IsKnot) (i : Fin n)
    (c : hG.simplyBlockedCycles R i) :
    (hG.simplyBlockedHomologyIsoQuotient R i).hom (G.oneVariableSpecializationHomologyClass R i c) =
      Submodule.Quotient.mk c := by
  exact oneVariableSpecializationHomologyIsoQuotient_hom_class G R i c

end TauCeti.GridDiagram.IsKnot
