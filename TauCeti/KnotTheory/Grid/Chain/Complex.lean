/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.KnotTheory.Grid.Differential.Square.Zero

/-!
# Grid differentials as homological complexes

This file packages the three grid chain modules and their square-zero differentials as
homological complexes in Mathlib's sense. Each uses the one-object circular shape
`ComplexShape.refl Unit`: its sole object is the total chain module and its sole differential is
the corresponding grid differential. This is the ungraded complex underlying the separate
bigraded decompositions of the fully blocked and unblocked chain modules.

The one-object form retains exactly the algebra needed for cycles, boundaries, chain maps, and
homology while applying to every grid diagram. In particular it does not require the odd-component
hypothesis used to make the Alexander grading integral. Later graded constructions can refine these
complexes by restricting the differential to their homogeneous pieces. Here
`simplyBlockedComplex` denotes the algebraic specialization obtained by setting one selected
`O`-variable to zero. This has the standard simply blocked interpretation for knot grids; for a
multi-component link, that interpretation instead requires one blocked `O`-marking on each
component.

The fully blocked complex is over `ZMod 2`. The unblocked complex and the one-variable
specialization are defined over an arbitrary commutative coefficient ring of characteristic two.
Their coefficient rings are, respectively, the polynomial ring on all columns and the polynomial
ring on the columns other than the selected blocked column.

## Main definitions

* `TauCeti.GridDiagram.fullyBlockedComplex`: the fully blocked grid complex.
* `TauCeti.GridDiagram.unblockedComplex`: the unblocked grid complex `GC⁻`.
* `TauCeti.GridDiagram.simplyBlockedComplex`: the one-variable specialization obtained by setting
  one selected `O`-variable to zero.

## References

The three grid complexes and their coefficient conventions follow Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapters 3--4.

The opaque-safe object and differential equations follow the formal pattern used in
`TauCeti.LowDimTopology.Plumbing.ChainComplex`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v

private noncomputable def endomorphismComplex {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (hd : d ≫ d = 0) :
    HomologicalComplex C (ComplexShape.refl Unit) where
  X _ := X
  d _ _ := d
  d_comp_d' _ _ _ _ _ := hd

private theorem endomorphismComplex_X {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (hd : d ≫ d = 0) (i : Unit) :
    (endomorphismComplex X d hd).X i = X :=
  rfl

private theorem endomorphismComplex_d {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
    (X : C) (d : X ⟶ X) (hd : d ≫ d = 0)
    (hX : (endomorphismComplex X d hd).X () = X) :
    (endomorphismComplex X d hd).d () () =
      eqToHom hX ≫ d ≫ eqToHom hX.symm := by
  change d = 𝟙 X ≫ d ≫ 𝟙 X
  simp only [Category.id_comp, Category.comp_id]

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

/-! ### Fully blocked complex -/

/-- The fully blocked grid chain module and differential as a one-object homological complex over
`ZMod 2`.

The unique differential counts empty rectangles avoiding every marking. Its square is zero by the
rectangle-juxtaposition pairing. -/
noncomputable def fullyBlockedComplex :
    HomologicalComplex (ModuleCat (ZMod 2)) (ComplexShape.refl Unit) :=
  endomorphismComplex
    (ModuleCat.of (ZMod 2) (GridChain (ZMod 2) n))
    (ModuleCat.ofHom G.fullyBlockedDifferential) <| by
      rw [← ModuleCat.ofHom_comp, G.fullyBlockedDifferential_comp_self_eq_zero,
        ModuleCat.ofHom_zero]

/-- The unique object of the fully blocked complex is the fully blocked grid chain module. -/
@[simp]
theorem fullyBlockedComplex_X (i : Unit) :
    G.fullyBlockedComplex.X i = ModuleCat.of (ZMod 2) (GridChain (ZMod 2) n) :=
  endomorphismComplex_X _ _ _ i

/-- The unique differential of the fully blocked complex is the fully blocked grid differential. -/
@[simp]
theorem fullyBlockedComplex_d :
    G.fullyBlockedComplex.d () () =
      eqToHom (G.fullyBlockedComplex_X ()) ≫
        ModuleCat.ofHom G.fullyBlockedDifferential ≫
          eqToHom (G.fullyBlockedComplex_X ()).symm := by
  unfold fullyBlockedComplex
  exact endomorphismComplex_d _ _ _ (G.fullyBlockedComplex_X ())

/-! ### Unblocked complex -/

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The unblocked grid chain module `GC⁻` and its differential as a one-object homological complex
over the polynomial ring `R[V₀, ..., V_{n-1}]`.

The unique differential counts empty rectangles avoiding the `X`-markings and weights each
rectangle by the monomial of the `O`-markings it covers. -/
noncomputable def unblockedComplex :
    HomologicalComplex (ModuleCat (MvPolynomial (Fin n) R)) (ComplexShape.refl Unit) :=
  endomorphismComplex
    (ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n))
    (ModuleCat.ofHom (G.unblockedDifferential R)) <| by
      rw [← ModuleCat.ofHom_comp, G.unblockedDifferential_comp_self_eq_zero R,
        ModuleCat.ofHom_zero]

/-- The unique object of the unblocked complex is the unblocked grid chain module. -/
@[simp]
theorem unblockedComplex_X (i : Unit) :
    (G.unblockedComplex R).X i =
      ModuleCat.of (MvPolynomial (Fin n) R) (GridChainMinus R n) :=
  endomorphismComplex_X _ _ _ i

/-- The unique differential of the unblocked complex is the unblocked grid differential. -/
@[simp]
theorem unblockedComplex_d :
    (G.unblockedComplex R).d () () =
      eqToHom (G.unblockedComplex_X R ()) ≫
        ModuleCat.ofHom (G.unblockedDifferential R) ≫
          eqToHom (G.unblockedComplex_X R ()).symm := by
  unfold unblockedComplex
  exact endomorphismComplex_d _ _ _ (G.unblockedComplex_X R ())

/-! ### One-variable specialization -/

/-- The one-variable specialization of the grid chain module and differential as a one-object
homological complex over the polynomial ring on the columns other than `i`.

The unique differential is obtained from the unblocked differential by setting the selected
variable `V_i` to zero. For a knot grid this is the standard simply blocked complex; for a link,
the standard simply blocked theory sets one variable on each component to zero. -/
noncomputable def simplyBlockedComplex (i : Fin n) :
    HomologicalComplex (ModuleCat (MvPolynomial {c : Fin n // c ≠ i} R))
      (ComplexShape.refl Unit) :=
  endomorphismComplex
    (ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i))
    (ModuleCat.ofHom (G.simplyBlockedDifferential R i)) <| by
      rw [← ModuleCat.ofHom_comp, G.simplyBlockedDifferential_comp_self_eq_zero R i,
        ModuleCat.ofHom_zero]

/-- The unique object of the one-variable specialization is its specialized grid chain module. -/
@[simp]
theorem simplyBlockedComplex_X (i : Fin n) (j : Unit) :
    (G.simplyBlockedComplex R i).X j =
      ModuleCat.of (MvPolynomial {c : Fin n // c ≠ i} R) (GridChainHat R n i) :=
  endomorphismComplex_X _ _ _ j

/-- The unique differential of the one-variable specialization is its specialized grid
differential. -/
@[simp]
theorem simplyBlockedComplex_d (i : Fin n) :
    (G.simplyBlockedComplex R i).d () () =
      eqToHom (G.simplyBlockedComplex_X R i ()) ≫
        ModuleCat.ofHom (G.simplyBlockedDifferential R i) ≫
          eqToHom (G.simplyBlockedComplex_X R i ()).symm := by
  unfold simplyBlockedComplex
  exact endomorphismComplex_d _ _ _ (G.simplyBlockedComplex_X R i ())

end GridDiagram

end TauCeti
