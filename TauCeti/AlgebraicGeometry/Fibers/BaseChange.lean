/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Maps between scheme-theoretic fibres under base change

A commutative square of families induces a map between the fibres over corresponding points.
It commutes with the inclusions into the total spaces and with the induced residue-field map.
For a cartesian square of families, the square over residue fields is the pullback square of
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Every scheme-theoretic fibre of a quasi-separated morphism is quasi-separated. -/
instance quasiSeparatedSpace_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiSeparated f] (s : S) : QuasiSeparatedSpace (f.fiber s) := by
  have : QuasiSeparated (f.fiberToSpecResidueField s) :=
    inferInstanceAs (QuasiSeparated (pullback.snd f (S.fromSpecResidueField s)))
  exact quasiSeparatedSpace_of_quasiSeparated (f.fiberToSpecResidueField s)

end AlgebraicGeometry.Scheme.Hom

namespace CategoryTheory.CommSq

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  {g : S' ⟶ S} {g' : X' ⟶ X}

/-- The canonical map between residue-field fibres in a commutative square. -/
def fiberBaseChangeMap (H : CommSq g' f' f g) (s' : S') :
    f'.fiber s' ⟶ f.fiber (g s') :=
  pullback.map f' (S'.fromSpecResidueField s') f (S.fromSpecResidueField (g s'))
    g' (Spec.map (g.residueFieldMap s')) g H.w.symm (by simp)

/-- The fibre comparison is the map induced on the two defining fibre pullbacks. -/
theorem fiberBaseChangeMap_def (H : CommSq g' f' f g) (s' : S') :
    fiberBaseChangeMap H s' =
      pullback.map f' (S'.fromSpecResidueField s') f (S.fromSpecResidueField (g s'))
        g' (Spec.map (g.residueFieldMap s')) g H.w.symm (by simp) := by rfl

/-- The fibre comparison preserves the map to the original total space. -/
@[reassoc (attr := simp)]
lemma fiberBaseChangeMap_comp_fiberι (H : CommSq g' f' f g) (s' : S') :
    fiberBaseChangeMap H s' ≫ f.fiberι (g s') = f'.fiberι s' ≫ g' :=
  pullback.lift_fst _ _ _

/-- The fibre comparison lies over the induced map of residue fields. -/
@[reassoc (attr := simp)]
lemma fiberBaseChangeMap_comp_fiberToSpecResidueField (H : CommSq g' f' f g) (s' : S') :
    fiberBaseChangeMap H s' ≫ f.fiberToSpecResidueField (g s') =
      f'.fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s') :=
  pullback.lift_snd _ _ _

end CategoryTheory.CommSq
