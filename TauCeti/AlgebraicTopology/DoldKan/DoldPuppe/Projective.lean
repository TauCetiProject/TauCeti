/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.AlgebraicTopology.DoldKan.DoldPuppe.Basic

/-!
# Resolution independence of the Dold–Puppe functor

In an abelian category `C`, quasi-isomorphisms between degreewise projective chain complexes are
chain homotopy equivalences, and `CategoryTheory.Functor.doldPuppeFunctor F` preserves chain
homotopy equivalences for any functor `F : C ⥤ D` (not necessarily additive). Hence
`F.doldPuppeFunctor` sends quasi-isomorphisms between degreewise projective chain complexes to
quasi-isomorphisms (`CategoryTheory.Functor.quasiIso_doldPuppeFunctor_map_of_projective`).
-/

public noncomputable section

universe v u v' u'

open CategoryTheory

namespace CategoryTheory

section AbelianDoldPuppe

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryWithHomology D]

/-- **Resolution independence of the Dold–Puppe construction**: in an abelian category `C`, if
`P` and `Q` are degreewise projective chain complexes and `f : P ⟶ Q` is a quasi-isomorphism, then
for *any* functor `F : C ⥤ D` (not necessarily additive), `F.doldPuppeFunctor.map f` is a
quasi-isomorphism. -/
theorem Functor.quasiIso_doldPuppeFunctor_map_of_projective (F : C ⥤ D)
    {P Q : ChainComplex C ℕ} [∀ n, Projective (P.X n)] [∀ n, Projective (Q.X n)]
    (f : P ⟶ Q) [hf : QuasiIso f] :
    QuasiIso (F.doldPuppeFunctor.map f) := by
  rw [ChainComplex.quasiIso_iff_of_projective] at hf
  obtain ⟨e, rfl⟩ := hf
  rw [← F.doldPuppeMapHomotopyEquiv_hom e]
  exact homotopyEquivalences_le_quasiIso D (.down ℕ) _
    (F.doldPuppeMapHomotopyEquiv e).homotopyEquivalences_hom

end AbelianDoldPuppe

end CategoryTheory
