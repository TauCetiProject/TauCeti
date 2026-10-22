/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.TruncLE
public import TauCeti.AlgebraicTopology.DoldKan.Monoidal
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.SimplicialGroup
public import TauCeti.Algebra.Category.ModuleCat.Monoidal.Forget

/-!
# From cochain complexes to Kan complexes

Good truncation and Dold–Kan send a cochain complex `K` to the underlying simplicial set
of `Γ(K.truncLE' embeddingDownNat)`. In particular degree zero uses cycles, rather than
the whole of `K.X 0`. This functor is lax monoidal, using the lax good truncation and
the Alexander–Whitney lax structure on `Γ`, and its values are Kan complexes by Moore's
theorem for simplicial groups. It supplies the mapping objects for simplicial enrichment
of differential graded categories.

## References

* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

noncomputable section

variable (R : Type u) [CommRing R]

/-- The underlying Kan complex of the Dold–Kan image of the good homological truncation.
Its nonnegative chain degree `n` corresponds to cochain degree `-n`. -/
@[expose]
def cochainToSSet : CochainComplex (ModuleCat.{u} R) ℤ ⥤ SSet.{u} :=
  ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R) ⋙
    Idempotents.DoldKan.Γ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R))

/-- The simplicial set assigned to a complex is the underlying simplicial module of
its good truncation under Dold–Kan. -/
theorem cochainToSSet_obj (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (cochainToSSet R).obj K =
      Idempotents.DoldKan.Γ.obj (K.truncLE' ComplexShape.embeddingDownNat) ⋙
        forget (ModuleCat.{u} R) :=
  (rfl)

/-- The functor to simplicial sets uses the Alexander–Whitney lax monoidal structure
on Dold–Kan and the lax monoidal good truncation. -/
instance cochainToSSetLaxMonoidal : (cochainToSSet R).LaxMonoidal :=
  inferInstanceAs ((ComplexShape.embeddingDownNat.truncLE'Functor (ModuleCat.{u} R) ⋙
    Idempotents.DoldKan.Γ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget (ModuleCat.{u} R))).LaxMonoidal)

/-- The simplicial set assigned to every cochain complex is a Kan complex. -/
instance (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    SSet.KanComplex ((cochainToSSet R).obj K) := by
  rw [cochainToSSet_obj]
  infer_instance

end

end TauCeti
