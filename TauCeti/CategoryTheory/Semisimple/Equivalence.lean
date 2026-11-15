/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Semisimple.Multiplicity

/-!
# Simple multiplicities under equivalences

An equivalence between finite semisimple abelian categories transports the decomposition
multiplicity function along the induced equivalence of simple isomorphism classes. Thus the
multiplicity of a simple class is intrinsic to the category and does not depend on a chosen
equivalent presentation.

## Main results

* `TauCeti.simpleMultiplicities_map_equivalence`: the whole finitely supported multiplicity
  function is transported along an equivalence.
* `TauCeti.simpleMultiplicities_map_equivalence_apply`: the corresponding pointwise formula.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C] [IsFiniteSemisimpleCategory C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- An equivalence transports the simple multiplicity function along its equivalence of simple
isomorphism classes. -/
@[simp]
theorem simpleMultiplicities_map_equivalence (e : C ≌ D) (X : C) :
    Finsupp.equivMapDomain (SimpleClasses.equiv e) (simpleMultiplicities X) =
      @simpleMultiplicities D _ _ (IsFiniteSemisimpleCategory.of_equivalence e)
        (e.functor.obj X) := by
  classical
  let _ := IsFiniteSemisimpleCategory.of_equivalence e
  obtain ⟨ι, hι, f, hf, hbf, ⟨d⟩⟩ :=
    IsFiniteSemisimpleCategory.exists_biproduct_simples X
  let := hι
  let := hf
  let := hbf
  let hfe : ∀ i, Simple (e.functor.obj (f i)) := fun i ↦ simple_obj e.functor (f i)
  let _ := hfe
  have := preservesBiproduct_of_preservesProduct e.functor (f := f)
  rw [simpleMultiplicities_eq_of_iso_biproduct f d,
    simpleMultiplicities_eq_of_iso_biproduct (fun i ↦ e.functor.obj (f i))
      (e.functor.mapIso d ≪≫ e.functor.mapBiproduct f)]
  rw [← Finsupp.domCongr_apply, map_sum]
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_single,
    SimpleClasses.equiv_apply_classOf]

/-- The multiplicity of a simple class is unchanged after transporting both the object and the
class along an equivalence. -/
@[simp]
theorem simpleMultiplicities_map_equivalence_apply (e : C ≌ D) (X : C)
    (S : SimpleClasses C) :
    @simpleMultiplicities D _ _ (IsFiniteSemisimpleCategory.of_equivalence e)
        (e.functor.obj X) (SimpleClasses.equiv e S) =
      simpleMultiplicities X S := by
  let _ := IsFiniteSemisimpleCategory.of_equivalence e
  have h := congrArg (fun m ↦ m (SimpleClasses.equiv e S))
    (simpleMultiplicities_map_equivalence e X)
  simpa only [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply] using h.symm

end TauCeti
