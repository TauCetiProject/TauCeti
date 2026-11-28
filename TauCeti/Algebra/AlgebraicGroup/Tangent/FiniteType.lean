/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.FinitePresentation
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent
public import TauCeti.RingTheory.Ideal.Cotangent.Basic

/-!
# Finiteness of the tangent space of a finite-type affine monoid

The counit of a finite-type commutative bialgebra has finite cotangent space at the
identity over any commutative base ring. Over a field it is consequently finite-dimensional
and projective. This is the finiteness input for the scalar-extension description of the
tangent space and the adjoint representation.

## Main declarations

* `TauCeti.Bialgebra.instModuleFiniteCotangentSpace`: the specialization to the counit of a
  finite-type commutative bialgebra.
* `TauCeti.FiniteTypeCommHopfAlgCat.dualCotangentMap_toBialgHom_id` and
  `TauCeti.FiniteTypeCommHopfAlgCat.dualCotangentMap_toBialgHom_comp`: functoriality of
  `Derivation.dualCotangentMap ∘ toBialgHom` in `FiniteTypeCommHopfAlgCat`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§12 and 14.
* Mathlib's `Algebra.FinitePresentation.ker_fG_of_surjective` supplies finite generation
  of the augmentation kernel in a polynomial presentation.
-/

public section

namespace TauCeti.Bialgebra

open _root_.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The cotangent space at the identity of a finite-type commutative bialgebra is finite
over any commutative base ring. -/
instance instModuleFiniteCotangentSpace [Algebra.FiniteType R A] :
    Module.Finite R (CotangentSpace R A) := by
  obtain ⟨s, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial.mp
    (inferInstance : Algebra.FiniteType R A))
  let f := counitAlgHom R A
  have hf : Function.Surjective f := fun r ↦ ⟨algebraMap R A r, f.commutes r⟩
  have hfg := (Algebra.FinitePresentation.ker_fG_of_surjective (f.comp g) (hf.comp hg)).map
    g.toRingHom
  simp_rw [RingHom.ker_eq_comap_bot, AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom] at hfg
  rw [← Ideal.comap_comap,
    Ideal.map_comap_of_surjective (g : MvPolynomial s R →+* A) hg] at hfg
  exact AlgHom.finite_cotangent_ker_of_fg f hf hfg

end TauCeti.Bialgebra

namespace TauCeti.FiniteTypeCommHopfAlgCat

open CategoryTheory Derivation

section Functoriality

universe u v

variable {R : Type u} [CommRing R]

/-- The dual cotangent map of the identity morphism in `FiniteTypeCommHopfAlgCat` acts as the
identity. -/
theorem dualCotangentMap_toBialgHom_id (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (x : Module.Dual R (Bialgebra.CotangentSpace R H)) :
    dualCotangentMap (toBialgHom (𝟙 H)) x = x := by
  rw [toBialgHom_id, dualCotangentMap_id, LinearMap.id_apply]

/-- The dual cotangent map of a composite morphism in `FiniteTypeCommHopfAlgCat` is the
contravariant composite of the dual cotangent maps. -/
theorem dualCotangentMap_toBialgHom_comp {H K L : FiniteTypeCommHopfAlgCat.{u, v} R}
    (f : H ⟶ K) (g : K ⟶ L) (x : Module.Dual R (Bialgebra.CotangentSpace R L)) :
    dualCotangentMap (toBialgHom f) (dualCotangentMap (toBialgHom g) x) =
      dualCotangentMap (toBialgHom (f ≫ g)) x := by
  rw [toBialgHom_comp, dualCotangentMap_comp, LinearMap.comp_apply]

end Functoriality

end TauCeti.FiniteTypeCommHopfAlgCat
