/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Mackey.Irreducible

/-!
# Endomorphisms of induced representations

Induction gives an injective algebra homomorphism from the endomorphisms of a
finite-dimensional subgroup representation to the endomorphisms of its induction.
When all nonidentity Mackey intertwining spaces vanish, this homomorphism is an
isomorphism. This identifies the algebra structure over arbitrary fields, including
nonsplitting fields.

This is the algebra comparison used in the sufficient direction of Mackey's
irreducibility criterion: a division endomorphism algebra remains a division algebra
under induction when the other Mackey terms vanish. No semisimplicity hypothesis is
needed for the comparison itself.

The construction uses `TauCeti.indFDRepMap` and the characteristic-free natural-number
formula `TauCeti.finrank_hom_indFDRep_mackey_erase`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §7.4, Proposition 23.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory*, Vol. I, §10.
-/

public section

open CategoryTheory TauCeti

namespace FDRep

universe u

variable {k G : Type u} [Field k] [Group G] {H : Subgroup G}

/-- The algebra homomorphism on endomorphisms given by induction from a finite-index subgroup.
Multiplication on both native endomorphism algebras is reverse categorical composition. -/
noncomputable def indEndAlgHom [H.FiniteIndex] (A : FDRep k H) :
    CategoryTheory.End A →ₐ[k] CategoryTheory.End (indFDRep A) :=
  AlgHom.ofLinearMap
    { toFun := fun f ↦ End.of (indFDRepMap f.asHom)
      map_add' := fun f g ↦ by ext; simp [End.add_asHom, indFDRepMap_add]
      map_smul' := fun r f ↦ by ext; simp [End.smul_asHom, indFDRepMap_smul] }
    (by ext; simp [End.one_asHom])
    (fun f g ↦ by ext; simp [End.mul_asHom, indFDRepMap_comp])

/-- The endomorphism algebra map acts by the native induction map on intertwiners. -/
@[simp]
theorem indEndAlgHom_asHom [H.FiniteIndex] (A : FDRep k H) (f : CategoryTheory.End A) :
    (A.indEndAlgHom f).asHom = indFDRepMap f.asHom :=
  (rfl)

/-- Induction from a finite-index subgroup embeds the endomorphism algebra. -/
theorem indEndAlgHom_injective [H.FiniteIndex] (A : FDRep k H) :
    Function.Injective A.indEndAlgHom := by
  intro f g h
  apply End.ext
  apply indFDRepMap_injective
  simpa only [indEndAlgHom_asHom] using congrArg End.asHom h

/-- If all nonidentity double cosets are Mackey disjoint, every endomorphism of the induced
representation is induced from a unique endomorphism of the original representation. -/
theorem indEndAlgHom_bijective [Finite G] (A : FDRep k H)
    (h : ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out) :
    Function.Bijective A.indEndAlgHom := by
  classical
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  have hdim : Module.finrank k (A ⟶ A) = Module.finrank k (indFDRep A ⟶ indFDRep A) := by
    rw [finrank_hom_indFDRep_mackey_erase]
    simp only [mackeyDisjoint_iff_finrank_eq_zero] at h
    rw [Finset.sum_eq_zero (fun D hD ↦ h D (Finset.mem_erase.mp hD).1), add_zero]
  let l : (A ⟶ A) →ₗ[k] (indFDRep A ⟶ indFDRep A) :=
    { toFun := indFDRepMap
      map_add' := indFDRepMap_add
      map_smul' := indFDRepMap_smul }
  have hsurj : Function.Surjective l :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp indFDRepMap_injective
  refine ⟨A.indEndAlgHom_injective, fun f ↦ ?_⟩
  obtain ⟨g, hg⟩ := hsurj f.asHom
  refine ⟨End.of g, End.ext ?_⟩
  rw [indEndAlgHom_asHom]
  exact hg

/-- With no nonidentity Mackey intertwiners, induction identifies the actual endomorphism
algebras, over any coefficient field. -/
noncomputable def indEndAlgEquiv [Finite G] (A : FDRep k H)
    (h : ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out) :
    CategoryTheory.End A ≃ₐ[k] CategoryTheory.End (indFDRep A) :=
  AlgEquiv.ofBijective A.indEndAlgHom (A.indEndAlgHom_bijective h)

/-- The endomorphism algebra comparison acts by induction on underlying intertwiners. -/
@[simp]
theorem indEndAlgEquiv_asHom [Finite G] (A : FDRep k H)
    (h : ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out) (f : CategoryTheory.End A) :
    (A.indEndAlgEquiv h f).asHom = indFDRepMap f.asHom := by
  rw [indEndAlgEquiv, AlgEquiv.ofBijective_apply, indEndAlgHom_asHom]

/-- The inverse algebra comparison recovers the unique subgroup endomorphism inducing a given
endomorphism of the induced representation. -/
@[simp]
theorem indFDRepMap_indEndAlgEquiv_symm_asHom [Finite G] (A : FDRep k H)
    (h : ∀ D : DoubleCoset.Quotient (H : Set G) (H : Set G),
      D ≠ DoubleCoset.mk H H 1 → MackeyDisjoint A D.out)
    (f : CategoryTheory.End (indFDRep A)) :
    indFDRepMap ((A.indEndAlgEquiv h).symm f).asHom = f.asHom := by
  rw [← indEndAlgEquiv_asHom A h, AlgEquiv.apply_symm_apply]

end FDRep
