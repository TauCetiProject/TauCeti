/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.FullFaithful

/-!
# Endomorphism algebras of Clifford multiplicities

For an inertia representation with semisimple isotypic restriction to the normal
subgroup, postcomposition identifies its endomorphism algebra with the endomorphism
algebra of its crossed-product multiplicity module. The coefficients are the full
opposite commutant, and the factors are inverse factors. No splitting-field or
finite-group hypothesis is required.

The algebra equivalence uses the linear Hom correspondence and preserves the native
endomorphism multiplication: the product of two endomorphisms is their composition
in reverse categorical order. Its inverse is characterized by balanced evaluation.
This permits endomorphism-algebra calculations on the multiplicity side without
identifying the commutant with the ground field.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory TauCeti TauCeti.CliffordExtension
open scoped MonoidAlgebra ModuleCat.Algebra

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)
  (W : FDRep k (inertia A))
  [IsSemisimpleModule k[N] (Representation.asModule (FDRep.ρ
    ((Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)))]
  (hW : IsIsotypicOfType k[N] (Representation.asModule (FDRep.ρ
    ((Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)))
    (Representation.asModule A.ρ))

local notation "C" => cliffordMultiplicityFunctor A s hs

/-- Postcomposition gives an algebra equivalence between inertia endomorphisms and
endomorphisms of the crossed-product multiplicity module. The source representation
must have semisimple isotypic restriction; the coefficient field need not split it. -/
noncomputable def cliffordMultiplicityEndAlgEquiv :
    End W ≃ₐ[k] End ((C).obj W) :=
  AlgEquiv.ofBijective ((C).mapEndAlgHom k W)
    ((C).mapEndAlgHom_bijective k W (cliffordMultiplicityFunctor_map_bijective A s hs hW))

/-- The forward algebra equivalence is the multiplicity functor on endomorphisms. -/
@[simp]
theorem cliffordMultiplicityEndAlgEquiv_asHom (f : End W) :
    (cliffordMultiplicityEndAlgEquiv A s hs W hW f).asHom = (C).map f.asHom := by
  unfold cliffordMultiplicityEndAlgEquiv
  exact (congrArg End.asHom (AlgEquiv.ofBijective_apply _ _ f)).trans
    ((C).mapEndAlgHom_asHom k W f)

/-- The inverse algebra equivalence reconstructs the intertwiner by balanced evaluation. -/
@[simp]
theorem cliffordMultiplicityEndAlgEquiv_symm_asHom (f : End ((C).obj W)) :
    ((cliffordMultiplicityEndAlgEquiv A s hs W hW).symm f).asHom =
      cliffordMultiplicityPreimage A s hs hW f.asHom := by
  apply (cliffordMultiplicityHomEquiv A s hs hW).injective
  rw [cliffordMultiplicityHomEquiv_apply,
    ← cliffordMultiplicityEndAlgEquiv_asHom A s hs W hW,
    AlgEquiv.apply_symm_apply, cliffordMultiplicityHomEquiv_apply,
    cliffordMultiplicityFunctor_map_preimage]

end FDRep
