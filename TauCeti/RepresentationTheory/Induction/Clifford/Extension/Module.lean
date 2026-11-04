/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.Clifford.Extension.Multiplicity
public import TauCeti.Algebra.CrossedProduct.Noncommutative.Module
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Crossed-product modules on Clifford multiplicity spaces

A normalized section of the canonical Clifford extension makes `Hom_N(A, W)` a module
for the crossed product with coefficients `(End A)ᵐᵒᵖ` and factors `op (a(q,r)⁻¹)`.
The coefficient `op d` acts by precomposition with `d`, and the basis element `[q]`
acts by the section's Clifford operator. Postcomposition with an inertia intertwiner
is linear over this algebra, giving a functor from inertia representations to modules.

This constructs the multiplicity side of the isotypic correspondence over nonsplitting
fields. It does not require simplicity of `A`, semisimplicity, or finiteness of the
inertia quotient; the crossed product uses finite support even for an infinite quotient.

The construction connects `FDRep.cliffordMultiplicityRepresentation` and its semilinearity
and inverse-factor laws to `CrossedSystem.opInvSemilinearAction` and
`CrossedSystem.SemilinearAction.linearMap`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public section

namespace FDRep

open CategoryTheory MulOpposite TauCeti TauCeti.CliffordExtension

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]
  {N : Subgroup G} [N.Normal] (A : FDRep k N)
  (s : (groupExtension A).Section) (hs : s 1 = 1)

/-- The Clifford section operators form a semilinear action on the right-commutant
multiplicity space, with opposite coefficients and inverse factors. -/
noncomputable def cliffordMultiplicitySemilinearAction (W : FDRep k (inertia A)) :
    CrossedSystem.SemilinearAction (cliffordCrossedSystem A s hs).opInv
      (A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W) :=
  CrossedSystem.opInvSemilinearAction (cliffordCrossedSystem A s hs) _
    (fun q => cliffordMultiplicityRepresentation A W (s q))
    (by rw [hs, map_one])
    (fun q d f => by
      simpa only [cliffordCrossedSystem_action] using
        cliffordMultiplicityRepresentation_smul A W (s q) d f)
    (cliffordMultiplicityRepresentation_section_mul A W s hs)

/-- The semilinear operator at `q` is the Clifford operator of the chosen section. -/
@[simp]
theorem cliffordMultiplicitySemilinearAction_operator (W : FDRep k (inertia A))
    (q : Quotient A) :
    (cliffordMultiplicitySemilinearAction A s hs W).operator q =
      cliffordMultiplicityRepresentation A W (s q) := by
  simp [cliffordMultiplicitySemilinearAction]

/-- Multiplicity spaces and postcomposition form a functor to modules over the
opposite-coefficient, inverse-factor crossed product of the chosen Clifford section.
This abbreviation preserves the concrete Hom carriers for evaluation of module elements. -/
noncomputable abbrev cliffordMultiplicityFunctor :
    FDRep k (inertia A) ⥤
      ModuleCat (CrossedSystem.Algebra (cliffordCrossedSystem A s hs).opInv) where
  obj W :=
    letI := (cliffordMultiplicitySemilinearAction A s hs W).module
    ModuleCat.of _
      (A ⟶ (Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).obj W)
  map {W W'} g :=
    letI := (cliffordMultiplicitySemilinearAction A s hs W).module
    letI := (cliffordMultiplicitySemilinearAction A s hs W').module
    ModuleCat.ofHom (
      CrossedSystem.SemilinearAction.linearMap
        (cliffordMultiplicitySemilinearAction A s hs W)
        (cliffordMultiplicitySemilinearAction A s hs W')
        (Linear.rightComp k A
          ((Action.res (FGModuleCat k) (Subgroup.inclusion (le_inertia A))).map g))
        (by
          intro d f
          ext x
          simp only [Linear.rightComp_apply, End.smul_left, Category.assoc])
        (fun q f => by
          simpa only [cliffordMultiplicitySemilinearAction_operator, Linear.rightComp_apply] using
            cliffordMultiplicityRepresentation_naturality A W g (s q) f))
  map_id W := by
    let := (cliffordMultiplicitySemilinearAction A s hs W).module
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun f => by simp
  map_comp {W W' W''} g h := by
    let := (cliffordMultiplicitySemilinearAction A s hs W).module
    let := (cliffordMultiplicitySemilinearAction A s hs W').module
    let := (cliffordMultiplicitySemilinearAction A s hs W'').module
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun f => by simp

end FDRep
