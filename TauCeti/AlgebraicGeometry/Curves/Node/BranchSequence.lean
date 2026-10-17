/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.BranchSequence
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Pushforward

/-!
# The normalization sequence of a split node

Write `A = R[x,y]/(xy)`, `B = R[t] × R[t]`, let `ν : Spec B → Spec A` be the
branch morphism, and let `s : Spec R → Spec A` be the singular section. The branch
sequence gives a short exact sequence of sheaves of `𝒪_{Spec A}`-modules whose
terms are canonically identified with `𝒪_{Spec A}`, `ν_*𝒪_{Spec B}`, and
`s_*𝒪_{Spec R}`. Its maps are induced by the branch inclusion and the difference
of the values at the two branch origins.

The construction works over any commutative ring. Over an integrally closed domain,
`NodeAlgebra.isIntegralClosure_branchFractionMap` identifies `B` with the normalization
of `A` in its total ring of fractions. No normality assumption is needed for the sequence.
This is the local contribution of a split node to the normalization exact sequence
and hence to the arithmetic genus of a nodal curve.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
* R. Hartshorne, *Algebraic Geometry*, Exercise IV.1.8.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

universe u

variable (R : Type u) [CommRing R]

-- Specialize before instance search unfolds the concrete node algebra's ring structure.
local instance : (tilde.functor (.of (NodeAlgebra R 0))).Additive :=
  instAdditiveModuleCatCarrierModulesSpecFunctor (R := .of (NodeAlgebra R 0))

/-- The associated-sheaf branch sequence on the split node. Its objects and maps
remain transparent so that exact-sequence and cohomology constructions can use them. -/
abbrev branchSheafSequence : ShortComplex (Spec (.of (NodeAlgebra R 0))).Modules :=
  (branchModuleSequence R).map (tilde.functor (.of (NodeAlgebra R 0)))

/-- The middle term of the branch sequence is the direct image of the structure
sheaf of the two branches. -/
def branchSheafSequenceMiddleIso :
    (branchSheafSequence R).X₂ ≅
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (branchMap R).toRingHom))).obj
        (SheafOfModules.unit (Spec (.of (R[X] × R[X]))).ringCatSheaf) :=
  tildeRestrictScalarsIsoPushforward (CommRingCat.ofHom (branchMap R).toRingHom)
      (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])) ≪≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (branchMap R).toRingHom))).mapIso tildeSelf

/-- The middle-term comparison sends a pair of branch functions to its associated
section on the two branches. -/
@[simp]
theorem branchSheafSequenceMiddleIso_hom_toOpen (p : R[X] × R[X]) :
    dsimp% only [ShortComplex.map_X₂, AlgHom.toRingHom_eq_coe]
    (branchSheafSequenceMiddleIso R).hom.val.app (.op ⊤)
        (tilde.toOpen (R := .of (NodeAlgebra R 0))
          ((ModuleCat.restrictScalars (branchMap R : NodeAlgebra R 0 →+* R[X] × R[X])).obj
            (ModuleCat.of (R[X] × R[X]) (R[X] × R[X]))) ⊤ p) =
      tilde.toOpen (R := .of (R[X] × R[X])) (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])) ⊤ p := by
  exact tildeRestrictScalarsIsoPushforward_hom_toOpen
    (CommRingCat.ofHom (branchMap R).toRingHom)
    (ModuleCat.of (R[X] × R[X]) (R[X] × R[X])) p

/-- The last term of the branch sequence is the direct image of the structure
sheaf of the singular section. -/
def branchSheafSequenceRightIso :
    (branchSheafSequence R).X₃ ≅
      (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (nodeValue R).toRingHom))).obj
        (SheafOfModules.unit (Spec (.of R)).ringCatSheaf) :=
  tildeRestrictScalarsIsoPushforward
      (CommRingCat.ofHom (nodeValue R).toRingHom) (ModuleCat.of R R) ≪≫
    (Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (nodeValue R).toRingHom))).mapIso tildeSelf

/-- The last-term comparison sends a value at the node to its associated section
on the singular section. -/
@[simp]
theorem branchSheafSequenceRightIso_hom_toOpen (r : R) :
    dsimp% only [ShortComplex.map_X₃, AlgHom.toRingHom_eq_coe]
    (branchSheafSequenceRightIso R).hom.val.app (.op ⊤)
        (tilde.toOpen (R := .of (NodeAlgebra R 0))
          ((ModuleCat.restrictScalars (nodeValue R : NodeAlgebra R 0 →+* R)).obj
            (ModuleCat.of R R)) ⊤ r) =
      tilde.toOpen (R := .of R) (ModuleCat.of R R) ⊤ r := by
  exact tildeRestrictScalarsIsoPushforward_hom_toOpen
    (CommRingCat.ofHom (nodeValue R).toRingHom) (ModuleCat.of R R) r

/-- The normalization sequence of the split node is short exact as sheaves of
modules on the node, including over nonreduced base rings. -/
theorem branchSheafSequence_shortExact : (branchSheafSequence R).ShortExact := by
  have hmap (A : CommRingCat.{u}) (S : ShortComplex (ModuleCat A)) (hS : S.ShortExact) :
      (S.map (tilde.functor A)).ShortExact := hS.map_of_exact (tilde.functor A)
  exact hmap _ _ (branchModuleSequence_shortExact R)

end TauCeti.NodeAlgebra
