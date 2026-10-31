/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Pivotal.Biproduct
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Simple
public import TauCeti.CategoryTheory.Semisimple.Basic

/-!
# Pivotal structures on finite semisimple categories

In a finite semisimple rigid category every object is a finite biproduct of simple objects, so
pivotal structures and their traces are controlled by what happens on simple objects.

* A pivotal structure is a natural isomorphism out of the identity functor, so two pivotal
  structures whose components agree at every simple object are equal.
* Over an algebraically closed field `k`, two pivotal structures `P` and `Q` differ at a simple
  object `X` by an automorphism of `X`, which is a scalar `c`, and the left dimension of `X` for
  `P` is `c` times its left dimension for `Q`. So two pivotal structures with the same nonzero
  left dimensions at every simple object are equal.
* Every endomorphism of a biproduct of simple objects has trace equal to the sum of the scalars of
  its diagonal components times the dimensions of the summands. So a pivotal structure is spherical
  exactly when the left and right dimensions of every simple object agree.

## Main results

* `TauCeti.PivotalCategory.ext_of_simple`: pivotal structures agreeing on simple objects are
  equal.
* `TauCeti.PivotalCategory.ext_of_leftDim`: pivotal structures with the same nonzero left
  dimensions on simple objects are equal.
* `TauCeti.sphericalCategory_iff_leftDim_eq_rightDim`: a pivotal structure is spherical if and
  only if its left and right dimensions agree on simple objects.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §§4.7, 7.21
* P. Etingof, D. Nikshych, V. Ostrik, *On fusion categories*, Ann. of Math. **162** (2005), §2
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [RigidCategory C]
  [IsFiniteSemisimpleCategory C]

namespace PivotalCategory

/-- In a finite semisimple rigid category, two pivotal structures whose pivotal isomorphisms agree
at every simple object are equal. -/
theorem ext_of_simple {P Q : PivotalCategory C}
    (h : ∀ (X : C) [Simple X],
      (@pivotalIsoApp C _ _ _ P X).hom = (@pivotalIsoApp C _ _ _ Q X).hom) :
    P = Q := by
  ext : 1
  refine Iso.ext (natTrans_ext_of_simple fun X _ ↦ ?_)
  rw [@pivotalIso_hom_app C _ _ _ P, @pivotalIso_hom_app C _ _ _ Q, h]

variable (k : Type w) [Field k] [IsAlgClosed k] [MonoidalPreadditive C] [Linear k C]
  [MonoidalLinear k C] [∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include k in
/-- Over an algebraically closed field, two pivotal structures `P` and `Q` on a finite semisimple
rigid category are equal if every simple object has the same left dimension for `P` as for `Q`,
and that dimension is nonzero. -/
theorem ext_of_leftDim {P Q : PivotalCategory C}
    (h : ∀ (X : C) [Simple X], @leftDim C _ _ _ P X = @leftDim C _ _ _ Q X)
    (h₀ : ∀ (X : C) [Simple X], @leftDim C _ _ _ Q X ≠ 0) :
    P = Q := by
  refine ext_of_simple fun X _ ↦ ?_
  let _ := Q
  -- The left dimension of `X` for `P` is the scalar `c` of the automorphism `ψ_X ≫ φ_X⁻¹` of `X`
  -- times the left dimension for `Q`, where `φ` and `ψ` are the pivotal isomorphisms of `P` and
  -- `Q`. The hypotheses force `c = 1`.
  have hc : endAlgEquivOfSimple k X
      (End.of ((pivotalIsoApp X).hom ≫ (@pivotalIsoApp C _ _ _ P X).inv)) = 1 := by
    refine smul_left_injective k (h₀ X) ?_
    dsimp only
    rw [one_smul, ← leftTrace_eq_smul_leftDim, ← leftDim_eq_leftTrace, h]
  rw [endAlgEquivOfSimple_apply_eq_iff, one_smul] at hc
  exact ((Iso.comp_inv_eq_id _).1 hc).symm

end PivotalCategory

section Spherical

variable (k : Type w) [Field k] [IsAlgClosed k] [PivotalCategory C] [MonoidalPreadditive C]
  [Linear k C] [MonoidalLinear k C] [∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)]

include k in
/-- Over an algebraically closed field, a pivotal structure on a finite semisimple rigid category
is spherical if and only if the left and right dimensions of every simple object agree. -/
theorem sphericalCategory_iff_leftDim_eq_rightDim :
    SphericalCategory C ↔ ∀ (X : C) [Simple X], leftDim X = rightDim X := by
  refine ⟨fun _ X _ ↦ leftDim_eq_rightDim X, fun h ↦ ⟨fun {X} f ↦ ?_⟩⟩
  obtain ⟨ι, hι, g, hg, hbg, ⟨e⟩⟩ := IsFiniteSemisimpleCategory.exists_biproduct_simples X
  -- Conjugate `f` to an endomorphism of `⨁ g` and compare the traces of its diagonal components,
  -- which are endomorphisms of simple objects.
  rw [← leftTrace_conj e, ← rightTrace_conj e, leftTrace_biproduct, rightTrace_biproduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [leftTrace_eq_smul_leftDim k, rightTrace_eq_smul_rightDim k, h]

end Spherical

end TauCeti
