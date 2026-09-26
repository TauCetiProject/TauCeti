/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.GroupLike.Evaluation
public import TauCeti.Algebra.Bialgebra.GroupLike.Map

/-!
# Extending homomorphisms of group-like elements

When group-like elements form a basis of a bialgebra over a commutative semiring, every
monoid homomorphism from its group-like elements extends uniquely to a bialgebra homomorphism.
Over a domain, linear independence follows from torsion-freeness by
`linearIndep_groupLikeVal`. Only the source needs the basis hypotheses. This is the
coordinate-algebra extension step in descent of morphisms between groups of multiplicative type.

The construction uses `TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop`
and Mathlib's `MonoidAlgebra.mapDomainBialgHom`. See Milne, *Algebraic Groups* (2017), §12.
-/

public section

open scoped TensorProduct

namespace MonoidHom

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Bialgebra R A]
  [Semiring B] [Bialgebra R B]

/-- Extend a homomorphism of group-like elements across a group-like spanning basis.
No linear independence or spanning assumption is imposed on the target. -/
noncomputable def liftBialgHom (f : GroupLike R A →* GroupLike R B)
    (hlinear : LinearIndependent R (GroupLike.val (R := R) (A := A)))
    (hA : Submodule.span R (Set.range (GroupLike.val (R := R) (A := A))) = ⊤) :
    A →ₐc[R] B :=
  (TauCeti.GroupLike.evaluationBialgHom R B).comp
    ((MonoidAlgebra.mapDomainBialgHom R f).comp
      (TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop
        R A hlinear hA).symm.toBialgHom)

/-- The extension agrees with the prescribed homomorphism on group-like elements. -/
@[simp]
theorem liftBialgHom_apply_val (f : GroupLike R A →* GroupLike R B)
    (hlinear : LinearIndependent R (GroupLike.val (R := R) (A := A)))
    (hA : Submodule.span R (Set.range (GroupLike.val (R := R) (A := A))) = ⊤)
    (x : GroupLike R A) :
    f.liftBialgHom hlinear hA x.val = (f x).val := by
  have hx : (TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop
      R A hlinear hA).symm x.val =
      MonoidAlgebra.single x 1 := by
    apply EquivLike.injective
      (TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop R A hlinear hA)
    simp only [BialgEquiv.apply_symm_apply,
      TauCeti.GroupLike.evaluationBialgEquivOfLinearIndependentOfSpanEqTop_apply,
      TauCeti.GroupLike.evaluationBialgHom_single, one_smul]
  simp [liftBialgHom, hx]

/-- Restricting the extension to group-like elements recovers the given homomorphism. -/
@[simp]
theorem groupLikeMap_liftBialgHom (f : GroupLike R A →* GroupLike R B)
    (hlinear : LinearIndependent R (GroupLike.val (R := R) (A := A)))
    (hA : Submodule.span R (Set.range (GroupLike.val (R := R) (A := A))) = ⊤) :
    TauCeti.GroupLike.map (f.liftBialgHom hlinear hA) = f := by
  ext x
  simp only [TauCeti.GroupLike.val_map, liftBialgHom_apply_val]

/-- A bialgebra morphism extending the prescribed group-like homomorphism is unique. -/
theorem liftBialgHom_unique (f : GroupLike R A →* GroupLike R B)
    (hlinear : LinearIndependent R (GroupLike.val (R := R) (A := A)))
    (hA : Submodule.span R (Set.range (GroupLike.val (R := R) (A := A))) = ⊤)
    (g : A →ₐc[R] B) (hg : ∀ x : GroupLike R A, g x.val = (f x).val) :
    g = f.liftBialgHom hlinear hA := by
  have h : (g : A →ₗ[R] B) = (f.liftBialgHom hlinear hA : A →ₗ[R] B) := by
    apply LinearMap.ext_on_range hA
    intro x
    simpa only [BialgHom.coe_toLinearMap, liftBialgHom_apply_val] using hg x
  exact BialgHom.ext (LinearMap.congr_fun h)

end MonoidHom
