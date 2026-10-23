/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Torsor.Defs
public import TauCeti.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Basic

/-!
# The torsor of pivotal structures

Let `C` be a rigid monoidal category, and write `Aut_⊗(𝟭_C)` for the commutative group
`Aut (LaxMonoidalFunctor.of (𝟭 C))` of monoidal natural automorphisms of the identity functor.
An element `u` of this group acts on a pivotal structure `φ : 𝟭 C ≅ doubleRightDualFunctor C` by
precomposition, giving the pivotal structure `u • φ` with components `u_X ≫ φ_X`; this is
again monoidal, since monoidal natural transformations compose.

Conversely, two pivotal structures `φ` and `ψ` differ by the monoidal automorphism
`φ /ₛ ψ := φ ≪≫ ψ⁻¹` of `𝟭 C`, and `(φ /ₛ ψ) • ψ = φ`. So the action is free and transitive:
whenever `C` admits a pivotal structure at all, its pivotal structures form a torsor over
`Aut_⊗(𝟭_C)`. Whether a pivotal structure exists is a separate question, so the torsor instance
carries `Nonempty (PivotalCategory C)` as a hypothesis.

This reduces classifying the pivotal structures of `C` to computing `Aut_⊗(𝟭_C)`, which for a
fusion category over an algebraically closed field of characteristic zero is the character group
of the universal grading group.

## Main declarations

* `TauCeti.PivotalCategory.instMulAction`: the action of `Aut_⊗(𝟭_C)` on pivotal structures,
  computed by `TauCeti.PivotalCategory.smul_pivotalIso`;
* `TauCeti.PivotalCategory.instSDiv`: the monoidal automorphism `φ /ₛ ψ` relating two pivotal
  structures, computed by `TauCeti.PivotalCategory.forgetAut_sdiv`;
* `TauCeti.PivotalCategory.instTorsor`: the pivotal structures of `C`, if there are any, form a
  torsor over `Aut_⊗(𝟭_C)`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §4.7
* [A. Henriques, D. Penneys, J. Tener, *Categorified trace for module tensor categories over
  braided tensor categories*](https://arxiv.org/abs/1509.02937), §2.1
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti.PivotalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- A monoidal natural automorphism `u` of `𝟭 C` acts on a pivotal structure `φ` by
precomposition: `u • φ` has pivotal isomorphism `u ≪≫ φ`. -/
noncomputable instance instSMul : SMul (Aut (LaxMonoidalFunctor.of (𝟭 C))) (PivotalCategory C) where
  smul u P :=
    { pivotalIso := (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso ≪≫ P.pivotalIso
      pivotalIso_isMonoidal := by
        have := P.pivotalIso_isMonoidal
        rw [Iso.trans_hom]
        infer_instance }

/-- The pivotal isomorphism of `u • φ` is `u ≪≫ φ`. -/
@[simp]
theorem smul_pivotalIso (u : Aut (LaxMonoidalFunctor.of (𝟭 C))) (P : PivotalCategory C) :
    (u • P).pivotalIso = (LaxMonoidalFunctor.forgetAut (𝟭 C) u).asIso ≪≫ P.pivotalIso :=
  (rfl)

/-- The monoidal natural automorphisms of `𝟭 C` act on the pivotal structures of `C`. -/
noncomputable instance instMulAction :
    MulAction (Aut (LaxMonoidalFunctor.of (𝟭 C))) (PivotalCategory C) where
  one_smul P := by
    ext : 1
    simp
  mul_smul u v P := by
    ext : 1
    -- The action is by precomposition, so `u * v` acts as `v ≪≫ u`; the group is commutative.
    rw [smul_pivotalIso, smul_pivotalIso, smul_pivotalIso, mul_comm', map_mul, Aut.mul_asIso,
      Iso.trans_assoc]

/-- The monoidal natural automorphism `φ /ₛ ψ := φ ≪≫ ψ⁻¹` of `𝟭 C` relating two pivotal
structures `φ` and `ψ` on `C`. -/
noncomputable instance instSDiv : SDiv (Aut (LaxMonoidalFunctor.of (𝟭 C))) (PivotalCategory C) where
  -- The instance argument of `isoMk` is stated for `(LaxMonoidalFunctor.of (𝟭 C)).toFunctor`,
  -- which is `𝟭 C` only up to unfolding, so it is supplied explicitly.
  sdiv P Q := Aut.of <| @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (P.pivotalIso ≪≫ Q.pivotalIso.symm)
    (by
      have := P.pivotalIso_isMonoidal
      have := Q.pivotalIso_isMonoidal
      exact (inferInstance : NatTrans.IsMonoidal (P.pivotalIso.hom ≫ Q.pivotalIso.inv)))

/-- The underlying natural automorphism of `φ /ₛ ψ` is `φ ≪≫ ψ⁻¹`. -/
@[simp]
theorem forgetAut_sdiv (P Q : PivotalCategory C) :
    LaxMonoidalFunctor.forgetAut (𝟭 C) (P /ₛ Q) = Aut.of (P.pivotalIso ≪≫ Q.pivotalIso.symm) :=
  Aut.ext (Iso.ext (LaxMonoidalFunctor.forgetAut_apply_asIso_hom _ _))

/-- **The torsor of pivotal structures.** If a rigid monoidal category admits a pivotal
structure, then the monoidal natural automorphisms of its identity functor act freely and
transitively on its pivotal structures. -/
noncomputable instance instTorsor [Nonempty (PivotalCategory C)] :
    Torsor (Aut (LaxMonoidalFunctor.of (𝟭 C))) (PivotalCategory C) where
  sdiv_smul' P Q := by
    ext : 1
    simp
  smul_sdiv' u P := by
    apply LaxMonoidalFunctor.forgetAut_injective
    ext : 1
    simp

end TauCeti.PivotalCategory
