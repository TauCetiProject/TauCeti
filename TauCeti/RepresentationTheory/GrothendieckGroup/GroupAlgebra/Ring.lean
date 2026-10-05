/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Equivalence
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Restriction
-- Non-public: `Action.resTensorator`, restriction commutes with the tensor product.
import TauCeti.CategoryTheory.Action.Monoidal

/-!
# The ring structure on the Grothendieck group of a group algebra

Let `k` be a field and `G` a finite monoid. The exact Grothendieck group
`G₀(k[G]) = ExactK0 (finiteModulesExactStructure k[G])` of finitely generated `k[G]`-modules is
the Grothendieck group in which restriction (`TauCeti.resK0`), induction (`TauCeti.indK0`) and
permutation classes (`TauCeti.permK0`) live. This file makes it a commutative ring, with

`[V] * [W] = [V ⊗ W]`  and  `1 = [k]`,

the tensor product of representations over `k` with the diagonal action, and the trivial line.

The tensor product is a structure on representations rather than on `k[G]`-modules, so the ring
structure is the one of the exact Grothendieck ring of `FDRep k G` (`TauCeti.ExactK0.instCommRing`
with `TauCeti.isMonoidal_abelian_fdRep`), carried along the exact equivalence
`TauCeti.fdRepEquivalence : FDRep k G ≌ FGModuleCat k[G]`. The resulting identification of the two
Grothendieck rings is `TauCeti.fdRepK0RingEquiv`, sending the class of a representation `V` to the
class of its group-algebra module `Representation.asModule V.ρ`. The additive structure of
`G₀(k[G])` is left untouched: only the multiplication and the unit are new.

Restriction along a monoid homomorphism is then multiplicative and unital (`TauCeti.resK0_mul`,
`TauCeti.resK0_one`), because restricting a tensor product of representations is tensoring the
restrictions.

## Implementation notes

When `G` is commutative, `k[G]` is a commutative ring and `k[G]`-modules also have a tensor
product over `k[G]`. That is not the product used here: the product of `G₀(k[G])` is the tensor
product over `k` with the diagonal action of `G`, the one of representations.

## Main definitions

* `TauCeti.fdRepK0RingEquiv`: the exact Grothendieck ring of `FDRep k G` is isomorphic to
  `G₀(k[G])`.
* `TauCeti.instCommRingExactK0MonoidAlgebra`: the commutative ring structure on `G₀(k[G])`.

## Main results

* `TauCeti.fdRepK0RingEquiv_of`: the class of a representation goes to the class of its
  group-algebra module.
* `TauCeti.of_asModule_mul_of_asModule`: the product of the classes of two representations is the
  class of their tensor product.
* `TauCeti.exactK0_one_eq_of_trivial`: the unit is the class of the trivial line.
* `TauCeti.resK0_mul` and `TauCeti.resK0_one`: restriction is a ring homomorphism.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §14.1, for the
  ring `R_k(G)` of a finite group over a field of arbitrary characteristic.
-/

public section

open CategoryTheory MonoidalCategory
open scoped MonoidAlgebra

namespace TauCeti

universe u

section Ring

variable (k G : Type u) [Field k] [Monoid G] [Finite G]

/-- The multiplication of `G₀(k[G])`: the tensor product of representations, carried along the
equivalence `TauCeti.fdRepEquivalence`. It is characterised by
`TauCeti.of_asModule_mul_of_asModule`. -/
noncomputable instance : Mul (ExactK0 (finiteModulesExactStructure k[G])) where
  mul x y :=
    let e := ExactK0.mapEquiv (fdRepEquivalence k G)
      (isConflationExact_fdRepEquivalence_functor k G)
      (isConflationExact_fdRepEquivalence_inverse k G)
    e (e.symm x * e.symm y)

/-- The unit of `G₀(k[G])`: the class of the trivial line
(`TauCeti.exactK0_one_eq_of_trivial`). -/
noncomputable instance : One (ExactK0 (finiteModulesExactStructure k[G])) where
  one := ExactK0.mapEquiv (fdRepEquivalence k G) (isConflationExact_fdRepEquivalence_functor k G)
    (isConflationExact_fdRepEquivalence_inverse k G) 1

/-- **The Grothendieck ring of `FDRep k G` is `G₀(k[G])`.** The exact Grothendieck group of the
abelian category of finite-dimensional representations is identified with the exact Grothendieck
group of finitely generated `k[G]`-modules by the equivalence `TauCeti.fdRepEquivalence`, and this
identification is multiplicative for the tensor product of representations. -/
noncomputable def fdRepK0RingEquiv :
    ExactK0.{u} (ExactStructure.abelian (FDRep k G)) ≃+*
      ExactK0 (finiteModulesExactStructure k[G]) where
  __ := ExactK0.mapEquiv (fdRepEquivalence k G) (isConflationExact_fdRepEquivalence_functor k G)
    (isConflationExact_fdRepEquivalence_inverse k G)
  map_mul' x y := by
    -- The product on the right is, by definition, the transported product.
    change _ = ExactK0.mapEquiv _ _ _ (_ * _)
    simp

variable {k G}

/-- `TauCeti.fdRepK0RingEquiv` sends the class of a representation to the class of its
group-algebra module. -/
@[simp]
theorem fdRepK0RingEquiv_of (V : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    fdRepK0RingEquiv k G (ExactK0.of V) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.asModule V.ρ)) :=
  (ExactK0.mapEquiv_of (fdRepEquivalence k G) _ _ V).trans
    (ExactK0.of_congr (ObjectProperty.isoMk _ (eqToIso (fdRepEquivalence_functor_obj_obj k G V))))

/-- The multiplication of `G₀(k[G])` is the transported multiplication of the Grothendieck ring of
`FDRep k G`. -/
private theorem mul_def (x y : ExactK0 (finiteModulesExactStructure k[G])) :
    x * y = fdRepK0RingEquiv k G ((fdRepK0RingEquiv k G).symm x * (fdRepK0RingEquiv k G).symm y) :=
  (rfl)

/-- The unit of `G₀(k[G])` is the transported unit of the Grothendieck ring of `FDRep k G`. -/
private theorem one_def :
    (1 : ExactK0 (finiteModulesExactStructure k[G])) = fdRepK0RingEquiv k G 1 :=
  (rfl)

variable (k G) in
/-- **`G₀(k[G])` is a commutative ring** under the tensor product of representations, with unit
the class of the trivial line. Its additive group is the exact Grothendieck group of finitely
generated `k[G]`-modules; the ring axioms are those of the Grothendieck ring of `FDRep k G`, read
through `TauCeti.fdRepK0RingEquiv`. -/
noncomputable instance instCommRingExactK0MonoidAlgebra :
    CommRing (ExactK0 (finiteModulesExactStructure k[G])) where
  __ := (inferInstance : AddCommGroup (ExactK0 (finiteModulesExactStructure k[G])))
  left_distrib x y z := by simp only [mul_def, map_add, mul_add]
  right_distrib x y z := by simp only [mul_def, map_add, add_mul]
  zero_mul x := by simp only [mul_def, map_zero, zero_mul]
  mul_zero x := by simp only [mul_def, map_zero, mul_zero]
  mul_assoc x y z := by simp only [mul_def, RingEquiv.symm_apply_apply, mul_assoc]
  one_mul x := by simp only [mul_def, one_def, RingEquiv.symm_apply_apply, one_mul,
    RingEquiv.apply_symm_apply]
  mul_one x := by simp only [mul_def, one_def, RingEquiv.symm_apply_apply, mul_one,
    RingEquiv.apply_symm_apply]
  mul_comm x y := by rw [mul_def, mul_def, mul_comm]

/-- **The product of two classes is the class of the tensor product**: in `G₀(k[G])`,
`[V] * [W] = [V ⊗ W]` for finite-dimensional representations `V` and `W`. -/
@[simp]
theorem of_asModule_mul_of_asModule (V W : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    letI : Module.Finite k[G] (Representation.asModule W.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    letI : Module.Finite k[G] (Representation.asModule (V ⊗ W).ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    (ExactK0.of (FGModuleCat.of k[G] (Representation.asModule V.ρ)) :
        ExactK0 (finiteModulesExactStructure k[G])) *
        ExactK0.of (FGModuleCat.of k[G] (Representation.asModule W.ρ)) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.asModule (V ⊗ W).ρ)) := by
  rw [← fdRepK0RingEquiv_of, ← fdRepK0RingEquiv_of, ← fdRepK0RingEquiv_of, ← map_mul,
    ExactK0.of_mul_of]

/-- **The unit is the class of the trivial line**: in `G₀(k[G])`, `1 = [k]`. -/
theorem exactK0_one_eq_of_trivial :
    letI : Module.Finite k[G] (Representation.trivial k G k).asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    (1 : ExactK0 (finiteModulesExactStructure k[G])) =
      ExactK0.of (FGModuleCat.of k[G] (Representation.trivial k G k).asModule) := by
  rw [← map_one (fdRepK0RingEquiv k G), ExactK0.one_def, fdRepK0RingEquiv_of]
  -- The tensor unit of `FDRep k G` is `FDRep.of (Representation.trivial k G k)` by definition.
  rfl

end Ring

section Restriction

variable {k G H : Type u} [Field k] [Monoid G] [Monoid H] [Finite G] [Finite H]

/-- **Restriction of the class of a representation**, read through `TauCeti.fdRepK0RingEquiv`: it
is the class of the restricted representation `Action.res φ V`. -/
theorem resK0_fdRepK0RingEquiv_of (φ : H →* G) (V : FDRep k G) :
    resK0 k φ (fdRepK0RingEquiv k G (ExactK0.of V)) =
      fdRepK0RingEquiv k H (ExactK0.of ((Action.res (FGModuleCat k) φ).obj V)) := by
  rw [fdRepK0RingEquiv_of, fdRepK0RingEquiv_of, resK0_of_asModule]
  -- The restricted representation is the composite `V.ρ ∘ φ` by definition.
  rfl

/-- **Restriction is multiplicative**: restricting the class of a tensor product is the product of
the restricted classes. -/
@[simp]
theorem resK0_mul (φ : H →* G) (x y : ExactK0 (finiteModulesExactStructure k[G])) :
    resK0 k φ (x * y) = resK0 k φ x * resK0 k φ y := by
  obtain ⟨a, rfl⟩ := (fdRepK0RingEquiv k G).surjective x
  obtain ⟨b, rfl⟩ := (fdRepK0RingEquiv k G).surjective y
  induction a using ExactK0.induction_on with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, add_mul, ha, ha']
  | neg a ha => simp only [map_neg, neg_mul, ha]
  | of V =>
    induction b using ExactK0.induction_on with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, mul_add, hb, hb']
    | neg b hb => simp only [map_neg, mul_neg, hb]
    | of W =>
      rw [← map_mul, ExactK0.of_mul_of, resK0_fdRepK0RingEquiv_of, resK0_fdRepK0RingEquiv_of,
        resK0_fdRepK0RingEquiv_of, ← map_mul, ExactK0.of_mul_of]
      exact congrArg _ (ExactK0.of_congr (Action.resTensorator _ φ V W).symm)

/-- **Restriction is unital**: it sends the class of the trivial line to the class of the trivial
line. -/
@[simp]
theorem resK0_one (φ : H →* G) : resK0 k φ 1 = 1 := by
  rw [exactK0_one_eq_of_trivial, exactK0_one_eq_of_trivial, resK0_of_trivial]

end Restriction

end TauCeti
