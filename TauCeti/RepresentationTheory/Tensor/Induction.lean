/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Rep.Res
public import TauCeti.GroupTheory.Perm.WreathProduct.Monomial
public import TauCeti.RepresentationTheory.Symmetric.TensorAction.Basic

/-!
# Tensor induction of representations

Let a group `D` act linearly on an `R`-module `M`, and let `ι` be an index type. The permutation
wreath product `(ι → D) ⋊ Equiv.Perm ι` acts on the indexed tensor power `⨂[R] i : ι, M`: its
base coordinate at `i` acts on the `i`-th tensor factor, and its top permutation reindexes the
factors. On pure tensors the action is

```text
(a, σ) • (⨂ₜ i, m i) = ⨂ₜ i, a i • m (σ⁻¹ i).
```

This construction is functorial in the `D`-representation. Composing it with the monomial
homomorphism attached to a transversal of `U ≤ G` gives tensor induction from `U` to `G`.
The underlying representations and intertwining maps work over every commutative semiring. The
bundled `Rep` functors use a commutative ring, because the empty indexed tensor product need not be
an additive group over a semiring. Characteristic two is needed only later, when tensor induction
is applied to the sign-free Evens norm.

## Main definitions

* `Representation.wreathTensor`: the wreath-product representation on an indexed tensor power.
* `Rep.wreathTensorFunctor`: its functorial form on representation categories.
* `Subgroup.tensorInducedRepresentation`: tensor induction along a chosen transversal.
* `Subgroup.tensorInductionFunctor`: tensor induction along a subgroup with a chosen transversal.

## References

* L. Evens, "A generalization of the transfer map in the cohomology of groups",
  *Transactions of the American Mathematical Society* 108 (1963), §§2–5.
-/

public section

open CategoryTheory
open scoped TensorProduct

universe u v w x y z

namespace Representation

variable {R : Type u} {D : Type v} {M : Type w}
variable [CommSemiring R] [Group D] [AddCommMonoid M] [Module R M]

/-- The representation of the permutation wreath product on an indexed tensor power. The base
group acts coordinatewise and the top symmetric group permutes the tensor factors. -/
noncomputable def wreathTensor (ρ : Representation R D M) (ι : Type x) :
    Representation R (TauCeti.WreathProduct D ι) (⨂[R] _ : ι, M) where
  toFun a := PiTensorProduct.map (fun i ↦ ρ (a.left i)) ∘ₗ
    (PiTensorProduct.reindex R (fun _ : ι ↦ M) a.right).toLinearMap
  map_one' := by
    ext m
    simp
    congr 1
  map_mul' a b := by
    ext m
    simp [TauCeti.PermutationWreathProduct.mul_left]
    congr 1

/-- The wreath-product action on a pure tensor applies the base coordinate after reindexing by
the inverse of the top permutation. -/
@[simp]
theorem wreathTensor_apply_tprod (ρ : Representation R D M) (ι : Type x)
    (a : TauCeti.WreathProduct D ι) (m : ι → M) :
    ρ.wreathTensor ι a (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ ρ (a.left i) (m (a.right.symm i)) := by
  simp [wreathTensor]

/-- The base subgroup of the wreath product acts independently in each tensor factor.

This derived normal form is an explicit rewrite lemma rather than a simp lemma, since
`wreathTensor_apply_tprod` already simplifies its left-hand side. -/
theorem wreathTensor_inl_apply_tprod (ρ : Representation R D M) (ι : Type x)
    (a : ι → D) (m : ι → M) :
    ρ.wreathTensor ι (SemidirectProduct.inl a) (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ ρ (a i) (m i) := by
  rw [wreathTensor_apply_tprod]
  congr 1

/-- The top symmetric subgroup of the wreath product acts by reindexing tensor factors.

This derived normal form is an explicit rewrite lemma rather than a simp lemma, since
`wreathTensor_apply_tprod` already proves it by simplification. -/
theorem wreathTensor_inr_apply_tprod (ρ : Representation R D M) (ι : Type x)
    (σ : Equiv.Perm ι) (m : ι → M) :
    ρ.wreathTensor ι (SemidirectProduct.inr σ) (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ m (σ.symm i) := by
  simp

variable {N : Type y} [AddCommMonoid N] [Module R N]
variable {ρ : Representation R D M} {τ : Representation R D N}

/-- Applying an intertwining map in every tensor factor intertwines the corresponding
wreath-product representations. -/
noncomputable def IntertwiningMap.wreathTensor (f : ρ.IntertwiningMap τ) (ι : Type x) :
    (ρ.wreathTensor ι).IntertwiningMap (τ.wreathTensor ι) where
  toLinearMap := PiTensorProduct.map fun _ ↦ f.toLinearMap
  isIntertwining' a := by
    ext m
    simp [wreathTensor_apply_tprod, f.isIntertwining]

/-- The tensor of an intertwining map acts factorwise on pure tensors. -/
@[simp]
theorem IntertwiningMap.wreathTensor_apply_tprod (f : ρ.IntertwiningMap τ) (ι : Type x)
    (m : ι → M) :
    f.wreathTensor ι (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ f (m i) := by
  simp [IntertwiningMap.wreathTensor]

/-- Tensoring the identity intertwining map gives the identity map. -/
@[simp]
theorem IntertwiningMap.wreathTensor_id (ι : Type x) :
    (IntertwiningMap.id ρ).wreathTensor ι = IntertwiningMap.id (ρ.wreathTensor ι) := by
  apply IntertwiningMap.ext
  exact PiTensorProduct.map_id

/-- Tensoring a composite of intertwining maps gives the composite of their tensors. -/
@[simp]
theorem IntertwiningMap.wreathTensor_comp {P : Type z} [AddCommMonoid P] [Module R P]
    {υ : Representation R D P} (g : τ.IntertwiningMap υ) (f : ρ.IntertwiningMap τ)
    (ι : Type x) :
    (g.comp f).wreathTensor ι = (g.wreathTensor ι).comp (f.wreathTensor ι) := by
  apply IntertwiningMap.ext
  exact PiTensorProduct.map_comp _ _

end Representation

namespace Rep

variable (R : Type u) (D : Type v) (ι : Type x)
variable [CommRing R] [Group D]

/-- Apply an intertwining map in every factor of a wreath-product tensor representation. -/
noncomputable def wreathTensorMap {A B : Rep.{w} R D} (f : A ⟶ B) :
    Rep.of (A.ρ.wreathTensor ι) ⟶ Rep.of (B.ρ.wreathTensor ι) :=
  Rep.ofHom (Representation.IntertwiningMap.wreathTensor
    (ρ := A.ρ) (τ := B.ρ) f.hom ι)

/-- Tensoring a representation morphism applies it in every factor of a pure tensor. -/
@[simp]
theorem wreathTensorMap_hom_apply_tprod {A B : Rep.{w} R D} (f : A ⟶ B) (m : ι → A.V) :
    (wreathTensorMap R D ι f).hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun i ↦ f.hom (m i) :=
  Representation.IntertwiningMap.wreathTensor_apply_tprod f.hom ι m

/-- Tensoring an identity morphism gives the identity morphism. -/
@[simp]
theorem wreathTensorMap_id (A : Rep.{w} R D) :
    wreathTensorMap R D ι (𝟙 A) = 𝟙 (Rep.of (A.ρ.wreathTensor ι)) := by
  apply Rep.hom_ext
  exact Representation.IntertwiningMap.wreathTensor_id (R := R) (ρ := A.ρ) ι

/-- Tensoring representation morphisms preserves composition. -/
@[simp]
theorem wreathTensorMap_comp {A B C : Rep.{w} R D} (f : A ⟶ B) (g : B ⟶ C) :
    wreathTensorMap R D ι (f ≫ g) =
      wreathTensorMap R D ι f ≫ wreathTensorMap R D ι g := by
  apply Rep.hom_ext
  exact Representation.IntertwiningMap.wreathTensor_comp
    (R := R) (D := D) (ρ := A.ρ) (τ := B.ρ) (υ := C.ρ) g.hom f.hom ι

/-- Tensor power with its wreath-product action, functorial in the representation of the base
group. -/
@[expose] noncomputable def wreathTensorFunctor :
    Rep.{w} R D ⥤ Rep.{max u w x} R (TauCeti.WreathProduct D ι) where
  obj A := Rep.of (A.ρ.wreathTensor ι)
  map f := wreathTensorMap R D ι f
  map_id A := wreathTensorMap_id R D ι A
  map_comp f g := wreathTensorMap_comp R D ι f g

/-- The wreath tensor functor sends a representation to its indexed tensor power with the
wreath-product action. -/
@[simp]
theorem wreathTensorFunctor_obj (A : Rep.{w} R D) :
    (wreathTensorFunctor R D ι).obj A = Rep.of (A.ρ.wreathTensor ι) :=
  rfl

/-- The wreath tensor functor applies a representation morphism in every tensor factor. -/
@[simp]
theorem wreathTensorFunctor_map {A B : Rep.{w} R D} (f : A ⟶ B) :
    (wreathTensorFunctor R D ι).map f = wreathTensorMap R D ι f :=
  rfl

end Rep

namespace Subgroup

open TauCeti

variable {R : Type u} {G : Type v}

section

variable [CommSemiring R] [Group G]

/-- The representation obtained by tensor induction from a subgroup with a chosen transversal. -/
noncomputable def tensorInducedRepresentation (U : Subgroup G) (s : U.LeftTransversal)
    {M : Type w} [AddCommMonoid M] [Module R M] (ρ : Representation R U M) :
    Representation R G (⨂[R] _ : G ⧸ U, M) :=
  (ρ.wreathTensor (G ⧸ U)).comp (U.monomialHom s)

/-- The action of tensor induction on a pure tensor. The factor at the coset `x` is acted on by
the transversal word at `x`, while the tensor coordinates are translated by `g⁻¹`. -/
@[simp]
theorem tensorInducedRepresentation_apply_tprod (U : Subgroup G) (s : U.LeftTransversal)
    {M : Type w} [AddCommMonoid M] [Module R M] (ρ : Representation R U M)
    (g : G) (m : (G ⧸ U) → M) :
    U.tensorInducedRepresentation s ρ g (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        ρ ((U.monomialHom s g).left x) (m (g⁻¹ • x)) := by
  rw [tensorInducedRepresentation, MonoidHom.comp_apply,
    Representation.wreathTensor_apply_tprod]
  congr 1
  funext x
  rw [← Equiv.Perm.coe_inv, Subgroup.monomialHom_right_inv]

end

variable [CommRing R] [Group G]

/-- **Tensor induction from a subgroup**: tensor the representation over the left cosets and
restrict the resulting wreath-product representation along the monomial homomorphism associated
to a chosen transversal. -/
@[expose] noncomputable def tensorInductionFunctor (U : Subgroup G) (s : U.LeftTransversal) :
    Rep.{w} R U ⥤ Rep.{max u v w} R G :=
  Rep.wreathTensorFunctor R U (G ⧸ U) ⋙ Rep.resFunctor (U.monomialHom s)

/-- On objects, tensor induction is the tensor-power representation restricted along the
monomial homomorphism determined by the transversal. -/
@[simp]
theorem tensorInductionFunctor_obj (U : Subgroup G) (s : U.LeftTransversal)
    (A : Rep.{w} R U) :
    (U.tensorInductionFunctor (R := R) s).obj A =
      Rep.of (U.tensorInducedRepresentation s A.ρ) := by
  rw [tensorInductionFunctor, Functor.comp_obj, Rep.wreathTensorFunctor_obj,
    tensorInducedRepresentation]

/-- On morphisms, tensor induction applies the representation morphism in every factor of a pure
tensor. -/
@[simp]
theorem tensorInductionFunctor_map_hom_apply_tprod (U : Subgroup G) (s : U.LeftTransversal)
    {A B : Rep.{w} R U} (f : A ⟶ B) (m : G ⧸ U → A.V) :
    ((U.tensorInductionFunctor (R := R) s).map f).hom (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ f.hom (m x) :=
  Rep.wreathTensorMap_hom_apply_tprod R U (G ⧸ U) f m

end Subgroup
