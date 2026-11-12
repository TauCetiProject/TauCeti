/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.BaseChange
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Projection
import TauCeti.RepresentationTheory.Induction.BaseChange
import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# Scalar extension of group-algebra Grothendieck rings

For a field extension `k → K` and a finite monoid `G`, scalar extension gives a ring
homomorphism `G₀(k[G]) → G₀(K[G])`. The product here is tensor product over the coefficient
field with diagonal action, rather than tensor product over the group algebra.

`groupAlgebraBaseChangeK0` transports `baseChangeK0` along `fdRepK0RingEquiv`. Its formula on
representation classes characterizes it without unfolding the equivalences. Scalar extension
is the identity over the original field and is transitive along field towers. It commutes
with restriction along monoid homomorphisms, induction from subgroups of finite groups, and
permutation classes. Thus relations between induced or permutation classes can be transported
to an extension field, including a splitting field, in any characteristic.

The induction compatibility uses `Rep.indBaseChangeEquiv`, the scalar-extension comparison
on the finite coset model of induction.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977),
  Part III, §14.1 and §15.5.
-/

public section

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

namespace TauCeti

universe u

variable {k : Type u} (K : Type u) [Field k] [Field K] [Algebra k K]

section Monoid

variable {G : Type u} [Monoid G] [Finite G]

/-- Extension of the coefficient field on the exact Grothendieck ring of a finite
monoid algebra. On representation classes it sends `[V]` to `[K ⊗[k] V]`. -/
noncomputable def groupAlgebraBaseChangeK0 :
    ExactK0 (finiteModulesExactStructure k[G]) →+*
      ExactK0 (finiteModulesExactStructure K[G]) :=
  (fdRepK0RingEquiv K G).toRingHom.comp
    ((baseChangeK0 K).comp (fdRepK0RingEquiv k G).symm.toRingHom)

/-- Scalar extension of modules agrees with scalar extension of representations under the
representation/module dictionary. -/
@[simp]
theorem groupAlgebraBaseChangeK0_fdRepK0RingEquiv
    (x : ExactK0 (ExactStructure.abelian (FDRep k G))) :
    groupAlgebraBaseChangeK0 K (fdRepK0RingEquiv k G x) =
      fdRepK0RingEquiv K G (baseChangeK0 K x) := by
  simp [groupAlgebraBaseChangeK0]

/-- Scalar extension takes the class of the module of `ρ` to the class of the module
of its scalar extension. -/
@[simp]
theorem groupAlgebraBaseChangeK0_of_asModule {V : Type u} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (ρ : Representation k G V) :
    letI : Module.Finite k[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    letI : Module.Finite K[G] (ρ.baseChange K).asModule :=
      Module.Finite.of_restrictScalars_finite K K[G] _
    groupAlgebraBaseChangeK0 K (ExactK0.of (FGModuleCat.of k[G] ρ.asModule)) =
      ExactK0.of (FGModuleCat.of K[G] (ρ.baseChange K).asModule) := by
  have h := groupAlgebraBaseChangeK0_fdRepK0RingEquiv K (ExactK0.of (FDRep.of ρ))
  simpa only [baseChangeK0_of, fdRepK0RingEquiv_of, FDRep.of_ρ'] using h

/-- Extending scalars from a field to itself is the identity. -/
@[simp]
theorem groupAlgebraBaseChangeK0_id :
    groupAlgebraBaseChangeK0 (k := k) k (G := G) = RingHom.id _ := by
  ext x
  obtain ⟨y, rfl⟩ := (fdRepK0RingEquiv k G).surjective x
  simp

/-- Extending scalars along a tower is the composite of the two scalar extensions. -/
theorem groupAlgebraBaseChangeK0_comp (L : Type u) [Field L] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] :
    (groupAlgebraBaseChangeK0 (k := K) L (G := G)).comp
        (groupAlgebraBaseChangeK0 (k := k) K) =
      groupAlgebraBaseChangeK0 (k := k) L := by
  ext x
  obtain ⟨y, rfl⟩ := (fdRepK0RingEquiv k G).surjective x
  simp only [RingHom.comp_apply, groupAlgebraBaseChangeK0_fdRepK0RingEquiv]
  exact congrArg (fdRepK0RingEquiv L G) (DFunLike.congr_fun (baseChangeK0_comp K L) y)

/-- Scalar extension preserves the class of a finite permutation module. -/
@[simp]
theorem groupAlgebraBaseChangeK0_permK0 (X : Type u) [MulAction G X] [Finite X] :
    groupAlgebraBaseChangeK0 K (permK0 k G X) = permK0 K G X := by
  have h := congrArg (fdRepK0RingEquiv K G)
    (baseChangeK0_of_ofMulAction (k := k) K (G := G) X)
  rw [← groupAlgebraBaseChangeK0_fdRepK0RingEquiv] at h
  simp only [fdRepK0RingEquiv_of, FDRep.of_ρ'] at h
  simpa only [permK0_def] using h

variable {H : Type u} [Monoid H] [Finite H]

/-- Scalar extension commutes with restriction along a homomorphism of finite monoids. -/
theorem groupAlgebraBaseChangeK0_comp_resK0 (φ : H →* G) :
    (groupAlgebraBaseChangeK0 (k := k) K (G := H)).toAddMonoidHom.comp (resK0 k φ) =
      (resK0 K φ).comp (groupAlgebraBaseChangeK0 (k := k) K).toAddMonoidHom := by
  apply (AddMonoidHom.cancel_right (f := (fdRepK0RingEquiv k G).toAddMonoidHom)
    (fdRepK0RingEquiv k G).surjective).mp
  apply ExactK0.hom_ext
  intro V
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    resK0_fdRepK0RingEquiv_of,
    groupAlgebraBaseChangeK0_fdRepK0RingEquiv, baseChangeK0_of]
  apply congrArg (fdRepK0RingEquiv K H)
  -- The restricted object has the same carrier, but rewriting its action inside
  -- `baseChange` retains the old dependent carrier. Convert the whole class instead.
  convert congrArg (fun ρ : Representation K H (K ⊗[k] V) => ExactK0.of (FDRep.of ρ))
    (_root_.Representation.baseChange_comp (A := K) V.ρ φ) using 1
  · rfl
  · rw [← FDRep.of_ρ_eq_self
      ((Action.res (FGModuleCat K) φ).obj (FDRep.of (Representation.baseChange K V.ρ)))]
    rfl

/-- Restricting a class and extending scalars gives the restriction of its scalar extension. -/
@[simp]
theorem groupAlgebraBaseChangeK0_resK0 (φ : H →* G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    groupAlgebraBaseChangeK0 K (resK0 k φ x) =
      resK0 K φ (groupAlgebraBaseChangeK0 K x) :=
  DFunLike.congr_fun (groupAlgebraBaseChangeK0_comp_resK0 K φ) x

end Monoid

section Group

variable {G : Type u} [Group G] [Finite G] (S : Subgroup G)

/-- Scalar extension commutes with induction from a subgroup of a finite group. -/
theorem groupAlgebraBaseChangeK0_comp_indK0 :
    (groupAlgebraBaseChangeK0 (k := k) K (G := G)).toAddMonoidHom.comp (indK0 k S) =
      (indK0 K S).comp (groupAlgebraBaseChangeK0 (k := k) K).toAddMonoidHom := by
  apply (AddMonoidHom.cancel_right (f := (fdRepK0RingEquiv k S).toAddMonoidHom)
    (fdRepK0RingEquiv k S).surjective).mp
  apply ExactK0.hom_ext
  intro V
  simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    indK0_fdRepK0RingEquiv_of,
    groupAlgebraBaseChangeK0_fdRepK0RingEquiv, baseChangeK0_of]
  apply congrArg (fdRepK0RingEquiv K G)
  let e : (Representation.baseChange K (indFDRep V).ρ).Equiv
      (indFDRep (FDRep.of (Representation.baseChange K V.ρ))).ρ :=
    ((indFDRepForgetEquiv V).baseChange K).trans
      ((Rep.indBaseChangeEquiv (A := K) ((forget₂ (FDRep k S) (Rep k S)).obj V)).trans
        (indFDRepForgetEquiv (FDRep.of (Representation.baseChange K V.ρ))).symm)
  refine ExactK0.of_congr (e.toLinearEquiv.toFDRepIso fun g x => ?_)
  simpa only [FDRep.of_ρ', _root_.Representation.Equiv.toLinearEquiv_apply] using
    (_root_.Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g x)

/-- Inducing a class and extending scalars gives the induction of its scalar extension. -/
@[simp]
theorem groupAlgebraBaseChangeK0_indK0 (x : ExactK0 (finiteModulesExactStructure k[S])) :
    groupAlgebraBaseChangeK0 K (indK0 k S x) =
      indK0 K S (groupAlgebraBaseChangeK0 K x) :=
  DFunLike.congr_fun (groupAlgebraBaseChangeK0_comp_indK0 K S) x

end Group

end TauCeti
