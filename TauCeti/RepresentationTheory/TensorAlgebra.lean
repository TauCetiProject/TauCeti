/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Representations on tensor algebras

A representation on `M` extends multiplicatively to its tensor algebra. The extension is
available both as a representation and as a locally installed `MulSemiringAction`, commuting
with the ground scalars. In particular it supplies the action needed to form the tensor
skew monoid algebra. No finiteness, field, or invertibility-of-group-order assumption is needed.

Intertwining maps extend to intertwining maps of tensor algebras. Faithfulness is detected
on the degree-one generators. For a group, the algebra automorphisms and their inverses are
available from Mathlib's `MulSemiringAction.toAlgAut` after installing the action and its
`SMulCommClass`.

The construction uses Mathlib's `TensorAlgebra.lift`, following the existing
`Representation.symmetricAlgebra` interface.
-/

public section

namespace Representation

variable {R G M : Type*} [CommSemiring R] [Monoid G] [AddCommMonoid M] [Module R M]
variable (ρ : Representation R G M)

/-- The multiplicative extension of a representation to its tensor algebra. -/
noncomputable def tensorAlgebra : Representation R G (TensorAlgebra R M) where
  toFun g := (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ g))).toLinearMap
  map_one' := by
    have h : TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ 1)) =
        AlgHom.id R (TensorAlgebra R M) := by
      ext m
      simp
    simpa only [AlgHom.toLinearMap_id, Module.End.one_eq_id] using
      congrArg AlgHom.toLinearMap h
  map_mul' g h := by
    have he : TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ (g * h))) =
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ g))).comp
          (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ h))) := by
      ext m
      simp
    simpa only [AlgHom.comp_toLinearMap, Module.End.mul_eq_comp] using
      congrArg AlgHom.toLinearMap he

/-- The tensor-algebra action is the universal multiplicative extension of `ρ g`. -/
@[simp]
theorem tensorAlgebra_apply (g : G) (p : TensorAlgebra R M) :
    ρ.tensorAlgebra g p = TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ g)) p := (rfl)

/-- Pulling back a representation commutes with extending it to the tensor algebra. -/
theorem tensorAlgebra_comp_apply {G' : Type*} [Monoid G'] (f : G' →* G) (g : G') :
    Representation.tensorAlgebra (ρ.comp f) g = ρ.tensorAlgebra (f g) := by
  ext p
  simp

/-- The induced action by semiring endomorphisms, for local installation with `letI`.
It is not a global instance, since the original representation cannot be inferred. -/
noncomputable abbrev tensorAlgebraMulSemiringAction :
    MulSemiringAction G (TensorAlgebra R M) where
  smul g p := ρ.tensorAlgebra g p
  one_smul := LinearMap.congr_fun (map_one ρ.tensorAlgebra)
  mul_smul g h := LinearMap.congr_fun (map_mul ρ.tensorAlgebra g h)
  smul_zero g := map_zero (ρ.tensorAlgebra g)
  smul_add g := map_add (ρ.tensorAlgebra g)
  smul_one g := (ρ.tensorAlgebra_apply g 1).trans (map_one _)
  smul_mul g p q := (ρ.tensorAlgebra_apply g (p * q)).trans <| (map_mul _ p q).trans <|
    congrArg₂ (· * ·) (ρ.tensorAlgebra_apply g p).symm (ρ.tensorAlgebra_apply g q).symm

/-- The locally installed action agrees with the tensor-algebra representation. -/
theorem tensorAlgebraMulSemiringAction_smul (g : G) (p : TensorAlgebra R M) :
    letI := ρ.tensorAlgebraMulSemiringAction
    g • p = ρ.tensorAlgebra g p := (rfl)

/-- The tensor-algebra action commutes with ground scalars. -/
theorem smulCommClass_tensorAlgebraMulSemiringAction :
    letI := ρ.tensorAlgebraMulSemiringAction
    SMulCommClass G R (TensorAlgebra R M) :=
  letI := ρ.tensorAlgebraMulSemiringAction
  ⟨fun g r p ↦ map_smul (ρ.tensorAlgebra g) r p⟩

/-- The induced action is faithful if and only if the original representation is injective. -/
theorem faithfulSMul_tensorAlgebraMulSemiringAction_iff :
    letI := ρ.tensorAlgebraMulSemiringAction
    FaithfulSMul G (TensorAlgebra R M) ↔ Function.Injective ρ := by
  let := ρ.tensorAlgebraMulSemiringAction
  refine ⟨fun h g k hg ↦ h.eq_of_smul_eq_smul fun p ↦ ?_, fun hρ ↦
    ⟨fun h ↦ hρ <| LinearMap.ext fun m ↦ (TensorAlgebra.ι_inj R _ _).mp ?_⟩⟩
  · simp [tensorAlgebraMulSemiringAction_smul, hg]
  · simpa [tensorAlgebraMulSemiringAction_smul] using h (TensorAlgebra.ι R m)

variable {ρ} in
/-- A linear intertwiner extends multiplicatively to an intertwiner of tensor algebras. -/
theorem IsIntertwiningMap.tensorAlgebraMap {N : Type*} [AddCommMonoid N] [Module R N]
    {σ : Representation R G N} {f : M →ₗ[R] N} (hf : IsIntertwiningMap ρ σ f) :
    IsIntertwiningMap ρ.tensorAlgebra σ.tensorAlgebra
      (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f)).toLinearMap := by
  constructor
  intro g p
  have h : (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f)).comp
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ g))) =
      (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (σ g))).comp
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f)) := by
    ext m
    simp [hf.1 g m]
  exact DFunLike.congr_fun h p

end Representation
