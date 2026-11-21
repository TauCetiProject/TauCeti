/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.TensorAlgebra
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Representations on exterior algebras

A representation on `M` extends to its exterior algebra by algebra endomorphisms. The
locally installed action commutes with the ground scalars, so it defines the exterior
skew monoid algebra. For group actions, Mathlib's `MulSemiringAction.toAlgAut` supplies
the corresponding algebra automorphisms. The construction works over any commutative ring.

The exterior-algebra map of an intertwiner is an intertwiner. The canonical quotient from
the tensor algebra to the exterior algebra is equivariant, making the two multiplicative
extensions compatible rather than unrelated actions.

The construction uses Mathlib's `ExteriorAlgebra.map` and follows the existing
`Representation.symmetricAlgebra` interface.
-/

public section

namespace Representation

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommGroup M] [Module R M]
variable (ρ : Representation R G M)

/-- The multiplicative extension of a representation to its exterior algebra. -/
def exteriorAlgebra : Representation R G (ExteriorAlgebra R M) where
  toFun g := (ExteriorAlgebra.map (ρ g)).toLinearMap
  map_one' := by
    rw [ρ.map_one, Module.End.one_eq_id, ExteriorAlgebra.map_id]
    rfl
  map_mul' g h := by
    rw [ρ.map_mul, Module.End.mul_eq_comp, ← ExteriorAlgebra.map_comp_map]
    rfl

/-- The exterior-algebra action is the algebra map induced by `ρ g`. -/
@[simp]
theorem exteriorAlgebra_apply (g : G) (p : ExteriorAlgebra R M) :
    ρ.exteriorAlgebra g p = ExteriorAlgebra.map (ρ g) p := (rfl)

/-- Pulling back a representation commutes with extending it to the exterior algebra. -/
theorem exteriorAlgebra_comp_apply {G' : Type*} [Monoid G'] (f : G' →* G) (g : G') :
    Representation.exteriorAlgebra (ρ.comp f) g = ρ.exteriorAlgebra (f g) := by
  ext p
  simp

/-- The induced action by semiring endomorphisms, for local installation with `letI`.
It is not a global instance, since the original representation cannot be inferred. -/
abbrev exteriorAlgebraMulSemiringAction :
    MulSemiringAction G (ExteriorAlgebra R M) where
  smul g p := ρ.exteriorAlgebra g p
  one_smul := LinearMap.congr_fun (map_one ρ.exteriorAlgebra)
  mul_smul g h := LinearMap.congr_fun (map_mul ρ.exteriorAlgebra g h)
  smul_zero g := map_zero (ρ.exteriorAlgebra g)
  smul_add g := map_add (ρ.exteriorAlgebra g)
  smul_one g := (ρ.exteriorAlgebra_apply g 1).trans (map_one _)
  smul_mul g p q := (ρ.exteriorAlgebra_apply g (p * q)).trans <| (map_mul _ p q).trans <|
    congrArg₂ (· * ·) (ρ.exteriorAlgebra_apply g p).symm (ρ.exteriorAlgebra_apply g q).symm

/-- The locally installed action agrees with the exterior-algebra representation. -/
theorem exteriorAlgebraMulSemiringAction_smul (g : G) (p : ExteriorAlgebra R M) :
    letI := ρ.exteriorAlgebraMulSemiringAction
    g • p = ρ.exteriorAlgebra g p := (rfl)

/-- The exterior-algebra action commutes with ground scalars. -/
theorem smulCommClass_exteriorAlgebraMulSemiringAction :
    letI := ρ.exteriorAlgebraMulSemiringAction
    SMulCommClass G R (ExteriorAlgebra R M) :=
  letI := ρ.exteriorAlgebraMulSemiringAction
  ⟨fun g r p ↦ map_smul (ρ.exteriorAlgebra g) r p⟩

/-- The induced action is faithful if and only if the original representation is injective. -/
theorem faithfulSMul_exteriorAlgebraMulSemiringAction_iff :
    letI := ρ.exteriorAlgebraMulSemiringAction
    FaithfulSMul G (ExteriorAlgebra R M) ↔ Function.Injective ρ := by
  let := ρ.exteriorAlgebraMulSemiringAction
  refine ⟨fun h g k hg ↦ h.eq_of_smul_eq_smul fun p ↦ ?_, fun hρ ↦
    ⟨fun h ↦ hρ <| LinearMap.ext fun m ↦ (ExteriorAlgebra.ι_inj R _ _).mp ?_⟩⟩
  · simp [exteriorAlgebraMulSemiringAction_smul, hg]
  · simpa [exteriorAlgebraMulSemiringAction_smul] using h (ExteriorAlgebra.ι R m)

variable {ρ} in
/-- The exterior-algebra map of a linear intertwiner intertwines the induced actions. -/
theorem IsIntertwiningMap.exteriorAlgebraMap {N : Type*} [AddCommGroup N] [Module R N]
    {σ : Representation R G N} {f : M →ₗ[R] N} (hf : IsIntertwiningMap ρ σ f) :
    IsIntertwiningMap ρ.exteriorAlgebra σ.exteriorAlgebra
      (ExteriorAlgebra.map f).toLinearMap := by
  constructor
  intro g p
  have h : (ExteriorAlgebra.map f).comp (ExteriorAlgebra.map (ρ g)) =
      (ExteriorAlgebra.map (σ g)).comp (ExteriorAlgebra.map f) := by
    rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map]
    congr 1
    exact LinearMap.ext (hf.1 g)
  exact DFunLike.congr_fun h p

/-- The canonical quotient from the tensor algebra to the exterior algebra is equivariant. -/
theorem isIntertwiningMap_tensorAlgebraLift_exteriorAlgebra :
    IsIntertwiningMap ρ.tensorAlgebra ρ.exteriorAlgebra
      (TensorAlgebra.lift R (ExteriorAlgebra.ι R)).toLinearMap := by
  constructor
  intro g p
  have h : (TensorAlgebra.lift R (ExteriorAlgebra.ι R)).comp
        (TensorAlgebra.lift R ((TensorAlgebra.ι R).comp (ρ g))) =
      (ExteriorAlgebra.map (ρ g)).comp (TensorAlgebra.lift R (ExteriorAlgebra.ι R)) := by
    ext m
    simp
  simpa only [tensorAlgebra_apply, exteriorAlgebra_apply, AlgHom.comp_apply,
    AlgHom.toLinearMap_apply] using DFunLike.congr_fun h p

end Representation
