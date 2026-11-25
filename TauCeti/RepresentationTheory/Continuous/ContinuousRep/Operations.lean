/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.Character.Twist
public import TauCeti.RepresentationTheory.Continuous.ContinuousRep
public import TauCeti.RepresentationTheory.LinHom.Basic

/-!
# Operations on jointly continuous representations

This file builds the standard operations on jointly continuous representations
`TauCeti.ContinuousRep Γ A M`: restriction along a continuous homomorphism, tensor products with
the diagonal action, the Hom representation `g • f = σ g ∘ f ∘ ρ g⁻¹`, and the twist by a
continuous character. Together with the contragredient `TauCeti.ContinuousRep.dual` and extension
of scalars `TauCeti.ContinuousRep.baseChange` of the defining file, these are the operations
on Galois representations used throughout the arithmetic theory.

Each operation is jointly continuous for the module topology on its carrier. For the tensor
product, the pure tensors of finite generating families span `M ⊗[A] N`, and their orbits are
continuous because every bilinear map out of a product of modules with their module topologies is
continuous once one factor is finite. For the Hom representation, a finite dual basis of the
finite projective module `M` writes every `f : M →ₗ[A] N` as `∑ j, φ j ⬝ f (b j)`, and the
coefficients of `σ g ∘ f ∘ ρ g⁻¹` are continuous in `(g, f)`. For the twist, the scalar `χ g`
depends continuously on `g`.

The comparisons between the operations hold for finite projective carriers: the evaluation
isomorphism `M ≅ M^∨∨`, the isomorphism `M^∨ ⊗ N ≅ Hom_A(M, N)` (Mathlib's
`dualTensorHomEquiv`, as the equivalence of representations
`Representation.Equiv.dualTensorHomOfProjective`), and the
identification of the twist `M(χ)` with the tensor product `M ⊗ A(χ)`. Twisting by `1` does
nothing and twisting twice multiplies the characters. The invariants of the Hom representation are
the morphisms of continuous representations. Evaluation `M^∨ ⊗ M → A` is a morphism to the trivial
representation, and the scalar map `A → Hom_A(M, M)`, `a ↦ a • id`, and coevaluation
`A → M ⊗ M^∨` are morphisms from it.
Restriction is functorial and commutes with products, tensor products, Hom, the contragredient,
twists and character lines.

## Main definitions

* `TauCeti.ContinuousRep.res`: restriction along a continuous monoid homomorphism `Γ' →ₜ* Γ`.
* `TauCeti.ContinuousRep.tprod`: the tensor product `ρ ⊗ σ` on `M ⊗[A] N`.
* `TauCeti.ContinuousRep.tprodCommIso`: the braiding `M ⊗ N ≅ N ⊗ M`.
* `TauCeti.ContinuousRep.linHom`: the Hom representation on `M →ₗ[A] N`, using
  `Representation.linHom`.
* `TauCeti.ContinuousRep.twist`: the twist `M(χ)` by a continuous character, using
  `Representation.charTwist`.
* `TauCeti.ContinuousRep.dualDualIso`: `M ≅ M^∨∨` for finite projective `M`.
* `TauCeti.ContinuousRep.dualTensorIsoHom`: `M^∨ ⊗ N ≅ Hom_A(M, N)` for finite projective `M`.
* `TauCeti.ContinuousRep.tprodOfCharacterIsoTwist`: `M ⊗ A(χ) ≅ M(χ)`.
* `TauCeti.ContinuousRep.invariantsLinHomEquiv`: the invariants of `Hom_A(M, N)` are the morphisms
  `ρ ⟶ σ` of continuous representations.
* `TauCeti.ContinuousRep.evaluation` and `TauCeti.ContinuousRep.scalarToLinHom`: the evaluation
  morphism `M^∨ ⊗ M → A` and the scalar morphism `A → Hom_A(M, M)`, `a ↦ a • id`.
* `TauCeti.ContinuousRep.coevaluation`: the coevaluation morphism `A → M ⊗ M^∨`.

## Main results

* `TauCeti.ContinuousRep.res_id` and `TauCeti.ContinuousRep.res_res`: restriction along the
  identity is the identity, and restriction composes.
* `TauCeti.ContinuousRep.twist_one` and `TauCeti.ContinuousRep.twist_twist`: `M(1) = M` and
  `M(ψ)(χ) = M(χψ)`.
* `TauCeti.ContinuousRep.res_prod`, `TauCeti.ContinuousRep.res_tprod`,
  `TauCeti.ContinuousRep.res_linHom`, `TauCeti.ContinuousRep.res_dual`,
  `TauCeti.ContinuousRep.res_twist` and `TauCeti.ContinuousRep.res_ofCharacter`: restriction
  commutes with the operations.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace ContinuousRep

section Res

variable {Γ Γ' Γ'' A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [Monoid Γ'] [TopologicalSpace Γ']
  [Monoid Γ''] [TopologicalSpace Γ''] [Semiring A] [AddCommMonoid M] [Module A M]
  [TopologicalSpace M]

/-- **Restriction of a continuous representation** along a continuous monoid homomorphism
`φ : Γ' →ₜ* Γ`, for instance the inclusion of a closed subgroup or the map of absolute Galois
groups induced by a field extension: `g'` acts by `ρ (φ g')`. -/
def res (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) : ContinuousRep Γ' A M where
  toRepresentation := ρ.toRepresentation.comp φ.toMonoidHom
  continuous_action := ρ.continuous_action.comp (φ.continuous.prodMap continuous_id)

@[simp]
theorem res_apply (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) (g : Γ') : ρ.res φ g = ρ (φ g) :=
  (rfl)

@[simp]
theorem toRepresentation_res (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) :
    (ρ.res φ).toRepresentation = ρ.toRepresentation.comp φ.toMonoidHom :=
  (rfl)

/-- Restriction along the identity is the identity. -/
@[simp]
theorem res_id (ρ : ContinuousRep Γ A M) : ρ.res (ContinuousMonoidHom.id Γ) = ρ :=
  (rfl)

/-- Restriction composes: restricting along `φ` and then along `ψ` is restricting along
`φ ∘ ψ`. -/
@[simp]
theorem res_res (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') :
    (ρ.res φ).res ψ = ρ.res (φ.comp ψ) :=
  (rfl)

/-- Restriction of the trivial representation is trivial. -/
@[simp]
theorem res_trivial (φ : Γ' →ₜ* Γ) : (trivial Γ A M).res φ = trivial Γ' A M :=
  ext fun _ _ => by simp

variable {N : Type*} [AddCommMonoid N] [Module A N] [TopologicalSpace N]
  {ρ : ContinuousRep Γ A M} {σ : ContinuousRep Γ A N}

/-- The restriction of a morphism of continuous representations. -/
def Hom.res (f : Hom ρ σ) (φ : Γ' →ₜ* Γ) : Hom (ρ.res φ) (σ.res φ) where
  toIntertwiningMap := f.toIntertwiningMap.res φ.toMonoidHom
  cont := by simpa using f.cont

@[simp]
theorem Hom.res_apply (f : Hom ρ σ) (φ : Γ' →ₜ* Γ) (x : M) : f.res φ x = f x :=
  congrFun (f.toIntertwiningMap.coe_res φ.toMonoidHom) x

/-- The restriction of an isomorphism of continuous representations. -/
def Iso.res (e : Iso ρ σ) (φ : Γ' →ₜ* Γ) : Iso (ρ.res φ) (σ.res φ) where
  toRepresentationEquiv := e.toRepresentationEquiv.res φ.toMonoidHom
  continuous_toFun := e.continuous_toFun.congr fun x =>
    (e.toRepresentationEquiv.res_apply φ.toMonoidHom x).symm
  continuous_invFun := by
    simpa [Representation.Equiv.coe_invFun] using e.continuous_invFun.congr fun x =>
      (e.toRepresentationEquiv.symm.res_apply φ.toMonoidHom x).symm

@[simp]
theorem Iso.res_apply (e : Iso ρ σ) (φ : Γ' →ₜ* Γ) (x : M) : e.res φ x = e x :=
  e.toRepresentationEquiv.res_apply φ.toMonoidHom x

@[simp]
theorem Iso.symm_res (e : Iso ρ σ) (φ : Γ' →ₜ* Γ) : (e.res φ).symm = e.symm.res φ :=
  Iso.ext fun x => (e.res φ).injective (by simp)

/-- Restriction commutes with products. -/
@[simp]
theorem res_prod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (φ : Γ' →ₜ* Γ) :
    (ρ.prod σ).res φ = (ρ.res φ).prod (σ.res φ) :=
  ext fun _ _ => by simp

end Res

section Tensor

variable {Γ A M N : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [Module.Finite A N] [TopologicalSpace (M ⊗[A] N)] [IsModuleTopology A (M ⊗[A] N)]

/-- The diagonal action on the tensor product of two finite modules is jointly continuous for the
module topology on `M ⊗[A] N`. -/
private theorem continuous_tprod_action (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Continuous fun p : Γ × (M ⊗[A] N) =>
      ρ.toRepresentation.tprod σ.toRepresentation p.1 p.2 := by
  obtain ⟨a, m, hm⟩ := Module.Finite.exists_fin (R := A) (M := M)
  obtain ⟨b, n, hn⟩ := Module.Finite.exists_fin (R := A) (M := N)
  have hspan : Submodule.span A (Set.range fun ij : Fin a × Fin b => m ij.1 ⊗ₜ[A] n ij.2) = ⊤ := by
    have hrange : (Set.range fun ij : Fin a × Fin b => m ij.1 ⊗ₜ[A] n ij.2) =
        Set.image2 (fun x y => TensorProduct.mk A M N x y) (Set.range m) (Set.range n) := by
      simp [← Set.image2_range, TensorProduct.mk_apply]
    rw [hrange, ← Submodule.map₂_span_span, hm, hn, TensorProduct.map₂_mk_top_top_eq_top]
  refine (IsModuleTopology.continuous_linearMap_apply_iff_of_span_eq_top
    (ρ.toRepresentation.tprod σ.toRepresentation) hspan).2 fun ij => ?_
  have hmk : Continuous fun p : M × N => TensorProduct.mk A M N p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left _
  exact (hmk.comp ((ρ.continuous_orbit (m ij.1)).prodMk (σ.continuous_orbit (n ij.2)))).congr
    fun g => by simp

/-- **The tensor product of two continuous representations** on finite modules: `Γ` acts on
`M ⊗[A] N` diagonally, `g • (x ⊗ y) = ρ g x ⊗ σ g y`, jointly continuously for the module
topology on `M ⊗[A] N`. -/
noncomputable def tprod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    ContinuousRep Γ A (M ⊗[A] N) where
  toRepresentation := ρ.toRepresentation.tprod σ.toRepresentation
  continuous_action := continuous_tprod_action ρ σ

@[simp]
theorem toRepresentation_tprod (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (ρ.tprod σ).toRepresentation = ρ.toRepresentation.tprod σ.toRepresentation :=
  (rfl)

theorem tprod_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ) :
    ρ.tprod σ g = TensorProduct.map (ρ g) (σ g) :=
  (rfl)

/-- The diagonal action on a pure tensor. -/
@[simp]
theorem tprod_apply_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ) (x : M)
    (y : N) : ρ.tprod σ g (x ⊗ₜ y) = ρ g x ⊗ₜ σ g y :=
  (rfl)

/-- Restriction commutes with tensor products. -/
@[simp]
theorem res_tprod {Γ' : Type*} [Monoid Γ'] [TopologicalSpace Γ'] (ρ : ContinuousRep Γ A M)
    (σ : ContinuousRep Γ A N) (φ : Γ' →ₜ* Γ) :
    (ρ.tprod σ).res φ = (ρ.res φ).tprod (σ.res φ) :=
  (rfl)

variable [TopologicalSpace (N ⊗[A] M)] [IsModuleTopology A (N ⊗[A] M)]

/-- **The braiding** `M ⊗ N ≅ N ⊗ M`, `x ⊗ y ↦ y ⊗ x`: Mathlib's
`Representation.TensorProduct.comm` as an isomorphism of continuous representations. -/
noncomputable def tprodCommIso (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Iso (ρ.tprod σ) (σ.tprod ρ) :=
  Iso.ofEquiv (Representation.TensorProduct.comm ρ.toRepresentation σ.toRepresentation)

@[simp]
theorem tprodCommIso_tmul (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (x : M) (y : N) :
    tprodCommIso ρ σ (x ⊗ₜ y) = y ⊗ₜ x :=
  Iso.ofEquiv_apply _ _

@[simp]
theorem tprodCommIso_symm (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (tprodCommIso ρ σ).symm = tprodCommIso σ ρ :=
  (Iso.ofEquiv_symm _).trans (congrArg Iso.ofEquiv (Representation.TensorProduct.comm_symm _ _))

/-- The braiding is an involution. -/
@[simp]
theorem tprodCommIso_tprodCommIso (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N)
    (x : N ⊗[A] M) : tprodCommIso ρ σ (tprodCommIso σ ρ x) = x := by
  rw [← tprodCommIso_symm σ ρ, Iso.symm_apply_apply]

end Tensor

section Twist

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommSemiring A] [TopologicalSpace A]
  [AddCommMonoid M] [Module A M] [TopologicalSpace M] [ContinuousSMul A M]

/-- **The twist `M(χ)` of a continuous representation by a continuous character** `χ : Γ →ₜ* Aˣ`:
the same carrier, with `g` acting by `χ g • ρ g`. It is the tensor product with the line of `χ`
(`TauCeti.ContinuousRep.tprodOfCharacterIsoTwist`), realised on `M` itself by
`Representation.charTwist`. -/
def twist (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) : ContinuousRep Γ A M where
  toRepresentation := Representation.charTwist (χ : Γ →* Aˣ) ρ.toRepresentation
  continuous_action :=
    (((Units.continuous_val.comp χ.continuous).comp continuous_fst).smul ρ.continuous_action).congr
      fun p => (Representation.charTwist_apply_apply _ _ p.1 p.2).symm

@[simp]
theorem toRepresentation_twist (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) :
    (ρ.twist χ).toRepresentation = Representation.charTwist (χ : Γ →* Aˣ) ρ.toRepresentation :=
  (rfl)

@[simp]
theorem twist_apply (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) (g : Γ) (x : M) :
    ρ.twist χ g x = (χ g : A) • ρ g x :=
  Representation.charTwist_apply_apply _ _ g x

/-- Each operator of a twist is the scalar multiple of the original operator by the character. -/
theorem twist_apply_eq_smul (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) (g : Γ) :
    ρ.twist χ g = (χ g : A) • ρ g :=
  LinearMap.ext (twist_apply ρ χ g)

/-- **Twisting by the trivial character changes nothing**: `M(1) = M`. -/
@[simp]
theorem twist_one (ρ : ContinuousRep Γ A M) : ρ.twist 1 = ρ :=
  ext fun g x => by simp

/-- **Twisting twice multiplies the characters**: `M(ψ)(χ) = M(χψ)`. -/
@[simp]
theorem twist_twist [ContinuousMul A] (ρ : ContinuousRep Γ A M) (χ ψ : Γ →ₜ* Aˣ) :
    (ρ.twist ψ).twist χ = ρ.twist (χ * ψ) :=
  ext fun g x => by simp [mul_smul]

/-- The twist of the trivial line by `χ` is the line of `χ`. -/
@[simp]
theorem twist_trivial [ContinuousMul A] (χ : Γ →ₜ* Aˣ) : (trivial Γ A A).twist χ = ofCharacter χ :=
  ext fun g x => by simp

/-- Restriction commutes with twisting. -/
@[simp]
theorem res_twist {Γ' : Type*} [Monoid Γ'] [TopologicalSpace Γ'] (ρ : ContinuousRep Γ A M)
    (χ : Γ →ₜ* Aˣ) (φ : Γ' →ₜ* Γ) : (ρ.twist χ).res φ = (ρ.res φ).twist (χ.comp φ) :=
  ext fun _ _ => by simp

/-- Restriction of the line of `χ` is the line of the restricted character. -/
@[simp]
theorem res_ofCharacter {Γ' : Type*} [Monoid Γ'] [TopologicalSpace Γ'] [ContinuousMul A]
    (χ : Γ →ₜ* Aˣ) (φ : Γ' →ₜ* Γ) : (ofCharacter χ).res φ = ofCharacter (χ.comp φ) :=
  ext fun _ _ => by simp

end Twist

section TwistTensor

variable {Γ A M : Type*} [Monoid Γ] [TopologicalSpace Γ] [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [TopologicalSpace (M ⊗[A] A)] [IsModuleTopology A (M ⊗[A] A)]

/-- **The twist is the tensor product with the line of the character**: `M ⊗ A(χ) ≅ M(χ)`, along
`TensorProduct.rid`. This is `Representation.tprodOfLinearCharacterEquivCharTwist` as an
isomorphism of continuous representations. -/
noncomputable def tprodOfCharacterIsoTwist (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) :
    haveI := IsModuleTopology.toContinuousSMul A M
    Iso (ρ.tprod (ofCharacter χ)) (ρ.twist χ) :=
  haveI := IsModuleTopology.toContinuousSMul A M
  -- `toRepresentation_ofCharacter` is `rfl` only inside its own module, so the equivalence of
  -- the underlying representations is transported along the `toRepresentation_*` lemmas.
  let e := Representation.tprodOfLinearCharacterEquivCharTwist (χ : Γ →* Aˣ) ρ.toRepresentation
  Iso.ofEquiv <| .mk e.toLinearEquiv fun g => by
    rw [toRepresentation_tprod, toRepresentation_ofCharacter, toRepresentation_twist]
    exact e.toIntertwiningMap.isIntertwining' g

@[simp]
theorem tprodOfCharacterIsoTwist_tmul (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) (x : M) (a : A) :
    tprodOfCharacterIsoTwist ρ χ (x ⊗ₜ a) = a • x := by
  simp [tprodOfCharacterIsoTwist]

@[simp]
theorem tprodOfCharacterIsoTwist_symm_apply (ρ : ContinuousRep Γ A M) (χ : Γ →ₜ* Aˣ) (x : M) :
    (tprodOfCharacterIsoTwist ρ χ).symm x = x ⊗ₜ 1 :=
  (tprodOfCharacterIsoTwist ρ χ).injective <| by simp

end TwistTensor

section Hom

variable {Γ A M N : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [TopologicalSpace (M →ₗ[A] N)] [IsModuleTopology A (M →ₗ[A] N)]

/-- The conjugation action on `Hom_A(M, N)` for a finite projective `M` is jointly continuous for
the module topology on `M →ₗ[A] N`. -/
private theorem continuous_linHom_action (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Continuous fun p : Γ × (M →ₗ[A] N) =>
      ρ.toRepresentation.linHom σ.toRepresentation p.1 p.2 := by
  -- A finite dual basis `x = ∑ j, φ j x • b j` writes `σ g ∘ f ∘ ρ g⁻¹` as
  -- `∑ j, (φ j ∘ ρ g⁻¹) ⬝ σ g (f (b j))`.
  obtain ⟨n, b, φ, hb⟩ := exists_sum_dual_smul_eq (R := A) (M := M)
  have := IsModuleTopology.toContinuousAdd A (M →ₗ[A] N)
  have := IsModuleTopology.toContinuousAdd A N
  let : TopologicalSpace (Module.Dual A M) := moduleTopology A _
  have : IsModuleTopology A (Module.Dual A M) := ⟨rfl⟩
  -- The bilinear map `(ψ, y) ↦ ψ ⬝ y` is continuous since `Module.Dual A M` is finite.
  have hsr : Continuous fun p : Module.Dual A M × N => LinearMap.smulRightₗ p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left _
  have hev (j : Fin n) : Continuous fun f : M →ₗ[A] N => f (b j) :=
    IsModuleTopology.continuous_of_linearMap (LinearMap.applyₗ (b j))
  have h : Continuous fun p : Γ × (M →ₗ[A] N) =>
      ∑ j, LinearMap.smulRightₗ (ρ.dual p.1 (φ j)) (σ p.1 (p.2 (b j))) := by
    refine continuous_finsetSum _ fun j _ => ?_
    have h1 : Continuous fun p : Γ × (M →ₗ[A] N) => ρ.dual p.1 (φ j) :=
      (ρ.dual.continuous_orbit (φ j)).comp continuous_fst
    have h2 : Continuous fun p : Γ × (M →ₗ[A] N) => σ p.1 (p.2 (b j)) :=
      σ.continuous_action.comp (continuous_fst.prodMk ((hev j).comp continuous_snd))
    exact hsr.comp (h1.prodMk h2)
  refine h.congr fun p => LinearMap.ext fun x => ?_
  simpa [map_sum] using congr(σ p.1 (p.2 $(hb (ρ p.1⁻¹ x))))

/-- **The Hom representation** of two continuous representations, for a finite projective
source: `Γ` acts on `Hom_A(M, N)` by `g • f = σ g ∘ f ∘ ρ g⁻¹` (Mathlib's
`Representation.linHom`), jointly continuously for the module topology on `M →ₗ[A] N`. -/
def linHom (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) : ContinuousRep Γ A (M →ₗ[A] N) where
  toRepresentation := ρ.toRepresentation.linHom σ.toRepresentation
  continuous_action := continuous_linHom_action ρ σ

@[simp]
theorem toRepresentation_linHom (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (ρ.linHom σ).toRepresentation = ρ.toRepresentation.linHom σ.toRepresentation :=
  (rfl)

theorem linHom_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ) (f : M →ₗ[A] N) :
    ρ.linHom σ g f = σ g ∘ₗ f ∘ₗ ρ g⁻¹ :=
  (rfl)

@[simp]
theorem linHom_apply_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (g : Γ)
    (f : M →ₗ[A] N) (x : M) : ρ.linHom σ g f x = σ g (f (ρ g⁻¹ x)) :=
  (rfl)

/-- Restriction commutes with the Hom representation. -/
@[simp]
theorem res_linHom {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] [ContinuousInv Γ']
    (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) (φ : Γ' →ₜ* Γ) :
    (ρ.linHom σ).res φ = (ρ.res φ).linHom (σ.res φ) :=
  ext fun g f => LinearMap.ext fun x => by simp

/-- **The invariants of the Hom representation are the morphisms of continuous representations**:
`Hom_A(M, N)^Γ = Hom_Γ(M, N)`, from Mathlib's `Representation.invariantsEquivIntertwiningMap`.
Every intertwining map is continuous for the module topologies. -/
noncomputable def invariantsLinHomEquiv (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    (ρ.linHom σ).toRepresentation.invariants ≃ Hom ρ σ :=
  haveI := IsModuleTopology.toContinuousAdd A N
  haveI := IsModuleTopology.toContinuousSMul A N
  (ρ.toRepresentation.invariantsEquivIntertwiningMap σ.toRepresentation).toEquiv.trans
    { toFun := Hom.ofIntertwiningMap
      invFun := Hom.toIntertwiningMap
      left_inv := Hom.toIntertwiningMap_ofIntertwiningMap
      right_inv := Hom.ofIntertwiningMap_toIntertwiningMap }

@[simp]
theorem invariantsLinHomEquiv_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N)
    (f : (ρ.linHom σ).toRepresentation.invariants) (x : M) :
    invariantsLinHomEquiv ρ σ f x = (f : M →ₗ[A] N) x :=
  haveI := IsModuleTopology.toContinuousAdd A N
  haveI := IsModuleTopology.toContinuousSMul A N
  Hom.ofIntertwiningMap_apply _ x

@[simp]
theorem coe_invariantsLinHomEquiv_symm_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N)
    (f : Hom ρ σ) (x : M) : ((invariantsLinHomEquiv ρ σ).symm f : M →ₗ[A] N) x = f x :=
  congr($(Hom.coe_toIntertwiningMap f) x)

end Hom

section Dual

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]

/-- Restriction commutes with the contragredient. -/
@[simp]
theorem res_dual {Γ' : Type*} [Group Γ'] [TopologicalSpace Γ'] [ContinuousInv Γ']
    (ρ : ContinuousRep Γ A M) (φ : Γ' →ₜ* Γ) : ρ.dual.res φ = (ρ.res φ).dual :=
  ext fun g ψ => LinearMap.ext fun x => by simp

section DualDual

variable [TopologicalSpace (Module.Dual A (Module.Dual A M))]
  [IsModuleTopology A (Module.Dual A (Module.Dual A M))]

/-- **The double dual**: evaluation `x ↦ (ψ ↦ ψ x)` is an isomorphism `M ≅ M^∨∨` of continuous
representations for a finite projective `M`. -/
noncomputable def dualDualIso (ρ : ContinuousRep Γ A M) : Iso ρ ρ.dual.dual :=
  Iso.ofEquiv <| .mk (Module.evalEquiv A M) fun g => LinearMap.ext fun x => LinearMap.ext
    fun ψ => by simp [Module.Dual.transpose_apply]

@[simp]
theorem dualDualIso_apply_apply (ρ : ContinuousRep Γ A M) (x : M) (ψ : Module.Dual A M) :
    dualDualIso ρ x ψ = ψ x := by
  simp [dualDualIso]

end DualDual

variable {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N] [IsModuleTopology A N]
  [Module.Finite A N] [TopologicalSpace (Module.Dual A M ⊗[A] N)]
  [IsModuleTopology A (Module.Dual A M ⊗[A] N)]
  [TopologicalSpace (M →ₗ[A] N)] [IsModuleTopology A (M →ₗ[A] N)]

/-- **`M^∨ ⊗ N ≅ Hom_A(M, N)`** for a finite projective `M`: Mathlib's `dualTensorHomEquiv`,
`ψ ⊗ y ↦ (x ↦ ψ x • y)`, is an isomorphism of continuous representations. It is
`Representation.Equiv.dualTensorHomOfProjective` with the automatic continuity of
`TauCeti.ContinuousRep.Iso.ofEquiv`. -/
noncomputable def dualTensorIsoHom (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N) :
    Iso (ρ.dual.tprod σ) (ρ.linHom σ) :=
  let e := Representation.Equiv.dualTensorHomOfProjective ρ.toRepresentation σ.toRepresentation
  Iso.ofEquiv <| .mk e.toLinearEquiv fun g => by
    rw [toRepresentation_tprod, toRepresentation_dual, toRepresentation_linHom]
    exact e.toIntertwiningMap.isIntertwining' g

@[simp]
theorem dualTensorIsoHom_tmul_apply (ρ : ContinuousRep Γ A M) (σ : ContinuousRep Γ A N)
    (ψ : Module.Dual A M) (y : N) (x : M) : dualTensorIsoHom ρ σ (ψ ⊗ₜ y) x = ψ x • y := by
  simp [dualTensorIsoHom]

end Dual

section Evaluation

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]
  [TopologicalSpace (Module.Dual A M ⊗[A] M)] [IsModuleTopology A (Module.Dual A M ⊗[A] M)]

/-- **The evaluation morphism** `M^∨ ⊗ M → A`, `ψ ⊗ x ↦ ψ x`, to the trivial representation. -/
noncomputable def evaluation (ρ : ContinuousRep Γ A M) : Hom (ρ.dual.tprod ρ) (trivial Γ A A) :=
  Hom.ofIntertwiningMap
    { toLinearMap := contractLeft A M
      isIntertwining' g := TensorProduct.ext' fun ψ x => by
        simp [Module.Dual.transpose_apply, ← mul_apply_eq_comp, ← map_mul] }

@[simp]
theorem evaluation_tmul (ρ : ContinuousRep Γ A M) (ψ : Module.Dual A M) (x : M) :
    evaluation ρ (ψ ⊗ₜ x) = ψ x := by
  simp [evaluation]

end Evaluation

section ScalarToLinHom

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [TopologicalSpace (M →ₗ[A] M)] [IsModuleTopology A (M →ₗ[A] M)]

/-- **The scalar morphism** `A → Hom_A(M, M)`, `a ↦ a • id`, from the trivial
representation. Composed with the inverse of `TauCeti.ContinuousRep.dualTensorIsoHom` and the
braiding `TauCeti.ContinuousRep.tprodCommIso` from `M^∨ ⊗ M` to `M ⊗ M^∨`, it gives the
coevaluation `TauCeti.ContinuousRep.coevaluation`. -/
noncomputable def scalarToLinHom (ρ : ContinuousRep Γ A M) : Hom (trivial Γ A A) (ρ.linHom ρ) :=
  haveI := IsModuleTopology.toContinuousAdd A (M →ₗ[A] M)
  haveI := IsModuleTopology.toContinuousSMul A (M →ₗ[A] M)
  Hom.ofIntertwiningMap
    { toLinearMap := LinearMap.toSpanSingleton A (M →ₗ[A] M) LinearMap.id
      isIntertwining' g := LinearMap.ext fun a => LinearMap.ext fun x => by
        simp [← mul_apply_eq_comp, ← map_mul] }

@[simp]
theorem scalarToLinHom_apply (ρ : ContinuousRep Γ A M) (a : A) :
    scalarToLinHom ρ a = a • LinearMap.id := by
  simp [scalarToLinHom]

end ScalarToLinHom

section Coevaluation

variable {Γ A M : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousInv Γ]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [IsModuleTopology A M]
  [Module.Finite A M] [Module.Projective A M]
  [TopologicalSpace (Module.Dual A M)] [IsModuleTopology A (Module.Dual A M)]
  [TopologicalSpace (Module.Dual A M ⊗[A] M)] [IsModuleTopology A (Module.Dual A M ⊗[A] M)]
  [TopologicalSpace (M ⊗[A] Module.Dual A M)] [IsModuleTopology A (M ⊗[A] Module.Dual A M)]
  [TopologicalSpace (M →ₗ[A] M)] [IsModuleTopology A (M →ₗ[A] M)]

/-- **The coevaluation morphism** `A → M ⊗ M^∨` from the trivial representation, for a finite
projective `M`: the element of `M ⊗ M^∨` corresponding to `a • id` under
`Hom_A(M, M) ≅ M^∨ ⊗ M ≅ M ⊗ M^∨`. As for Mathlib's `coevaluation`, the target is `M ⊗ M^∨`, so
that it pairs with the evaluation `TauCeti.ContinuousRep.evaluation` on `M^∨ ⊗ M`. -/
noncomputable def coevaluation (ρ : ContinuousRep Γ A M) : Hom (trivial Γ A A) (ρ.tprod ρ.dual) :=
  (tprodCommIso ρ.dual ρ).toHom.comp ((dualTensorIsoHom ρ ρ).symm.toHom.comp (scalarToLinHom ρ))

/-- Under `M ⊗ M^∨ ≅ M^∨ ⊗ M ≅ Hom_A(M, M)`, the coevaluation of `a` is `a • id`. -/
@[simp]
theorem dualTensorIsoHom_tprodCommIso_coevaluation (ρ : ContinuousRep Γ A M) (a : A) :
    dualTensorIsoHom ρ ρ (tprodCommIso ρ ρ.dual (coevaluation ρ a)) = a • LinearMap.id := by
  simp [coevaluation]

end Coevaluation

end ContinuousRep

end TauCeti
