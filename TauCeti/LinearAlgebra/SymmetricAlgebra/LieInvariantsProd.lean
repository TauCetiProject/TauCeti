/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Prod
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Lie invariants of the symmetric algebra of a product with an abelian factor

Let `Z` be an abelian Lie algebra, free as a module, and `S` a Lie algebra over a commutative ring
`K`. The symmetric algebra of
the product Lie algebra is `S(Z × S) ≃ S(Z) ⊗ S(S)` (`SymmetricAlgebra.prodEquiv`), and under this
equivalence the adjoint action of `(z, s)` is `1 ⊗ ad s`: the factor `Z` is central, so it acts
by zero on both factors, and `S` acts trivially on `S(Z)`. Hence the adjoint invariants of the
product are

`S(Z × S)^{Z × S} ≃ S(Z) ⊗ S(S)^S`

(`TauCeti.SymmetricAlgebra.lieInvariantsProdEquiv`). The last step is that for a free module `A`
the maps `1 ⊗ f_j` on `A ⊗ M` have common kernel `A ⊗ ⋂ ker f_j`
(`TensorProduct.forall_lTensor_eq_zero_iff_mem_range`), read off coordinates in a basis of `A`
(`Module.Basis.mem_range_lTensor_subtype_iff`).

This is the abelian-factor case of the invariant side of the reductive Lie–Chevalley square:
through `TauCeti.centerDerivedEquiv : L ≃ z(L) × [L, L]` for a reductive Lie algebra `L` it
identifies `S(L)^L` with `S(z(L)) ⊗ S([L, L])^{[L, L]}`, matching the decomposition
`Z(U(Z × S)) ≃ S(Z) ⊗ Z(U(S))` of the centre of the enveloping algebra
(`TauCeti.UniversalEnvelopingAlgebra.productCenterEquiv`).

## Main results

* `Module.Basis.mem_range_lTensor_subtype_iff`: an element of `A ⊗ M` lies in `A ⊗ W` exactly
  when its coordinates in a basis of `A` lie in `W`.
* `TensorProduct.forall_lTensor_eq_zero_iff_mem_range`: for free `A`, the common kernel of the
  maps `1 ⊗ f_j` is `A ⊗ ⋂ ker f_j`.
* `TauCeti.SymmetricAlgebra.lieModuleDerivation_prodEquiv_symm`: under `S(Z × S) ≃ S(Z) ⊗ S(S)`
  the action of `x` is `1 ⊗` the action of `x.2`.
* `TauCeti.SymmetricAlgebra.prodEquiv_symm_mem_lieInvariants_iff`: an element of `S(Z) ⊗ S(S)` is
  invariant exactly when it lies in `S(Z) ⊗ S(S)^S`.
* `TauCeti.SymmetricAlgebra.lieInvariantsProdHom`,
  `TauCeti.SymmetricAlgebra.lieInvariantsProdEquiv`: the algebra equivalence
  `S(Z × S)^{Z × S} ≃ S(Z) ⊗ S(S)^S`, inverse to `p ⊗ q ↦ p q`.
-/

public section

open TensorProduct

/-! ### Common kernels of `1 ⊗ f` -/

namespace Module.Basis

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M]
  {κ : Type*} [DecidableEq κ] (b : Module.Basis κ R A)

/-- **An element of `A ⊗ M` lies in `A ⊗ W` exactly when its coordinates lie in `W`**, for a
basis of `A`. -/
theorem mem_range_lTensor_subtype_iff (W : Submodule R M) (x : A ⊗[R] M) :
    x ∈ LinearMap.range (W.subtype.lTensor A) ↔ ∀ k, equivFinsuppOfBasisLeft b x k ∈ W := by
  constructor
  · rintro ⟨y, rfl⟩ k
    rw [equivFinsuppOfBasisLeft_lTensor_apply]
    exact (equivFinsuppOfBasisLeft b y k).property
  · intro h
    refine ⟨∑ k ∈ (equivFinsuppOfBasisLeft b x).support, b k ⊗ₜ ⟨_, h k⟩, ?_⟩
    rw [map_sum]
    simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
    conv_rhs => rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x,
      equivFinsuppOfBasisLeft_symm_apply]
    rfl

omit [DecidableEq κ] in
/-- **The common kernel of the maps `1 ⊗ f_j` on `A ⊗ M` is `A ⊗ ⋂ ker f_j`**, for a free
module `A`. -/
theorem _root_.TensorProduct.forall_lTensor_eq_zero_iff_mem_range [Module.Free R A]
    {N ι : Type*} [AddCommMonoid N] [Module R N] (f : ι → M →ₗ[R] N) (x : A ⊗[R] M) :
    (∀ j, (f j).lTensor A x = 0) ↔
      x ∈ LinearMap.range ((⨅ j, LinearMap.ker (f j)).subtype.lTensor A) := by
  classical
  let b := Module.Free.chooseBasis R A
  simp_rw [b.mem_range_lTensor_subtype_iff, b.lTensor_eq_zero_iff_forall_equivFinsuppOfBasisLeft,
    Submodule.mem_iInf, LinearMap.mem_ker]
  exact forall_comm

end Module.Basis

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

variable {K Z S : Type*} [CommRing K] [LieRing Z] [LieAlgebra K Z] [IsLieAbelian Z] [LieRing S]
  [LieAlgebra K S]

/-- `Z` acts trivially on its own symmetric algebra through the product: the action of `x` on the
image of `S(Z)` in `S(Z × S)` is zero, `Z` being abelian. -/
theorem lieModuleDerivation_map_inl (x : Z × S) (p : SymmetricAlgebra K Z) :
    lieModuleDerivation K (Z × S) (Z × S) x (map K (LinearMap.inl K Z S) p) = 0 := by
  rw [lieModuleDerivation_apply, ← map_apply_derivationOfEnd K (LinearMap.inl K Z S)
    (f := 0), map_zero, zero_apply, map_zero]
  ext z <;> simp [LieAlgebra.Prod.bracket_apply, LieModule.toEnd_apply_apply, trivial_lie_zero]

omit [IsLieAbelian Z] in
/-- The action of `x` on the image of `S(S)` in `S(Z × S)` is the action of `x.2` on `S(S)`. -/
theorem lieModuleDerivation_map_inr (x : Z × S) (q : SymmetricAlgebra K S) :
    lieModuleDerivation K (Z × S) (Z × S) x (map K (LinearMap.inr K Z S) q) =
      map K (LinearMap.inr K Z S) (lieModuleDerivation K S S x.2 q) := by
  rw [lieModuleDerivation_apply, lieModuleDerivation_apply,
    ← map_apply_derivationOfEnd K (LinearMap.inr K Z S)]
  ext s <;> simp [LieAlgebra.Prod.bracket_apply, LieModule.toEnd_apply_apply]

/-- **Under `S(Z × S) ≃ S(Z) ⊗ S(S)` the action of `x` is `1 ⊗` the action of `x.2`**, for an
abelian Lie algebra `Z`. -/
theorem lieModuleDerivation_prodEquiv_symm (x : Z × S)
    (y : SymmetricAlgebra K Z ⊗[K] SymmetricAlgebra K S) :
    lieModuleDerivation K (Z × S) (Z × S) x ((prodEquiv K Z S).symm y) =
      (prodEquiv K Z S).symm
        ((lieModuleDerivation K S S x.2).toLinearMap.lTensor (SymmetricAlgebra K Z) y) := by
  induction y using TensorProduct.inductionOn with
  | add y y' hy hy' => rw [map_add, map_add, hy, hy', map_add, map_add]
  | tmul p q =>
    rw [prodEquiv_symm_tmul, Derivation.leibniz, lieModuleDerivation_map_inl,
      lieModuleDerivation_map_inr, smul_zero, add_zero, LinearMap.lTensor_tmul,
      prodEquiv_symm_tmul, smul_eq_mul]
    rfl

variable [Module.Free K Z]

/-- **An element of `S(Z) ⊗ S(S)` is invariant exactly when it lies in `S(Z) ⊗ S(S)^S`**, for an
abelian Lie algebra `Z`. -/
theorem prodEquiv_symm_mem_lieInvariants_iff
    (y : SymmetricAlgebra K Z ⊗[K] SymmetricAlgebra K S) :
    (prodEquiv K Z S).symm y ∈ lieInvariants K (Z × S) (Z × S) ↔
      y ∈ LinearMap.range
        ((lieInvariants K S S).toSubmodule.subtype.lTensor (SymmetricAlgebra K Z)) := by
  have hW : (lieInvariants K S S).toSubmodule =
      ⨅ s : S, LinearMap.ker (lieModuleDerivation K S S s).toLinearMap := by
    ext q
    simp [mem_lieInvariants]
  rw [hW, ← TensorProduct.forall_lTensor_eq_zero_iff_mem_range,
    mem_lieInvariants]
  simp_rw [lieModuleDerivation_prodEquiv_symm, map_eq_zero_iff _ (prodEquiv K Z S).symm.injective]
  exact ⟨fun h s ↦ h (0, s), fun h x ↦ h x.2⟩

variable (K Z S) in
/-- The algebra map `S(Z) ⊗ S(S)^S → S(Z × S)`, `p ⊗ q ↦ p q`: the inclusion followed by the
inverse of `S(Z × S) ≃ S(Z) ⊗ S(S)`. -/
noncomputable def lieInvariantsProdHom :
    SymmetricAlgebra K Z ⊗[K] lieInvariants K S S →ₐ[K] SymmetricAlgebra K (Z × S) :=
  (prodEquiv K Z S).symm.toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K _) (lieInvariants K S S).val)

omit [IsLieAbelian Z] [Module.Free K Z] in
/-- `lieInvariantsProdHom` is the inclusion `S(Z) ⊗ S(S)^S → S(Z) ⊗ S(S)` followed by the inverse
of `S(Z × S) ≃ S(Z) ⊗ S(S)`. -/
theorem lieInvariantsProdHom_apply (y : SymmetricAlgebra K Z ⊗[K] lieInvariants K S S) :
    lieInvariantsProdHom K Z S y = (prodEquiv K Z S).symm
      ((lieInvariants K S S).toSubmodule.subtype.lTensor (SymmetricAlgebra K Z) y) := by
  change (prodEquiv K Z S).symm _ = _
  congr 1

omit [IsLieAbelian Z] [Module.Free K Z] in
/-- `lieInvariantsProdHom` sends `p ⊗ q` to the product of the images of `p` and `q` in
`S(Z × S)`. -/
theorem lieInvariantsProdHom_tmul (p : SymmetricAlgebra K Z) (q : lieInvariants K S S) :
    lieInvariantsProdHom K Z S (p ⊗ₜ q) =
      map K (LinearMap.inl K Z S) p * map K (LinearMap.inr K Z S) q := by
  rw [lieInvariantsProdHom_apply, LinearMap.lTensor_tmul, prodEquiv_symm_tmul]
  rfl

omit [IsLieAbelian Z] in
/-- `lieInvariantsProdHom` is injective: tensoring with the free module `S(Z)` preserves
injectivity. -/
theorem lieInvariantsProdHom_injective : Function.Injective (lieInvariantsProdHom K Z S) := by
  intro y y' h
  rw [lieInvariantsProdHom_apply, lieInvariantsProdHom_apply] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    ((prodEquiv K Z S).symm.injective h)

/-- The range of `lieInvariantsProdHom` is the algebra of invariants `S(Z × S)^{Z × S}`. -/
theorem range_lieInvariantsProdHom :
    (lieInvariantsProdHom K Z S).range = lieInvariants K (Z × S) (Z × S) := by
  ext p
  rw [AlgHom.mem_range, ← (prodEquiv K Z S).symm_apply_apply p,
    prodEquiv_symm_mem_lieInvariants_iff, LinearMap.mem_range]
  simp_rw [lieInvariantsProdHom_apply, (prodEquiv K Z S).symm.injective.eq_iff]
  exact Iff.rfl

variable (K Z S) in
/-- **The adjoint invariants of a product with an abelian factor**:
`S(Z × S)^{Z × S} ≃ S(Z) ⊗ S(S)^S` as algebras, through `S(Z × S) ≃ S(Z) ⊗ S(S)`. -/
noncomputable def lieInvariantsProdEquiv :
    lieInvariants K (Z × S) (Z × S) ≃ₐ[K] SymmetricAlgebra K Z ⊗[K] lieInvariants K S S :=
  ((AlgEquiv.ofInjective _ lieInvariantsProdHom_injective).trans
    (Subalgebra.equivOfEq _ _ range_lieInvariantsProdHom)).symm

/-- The inverse of `lieInvariantsProdEquiv` is `lieInvariantsProdHom`. -/
@[simp]
theorem coe_lieInvariantsProdEquiv_symm_apply
    (y : SymmetricAlgebra K Z ⊗[K] lieInvariants K S S) :
    ((lieInvariantsProdEquiv K Z S).symm y : SymmetricAlgebra K (Z × S)) =
      lieInvariantsProdHom K Z S y :=
  (rfl)

end TauCeti.SymmetricAlgebra
