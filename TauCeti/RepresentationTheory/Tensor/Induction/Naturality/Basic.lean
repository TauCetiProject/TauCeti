/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Naturality
public import TauCeti.RepresentationTheory.Tensor.Induction.Basic

/-!
# Naturality of tensor induction in the group

Tensor induction commutes with a homomorphism that identifies the relevant coset spaces.  If
`φ : G →* G'` carries `U ≤ G` to `U' ≤ G'`, restricts to `ψ : U →* U'`, and induces an
equivalence `G ⧸ U ≃ G' ⧸ U'`, then reindexing the tensor factors along that equivalence
identifies tensor induction of a pulled-back representation with the pullback of tensor
induction.

The main specialization is inflation.  For a normal subgroup `N ≤ U`, tensor induction from
`U` to `G` after pulling coefficients back from the image of `U` in `G ⧸ N` agrees with tensor
induction in the quotient, pulled back to `G`.  This is the representation-level comparison
needed to prove that the Evens norm commutes with inflation.

## Main definitions

* `Subgroup.tensorInducedMapEquiv`: naturality under a homomorphism inducing an equivalence of
  coset spaces.
* `Subgroup.tensorInducedQuotientEquiv`: the specialization to a quotient by a normal subgroup.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), Sections 2--3 and 6.
-/

public section

open TauCeti
open scoped TensorProduct

universe u v v' w

namespace Subgroup

variable {R : Type u} [CommSemiring R]
  {G : Type v} [Group G] {G' : Type v'} [Group G']
  {U : Subgroup G} {U' : Subgroup G'}
  {M : Type w} [AddCommMonoid M] [Module R M]

/-- Reindexing tensor factors identifies tensor induction before and after a homomorphism that
identifies the coset spaces. -/
noncomputable def tensorInducedMapEquiv (φ : G →* G') (ψ : U →* U')
    (hψ : ∀ u, (ψ u : G') = φ u) (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)
    (ρ : Representation R U' M) :
    (U.tensorInducedRepresentation s (ρ.comp ψ)).Equiv
      ((U'.tensorInducedRepresentation (s.map φ e he) ρ).comp φ) :=
  Representation.Equiv.mk (PiTensorProduct.reindex R (fun _ : G ⧸ U ↦ M) e) (fun g ↦ by
    apply PiTensorProduct.ext
    ext m
    -- Extensionality presents the goal through `compMultilinearMap`; expose the two actions on
    -- the generating pure tensor so their public computation rules can rewrite it.
    change PiTensorProduct.reindex R (fun _ : G ⧸ U ↦ M) e
        (U.tensorInducedRepresentation s (ρ.comp ψ) g (PiTensorProduct.tprod R m)) =
      U'.tensorInducedRepresentation (s.map φ e he) ρ (φ g)
        (PiTensorProduct.reindex R (fun _ : G ⧸ U ↦ M) e (PiTensorProduct.tprod R m))
    simp only [tensorInducedRepresentation_apply_tprod, PiTensorProduct.reindex_tprod,
      MonoidHom.comp_apply]
    rw [monomialHom_map φ ψ hψ e he s g]
    simp only [TauCeti.WreathProduct.congr_left, TauCeti.WreathProduct.map_left]
    congr 1
    funext y
    congr 1
    exact congrArg m (e.injective (by
      rw [apply_smul_of_apply_mk U φ e he]
      simp)))

/-- The map comparison sends a pure tensor to the same tensor with its factors relabeled by the
induced equivalence of coset spaces. -/
@[simp]
theorem tensorInducedMapEquiv_apply_tprod (φ : G →* G') (ψ : U →* U')
    (hψ : ∀ u, (ψ u : G') = φ u) (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)
    (ρ : Representation R U' M) (m : G ⧸ U → M) :
    tensorInducedMapEquiv φ ψ hψ e he s ρ (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦ m (e.symm y) :=
  PiTensorProduct.reindex_tprod e m

/-- The inverse map comparison relabels tensor factors along the inverse equivalence of coset
spaces. -/
@[simp]
theorem tensorInducedMapEquiv_symm_apply_tprod (φ : G →* G') (ψ : U →* U')
    (hψ : ∀ u, (ψ u : G') = φ u) (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)
    (ρ : Representation R U' M) (m : G' ⧸ U' → M) :
    (tensorInducedMapEquiv φ ψ hψ e he s ρ).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦ m (e x) := by
  -- Expose the underlying inverse linear equivalence; `Representation.Equiv.symm` otherwise
  -- keeps the reindexing map behind the representation wrapper.
  change (PiTensorProduct.reindex R (fun _ : G ⧸ U ↦ M) e).symm
      (PiTensorProduct.tprod R m) = _
  simpa only [Equiv.apply_symm_apply] using
    PiTensorProduct.reindex_symm_tprod e (fun x ↦ m (e x))

/-- The tensor-induction comparison is natural in the coefficient representation. -/
theorem tensorInducedMapEquiv_naturality (φ : G →* G') (ψ : U →* U')
    (hψ : ∀ u, (ψ u : G') = φ u) (e : G ⧸ U ≃ G' ⧸ U')
    (he : ∀ g : G, e g = (φ g : G' ⧸ U')) (s : U.LeftTransversal)
    {N : Type*} [AddCommMonoid N] [Module R N]
    {ρ : Representation R U' M} {τ : Representation R U' N}
    (f : ρ.IntertwiningMap τ) :
    PiTensorProduct.map (fun _ : G' ⧸ U' ↦ f.toLinearMap) ∘ₗ
        (tensorInducedMapEquiv φ ψ hψ e he s ρ).toLinearEquiv.toLinearMap =
      (tensorInducedMapEquiv φ ψ hψ e he s τ).toLinearEquiv.toLinearMap ∘ₗ
        PiTensorProduct.map (fun _ : G ⧸ U ↦ f.toLinearMap) :=
  PiTensorProduct.map_comp_reindex_eq (fun _ : G ⧸ U ↦ f.toLinearMap) e

/-- Tensor induction commutes with inflation through a quotient by a normal subgroup contained
in the subgroup of induction. -/
noncomputable def tensorInducedQuotientEquiv (N : Subgroup G) [N.Normal] (hNU : N ≤ U)
    (s : U.LeftTransversal)
    (ρ : Representation R (U.map (QuotientGroup.mk' N)) M) :
    (U.tensorInducedRepresentation s
      (ρ.comp ((QuotientGroup.mk' N).subgroupMap U))).Equiv
      (((U.map (QuotientGroup.mk' N)).tensorInducedRepresentation
        (s.map (QuotientGroup.mk' N) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
          (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU)) ρ).comp
        (QuotientGroup.mk' N)) :=
  tensorInducedMapEquiv (QuotientGroup.mk' N) ((QuotientGroup.mk' N).subgroupMap U)
    (MonoidHom.subgroupMap_apply_coe _ U) (QuotientGroup.quotientEquivQuotientMapOfLE hNU)
    (QuotientGroup.quotientEquivQuotientMapOfLE_mk hNU) s ρ

/-- On pure tensors, the quotient comparison relabels a coset of `U` by its image in the
quotient. -/
@[simp]
theorem tensorInducedQuotientEquiv_apply_tprod (N : Subgroup G) [N.Normal] (hNU : N ≤ U)
    (s : U.LeftTransversal) (ρ : Representation R (U.map (QuotientGroup.mk' N)) M)
    (m : G ⧸ U → M) :
    tensorInducedQuotientEquiv N hNU s ρ (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun y ↦
        m ((QuotientGroup.quotientEquivQuotientMapOfLE hNU).symm y) :=
  tensorInducedMapEquiv_apply_tprod _ _ _ _ _ _ _ _

/-- The inverse quotient comparison replaces a quotient coset by its preimage coset in `G`. -/
@[simp]
theorem tensorInducedQuotientEquiv_symm_apply_tprod (N : Subgroup G) [N.Normal]
    (hNU : N ≤ U) (s : U.LeftTransversal)
    (ρ : Representation R (U.map (QuotientGroup.mk' N)) M)
    (m : (G ⧸ N) ⧸ U.map (QuotientGroup.mk' N) → M) :
    (tensorInducedQuotientEquiv N hNU s ρ).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R fun x ↦
        m (QuotientGroup.quotientEquivQuotientMapOfLE hNU x) :=
  tensorInducedMapEquiv_symm_apply_tprod _ _ _ _ _ _ _ _

/-- The quotient comparison commutes with equivariant maps of coefficient representations. -/
theorem tensorInducedQuotientEquiv_naturality (N : Subgroup G) [N.Normal] (hNU : N ≤ U)
    (s : U.LeftTransversal) {P : Type*} [AddCommMonoid P] [Module R P]
    {ρ : Representation R (U.map (QuotientGroup.mk' N)) M}
    {τ : Representation R (U.map (QuotientGroup.mk' N)) P}
    (f : ρ.IntertwiningMap τ) :
    PiTensorProduct.map
          (fun _ : (G ⧸ N) ⧸ U.map (QuotientGroup.mk' N) ↦ f.toLinearMap) ∘ₗ
        (tensorInducedQuotientEquiv N hNU s ρ).toLinearEquiv.toLinearMap =
      (tensorInducedQuotientEquiv N hNU s τ).toLinearEquiv.toLinearMap ∘ₗ
        PiTensorProduct.map (fun _ : G ⧸ U ↦ f.toLinearMap) :=
  tensorInducedMapEquiv_naturality _ _ _ _ _ _ f

end Subgroup
