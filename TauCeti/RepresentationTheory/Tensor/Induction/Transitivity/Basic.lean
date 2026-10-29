/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.RepresentationTheory.Tensor.Induction.Diagonal
public import TauCeti.LinearAlgebra.PiTensorProduct.Assoc
import TauCeti.GroupTheory.Perm.WreathProduct.Transitivity

/-!
# Transitivity of tensor induction

For a subgroup tower `V ≤ U ≤ G`, tensor induction from `V` to `U` followed by tensor induction
from `U` to `G` is equivalent to tensor induction from `V` to `G` for the composite transversal.
The equivalence flattens the two tensor indices and relabels them by the tower's coset
coordinates. It is natural in the representation of `V`.

Only `G ⧸ U` must be finite: its finiteness permits expansion of tensors of sums in the inner
tensor powers. No finiteness of `U ⧸ V`, topology, or characteristic assumption is needed.
This is the coefficient-level regrouping used in transitivity of the multiplicative transfer.

## References

* L. Evens, *A generalization of the transfer map in the cohomology of groups*,
  Transactions of the American Mathematical Society 108 (1963), §§2–3 and §6.1, pp. 60–61
  (the module identification preceding Proposition 1).
-/

public section

open scoped TensorProduct

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommSemiring R] {G : Type v} [Group G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Finite (G ⧸ U)] {M : Type w} [AddCommMonoid M] [Module R M]

/-- Flatten the tensor powers of a subgroup tower and relabel their product index by the cosets
of the smaller subgroup, using the outer transversal. -/
noncomputable def tensorInducedTransitivityLinearEquiv :
    (⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) ≃ₗ[R]
      (⨂[R] _ : G ⧸ V, M) :=
  PiTensorProduct.prodEquiv.trans
    (PiTensorProduct.reindex R (fun _ ↦ M)
      (quotientEquivProdOfLE' hVU (leftTransversalRep U s) (leftTransversalRep_mk U s)).symm)

/-- On tensors of pure tensors, regrouping reads the two coordinates of each coset. -/
@[simp] theorem tensorInducedTransitivityLinearEquiv_tprod
    (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → M) :
    tensorInducedTransitivityLinearEquiv (R := R) hVU s (PiTensorProduct.tprod R
      fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s) q).1
          (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
            (leftTransversalRep_mk U s) q).2) := by
  simp [tensorInducedTransitivityLinearEquiv]

/-- The inverse linear regrouping expands a pure tensor according to the two coset indices. -/
@[simp] theorem tensorInducedTransitivityLinearEquiv_symm_tprod (m : G ⧸ V → M) :
    (tensorInducedTransitivityLinearEquiv (R := R) hVU s).symm
        (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s)).symm (a, b)))) := by
  apply (tensorInducedTransitivityLinearEquiv hVU s).injective
  simp only [LinearEquiv.apply_symm_apply, tensorInducedTransitivityLinearEquiv_tprod,
    Equiv.symm_apply_apply, Prod.mk.eta]

/-- Tensor induction is transitive along a subgroup tower, with the composite transversal on
the direct induction. The representation of `V` is restricted to `V.subgroupOf U` through its
canonical equivalence with `V`. -/
noncomputable def tensorInducedTransitivity (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) :
    (U.tensorInducedRepresentation s ((V.subgroupOf U).tensorInducedRepresentation t
      (ρ.comp (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)))).Equiv
      (V.tensorInducedRepresentation (compositeLeftTransversal hVU s t) ρ) :=
  Representation.Equiv.mk (tensorInducedTransitivityLinearEquiv hVU s) (fun g ↦ by
    apply PiTensorProduct.ext_sigma_tprod
    intro m
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      tensorInducedRepresentation_apply_tprod, tensorInducedTransitivityLinearEquiv_tprod]
    simp only [MonoidHom.comp_apply]
    congr 1
    funext q
    let e := quotientEquivProdOfLE' hVU (leftTransversalRep U s) (leftTransversalRep_mk U s)
    have hcoords := quotientEquivProdOfLE'_inv_smul_symm U (leftTransversalRep U s)
      hVU (leftTransversalRep_mk U s) (e q).1 (e q).2 g
    rw [Prod.mk.eta, e.symm_apply_apply] at hcoords
    have hword : (subgroupOfEquivOfLe hVU)
        (((V.subgroupOf U).monomialHom t ((U.monomialHom s g).left (e q).1)).left
          (e q).2) =
        (V.monomialHom (compositeLeftTransversal hVU s t) g).left q := by
      simpa [e] using (congrArg (fun a ↦ a.left q)
        (monomialHom_compositeLeftTransversal hVU s t g)).symm
    -- Identify the composed representation's group argument with the underlying subgroup
    -- equivalence, and write both coefficient indices using the same coset-coordinate map `e`.
    change ρ ((subgroupOfEquivOfLe hVU) _)
        (m (g⁻¹ • (e q).1) (((U.monomialHom s g).left (e q).1)⁻¹ • (e q).2)) =
      ρ ((V.monomialHom (compositeLeftTransversal hVU s t) g).left q)
        (m (e (g⁻¹ • q)).1 (e (g⁻¹ • q)).2)
    rw [hword]
    congr 1
    rw [monomialHom_left]
    exact congrArg (fun p ↦ m p.1 p.2) hcoords.symm)

/-- The transitivity equivalence is the flattening and coset-reindexing linear equivalence. -/
theorem tensorInducedTransitivity_toLinearEquiv (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) :
    (tensorInducedTransitivity hVU s t ρ).toLinearEquiv =
      tensorInducedTransitivityLinearEquiv hVU s := by
  simp only [tensorInducedTransitivity, Representation.Equiv.toLinearEquiv_mk']

/-- The transitivity equivalence evaluates by the named linear regrouping. -/
theorem tensorInducedTransitivity_apply (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    tensorInducedTransitivity hVU s t ρ z =
      tensorInducedTransitivityLinearEquiv hVU s z := by
  simp only [tensorInducedTransitivity, Representation.Equiv.mk_apply]

/-- The representation comparison flattens pure tensors using the tower's coset coordinates. -/
@[simp] theorem tensorInducedTransitivity_tprod (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) (m : (G ⧸ U) → (U ⧸ V.subgroupOf U) → M) :
    tensorInducedTransitivity hVU s t ρ (PiTensorProduct.tprod R
      fun a ↦ PiTensorProduct.tprod R (m a)) =
      PiTensorProduct.tprod R (fun q : G ⧸ V ↦
        m (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s) q).1
          (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
            (leftTransversalRep_mk U s) q).2) := by
  rw [tensorInducedTransitivity_apply, tensorInducedTransitivityLinearEquiv_tprod]

/-- The inverse comparison regroups a pure tensor according to the two coset indices. -/
@[simp] theorem tensorInducedTransitivity_symm_tprod (t : (V.subgroupOf U).LeftTransversal)
    (ρ : Representation R V M) (m : G ⧸ V → M) :
    (tensorInducedTransitivity hVU s t ρ).symm (PiTensorProduct.tprod R m) =
      PiTensorProduct.tprod R (fun a ↦ PiTensorProduct.tprod R (fun b ↦
        m ((quotientEquivProdOfLE' hVU (leftTransversalRep U s)
          (leftTransversalRep_mk U s)).symm (a, b)))) := by
  apply (tensorInducedTransitivity hVU s t ρ).toLinearEquiv.injective
  simp only [Representation.Equiv.toLinearEquiv_apply,
    Representation.Equiv.coe_toIntertwiningMap, Representation.Equiv.apply_symm_apply,
    tensorInducedTransitivity_tprod, Equiv.symm_apply_apply, Prod.mk.eta]

/-- Regrouping is natural in an intertwining map: applying that map to each of the inner
factors and then regrouping equals applying the tensor-induced map after regrouping. -/
theorem tensorInducedTransitivity_naturality (t : (V.subgroupOf U).LeftTransversal)
    {N : Type*} [AddCommMonoid N] [Module R N]
    {ρ : Representation R V M} {τ : Representation R V N} (f : ρ.IntertwiningMap τ)
    (z : ⨂[R] _ : G ⧸ U, ⨂[R] _ : U ⧸ V.subgroupOf U, M) :
    let e := (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    let f' : Representation.IntertwiningMap (ρ.comp e) (τ.comp e) :=
      { toLinearMap := f.toLinearMap
        isIntertwining' := fun v ↦ f.isIntertwining' (e v) }
    tensorInducedTransitivity hVU s t τ (((f'.tensorInduced t).tensorInduced s) z) =
      f.tensorInduced (compositeLeftTransversal hVU s t)
        (tensorInducedTransitivity hVU s t ρ z) := by
  dsimp only
  have H : (tensorInducedTransitivityLinearEquiv (R := R) (M := N) hVU s).toLinearMap ∘ₗ
        PiTensorProduct.map (fun _ : G ⧸ U ↦
          PiTensorProduct.map (fun _ : U ⧸ V.subgroupOf U ↦ f.toLinearMap)) =
      PiTensorProduct.map (fun _ : G ⧸ V ↦ f.toLinearMap) ∘ₗ
        (tensorInducedTransitivityLinearEquiv hVU s).toLinearMap := by
    apply LinearMap.ext
    intro x
    simp only [tensorInducedTransitivityLinearEquiv, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.trans_apply, PiTensorProduct.prodEquiv_map]
    exact (PiTensorProduct.map_reindex
      (fun _ : (G ⧸ U) × (U ⧸ V.subgroupOf U) ↦ f.toLinearMap)
      (quotientEquivProdOfLE' hVU (leftTransversalRep U s)
        (leftTransversalRep_mk U s)).symm (PiTensorProduct.prodEquiv x)).symm
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorInducedTransitivity_apply,
    Representation.IntertwiningMap.tensorInduced_toLinearMap,
    ← Representation.IntertwiningMap.toLinearMap_apply] using LinearMap.congr_fun H z

end Subgroup

namespace Subgroup

open TauCeti

universe u v w

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  {U V : Subgroup G} (hVU : V ≤ U) (s : U.LeftTransversal)
  [Finite (G ⧸ U)] {M : Type w} [AddCommGroup M] [Module R M]

/-- Transitivity carries the iterated invariant diagonal to the direct invariant diagonal. -/
theorem tensorInducedTransitivity_tensorInducedDiagonal
    (t : (V.subgroupOf U).LeftTransversal) (ρ : Representation R V M) (x : ρ.invariants) :
    let τ : Representation R (V.subgroupOf U) M :=
      ρ.comp (subgroupOfEquivOfLe hVU : V.subgroupOf U →* V)
    let y : τ.invariants := ⟨x, fun v ↦ x.property ((subgroupOfEquivOfLe hVU) v)⟩
    tensorInducedTransitivity hVU s t ρ
        (((V.subgroupOf U).tensorInducedRepresentation t τ).tensorInducedDiagonal s
          (τ.tensorInducedDiagonal t y)) =
      (ρ.tensorInducedDiagonal (compositeLeftTransversal hVU s t) x :
        ⨂[R] _ : G ⧸ V, M) := by
  simp only [Representation.coe_tensorInducedDiagonal, tensorInducedTransitivity_tprod]

end Subgroup
