/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.TensorProduct
public import TauCeti.RepresentationTheory.FDRep.Continuous.External
public import TauCeti.RepresentationTheory.RepresentationRing.Continuous.Restriction
public import TauCeti.RepresentationTheory.RepresentationRing.External
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Prod

/-!
# The external tensor product of representation rings of continuous representations

For topological monoids `G` and `H` over a topological field `k`, the external tensor product
`V ⊠ W` of continuous finite-dimensional representations of `G` and `H`, on which `(g, h)` acts by
`ρ_V g ⊗ ρ_W h`, is again continuous (`FDRep.isContinuous_externalTensor` of
`TauCeti/RepresentationTheory/FDRep/Continuous/External.lean`). This file builds the
corresponding biadditive map of representation rings of continuous representations,

`TauCeti.contRepRingExternalTensor k G H : R(G) →+ R(H) →+ R(G × H)`,

`x ⊠ y = res_{pr₁} x * res_{pr₂} y`, through the restrictions `TauCeti.contRepRingRes` along the
two continuous projections of `G × H`. On classes it is the class of the external tensor product
(`TauCeti.contRepRingExternalTensor_of_of`). It is multiplicative, sends `1 ⊠ 1` to `1`, is
compatible with restriction along products of continuous homomorphisms, recovers the product of
`R(G)` along the diagonal, and forgetting continuity takes it to the external tensor product
`TauCeti.repRingExternalTensor` of all finite-dimensional representations.

For compact groups this is the external product `R(G) ⊗ R(H) → R(G × H)` of equivariant K-theory at
a point. It is the product in which the equivariant index of the external product of a
`G`-equivariant and an `H`-equivariant elliptic operator is the product of their equivariant
indices.

## Main definitions

* `TauCeti.contRepRingExternalTensor`: the external tensor product `R(G) →+ R(H) →+ R(G × H)` of
  representation rings of continuous representations.

## Main statements

* `TauCeti.contRepRingExternalTensor_of_of`: `[V] ⊠ [W]` is the class of the external tensor
  product.
* `TauCeti.contRepRingExternalTensor_mul_mul` and `TauCeti.contRepRingExternalTensor_one_one`:
  compatibility with the ring structures.
* `TauCeti.contRepRingRes_prodMap_contRepRingExternalTensor`: restriction along `φ × ψ`.
* `TauCeti.contRepRingRes_diag_contRepRingExternalTensor`: restriction along the diagonal is the
  product of `R(G)`.
* `TauCeti.contRepRingToRepRing_contRepRingExternalTensor`: forgetting continuity commutes with
  the external tensor product.
* `ContRepresentation.contRepRingExternalTensor_of_ofContRepresentation`: for continuous
  representations on finite-dimensional inner product spaces, the class of the external tensor
  product `ContRepresentation.externalTensor` is the external product of the classes.

## References

* G. Segal, *Equivariant K-theory*, Publ. Math. IHÉS 34 (1968), §2, for the representation ring
  `R(G)` of continuous representations of a compact group.
* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §9, for the external product of equivariant indices in `R(G × H)`.
-/

public section

open CategoryTheory MonoidalCategory

universe u v v' w w'

namespace TauCeti

variable {k : Type u} [Field k] [TopologicalSpace k] [ContinuousAdd k] [ContinuousMul k]
  {G : Type v} {H : Type v'} [Monoid G] [TopologicalSpace G] [Monoid H] [TopologicalSpace H]

variable (k G H) in
/-- **The external tensor product of representation rings of continuous representations**, the
biadditive map `R(G) →+ R(H) →+ R(G × H)` sending `(x, y)` to the product in `R(G × H)` of the
restrictions of `x` and `y` along the two continuous projections. On classes of representations it
is the class of their external tensor product (`TauCeti.contRepRingExternalTensor_of_of`). -/
noncomputable def contRepRingExternalTensor :
    contRepRing k G →+ contRepRing k H →+ contRepRing k (G × H) :=
  (AddMonoidHom.mul.comp (contRepRingRes k (ContinuousMonoidHom.fst G H)).toAddMonoidHom).compl₂
    (contRepRingRes k (ContinuousMonoidHom.snd G H)).toAddMonoidHom

/-- The external tensor product is the product of the restrictions along the two projections. -/
theorem contRepRingExternalTensor_apply (x : contRepRing k G) (y : contRepRing k H) :
    contRepRingExternalTensor k G H x y =
      contRepRingRes k (ContinuousMonoidHom.fst G H) x *
        contRepRingRes k (ContinuousMonoidHom.snd G H) y :=
  (rfl)

/-- The external tensor product of the classes of two continuous representations is the class of
their external tensor product `(g, h) ↦ ρ_V g ⊗ ρ_W h`. -/
@[simp]
theorem contRepRingExternalTensor_of_of (V : ContFDRep k G) (W : ContFDRep k H) :
    contRepRingExternalTensor k G H (SplitK0.of V) (SplitK0.of W) =
      SplitK0.of (⟨FDRep.of (Representation.externalTensor V.obj.ρ W.obj.ρ),
        FDRep.isContinuous_externalTensor V.property W.property⟩ : ContFDRep k (G × H)) := by
  rw [contRepRingExternalTensor_apply, contRepRingRes_of, contRepRingRes_of, SplitK0.of_mul_of]
  refine SplitK0.of_congr ((FDRep.isContinuous k (G × H)).isoMk ?_)
  dsimp only [ObjectProperty.tensorObj_obj]
  rw [ContFDRep.res_obj_obj, ContFDRep.res_obj_obj, ContinuousMonoidHom.coe_toMonoidHom,
    ContinuousMonoidHom.coe_toMonoidHom, ContinuousMonoidHom.coe_fst, ContinuousMonoidHom.coe_snd]
  exact FDRep.externalTensorIso V.obj W.obj

/-- **The external tensor product is multiplicative** in both variables at once:
`(x * x') ⊠ (y * y') = (x ⊠ y) * (x' ⊠ y')`. -/
theorem contRepRingExternalTensor_mul_mul (x x' : contRepRing k G) (y y' : contRepRing k H) :
    contRepRingExternalTensor k G H (x * x') (y * y') =
      contRepRingExternalTensor k G H x y * contRepRingExternalTensor k G H x' y' := by
  simp only [contRepRingExternalTensor_apply, map_mul]
  ring

/-- The external tensor product of the units is the unit. -/
@[simp]
theorem contRepRingExternalTensor_one_one : contRepRingExternalTensor k G H 1 1 = 1 := by
  simp [contRepRingExternalTensor_apply]

/-- **Restriction along a product of continuous homomorphisms**: restricting `x ⊠ y` along `φ × ψ`
is the external tensor product of the restrictions of `x` along `φ` and of `y` along `ψ`. -/
theorem contRepRingRes_prodMap_contRepRingExternalTensor {G' : Type w} {H' : Type w'} [Monoid G']
    [TopologicalSpace G'] [Monoid H'] [TopologicalSpace H'] (φ : G' →ₜ* G) (ψ : H' →ₜ* H)
    (x : contRepRing k G) (y : contRepRing k H) :
    contRepRingRes k (φ.prodMap ψ) (contRepRingExternalTensor k G H x y) =
      contRepRingExternalTensor k G' H' (contRepRingRes k φ x) (contRepRingRes k ψ y) := by
  have hfst : (ContinuousMonoidHom.fst G H).comp (φ.prodMap ψ) =
      φ.comp (ContinuousMonoidHom.fst G' H') := ContinuousMonoidHom.ext fun _ ↦ rfl
  have hsnd : (ContinuousMonoidHom.snd G H).comp (φ.prodMap ψ) =
      ψ.comp (ContinuousMonoidHom.snd G' H') := ContinuousMonoidHom.ext fun _ ↦ rfl
  simp only [contRepRingExternalTensor_apply, map_mul, ← RingHom.comp_apply,
    ← contRepRingRes_comp, hfst, hsnd]

/-- **Along the diagonal the external tensor product is the product**: restricting `x ⊠ y` along
`g ↦ (g, g)` gives `x * y`. -/
@[simp]
theorem contRepRingRes_diag_contRepRingExternalTensor (x y : contRepRing k G) :
    contRepRingRes k (ContinuousMonoidHom.diag G) (contRepRingExternalTensor k G G x y) =
      x * y := by
  have hfst : (ContinuousMonoidHom.fst G G).comp (ContinuousMonoidHom.diag G) =
      ContinuousMonoidHom.id G := ContinuousMonoidHom.ext fun _ ↦ rfl
  have hsnd : (ContinuousMonoidHom.snd G G).comp (ContinuousMonoidHom.diag G) =
      ContinuousMonoidHom.id G := ContinuousMonoidHom.ext fun _ ↦ rfl
  simp only [contRepRingExternalTensor_apply, map_mul, ← RingHom.comp_apply,
    ← contRepRingRes_comp, hfst, hsnd, contRepRingRes_id, RingHom.id_apply]

/-- **Forgetting continuity commutes with the external tensor product.** -/
@[simp]
theorem contRepRingToRepRing_contRepRingExternalTensor (x : contRepRing k G)
    (y : contRepRing k H) :
    contRepRingToRepRing k (G × H) (contRepRingExternalTensor k G H x y) =
      repRingExternalTensor k G H (contRepRingToRepRing k G x) (contRepRingToRepRing k H y) := by
  simp only [contRepRingExternalTensor_apply, repRingExternalTensor_apply, map_mul,
    contRepRingToRepRing_contRepRingRes, ContinuousMonoidHom.coe_toMonoidHom,
    ContinuousMonoidHom.coe_fst, ContinuousMonoidHom.coe_snd]

end TauCeti

namespace ContRepresentation

open TauCeti

variable {𝕜 G H X Y : Type*} [RCLike 𝕜] [Monoid G] [Monoid H] [TopologicalSpace G]
  [TopologicalSpace H] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [FiniteDimensional 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]

/-- **The class of an external tensor product.** For continuous representations `σ` of `G` and `τ`
of `H` on finite-dimensional inner product spaces, the class of the external tensor product
`σ ⊠ τ` in the representation ring of `G × H` is the external product of the classes of `σ` and
`τ`. -/
theorem contRepRingExternalTensor_of_ofContRepresentation (σ : ContRepresentation 𝕜 G X)
    (τ : ContRepresentation 𝕜 H Y) (hσ : Continuous σ) (hτ : Continuous τ) :
    contRepRingExternalTensor 𝕜 G H (SplitK0.of (ContFDRep.ofContRepresentation σ hσ))
        (SplitK0.of (ContFDRep.ofContRepresentation τ hτ)) =
      SplitK0.of (ContFDRep.ofContRepresentation (σ.externalTensor τ)
        (continuous_externalTensor σ τ hσ hτ)) := by
  rw [contRepRingExternalTensor_of_of]
  refine SplitK0.of_congr (ObjectProperty.isoMk _ ?_)
  let E₁ := (ContFDRep.ofContRepresentationEquiv hσ).externalTensor
    (ContFDRep.ofContRepresentationEquiv hτ)
  let E₂ := (ContFDRep.ofContRepresentationEquiv (continuous_externalTensor σ τ hσ hτ)).symm
  rw [toRepresentation_externalTensor] at E₂
  let E := E₁.trans E₂
  exact E.toLinearEquiv.toFDRepIso fun g x ↦
    Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap g x

end ContRepresentation
