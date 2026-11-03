/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.GeckConstruction.PinnedSymmetry

/-!
# Diagram automorphisms of the pinned split Lie algebra

A symmetry `σ` of the Bourbaki-numbered Cartan matrix of a valid Dynkin type `t` induces an
automorphism of the pinned rational Lie algebra `TauCeti.DynkinType.lieAlgebra`,

```text
hᵢ ↦ h_{σ i},   eᵢ ↦ e_{σ i},   fᵢ ↦ f_{σ i}.
```

It is built without Serre's theorem. Geck's matrices carry no sign choices, so reindexing them along
the coordinate permutation `TauCeti.DynkinType.geckDiagramIndexEquiv` of the pinned Geck module
carries each numbered generator to the one renumbered by `σ`, and
`TauCeti.DynkinType.diagramLieEquiv` is the resulting equivalence
`RootPairing.Equiv.geckLieEquivOfEquiv` of Geck's Lie algebra, read on the pinned carrier. On the
Geck module it is therefore conjugation by `TauCeti.DynkinType.geckDiagramModuleEquiv`, the
coordinate permutation from which the graph automorphism `TauCeti.DynkinType.geckGraphAut` of the
Geck carrier is built.

The raising and lowering generators generate the Lie algebra, so a Lie homomorphism out of it is
determined by their images (`TauCeti.DynkinType.lieHom_ext`). That makes `σ ↦ diagramLieEquiv σ`
multiplicative, unital and compatible with the Chevalley involution. It preserves the Cartan
subalgebra, on which it permutes the basis of Cartan generators by `σ`; this is what a twist of a
highest-weight module by a diagram automorphism needs in order to read off the new highest
weight.

## Main definitions

* `TauCeti.DynkinType.diagramLieEquiv`: the diagram automorphism of the pinned Lie algebra.

## Main results

* `TauCeti.DynkinType.diagramLieEquiv_lieBasis_h`, `diagramLieEquiv_lieBasis_e` and
  `diagramLieEquiv_lieBasis_f`: the automorphism renumbers the Chevalley generators by `σ`.
* `TauCeti.DynkinType.coe_diagramLieEquiv`: as matrices, it is reindexing along the coordinate
  permutation of the Geck module.
* `TauCeti.DynkinType.geckDiagramModuleEquiv_mulVec_diagramLieEquiv`: the coordinate permutation
  of the Geck module intertwines the defining action with its twist by the automorphism.
* `TauCeti.DynkinType.diagramLieEquiv_one`, `diagramLieEquiv_mul` and `diagramLieEquiv_symm`:
  the assignment is a homomorphism from the diagram symmetry group.
* `TauCeti.DynkinType.diagramLieEquiv_chevalleyInvolution`: it commutes with the Chevalley
  involution.
* `TauCeti.DynkinType.diagramLieEquiv_cartan` and
  `TauCeti.DynkinType.map_cartanSubalgebra_diagramLieEquiv`: it preserves the Cartan subalgebra,
  permuting its basis of Cartan generators.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.15.
-/

public section

open Matrix

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction Module

noncomputable section

-- Matrices form a Lie ring through their commutator, which is how Geck's construction reads
-- them; the module defining `TauCeti.DynkinType.lieAlgebra` activates the same instance locally.
attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : DynkinType} (ht : t.Valid) {σ τ : Equiv.Perm (Fin t.rank)}

/-! ## The diagram automorphism -/

/-- **The diagram automorphism of the pinned split Lie algebra** attached to a symmetry `σ` of the
Bourbaki-numbered Cartan matrix: the automorphism `hᵢ ↦ h_{σ i}`, `eᵢ ↦ e_{σ i}`, `fᵢ ↦ f_{σ i}`.
It is Geck's equivalence `RootPairing.Equiv.geckLieEquivOfEquiv` along the rational diagram
automorphism, the restriction of conjugation by the coordinate permutation
`TauCeti.DynkinType.geckDiagramIndexEquiv` of the pinned Geck module, read on the pinned carrier. -/
def diagramLieEquiv (hσ : σ ∈ t.diagramSymmetry) : t.lieAlgebra ht ≃ₗ⁅ℚ⁆ t.lieAlgebra ht :=
  ((t.geckLieEquiv ht).trans ((t.rationalDiagramAut ht hσ).geckLieEquivOfEquiv
    (t.geckDiagramBaseEquiv ht σ) (coe_geckDiagramBaseEquiv_apply ht hσ))).trans
      (t.geckLieEquiv ht).symm

/-- **The diagram automorphism is conjugation by the Geck coordinate permutation**, read on
matrices. -/
theorem coe_diagramLieEquiv (hσ : σ ∈ t.diagramSymmetry) (x : t.lieAlgebra ht) :
    (t.diagramLieEquiv ht hσ x : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      Matrix.reindexAlgEquiv ℚ ℚ (t.geckDiagramIndexEquiv ht hσ) x :=
by
  rw [diagramLieEquiv, LieEquiv.trans_apply, LieEquiv.trans_apply, coe_geckLieEquiv_symm,
    RootPairing.Equiv.geckLieEquivOfEquiv_apply, coe_geckLieEquiv, geckDiagramIndexEquiv_def]

/-- **The diagram automorphism renumbers the Cartan generators by the diagram symmetry.** -/
@[simp]
theorem diagramLieEquiv_lieBasis_h (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    t.diagramLieEquiv ht hσ ((t.lieBasis ht).h i) = (t.lieBasis ht).h (σ i) := by
  apply Subtype.ext
  rw [coe_diagramLieEquiv, coe_lieBasis_h, coe_lieBasis_h, geckDiagramIndexEquiv_def,
    RootPairing.Equiv.reindex_geckIndexEquiv_h _ _ (coe_geckDiagramBaseEquiv_apply ht hσ),
    geckDiagramBaseEquiv_apply_simpleSupportEquiv]

/-- **The diagram automorphism renumbers the raising generators by the diagram symmetry.** -/
@[simp]
theorem diagramLieEquiv_lieBasis_e (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    t.diagramLieEquiv ht hσ ((t.lieBasis ht).e i) = (t.lieBasis ht).e (σ i) := by
  apply Subtype.ext
  rw [coe_diagramLieEquiv, coe_lieBasis_e, coe_lieBasis_e, geckDiagramIndexEquiv_def,
    RootPairing.Equiv.reindex_geckIndexEquiv_e _ _ (coe_geckDiagramBaseEquiv_apply ht hσ),
    geckDiagramBaseEquiv_apply_simpleSupportEquiv]

/-- **The diagram automorphism renumbers the lowering generators by the diagram symmetry.** -/
@[simp]
theorem diagramLieEquiv_lieBasis_f (hσ : σ ∈ t.diagramSymmetry) (i : Fin t.rank) :
    t.diagramLieEquiv ht hσ ((t.lieBasis ht).f i) = (t.lieBasis ht).f (σ i) := by
  apply Subtype.ext
  rw [coe_diagramLieEquiv, coe_lieBasis_f, coe_lieBasis_f, geckDiagramIndexEquiv_def,
    RootPairing.Equiv.reindex_geckIndexEquiv_f _ _ (coe_geckDiagramBaseEquiv_apply ht hσ),
    geckDiagramBaseEquiv_apply_simpleSupportEquiv]

/-- **The Geck coordinate permutation intertwines the defining action with its twist by the
diagram automorphism**: permuting the coordinates of `x v` gives the automorphism applied to `x`
acting on the permuted vector. -/
theorem geckDiagramModuleEquiv_mulVec_diagramLieEquiv (hσ : σ ∈ t.diagramSymmetry)
    (x : t.lieAlgebra ht) (v : t.GeckIndex ht → ℚ) :
    t.geckDiagramModuleEquiv ht hσ ((x : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *ᵥ v) =
      (t.diagramLieEquiv ht hσ x : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *ᵥ
        t.geckDiagramModuleEquiv ht hσ v := by
  rw [coe_diagramLieEquiv, geckDiagramModuleEquiv_def, geckDiagramIndexEquiv_def,
    RootPairing.Equiv.geckModuleEquiv_mulVec]

/-! ## Multiplicativity and the Chevalley involution -/

/-- The identity symmetry of the diagram gives the identity automorphism. -/
@[simp]
theorem diagramLieEquiv_one : t.diagramLieEquiv ht t.diagramSymmetry.one_mem = LieEquiv.refl := by
  refine lieEquiv_ext ht (fun i => ?_) fun i => ?_ <;> simp

/-- **The diagram automorphism of a product of symmetries is the composite**, the right-hand
symmetry acting first. -/
theorem diagramLieEquiv_mul (hσ : σ ∈ t.diagramSymmetry) (hτ : τ ∈ t.diagramSymmetry) :
    t.diagramLieEquiv ht (t.diagramSymmetry.mul_mem hσ hτ) =
      (t.diagramLieEquiv ht hτ).trans (t.diagramLieEquiv ht hσ) := by
  refine lieEquiv_ext ht (fun i => ?_) fun i => ?_ <;> simp

/-- The inverse of the diagram automorphism is the automorphism of the inverse symmetry. -/
@[simp]
theorem diagramLieEquiv_symm (hσ : σ ∈ t.diagramSymmetry) :
    (t.diagramLieEquiv ht hσ).symm = t.diagramLieEquiv ht (t.diagramSymmetry.inv_mem hσ) := by
  refine LieEquiv.ext fun x => ?_
  rw [LieEquiv.symm_apply_eq, ← LieEquiv.trans_apply, ← diagramLieEquiv_mul]
  simp only [mul_inv_cancel, diagramLieEquiv_one, LieEquiv.refl_apply]

/-- **The diagram automorphism commutes with the Chevalley involution.** Both send `eᵢ` to
`-f_{σ i}` and `fᵢ` to `-e_{σ i}` in either order. -/
theorem diagramLieEquiv_chevalleyInvolution (hσ : σ ∈ t.diagramSymmetry) (x : t.lieAlgebra ht) :
    t.diagramLieEquiv ht hσ (t.chevalleyInvolution ht x) =
      t.chevalleyInvolution ht (t.diagramLieEquiv ht hσ x) := by
  have h : ((t.chevalleyInvolution ht).trans (t.diagramLieEquiv ht hσ)).toLieHom =
      ((t.diagramLieEquiv ht hσ).trans (t.chevalleyInvolution ht)).toLieHom :=
    lieHom_ext ht (fun i => by simp) fun i => by simp
  exact congr($h x)

/-! ## The Cartan subalgebra -/

/-- **The diagram automorphism preserves the Cartan subalgebra, permuting the Cartan generators by
the diagram symmetry**: on an element of the Cartan subalgebra it is the linear equivalence carrying
the `i`-th Cartan basis vector to the `σ i`-th one. -/
theorem diagramLieEquiv_cartan (hσ : σ ∈ t.diagramSymmetry) (x : t.cartanSubalgebra ht) :
    t.diagramLieEquiv ht hσ (x : t.lieAlgebra ht) =
      ((t.cartanBasis ht).equiv (t.cartanBasis ht) σ x : t.lieAlgebra ht) := by
  let f : t.cartanSubalgebra ht →ₗ[ℚ] t.lieAlgebra ht :=
    (t.diagramLieEquiv ht hσ).toLieHom.toLinearMap.comp (t.cartanSubalgebra ht).incl.toLinearMap
  let g : t.cartanSubalgebra ht →ₗ[ℚ] t.lieAlgebra ht :=
    (t.cartanSubalgebra ht).incl.toLinearMap.comp
      ((t.cartanBasis ht).equiv (t.cartanBasis ht) σ).toLinearMap
  have hfg : f = g := (t.cartanBasis ht).ext fun i => by
    simp [f, g]
  exact congr($hfg x)

/-- **The diagram automorphism maps the Cartan subalgebra onto itself.** -/
theorem map_cartanSubalgebra_diagramLieEquiv (hσ : σ ∈ t.diagramSymmetry) :
    (t.cartanSubalgebra ht).map (t.diagramLieEquiv ht hσ).toLieHom = t.cartanSubalgebra ht := by
  ext y
  simp only [LieSubalgebra.mem_map, LieEquiv.coe_toLieHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [diagramLieEquiv_cartan ht hσ ⟨x, hx⟩]
    exact Subtype.property _
  · intro hy
    refine ⟨_, ((t.cartanBasis ht).equiv (t.cartanBasis ht) σ).symm ⟨y, hy⟩ |>.property, ?_⟩
    rw [diagramLieEquiv_cartan ht hσ, LinearEquiv.apply_symm_apply]

end

end TauCeti.DynkinType
