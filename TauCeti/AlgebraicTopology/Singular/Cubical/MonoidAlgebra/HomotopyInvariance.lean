/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action
public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.HomotopyInvariance
public import TauCeti.Algebra.Homology.DG.Module.Right.QuasiIso

/-!
# Homotopy invariance of the DG modules of chains on spaces with a monoid action

An equivariant map of spaces with a right action of a topological monoid `G` which is a homotopy
equivalence induces a quasi-isomorphism of the DG right modules of normalized cubical chains of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action`
(`TauCeti.isQuasiIso_cubicalChainModuleMap`).  The homotopy inverse and the homotopies come from
the chain homotopy equivalence of normalized cubical chains induced by a homotopy equivalence
(`ContinuousMap.HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv`), read on the direct
sum; they are linear over the ground ring and need not be equivariant.

## Main definitions

* `TauCeti.homotopyEquivChainHomotopy R e n`: the components of the chain homotopy `g ∘ f ≃ 1`.
* `TauCeti.cubicalChainModuleHomotopy R e`: the same homotopy on the module of chains.

## Main results

* `TauCeti.cubicalChainModuleHomotopy_spec`: `g (f x) = x + d (K x) + K (d x)`.
* `TauCeti.isQuasiIso_cubicalChainModuleMap`: an equivariant homotopy equivalence induces a
  quasi-isomorphism.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open CategoryTheory MulOpposite ContinuousMap

namespace TauCeti

universe u

section Module

variable {Y Y' : Type u} {G : Type*} [TopologicalSpace Y] [TopologicalSpace Y']
  [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [MulAction Gᵐᵒᵖ Y] [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y']
  (R : Type u) [CommRing R]

/-- The component in dimension `n` of the homotopy `g ∘ f ≃ 1` of normalized cubical chains
induced by a homotopy equivalence `e`. -/
def homotopyEquivChainHomotopy (e : Y ≃ₕ Y') (n : ℕ) :
    NormalizedCubicalChain Y R n →ₗ[R] NormalizedCubicalChain Y R (n + 1) :=
  ((HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv R e).homotopyHomInvId.hom n
    (n + 1)).hom

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The chain homotopy `g ∘ f ≃ 1` in dimension `0`. -/
theorem homotopyEquivChainHomotopy_spec_zero (e : Y ≃ₕ Y') (c : NormalizedCubicalChain Y R 0) :
    NormalizedCubicalChain.map R e.invFun 0 (NormalizedCubicalChain.map R e.toFun 0 c) =
      NormalizedCubicalChain.boundary Y R 0 (homotopyEquivChainHomotopy R e 0 c) + c := by
  set E := HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv R e with hE
  have hl : ((E.hom ≫ E.inv).f 0).hom c =
      NormalizedCubicalChain.map R e.invFun 0 (NormalizedCubicalChain.map R e.toFun 0 c) := by
    rw [hE, HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv_hom,
      HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv_inv]
    rfl
  have comm := E.homotopyHomInvId.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at comm
  rw [← hl, comm]
  rfl

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The chain homotopy `g ∘ f ≃ 1` in dimension `k + 1`. -/
theorem homotopyEquivChainHomotopy_spec_succ (e : Y ≃ₕ Y') (k : ℕ)
    (c : NormalizedCubicalChain Y R (k + 1)) :
    NormalizedCubicalChain.map R e.invFun (k + 1) (NormalizedCubicalChain.map R e.toFun (k + 1) c) =
      homotopyEquivChainHomotopy R e k (NormalizedCubicalChain.boundary Y R k c) +
        NormalizedCubicalChain.boundary Y R (k + 1) (homotopyEquivChainHomotopy R e (k + 1) c) +
          c := by
  set E := HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv R e with hE
  have hl : ((E.hom ≫ E.inv).f (k + 1)).hom c =
      NormalizedCubicalChain.map R e.invFun (k + 1)
        (NormalizedCubicalChain.map R e.toFun (k + 1) c) := by
    rw [hE, HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv_hom,
      HomotopyEquiv.normalizedCubicalChainComplexHomotopyEquiv_inv]
    rfl
  have comm := E.homotopyHomInvId.comm (k + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at comm
  rw [← hl, comm, ModuleCat.hom_add, ModuleCat.hom_add]
  -- The chain `c` is stated in `C^□_{k + 1}(Y)` and the maps on the carriers of the chain complex,
  -- which agree only up to unfolding; `erw` matches across this.
  erw [LinearMap.add_apply, LinearMap.add_apply, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, normalizedCubicalChainComplex_obj_d_apply,
    normalizedCubicalChainComplex_obj_d_apply]
  rfl

/-- The degree-raising operator `K` on the module of chains of `Y` given by the chain homotopy
`g ∘ f ≃ 1` of a homotopy equivalence `e`. -/
def cubicalChainModuleHomotopy (e : Y ≃ₕ Y') :
    cubicalChainModule Y G R →ₗ[R] cubicalChainModule Y G R :=
  cubicalChainModuleDesc fun n ↦
    (cubicalChainModuleLof Y G R (n + 1)).comp (homotopyEquivChainHomotopy R e n)

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The operator `K` on a homogeneous chain. -/
theorem cubicalChainModuleHomotopy_lof (e : Y ≃ₕ Y') {n : ℕ} (c : NormalizedCubicalChain Y R n) :
    cubicalChainModuleHomotopy (G := G) R e (cubicalChainModuleLof Y G R n c) =
      cubicalChainModuleLof Y G R (n + 1) (homotopyEquivChainHomotopy R e n c) := by
  rw [cubicalChainModuleHomotopy, cubicalChainModuleDesc_lof, LinearMap.comp_apply]

omit [Monoid G] [TopologicalSpace G] [ContinuousMul G] [MulAction Gᵐᵒᵖ Y]
  [ContinuousSMul Gᵐᵒᵖ Y] [MulAction Gᵐᵒᵖ Y'] [ContinuousSMul Gᵐᵒᵖ Y'] in
/-- The chain homotopy `g ∘ f ≃ 1` on the module: `g (f x) = x + d (K x) + K (d x)`. -/
theorem cubicalChainModuleHomotopy_spec (e : Y ≃ₕ Y') (x : cubicalChainModule Y G R) :
    cubicalChainModuleLinearMap R e.invFun (cubicalChainModuleLinearMap R e.toFun x) =
      x + cubicalChainModuleDifferential Y G R (cubicalChainModuleHomotopy R e x) +
        cubicalChainModuleHomotopy R e (cubicalChainModuleDifferential Y G R x) := by
  induction x using cubicalChainModule.induction_on with
  | zero => simp only [map_zero, add_zero]
  | add x x' hx hx' =>
    rw [map_add, map_add, hx, hx', map_add, map_add, map_add, map_add]
    abel
  | lof n c =>
    rw [cubicalChainModuleLinearMap_lof, cubicalChainModuleLinearMap_lof,
      cubicalChainModuleHomotopy_lof, cubicalChainModuleDifferential_lof_succ]
    rcases n with _ | k
    · rw [cubicalChainModuleDifferential_lof_zero, map_zero, add_zero,
        homotopyEquivChainHomotopy_spec_zero, map_add, add_comm]
    · rw [cubicalChainModuleDifferential_lof_succ, cubicalChainModuleHomotopy_lof,
        homotopyEquivChainHomotopy_spec_succ, map_add, map_add]
      abel

/-- **A morphism of DG modules of chains which pushes chains forward along a homotopy equivalence
is a quasi-isomorphism.**  The homotopy inverse and the homotopies need not be equivariant. -/
theorem isQuasiIso_of_apply_eq {G' : Type*} [Monoid G'] [TopologicalSpace G'] [ContinuousMul G']
    [MulAction G'ᵐᵒᵖ Y] [ContinuousSMul G'ᵐᵒᵖ Y] [MulAction G'ᵐᵒᵖ Y']
    [ContinuousSMul G'ᵐᵒᵖ Y']
    (φ : cubicalChainModuleDG Y G' R ⟶ cubicalChainModuleDG Y' G' R) (e : Y ≃ₕ Y')
    (hφ : ∀ x, φ x = cubicalChainModuleLinearMap R e.toFun x) :
    DGRightModuleHom.IsQuasiIso φ := by
  refine DGRightModuleHom.isQuasiIso_of_homotopyInverse φ
    (cubicalChainModuleLinearMap R e.invFun)
    (cubicalChainModuleHomotopy R e) (cubicalChainModuleHomotopy R e.symm)
    (cubicalChainModuleDifferential_linearMap e.invFun) (fun x ↦ ?_) (fun y ↦ ?_)
  · rw [hφ]
    exact cubicalChainModuleHomotopy_spec R e x
  · rw [hφ]
    exact cubicalChainModuleHomotopy_spec R e.symm y

/-- **An equivariant homotopy equivalence induces a quasi-isomorphism** of the DG right modules
of cubical chains.  The homotopy inverse and the homotopies need not be equivariant. -/
theorem isQuasiIso_cubicalChainModuleMap (f : C(Y, Y'))
    (hf : ∀ (g : G) (y : Y), f (op g • y) = op g • f y) (e : Y ≃ₕ Y') (he : e.toFun = f) :
    DGRightModuleHom.IsQuasiIso (cubicalChainModuleMap R f hf) := by
  subst he
  exact isQuasiIso_of_apply_eq (G' := G) R _ e fun x ↦ cubicalChainModuleMap_apply _ hf x

end Module

end TauCeti

end
