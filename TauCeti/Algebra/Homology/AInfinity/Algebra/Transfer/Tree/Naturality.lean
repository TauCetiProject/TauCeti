/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Strict
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic

/-!
# Strict-morphism naturality of planar-tree evaluation maps

Given a strict morphism `f : AInfinityStrictHom 𝒜 ℬ` of `A∞` algebras and a linear map
`g : H →ₗ[R] K` intertwining the auxiliary linear maps `(incl, h)` with `(incl', h')` (and `proj`
with `proj'` for tree operations), `f` and `g` intertwine the suspended planar-tree evaluation maps
`suspendedTreeBranch` and `suspendedTreeOperation` from
`TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Tree.Basic` on every reduced planar tree. When
`g` is also homogeneous of degree zero for internal gradings `GH` and `GK`, the same compatibility
holds for the unsuspended Koszul-twisted maps `treeBranch` and `treeOperation`. No contraction or
retraction hypothesis on `(incl, proj, h)` or `g` is needed.

## Main results

* `TauCeti.AInfinityStrictHom.compMultilinearMap_suspendedTreeBranch` and
  `TauCeti.AInfinityStrictHom.compMultilinearMap_treeBranch`: naturality of `suspendedTreeBranch`
  and `treeBranch` under a strict `A∞` morphism `f` and an intertwining linear map `g : H →ₗ[R] K`.
* `TauCeti.AInfinityStrictHom.compMultilinearMap_suspendedTreeOperation` and
  `TauCeti.AInfinityStrictHom.compMultilinearMap_treeOperation`: naturality of
  `suspendedTreeOperation` and `treeOperation` under `f` and `g`.

## References

* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*, Section 6.4.
* J.-L. Loday and B. Vallette, *Algebraic Operads*, Chapter 10, Section 10.3.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3--3.4.
-/

public section

universe uR uA uH uB uK

namespace TauCeti.AInfinityStrictHom

section Naturality

variable {R : Type uR} [CommRing R] {A : Type uA} {H : Type uH} {B : Type uB} {K : Type uK}
  [AddCommGroup A] [Module R A] [AddCommGroup H] [Module R H]
  [AddCommGroup B] [Module R B] [AddCommGroup K] [Module R K]
  {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}
  {GH : InternalGrading R H ℤ} {GK : InternalGrading R K ℤ}
  {incl : H →ₗ[R] A} {h : Module.End R A} {incl' : K →ₗ[R] B} {h' : Module.End R B}
  (f : AInfinityStrictHom 𝒜 ℬ) (g : H →ₗ[R] K)

section BranchNaturality

variable (hι : f.toLinearMap ∘ₗ incl = incl' ∘ₗ g) (hη : f.toLinearMap ∘ₗ h = h' ∘ₗ f.toLinearMap)
include hι hη

/-- A strict `A∞` morphism `f` and a linear map `g : H →ₗ[R] K` intertwining `(incl, h)` with
`(incl', h')` intertwine `suspendedTreeBranch` on every reduced planar tree. -/
theorem compMultilinearMap_suspendedTreeBranch (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.suspendedTreeBranch incl h t) =
      (ℬ.suspendedTreeBranch incl' h' t).compLinearMap fun _ ↦ g := by
  induction t with
  | leaf =>
    ext x
    simpa only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      AInfinityAlgebra.suspendedTreeBranch_leaf_apply, coe_toLinearMap, LinearMap.comp_apply] using
      LinearMap.congr_fun hι (x ⟨0, ReducedPlanarTree.leaf.numLeaves_pos⟩)
  | node k children ih =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, coe_toLinearMap,
      MultilinearMap.compLinearMap_apply, AInfinityAlgebra.suspendedTreeBranch_node_apply, map_neg]
    have hηx := LinearMap.congr_fun hη
    simp only [LinearMap.comp_apply, coe_toLinearMap] at hηx
    rw [hηx, f.map_suspendedM]
    refine congrArg (fun v ↦ -h' (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      MultilinearMap.congr_fun (ih i) fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

/-- A strict `A∞` morphism `f` and a degree-zero linear map `g : H →ₗ[R] K` intertwining
`(incl, h)` with `(incl', h')` intertwine `treeBranch` on every reduced planar tree. -/
theorem compMultilinearMap_treeBranch (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    f.toLinearMap.compMultilinearMap (𝒜.treeBranch incl h GH t) =
      (ℬ.treeBranch incl' h' GK t).compLinearMap fun _ ↦ g := by
  rw [AInfinityAlgebra.treeBranch_def, AInfinityAlgebra.treeBranch_def,
    LinearMap.compMultilinearMap_compLinearMap,
    f.compMultilinearMap_suspendedTreeBranch g hι hη t]
  simpa only [mul_zero, Finset.sum_const_zero, negOnePowCast_zero, one_smul] using
    (InternalGrading.compLinearMap_koszulTwist_compLinearMap (fun _ ↦ hg) _
      (ℬ.suspendedTreeBranch incl' h' t)).symm

end BranchNaturality

section OperationNaturality

variable {proj : A →ₗ[R] H} {proj' : B →ₗ[R] K} (hι : f.toLinearMap ∘ₗ incl = incl' ∘ₗ g)
  (hπ : g ∘ₗ proj = proj' ∘ₗ f.toLinearMap) (hη : f.toLinearMap ∘ₗ h = h' ∘ₗ f.toLinearMap)
include hι hπ hη

/-- A strict `A∞` morphism `f` and a linear map `g : H →ₗ[R] K` intertwining `(incl, proj, h)`
with `(incl', proj', h')` intertwine `suspendedTreeOperation` on every reduced planar tree. -/
theorem compMultilinearMap_suspendedTreeOperation (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.suspendedTreeOperation incl proj h t) =
      (ℬ.suspendedTreeOperation incl' proj' h' t).compLinearMap fun _ ↦ g := by
  cases t with
  | leaf => ext x; simp
  | node k children =>
    ext x
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      AInfinityAlgebra.suspendedTreeOperation_node_apply]
    have hπx := LinearMap.congr_fun hπ
    simp only [LinearMap.comp_apply, coe_toLinearMap] at hπx
    rw [hπx, f.map_suspendedM]
    refine congrArg (fun v ↦ proj' (ℬ.suspendedM (k + 2) v)) (funext fun i ↦ ?_)
    simpa [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply] using
      MultilinearMap.congr_fun (f.compMultilinearMap_suspendedTreeBranch g hι hη (children i))
        fun j ↦ x (finSigmaFinEquiv ⟨i, j⟩)

/-- A strict `A∞` morphism `f` and a degree-zero linear map `g : H →ₗ[R] K` intertwining
`(incl, proj, h)` with `(incl', proj', h')` intertwine `treeOperation` on every reduced planar
tree. -/
theorem compMultilinearMap_treeOperation (hg : LinearMap.IsHomogeneous g GH.piece GK.piece 0)
    (t : ReducedPlanarTree) :
    g.compMultilinearMap (𝒜.treeOperation incl proj h GH t) =
      (ℬ.treeOperation incl' proj' h' GK t).compLinearMap fun _ ↦ g := by
  rw [AInfinityAlgebra.treeOperation_def, AInfinityAlgebra.treeOperation_def,
    LinearMap.compMultilinearMap_compLinearMap,
    f.compMultilinearMap_suspendedTreeOperation g hι hπ hη t]
  simpa only [mul_zero, Finset.sum_const_zero, negOnePowCast_zero, one_smul] using
    (InternalGrading.compLinearMap_koszulTwist_compLinearMap (fun _ ↦ hg) _
      (ℬ.suspendedTreeOperation incl' proj' h' t)).symm

end OperationNaturality
end Naturality
end TauCeti.AInfinityStrictHom
