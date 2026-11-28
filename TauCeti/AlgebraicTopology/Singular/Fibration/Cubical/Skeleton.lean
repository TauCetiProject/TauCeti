/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Relative.QuasiIso
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cubical.Cells

/-!
# The quotients of the skeletal filtration of the chains of a Serre fibration

Let `p : E → B` be a Serre fibration over a space containing a relative CW complex `C`, with
skeleta `Xⁿ = skeletonLT C (n + 1)`. The normalized cubical chains of `E` are filtered by the
chains supported over the preimages `preimageSkeleton C p n = p⁻¹(Xⁿ)` of the skeleta; this is the
filtration whose spectral sequence is the Serre spectral sequence of `p`. This file computes the
quotients of consecutive stages cell by cell, on chains.

Let `P` be the pullback of `p` to the disks of the `n`-cells (`TauCeti.TopCat.cellPullback`) and
`∂P` its part over their boundary spheres. The projection `(P, ∂P) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` is a
quasi-isomorphism of relative cubical chains
(`TauCeti.TopCat.quasiIso_cubicalChainComplexMap_cellPullbackPairMap`).
Read on the chains of `E`, through
`TauCeti.exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso`, every
relative cycle of the pair `(P, ∂P)` relative to the quotient of the `n`-th stage by the
`(n - 1)`-th is a relative boundary
(`TauCeti.TopCat.exists_add_differential_sub_mem_preimageSkeleton`).

The pullback is allowed to be presented by any space `Z` homeomorphic to `P` over `E`, since the
pullbacks met in practice, such as those of the end point maps of path spaces, are fibre products
of their own. This is the form in which a quotient of the filtration is compared with free
generators attached over the cells, as in Brown's twisted tensor products.

## Main results

* `TauCeti.TopCat.exists_add_differential_sub_mem_preimageSkeleton`: the projection from the
  pullback to the `n`-cells, relative to the boundary spheres, is a quasi-isomorphism onto the
  quotient of the `n`-th stage of the skeletal filtration of the chains of `E` by the `(n - 1)`-th.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* E. H. Brown, *Twisted tensor products, I*, Ann. of Math. (2) 69 (1959), 223–246.
-/

public section

noncomputable section

open Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

universe u

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]
  {R : Type u} [CommRing R] (H : Type*)

/-- The preimage of `Xⁿ` is the `n`-th stage of the skeletal filtration. -/
private theorem range_subtypeVal_preimage_skeletonLT_succ (n : ℕ) :
    range (ContinuousMap.subtypeVal (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B))) =
      preimageSkeleton C p n :=
  Subtype.range_coe.trans (preimageSkeleton_eq_preimage_skeletonLT _ (n + 1) n (by lia)).symm

/-- The preimage of `Xⁿ⁻¹`, as a subset of `E`, is the `(n - 1)`-th stage of the skeletal
filtration. -/
private theorem image_range_preimageSkeletonPair_map (n : ℕ) :
    ContinuousMap.subtypeVal (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)) ''
        range (preimageSkeletonPair p C n).map =
      preimageSkeleton C p (n - 1) := by
  rw [preimageSkeleton_eq_preimage_skeletonLT _ n (n - 1) rfl]
  refine Set.ext fun x ↦ ⟨?_, fun hx ↦ ⟨_, ⟨⟨x, hx⟩, rfl⟩, rfl⟩⟩
  rintro ⟨_, ⟨w, rfl⟩, rfl⟩
  exact w.property

/-- **The quotients of the skeletal filtration of the chains of a Serre fibration are computed
over the cells.** Let `p : E → B` be a Serre fibration, `C ⊆ B` a relative CW complex, `Z` a space
homeomorphic over `E` to the pullback `P` of `p` to the disks of the `n`-cells, by `e` with
`Φ = pr₂ ∘ e`, and `A ⊆ Z` its part over the boundary spheres. Pushing chains forward along
`Φ : Z → E` is a quasi-isomorphism from the relative chains `C_*(Z, A)` onto the quotient of the
chains of `E` supported over `p⁻¹(Xⁿ)` by those supported over `p⁻¹(Xⁿ⁻¹)`, in the following form:
if `x` is a chain of `Z` whose boundary lies in `A` and `y` a chain over `p⁻¹(Xⁿ)` such that
`Φ_* x - ∂y` lies over `p⁻¹(Xⁿ⁻¹)`, then `x` is the boundary of a chain `u` modulo `A`, and `y` is
`Φ_* u` plus the boundary of a chain `v` over `p⁻¹(Xⁿ)`, modulo `p⁻¹(Xⁿ⁻¹)`. -/
theorem exists_add_differential_sub_mem_preimageSkeleton (hp : serreFibrations p) {n : ℕ}
    {Z : Type u} [TopologicalSpace Z] (e : Z ≃ₜ cellPullback p C n) (Φ : C(Z, E))
    (hΦ : ∀ z, Φ z = (e z).val.2) {A : Set Z}
    (hA : ∀ z, z ∈ A ↔ ‖((e z).val.1.2 : Fin n → ℝ)‖ = 1)
    {x : cubicalChainModule Z H R} {y : cubicalChainModule E H R}
    (hx : cubicalChainModuleDifferential Z H R x ∈ cubicalChainModuleSupportedIn H R A)
    (hy : y ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C p n))
    (hxy : cubicalChainModuleLinearMap R Φ x - cubicalChainModuleDifferential E H R y ∈
      cubicalChainModuleSupportedIn H R (preimageSkeleton C p (n - 1))) :
    ∃ (u : cubicalChainModule Z H R) (v : cubicalChainModule E H R),
      v ∈ cubicalChainModuleSupportedIn H R (preimageSkeleton C p n) ∧
        cubicalChainModuleDifferential Z H R u - x ∈ cubicalChainModuleSupportedIn H R A ∧
        cubicalChainModuleLinearMap R Φ u + cubicalChainModuleDifferential E H R v - y ∈
          cubicalChainModuleSupportedIn H R (preimageSkeleton C p (n - 1)) := by
  have := quasiIso_cubicalChainComplexMap_cellPullbackPairMap C hp R n
  refine exists_add_differential_sub_mem_cubicalChainModuleSupportedIn_of_quasiIso H
    (cellPullbackPairMap p C n) e
    (ι := ContinuousMap.subtypeVal (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
    IsEmbedding.subtypeVal Φ
    (fun z ↦ (hΦ z).trans (coe_cellPullbackPairMap_fst_apply n (e z)).symm) ?_
    (range_subtypeVal_preimage_skeletonLT_succ n) (image_range_preimageSkeletonPair_map n)
    hx hy hxy
  ext z
  rw [TopPair.range_ofSubset_map, hA]
  refine ⟨?_, fun hz ↦ ⟨e z, hz, e.symm_apply_apply z⟩⟩
  rintro ⟨w, hw, rfl⟩
  -- `hw` is the condition at `w`, and `e (e.symm w) = w`.
  have hw' : ‖((w : cellPullback p C n).val.1.2 : Fin n → ℝ)‖ = 1 := hw
  convert hw' using 4
  exact congrArg (fun q : cellPullback p C n ↦ q.val.1) (e.apply_symm_apply w)

end TopCat

end TauCeti
