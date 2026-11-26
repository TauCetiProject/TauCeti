/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.KTheory.Basic
public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Pullback on topological `K⁰` and homotopy invariance

A continuous map `f : C(X, Y)` pulls finite-rank bundles over `Y` back to bundles over `X`, and
pullback preserves Whitney sums. It therefore induces an additive homomorphism
`TauCeti.TopologicalKZero.pullback 𝕜 f : K⁰(Y) →+ K⁰(X)`, `[E] ↦ [f* E]`, with no hypothesis on the
spaces. Pullback along the identity is the identity, pullback along a composite is the composite
of the pullbacks in the opposite order, and pullback is compatible with the rank homomorphism and
with its splitting by trivial bundles.

Over a paracompact R₁ base `X`, for instance a paracompact Hausdorff space, and for real or complex
scalars, pullbacks of bundles along homotopic maps are isomorphic
(`TauCeti.FiniteRankAtlas.nonempty_pullback_iso_pullback_of_homotopic`), so homotopic maps induce
the same homomorphism on `K⁰`. Consequently a homotopy equivalence between paracompact R₁ spaces
induces an isomorphism of their `K⁰` groups, and the `K⁰` of a contractible paracompact R₁ space is
`ℤ`, by the rank. This applies for instance to `ℝ`, although `ℝ` is not compact.

## Main definitions

* `TauCeti.TopologicalKZero.pullback`: the homomorphism `f* : K⁰(Y) →+ K⁰(X)`.
* `TauCeti.TopologicalKZero.pullbackAddEquiv`: the isomorphism `K⁰(Y) ≃+ K⁰(X)` induced by a
  homotopy equivalence `X ≃ₕ Y` of paracompact R₁ spaces.
* `TauCeti.TopologicalKZero.addEquivIntOfContractibleSpace`: `K⁰(X) ≃+ ℤ` for a contractible
  paracompact R₁ space `X`.

## Main results

* `TauCeti.TopologicalKZero.pullback_id`, `TauCeti.TopologicalKZero.pullback_comp`: functoriality.
* `TauCeti.TopologicalKZero.rankHom_pullback`, `TauCeti.TopologicalKZero.pullback_trivialHom`:
  compatibility with the rank and with trivial bundles.
* `TauCeti.TopologicalKZero.pullback_eq_of_homotopic`: homotopic maps out of a paracompact R₁
  space induce the same homomorphism on `K⁰`.

## References

* A. Hatcher, *Vector Bundles and K-Theory*, version 2.2 (2017), §2.1, p. 40, for the induced
  homomorphisms `f*` and their homotopy invariance over a compact Hausdorff base.
-/

public section

namespace TauCeti.TopologicalKZero

open CategoryTheory FiniteRankAtlas
open scoped ContinuousMap

universe u v w z

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} {Y : Type w} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

variable (𝕜) in
/-- The pullback homomorphism `f* : K⁰(Y) →+ K⁰(X)` induced by a continuous map `f : C(X, Y)`,
sending the class of a bundle `E` over `Y` to the class of its pullback `f* E` over `X`. -/
noncomputable def pullback (f : C(X, Y)) : TopologicalKZero 𝕜 Y →+ TopologicalKZero 𝕜 X :=
  SplitK0.map (pullbackFunctor 𝕜 f)

/-- The pullback homomorphism sends the class of a bundle to the class of its pullback. -/
@[simp]
theorem pullback_of (f : C(X, Y)) (A : FiniteRankAtlas 𝕜 Y) :
    pullback 𝕜 f (SplitK0.of A) = SplitK0.of (A.pullback f) :=
  SplitK0.map_of _ A

variable (𝕜 X) in
/-- Pullback along the identity is the identity of `K⁰`. -/
@[simp]
theorem pullback_id : pullback 𝕜 (ContinuousMap.id X) = AddMonoidHom.id _ := by
  exact (SplitK0.map_congr fun A => ⟨(pullbackFunctorIdIso 𝕜 X).app A⟩).trans SplitK0.map_id

variable (𝕜) in
/-- Pullback along a composite is the composite of the pullbacks, in the opposite order. -/
theorem pullback_comp (g : C(Y, Z)) (f : C(X, Y)) :
    pullback 𝕜 (g.comp f) = (pullback 𝕜 f).comp (pullback 𝕜 g) := by
  rw [pullback, pullback, pullback, ← SplitK0.map_comp]
  -- Pullback along a composite is literally the iterated pullback (`pullbackFunctor_comp`).
  exact SplitK0.map_congr fun A => ⟨Iso.refl _⟩

/-- Pulling back twice is pulling back along the composite. -/
@[simp]
theorem pullback_pullback (g : C(Y, Z)) (f : C(X, Y)) (a : TopologicalKZero 𝕜 Z) :
    pullback 𝕜 f (pullback 𝕜 g a) = pullback 𝕜 (g.comp f) a := by
  rw [pullback_comp, AddMonoidHom.comp_apply]

/-- The rank of a pulled-back class is the rank of the class composed with the map. -/
@[simp]
theorem rankHom_pullback (f : C(X, Y)) (a : TopologicalKZero 𝕜 Y) :
    rankHom 𝕜 X (pullback 𝕜 f a) = (rankHom 𝕜 Y a).comap f := by
  have h : (rankHom 𝕜 X).comp (pullback 𝕜 f) =
      (LocallyConstant.comapAddMonoidHom f).comp (rankHom 𝕜 Y) :=
    SplitK0.hom_ext fun A => LocallyConstant.ext fun x => by
      simp only [AddMonoidHom.comp_apply, pullback_of, rankHom_of_apply, rank_pullback,
        LocallyConstant.comapAddMonoidHom_apply, LocallyConstant.coe_comap,
        Function.comp_apply]
  exact DFunLike.congr_fun h a

/-- Pullback sends the difference of trivial bundles with a given locally constant rank to the
difference of trivial bundles with the pulled-back rank. -/
@[simp]
theorem pullback_trivialHom (f : C(X, Y)) (r : LocallyConstant Y ℤ) :
    pullback 𝕜 f (trivialHom 𝕜 Y r) = trivialHom 𝕜 X (r.comap f) := by
  have h (s : LocallyConstant Y ℤ) : (s.map Int.toNat).comap f = (s.comap f).map Int.toNat :=
    LocallyConstant.ext fun _ => by
      simp only [LocallyConstant.coe_comap, LocallyConstant.map_apply, Function.comp_apply]
  have hneg : (-r).comap f = -r.comap f := map_neg (LocallyConstant.comapAddMonoidHom f) r
  rw [trivialHom_apply, trivialHom_apply, map_sub, pullback_of, pullback_of, pullback_trivial,
    pullback_trivial, h, h, hneg]

section Homotopy

variable [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜]

/-- **Homotopy invariance of `K⁰`.** Homotopic maps out of a paracompact R₁ space induce the same
homomorphism on `K⁰`. -/
theorem pullback_eq_of_homotopic [R1Space X] [ParacompactSpace X] {f₀ f₁ : C(X, Y)}
    (h : f₀.Homotopic f₁) : pullback 𝕜 f₀ = pullback 𝕜 f₁ :=
  SplitK0.map_congr fun A => A.nonempty_pullback_iso_pullback_of_homotopic h

variable [R1Space X] [ParacompactSpace X] [R1Space Y] [ParacompactSpace Y]

variable (𝕜) in
/-- A homotopy equivalence `X ≃ₕ Y` of paracompact R₁ spaces induces an isomorphism
`K⁰(Y) ≃+ K⁰(X)`, by pullback along either of its maps. -/
noncomputable def pullbackAddEquiv (e : X ≃ₕ Y) : TopologicalKZero 𝕜 Y ≃+ TopologicalKZero 𝕜 X :=
  AddMonoidHom.toAddEquiv (pullback 𝕜 e.toFun) (pullback 𝕜 e.invFun)
    (by rw [← pullback_comp, pullback_eq_of_homotopic e.right_inv, pullback_id])
    (by rw [← pullback_comp, pullback_eq_of_homotopic e.left_inv, pullback_id])

/-- The isomorphism induced by a homotopy equivalence is pullback along its forward map. -/
@[simp]
theorem pullbackAddEquiv_apply (e : X ≃ₕ Y) (a : TopologicalKZero 𝕜 Y) :
    pullbackAddEquiv 𝕜 e a = pullback 𝕜 e.toFun a :=
  (rfl)

/-- The inverse of the isomorphism induced by a homotopy equivalence is pullback along its
backward map. -/
@[simp]
theorem pullbackAddEquiv_symm_apply (e : X ≃ₕ Y) (a : TopologicalKZero 𝕜 X) :
    (pullbackAddEquiv 𝕜 e).symm a = pullback 𝕜 e.invFun a :=
  (rfl)

end Homotopy

section Contractible

variable [NormedAlgebra ℝ 𝕜] [CompleteSpace 𝕜] [R1Space X] [ParacompactSpace X]
  [ContractibleSpace X]

variable (𝕜 X) in
/-- The `K⁰` of a contractible paracompact R₁ space is `ℤ`, by the rank of a bundle at any point
(`TauCeti.TopologicalKZero.addEquivIntOfContractibleSpace_apply`). -/
noncomputable def addEquivIntOfContractibleSpace : TopologicalKZero 𝕜 X ≃+ ℤ :=
  (pullbackAddEquiv 𝕜 (ContractibleSpace.hequiv_unit X).some).symm.trans
    (rankAddEquivInt 𝕜 Unit)

/-- The isomorphism `K⁰(X) ≃+ ℤ` of a contractible space evaluates the rank at any point. -/
theorem addEquivIntOfContractibleSpace_apply (a : TopologicalKZero 𝕜 X) (x : X) :
    addEquivIntOfContractibleSpace 𝕜 X a = rankHom 𝕜 X a x := by
  rw [addEquivIntOfContractibleSpace, AddEquiv.trans_apply, pullbackAddEquiv_symm_apply,
    rankAddEquivInt_apply, rankHom_pullback, LocallyConstant.coe_comap, Function.comp_apply]
  exact (rankHom 𝕜 X a).apply_eq_of_preconnectedSpace _ _

/-- The isomorphism `K⁰(X) ≃+ ℤ` of a contractible space sends the class of a bundle to its rank,
which is the same at every point. -/
theorem addEquivIntOfContractibleSpace_of (A : FiniteRankAtlas 𝕜 X) (x : X) :
    addEquivIntOfContractibleSpace 𝕜 X (SplitK0.of A) = A.rank x := by
  rw [addEquivIntOfContractibleSpace_apply _ x, rankHom_of_apply]

/-- The inverse of the isomorphism `K⁰(X) ≃+ ℤ` of a contractible space sends `n` to the class of
the trivial bundle of rank `n`. -/
@[simp]
theorem addEquivIntOfContractibleSpace_symm_apply (n : ℤ) :
    (addEquivIntOfContractibleSpace 𝕜 X).symm n = trivialHom 𝕜 X (LocallyConstant.const X n) := by
  rw [AddEquiv.symm_apply_eq, addEquivIntOfContractibleSpace_apply _ (Classical.arbitrary X),
    rankHom_trivialHom, LocallyConstant.coe_const, Function.const_apply]

end Contractible

end TauCeti.TopologicalKZero
