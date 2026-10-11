/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.WreathProduct.Basic
public import TauCeti.GroupTheory.TransversalWord
public import TauCeti.Topology.Algebra.Group.TransversalWord
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Constructions.SumProd
public import Mathlib.Topology.Algebra.MulAction

/-!
# The monomial homomorphism of a subgroup

Given a subgroup `U ≤ G` and a transversal of its left cosets, the Schreier words of the
transversal assemble into a homomorphism from `G` to the permutation wreath product with base
`U` and top group the permutations of `G ⧸ U`. This is the group-theoretic input to the
transversal construction of the Evens norm.

The transversal word is Tau Ceti's `TauCeti.lWord`; the construction follows Evens,
*A generalization of the transfer map in the cohomology of groups*, §§2–3.
-/

public section

namespace TauCeti.ContCohomology

variable {G : Type*} [Group G]

/-- The monomial homomorphism associated to a subgroup and a transversal. Its base coordinate at
`u : G ⧸ U` is the Schreier word `lWord U t u g`, and its permutation coordinate is left
multiplication by `g` on `G ⧸ U`. The transversal condition ensures that every base coordinate lies
in `U`. -/
@[expose] noncomputable def monomialHom (U : Subgroup G) (t : G ⧸ U → G)
    (ht : ∀ u, (QuotientGroup.mk (t u) : G ⧸ U) = u) :
    G →* TauCeti.WreathProduct U (G ⧸ U) where
  toFun g :=
    ⟨fun u => ⟨lWord U t u g, lWord_mem U t ht u g⟩, MulAction.toPerm g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · funext u
      simp
    · ext u
      simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · funext u
      rw [TauCeti.PermutationWreathProduct.mul_left]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      simpa using (lWord_mul_lWord U t u g h).symm
    · ext u
      simp [mul_smul]

/-- Evaluation of the base coordinate of the monomial homomorphism is the corresponding
transversal word. -/
@[simp]
theorem monomialHom_left_apply (U : Subgroup G) (t : G ⧸ U → G)
    (ht : ∀ u, (QuotientGroup.mk (t u) : G ⧸ U) = u) (g : G) (u : G ⧸ U) :
    (monomialHom U t ht g).left u = ⟨lWord U t u g, lWord_mem U t ht u g⟩ := rfl

/-- The permutation coordinate of the monomial homomorphism is the action on left cosets. -/
@[simp]
theorem monomialHom_right (U : Subgroup G) (t : G ⧸ U → G)
    (ht : ∀ u, (QuotientGroup.mk (t u) : G ⧸ U) = u) (g : G) :
    (monomialHom U t ht g).right = MulAction.toPerm g := rfl

/-- The product topology on the base coordinates and on the pointwise permutation action, viewed
as a topology on the permutation wreath product. This is the topology used for the monomial map
when the coset space is finite and discrete. -/
@[instance_reducible] def monomialTopology (U : Subgroup G) [TopologicalSpace G] :
    TopologicalSpace (TauCeti.WreathProduct U (G ⧸ U)) :=
  letI : TopologicalSpace U := TopologicalSpace.induced Subtype.val inferInstance
  TopologicalSpace.induced
    (fun w : TauCeti.WreathProduct U (G ⧸ U) =>
      (w.left, fun x => (w.right x : G ⧸ U))) inferInstance

/-- For an open subgroup, the monomial homomorphism is continuous when the wreath product is
given the product topology on its base and permutation coordinates. The Schreier word is
continuous on each coset, and the permutation coordinate is continuous pointwise. -/
theorem continuous_monomialHom (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : OpenSubgroup G) (t : G ⧸ U.toSubgroup → G)
    (ht : ∀ u, (QuotientGroup.mk (t u) : G ⧸ U.toSubgroup) = u) :
    @Continuous G (TauCeti.WreathProduct U.toSubgroup (G ⧸ U.toSubgroup)) _
      (monomialTopology U.toSubgroup) (monomialHom U.toSubgroup t ht) := by
  let _ : TopologicalSpace U.toSubgroup := TopologicalSpace.induced Subtype.val inferInstance
  rw [monomialTopology, continuous_induced_rng]
  apply Continuous.prodMk
  · apply continuous_pi
    intro u
    exact continuous_induced_rng.mpr
      (TauCeti.continuous_lWord U.toSubgroup t U.isOpen u)
  · apply continuous_pi
    intro u
    simpa only [monomialHom_right, MulAction.toPerm_apply] using
      U.toSubgroup.continuous_smul_const u

end TauCeti.ContCohomology
