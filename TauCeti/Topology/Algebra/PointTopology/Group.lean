/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Topology.Algebra.PointTopology.Functoriality

/-!
# The topological group of points of an affine group scheme

Let `H` be a Hopf algebra over `k` and `R` a commutative topological `k`-algebra. The points
`WithConv (H →ₐ[k] R)` form a group under convolution, with `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and
`f⁻¹ = f ∘ S` for the antipode `S`. When `H` is commutative, these are the `R`-points of the affine
group scheme `Spec H`. With the point topology, the coarsest topology making every evaluation
continuous, this group is a topological group. Each value of a product is a finite sum of products
of values of the factors, so multiplication is continuous when `R` is a topological semiring; each
value of an inverse is a value of the point itself, so inversion is continuous for every topology
on `R`. The coefficients `R` must be commutative, but `H` need not be, and no finiteness or
separation hypothesis on `H` or `R` is needed.

This is the topology on rational points used for groups of points over local fields and adeles:
for an affine group `G` over a nonarchimedean local field `E`, the group `G(E)` is a topological
group in this way, as is `𝒢(O)` for an affine group `𝒢` over the valuation ring `O` of `E`. When
`G` is of finite type over `E`, the points are locally compact
(`TauCeti.PointTopology.locallyCompactSpace_of_finiteType`), so these topological groups carry
the Haar measures and the open subgroups of local representation theory. Without a finiteness
hypothesis the points need not be locally compact: for a polynomial ring in infinitely many
variables they form an infinite product of copies of `E`.

The group of points is functorial in both variables, and the induced maps are continuous: a
bialgebra map `H₁ → H₂` induces the continuous homomorphism `BialgHom.mapDomain` from the points of
`H₂` to those of `H₁`, and a continuous algebra map `R → R'` of coefficients induces the continuous
homomorphism `AlgHom.mapValue`. Since the group of points carries the point topology of the
underlying homomorphisms, `AlgHom.mapValue ψ` is an embedding or a closed embedding whenever `ψ`
is, and an open embedding when `ψ` is and the coordinate algebra is of finite type. An
isomorphism of topological coefficient algebras induces an isomorphism of topological monoids of
points. No topology on the source of `ψ` is needed to locate its points among those with values in
the target: when `ψ` is injective with closed image, its image on points is closed, and when the
image of `ψ` is discrete and the coordinate algebra is commutative of finite type, its image on
points is discrete. This is how the rational points of an affine group over a number field sit in
its adelic points.

## Main declarations

* `TauCeti.PointTopology.instContinuousMulWithConv`: the convolution product on the points of a
  bialgebra is continuous.
* `TauCeti.PointTopology.instContinuousInvWithConv`: the convolution inverse on the points of a
  Hopf algebra is continuous.
* `TauCeti.PointTopology.isTopologicalGroup`: the points of a Hopf algebra form a topological
  group.
* `BialgHom.continuous_mapDomain` and `AlgHom.continuous_mapValue`: functoriality of the points is
  continuous in the coordinate algebra and in continuous maps of coefficients.
* `AlgHom.isEmbedding_mapValue`, `AlgHom.isClosedEmbedding_mapValue` and
  `AlgHom.isOpenEmbedding_mapValue`: change of coefficients along an embedding, closed embedding
  or open embedding of coefficient rings.
* `AlgHom.isClosed_range_mapValue` and `AlgHom.isDiscrete_range_mapValue`: change of
  coefficients along an injective map with closed, respectively discrete, image.
* `BialgHom.isClosedEmbedding_mapDomain_of_surjective`: a closed immersion of affine groups induces
  a closed embedding of groups of points over a T1 ring.
* `ContinuousAlgEquiv.mapValueContinuousMulEquiv`: change of coefficients along an isomorphism of
  topological coefficient algebras, as an isomorphism of topological monoids of points.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1 and the discussion after it, p. 2, and Ex. 2.2–2.3, p. 3.
-/

public section

open Coalgebra WithConv

namespace TauCeti.PointTopology

variable {k H R : Type*} [CommSemiring k] [Semiring H] [CommSemiring R] [Algebra k R]
  [TopologicalSpace R]

section Bialgebra

variable [Bialgebra k H] [IsTopologicalSemiring R]

/-- The convolution product on the points of a bialgebra is continuous for the point topology,
when the coefficients form a topological semiring. -/
instance instContinuousMulWithConv : ContinuousMul (WithConv (H →ₐ[k] R)) where
  continuous_mul := continuous_withConv_iff.2 fun h ↦ by
    -- Writing `Δ h = ∑ i, h₁ i ⊗ h₂ i`, the value of `f * g` at `h` is `∑ i, f (h₁ i) * g (h₂ i)`.
    have hsum (p : WithConv (H →ₐ[k] R) × WithConv (H →ₐ[k] R)) : (p.1 * p.2).ofConv h =
        ∑ i ∈ (ℛ k h).index, p.1.ofConv ((ℛ k h).left i) * p.2.ofConv ((ℛ k h).right i) := by
      rw [AlgHom.convMul_apply, ← (ℛ k h).eq, map_sum]
      simp
    simp_rw [hsum]
    refine continuous_finsetSum _ fun i _ ↦ .mul ?_ ?_
    · exact (continuous_eval_ofConv _).comp continuous_fst
    · exact (continuous_eval_ofConv _).comp continuous_snd

end Bialgebra

section HopfAlgebra

variable [HopfAlgebra k H]

/-- The convolution inverse `f ↦ f ∘ S` on the points of a Hopf algebra is continuous for the
point topology, for every topology on the coefficients. -/
instance instContinuousInvWithConv : ContinuousInv (WithConv (H →ₐ[k] R)) where
  continuous_inv := continuous_withConv_iff.2 fun h ↦ by
    simp_rw [WithConv.algHom_inv_apply]
    exact continuous_eval_ofConv _

/-- The points `WithConv (H →ₐ[k] R)` of a Hopf algebra, with the convolution group structure and
the point topology, form a topological group when the coefficients form a topological semiring. -/
instance isTopologicalGroup [IsTopologicalSemiring R] :
    IsTopologicalGroup (WithConv (H →ₐ[k] R)) where

end HopfAlgebra

end TauCeti.PointTopology

section Functoriality

variable {k H₁ H₂ R R' : Type*} [CommSemiring k] [Semiring H₁] [Bialgebra k H₁] [Semiring H₂]
  [Bialgebra k H₂] [CommSemiring R] [Algebra k R] [TopologicalSpace R] [CommSemiring R']
  [Algebra k R'] [TopologicalSpace R']

open Topology TauCeti.PointTopology

/-- Precomposition with a bialgebra map `φ : H₁ → H₂` is a continuous homomorphism from the points
of `H₂` to those of `H₁`. -/
@[continuity, fun_prop]
theorem BialgHom.continuous_mapDomain (φ : H₁ →ₐc[k] H₂) :
    Continuous (mapDomain (A := R) φ) :=
  continuous_withConv_iff.2 fun h ↦ by
    simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply]
    exact continuous_eval_ofConv _

/-- Postcomposition with a continuous algebra map `ψ : R → R'` of coefficients is a continuous
homomorphism from the points with values in `R` to those with values in `R'`. -/
@[fun_prop]
theorem AlgHom.continuous_mapValue {ψ : R →ₐ[k] R'} (hψ : Continuous ψ) :
    Continuous (mapValue (H := H₁) ψ) :=
  continuous_withConv_iff.2 fun h ↦ by
    simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]
    exact hψ.comp (continuous_eval_ofConv _)

/-- An embedding of coefficient rings induces an embedding of groups of points. -/
theorem AlgHom.isEmbedding_mapValue {ψ : R →ₐ[k] R'} (hψ : IsEmbedding ψ) :
    IsEmbedding (mapValue (H := H₁) ψ) := by
  rw [← isHomeomorph_ofConv.isEmbedding.of_comp_iff, AlgHom.ofConv_comp_mapValue]
  exact (isEmbedding_map_codomain ψ hψ).comp isHomeomorph_ofConv.isEmbedding

/-- A closed embedding of coefficient rings induces a closed embedding of groups of points. -/
theorem AlgHom.isClosedEmbedding_mapValue {ψ : R →ₐ[k] R'} (hψ : IsClosedEmbedding ψ) :
    IsClosedEmbedding (mapValue (H := H₁) ψ) := by
  rw [← isHomeomorph_ofConv.isClosedEmbedding.of_comp_iff, AlgHom.ofConv_comp_mapValue]
  exact (isClosedEmbedding_map_codomain ψ hψ).comp isHomeomorph_ofConv.isClosedEmbedding

/-- An open embedding of coefficient rings induces an open embedding of groups of points when
the coordinate algebra is of finite type. -/
theorem AlgHom.isOpenEmbedding_mapValue [Algebra.FiniteType k H₁] {ψ : R →ₐ[k] R'}
    (hψ : IsOpenEmbedding ψ) : IsOpenEmbedding (mapValue (H := H₁) ψ) := by
  rw [← IsOpenEmbedding.of_comp_iff _ isHomeomorph_ofConv.isOpenEmbedding,
    AlgHom.ofConv_comp_mapValue]
  exact (isOpenEmbedding_map_codomain ψ hψ).comp isHomeomorph_ofConv.isOpenEmbedding

/-- An isomorphism `e : R ≃A[k] R'` of topological coefficient algebras induces, by
post-composition, an isomorphism of topological monoids of points
`WithConv (H₁ →ₐ[k] R) ≃ₜ* WithConv (H₁ →ₐ[k] R')`; it is `AlgEquiv.mapValueMulEquiv` with its
continuity in both directions. -/
noncomputable def ContinuousAlgEquiv.mapValueContinuousMulEquiv (e : R ≃A[k] R') :
    WithConv (H₁ →ₐ[k] R) ≃ₜ* WithConv (H₁ →ₐ[k] R') where
  toMulEquiv := e.toAlgEquiv.mapValueMulEquiv
  continuous_toFun := continuous_withConv_iff.2 fun h ↦ by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, MulEquiv.coe_toEquiv,
      AlgEquiv.mapValueMulEquiv_apply, AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, ContinuousAlgEquiv.coe_toAlgEquiv]
    exact e.continuous.comp (continuous_eval_ofConv h)
  continuous_invFun := continuous_withConv_iff.2 fun h ↦ by
    simp only [MulEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, MulEquiv.coe_toEquiv_symm,
      AlgEquiv.mapValueMulEquiv_symm_apply, AlgHom.mapValue_apply, ofConv_toConv,
      AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ← ContinuousAlgEquiv.symm_toAlgEquiv,
      ContinuousAlgEquiv.coe_toAlgEquiv]
    exact e.symm.continuous.comp (continuous_eval_ofConv h)

@[simp]
theorem ContinuousAlgEquiv.mapValueContinuousMulEquiv_apply_apply (e : R ≃A[k] R')
    (x : WithConv (H₁ →ₐ[k] R)) (h : H₁) :
    (e.mapValueContinuousMulEquiv x).ofConv h = e (x.ofConv h) := by
  simp [mapValueContinuousMulEquiv]

@[simp]
theorem ContinuousAlgEquiv.mapValueContinuousMulEquiv_symm_apply_apply (e : R ≃A[k] R')
    (x : WithConv (H₁ →ₐ[k] R')) (h : H₁) :
    (e.mapValueContinuousMulEquiv.symm x).ofConv h = e.symm (x.ofConv h) := by
  obtain ⟨y, rfl⟩ := (e.mapValueContinuousMulEquiv (H₁ := H₁)).surjective x
  simp

end Functoriality

section Range

variable {k H R R' : Type*} [CommSemiring k] [CommSemiring R] [Algebra k R] [CommSemiring R']
  [Algebra k R'] [TopologicalSpace R']

open TauCeti.PointTopology

/-- If an injective coefficient map `ψ : R → R'` has closed image, then the points with values in
`R` form a closed subset of the convolution monoid of points with values in `R'`, with no topology
on `R` and no finiteness assumption on the bialgebra. -/
theorem AlgHom.isClosed_range_mapValue [Semiring H] [Bialgebra k H] {ψ : R →ₐ[k] R'}
    (hψ : Function.Injective ψ) (hc : IsClosed (Set.range ψ)) :
    IsClosed (Set.range (mapValue (H := H) ψ)) := by
  rw [AlgHom.range_mapValue]
  exact (isClosed_range_map_codomain ψ hψ hc).preimage isHomeomorph_ofConv.continuous

/-- If an injective coefficient map `ψ : R → R'` has discrete image, then the points with values
in `R` of a commutative bialgebra of finite type form a discrete subset of the convolution monoid of
points with values in `R'`. -/
theorem AlgHom.isDiscrete_range_mapValue [CommSemiring H] [Bialgebra k H] [Algebra.FiniteType k H]
    {ψ : R →ₐ[k] R'} (hψ : Function.Injective ψ) (hd : IsDiscrete (Set.range ψ)) :
    IsDiscrete (Set.range (mapValue (H := H) ψ)) := by
  rw [AlgHom.range_mapValue]
  exact (isDiscrete_range_map_codomain ψ hψ hd).preimage
    isHomeomorph_ofConv.continuous.continuousOn WithConv.ofConv_injective

end Range

section ClosedImmersion

variable {k H₁ H₂ R : Type*} [CommSemiring k] [Ring H₁] [Bialgebra k H₁] [Ring H₂]
  [Bialgebra k H₂] [CommRing R] [Algebra k R] [TopologicalSpace R] [T1Space R]

open Topology TauCeti.PointTopology

/-- Over a T1 ring of coefficients, precomposition with a surjective bialgebra map `φ : H₁ → H₂`,
that is, a closed immersion of affine groups, is a closed embedding of groups of points. -/
theorem BialgHom.isClosedEmbedding_mapDomain_of_surjective {φ : H₁ →ₐc[k] H₂}
    (hφ : Function.Surjective φ) : IsClosedEmbedding (mapDomain (A := R) φ) := by
  have hcomp : ofConv ∘ mapDomain (A := R) φ =
      (fun x : H₂ →ₐ[k] R ↦ x.comp (φ : H₁ →ₐ[k] H₂)) ∘ ofConv := by
    funext x
    simp [BialgHom.mapDomain_apply]
  rw [← (isHomeomorph_ofConv (k := k) (A := H₁) (R := R)).isClosedEmbedding.of_comp_iff, hcomp]
  exact (isClosedEmbedding_comap_of_surjective (φ : H₁ →ₐ[k] H₂) hφ).comp
    (isHomeomorph_ofConv (k := k) (A := H₂) (R := R)).isClosedEmbedding

end ClosedImmersion
