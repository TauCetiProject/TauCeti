/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Naturality

/-!
# Component groups of closed subgroups

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k` and
let `N ⊆ G` be the closed subgroup cut out by a Hopf ideal `I`. Its component group
`π₀(N)` is the group of connected components of `Spec (H ⧸ I)`, with the group structure
`TauCeti.FiniteTypeCommHopfAlgCat.instGroupConnectedComponents`. This file describes it through
the rational points of `N`, viewed inside `G(k)`:

* `TauCeti.HopfIdeal.ComponentGroup I` is `π₀(N)`, a finite group.
* `TauCeti.HopfIdeal.rationalComponentMap I : N(k) →* π₀(N)` sends a rational point of `N` to
  its connected component. It is surjective, and its kernel is `N°(k)`, the rational points of
  the identity component `I.identityComponent`. Hence `π₀(N) ≃* N(k) ⧸ N°(k)`
  (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`).
* `TauCeti.HopfIdeal.toComponentGroup I : π₀(N) →* π₀(G)` is induced by the inclusion `N ⊆ G`.
* `TauCeti.HopfIdeal.componentGroupConjugationEquiv` is the isomorphism `π₀(N) ≃* π₀(gNg⁻¹)`
  induced by conjugation by a rational point `g`; on rational points it sends the component
  of `n` to the component of `gng⁻¹`.

These are the maps by which component groups of particular closed subgroups, such as
centralizers, are compared under inclusion and conjugation.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1, for component groups of centralizers.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.HopfIdeal

universe u

open FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The component group `π₀(N)` of the closed subgroup `N` cut out by `I`: the connected
components of `Spec (H ⧸ I)`. -/
abbrev ComponentGroup (I : HopfIdeal k H) : Type u :=
  ConnectedComponents (PrimeSpectrum (quotient H I))

variable [IsAlgClosed k]

/-- The group structure on `π₀(N)` is that of the component group of the finite-type affine
group `H ⧸ I`. Instance search does not see through the bundled quotient `quotient H I`, so the
instance is restated here. -/
noncomputable instance (I : HopfIdeal k H) : Group I.ComponentGroup :=
  instGroupConnectedComponents (quotient H I)

section RationalComponentMap

/-- The component map of the closed subgroup `N` cut out by `I`: a rational point of `N`, viewed
in `G(k)`, goes to the connected component of `Spec (H ⧸ I)` containing it. -/
noncomputable def rationalComponentMap (I : HopfIdeal k H) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) →* I.ComponentGroup :=
  (FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I)).comp
    (CommHopfAlgCat.quotientPointsSubgroupIso H.obj I (CommAlgCat.of k k)).inv.hom

/-- The component map of `I` is the rational component map of the finite-type affine group
`H ⧸ I`, applied to the point of `H ⧸ I` through which `n` factors. -/
theorem rationalComponentMap_apply (I : HopfIdeal k H)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    I.rationalComponentMap n =
      FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I)
        (CommHopfAlgCat.liftQuotientPoint H.obj I (CommAlgCat.of k k) n
          ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I _
            (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))).mp n.2)) :=
  congrArg (FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I))
    (CommHopfAlgCat.quotientPointsSubgroupIso_inv_apply H.obj I _ n)

/-- On an included point of `H ⧸ I`, the component map of `I` is the rational component map of
the finite-type affine group `H ⧸ I`. -/
@[simp]
theorem rationalComponentMap_quotientPointsHom (I : HopfIdeal k H)
    (f : HopfAlgebra.points (R := k) (H := quotient H I) (CommAlgCat.of k k)) :
    I.rationalComponentMap
        ⟨CommHopfAlgCat.quotientPointsHom H.obj I (CommAlgCat.of k k) f,
          CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj I _ f⟩ =
      FiniteTypeCommHopfAlgCat.rationalComponentMap (quotient H I) f := by
  rw [HopfIdeal.rationalComponentMap_apply,
    (CommHopfAlgCat.liftQuotientPoint_eq_iff _ _ _ _ _ f).mpr rfl]

/-- Every connected component of a closed subgroup contains a rational point. -/
theorem rationalComponentMap_surjective (I : HopfIdeal k H) :
    Function.Surjective I.rationalComponentMap := by
  intro c
  obtain ⟨f, rfl⟩ := FiniteTypeCommHopfAlgCat.rationalComponentMap_surjective _ c
  exact ⟨_, rationalComponentMap_quotientPointsHom I f⟩

/-- A rational point of the closed subgroup `N` cut out by `I` lies in the identity component of
`N` exactly when it is a rational point of `N°`. -/
theorem rationalComponentMap_eq_one_iff (I : HopfIdeal k H)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    I.rationalComponentMap n = 1 ↔
      (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent (CommAlgCat.of k k) := by
  rw [HopfIdeal.rationalComponentMap_apply,
    FiniteTypeCommHopfAlgCat.rationalComponentMap_eq_one_iff,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff (quotient H I).obj,
    CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I.identityComponent]
  -- `N°` is cut out in `G` by the functions whose restriction to `N` vanishes on `N°`.
  constructor
  · intro h x hx
    have hx' := h _ ((mem_identityComponent I x).mp hx)
    rwa [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk,
      CommHopfAlgCat.liftQuotientPoint_mk] at hx'
  · intro h y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [CommHopfAlgCat.liftQuotientPoint_mk]
    exact h x ((mem_identityComponent I x).mpr
      (by rwa [CommHopfAlgCat.mkQuotient_apply, Ideal.Quotient.mkₐ_eq_mk]))

/-- The kernel of the component map of `N` consists of the rational points of `N°`. -/
theorem ker_rationalComponentMap (I : HopfIdeal k H) :
    I.rationalComponentMap.ker =
      (CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
        (CommAlgCat.of k k)).subgroupOf
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, rationalComponentMap_eq_one_iff]

/-- The identity-component points `N°(k)` form a normal subgroup of `N(k)`. -/
instance normal_quotientPointsSubgroup_identityComponent_subgroupOf (I : HopfIdeal k H) :
    ((CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
        (CommAlgCat.of k k)).subgroupOf
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))).Normal :=
  I.ker_rationalComponentMap ▸ MonoidHom.normal_ker _

/-- **The component group of a closed subgroup on rational points.** The component group of the
closed subgroup `N` cut out by `I` is `N(k) ⧸ N°(k)`. -/
noncomputable def quotientMulEquivComponentGroup (I : HopfIdeal k H) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) ⧸
        (CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
          (CommAlgCat.of k k)).subgroupOf
          (CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) ≃*
      I.ComponentGroup :=
  (QuotientGroup.quotientMulEquivOfEq I.ker_rationalComponentMap.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ I.rationalComponentMap_surjective)

/-- The isomorphism `N(k) ⧸ N°(k) ≃* π₀(N)` sends the class of `n` to its component. -/
@[simp]
theorem quotientMulEquivComponentGroup_mk (I : HopfIdeal k H)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    I.quotientMulEquivComponentGroup (QuotientGroup.mk n) = I.rationalComponentMap n :=
  (rfl)

end RationalComponentMap

section Inclusion

/-- The homomorphism `π₀(N) →* π₀(G)` induced by the inclusion of the closed subgroup `N` cut out
by `I`. -/
noncomputable def toComponentGroup (I : HopfIdeal k H) :
    I.ComponentGroup →* ConnectedComponents (PrimeSpectrum H) :=
  mapComponentGroup (mkQuotient H I)

/-- The inclusion of components sends the component of a rational point `n` of `N` to the
component of `n` in `G`. -/
@[simp]
theorem toComponentGroup_rationalComponentMap (I : HopfIdeal k H)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    I.toComponentGroup (I.rationalComponentMap n) =
      FiniteTypeCommHopfAlgCat.rationalComponentMap H n := by
  rw [HopfIdeal.rationalComponentMap_apply, toComponentGroup,
    mapComponentGroup_rationalComponentMap]
  have h := CommHopfAlgCat.quotientPointsHom_liftQuotientPoint H.obj I (CommAlgCat.of k k)
    (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I _ _).mp n.2)
  rw [CommHopfAlgCat.quotientPointsHom_apply] at h
  rw [BialgHom.mapDomain_apply]
  exact congrArg _ h

end Inclusion

section Conjugation

omit [IsAlgClosed k] in
/-- The coordinate isomorphism `H ⧸ J ≅ H ⧸ I` between a closed subgroup and its conjugate
`J = I.conjugate g`, in the category of finite-type commutative Hopf algebras. -/
private noncomputable def quotientConjugationIso (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (hJ : J = I.conjugate g) :
    quotient H J ≅ quotient H I :=
  ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk (I.quotientConjugationEquiv J g hJ))

omit [IsAlgClosed k] in
/-- The coordinate isomorphism of conjugation acts by the bialgebra equivalence
`HopfIdeal.quotientConjugationEquiv`. -/
private theorem quotientConjugationIso_hom_apply (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (hJ : J = I.conjugate g)
    (y : quotient H J) :
    toBialgHom (quotientConjugationIso I J g hJ).hom y = I.quotientConjugationEquiv J g hJ y :=
  (rfl)

/-- **Conjugation of component groups.** Conjugation by a rational point `g` induces an
isomorphism `π₀(N) ≃* π₀(gNg⁻¹)`, where `N` is cut out by `I` and `gNg⁻¹` by
`J = I.conjugate g`. -/
noncomputable def componentGroupConjugationEquiv (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (hJ : J = I.conjugate g) :
    I.ComponentGroup ≃* J.ComponentGroup :=
  mapComponentGroupMulEquiv (quotientConjugationIso I J g hJ)

/-- On rational points, the conjugation isomorphism sends the component of `n` to the component
of `gng⁻¹`. -/
theorem componentGroupConjugationEquiv_rationalComponentMap (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) (hJ : J = I.conjugate g)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv I J g hJ (I.rationalComponentMap n) =
      J.rationalComponentMap ⟨g * n * g⁻¹,
        hJ ▸ (CommHopfAlgCat.mul_mul_inv_mem_conjugate_iff I g n).mpr n.2⟩ := by
  rw [componentGroupConjugationEquiv, mapComponentGroupMulEquiv_apply,
    HopfIdeal.rationalComponentMap_apply, mapComponentGroup_rationalComponentMap,
    HopfIdeal.rationalComponentMap_apply]
  congr 1
  -- `gng⁻¹` is the point `n ∘ conj g`, which is what the coordinate isomorphism pulls back to.
  have hconj := HopfAlgebra.comp_pointConjugationAlgHom g
    (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
  simp only [Algebra.ofId_self, AlgHom.mapValue_id, MonoidHom.id_apply] at hconj
  refine ((CommHopfAlgCat.liftQuotientPoint_eq_iff H.obj J (CommAlgCat.of k k) _ _ _).mpr ?_).symm
  dsimp only
  rw [← hconj]
  apply WithConv.ofConv_injective
  ext a
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply, BialgHom.mapDomain_apply_apply,
    Ideal.Quotient.mkₐ_eq_mk, quotientConjugationIso_hom_apply, quotientConjugationEquiv_mk,
    CommHopfAlgCat.liftQuotientPoint_mk, WithConv.ofConv_toConv, AlgHom.comp_apply]

/-- Conjugation by the identity point induces the identity of `π₀(N)`. -/
@[simp]
theorem componentGroupConjugationEquiv_one (I : HopfIdeal k H) :
    componentGroupConjugationEquiv I I 1 (conjugate_one I).symm =
      MulEquiv.refl I.ComponentGroup := by
  ext c
  obtain ⟨n, rfl⟩ := I.rationalComponentMap_surjective c
  rw [componentGroupConjugationEquiv_rationalComponentMap, MulEquiv.refl_apply]
  congr 1
  exact Subtype.ext (by simp)

/-- Conjugating by `g` and then by `g'` is conjugating by `g' * g`. -/
theorem componentGroupConjugationEquiv_trans (I J L : HopfIdeal k H)
    (g g' : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g) (hL : L = J.conjugate g') :
    (componentGroupConjugationEquiv I J g hJ).trans
        (componentGroupConjugationEquiv J L g' hL) =
      componentGroupConjugationEquiv I L (g' * g) (by rw [hL, hJ, conjugate_mul]) := by
  ext c
  obtain ⟨n, rfl⟩ := I.rationalComponentMap_surjective c
  rw [MulEquiv.trans_apply, componentGroupConjugationEquiv_rationalComponentMap,
    componentGroupConjugationEquiv_rationalComponentMap,
    componentGroupConjugationEquiv_rationalComponentMap]
  congr 1
  exact Subtype.ext (by simp [mul_assoc])

end Conjugation

end TauCeti.HopfIdeal
