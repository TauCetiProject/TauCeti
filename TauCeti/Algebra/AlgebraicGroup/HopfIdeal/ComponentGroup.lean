/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

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
* `TauCeti.HopfIdeal.componentGroupInclusion I : π₀(N) →* π₀(G)` is induced by the inclusion
  `N ⊆ G` (trivial when `G` is connected, `TauCeti.HopfIdeal.componentGroupInclusion_eq_one`).
* `TauCeti.HopfIdeal.componentGroupEquivOfEq` and `TauCeti.HopfIdeal.componentGroupEquivOfEqBot`
  transport component groups along equalities of Hopf ideals and identify `π₀(V(⊥)) ≃* π₀(G)`.
* `TauCeti.HopfIdeal.componentGroupMap I J f h : π₀(N') →* π₀(N)` is induced by a homomorphism
  `φ : G' → G` mapping the closed subgroup `N'` cut out by `J` into `N`. It commutes with the
  ambient inclusions (`TauCeti.HopfIdeal.componentGroupInclusion_comp_componentGroupMap`) and is
  surjective when the coordinate map of `φ` is injective and `N'` is the inverse image of `N`
  (`TauCeti.HopfIdeal.componentGroupMap_surjective`).

These are the maps by which component groups of particular closed subgroups, such as
centralizers, are compared under inclusion and homomorphisms. (Conjugation of closed-subgroup
component groups lives in `TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation`.)

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
            (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))).mp n.property)) :=
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
@[simp]
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

/-- If the coordinate morphism `u : H ⧸ I ⟶ K ⧸ J` is induced by an algebra map `F : H → K`, then
`π₀(u)` sends the component of a rational point `n` of `J` to the component of the point
`n ∘ F` of `I`. -/
theorem mapComponentGroup_rationalComponentMap_of_mk
    {K : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H} {J : HopfIdeal k K}
    (u : quotient H I ⟶ quotient K J) (F : H →ₐ[k] K)
    (hu : ∀ a : H, toBialgHom u (Ideal.Quotient.mk I.toIdeal a) =
      Ideal.Quotient.mk J.toIdeal (F a))
    (n : CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k))
    (m : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k))
    (hm : (m : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) =
      toConv ((n : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)).ofConv.comp F)) :
    mapComponentGroup u (J.rationalComponentMap n) = I.rationalComponentMap m := by
  rw [HopfIdeal.rationalComponentMap_apply, mapComponentGroup_rationalComponentMap,
    HopfIdeal.rationalComponentMap_apply]
  congr 1
  refine ((CommHopfAlgCat.liftQuotientPoint_eq_iff H.obj I (CommAlgCat.of k k) _ _ _).mpr ?_).symm
  rw [hm]
  apply WithConv.ofConv_injective
  ext a
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply, BialgHom.mapDomain_apply_apply,
    Ideal.Quotient.mkₐ_eq_mk, hu, CommHopfAlgCat.liftQuotientPoint_mk, WithConv.ofConv_toConv,
    AlgHom.comp_apply]

end RationalComponentMap

section Inclusion

/-- The homomorphism `π₀(N) →* π₀(G)` induced by the inclusion of the closed subgroup `N` cut out
by `I`. It need not be injective. -/
noncomputable def componentGroupInclusion (I : HopfIdeal k H) :
    I.ComponentGroup →* ConnectedComponents (PrimeSpectrum H) :=
  mapComponentGroup (mkQuotient H I)

/-- The inclusion of components sends the component of a rational point `n` of `N` to the
component of `n` in `G`. -/
@[simp]
theorem componentGroupInclusion_rationalComponentMap (I : HopfIdeal k H)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    I.componentGroupInclusion (I.rationalComponentMap n) =
      FiniteTypeCommHopfAlgCat.rationalComponentMap H n := by
  rw [HopfIdeal.rationalComponentMap_apply, componentGroupInclusion,
    mapComponentGroup_rationalComponentMap]
  have h := CommHopfAlgCat.quotientPointsHom_liftQuotientPoint H.obj I (CommAlgCat.of k k)
    (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj I _ _).mp n.property)
  rw [CommHopfAlgCat.quotientPointsHom_apply] at h
  rw [BialgHom.mapDomain_apply]
  exact congrArg _ h

/-- If `G` is connected, the homomorphism `π₀(N) →* π₀(G)` induced by the inclusion `N ⊆ G` of
any closed subgroup is trivial (even though `π₀(N)` itself may be nontrivial). -/
theorem componentGroupInclusion_eq_one (I : HopfIdeal k H)
    [ConnectedSpace (PrimeSpectrum H)] (C : I.ComponentGroup) :
    I.componentGroupInclusion C = 1 :=
  Subsingleton.elim _ _

end Inclusion

section Transport

/-- Transport a closed-subgroup component group across an equality of Hopf ideals. -/
noncomputable def componentGroupEquivOfEq {I J : HopfIdeal k H} (hIJ : I = J) :
    I.ComponentGroup ≃* J.ComponentGroup := by
  subst hIJ
  exact MulEquiv.refl _

/-- Transporting a rational-point component across an equality of Hopf ideals preserves the
underlying rational point. -/
@[simp]
theorem componentGroupEquivOfEq_rationalComponentMap {I J : HopfIdeal k H} (hIJ : I = J)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupEquivOfEq hIJ (I.rationalComponentMap n) =
      J.rationalComponentMap ⟨n.val, hIJ ▸ n.property⟩ := by
  subst hIJ
  rfl

/-- Reflexive transport on closed-subgroup component groups is the identity equivalence. -/
@[simp]
theorem componentGroupEquivOfEq_refl (I : HopfIdeal k H) (h : I = I) :
    componentGroupEquivOfEq h = MulEquiv.refl I.ComponentGroup := by
  rw [componentGroupEquivOfEq]

/-- The inverse of a closed-subgroup component-group transport is transport along the symmetric
equality. -/
@[simp]
theorem componentGroupEquivOfEq_symm {I J : HopfIdeal k H} (hIJ : I = J) :
    (componentGroupEquivOfEq hIJ).symm = componentGroupEquivOfEq hIJ.symm := by
  subst hIJ
  rfl

/-- Composing two closed-subgroup component-group transports gives the transport along the
transitive equality. -/
@[simp]
theorem componentGroupEquivOfEq_trans {I J L : HopfIdeal k H} (hIJ : I = J) (hJL : J = L) :
    (componentGroupEquivOfEq hIJ).trans (componentGroupEquivOfEq hJL) =
      componentGroupEquivOfEq (hIJ.trans hJL) := by
  subst hIJ hJL
  rfl

/-- Transporting a closed-subgroup component group along `I = ⊥` identifies it with `π₀(G)`. -/
noncomputable def componentGroupEquivOfEqBot {I : HopfIdeal k H} (hI : I = ⊥) :
    I.ComponentGroup ≃* ConnectedComponents (PrimeSpectrum H) :=
  let e : H ≅ quotient H I :=
    (quotientBotIso H).symm ≪≫ eqToIso (congrArg (quotient H) hI.symm)
  mapComponentGroupMulEquiv e

/-- On rational points, the identification `π₀(V(⊥)) ≃* π₀(G)` sends a rational point to its
ambient component. -/
@[simp]
theorem componentGroupEquivOfEqBot_rationalComponentMap {I : HopfIdeal k H} (hI : I = ⊥)
    (n : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupEquivOfEqBot hI (I.rationalComponentMap n) =
      FiniteTypeCommHopfAlgCat.rationalComponentMap H n := by
  have he :
      ((quotientBotIso H).symm ≪≫ eqToIso (congrArg (quotient H) hI.symm)).hom =
        mkQuotient H I := by
    rw [Iso.trans_hom, Iso.symm_hom, quotientBotIso_inv, eqToIso.hom,
      mkQuotient_comp_eqToHom hI]
  rw [componentGroupEquivOfEqBot, mapComponentGroupMulEquiv_apply, he]
  exact I.componentGroupInclusion_rationalComponentMap n

end Transport

section Map

variable {K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Component groups under homomorphisms.** Let `φ : G' → G` be a homomorphism of affine
groups with coordinate arrow `f : H ⟶ K`, mapping the closed subgroup `N'` cut out by `J` into the
closed subgroup `N` cut out by `I` (that is, `I.map f ≤ J`). Then `φ` induces
`π₀(N') →* π₀(N)`. -/
noncomputable def componentGroupMap (I : HopfIdeal k H) (J : HopfIdeal k K) (f : H ⟶ K)
    (h : I.map (toBialgHom f) ≤ J) : J.ComponentGroup →* I.ComponentGroup :=
  mapComponentGroup (quotientMap I J f h)

/-- The homomorphism `componentGroupMap` is `mapComponentGroup` on `quotientMap`. -/
theorem componentGroupMap_eq_mapComponentGroup (I : HopfIdeal k H) (J : HopfIdeal k K)
    (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) :
    componentGroupMap I J f h = mapComponentGroup (quotientMap I J f h) := by
  rw [componentGroupMap]

/-- On rational points, the induced map of component groups sends the component of `c` to the
component of `φ(c)`. -/
@[simp]
theorem componentGroupMap_rationalComponentMap (I : HopfIdeal k H) (J : HopfIdeal k K)
    (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J)
    (c : CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k)) :
    componentGroupMap I J f h (J.rationalComponentMap c) =
      I.rationalComponentMap
        ⟨BialgHom.mapDomain (A := k) (toBialgHom f) c,
          CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le f.hom h _ c.property⟩ :=
  mapComponentGroup_rationalComponentMap_of_mk _ (toBialgHom f) (quotientMap_mk I J f h) _ _
    (BialgHom.mapDomain_apply _ _)

/-- For nested closed subgroups `V(J) ⊆ V(I)` (`I ≤ J`), the induced component-group map
`π₀(V(J)) → π₀(V(I))` agrees with the inclusion `V(J)(k) ⊆ V(I)(k)`. -/
@[simp]
theorem
    _root_.TauCeti.FiniteTypeCommHopfAlgCat.mapComponentGroup_quotientMapOfLe_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) {I J : HopfIdeal k H} (hIJ : I ≤ J)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj J (CommAlgCat.of k k)) :
    mapComponentGroup (quotientMapOfLe H hIJ) (J.rationalComponentMap g) =
      I.rationalComponentMap
        ⟨g.val, CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj hIJ _ g.property⟩ := by
  have h := componentGroupMap_rationalComponentMap I J (𝟙 H)
    (by rwa [toBialgHom_id, HopfIdeal.map_id]) g
  simpa only [componentGroupMap, quotientMap_id, toBialgHom_id,
    BialgHom.mapDomain_id, MonoidHom.id_apply] using h

/-- Along the identity morphism, the induced map of component groups is the identity. -/
@[simp]
theorem componentGroupMap_id (I : HopfIdeal k H) (h : I.map (toBialgHom (𝟙 H)) ≤ I) :
    componentGroupMap I I (𝟙 H) h = MonoidHom.id I.ComponentGroup := by
  rw [componentGroupMap, quotientMap_id, quotientMapOfLe_refl, mapComponentGroup_id]

/-- Induced maps of component groups compose contravariantly along composites of
homomorphisms. -/
@[simp]
theorem componentGroupMap_comp {L : FiniteTypeCommHopfAlgCat.{u, u} k} (I : HopfIdeal k H)
    (J : HopfIdeal k K) (M : HopfIdeal k L) (f : H ⟶ K) (g : K ⟶ L)
    (hf : I.map (toBialgHom f) ≤ J) (hg : J.map (toBialgHom g) ≤ M) :
    (componentGroupMap I J f hf).comp (componentGroupMap J M g hg) =
      componentGroupMap I M (f ≫ g) (by
        rw [toBialgHom_comp, ← HopfIdeal.map_map]
        exact (HopfIdeal.map_mono (toBialgHom g) hf).trans hg) := by
  rw [componentGroupMap, componentGroupMap, componentGroupMap, ← mapComponentGroup_comp,
    quotientMap_comp]

/-- Transporting the target of `componentGroupMap` along an equality of Hopf ideals agrees with
`componentGroupMap` at the transported ideal. -/
theorem componentGroupEquivOfEq_comp_componentGroupMap {I I' : HopfIdeal k H}
    (hI : I = I') (J : HopfIdeal k K) (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) :
    (componentGroupEquivOfEq hI).toMonoidHom.comp (componentGroupMap I J f h) =
      componentGroupMap I' J f (hI ▸ h) := by
  subst hI
  rfl

/-- Transporting the source of `componentGroupMap` along an equality of Hopf ideals agrees with
`componentGroupMap` at the original ideal. -/
theorem componentGroupMap_comp_componentGroupEquivOfEq (I : HopfIdeal k H)
    {J J' : HopfIdeal k K} (hJ : J = J') (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) :
    (componentGroupMap I J' f (hJ ▸ h)).comp (componentGroupEquivOfEq hJ).toMonoidHom =
      componentGroupMap I J f h := by
  subst hJ
  rfl

/-- Induced maps of closed-subgroup component groups commute with the inclusions into the
ambient component groups. -/
theorem componentGroupInclusion_comp_componentGroupMap (I : HopfIdeal k H) (J : HopfIdeal k K)
    (f : H ⟶ K) (h : I.map (toBialgHom f) ≤ J) :
    I.componentGroupInclusion.comp (componentGroupMap I J f h) =
      (mapComponentGroup f).comp J.componentGroupInclusion := by
  rw [componentGroupInclusion, componentGroupInclusion, componentGroupMap,
    ← mapComponentGroup_comp, ← mapComponentGroup_comp, mkQuotient_comp_quotientMap]

/-- **Surjectivity of component group maps.** Let `φ : G' → G` be a homomorphism of affine groups
whose coordinate map is injective, so that `φ` is surjective on rational points, and suppose the
closed subgroup `N'` cut out by `J` is the scheme-theoretic inverse image of the closed subgroup
`N` cut out by `I` (that is, `I.map f = J`). Then `π₀(N') →* π₀(N)` is surjective. -/
theorem componentGroupMap_surjective (I : HopfIdeal k H) (J : HopfIdeal k K) (f : H ⟶ K)
    (hf : Function.Injective (toBialgHom f)) (h : I.map (toBialgHom f) = J) :
    Function.Surjective (componentGroupMap I J f h.le) := by
  intro a
  obtain ⟨n, rfl⟩ := I.rationalComponentMap_surjective a
  obtain ⟨(c : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)), hc⟩ :=
    CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective k f.hom hf
      (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at hc
  have hmap : BialgHom.mapDomain (A := k) (toBialgHom f) c = n := by
    rw [BialgHom.mapDomain_apply]
    exact hc
  -- The lift `c` lies in `N'`, since `N'` is the inverse image of `N`.
  have hcJ : c ∈ CommHopfAlgCat.quotientPointsSubgroup K.obj J (CommAlgCat.of k k) := by
    rw [← h, CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff f.hom,
      CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, hc]
    exact n.property
  refine ⟨J.rationalComponentMap ⟨c, hcJ⟩, ?_⟩
  rw [componentGroupMap_rationalComponentMap]
  exact congrArg _ (Subtype.ext hmap)

end Map

end TauCeti.HopfIdeal
