/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation

/-!
# Component groups of centralizers of Lie algebra elements

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, with
Lie algebra `𝔤`, and let `x ∈ 𝔤`. The component group of the centralizer is the finite group
`A(x) = π₀(C_G(x))`, written `(centralizerHopfIdeal H x).ComponentGroup`. By the general theory
of component groups of closed subgroups (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`)
it is `C_G(x)(k) ⧸ C_G(x)°(k)`, and `TauCeti.HopfIdeal.toComponentGroup` maps it to `π₀(G)`.

This file supplies the two comparison maps between these groups for different elements and
groups.

* Conjugation: a rational point `g` gives an isomorphism `A(x) ≃* A(Ad(g) x)`, sending the
  component of `c` to the component of `gcg⁻¹`
  (`TauCeti.centralizerComponentGroupConjugationEquiv`). It rests on
  `C_G(Ad(g) x) = g C_G(x) g⁻¹`; here `Ad` is `Comodule.basePointsRepresentation`.
* Homomorphisms: a homomorphism `φ : G' → G` of affine groups, given by its coordinate arrow
  `f : H ⟶ K` with `G' = Spec K`, maps `C_G'(x)` into `C_G(dφ x)` and so induces
  `A_G'(x) →* A_G(dφ x)` (`TauCeti.centralizerComponentGroupMap`), sending the component of `c`
  to the component of `φ(c)`. This map is not asserted to be injective. If the coordinate map of
  `φ` is injective, so that `φ` is surjective on rational points, and `C_G'(x)` is the full
  inverse image of `C_G(dφ x)`, it is surjective
  (`TauCeti.centralizerComponentGroupMap_surjective`). In characteristic zero this applies to
  every isogeny (`TauCeti.centralizerComponentGroupMap_surjective_of_isIsogeny`), in particular
  to central isogenies of semisimple groups, where the map need not be injective: for the
  regular nilpotent of `𝔰𝔩₂` it is the map from `π₀` of the centralizer `{±1} × Gₐ` in `SL₂` onto
  the trivial component group of the centralizer `Gₐ` in `PGL₂`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1, for the component groups `A(x)` of centralizers.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Chapter 10.
-/

public section

open CategoryTheory Derivation WithConv

namespace TauCeti

universe u

open FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] Derivation.adjointComodule

section Conjugation

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Conjugation of centralizer component groups.** Conjugation by a rational point `g` of `G`
identifies the component group of `C_G(x)` with that of `C_G(Ad(g) x) = g C_G(x) g⁻¹`. -/
noncomputable def centralizerComponentGroupConjugationEquiv
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (centralizerHopfIdeal H x).ComponentGroup ≃*
      (centralizerHopfIdeal H (Comodule.basePointsRepresentation (H := H) _ g x)).ComponentGroup :=
  HopfIdeal.componentGroupConjugationEquiv _ _ g
    (centralizerHopfIdeal_basePointsRepresentation x g)

/-- On rational points, conjugation of centralizer component groups sends the component of `c`
to the component of `gcg⁻¹`. -/
theorem centralizerComponentGroupConjugationEquiv_rationalComponentMap
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (c : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupConjugationEquiv x g
        ((centralizerHopfIdeal H x).rationalComponentMap c) =
      HopfIdeal.rationalComponentMap
        (centralizerHopfIdeal H (Comodule.basePointsRepresentation (H := H) _ g x))
        ⟨g * c * g⁻¹, centralizerHopfIdeal_basePointsRepresentation x g ▸
          (CommHopfAlgCat.mul_mul_inv_mem_conjugate_iff _ g c).mpr c.2⟩ :=
  HopfIdeal.componentGroupConjugationEquiv_rationalComponentMap _ _ g _ c

end Conjugation

section Map

variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

omit [IsAlgClosed k] in
/-- A homomorphism of affine groups carries the rational points of `C_G'(x)` into those of
`C_G(dφ x)`. The coordinate arrow `f : H ⟶ K` represents `φ : Spec K → Spec H`. -/
theorem mapDomain_mem_quotientPointsSubgroup_centralizerHopfIdeal (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    {c : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k)}
    (hc : c ∈ CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)) :
    BialgHom.mapDomain (A := k) (toBialgHom f) c ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) (CommAlgCat.of k k) := by
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff] at hc ⊢
  intro a ha
  rw [BialgHom.mapDomain_apply_apply]
  exact hc _ ((toBialgHom f).map_centralizerHopfIdeal_le x (HopfIdeal.mem_map_of_mem _ ha))

/-- The coordinate morphism of the restriction `C_G'(x) → C_G(dφ x)` of a homomorphism of affine
groups, in the category of finite-type commutative Hopf algebras. -/
private noncomputable def centralizerMapHom (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
      quotient K (centralizerHopfIdeal K x) :=
  ObjectProperty.homMk (_root_.CommHopfAlgCat.ofHom ((toBialgHom f).centralizerMap x))

omit [IsAlgClosed k] in
private theorem centralizerMapHom_apply (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (y : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x))) :
    toBialgHom (centralizerMapHom f x) y = (toBialgHom f).centralizerMap x y :=
  (rfl)

/-- **Centralizer component groups under homomorphisms.** A homomorphism `φ : G' → G` of affine
groups induces `π₀(C_G'(x)) →* π₀(C_G(dφ x))`. -/
noncomputable def centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal K x).ComponentGroup →*
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).ComponentGroup :=
  mapComponentGroup (centralizerMapHom f x)

/-- On rational points, the induced map of centralizer component groups sends the component of
`c` to the component of `φ(c)`. -/
theorem centralizerComponentGroupMap_rationalComponentMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (c : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupMap f x ((centralizerHopfIdeal K x).rationalComponentMap c) =
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).rationalComponentMap
        ⟨BialgHom.mapDomain (A := k) (toBialgHom f) c,
          mapDomain_mem_quotientPointsSubgroup_centralizerHopfIdeal f x c.2⟩ := by
  rw [centralizerComponentGroupMap, HopfIdeal.rationalComponentMap_apply,
    mapComponentGroup_rationalComponentMap, HopfIdeal.rationalComponentMap_apply]
  congr 1
  refine ((CommHopfAlgCat.liftQuotientPoint_eq_iff H.obj _ (CommAlgCat.of k k) _ _ _).mpr ?_).symm
  apply WithConv.ofConv_injective
  ext a
  rw [CommHopfAlgCat.quotientPointsHom_apply_apply, BialgHom.mapDomain_apply_apply,
    BialgHom.mapDomain_apply_apply, Ideal.Quotient.mkₐ_eq_mk, centralizerMapHom_apply,
    BialgHom.centralizerMap_mk, CommHopfAlgCat.liftQuotientPoint_mk]

/-- **Surjectivity of centralizer component group maps.** Let `φ : G' → G` be a homomorphism of
affine groups whose coordinate map is injective, so that `φ` is surjective on rational points,
and suppose `C_G'(x)` is the scheme-theoretic inverse image of `C_G(dφ x)`. Then
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` is surjective. -/
theorem centralizerComponentGroupMap_surjective (f : H ⟶ K)
    (hf : Function.Injective (toBialgHom f))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hx : (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).map (toBialgHom f) =
      centralizerHopfIdeal K x) :
    Function.Surjective (centralizerComponentGroupMap f x) := by
  intro a
  obtain ⟨n, rfl⟩ := HopfIdeal.rationalComponentMap_surjective _ a
  obtain ⟨c, hc⟩ := CommHopfAlgCat.mapPointsFunctor_app_surjective_of_injective k f.hom hf
    (n : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
  -- The point functor's object is the rational point group; its map is `mapDomain`.
  let c' : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k) := c
  have hc' : BialgHom.mapDomain (A := k) (toBialgHom f) c' = n := hc
  -- The lift `c'` centralizes `x`, since `C_G'(x)` is the inverse image of `C_G(dφ x)`.
  have hcx : c' ∈ CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k) := by
    rw [← hx, CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff f.hom]
    exact hc ▸ n.2
  refine ⟨(centralizerHopfIdeal K x).rationalComponentMap ⟨c', hcx⟩, ?_⟩
  rw [centralizerComponentGroupMap_rationalComponentMap]
  exact congrArg _ (Subtype.ext hc')

/-- In characteristic zero, an isogeny `φ : G' → G` induces a surjection
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` of centralizer component groups. This includes central isogenies
of semisimple groups, for which the map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_isIsogeny [CharZero k] (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf.injective x
    (hf.map_centralizerHopfIdeal_of_charZero x)

end Map

end TauCeti
