/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Identity components and component groups of centralizers of Lie algebra elements

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, with
Lie algebra `𝔤`, and let `x ∈ 𝔤`. The component group of the centralizer is the finite group
`A(x) = π₀(C_G(x))`, written `(centralizerHopfIdeal H x).ComponentGroup`. By the general theory
of component groups of closed subgroups (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`)
it is `C_G(x)(k) ⧸ C_G(x)°(k)`, and `TauCeti.HopfIdeal.componentGroupInclusion` maps it to
`π₀(G)`. The identity component `C_G(x)°` is the closed subgroup
`(centralizerHopfIdeal H x).identityComponent` of `G`.

* `C_G(x)°` has the same Lie algebra `ker (ad x)` as `C_G(x)`
  (`TauCeti.lieSubalgebra_identityComponent_centralizerHopfIdeal`), and in characteristic zero
  the same dimension `dim ker (ad x)`
  (`TauCeti.ringKrullDim_quotient_identityComponent_centralizerHopfIdeal`).
* For a rational point `g` of `G`, `C_G(Ad(g) x)° = g C_G(x)° g⁻¹` as closed subgroup schemes
  (`TauCeti.identityComponent_centralizerHopfIdeal_basePointsRepresentation`).

This file also supplies the two comparison maps between the component groups for different
elements and groups.

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
  (`TauCeti.centralizerComponentGroupMap_surjective`, from
  `TauCeti.HopfIdeal.componentGroupMap_surjective`). This applies to every isogeny with injective
  differential (`TauCeti.centralizerComponentGroupMap_surjective_of_injective`), and so in
  characteristic zero to every isogeny
  (`TauCeti.centralizerComponentGroupMap_surjective_of_isIsogeny`), in particular to central
  isogenies of semisimple groups, where the map need not be injective: for the regular nilpotent
  of `𝔰𝔩₂` it is the map from `π₀` of the centralizer `{±1} × Gₐ` in `SL₂` onto the trivial
  component group of the centralizer `Gₐ` in `PGL₂`.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1, for the component groups `A(x)` of centralizers.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37, Section 5 and Chapter 10.
* The identity-component centralizer lemmas are adapted from the closed Tau Ceti pull request
  https://github.com/TauCetiProject/TauCeti/pull/24762.
-/

public section

open CategoryTheory Derivation WithConv

namespace TauCeti

universe u

open FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] Derivation.adjointComodule

section IdentityComponent

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **The Lie algebra of the identity component of a centralizer.** The identity component of
`C_G(x)` has the same Lie algebra as `C_G(x)`, the kernel of `ad x`. -/
theorem lieSubalgebra_identityComponent_centralizerHopfIdeal
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    ((centralizerHopfIdeal H x).identityComponent.lieSubalgebra (B := k)).toSubmodule =
      LinearMap.ker (LieAlgebra.ad k (Derivation k H (Bialgebra.CounitAlgebra k H k))
        (Derivation.cotangentDualLieEquiv (R := k) (H := H) x)) := by
  rw [HopfIdeal.lieSubalgebra_identityComponent, lieSubalgebra_centralizerHopfIdeal]

/-- **The dimension of the identity component of a centralizer.** Over an algebraically closed
field of characteristic zero, `dim C_G(x)° = dim ker (ad x)`. -/
theorem ringKrullDim_quotient_identityComponent_centralizerHopfIdeal [CharZero k]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    ringKrullDim (H ⧸ (centralizerHopfIdeal H x).identityComponent.toIdeal) =
      Module.finrank k
        (LinearMap.ker (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)) := by
  let _ : Algebra.Smooth k (H ⧸ (centralizerHopfIdeal H x).toIdeal) :=
    (smoothCommHopfAlgProperty_iff _).mp <| smoothCommHopfAlgProperty_of_charZero k
      (FiniteTypeCommHopfAlgCat.quotient H (centralizerHopfIdeal H x)).obj
  rw [HopfIdeal.ringKrullDim_quotient_identityComponent_of_smooth,
    ringKrullDim_quotient_centralizerHopfIdeal]

/-- **Conjugation of identity components of centralizers.** For a rational point `g`,
`C_G(Ad(g) x)° = g C_G(x)° g⁻¹`. -/
theorem identityComponent_centralizerHopfIdeal_basePointsRepresentation
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (g : WithConv (H →ₐ[k] k)) :
    (centralizerHopfIdeal H
        (Comodule.basePointsRepresentation (H := H) _ g x)).identityComponent =
      (centralizerHopfIdeal H x).identityComponent.conjugate g := by
  rw [centralizerHopfIdeal_basePointsRepresentation, HopfIdeal.identityComponent_conjugate]

end IdentityComponent

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
@[simp]
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

/-- **Centralizer component groups under homomorphisms.** A homomorphism `φ : G' → G` of affine
groups induces `π₀(C_G'(x)) →* π₀(C_G(dφ x))`. -/
noncomputable def centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal K x).ComponentGroup →*
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).ComponentGroup :=
  HopfIdeal.componentGroupMap _ _ f ((toBialgHom f).map_centralizerHopfIdeal_le x)

/-- On rational points, the induced map of centralizer component groups sends the component of
`c` to the component of `φ(c)`. -/
@[simp]
theorem centralizerComponentGroupMap_rationalComponentMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (c : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupMap f x ((centralizerHopfIdeal K x).rationalComponentMap c) =
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).rationalComponentMap
        ⟨BialgHom.mapDomain (A := k) (toBialgHom f) c,
          CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le f.hom
            ((toBialgHom f).map_centralizerHopfIdeal_le x) _ c.2⟩ :=
  HopfIdeal.componentGroupMap_rationalComponentMap _ _ f _ c

/-- **Surjectivity of centralizer component group maps.** Let `φ : G' → G` be a homomorphism of
affine groups whose coordinate map is injective, so that `φ` is surjective on rational points,
and suppose `C_G'(x)` is the scheme-theoretic inverse image of `C_G(dφ x)`. Then
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` is surjective. -/
theorem centralizerComponentGroupMap_surjective (f : H ⟶ K)
    (hf : Function.Injective (toBialgHom f))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hx : (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).map (toBialgHom f) =
      centralizerHopfIdeal K x) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  HopfIdeal.componentGroupMap_surjective _ _ f hf hx

/-- **Centralizer component groups under isogenies.** If `φ : G' → G` is an isogeny whose
differential is injective, the induced map `π₀(C_G'(x)) →* π₀(C_G(dφ x))` is surjective. It need
not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_injective (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf.injective x
    ((toBialgHom f).map_centralizerHopfIdeal_eq_of_injective hinj x)

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
