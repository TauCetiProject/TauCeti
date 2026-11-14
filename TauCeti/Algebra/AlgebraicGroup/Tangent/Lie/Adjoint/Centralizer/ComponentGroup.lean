/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.IdentityComponent
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# The identity component and component group of a centralizer

Let `G = Spec H` be a finite-type affine group over an algebraically closed field `k`, with Lie
algebra `𝔤`, and let `x ∈ 𝔤`. The centralizer `C_G(x)` is a closed subgroup scheme, possibly
disconnected. Its identity component `C_G(x)°` is the closed subgroup
`(centralizerHopfIdeal H x).identityComponent` of `G`, and its finite component group
`A(x) = π₀(C_G(x))` is the group of connected components of `Spec (H ⧸ C_G(x))`.

* `C_G(x)°` has the same Lie algebra `ker (ad x)` as `C_G(x)`, and in characteristic zero the
  same dimension `dim ker (ad x)`.
* For a rational point `g` of `G`, `C_G(Ad(g) x)° = g C_G(x)° g⁻¹` as closed subgroup schemes.
  Conjugation by `g` identifies `A(x)` with `A(Ad(g) x)`: this is
  `TauCeti.HopfIdeal.componentGroupConjugationMulEquiv` applied to the equality of Hopf ideals
  `TauCeti.centralizerHopfIdeal_basePointsRepresentation`, and it sends the component of a
  rational point `y` of `C_G(x)` to the component of `gyg⁻¹`.
* A homomorphism `φ : G̃ → G` carries `C_G̃(x)` into `C_G(dφ x)`, and so induces a homomorphism
  `A(x) → A(dφ x)` of component groups (`TauCeti.centralizerComponentGroupMap`). For an isogeny
  with injective differential, for instance any isogeny in characteristic zero, it is surjective.
  It need not be injective: component groups of centralizers are not invariant under isogeny.

In the theory of nilpotent orbits these are the centralizer data attached to a nilpotent element
`x`: the identity component and the component group `A(x)` of its centralizer.

## Main declarations

* `TauCeti.lieSubalgebra_identityComponent_centralizerHopfIdeal`: `Lie(C_G(x)°) = ker (ad x)`.
* `TauCeti.ringKrullDim_quotient_identityComponent_centralizerHopfIdeal`: in characteristic
  zero, `dim C_G(x)° = dim ker (ad x)`.
* `TauCeti.identityComponent_centralizerHopfIdeal_basePointsRepresentation`:
  `C_G(Ad(g) x)° = g C_G(x)° g⁻¹`.
* `TauCeti.centralizerComponentGroupMap`: the induced map `A(x) → A(dφ x)`.
* `TauCeti.centralizerComponentGroupMap_surjective_of_injective` and
  `TauCeti.centralizerComponentGroupMap_surjective_of_charZero`: it is surjective for isogenies
  with injective differential, in particular for all isogenies in characteristic zero.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §§1.3 and 6.1.
* J. S. Milne, *Algebraic Groups* (2017), Section 5 and Chapter 10.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

section IdentityComponent

attribute [local instance] Derivation.adjointComodule

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

section Isogeny

/-- **The map of centralizer component groups induced by a homomorphism.** The coordinate arrow
`f : H ⟶ K` represents `φ : Spec K → Spec H`, which carries `C_{Spec K}(x)` into
`C_{Spec H}(dφ x)`. This is the induced homomorphism `π₀(C_{Spec K}(x)) → π₀(C_{Spec H}(dφ x))`;
its coordinate morphism is `BialgHom.centralizerMap`. -/
noncomputable def centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    ConnectedComponents (PrimeSpectrum
        (FiniteTypeCommHopfAlgCat.quotient K (centralizerHopfIdeal K x))) →*
      ConnectedComponents (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H
        (centralizerHopfIdeal H (Derivation.dualCotangentMap f.hom.hom x)))) :=
  FiniteTypeCommHopfAlgCat.mapComponentGroup
    (FiniteTypeCommHopfAlgCat.ofHom (f.hom.hom.centralizerMap x))

/-- On a represented component, the centralizer component-group map is contraction along the
centralizer coordinate map. -/
@[simp]
theorem centralizerComponentGroupMap_mk (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (p : PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient K (centralizerHopfIdeal K x))) :
    centralizerComponentGroupMap f x (ConnectedComponents.mk p) =
      ConnectedComponents.mk (PrimeSpectrum.comap
        ((f.hom.hom.centralizerMap x).toAlgHom : _ →+* K ⧸ (centralizerHopfIdeal K x).toIdeal)
          p) :=
  FiniteTypeCommHopfAlgCat.mapComponentGroup_mk _ p

/-- The centralizer component-group map sends the component of a rational point `y` of
`C_{Spec K}(x)` to the component of its image `φ(y)` in `C_{Spec H}(dφ x)`. -/
theorem centralizerComponentGroupMap_rationalComponentMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (y : HopfAlgebra.points (R := k)
      (H := FiniteTypeCommHopfAlgCat.quotient K (centralizerHopfIdeal K x)) (CommAlgCat.of k k)) :
    centralizerComponentGroupMap f x (FiniteTypeCommHopfAlgCat.rationalComponentMap _ y) =
      FiniteTypeCommHopfAlgCat.rationalComponentMap _
        (BialgHom.mapDomain (A := k) (f.hom.hom.centralizerMap x) y) :=
  FiniteTypeCommHopfAlgCat.mapComponentGroup_rationalComponentMap _ y

/-- **Centralizer component groups under isogenies.** If `φ : Spec K → Spec H` is an isogeny
whose differential is injective, every component of `C_{Spec H}(dφ x)` is the image of a
component of `C_{Spec K}(x)`. The map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_injective {f : H ⟶ K}
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (Derivation.dualCotangentMap f.hom.hom))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  FiniteTypeCommHopfAlgCat.mapComponentGroup_surjective_of_injective _
    (hf.centralizerMap_of_injective hinj x).injective

/-- **Centralizer component groups under isogenies in characteristic zero.** For an isogeny
`φ : Spec K → Spec H`, such as a central isogeny of semisimple groups, the induced map
`π₀(C_{Spec K}(x)) → π₀(C_{Spec H}(dφ x))` is surjective. -/
theorem centralizerComponentGroupMap_surjective_of_charZero [CharZero k] {f : H ⟶ K}
    (hf : CommHopfAlgCat.IsIsogeny f.hom) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective_of_injective hf
    hf.dualCotangentMap_bijective_of_charZero.injective x

end Isogeny

end TauCeti
