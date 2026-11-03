/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.RingTheory.TensorProduct.Maps
public import TauCeti.RingTheory.WeilRestriction.Basic
import TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Weil restriction of affine group schemes

Let `B` be a commutative `A`-algebra that is finitely generated and projective as an `A`-module,
and `H` a commutative Hopf `B`-algebra of finite presentation, the coordinate ring of an affine
group scheme `G` over `Spec B`. The Weil restriction `W = WeilRestriction A B H` represents the
functor `T ↦ (H →ₐ[B] B ⊗[A] T)` on `A`-algebras, that is, `T ↦ G(B ⊗[A] T)`. Each of these
point sets is a group under convolution, and post-composition is a group homomorphism, so `W` is
itself a commutative Hopf `A`-algebra, the coordinate ring of the Weil restriction `Res_{B/A} G`.
The comultiplication and counit only use the bialgebra structure of `H`, so the Weil restriction
of a commutative bialgebra (an affine monoid scheme) is a bialgebra (`instBialgebra`).

The Hopf structure is the unique one for which the universal bijection
`WeilRestriction.homEquiv : (W →ₐ[A] T) ≃ (H →ₐ[B] B ⊗[A] T)` is a group isomorphism for the
convolution products on both sides (`WeilRestriction.pointsMulEquiv`):

* the comultiplication `W → W ⊗[A] W` classifies the convolution product of the two points of
  `G(B ⊗[A] (W ⊗[A] W))` coming from the two factors;
* the counit `W → A` classifies the identity point of `G(B ⊗[A] A)`;
* the antipode `W → W` classifies the convolution inverse of the universal point.

Every Hopf axiom is an equality of algebra maps out of `W`, which is checked on points by
`WeilRestriction.hom_ext`, where it becomes a group law in `G(B ⊗[A] T)`. The isomorphism
`pointsMulEquiv` is natural in `T` (`WeilRestriction.pointsMulEquiv_naturality`). The same
transport shows that the Weil restriction of a commutative group is commutative.

The Weil restriction is functorial for homomorphisms of affine monoid and group schemes: a
bialgebra map `φ : H₁ →ₐc[B] H₂` induces the bialgebra map `WeilRestriction.mapBialgHom A B φ`,
which on points is precomposition with `φ`. For an affine monoid scheme `G = Spec H` over `Spec A`,
the diagonal `G → Res_{B/A} G_B`, sending a point `x ∈ G(T)` to its base change
`B ⊗[A] x ∈ G_B(B ⊗[A] T)`, is a homomorphism; its coordinate map is the bialgebra map
`WeilRestriction.diagonal A B H : WeilRestriction A B (B ⊗[A] H) →ₐc[A] H`.

## Main declarations

* `TauCeti.Algebra.WeilRestriction.instBialgebra` and
  `TauCeti.Algebra.WeilRestriction.instHopfAlgebra`: the bialgebra and Hopf algebra structures on
  the Weil restriction of a commutative bialgebra or Hopf algebra.
* `TauCeti.Algebra.WeilRestriction.homEquiv_comp_comul`: the comultiplication classifies the
  convolution product of the points defined by the two tensor factors.
* `TauCeti.Algebra.WeilRestriction.homEquiv_counit` and
  `TauCeti.Algebra.WeilRestriction.homEquiv_comp_antipode`: the counit classifies the identity
  point, and the antipode inverts points.
* `TauCeti.Algebra.WeilRestriction.pointsMulEquiv`: the monoid (for Hopf algebras, group)
  isomorphism `(Res_{B/A} G)(T) ≃* G(B ⊗[A] T)`.
* `TauCeti.Algebra.WeilRestriction.instIsCocomm`: the Weil restriction of a cocommutative
  bialgebra is cocommutative.
* `TauCeti.Algebra.WeilRestriction.mapBialgHom` and
  `TauCeti.Algebra.WeilRestriction.pointsMulEquiv_mapDomain_mapBialgHom`: the bialgebra map of
  Weil restrictions induced by a bialgebra map, and its effect on points.
* `TauCeti.Algebra.WeilRestriction.diagonal` and
  `TauCeti.Algebra.WeilRestriction.pointsMulEquiv_mapDomain_diagonal`: the diagonal
  `G → Res_{B/A} G_B`, which on points is base change `x ↦ B ⊗[A] x`.

## References

* F. Bruhat, J. Tits, *Groupes réductifs sur un corps local. II*, Publ. Math. IHÉS 60 (1984),
  §1.5.
* J. S. Milne, *Algebraic Groups* (2017), §2.i.
-/

public section

open Bialgebra WithConv
open scoped TensorProduct

namespace TauCeti.Algebra.WeilRestriction

variable {A B H : Type*} [CommRing A] [CommRing B] [CommRing H] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]

section Bialgebra

variable [Bialgebra B H] [Algebra.FinitePresentation B H]

section Structure

variable (A B H)

/-- The comultiplication of the Weil restriction, classifying the convolution product of the
points of `H` defined by the two tensor factors of `W ⊗[A] W`. -/
noncomputable def comul :
    WeilRestriction A B H →ₐ[A] WeilRestriction A B H ⊗[A] WeilRestriction A B H :=
  (homEquiv A B H _).symm <| ofConv <|
    toConv (homEquiv A B H _ Algebra.TensorProduct.includeLeft) *
      toConv (homEquiv A B H _ Algebra.TensorProduct.includeRight)

/-- The counit of the Weil restriction, classifying the identity point of `H` with values in
`B ⊗[A] A`. -/
noncomputable def counit : WeilRestriction A B H →ₐ[A] A :=
  (homEquiv A B H A).symm (1 : WithConv (H →ₐ[B] B ⊗[A] A)).ofConv

variable {A B H} {T : Type*} [CommRing T] [Algebra A T]

/-- The comultiplication classifies the convolution product of the points defined by the two
tensor factors of `W ⊗[A] W`. -/
theorem homEquiv_comul :
    homEquiv A B H _ (comul A B H) =
      ofConv (toConv (homEquiv A B H _ Algebra.TensorProduct.includeLeft) *
        toConv (homEquiv A B H _ Algebra.TensorProduct.includeRight)) := by
  rw [comul, Equiv.apply_symm_apply]

/-- Post-composing the comultiplication with `f : W ⊗[A] W → T` gives the convolution product of
the points classified by the restrictions of `f` to the two tensor factors. -/
theorem homEquiv_comp_comul (f : WeilRestriction A B H ⊗[A] WeilRestriction A B H →ₐ[A] T) :
    homEquiv A B H T (f.comp (comul A B H)) =
      ofConv (toConv (homEquiv A B H T (f.comp Algebra.TensorProduct.includeLeft)) *
        toConv (homEquiv A B H T (f.comp Algebra.TensorProduct.includeRight))) := by
  rw [homEquiv_comp, comul, Equiv.apply_symm_apply, AlgHom.comp_convMul_distrib,
    ← homEquiv_comp, ← homEquiv_comp]

/-- The counit classifies the identity point. -/
theorem homEquiv_counit :
    homEquiv A B H A (counit A B H) = (1 : WithConv (H →ₐ[B] B ⊗[A] A)).ofConv := by
  rw [counit, Equiv.apply_symm_apply]

/-- Post-composing the counit with the structure map `A → T` classifies the identity point. -/
theorem homEquiv_ofId_comp_counit :
    homEquiv A B H T ((Algebra.ofId A T).comp (counit A B H)) =
      (1 : WithConv (H →ₐ[B] B ⊗[A] T)).ofConv := by
  rw [homEquiv_comp, homEquiv_counit, AlgHom.convOne_def, ofConv_toConv, AlgHom.convOne_def,
    ofConv_toConv, ← AlgHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

/-- Post-composing the comultiplication with `lift f g` gives the convolution product of the
points classified by `f` and `g`. -/
theorem homEquiv_lift_comp_comul (f g : WeilRestriction A B H →ₐ[A] T)
    (hfg : ∀ x y, Commute (f x) (g y)) :
    homEquiv A B H T ((Algebra.TensorProduct.lift f g hfg).comp (comul A B H)) =
      ofConv (toConv (homEquiv A B H T f) * toConv (homEquiv A B H T g)) := by
  rw [homEquiv_comp_comul, Algebra.TensorProduct.lift_comp_includeLeft,
    Algebra.TensorProduct.lift_comp_includeRight']

variable (A B H)

/-- Coassociativity of the comultiplication of the Weil restriction. -/
theorem assoc_comp_map_comul_comp_comul :
    (Algebra.TensorProduct.assoc A A A (WeilRestriction A B H) (WeilRestriction A B H)
        (WeilRestriction A B H)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul A B H) (.id A _)).comp (comul A B H)) =
      (Algebra.TensorProduct.map (.id A _) (comul A B H)).comp (comul A B H) := by
  -- both sides classify the threefold product of the points defined by the tensor factors
  refine (homEquiv A B H _).injective ?_
  -- expand the outer comultiplications, restrict the tensor maps to the factors, then expand the
  -- inner comultiplications
  simp only [← AlgHom.comp_assoc, homEquiv_comp_comul]
  simp only [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
  simp only [← AlgHom.comp_assoc, homEquiv_comp_comul,
    Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeLeft,
    Algebra.TensorProduct.assoc_comp_includeLeft_comp_includeRight,
    Algebra.TensorProduct.assoc_comp_includeRight, toConv_ofConv, mul_assoc]

/-- The counit of the Weil restriction is a left counit for its comultiplication. -/
theorem map_counit_comp_comul :
    (Algebra.TensorProduct.map (counit A B H) (.id A _)).comp (comul A B H) =
      (Algebra.TensorProduct.lid A (WeilRestriction A B H)).symm.toAlgHom := by
  refine (homEquiv A B H _).injective ?_
  have h : (Algebra.TensorProduct.includeLeft : A →ₐ[A] A ⊗[A] WeilRestriction A B H) =
      Algebra.ofId _ _ := Subsingleton.elim _ _
  rw [homEquiv_comp_comul, Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id, h, homEquiv_ofId_comp_counit,
    toConv_ofConv, one_mul, ofConv_toConv]
  exact congrArg _ (AlgHom.ext fun _ ↦ rfl)

/-- The counit of the Weil restriction is a right counit for its comultiplication. -/
theorem map_id_counit_comp_comul :
    (Algebra.TensorProduct.map (.id A _) (counit A B H)).comp (comul A B H) =
      (Algebra.TensorProduct.rid A A (WeilRestriction A B H)).symm.toAlgHom := by
  refine (homEquiv A B H _).injective ?_
  have h : (Algebra.TensorProduct.includeRight : A →ₐ[A] WeilRestriction A B H ⊗[A] A) =
      Algebra.ofId _ _ := Subsingleton.elim _ _
  rw [homEquiv_comp_comul, Algebra.TensorProduct.map_comp_includeLeft,
    Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id, h, homEquiv_ofId_comp_counit,
    toConv_ofConv, mul_one, ofConv_toConv]
  exact congrArg _ (AlgHom.ext fun _ ↦ rfl)

end Structure

/-- The Weil restriction of a commutative bialgebra is a bialgebra, whose comultiplication and
counit classify the convolution product and the identity of points. -/
noncomputable instance instBialgebra : Bialgebra A (WeilRestriction A B H) :=
  .ofAlgHom (comul A B H) (counit A B H) (assoc_comp_map_comul_comp_comul A B H)
    (map_counit_comp_comul A B H) (map_id_counit_comp_comul A B H)

/-- The comultiplication of the Weil restriction as an algebra map is `WeilRestriction.comul`. -/
theorem comulAlgHom_eq : comulAlgHom A (WeilRestriction A B H) = comul A B H := (rfl)

/-- The counit of the Weil restriction as an algebra map is `WeilRestriction.counit`. -/
theorem counitAlgHom_eq : counitAlgHom A (WeilRestriction A B H) = counit A B H := (rfl)

section Points

variable (A B H) (T : Type*) [CommRing T] [Algebra A T]

/-- **Points of the Weil restriction.** For every `A`-algebra `T`, the universal bijection
`WeilRestriction.homEquiv` is a monoid isomorphism `(Res_{B/A} G)(T) ≃* G(B ⊗[A] T)` for the
convolution products; it is a group isomorphism when `H` is a Hopf algebra. -/
noncomputable def pointsMulEquiv :
    WithConv (WeilRestriction A B H →ₐ[A] T) ≃* WithConv (H →ₐ[B] B ⊗[A] T) where
  toFun f := toConv (homEquiv A B H T f.ofConv)
  invFun g := toConv ((homEquiv A B H T).symm g.ofConv)
  left_inv f := by simp only [Equiv.symm_apply_apply, toConv_ofConv]
  right_inv g := by simp only [Equiv.apply_symm_apply, toConv_ofConv]
  map_mul' f g := by
    rw [AlgHom.convMul_def, ofConv_toConv, ← AlgHom.comp_assoc,
      Algebra.TensorProduct.lmul'_comp_map, comulAlgHom_eq, homEquiv_lift_comp_comul,
      toConv_ofConv]

variable {A B H T}

/-- The point of `H` attached to a point of the Weil restriction is the one classified by
`WeilRestriction.homEquiv`. -/
@[simp]
theorem pointsMulEquiv_apply (f : WithConv (WeilRestriction A B H →ₐ[A] T)) :
    (pointsMulEquiv A B H T f).ofConv = homEquiv A B H T f.ofConv := (rfl)

/-- The point of the Weil restriction attached to a point of `H` is the one classified by the
inverse of `WeilRestriction.homEquiv`. -/
@[simp]
theorem pointsMulEquiv_symm_apply (g : WithConv (H →ₐ[B] B ⊗[A] T)) :
    ((pointsMulEquiv A B H T).symm g).ofConv = (homEquiv A B H T).symm g.ofConv := (rfl)

/-- Naturality of `WeilRestriction.pointsMulEquiv` in the `A`-algebra `T`: post-composing with
`h : T →ₐ[A] T'` corresponds to post-composing with `B ⊗[A] h`. -/
theorem pointsMulEquiv_naturality {T' : Type*} [CommRing T'] [Algebra A T'] (h : T →ₐ[A] T')
    (f : WithConv (WeilRestriction A B H →ₐ[A] T)) :
    pointsMulEquiv A B H T' (toConv (h.comp f.ofConv)) =
      toConv ((Algebra.TensorProduct.lTensor (S := B) B h).comp
        (pointsMulEquiv A B H T f).ofConv) :=
  WithConv.ofConv_injective <| by
    rw [pointsMulEquiv_apply, ofConv_toConv, ofConv_toConv, homEquiv_comp, pointsMulEquiv_apply]

end Points

/-- **The Weil restriction of a commutative affine monoid scheme is commutative.** If `H` is
cocommutative, then so is its Weil restriction: the points of `Res_{B/A} G` over `T` are the
points of `G` over `B ⊗[A] T`, which commute. -/
instance instIsCocomm [Coalgebra.IsCocomm B H] : Coalgebra.IsCocomm A (WeilRestriction A B H) := by
  rw [← HopfAlgebra.commute_includeLeft_includeRight_iff_isCocomm]
  let e := pointsMulEquiv A B H (WeilRestriction A B H ⊗[A] WeilRestriction A B H)
  simpa using (Commute.all (e (toConv Algebra.TensorProduct.includeLeft))
    (e (toConv Algebra.TensorProduct.includeRight))).map e.symm

section Map

variable {H₁ H₂ H₃ : Type*} [CommRing H₁] [CommRing H₂] [CommRing H₃]
  [Bialgebra B H₁] [Bialgebra B H₂] [Bialgebra B H₃]
  [Algebra.FinitePresentation B H₁] [Algebra.FinitePresentation B H₂]
  [Algebra.FinitePresentation B H₃]

variable (A B) in
/-- **Functoriality of the Weil restriction of affine group schemes.** A bialgebra map
`φ : H₁ →ₐc[B] H₂`, that is, a homomorphism `Spec H₂ → Spec H₁` of affine monoid (for Hopf
algebras, group) schemes over `Spec B`, induces a bialgebra map of Weil restrictions, with
underlying algebra map `WeilRestriction.map A B φ`. On points it is precomposition with `φ`, see
`WeilRestriction.pointsMulEquiv_mapDomain_mapBialgHom`. -/
noncomputable def mapBialgHom (φ : H₁ →ₐc[B] H₂) :
    WeilRestriction A B H₁ →ₐc[A] WeilRestriction A B H₂ :=
  .ofAlgHom (map A B (φ : H₁ →ₐ[B] H₂))
    ((homEquiv A B H₁ A).injective <| by
      -- both counits classify the identity point, and precomposing the identity point of `H₂`
      -- with the bialgebra map `φ` gives the identity point of `H₁`
      simp only [counitAlgHom_eq, homEquiv_comp_map, homEquiv_counit, AlgHom.convOne_def,
        ofConv_toConv, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp])
    ((homEquiv A B H₁ _).injective <| by
      -- both sides classify convolution products of the points defined by the two tensor
      -- factors: on the left that of `H₂`, precomposed with `φ`; on the right that of `H₁`, of
      -- the factor points precomposed with `φ`
      simp only [comulAlgHom_eq, homEquiv_comp_comul, homEquiv_comp_map,
        Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight]
      -- precomposition with the bialgebra map `φ` distributes over the convolution product
      simp only [homEquiv_comul, AlgHom.convMul_comp_bialgHom_distrib])

/-- The algebra map underlying `WeilRestriction.mapBialgHom φ` is `WeilRestriction.map φ`. -/
@[simp]
theorem mapBialgHom_toAlgHom (φ : H₁ →ₐc[B] H₂) :
    (mapBialgHom A B φ : WeilRestriction A B H₁ →ₐ[A] WeilRestriction A B H₂) =
      map A B (φ : H₁ →ₐ[B] H₂) := (rfl)

/-- `WeilRestriction.mapBialgHom φ` agrees pointwise with `WeilRestriction.map φ`. -/
@[simp]
theorem mapBialgHom_apply (φ : H₁ →ₐc[B] H₂) (x : WeilRestriction A B H₁) :
    mapBialgHom A B φ x = map A B (φ : H₁ →ₐ[B] H₂) x := (rfl)

/-- The identity bialgebra map induces the identity of the Weil restriction. -/
@[simp]
theorem mapBialgHom_id : mapBialgHom A B (BialgHom.id B H₁) = BialgHom.id A _ :=
  BialgHom.coe_toAlgHom_injective <| by
    rw [mapBialgHom_toAlgHom, BialgHom.id_toAlgHom, BialgHom.id_toAlgHom, map_id]

/-- `WeilRestriction.mapBialgHom` respects composition. -/
theorem mapBialgHom_comp (ψ : H₂ →ₐc[B] H₃) (φ : H₁ →ₐc[B] H₂) :
    mapBialgHom A B (ψ.comp φ) = (mapBialgHom A B ψ).comp (mapBialgHom A B φ) :=
  BialgHom.coe_toAlgHom_injective <| by
    rw [mapBialgHom_toAlgHom, BialgHom.comp_toAlgHom, BialgHom.comp_toAlgHom,
      mapBialgHom_toAlgHom, mapBialgHom_toAlgHom, map_comp]

/-- **`WeilRestriction.mapBialgHom` on points.** Under `WeilRestriction.pointsMulEquiv`,
precomposition with `WeilRestriction.mapBialgHom φ` on the points of the Weil restrictions over
`T` is precomposition with `φ` on the points of `H₂` and `H₁` over `B ⊗[A] T`. -/
theorem pointsMulEquiv_mapDomain_mapBialgHom (T : Type*) [CommRing T] [Algebra A T]
    (φ : H₁ →ₐc[B] H₂) (f : WithConv (WeilRestriction A B H₂ →ₐ[A] T)) :
    pointsMulEquiv A B H₁ T (BialgHom.mapDomain (mapBialgHom A B φ) f) =
      BialgHom.mapDomain φ (pointsMulEquiv A B H₂ T f) :=
  WithConv.ofConv_injective <| by
    rw [BialgHom.mapDomain_apply, pointsMulEquiv_apply, ofConv_toConv, mapBialgHom_toAlgHom,
      homEquiv_comp_map, BialgHom.mapDomain_apply, ofConv_toConv, pointsMulEquiv_apply]

end Map

end Bialgebra

section Diagonal

variable [Bialgebra A H] [Algebra.FinitePresentation A H]

/-- The point of the Weil restriction of `B ⊗[A] H` over `T` attached to `x : H →ₐ[A] T` is the
base change `B ⊗[A] x`. -/
private theorem homEquiv_comp_symm_id {T : Type*} [CommRing T] [Algebra A T] (x : H →ₐ[A] T) :
    homEquiv A B (B ⊗[A] H) T
        (x.comp ((homEquiv A B (B ⊗[A] H) H).symm (AlgHom.id B (B ⊗[A] H)))) =
      Algebra.TensorProduct.lTensor B x := by
  rw [homEquiv_comp, Equiv.apply_symm_apply, AlgHom.comp_id]

variable (A B H) in
/-- **The diagonal of the Weil restriction.** For an affine monoid (or group) scheme `G = Spec H`
over `Spec A`, the bialgebra map `Res_{B/A} (B ⊗[A] H) → H` corresponding to the homomorphism
`G → Res_{B/A} G_B` which on points over `T` is `x ↦ B ⊗[A] x`, from `G(T)` to
`G_B(B ⊗[A] T)`; see `WeilRestriction.pointsMulEquiv_mapDomain_diagonal`. Its underlying algebra
map classifies the identity of `B ⊗[A] H`, viewed as a point of `B ⊗[A] H` with values in
`B ⊗[A] H`, so `G → Res_{B/A} G_B` is the unit of the adjunction between base change and Weil
restriction. -/
noncomputable def diagonal : WeilRestriction A B (B ⊗[A] H) →ₐc[A] H :=
  .ofAlgHom ((homEquiv A B (B ⊗[A] H) H).symm (AlgHom.id B (B ⊗[A] H)))
    ((homEquiv A B (B ⊗[A] H) A).injective <| by
      -- the counit of `H` is the identity point, whose base change is the identity point
      rw [homEquiv_comp_symm_id, counitAlgHom_eq, homEquiv_counit,
        ← TauCeti.Bialgebra.ofConv_one_eq_counitAlgHom, ← TauCeti.AlgHom.ofConv_pointsLTensor,
        map_one])
    ((homEquiv A B (B ⊗[A] H) _).injective <| by
      -- the left side classifies the convolution product of the base changes of the two
      -- tensor-factor points of `H`, the right side the base change of its comultiplication point
      simp only [comulAlgHom_eq, homEquiv_comp_comul, Algebra.TensorProduct.map_comp_includeLeft,
        Algebra.TensorProduct.map_comp_includeRight, homEquiv_comp_symm_id]
      -- base change of points `x ↦ B ⊗[A] x` is multiplicative for convolution
      rw [← TauCeti.AlgHom.ofConv_pointsLTensor, ← TauCeti.AlgHom.ofConv_pointsLTensor,
        toConv_ofConv, toConv_ofConv, ← map_mul]
      -- the convolution product of the two tensor-factor points is the comultiplication point
      rw [← TauCeti.Bialgebra.comulPoint_eq_include_mul, TauCeti.AlgHom.ofConv_pointsLTensor,
        ofConv_toConv])

/-- The algebra map underlying `WeilRestriction.diagonal` is the one classifying the identity of
`B ⊗[A] H`. -/
theorem diagonal_toAlgHom :
    (diagonal A B H : WeilRestriction A B (B ⊗[A] H) →ₐ[A] H) =
      (homEquiv A B (B ⊗[A] H) H).symm (AlgHom.id B (B ⊗[A] H)) := (rfl)

/-- `WeilRestriction.diagonal` classifies the identity of `B ⊗[A] H`. -/
theorem homEquiv_diagonal :
    homEquiv A B (B ⊗[A] H) H (diagonal A B H) = AlgHom.id B (B ⊗[A] H) := by
  rw [diagonal_toAlgHom, Equiv.apply_symm_apply]

/-- **The diagonal on points.** Precomposing a point `x : H →ₐ[A] T` with
`WeilRestriction.diagonal` gives the point of `Res_{B/A} (B ⊗[A] H)` over `T` classifying the
base change `B ⊗[A] x : B ⊗[A] H →ₐ[B] B ⊗[A] T`. -/
theorem homEquiv_comp_diagonal {T : Type*} [CommRing T] [Algebra A T] (x : H →ₐ[A] T) :
    homEquiv A B (B ⊗[A] H) T (x.comp (diagonal A B H)) = Algebra.TensorProduct.lTensor B x := by
  rw [diagonal_toAlgHom, homEquiv_comp_symm_id]

/-- **The diagonal as a homomorphism of points.** Under `WeilRestriction.pointsMulEquiv`, the
homomorphism `G(T) → (Res_{B/A} G_B)(T)` induced by `WeilRestriction.diagonal` is base change
`x ↦ B ⊗[A] x`, from `G(T)` to `G_B(B ⊗[A] T)`. -/
theorem pointsMulEquiv_mapDomain_diagonal (T : Type*) [CommRing T] [Algebra A T]
    (x : WithConv (H →ₐ[A] T)) :
    pointsMulEquiv A B (B ⊗[A] H) T (BialgHom.mapDomain (diagonal A B H) x) =
      TauCeti.AlgHom.pointsLTensor B x :=
  WithConv.ofConv_injective <| by
    rw [BialgHom.mapDomain_apply, pointsMulEquiv_apply, ofConv_toConv,
      TauCeti.AlgHom.ofConv_pointsLTensor]
    exact homEquiv_comp_diagonal x.ofConv

end Diagonal

section HopfAlgebra

variable [HopfAlgebra B H] [Algebra.FinitePresentation B H]

section Structure

variable (A B H)

/-- The antipode of the Weil restriction, classifying the convolution inverse of the universal
point. -/
noncomputable def antipode : WeilRestriction A B H →ₐ[A] WeilRestriction A B H :=
  (homEquiv A B H _).symm (toConv (universalPoint A B H))⁻¹.ofConv

variable {A B H} {T : Type*} [CommRing T] [Algebra A T]

/-- Post-composing the antipode with `f : W → T` inverts the point classified by `f`. -/
theorem homEquiv_comp_antipode (f : WeilRestriction A B H →ₐ[A] T) :
    homEquiv A B H T (f.comp (antipode A B H)) = (toConv (homEquiv A B H T f))⁻¹.ofConv := by
  rw [homEquiv_comp, antipode, Equiv.apply_symm_apply, WithConv.algHom_inv_def,
    WithConv.algHom_inv_def, ofConv_toConv, ofConv_toConv]
  ext
  simp

/-- The antipode classifies the inverse of the universal point. -/
theorem homEquiv_antipode :
    homEquiv A B H _ (antipode A B H) =
      (toConv (homEquiv A B H _ (AlgHom.id A (WeilRestriction A B H))))⁻¹.ofConv := by
  simpa using homEquiv_comp_antipode (AlgHom.id A (WeilRestriction A B H))

end Structure

/-- The antipode of the Weil restriction is a left convolution inverse of the identity. -/
theorem lift_antipode_comp_comul :
    (Algebra.TensorProduct.lift (antipode A B H) (.id A _) fun _ _ ↦ .all _ _).comp
      (comul A B H) = (Algebra.ofId A _).comp (counit A B H) := by
  refine (homEquiv A B H _).injective ?_
  rw [homEquiv_lift_comp_comul, homEquiv_ofId_comp_counit, homEquiv_antipode, toConv_ofConv,
    inv_mul_cancel]

/-- The antipode of the Weil restriction is a right convolution inverse of the identity. -/
theorem lift_id_antipode_comp_comul :
    (Algebra.TensorProduct.lift (.id A _) (antipode A B H) fun _ _ ↦ .all _ _).comp
      (comul A B H) = (Algebra.ofId A _).comp (counit A B H) := by
  refine (homEquiv A B H _).injective ?_
  rw [homEquiv_lift_comp_comul, homEquiv_ofId_comp_counit, homEquiv_antipode, toConv_ofConv,
    mul_inv_cancel]

/-- **The Weil restriction of an affine group scheme is an affine group scheme.** The Weil
restriction of a commutative Hopf algebra of finite presentation along a finite projective algebra
is a Hopf algebra; see `WeilRestriction.pointsMulEquiv` for its group of points. -/
noncomputable instance instHopfAlgebra : HopfAlgebra A (WeilRestriction A B H) :=
  .ofAlgHom (antipode A B H) lift_antipode_comp_comul lift_id_antipode_comp_comul

/-- The antipode of the Weil restriction as an algebra map is `WeilRestriction.antipode`. -/
theorem antipodeAlgHom_eq :
    HopfAlgebra.antipodeAlgHom A (WeilRestriction A B H) = antipode A B H := (rfl)

end HopfAlgebra

end TauCeti.Algebra.WeilRestriction
