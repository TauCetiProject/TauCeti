/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Comap

/-!
# Endomorphisms of the toral Kostant carrier

A homomorphism from the toral Kostant carrier `G` to `GLₙ` is the same thing as a morphism of
commutative Hopf algebras `ψ : O(GLₙ) → O(G)`. Such a homomorphism maps `G` into `G` exactly when
`ψ` is killed by the toral defining ideal, and this file reduces that condition to the
generators: it suffices that the composites of `ψ` with the factored root-subgroup and
weight-torus coordinate maps are killed by the toral defining ideal, which holds as soon as each
root subgroup is carried into some root subgroup and the weight torus into the weight torus.

The reduction is the two-sided argument for the defining ideal `𝔞`. The image Hopf ideal
`J := ψ(𝔞)` of `O(G)` pulls back along the quotient morphism to a Hopf ideal of `O(GLₙ)`
containing `𝔞`; the generator equations make every root-subgroup coordinate map and the
weight-torus coordinate map kill that pullback, so it is contained in `𝔞` because `𝔞` is the
largest Hopf ideal with that property. The pullback is therefore `𝔞` itself, and `J` is zero.
Contravariantly: the preimage of `G` under the homomorphism is a closed subgroup scheme of `G`
containing every root subgroup and the weight torus, hence all of `G`.

From that containment the homomorphism factors through `G`, giving an endomorphism of the carrier
as a group scheme and, over every commutative ring, an endomorphism of its group of matrix
points. Two such endomorphisms whose coordinate morphisms agree on the generators are equal, by
rigidity of the carrier.

Nothing here asserts that such an endomorphism is an isogeny, surjective, or flat.

## Main results

In the namespace `TauCeti.UniversalEnvelopingAlgebra`:

* `kostantToralDefiningIdeal_toIdeal_le_ker` and
  `kostantToralDefiningIdeal_toIdeal_le_ker_of_comp_eq`: the coordinate morphism is killed by the
  toral defining ideal, from kernel containments and from generator equations respectively.
* `kostantToralGroupSchemeRestrict`, `kostantToralGroupSchemeRestrict_comp_ι` and
  `kostantToralGroupSchemeRestrict_eq_of_comp_eq`: the resulting endomorphism of the carrier, its
  compatibility with the closed immersion into `GLₙ`, and its determination by the generators.
* `pointsMulEquiv_mapPointsFunctor_mem_kostantToralPointsSubgroup`,
  `kostantToralPointsEndomorphism` and
  `ofConv_pointsMulEquiv_symm_kostantToralPointsEndomorphism`: the induced endomorphism of the
  matrix points over every commutative ring, and its defining property.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§7.1 and 12.2, for endomorphisms of a Chevalley
  group determined by their effect on the root subgroups and the torus.
* J. E. Humphreys, *Linear Algebraic Groups*, §27.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.2, for the Hopf-ideal dictionary used
  in the reduction.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

-- Match tensor products to the `ℤ`-algebra structure used by scalar extension.
attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {I : Type w} {κ : Type} [Finite κ]
variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
variable (wt : Fin n → κ → ℤ)

/-- A generating coordinate map of the toral carrier kills the pullback of the image Hopf ideal
of a morphism into the toral coordinate algebra, as soon as the generator equation holds. -/
private theorem comp_eq_zero_of_le_ker
    {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (χ : CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ⟶ Y)
    (hχ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker (ψ ≫ χ).hom.toAlgHom.toRingHom)
    {x : GeneralLinear.coordinateHopfAlgebra ℤ n}
    (hx : x ∈ HopfIdeal.comapOfSurjective
      (HopfIdeal.map (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ψ.hom)
      (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt)).hom
      (CommHopfAlgCat.mkQuotient_surjective _ _)) :
    χ.hom ((CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
      (kostantToralDefiningIdeal e h ρ M hM hnil b wt)).hom x) = 0 := by
  have hmem := HopfIdeal.mem_comapOfSurjective.1 hx
  rw [← HopfIdeal.mem_toIdeal, HopfIdeal.map_toIdeal] at hmem
  have hle : Ideal.map (ψ.hom : _ →+* _)
      (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker (χ.hom.toAlgHom.toRingHom) := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have hy' := hχ hy
    rw [RingHom.mem_ker] at hy'
    simpa only [_root_.CommHopfAlgCat.comp_apply, BialgHom.coe_toAlgHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using hy'
  exact RingHom.mem_ker.1 (hle hmem)

/-- **A morphism into the toral coordinate algebra whose composites with the generating
coordinate maps are killed by the toral defining ideal is itself killed by it.** Contravariantly,
a homomorphism from the toral Kostant carrier to `GLₙ` which carries every root subgroup and the
weight torus back into the carrier maps the whole carrier into it. -/
theorem kostantToralDefiningIdeal_toIdeal_le_ker
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (hroot : ∀ i, (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker (ψ ≫ kostantRootSubgroupToralCoordinateMap
        e h ρ M hM hnil b wt i).hom.toAlgHom.toRingHom)
    (htorus : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker (ψ ≫ kostantWeightTorusToralCoordinateMap
        e h ρ M hM hnil b wt).hom.toAlgHom.toRingHom) :
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom := by
  have hbot : HopfIdeal.map (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ψ.hom = ⊥ := by
    refine CommHopfAlgCat.eq_bot_of_comapOfSurjective_le _ ?_
    rw [le_kostantToralDefiningIdeal_iff]
    refine ⟨fun i x hx => ?_, fun x hx => ?_⟩
    · rw [RingHom.mem_ker]
      simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← mkQuotient_comp_kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i,
        _root_.CommHopfAlgCat.comp_apply]
      exact comp_eq_zero_of_le_ker e h ρ M hM hnil b wt ψ _ (hroot i) hx
    · rw [RingHom.mem_ker]
      simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← mkQuotient_comp_kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt,
        _root_.CommHopfAlgCat.comp_apply]
      exact comp_eq_zero_of_le_ker e h ρ M hM hnil b wt ψ _ htorus hx
  intro x hx
  have hker := (HopfIdeal.map_eq_bot_iff _ ψ.hom).1 hbot hx
  rw [RingHom.mem_ker] at hker ⊢
  exact hker

/-- **The generator form of the previous criterion.** A morphism into the toral coordinate
algebra whose composite with the `i`th factored root coordinate map is the `s i`th represented
root-subgroup coordinate map followed by an endomorphism of the additive coordinate algebra, and
whose composite with the factored torus coordinate map is the weight-torus coordinate map
followed by an endomorphism of the torus coordinate algebra, is killed by the toral defining
ideal.

Contravariantly, this is a homomorphism from the toral carrier to `GLₙ` which sends the `i`th
root subgroup into the `s i`th one and the weight torus into itself. -/
theorem kostantToralDefiningIdeal_toIdeal_le_ker_of_comp_eq
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (s : I → I)
    (σ : I → (AdditiveGroup.coordinateHopfAlgebra ℤ ⟶ AdditiveGroup.coordinateHopfAlgebra ℤ))
    (t : (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj ⟶
      (DiagonalizableGroup.coordinateRing ℤ (SplitTorus.characterGroup κ)).obj)
    (hroot : ∀ i, ψ ≫ kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i =
      kostantRootSubgroupCoordinateMap e h ρ M hM (s i) (hnil (s i)) b ≫ σ i)
    (htorus : ψ ≫ kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt =
      GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt ≫ t) :
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom := by
  refine kostantToralDefiningIdeal_toIdeal_le_ker e h ρ M hM hnil b wt ψ
    (fun i x hx => ?_) (fun x hx => ?_)
  · rw [RingHom.mem_ker]
    simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hroot i, _root_.CommHopfAlgCat.comp_apply]
    have hzero := kostantToralDefiningIdeal_toIdeal_le_root_ker e h ρ M hM hnil b wt (s i) hx
    rw [RingHom.mem_ker] at hzero
    simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hzero
    rw [hzero, map_zero]
  · rw [RingHom.mem_ker]
    simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [htorus, _root_.CommHopfAlgCat.comp_apply]
    have hzero := kostantToralDefiningIdeal_toIdeal_le_torus_ker e h ρ M hM hnil b wt hx
    rw [RingHom.mem_ker] at hzero
    simp only [BialgHom.coe_toAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hzero
    rw [hzero, map_zero]

/-! ### The restricted endomorphism of the carrier -/

/-- **The endomorphism of the toral Kostant carrier restricting a homomorphism to `GLₙ`** which
maps the carrier into itself: the spectrum of the factorization of the coordinate morphism `ψ`
through the toral quotient. -/
noncomputable def kostantToralGroupSchemeRestrict
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (hψ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom) :
    kostantToralGroupScheme e h ρ M hM hnil b wt ⟶
      kostantToralGroupScheme e h ρ M hM hnil b wt :=
  (hopfSpec (CommRingCat.of ℤ)).map
    (CommHopfAlgCat.liftQuotient (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ψ hψ).op

/-- The restricted endomorphism is the spectrum of the quotient factorization. -/
theorem kostantToralGroupSchemeRestrict_def
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (hψ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom) :
    kostantToralGroupSchemeRestrict e h ρ M hM hnil b wt ψ hψ =
      (hopfSpec (CommRingCat.of ℤ)).map
        (CommHopfAlgCat.liftQuotient
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ψ hψ).op := by
  rw [kostantToralGroupSchemeRestrict]

/-- Following the restricted endomorphism by the closed immersion into `GLₙ` recovers the
original homomorphism to `GLₙ`. -/
@[simp]
theorem kostantToralGroupSchemeRestrict_comp_ι
    (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (hψ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom) :
    kostantToralGroupSchemeRestrict e h ρ M hM hnil b wt ψ hψ ≫
        kostantToralGroupSchemeι e h ρ M hM hnil b wt =
      (hopfSpec (CommRingCat.of ℤ)).map ψ.op ≫
        eqToHom (GeneralLinear.groupScheme_def ℤ n).symm := by
  rw [kostantToralGroupSchemeRestrict_def, kostantToralGroupSchemeι_def,
    CommHopfAlgCat.quotientSpecι_def, ← Category.assoc, ← Functor.map_comp, ← op_comp,
    CommHopfAlgCat.mkQuotient_comp_liftQuotient]

/-- **Two restricted endomorphisms agreeing on the generators agree.** The coordinate morphisms
are determined by their composites with the factored root-subgroup and weight-torus coordinate
maps, so the endomorphisms they restrict to are equal. -/
theorem kostantToralGroupSchemeRestrict_eq_of_comp_eq
    (ψ ψ' : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
      CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
    (hψ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ.hom.toAlgHom.toRingHom)
    (hψ' : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
      RingHom.ker ψ'.hom.toAlgHom.toRingHom)
    (hroot : ∀ i, ψ ≫ kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i =
      ψ' ≫ kostantRootSubgroupToralCoordinateMap e h ρ M hM hnil b wt i)
    (htorus : ψ ≫ kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt =
      ψ' ≫ kostantWeightTorusToralCoordinateMap e h ρ M hM hnil b wt) :
    kostantToralGroupSchemeRestrict e h ρ M hM hnil b wt ψ hψ =
      kostantToralGroupSchemeRestrict e h ρ M hM hnil b wt ψ' hψ' := by
  have heq : ψ = ψ' :=
    kostantToralCoordinate_hom_ext e h ρ M hM hnil b wt ψ ψ' hroot htorus
  subst heq
  rfl

/-! ### Algebra-valued points -/

section Points

variable
  (ψ : GeneralLinear.coordinateHopfAlgebra ℤ n ⟶
    CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
      (kostantToralDefiningIdeal e h ρ M hM hnil b wt))
  (hψ : (kostantToralDefiningIdeal e h ρ M hM hnil b wt).toIdeal ≤
    RingHom.ker ψ.hom.toAlgHom.toRingHom)

include hψ in
/-- **A point of the toral carrier is carried by `ψ` to a point of the toral carrier.** -/
theorem pointsMulEquiv_mapPointsFunctor_mem_kostantToralPointsSubgroup
    (A : Type v) [CommRing A]
    (p : HopfAlgebra.points (R := ℤ)
      (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) (CommAlgCat.of ℤ A)) :
    GeneralLinear.pointsMulEquiv n
        ((CommHopfAlgCat.mapPointsFunctor ψ).app (CommAlgCat.of ℤ A) p) ∈
      kostantToralPointsSubgroup e h ρ M hM hnil b wt A := by
  rw [kostantToralPointsSubgroup_def]
  exact GeneralLinear.pointsMulEquiv_mapPointsFunctor_mem_hopfIdealPointsSubgroup n
    (kostantToralDefiningIdeal e h ρ M hM hnil b wt) ψ hψ A p

/-- The matrix points of the toral carrier read as points of its coordinate Hopf algebra. -/
private noncomputable def toralPointOfMatrix (A : Type v) [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b wt A →*
      HopfAlgebra.points (R := ℤ)
        (H := CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantToralDefiningIdeal e h ρ M hM hnil b wt)) (CommAlgCat.of ℤ A) :=
  ((MonoidHom.ofInjective
      (CommHopfAlgCat.quotientPointsHom_injective
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) (CommAlgCat.of ℤ A))).symm
    : _ ≃* _).toMonoidHom.comp
    (MonoidHom.codRestrict
      ((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm.toMonoidHom.comp
        (kostantToralPointsSubgroup e h ρ M hM hnil b wt A).subtype)
      (CommHopfAlgCat.quotientPointsSubgroup (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) (CommAlgCat.of ℤ A))
      fun g => (CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).2
        ((mem_kostantToralPointsSubgroup_iff e h ρ M hM hnil b wt A g).1 g.2))

private theorem quotientPointsHom_toralPointOfMatrix (A : Type v) [CommRing A]
    (g : kostantToralPointsSubgroup e h ρ M hM hnil b wt A) :
    CommHopfAlgCat.quotientPointsHom (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) (CommAlgCat.of ℤ A)
        (toralPointOfMatrix e h ρ M hM hnil b wt A g) =
      (GeneralLinear.pointsMulEquiv (R := ℤ) n).symm
        (g : Matrix.GeneralLinearGroup (Fin n) A) :=
  congrArg Subtype.val (MulEquiv.apply_symm_apply
    (MonoidHom.ofInjective
      (CommHopfAlgCat.quotientPointsHom_injective
        (GeneralLinear.coordinateHopfAlgebra ℤ n)
        (kostantToralDefiningIdeal e h ρ M hM hnil b wt) (CommAlgCat.of ℤ A))) _)

include hψ in
/-- **The endomorphism of the matrix points of the toral Kostant carrier** restricting the
homomorphism to `GLₙ` represented by `ψ`. -/
noncomputable def kostantToralPointsEndomorphism (A : Type v) [CommRing A] :
    kostantToralPointsSubgroup e h ρ M hM hnil b wt A →*
      kostantToralPointsSubgroup e h ρ M hM hnil b wt A :=
  (MonoidHom.codRestrict
      ((GeneralLinear.pointsMulEquiv (R := ℤ) n).toMonoidHom.comp
        ((CommHopfAlgCat.mapPointsFunctor ψ).app (CommAlgCat.of ℤ A)).hom)
      (kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
      (pointsMulEquiv_mapPointsFunctor_mem_kostantToralPointsSubgroup
        e h ρ M hM hnil b wt ψ hψ A)).comp
    (toralPointOfMatrix e h ρ M hM hnil b wt A)

/-- **The defining property of the point endomorphism**: the point of the image matrix evaluates
an ambient coordinate at the point of the argument, after transporting that coordinate along `ψ`
and choosing any representative of the result. -/
theorem ofConv_pointsMulEquiv_symm_kostantToralPointsEndomorphism
    (A : Type v) [CommRing A] (g : kostantToralPointsSubgroup e h ρ M hM hnil b wt A)
    (x y : GeneralLinear.coordinateHopfAlgebra ℤ n)
    (hxy : (CommHopfAlgCat.mkQuotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
      (kostantToralDefiningIdeal e h ρ M hM hnil b wt)).hom y = ψ.hom x) :
    ((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm
        (kostantToralPointsEndomorphism e h ρ M hM hnil b wt ψ hψ A g :
          Matrix.GeneralLinearGroup (Fin n) A)).ofConv x =
      ((GeneralLinear.pointsMulEquiv (R := ℤ) n).symm
        (g : Matrix.GeneralLinearGroup (Fin n) A)).ofConv y := by
  have hcoe : (kostantToralPointsEndomorphism e h ρ M hM hnil b wt ψ hψ A g :
      Matrix.GeneralLinearGroup (Fin n) A) =
      GeneralLinear.pointsMulEquiv n
        ((CommHopfAlgCat.mapPointsFunctor ψ).app (CommAlgCat.of ℤ A)
          (toralPointOfMatrix e h ρ M hM hnil b wt A g)) := rfl
  have hpt : (GeneralLinear.pointsMulEquiv (R := ℤ) n).symm
      (kostantToralPointsEndomorphism e h ρ M hM hnil b wt ψ hψ A g :
        Matrix.GeneralLinearGroup (Fin n) A) =
      (CommHopfAlgCat.mapPointsFunctor ψ).app (CommAlgCat.of ℤ A)
        (toralPointOfMatrix e h ρ M hM hnil b wt A g) := by
    rw [hcoe]
    exact (GeneralLinear.pointsMulEquiv n).symm_apply_apply _
  rw [hpt, CommHopfAlgCat.mapPointsFunctor_app_apply_apply, ← hxy,
    CommHopfAlgCat.mkQuotient_apply, ← CommHopfAlgCat.quotientPointsHom_apply_apply,
    quotientPointsHom_toralPointOfMatrix]

end Points

end TauCeti.UniversalEnvelopingAlgebra
