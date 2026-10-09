/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Semisimple
import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.TrivialIdentity
import TauCeti.Algebra.AlgebraicGroup.Connected.Finite
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.RationalPoint
import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import TauCeti.Algebra.AlgebraicGroup.Smooth.IdentityComponent
import TauCeti.Algebra.AlgebraicGroup.Solvable.Extension
import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Reduction
import TauCeti.RingTheory.Smooth.GeometricallyReduced
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Semisimplicity of central quotients

Let `f : G → Q` be a central isogeny of affine groups over a field. If `G` is semisimple, then so
is `Q`. Applied to the projection of a semisimple group onto its adjoint quotient, or to
`SLₙ → PGLₙ`, this shows that the target is semisimple.

The coordinate morphism `O(Q) → O(G)` is injective, so smoothness and geometric connectedness
pass from `G` to `Q`. The substance is the triviality of the solvable radical of `Q` over an
algebraic closure. Over an algebraically closed field, this holds for a faithfully flat
homomorphism with central kernel from a reduced finite-type group with trivial solvable radical;
the homomorphism need not be finite. Let `S ⊆ Q` be connected, normal, smooth and solvable,
with preimage `P ⊆ G`. The identity component `(P_red)°` of its reduction is a connected smooth
subgroup of `G`. It is normal because
conjugation by a rational point is an automorphism of `P_red`, and normality of reduced subgroups
can be tested on rational points. It is solvable because it is an extension of a subgroup of `S`
by a subgroup of the central kernel. Semisimplicity of `G` makes it trivial, so `P_red` is
finite. Faithful flatness embeds `O(S)` into `O(P_red)`, so `S` is a finite connected reduced
group, hence trivial.

## Main declarations

* `TauCeti.FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_of_isCentral`:
  over an algebraically closed field, triviality of the solvable radical passes from a reduced
  finite-type group to the target of a faithfully flat homomorphism with central kernel.
* `TauCeti.semisimpleCommHopfAlgProperty.of_isCentralIsogeny`: the target of a central isogeny
  from a semisimple group is semisimple.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§6.45–6.46 and 21.10, for radicals and semisimple
  groups.
* J. E. Humphreys, *Linear Algebraic Groups*, §19, for radicals under surjective homomorphisms.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (G : FiniteTypeCommHopfAlgCat.{u, u} k) (P : HopfIdeal k G)

/-- The coordinate algebra of the reduction `P_red` of the closed subgroup cut out by `P`. -/
private abbrev reducedQuotient : FiniteTypeCommHopfAlgCat.{u, u} k :=
  FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.quotient G P)
    (reduction k (FiniteTypeCommHopfAlgCat.quotient G P))

/-- The coordinate map from `G` onto `P_red`. -/
private abbrev toReducedQuotient : G.obj ⟶ (reducedQuotient G P).obj :=
  CommHopfAlgCat.mkQuotient G.obj P ≫
    CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient G.obj P)
      (reduction k (FiniteTypeCommHopfAlgCat.quotient G P))

/-- The coordinate map onto `P_red` is surjective. -/
private theorem toReducedQuotient_surjective :
    Function.Surjective (toReducedQuotient G P).hom :=
  (CommHopfAlgCat.mkQuotient_surjective _ _).comp (CommHopfAlgCat.mkQuotient_surjective _ _)

/-- An element of `G` vanishes on `P_red` exactly when its class modulo `P` is nilpotent. -/
private theorem toReducedQuotient_eq_zero_iff (y : G) :
    (toReducedQuotient G P).hom y = 0 ↔
      IsNilpotent ((CommHopfAlgCat.mkQuotient G.obj P).hom y) := by
  rw [CommHopfAlgCat.comp_apply, CommHopfAlgCat.mkQuotient_eq_zero_iff, mem_reduction]

/-- The Hopf ideal of the identity component of `P_red`, as a closed subgroup of `G`. -/
private abbrev reducedIdentityComponent : HopfIdeal k G :=
  (HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedQuotient G P)).comapOfSurjective
    (toReducedQuotient G P).hom (toReducedQuotient_surjective G P)

/-- The coordinate algebra of `(P_red)°`, computed in `G` and in `P_red`. -/
private abbrev reducedIdentityComponentIso :
    CommHopfAlgCat.quotient G.obj (reducedIdentityComponent G P) ≅
      (FiniteTypeCommHopfAlgCat.identityComponent (reducedQuotient G P)).obj :=
  CommHopfAlgCat.quotientIsoOfSurjective _ (toReducedQuotient_surjective G P) _

/-- Over an algebraically closed field, the reduced group `P_red` is smooth. -/
private instance : Algebra.Smooth k (reducedQuotient G P) :=
  (smoothCommHopfAlgProperty_iff _).mp
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k (reducedQuotient G P).obj)

private instance : Algebra.Smooth k
    (FiniteTypeCommHopfAlgCat.identityComponent (reducedQuotient G P)).obj :=
  FiniteTypeCommHopfAlgCat.smooth_identityComponent (reducedQuotient G P)

/-- The subgroup `(P_red)°` lies in the subgroup cut out by `P`: as Hopf ideals,
`P ≤ (P_red)°`. -/
private theorem le_reducedIdentityComponent : P ≤ reducedIdentityComponent G P := by
  intro x hx
  rw [mem_comapOfSurjective]
  have h0 : (toReducedQuotient G P).hom x = 0 := by
    rw [CommHopfAlgCat.comp_apply, (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ x).mpr hx,
      map_zero]
  rw [h0]
  exact zero_mem _

/-- The subgroup `(P_red)°` is geometrically connected. -/
private theorem geometricallyConnected_reducedIdentityComponent :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient G.obj (reducedIdentityComponent G P)) :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (reducedIdentityComponentIso G P).symm
    (FiniteTypeCommHopfAlgCat.geometricallyConnected_identityComponent _)

/-- The subgroup `(P_red)°` is smooth. -/
private theorem smooth_reducedIdentityComponent :
    Algebra.Smooth k (CommHopfAlgCat.quotient G.obj (reducedIdentityComponent G P)) :=
  (smoothCommHopfAlgProperty_iff _).mp <|
    (smoothCommHopfAlgProperty k).prop_of_iso (reducedIdentityComponentIso G P).symm
      ((smoothCommHopfAlgProperty_iff _).mpr inferInstance)

private instance :
    IsReduced (CommHopfAlgCat.quotient G.obj (reducedIdentityComponent G P)) :=
  let _ := smooth_reducedIdentityComponent G P
  isReduced_of_smooth k _

/-- If `P` is normal in a reduced group, then so is `(P_red)°`: conjugation by a rational point
induces an automorphism of `P_red`, which preserves its identity component. -/
private theorem isNormal_reducedIdentityComponent [IsReduced G] (hP : P.IsNormal) :
    (reducedIdentityComponent G P).IsNormal := by
  apply isNormal_of_forall_le_conjugate
  intro g x hx
  let C := HopfAlgebra.identityComponentHopfIdeal (k := k) (H := reducedQuotient G P)
  let D := (FiniteTypeCommHopfAlgCat.identityComponent (reducedQuotient G P)).obj
  let _ : IsReduced D := isReduced_of_smooth k D
  let _ : ConnectedSpace (PrimeSpectrum D) :=
    FiniteTypeCommHopfAlgCat.connectedSpace_identityComponent (reducedQuotient G P)
  -- Conjugation by `g`, followed by the projection onto `(P_red)°`.
  let ψ : G.obj ⟶ D :=
    _root_.CommHopfAlgCat.ofHom (HopfAlgebra.pointConjugationBialgEquiv g).toBialgHom ≫
      toReducedQuotient G P ≫ CommHopfAlgCat.mkQuotient (reducedQuotient G P).obj C
  have hψ (y : G) : ψ.hom y = (CommHopfAlgCat.mkQuotient (reducedQuotient G P).obj C).hom
      ((toReducedQuotient G P).hom (HopfAlgebra.pointConjugationAlgHom g y)) := by
    have hc : HopfAlgebra.pointConjugationBialgEquiv g y = HopfAlgebra.pointConjugationAlgHom g y :=
      DFunLike.congr_fun (HopfAlgebra.pointConjugationBialgEquiv_toAlgHom g) y
    simp only [ψ, CommHopfAlgCat.comp_apply, CommHopfAlgCat.hom_ofHom, BialgEquiv.toBialgHom_eq_coe,
      BialgHom.coe_coe, hc]
  -- Since `P` is normal, `ψ` kills `P`; since `D` is reduced, it then factors through `P_red`.
  have hψP : P.toIdeal ≤ RingHom.ker ψ.hom.toAlgHom.toRingHom := by
    intro y hy
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]
    have hy' : HopfAlgebra.pointConjugationAlgHom g y ∈ P :=
      mem_conjugate.mp (hP.le_conjugate g (mem_toIdeal.mp hy))
    have h0 := (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr hy'
    rw [hψ, CommHopfAlgCat.comp_apply, h0, map_zero, map_zero]
  let ψ₁ := CommHopfAlgCat.liftQuotient P ψ hψP
  have hψ₁ : (reduction k (FiniteTypeCommHopfAlgCat.quotient G P)).toIdeal ≤
      RingHom.ker ψ₁.hom.toAlgHom.toRingHom := by
    intro y hy
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom]
    exact ((mem_reduction k _).mp (mem_toIdeal.mp hy)).map ψ₁.hom |>.eq_zero
  let ψ₂ := CommHopfAlgCat.liftQuotient _ ψ₁ hψ₁
  have hcomp : toReducedQuotient G P ≫ ψ₂ = ψ := by
    rw [Category.assoc, CommHopfAlgCat.mkQuotient_comp_liftQuotient,
      CommHopfAlgCat.mkQuotient_comp_liftQuotient]
  -- The identity component of `P_red` maps trivially to the connected group `D`.
  have hC := CommHopfAlgCat.identityComponentHopfIdeal_toIdeal_le_ker_of_connected ψ₂
    (mem_toIdeal.mpr (mem_comapOfSurjective.mp hx))
  rw [RingHom.mem_ker] at hC
  have hx' : ψ.hom x = 0 := by
    rw [← hcomp]
    exact hC
  rw [hψ, CommHopfAlgCat.mkQuotient_eq_zero_iff] at hx'
  exact mem_conjugate.mpr (mem_comapOfSurjective.mpr hx')

/-- If `(P_red)°` is trivial, then `P_red` is finite. -/
private theorem moduleFinite_reducedQuotient
    (h : reducedIdentityComponent G P = augmentation k G) :
    Module.Finite k (reducedQuotient G P) := by
  apply FiniteTypeCommHopfAlgCat.moduleFinite_of_identityComponentHopfIdeal_eq_augmentation
  rw [← comapOfSurjective_eq_comapOfSurjective_iff _ (toReducedQuotient_surjective G P),
    comapOfSurjective_augmentation]
  exact h

end HopfIdeal

namespace CommHopfAlgCat

variable {k : Type u} [Field k]

/-- Let `f` represent a homomorphism `G → Q` with central kernel, and let `S ⊆ Q` be cut out by
`J`. Every closed subgroup of `G` lying inside the preimage of `S` has solvable geometric points
when `S` does: it is an extension of a subgroup of `S` by a central, hence commutative, group. -/
private theorem geometricallySolvablePoints_quotient_of_map_le {Q G : _root_.CommHopfAlgCat.{u} k}
    (f : Q ⟶ G) (hcentral : (kernelHopfIdeal f).IsCentral) {J : HopfIdeal k Q}
    {I : HopfIdeal k G} (hJI : J.map f.hom ≤ I)
    (hJ : geometricallySolvablePointsCommHopfAlgProperty k (quotient Q J)) :
    geometricallySolvablePointsCommHopfAlgProperty k (quotient G I) := by
  have hJ' : J.toIdeal ≤ RingHom.ker (f ≫ mkQuotient G I).hom.toAlgHom.toRingHom := by
    intro y hy
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom,
      _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
    exact (mkQuotient_eq_zero_iff _ _ _).mpr
      (hJI (HopfIdeal.mem_map_of_mem f.hom (HopfIdeal.mem_toIdeal.mp hy)))
  -- The restriction of `f` to the subgroup cut out by `I`, with values in `S`.
  let h : quotient Q J ⟶ quotient G I := liftQuotient J (f ≫ mkQuotient G I) hJ'
  apply geometricallySolvablePointsCommHopfAlgProperty_of_kernel k h hJ
  -- Its kernel is a closed subgroup of the central kernel of `f`.
  have hker : (kernelHopfIdeal f).toIdeal ≤
      RingHom.ker (mkQuotient G I ≫ mkQuotient _ (kernelHopfIdeal h)).hom.toAlgHom.toRingHom := by
    rw [kernelHopfIdeal_toIdeal, Ideal.map_le_iff_le_comap]
    intro y hy
    have hy' : (mkQuotient Q J).hom y ∈ HopfIdeal.augmentation k (quotient Q J) := by
      rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply]
      exact (HopfIdeal.mem_augmentation k Q).mp (HopfIdeal.mem_toIdeal.mp hy)
    have hcomp : (mkQuotient G I).hom (f.hom y) = h.hom ((mkQuotient Q J).hom y) :=
      (liftQuotient_mkQuotient_apply J _ hJ' y).symm
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      BialgHom.coe_toAlgHom, _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply]
    rw [hcomp, mkQuotient_eq_zero_iff, kernelHopfIdeal_def]
    exact HopfIdeal.mem_map_of_mem h.hom hy'
  let s := liftQuotient (kernelHopfIdeal f) (mkQuotient G I ≫ mkQuotient _ (kernelHopfIdeal h)) hker
  have hs : Function.Surjective s.hom :=
    liftQuotient_surjective_of_surjective _ _ hker
      ((mkQuotient_surjective _ _).comp (mkQuotient_surjective _ _))
  let _ := hcentral.isCocomm_quotient
  exact geometricallySolvablePointsCommHopfAlgProperty_of_surjective k s hs
    (geometricallySolvablePointsCommHopfAlgProperty_of_isCocomm k _)

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Let `f` represent a faithfully flat homomorphism `G → Q`, and let `S ⊆ Q` be a connected
smooth subgroup cut out by `J`. If the reduced preimage `P_red` of `S` is finite, then `S` is
trivial: faithful flatness embeds the coordinate ring of `S` into that of `P_red`. -/
private theorem eq_augmentation_of_moduleFinite_reducedQuotient
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k} (f : Q.obj ⟶ G.obj)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) {J : HopfIdeal k Q}
    (hJ : HopfIdeal.IsSolvableRadicalCandidate Q J)
    [Module.Finite k (HopfIdeal.reducedQuotient G (J.map f.hom))] :
    J = HopfIdeal.augmentation k Q := by
  let P : HopfIdeal k G := J.map f.hom
  let _ : Algebra.Smooth k (quotient Q J) := hJ.smooth
  let _ : IsReduced (quotient Q J) := isReduced_of_smooth k _
  -- The coordinate algebra of `S` embeds into that of the finite group `P_red`.
  have hJP : J.toIdeal ≤
      RingHom.ker (f ≫ HopfIdeal.toReducedQuotient G P).hom.toAlgHom.toRingHom := by
    intro y hy
    have hy' : f.hom y ∈ P := HopfIdeal.mem_map_of_mem f.hom (HopfIdeal.mem_toIdeal.mp hy)
    simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, BialgHom.coe_toAlgHom,
      _root_.CommHopfAlgCat.hom_comp, BialgHom.comp_apply,
      (CommHopfAlgCat.mkQuotient_eq_zero_iff _ _ _).mpr hy', map_zero]
  let j := CommHopfAlgCat.liftQuotient J (f ≫ HopfIdeal.toReducedQuotient G P) hJP
  have hj : Function.Injective j.hom := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨y, rfl⟩ := CommHopfAlgCat.mkQuotient_surjective Q.obj J z
    rw [CommHopfAlgCat.liftQuotient_mkQuotient_apply, CommHopfAlgCat.comp_apply,
      HopfIdeal.toReducedQuotient_eq_zero_iff] at hz
    obtain ⟨n, hn⟩ := hz
    rw [← map_pow, ← map_pow, CommHopfAlgCat.mkQuotient_eq_zero_iff] at hn
    -- Faithful flatness: `J` is the contraction of its extension `P`.
    let _ : Algebra Q G := f.hom.toAlgHom.toRingHom.toAlgebra
    let _ : Module.FaithfullyFlat Q G := hf
    have hyn : y ^ n ∈ J := by
      rw [← HopfIdeal.mem_toIdeal,
        ← Ideal.comap_map_eq_self_of_faithfullyFlat (A := Q) (B := G) J.toIdeal, Ideal.mem_comap]
      rw [← HopfIdeal.mem_toIdeal, HopfIdeal.map_toIdeal] at hn
      exact hn
    apply IsNilpotent.eq_zero
    exact ⟨n, by rw [← map_pow, CommHopfAlgCat.mkQuotient_eq_zero_iff]; exact hyn⟩
  let _ : Module.Finite k (quotient Q J) := Module.Finite.of_injective j.hom.toLinearMap hj
  let _ : ConnectedSpace (PrimeSpectrum (quotient Q J)) :=
    geometricallyConnectedCommHopfAlgProperty.connectedSpace k _ hJ.geometricallyConnected
  -- A finite connected reduced group is trivial.
  have hbot := HopfIdeal.augmentation_eq_bot_of_moduleFinite (k := k) (H := quotient Q J)
  apply le_antisymm (HopfIdeal.le_augmentation k Q J)
  intro y hy
  have hy' : (CommHopfAlgCat.mkQuotient Q.obj J).hom y ∈
      HopfIdeal.augmentation k (quotient Q J) := by
    rw [HopfIdeal.mem_augmentation, CoalgHomClass.counit_comp_apply]
    exact (HopfIdeal.mem_augmentation k Q).mp hy
  rw [hbot, HopfIdeal.mem_bot, CommHopfAlgCat.mkQuotient_eq_zero_iff] at hy'
  exact hy'

/-- **Trivial solvable radicals pass to central quotients.** Over an algebraically closed field,
let `f` represent a faithfully flat homomorphism `G → Q` with central kernel, from a reduced
finite-type affine group `G` with trivial solvable radical. Then the solvable radical of `Q` is
trivial as well. The homomorphism need not be finite. -/
theorem solvableRadicalDefiningIdeal_eq_augmentation_of_isCentral
    {Q G : FiniteTypeCommHopfAlgCat.{u, u} k} [IsReduced G] (f : Q.obj ⟶ G.obj)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat)
    (hcentral : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral)
    (hG : solvableRadicalDefiningIdeal G = HopfIdeal.augmentation k G) :
    solvableRadicalDefiningIdeal Q = HopfIdeal.augmentation k Q := by
  rw [solvableRadicalDefiningIdeal_eq_augmentation_iff] at hG ⊢
  intro J hJ
  let P : HopfIdeal k G := J.map f.hom
  -- The identity component of the reduced preimage `P_red` of `S` is a candidate, so trivial.
  have hI := hG (HopfIdeal.reducedIdentityComponent G P) <|
    .mk (HopfIdeal.isNormal_reducedIdentityComponent G P (hJ.isNormal.map f.hom))
      (HopfIdeal.geometricallyConnected_reducedIdentityComponent G P)
      (HopfIdeal.smooth_reducedIdentityComponent G P)
      (CommHopfAlgCat.geometricallySolvablePoints_quotient_of_map_le f hcentral
        (HopfIdeal.le_reducedIdentityComponent G P) hJ.geometricallySolvable)
  let _ := HopfIdeal.moduleFinite_reducedQuotient G P hI
  exact eq_augmentation_of_moduleFinite_reducedQuotient f hf hJ

end FiniteTypeCommHopfAlgCat

namespace semisimpleCommHopfAlgProperty

variable {k : Type u} [Field k] {Q G : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **The target of a central isogeny from a semisimple group is semisimple.** If `f` represents
a central isogeny `G → Q` and `G` is semisimple, then so is `Q`. -/
theorem of_isCentralIsogeny (hG : semisimpleCommHopfAlgProperty k G) (f : Q.obj ⟶ G.obj)
    (hf : CommHopfAlgCat.IsCentralIsogeny f) : semisimpleCommHopfAlgProperty k Q := by
  have hG' :=
    (semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation
      k G).mp hG
  rw [semisimpleCommHopfAlgProperty_iff_solvableRadicalDefiningIdeal_baseChange_eq_augmentation]
  have hinj : Function.Injective f.hom := hf.injective
  have hred : geometricallyReducedCommHopfAlgProperty k Q.obj :=
    .of_injective f.hom.toAlgHom hinj <| geometricallyReducedCommHopfAlgProperty_of_smooth k _ <|
      (smoothCommHopfAlgProperty_iff _).mpr hG.smooth
  refine ⟨(smoothCommHopfAlgProperty_iff _).mp <|
      smoothCommHopfAlgProperty_of_geometricallyReduced k _ hred,
    .of_injective f.hom.toAlgHom hinj hG.geometricallyConnected, ?_⟩
  let K := AlgebraicClosure k
  have hfK := hf.baseChange (L := K)
  let _ : Algebra.Smooth k G := hG.smooth
  let _ : IsReduced (FiniteTypeCommHopfAlgCat.baseChange (K := K) G) :=
    isReduced_of_smooth K (K ⊗[k] G)
  exact FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal_eq_augmentation_of_isCentral
    (CommHopfAlgCat.baseChangeMap f) hfK.faithfullyFlat hfK.isCentral_kernelHopfIdeal hG'.2.2

end semisimpleCommHopfAlgProperty

end

end TauCeti
