/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.SeparableDegree
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Galois and separable descent of the unipotent radical

Let `H` be a finite-type commutative Hopf algebra over a field `k`. Extending scalars to any field
`K / k` preserves and reflects unipotent-radical candidates: normality, geometric connectedness,
and smooth geometric unipotence of the coordinate quotient each descend along `k → K`.

For an arbitrary extension `K / k`, the defining Hopf ideal of the unipotent radical of `K ⊗[k] H`
need not come from `k`, because the geometric unipotent radical can fail to descend over an
imperfect field. However, `unipotentRadicalDefiningIdeal (K ⊗[k] H)` is stable under every
scalar-factor automorphism `σ ⊗ id` induced by `σ : K ≃ₐ[k] K`: wrapping `K` with the `σ`-twisted
`K`-algebra structure factors `σ ⊗ id` through base changes along two surjective field maps and the
tower comparison `baseChangeTowerIso`, avoiding any diamond with `Algebra.id K`.

When `K / k` is Galois, Galois descent of Hopf ideals
(`CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`) descends the radical ideal to `k`, and
candidate descent identifies the descended ideal with `unipotentRadicalDefiningIdeal H`. Passing to
a separable closure of `K` extends this equality—together with the induced base-change isomorphisms
for the unipotent radical and for the normal quotient `G ⧸ R_u(G)`—to every separable algebraic
extension `K / k`, finite or infinite. In particular, over a perfect field the `k`-unipotent
radical agrees after base change with the geometric unipotent radical over `AlgebraicClosure k`.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange` and
  `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.baseChange_iff`: unipotent-radical candidatehood
  descends along arbitrary field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.map_mem_unipotentRadicalDefiningIdeal_baseChange`: the
  unipotent radical after field extension is stable under scalar-factor field automorphisms.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`: formation
  of the unipotent radical commutes with every separable algebraic field extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff`:
  triviality of the unipotent radical is invariant under separable algebraic field extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIso`: the coordinate isomorphism
  `K ⊗[k] R_u(G) ≅ R_u(G_K)` along a separable algebraic extension `K / k`.
* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsUnipotentRadicalBaseChangeIso`: the coordinate
  isomorphism `(G ⧸ R_u(G))_K ≅ G_K ⧸ R_u(G_K)` along a separable algebraic extension `K / k`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 19.9 and 19.11.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9(1).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §AG.14 and §11.21.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- Unipotent-radical candidatehood descends along an arbitrary field extension. -/
theorem of_baseChange
    (hI : IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :
    IsUnipotentRadicalCandidate H I := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine .mk (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hI.isNormal) ?_ ?_
  · exact geometricallyConnectedCommHopfAlgProperty.of_baseChange k K _
      ((geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso hI.geometricallyConnected)
  · exact smoothUnipotentCommHopfAlgProperty.of_baseChange _
      ((smoothUnipotentCommHopfAlgProperty K).prop_of_iso
        (ObjectProperty.isoMk _ qIso) hI.smoothUnipotent)

/-- Being a unipotent-radical candidate is invariant under arbitrary field extension. -/
@[simp]
theorem baseChange_iff :
    IsUnipotentRadicalCandidate
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) ↔
      IsUnipotentRadicalCandidate H I :=
  ⟨of_baseChange, baseChange⟩

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The unipotent radical commutes with scalar extension along a surjective map of fields. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : Function.Surjective (algebraMap k K)) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le H)
  obtain ⟨I, hI⟩ := CommHopfAlgCat.baseChangeHopfIdeal_surjective (H := H.obj) h
    (unipotentRadicalDefiningIdeal (baseChange (K := K) H))
  rw [← hI]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H I <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hI.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
        (baseChange (K := K) H)

/-- Private wrapper around `K` carrying the `K`-algebra structure twisted by `σ : K ≃ₐ[k] K`,
used to factor `σ ⊗ id` through two surjective field extensions without creating an `Algebra K K`
diamond. -/
private structure ScalarTwist {k K : Type u} [Field k] [Field K] [Algebra k K]
    (_ : K ≃ₐ[k] K) : Type u where
  val : K

private def ScalarTwist.equiv {k K : Type u} [Field k] [Field K] [Algebra k K]
    (σ : K ≃ₐ[k] K) : ScalarTwist σ ≃ K where
  toFun x := x.val
  invFun y := ⟨y⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    Field (ScalarTwist σ) :=
  (ScalarTwist.equiv σ).field

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    Algebra k (ScalarTwist σ) :=
  (ScalarTwist.equiv σ).algebra k

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    Algebra K (ScalarTwist σ) :=
  RingHom.toAlgebra
    (((ScalarTwist.equiv σ).ringEquiv.symm : K →+* ScalarTwist σ).comp σ.toRingHom)

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    IsScalarTower k K (ScalarTwist σ) :=
  IsScalarTower.of_algebraMap_eq fun c ↦
    congrArg (ScalarTwist.equiv σ).symm (σ.commutes c).symm

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    Algebra (ScalarTwist σ) K :=
  RingHom.toAlgebra ((ScalarTwist.equiv σ).ringEquiv : ScalarTwist σ →+* K)

private instance {k K : Type u} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K) :
    IsScalarTower k (ScalarTwist σ) K :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The defining Hopf ideal of the unipotent radical of `K ⊗[k] H` is stable under the
scalar-factor action `σ ⊗ id` of every `k`-automorphism `σ` of `K`. -/
theorem map_mem_unipotentRadicalDefiningIdeal_baseChange
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (σ : K ≃ₐ[k] K)
    {x : baseChange (K := K) H}
    (hx : x ∈ unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    TensorProduct.map σ.toLinearMap LinearMap.id x ∈
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let e₁ := baseChangeTowerIso (E := K) k (ScalarTwist σ) H
  let e₂ := baseChangeTowerIso (E := ScalarTwist σ) k K H
  have hsurj₁ : Function.Surjective (algebraMap K (ScalarTwist σ)) :=
    fun m ↦ ⟨σ.symm m.val, congrArg (ScalarTwist.equiv σ).symm (σ.apply_symm_apply m.val)⟩
  have hsurj₂ : Function.Surjective (algebraMap (ScalarTwist σ) K) := fun a ↦ ⟨⟨a⟩, rfl⟩
  have hmem₁ : (1 : ScalarTwist σ) ⊗ₜ[K] x ∈
      CommHopfAlgCat.baseChangeHopfIdeal (K := ScalarTwist σ)
        (unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
    CommHopfAlgCat.one_tmul_mem_baseChangeHopfIdeal hx
  rw [baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective _ hsurj₁,
    ← comapOfSurjective_unipotentRadicalDefiningIdeal e₁,
    HopfIdeal.mem_comapOfSurjective] at hmem₁
  have hmem₂ : (1 : K) ⊗ₜ[ScalarTwist σ] toBialgHom e₁.hom ((1 : ScalarTwist σ) ⊗ₜ[K] x) ∈
      CommHopfAlgCat.baseChangeHopfIdeal (K := K)
        (unipotentRadicalDefiningIdeal (baseChange (K := ScalarTwist σ) H)) :=
    CommHopfAlgCat.one_tmul_mem_baseChangeHopfIdeal hmem₁
  rw [baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective _ hsurj₂,
    ← comapOfSurjective_unipotentRadicalDefiningIdeal e₂,
    HopfIdeal.mem_comapOfSurjective] at hmem₂
  have heval (y : K ⊗[k] H) :
      toBialgHom e₂.hom ((1 : K) ⊗ₜ[ScalarTwist σ]
        toBialgHom e₁.hom ((1 : ScalarTwist σ) ⊗ₜ[K] y)) =
      TensorProduct.map σ.toLinearMap LinearMap.id y := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add, map_add, hy, hz]
    | tmul a h =>
      rw [baseChangeTowerIso_hom_apply, baseChangeTowerIso_hom_apply,
        Algebra.smul_def, mul_one, Algebra.smul_def, mul_one]
      rfl
  rwa [heval x] at hmem₂

/-- Along a Galois extension `K / k`, the defining ideal of the unipotent radical commutes with
scalar extension. -/
private theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois
    [IsGalois k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le H)
  obtain ⟨I, hI, -⟩ :=
    (CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff
      (unipotentRadicalDefiningIdeal (baseChange (K := K) H))).mpr
      fun σ _ hx ↦ map_mem_unipotentRadicalDefiningIdeal_baseChange H σ hx
  rw [← hI]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H I <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hI.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal (baseChange (K := K) H)

/-- **Formation of the unipotent radical commutes with separable algebraic field extensions.** -/
@[simp]
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let L : Type u := SeparableClosure K
  let _ : Algebra k L := Algebra.compHom L (algebraMap k K)
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  have _ : Algebra.IsSeparable k L := Algebra.IsSeparable.trans k K L
  have _ : IsSepClosure k L := isSepClosure_iff.mpr ⟨inferInstance, inferInstance⟩
  have _ : IsGalois k L := IsSepClosure.isGalois
  let e := baseChangeTowerIso (E := K) k L H
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := L)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal (E := K) k L,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := L) H,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := L)
      (baseChange (K := K) H)]
  simpa only [e, toBialgHom, baseChangeTowerIso_hom_hom] using
    comapOfSurjective_unipotentRadicalDefiningIdeal e

/-- Triviality of the unipotent radical is invariant under separable algebraic extension of the
ground field. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) =
        HopfIdeal.augmentation K (baseChange (K := K) H) ↔
      unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact CommHopfAlgCat.baseChangeHopfIdeal_injective.eq_iff

private def quotientBaseChangeIsoOfEq
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    {I : HopfIdeal k H} {J : HopfIdeal K (baseChange (K := K) H)}
    (hIJ : CommHopfAlgCat.baseChangeHopfIdeal (K := K) I = J) :
    baseChange (K := K) (quotient H I) ≅ quotient (baseChange (K := K) H) J :=
  (ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBaseChangeIso (K := K) I)).symm ≪≫
    eqToIso (congrArg (quotient (baseChange (K := K) H)) hIJ)

private theorem baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfEq_hom
    {H : FiniteTypeCommHopfAlgCat.{u, u} k}
    {I : HopfIdeal k H} {J : HopfIdeal K (baseChange (K := K) H)}
    (hIJ : CommHopfAlgCat.baseChangeHopfIdeal (K := K) I = J) :
    baseChangeMap (K := K) (mkQuotient H I) ≫ (quotientBaseChangeIsoOfEq hIJ).hom =
      mkQuotient (baseChange (K := K) H) J := by
  subst hIJ
  apply ObjectProperty.hom_ext
  rw [← cancel_mono (CommHopfAlgCat.quotientBaseChangeIso (K := K) I).hom]
  simp [quotientBaseChangeIsoOfEq]

/-- **Scalar extension of the unipotent radical along a separable algebraic field extension.**
Contravariantly, this identifies `(R_u(G))_K` with `R_u(G_K)`. -/
def unipotentRadicalBaseChangeIso [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChange (K := K) (unipotentRadical H) ≅ unipotentRadical (baseChange (K := K) H) :=
  quotientBaseChangeIsoOfEq (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H)

/-- The unipotent-radical base-change isomorphism commutes with the coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) := by
  rw [unipotentRadicalBaseChangeIso, unipotentRadicalCoordinateMap_def,
    unipotentRadicalCoordinateMap_def]
  exact baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfEq_hom
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H)

/-- The inverse unipotent-radical base-change isomorphism commutes with the coordinate quotient
maps. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_inv
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) := by
  rw [← cancel_mono (unipotentRadicalBaseChangeIso (K := K) H).hom]
  simp

private def coinvariantsBaseChangeIsoOfEq
    {H : _root_.CommHopfAlgCat.{u} k} {I : HopfIdeal k H} (hI : I.IsNormal)
    {J : HopfIdeal K (CommHopfAlgCat.baseChange (K := K) H)} (hJ : J.IsNormal)
    (hIJ : CommHopfAlgCat.baseChangeHopfIdeal (K := K) I = J) :
    CommHopfAlgCat.baseChange (K := K) (CommHopfAlgCat.coinvariants hI) ≅
      CommHopfAlgCat.coinvariants hJ := by
  subst hIJ
  exact CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) hI

private theorem coinvariantsBaseChangeIsoOfEq_hom_comp_coinvariantsι
    {H : _root_.CommHopfAlgCat.{u} k} {I : HopfIdeal k H} (hI : I.IsNormal)
    {J : HopfIdeal K (CommHopfAlgCat.baseChange (K := K) H)} (hJ : J.IsNormal)
    (hIJ : CommHopfAlgCat.baseChangeHopfIdeal (K := K) I = J) :
    (coinvariantsBaseChangeIsoOfEq hI hJ hIJ).hom ≫ CommHopfAlgCat.coinvariantsι hJ =
      CommHopfAlgCat.baseChangeMap (K := K) (CommHopfAlgCat.coinvariantsι hI) := by
  subst hIJ
  exact CommHopfAlgCat.coinvariantsBaseChangeIso_hom_comp_coinvariantsι hI

/-- **Scalar extension of the normal affine quotient `G ⧸ R_u(G)` along a separable algebraic field
extension.** Contravariantly, this identifies `(G ⧸ R_u(G))_K` with `G_K ⧸ R_u(G_K)`. -/
def coinvariantsUnipotentRadicalBaseChangeIso [Algebra.IsSeparable k K]
    (G : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal G)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) :=
  coinvariantsBaseChangeIsoOfEq
    (isNormal_unipotentRadicalDefiningIdeal G)
    (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G))
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) G)

/-- The base-change comparison for `G ⧸ R_u(G)` commutes with the quotient coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι
    [Algebra.IsSeparable k K] (G : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) G).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G)) :=
  coinvariantsBaseChangeIsoOfEq_hom_comp_coinvariantsι
    (isNormal_unipotentRadicalDefiningIdeal G)
    (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G))
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) G)

/-- The inverse base-change comparison for `G ⧸ R_u(G)` commutes with the quotient coordinate
inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_inv_comp_baseChangeMap
    [Algebra.IsSeparable k K] (G : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) G).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal G)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) G)) := by
  rw [← coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι G, Iso.inv_hom_id_assoc]

end FiniteTypeCommHopfAlgCat

end

end TauCeti
