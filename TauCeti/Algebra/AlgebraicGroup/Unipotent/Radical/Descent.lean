/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Descent and separable base change of the unipotent radical

Let `H` be a finite-type commutative Hopf algebra over a field `k`. Each of the three conditions
defining a unipotent-radical candidate — normality, geometric connectedness, and smooth geometric
unipotence — is preserved and reflected by arbitrary extension of the base field. Consequently,
whether a Hopf ideal of `H` cuts out a unipotent-radical candidate is invariant under every field
extension `K / k`.

Combined with Hopf-ideal descent, this yields two base-change comparisons for the unipotent radical
itself:

* along a surjective map of fields `k → K`, every Hopf ideal of `K ⊗[k] H` descends, so the
  unipotent radical commutes with scalar extension;
* along any separable algebraic field extension `K / k`, the unipotent radical commutes with scalar
  extension (`baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable`).

The separable case first handles Galois extensions `L / k`: any `k`-automorphism `σ` of `L` acts on
`L ⊗[k] H` as scalar extension along `σ`, so isomorphism invariance and the surjective-field case
show that the unipotent radical of `L ⊗[k] H` is Galois-stable and therefore descends to a
candidate over `k`. For a general separable extension `K / k`, a separable closure `E` of `K` is
Galois over both `k` and `K`, and faithful-flat injectivity of `baseChangeHopfIdeal` reduces `K / k`
to the two Galois steps `E / k` and `E / K`.

Whenever the defining ideal of the unipotent radical commutes with base change along `K / k`, both
the coordinate Hopf algebra `unipotentRadical H` and the normal affine quotient
`coinvariants (isNormal_unipotentRadicalDefiningIdeal H)` commute canonically with scalar extension.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange` and `baseChange_iff`:
  unipotent-radical candidates descend along arbitrary field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.`
  `baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective`:
  the unipotent radical commutes with surjective field maps.
* `TauCeti.FiniteTypeCommHopfAlgCat.`
  `map_mem_unipotentRadicalDefiningIdeal_baseChange_of_surjective`:
  surjective `k`-algebra morphisms between extension fields preserve the base-changed unipotent
  radical's defining ideal.
* `TauCeti.FiniteTypeCommHopfAlgCat.`
  `baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable`:
  formation of the unipotent radical commutes with separable algebraic field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIsoOfEq` and
  `unipotentRadicalBaseChangeIsoOfIsSeparable`: the induced coordinate-Hopf-algebra comparisons on
  the unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsUnipotentRadicalBaseChangeIsoOfEq` and
  `coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable`: the induced coordinate-Hopf-algebra
  comparisons on the normal affine quotient by the unipotent radical.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9, p. 399.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9.
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

/-- The unipotent-radical candidate conditions descend along an arbitrary field extension. -/
theorem of_baseChange
    (hI : IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :
    IsUnipotentRadicalCandidate H I := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine .mk (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hI.isNormal) ?_ ?_
  · exact geometricallyConnectedCommHopfAlgProperty.of_baseChange k K _
      ((geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso hI.geometricallyConnected)
  · exact smoothUnipotentCommHopfAlgProperty.of_baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient H I)
      ((smoothUnipotentCommHopfAlgProperty K).prop_of_iso
        (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K) qIso) hI.smoothUnipotent)

/-- Being a unipotent-radical candidate is invariant under arbitrary extension of the ground
field. -/
@[simp]
theorem baseChange_iff :
    IsUnipotentRadicalCandidate
        (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I) ↔
      IsUnipotentRadicalCandidate H I :=
  ⟨of_baseChange, baseChange⟩

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

section Surjective

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The unipotent radical commutes with scalar extension along a surjective map of fields. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (hsurj : Function.Surjective (algebraMap k K)) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le (K := K) H)
  obtain ⟨I, hI⟩ := CommHopfAlgCat.baseChangeHopfIdeal_surjective (H := H.obj) hsurj
    (unipotentRadicalDefiningIdeal (baseChange (K := K) H))
  rw [← hI]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H I <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hI.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
        (baseChange (K := K) H)

end Surjective

section Equivariance

variable {k E K : Type u} [Field k] [Field E] [Field K] [Algebra k E] [Algebra k K]

/-- A surjective `k`-algebra morphism `φ : E →ₐ[k] K` between extension fields carries the
defining ideal of the unipotent radical over `E` into the defining ideal of the unipotent radical
over `K`. In particular, `Gal(L / k)` preserves the unipotent radical of `L ⊗[k] H`. -/
theorem map_mem_unipotentRadicalDefiningIdeal_baseChange_of_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (φ : E →ₐ[k] K) (hφ : Function.Surjective φ)
    {x : E ⊗[k] H}
    (hx : x ∈ unipotentRadicalDefiningIdeal (baseChange (K := E) H)) :
    Algebra.TensorProduct.map φ (AlgHom.id k H) x ∈
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let _ : Algebra E K := φ.toRingHom.toAlgebra
  let _ : IsScalarTower k E K := IsScalarTower.of_algebraMap_eq fun r ↦ (φ.commutes r).symm
  let e : baseChange (K := K) (baseChange (K := E) H) ≅ baseChange (K := K) H :=
    baseChangeTowerIso (E := E) k K H
  have hmem : (1 : K) ⊗ₜ[E] x ∈
      (unipotentRadicalDefiningIdeal (baseChange (K := K) H)).comapOfSurjective
        (toBialgHom e.hom) (ConcreteCategory.bijective_of_isIso e.hom).2 := by
    rw [comapOfSurjective_unipotentRadicalDefiningIdeal e,
      ← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective (K := K)
        (baseChange (K := E) H) hφ]
    exact CommHopfAlgCat.one_tmul_mem_baseChangeHopfIdeal (K := K) hx
  have heval (y : E ⊗[k] H) : toBialgHom e.hom ((1 : K) ⊗ₜ[E] y) =
      Algebra.TensorProduct.map φ (AlgHom.id k H) y := by
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => rw [TensorProduct.tmul_add, map_add, map_add, hy₁, hy₂]
    | tmul s h =>
        rw [baseChangeTowerIso_hom_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        have hs : s • (1 : K) = φ s := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rw [hs]
  rw [← heval x]
  exact HopfIdeal.mem_comapOfSurjective.mp hmem

end Equivariance

section Separable

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois
    [IsGalois k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le (K := K) H)
  have hgal : ∀ σ : K ≃ₐ[k] K,
      ∀ x ∈ unipotentRadicalDefiningIdeal (baseChange (K := K) H),
        TensorProduct.map σ.toLinearMap LinearMap.id x ∈
          unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
    intro σ x hx
    have hmap (y : K ⊗[k] H) : TensorProduct.map σ.toLinearMap LinearMap.id y =
        Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k H) y := by
      induction y using TensorProduct.inductionOn with
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
      | tmul s h => rfl
    rw [hmap x]
    exact map_mem_unipotentRadicalDefiningIdeal_baseChange_of_surjective H σ.toAlgHom σ.surjective
      hx
  obtain ⟨I, hI, -⟩ := (CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff (H := H.obj)
    (unipotentRadicalDefiningIdeal (baseChange (K := K) H))).mpr hgal
  rw [← hI]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H I <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hI.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal
        (baseChange (K := K) H)

/-- **Formation of the unipotent radical commutes with separable algebraic field extensions**
(Milne, Proposition 19.9). In particular, this applies to every Galois extension and, over a
perfect base field, to every algebraic extension including `AlgebraicClosure k`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let E := SeparableClosure K
  have hsep_kE : Algebra.IsSeparable k E := Algebra.IsSeparable.trans k K E
  have _ : IsSepClosure k E := isSepClosure_iff.mpr ⟨inferInstance, hsep_kE⟩
  have _ : IsGalois k E := inferInstance
  let e : baseChange (K := E) (baseChange (K := K) H) ≅ baseChange (K := E) H :=
    baseChangeTowerIso (E := K) k E H
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := E)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal k E (E := K),
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := E) H,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := E)
      (baseChange (K := K) H),
    ← comapOfSurjective_unipotentRadicalDefiningIdeal e]
  ext x
  simp [HopfIdeal.mem_comapOfSurjective, toBialgHom, e, baseChangeTowerIso_hom_hom]

/-- Along a separable algebraic field extension, triviality of the unipotent radical is invariant
under scalar extension. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff_of_isSeparable
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) =
        HopfIdeal.augmentation K (baseChange (K := K) H) ↔
      unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable (K := K) H,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact (CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)).eq_iff

end Separable

section ComparisonIso

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- When the defining ideal of the unipotent radical commutes with scalar extension along `K / k`,
the scalar extension of the coordinate Hopf algebra `unipotentRadical H` is canonically isomorphic
to `unipotentRadical (baseChange H)`. -/
def unipotentRadicalBaseChangeIsoOfEq
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    baseChange (K := K) (unipotentRadical H) ≅ unipotentRadical (baseChange (K := K) H) :=
  ObjectProperty.isoMk _
    (CommHopfAlgCat.quotientBaseChangeIso (K := K) (unipotentRadicalDefiningIdeal H)).symm ≪≫
    eqToIso (congrArg (quotient (baseChange (K := K) H)) h)

/-- The forward base-change comparison on the unipotent radical commutes with the coordinate
quotient morphisms. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIsoOfEq H h).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) := by
  have hbase : baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K)
        (CommHopfAlgCat.quotientBaseChangeIso (K := K)
          (unipotentRadicalDefiningIdeal H)).symm).hom =
      mkQuotient (baseChange (K := K) H)
        (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H)) := by
    apply ObjectProperty.hom_ext
    rw [← cancel_mono (CommHopfAlgCat.quotientBaseChangeIso (K := K)
      (unipotentRadicalDefiningIdeal H)).hom]
    simp [unipotentRadicalCoordinateMap_def]
  rw [unipotentRadicalBaseChangeIsoOfEq, Iso.trans_hom, eqToIso.hom, ← Category.assoc, hbase,
    unipotentRadicalCoordinateMap_def, mkQuotient_comp_eqToHom h.symm]

/-- The inverse base-change comparison on the unipotent radical commutes with the coordinate
quotient morphisms. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_inv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIsoOfEq H h).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) := by
  rw [← cancel_mono (unipotentRadicalBaseChangeIsoOfEq H h).hom]
  simp

/-- Along a separable algebraic field extension `K / k`, the scalar extension of the unipotent
radical's coordinate Hopf algebra is canonically isomorphic to the unipotent radical of the
base-changed coordinate Hopf algebra. -/
def unipotentRadicalBaseChangeIsoOfIsSeparable
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChange (K := K) (unipotentRadical H) ≅ unipotentRadical (baseChange (K := K) H) :=
  unipotentRadicalBaseChangeIsoOfEq H
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable H)

/-- The forward separable base-change comparison on the unipotent radical commutes with the
coordinate quotient morphisms. -/
@[reassoc (attr := simp)]
theorem
baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfIsSeparable_hom
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIsoOfIsSeparable (K := K) H).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) :=
  baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_hom H _

/-- The inverse separable base-change comparison on the unipotent radical commutes with the
coordinate quotient morphisms. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfIsSeparable_inv
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIsoOfIsSeparable (K := K) H).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) :=
  unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIsoOfEq_inv H _

/-- When the defining ideal of the unipotent radical commutes with scalar extension along `K / k`,
the scalar extension of the normal affine quotient `G ⧸ R_u(G)` is canonically isomorphic to the
quotient of `G_K` by `R_u(G_K)`. -/
def coinvariantsUnipotentRadicalBaseChangeIsoOfEq
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
  CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) (isNormal_unipotentRadicalDefiningIdeal H) ≪≫
    CommHopfAlgCat.coinvariantsIsoOfEq
      (CommHopfAlgCat.isNormal_baseChangeHopfIdeal (K := K)
        (isNormal_unipotentRadicalDefiningIdeal H))
      (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) h

/-- The forward quotient comparison commutes with the coordinate inclusions of the normal affine
quotients. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfEq_hom_comp_coinvariantsι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfEq H h).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) := by
  simp [coinvariantsUnipotentRadicalBaseChangeIsoOfEq]

/-- The inverse quotient comparison commutes with the coordinate inclusions of the normal affine
quotients. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfEq_inv_comp_baseChangeMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfEq H h).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [← coinvariantsUnipotentRadicalBaseChangeIsoOfEq_hom_comp_coinvariantsι H h,
    Iso.inv_hom_id_assoc]

/-- Along a separable algebraic field extension `K / k`, the normal affine quotient `G ⧸ R_u(G)`
commutes canonically with scalar extension. -/
def coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq H
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isSeparable H)

/-- The forward separable base-change comparison on `G ⧸ R_u(G)` commutes with the quotient
coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable_hom_comp_coinvariantsι
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable (K := K) H).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq_hom_comp_coinvariantsι H _

/-- The inverse separable base-change comparison on `G ⧸ R_u(G)` commutes with the quotient
coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable_inv_comp_baseChangeMap
    [Algebra.IsSeparable k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIsoOfIsSeparable (K := K) H).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
  coinvariantsUnipotentRadicalBaseChangeIsoOfEq_inv_comp_baseChangeMap H _

end ComparisonIso

end FiniteTypeCommHopfAlgCat

end

end TauCeti
