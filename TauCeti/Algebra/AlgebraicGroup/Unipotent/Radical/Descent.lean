/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Descent and separable base change of the unipotent radical

The conditions defining a unipotent-radical candidate — normality, geometric connectedness, and
smooth geometric unipotence of the represented closed subgroup — are all reflected by arbitrary
field extensions. Consequently, a base-changed Hopf ideal cuts out a unipotent-radical candidate
after scalar extension if and only if the original Hopf ideal does.

Combined with Galois descent of Hopf ideals, this yields invariance of the unipotent radical along
separable algebraic extensions:

1. For every field extension `L / k` and every `k`-algebra automorphism `σ` of `L`, the scalar
   action `σ ⊗ id` on `L ⊗[k] H` preserves `unipotentRadicalDefiningIdeal (L ⊗[k] H)`. Viewing a
   copy `L'` of `L` as an `L`-algebra through `σ` turns `σ ⊗ id` into scalar extension along the
   tower `k → L → L'`, where isomorphism invariance and base-change containment of the unipotent
   radical apply directly.
2. When `L / k` is Galois (possibly infinite), `existsUnique_baseChangeHopfIdeal_eq_iff` descends
   `unipotentRadicalDefiningIdeal (L ⊗[k] H)` to a Hopf ideal of `H`, which candidate descent
   identifies with `unipotentRadicalDefiningIdeal H`.
3. For an arbitrary separable algebraic extension `K / k`, embedding `K` into `SeparableClosure k`
   makes both `SeparableClosure k / k` and `SeparableClosure k / K` Galois, and faithful flatness
   reflects equality of the two defining ideals over `K ⊗[k] H`.

Over a perfect field `k`, every algebraic extension is separable, so this applies in particular to
`AlgebraicClosure k / k` and identifies the base change of the `k`-unipotent radical with the
geometric unipotent radical. Combining this defining-ideal identity with scalar extension of normal
coinvariants also identifies `(G ⧸ R_{u,k}(G))_K` with `G_K ⧸ R_{u,K}(G_K)` along every separable
algebraic extension `K / k`.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange` and
  `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.baseChange_iff`: descent and field-extension
  invariance of unipotent-radical candidates.
* `TauCeti.FiniteTypeCommHopfAlgCat.map_mem_unipotentRadicalDefiningIdeal_baseChange`: stability of
  the base-changed unipotent radical's defining ideal under `Gal(L / k)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`: the
  defining ideal of the unipotent radical commutes with separable algebraic field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIso`: the induced coordinate
  Hopf-algebra isomorphism `K ⊗[k] R_{u,k}(G) ≅ R_{u,K}(G_K)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalCoinvariantsBaseChangeIso`: the induced
  coordinate Hopf-algebra isomorphism for the normal affine quotient `(G ⧸ R_{u,k}(G))_K ≅
  G_K ⧸ R_{u,K}(G_K)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal`: the corresponding
  equality of closed subgroup schemes.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9(1).
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The unipotent-radical candidate conditions descend along arbitrary field extensions. -/
theorem of_baseChange
    (hI : IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :
    IsUnipotentRadicalCandidate H I := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine .mk (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hI.isNormal) ?_ ?_
  · exact geometricallyConnectedCommHopfAlgProperty.of_baseChange k K _
      ((geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso hI.geometricallyConnected)
  · exact smoothUnipotentCommHopfAlgProperty.of_baseChange (K := K) _
      ((smoothUnipotentCommHopfAlgProperty K).prop_of_iso
        (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K) qIso) hI.smoothUnipotent)

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

section ArbitraryExtension

/-- A copy of `L` indexed by `σ : L ≃ₐ[k] L`, equipping `L` with the `L`-algebra structure induced
by `σ` without creating a typeclass diamond with `Algebra.id L`, while keeping the underlying
`k`-algebra structure definitionally identical to `L`. -/
private def ScalarTwist {k L : Type u} [Field k] [Field L] [Algebra k L] (_ : L ≃ₐ[k] L) :
    Type u :=
  L

private instance {k L : Type u} [Field k] [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    Field (ScalarTwist σ) :=
  ‹Field L›

private instance {k L : Type u} [Field k] [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    Algebra k (ScalarTwist σ) :=
  ‹Algebra k L›

private def toScalarTwistRingHom {k L : Type u} [Field k] [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) : L →+* ScalarTwist σ :=
  σ.toRingHom

private instance {k L : Type u} [Field k] [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    Algebra L (ScalarTwist σ) :=
  (toScalarTwistRingHom σ).toAlgebra

private instance {k L : Type u} [Field k] [Field L] [Algebra k L] (σ : L ≃ₐ[k] L) :
    IsScalarTower k L (ScalarTwist σ) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ (σ.commutes c).symm

private def toScalarTwistTensor {k L : Type u} [Field k] [Field L] [Algebra k L]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} (σ : L ≃ₐ[k] L) (y : L ⊗[k] H) :
    ScalarTwist σ ⊗[k] H :=
  y

/-- Because `Algebra L (ScalarTwist σ)` is `(toScalarTwistRingHom σ).toAlgebra`, its `algebraMap`
is `toScalarTwistRingHom σ`. -/
private lemma toScalarTwistRingHom_eq_algebraMap {k L : Type u} [Field k] [Field L] [Algebra k L]
    (σ : L ≃ₐ[k] L) (c : L) :
    toScalarTwistRingHom σ c = algebraMap L (ScalarTwist σ) c :=
  rfl

/-- Because `ScalarTwist σ` inherits its `k`-module structure from `L` and `toScalarTwistRingHom σ`
is `σ` on the underlying type, viewing `(σ ⊗ id)(c ⊗ h)` in `ScalarTwist σ ⊗[k] H` gives
`toScalarTwistRingHom σ c ⊗ h`. -/
private lemma toScalarTwistTensor_map_tmul {k L : Type u} [Field k] [Field L] [Algebra k L]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} (σ : L ≃ₐ[k] L) (c : L) (h : H) :
    toScalarTwistTensor σ (TensorProduct.map σ.toLinearMap LinearMap.id (c ⊗ₜ[k] h)) =
      toScalarTwistRingHom σ c ⊗ₜ[k] h :=
  rfl

/-- Viewing an element of `L ⊗[k] H` in `ScalarTwist σ ⊗[k] H` preserves addition because
`ScalarTwist σ` shares the `Field` and `Algebra k` instances of `L`. -/
private lemma toScalarTwistTensor_add {k L : Type u} [Field k] [Field L] [Algebra k L]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} (σ : L ≃ₐ[k] L) (x y : L ⊗[k] H) :
    toScalarTwistTensor σ (x + y) = toScalarTwistTensor σ x + toScalarTwistTensor σ y :=
  rfl

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Because `baseChange` and `unipotentRadicalDefiningIdeal` depend only on the `Field` and
`Algebra k` instances on the extension field — which on `ScalarTwist σ` are definitionally those of
`L`, independent of the auxiliary `Algebra L (ScalarTwist σ)` instance — `toScalarTwistTensor σ`
preserves and reflects membership in `unipotentRadicalDefiningIdeal`. -/
private lemma mem_unipotentRadicalDefiningIdeal_scalarTwist_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (σ : L ≃ₐ[k] L) (x : L ⊗[k] H) :
    toScalarTwistTensor σ x ∈ unipotentRadicalDefiningIdeal (baseChange (K := ScalarTwist σ) H) ↔
      x ∈ unipotentRadicalDefiningIdeal (baseChange (K := L) H) :=
  Iff.rfl

/-- Viewing `L' := ScalarTwist σ` as an `L`-algebra via `σ : L ≃ₐ[k] L`, the inverse tower
comparison `(L' ⊗[k] H) → L' ⊗[L] (L ⊗[k] H)` sends `(σ ⊗ id)(z)` to `1 ⊗ z`. -/
private theorem baseChangeTowerIso_inv_scalarTwist_map_eq_one_tmul
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (σ : L ≃ₐ[k] L) (z : L ⊗[k] H) :
    toBialgHom (baseChangeTowerIso (E := L) k (ScalarTwist σ) H).inv
        (toScalarTwistTensor σ (TensorProduct.map σ.toLinearMap LinearMap.id z)) =
      (1 : ScalarTwist σ) ⊗ₜ[L] z := by
  induction z using TensorProduct.inductionOn with
  | tmul c h =>
    have hsmul : toScalarTwistRingHom σ c = c • (1 : ScalarTwist σ) := by
      rw [toScalarTwistRingHom_eq_algebraMap, Algebra.smul_def, mul_one]
    rw [toScalarTwistTensor_map_tmul, baseChangeTowerIso_inv_apply, hsmul, TensorProduct.smul_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    rw [map_add, toScalarTwistTensor_add, map_add, TensorProduct.tmul_add, hx, hy]

/-- The defining Hopf ideal of the unipotent radical of `L ⊗[k] H` is stable under every `k`-algebra
automorphism of the scalar factor `L`. -/
theorem map_mem_unipotentRadicalDefiningIdeal_baseChange
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) (σ : L ≃ₐ[k] L)
    {x : L ⊗[k] H} (hx : x ∈ unipotentRadicalDefiningIdeal (baseChange (K := L) H)) :
    TensorProduct.map σ.toLinearMap LinearMap.id x ∈
      unipotentRadicalDefiningIdeal (baseChange (K := L) H) := by
  let e := baseChangeTowerIso (E := L) k (ScalarTwist σ.symm) H
  let z := TensorProduct.map σ.toLinearMap LinearMap.id x
  have hz : TensorProduct.map σ.symm.toLinearMap LinearMap.id z = x := by
    dsimp only [z]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id]
    have hcomp : σ.symm.toLinearMap.comp σ.toLinearMap = LinearMap.id := by
      ext c
      exact σ.symm_apply_apply c
    rw [hcomp, TensorProduct.map_id, LinearMap.id_apply]
  have hx' : toScalarTwistTensor σ.symm (TensorProduct.map σ.symm.toLinearMap LinearMap.id z) ∈
      unipotentRadicalDefiningIdeal (baseChange (K := ScalarTwist σ.symm) H) := by
    rwa [hz, mem_unipotentRadicalDefiningIdeal_scalarTwist_iff]
  rw [← comapOfSurjective_unipotentRadicalDefiningIdeal e.symm,
    HopfIdeal.mem_comapOfSurjective, Iso.symm_hom,
    baseChangeTowerIso_inv_scalarTwist_map_eq_one_tmul H σ.symm z] at hx'
  have hmem := unipotentRadicalDefiningIdeal_baseChange_le (K := ScalarTwist σ.symm)
    (baseChange (K := L) H) hx'
  rwa [CommHopfAlgCat.mem_baseChangeHopfIdeal_iff, CommHopfAlgCat.baseChangeMap_apply_tmul,
    Module.FaithfullyFlat.one_tmul_eq_zero_iff, _root_.CommHopfAlgCat.mkQuotient_eq_zero_iff]
    at hmem

/-- Along a Galois extension `L / k`, the defining Hopf ideal of the unipotent radical commutes
with base change. -/
private theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois [IsGalois k L]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := L) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := L) H) := by
  apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le H)
  obtain ⟨J, hJ, -⟩ := (CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff
    (unipotentRadicalDefiningIdeal (baseChange (K := L) H))).mpr
      fun σ _ hx ↦ map_mem_unipotentRadicalDefiningIdeal_baseChange H σ hx
  rw [← hJ]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H J <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hJ.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal (baseChange (K := L) H)

end ArbitraryExtension

section Separable

variable {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]

/-- **Formation of the unipotent radical commutes with separable algebraic field extensions.**
In particular, when `k` is perfect this applies to `AlgebraicClosure k / k`, identifying the base
change of the `k`-unipotent radical with the geometric unipotent radical. -/
@[simp]
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let Ω := SeparableClosure k
  let ι : K →ₐ[k] Ω := IsSepClosed.lift
  let _ : Algebra K Ω := ι.toAlgebra
  have : IsScalarTower k K Ω := IsScalarTower.of_algebraMap_eq fun c ↦ (ι.commutes c).symm
  have : IsGalois K Ω := IsGalois.tower_top_of_isGalois k K Ω
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := Ω)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal k Ω (E := K),
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (L := Ω) H,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (L := Ω) (baseChange (K := K) H),
    ← comapOfSurjective_unipotentRadicalDefiningIdeal (baseChangeTowerIso (E := K) k Ω H)]
  ext y
  simp only [HopfIdeal.mem_comapOfSurjective, toBialgHom, baseChangeTowerIso_hom_hom]

/-- Along a separable algebraic field extension, triviality of the unipotent radical is preserved
and reflected by base change. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) =
        HopfIdeal.augmentation K (baseChange (K := K) H) ↔
      unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact (CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)).eq_iff

/-- **Base-change comparison for the unipotent radical** along a separable algebraic field
extension `K / k`: the scalar extension of the coordinate Hopf algebra of `R_{u,k}(G)` is
canonically isomorphic to the coordinate Hopf algebra of `R_{u,K}(G_K)`. -/
def unipotentRadicalBaseChangeIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChange (K := K) (unipotentRadical H) ≅ unipotentRadical (baseChange (K := K) H) :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.quotientBaseChangeIsoOfMapEq
      (unipotentRadicalDefiningIdeal H)
      (unipotentRadicalDefiningIdeal (baseChange (K := K) H))
      (Iso.refl (CommHopfAlgCat.baseChange (K := K) H.obj))
      (by
        rw [Iso.refl_hom, ← _root_.CommHopfAlgCat.ofHom_id, _root_.CommHopfAlgCat.hom_ofHom,
          HopfIdeal.map_id, baseChangeHopfIdeal_unipotentRadicalDefiningIdeal])

/-- The unipotent-radical base-change isomorphism commutes with the coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).hom =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) := by
  apply ObjectProperty.hom_ext
  simp only [unipotentRadicalBaseChangeIso, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.isoMk_hom, unipotentRadicalCoordinateMap_def, ObjectProperty.homMk_hom,
    CommHopfAlgCat.baseChangeMap_mkQuotient_comp_quotientBaseChangeIsoOfMapEq_hom,
    Iso.refl_hom, Category.id_comp]

/-- The inverse unipotent-radical base-change isomorphism commutes with the coordinate quotient
maps. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_inv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).inv =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) := by
  rw [← baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Base-change comparison for the normal affine quotient by the unipotent radical** along a
separable algebraic field extension `K / k`: the scalar extension of the coinvariant coordinate
Hopf algebra of `G ⧸ R_{u,k}(G)` is canonically isomorphic to that of `G_K ⧸ R_{u,K}(G_K)`.
No smoothness or geometric-reducedness hypothesis on `G` is required. -/
def unipotentRadicalCoinvariantsBaseChangeIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
  CommHopfAlgCat.coinvariantsBaseChangeIso (K := K)
      (isNormal_unipotentRadicalDefiningIdeal H) ≪≫
    eqToIso (CommHopfAlgCat.coinvariants_eq_of_eq _ _
      (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H))

/-- The base-change comparison for `G ⧸ R_{u,k}(G)` commutes with the quotient coordinate
inclusions. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoinvariantsBaseChangeIso_hom_comp_coinvariantsι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (unipotentRadicalCoinvariantsBaseChangeIso (K := K) H).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) := by
  rw [unipotentRadicalCoinvariantsBaseChangeIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    CommHopfAlgCat.eqToHom_comp_coinvariantsι _ _
      (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H),
    CommHopfAlgCat.coinvariantsBaseChangeIso_hom_comp_coinvariantsι]

/-- The inverse base-change comparison for `G ⧸ R_{u,k}(G)` commutes with the quotient coordinate
inclusions. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoinvariantsBaseChangeIso_inv_comp_baseChangeMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (unipotentRadicalCoinvariantsBaseChangeIso (K := K) H).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [← unipotentRadicalCoinvariantsBaseChangeIso_hom_comp_coinvariantsι, Iso.inv_hom_id_assoc]

/-- **Scheme-level base change of the unipotent radical.** Along a separable algebraic field
extension `K / k`, the base change of the closed subgroup scheme `R_{u,k}(G) ≤ G` along
`Spec K ⟶ Spec k` agrees, under `hopfSpecBaseChangeGrpIso`, with `R_{u,K}(G_K) ≤ G_K`. -/
theorem mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ClosedSubgroupScheme.mapIso (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (S := K) H.obj)
        ((CommHopfAlgCat.quotientClosedSubgroup H.obj (unipotentRadicalDefiningIdeal H)).baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      CommHopfAlgCat.quotientClosedSubgroup (CommHopfAlgCat.baseChange (K := K) H.obj)
        (unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [_root_.CommHopfAlgCat.mapIso_baseChange_quotientClosedSubgroup,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal]

end Separable

end FiniteTypeCommHopfAlgCat

end

end TauCeti
