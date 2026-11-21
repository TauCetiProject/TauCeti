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

1. Along any field extension `K / k`, the `K`-unipotent radical of `K ⊗[k] H` descends to a Hopf
   ideal over `k` if and only if it equals the base change of the `k`-unipotent radical. Along a
   surjective field map every Hopf ideal descends, so the unipotent radical commutes with such
   scalar extensions.
2. For every `k`-algebra equivalence `φ : K ≃ₐ[k] E` of extension fields, viewing `E` as a
   `K`-algebra through `φ` turns `φ ⊗ id` into scalar extension along the surjective tower
   `k → K → E`, so `φ ⊗ id` transports `unipotentRadicalDefiningIdeal (K ⊗[k] H)` onto
   `unipotentRadicalDefiningIdeal (E ⊗[k] H)`. When `L / k` is Galois (possibly infinite), taking
   `E = K = L` and applying `existsUnique_baseChangeHopfIdeal_eq_iff` descends
   `unipotentRadicalDefiningIdeal (L ⊗[k] H)` to a Hopf ideal of `H`, which step 1 identifies with
   `unipotentRadicalDefiningIdeal H`.
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
* `TauCeti.FiniteTypeCommHopfAlgCat.
    exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff`:
  the unipotent radical after field extension descends to `k` exactly when it equals the base change
  of the `k`-unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective`:
  the unipotent radical commutes with surjective field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.map_mem_unipotentRadicalDefiningIdeal_baseChange_iff`:
  `k`-algebra equivalences of extension fields preserve the base-changed unipotent radical; in
  particular its defining ideal is stable under `Gal(L / k)`.
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

variable {k K E : Type u} [Field k] [Field K] [Algebra k K] [Field E] [Algebra k E]

/-- Along any field extension `K / k`, the `K`-unipotent radical of `K ⊗[k] H` descends to a Hopf
ideal over `k` if and only if it equals the base change of the `k`-unipotent radical of `H`. -/
theorem exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (∃ J : HopfIdeal k H,
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) J =
          unipotentRadicalDefiningIdeal (baseChange (K := K) H)) ↔
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
        unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  constructor
  · rintro ⟨J, hJ⟩
    apply le_antisymm _ (unipotentRadicalDefiningIdeal_baseChange_le H)
    rw [← hJ]
    apply CommHopfAlgCat.baseChangeHopfIdeal_mono
    exact unipotentRadicalDefiningIdeal_le H J <|
      HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
        hJ.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal (baseChange (K := K) H)
  · intro h
    exact ⟨unipotentRadicalDefiningIdeal H, h⟩

/-- The unipotent radical commutes with scalar extension along a surjective map of fields. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (h : Function.Surjective (algebraMap k K)) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) :=
  (exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff H).mp
    (CommHopfAlgCat.baseChangeHopfIdeal_surjective (H := H.obj) h _)

/-- Any `k`-algebra equivalence `φ : K ≃ₐ[k] E` of extension fields transports the defining ideal of
the `K`-unipotent radical of `K ⊗[k] H` to that of `E ⊗[k] H` via `φ ⊗ id`. -/
theorem map_mem_unipotentRadicalDefiningIdeal_baseChange_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (φ : K ≃ₐ[k] E) (z : K ⊗[k] H) :
    TensorProduct.map φ.toLinearMap LinearMap.id z ∈
        unipotentRadicalDefiningIdeal (baseChange (K := E) H) ↔
      z ∈ unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let _ : Algebra K E := φ.toRingHom.toAlgebra
  have _ : IsScalarTower k K E :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (φ.commutes c).symm
  let t := baseChangeTowerIso (E := K) k E H
  have ht (w : K ⊗[k] H) :
      toBialgHom t.hom ((1 : E) ⊗ₜ[K] w) =
        TensorProduct.map φ.toLinearMap LinearMap.id w := by
    induction w with
    | add x y hx hy => simp [TensorProduct.tmul_add, hx, hy]
    | tmul c h =>
      simpa [t, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using
        baseChangeTowerIso_hom_apply (E := K) k E H 1 c h
  have hmem :
      z ∈ unipotentRadicalDefiningIdeal (baseChange (K := K) H) ↔
        (1 : E) ⊗ₜ[K] z ∈
          CommHopfAlgCat.baseChangeHopfIdeal (K := E)
            (unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
    rw [CommHopfAlgCat.mem_baseChangeHopfIdeal_iff,
      CommHopfAlgCat.baseChangeMap_apply_tmul,
      Module.FaithfullyFlat.one_tmul_eq_zero_iff,
      _root_.CommHopfAlgCat.mkQuotient_eq_zero_iff]
  rw [hmem,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective _ φ.surjective,
    ← comapOfSurjective_unipotentRadicalDefiningIdeal t,
    HopfIdeal.mem_comapOfSurjective, ht]

/-- Along a Galois extension `K / k`, the defining Hopf ideal of the unipotent radical commutes
with base change. -/
private theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois
    [IsGalois k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  apply (exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff H).mp
  refine ((CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff (H := H.obj)
    (unipotentRadicalDefiningIdeal (baseChange (K := K) H))).mpr ?_).exists
  intro σ z hz
  exact (map_mem_unipotentRadicalDefiningIdeal_baseChange_iff H σ z).mpr hz

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
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := Ω) H,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := Ω) (baseChange (K := K) H),
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
