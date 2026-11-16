/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import Mathlib.FieldTheory.IsSepClosed
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Descent of the unipotent radical

The conditions defining a unipotent-radical candidate — normality, geometric connectedness, and
smooth geometric unipotence — are reflected by arbitrary field extensions. Consequently, the
unipotent radical of a base-changed group `G_K` descends to `k` if and only if it equals the base
change of the `k`-unipotent radical `R_{u,k}(G)`.

For any `k`-algebra equivalence `e : K₁ ≃ₐ[k] K₂` between extension fields, transporting Hopf
ideals along `e` via `CommHopfAlgCat.mapBaseChangeHopfIdeal` preserves unipotent-radical
candidates and therefore carries `R_{u,K₁}(G_{K₁})` to `R_{u,K₂}(G_{K₂})`. In particular, over
any Galois extension `L / k` (finite or infinite), the `L`-unipotent radical is stable under
`Gal(L / k)` and hence descends to `k` by `CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`.

Embedding an arbitrary separable algebraic extension `K / k` into the separable closure of `k` —
which is Galois over both `k` and `K` — shows that formation of the unipotent radical commutes
with every separable algebraic extension `K / k`, yielding canonical base-change isomorphisms for
both the unipotent radical `R_u(G)` and the affine quotient `G ⧸ R_u(G)`. Over a perfect field,
every algebraic extension (in particular the algebraic closure) is separable, so the native
`k`-unipotent radical identifies with the geometric unipotent radical after scalar extension to
`AlgebraicClosure k`.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange` and
  `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.baseChange_iff`: being a unipotent-radical
  candidate is invariant under arbitrary field extensions.
* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.mapBaseChangeHopfIdeal`: transport of radical
  candidates along an algebra equivalence of extension fields.
* `TauCeti.FiniteTypeCommHopfAlgCat.mapBaseChangeHopfIdeal_unipotentRadicalDefiningIdeal`:
  algebra equivalences of extension fields preserve the unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff`:
  descent criterion for the unipotent radical along an arbitrary field extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal`: the
  unipotent radical commutes with every separable algebraic extension `K / k`.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIso`: the induced coordinate
  Hopf-algebra isomorphism `R_u(G_K) ≅ R_u(G)_K` along a separable algebraic extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsUnipotentRadicalBaseChangeIso`: the induced
  coordinate Hopf-algebra isomorphism `(G ⧸ R_u(G))_K ≅ G_K ⧸ R_u(G_K)` along a separable
  algebraic extension.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 19.9 and Remark 17.94(a).
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §11.21.
-/

public section

open CategoryTheory

namespace TauCeti

universe u

noncomputable section

namespace HopfIdeal.IsUnipotentRadicalCandidate

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}

/-- The unipotent-radical candidate conditions descend under arbitrary field extension. -/
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

/-- Transport along a `k`-algebra equivalence of extension fields preserves unipotent-radical
candidates. -/
theorem mapBaseChangeHopfIdeal {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂] (e : K₁ ≃ₐ[k] K₂)
    {I : HopfIdeal K₁ (FiniteTypeCommHopfAlgCat.baseChange (K := K₁) H)}
    (hI : IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.baseChange (K := K₁) H) I) :
    IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.baseChange (K := K₂) H)
      (CommHopfAlgCat.mapBaseChangeHopfIdeal e I) := by
  let _ : Algebra K₁ K₂ := e.toRingHom.toAlgebra
  let _ : IsScalarTower k K₁ K₂ :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (e.commutes c).symm
  have heq : CommHopfAlgCat.mapBaseChangeHopfIdeal e I =
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K₂) I).comapOfSurjective
        (FiniteTypeCommHopfAlgCat.toBialgHom
          (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := K₁) k K₂ H).symm.hom)
        (ConcreteCategory.bijective_of_isIso
          (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := K₁) k K₂ H).symm.hom).2 := by
    rw [CommHopfAlgCat.mapBaseChangeHopfIdeal_eq_comapOfSurjective_baseChangeTowerIso e
      (fun _ ↦ rfl)]
    ext x
    simp only [HopfIdeal.mem_comapOfSurjective, Iso.symm_hom,
      FiniteTypeCommHopfAlgCat.toBialgHom, FiniteTypeCommHopfAlgCat.baseChangeTowerIso_inv_hom]
  rw [heq]
  exact (hI.baseChange (K := K₂)).comapOfIso
    (FiniteTypeCommHopfAlgCat.baseChangeTowerIso (E := K₁) k K₂ H).symm

/-- Transport along a `k`-algebra equivalence of extension fields preserves and reflects
unipotent-radical candidates. -/
@[simp]
theorem mapBaseChangeHopfIdeal_iff {K₁ K₂ : Type u} [Field K₁] [Field K₂]
    [Algebra k K₁] [Algebra k K₂] (e : K₁ ≃ₐ[k] K₂)
    {I : HopfIdeal K₁ (FiniteTypeCommHopfAlgCat.baseChange (K := K₁) H)} :
    IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.baseChange (K := K₂) H)
        (CommHopfAlgCat.mapBaseChangeHopfIdeal e I) ↔
      IsUnipotentRadicalCandidate (FiniteTypeCommHopfAlgCat.baseChange (K := K₁) H) I := by
  refine ⟨fun h ↦ ?_, mapBaseChangeHopfIdeal e⟩
  simpa only [CommHopfAlgCat.mapBaseChangeHopfIdeal_symm_mapBaseChangeHopfIdeal] using
    h.mapBaseChangeHopfIdeal e.symm

end HopfIdeal.IsUnipotentRadicalCandidate

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k]

/-- A `k`-algebra equivalence between extension fields transports the defining ideal of the
unipotent radical to the defining ideal of the unipotent radical over the target field. -/
@[simp]
theorem mapBaseChangeHopfIdeal_unipotentRadicalDefiningIdeal
    {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra k K₁] [Algebra k K₂]
    (e : K₁ ≃ₐ[k] K₂) (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.mapBaseChangeHopfIdeal e
        (unipotentRadicalDefiningIdeal (baseChange (K := K₁) H)) =
      unipotentRadicalDefiningIdeal (baseChange (K := K₂) H) := by
  apply le_antisymm
  · have hle : unipotentRadicalDefiningIdeal (baseChange (K := K₁) H) ≤
        CommHopfAlgCat.mapBaseChangeHopfIdeal e.symm
          (unipotentRadicalDefiningIdeal (baseChange (K := K₂) H)) :=
      unipotentRadicalDefiningIdeal_le _ _
        ((isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal _).mapBaseChangeHopfIdeal
          e.symm)
    simpa only [CommHopfAlgCat.mapBaseChangeHopfIdeal_mapBaseChangeHopfIdeal_symm] using
      CommHopfAlgCat.mapBaseChangeHopfIdeal_mono e hle
  · exact unipotentRadicalDefiningIdeal_le _ _
      ((isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal _).mapBaseChangeHopfIdeal e)

/-- **Descent criterion for the unipotent radical.** Along an arbitrary field extension `K / k`,
the unipotent radical of `G_K` descends to some closed `k`-subgroup of `G` if and only if it is
the base change of the `k`-unipotent radical of `G`. -/
theorem exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff
    {K : Type u} [Field K] [Algebra k K] (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (∃ J : HopfIdeal k H,
        CommHopfAlgCat.baseChangeHopfIdeal (K := K) J =
          unipotentRadicalDefiningIdeal (baseChange (K := K) H)) ↔
      CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
        unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  refine ⟨fun ⟨J, hJ⟩ ↦ ?_, fun h ↦ ⟨unipotentRadicalDefiningIdeal H, h⟩⟩
  refine le_antisymm ?_ (unipotentRadicalDefiningIdeal_baseChange_le H)
  rw [← hJ]
  apply CommHopfAlgCat.baseChangeHopfIdeal_mono
  exact unipotentRadicalDefiningIdeal_le H J <|
    HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange <|
      hJ.symm ▸ isUnipotentRadicalCandidate_unipotentRadicalDefiningIdeal (baseChange (K := K) H)

/-- Along a Galois extension `L / k`, possibly infinite, the unipotent radical commutes with
scalar extension. -/
private theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois
    {L : Type u} [Field L] [Algebra k L] [IsGalois k L]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := L) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := L) H) := by
  rw [← exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff]
  obtain ⟨J, hJ, -⟩ :=
    (CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff_mapBaseChangeHopfIdeal
      (unipotentRadicalDefiningIdeal (baseChange (K := L) H))).mpr
    (fun σ ↦ mapBaseChangeHopfIdeal_unipotentRadicalDefiningIdeal σ H)
  exact ⟨J, hJ⟩

/-- **Separable algebraic base change of the unipotent radical.** For every separable algebraic
extension `K / k` (finite or infinite), formation of the unipotent radical commutes with scalar
extension to `K`. In particular, over a perfect field `k`, the native `k`-unipotent radical
base-changes to the geometric unipotent radical over `AlgebraicClosure k`. -/
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  let L := SeparableClosure k
  let ι : K →ₐ[k] L := IsSepClosed.lift
  let _ : Algebra K L := ι.toAlgebra
  let _ : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq fun x ↦ (ι.commutes x).symm
  have _ : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := L)
  rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (L := L) H,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (L := L) (baseChange (K := K) H),
    ← comapOfSurjective_unipotentRadicalDefiningIdeal (baseChangeTowerIso (E := K) k L H)]
  ext x
  simp only [HopfIdeal.mem_comapOfSurjective, toBialgHom, baseChangeTowerIso_hom_hom]

/-- Along a separable algebraic extension `K / k`, the unipotent radical is trivial over `K` if
and only if it is trivial over `k`. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) =
        HopfIdeal.augmentation K (baseChange (K := K) H) ↔
      unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact CommHopfAlgCat.baseChangeHopfIdeal_injective.eq_iff

/-- **Base-change isomorphism for the unipotent radical.** For every separable algebraic extension
`K / k`, the coordinate Hopf algebra of the unipotent radical of `G_K` is canonically isomorphic to
the base change of the coordinate Hopf algebra of the unipotent radical of `G`. -/
def unipotentRadicalBaseChangeIso
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadical (baseChange (K := K) H) ≅
      baseChange (K := K) (unipotentRadical H) :=
  eqToIso (congrArg (quotient (baseChange (K := K) H))
    (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H).symm) ≪≫
      ObjectProperty.isoMk _
        (CommHopfAlgCat.quotientBaseChangeIso (K := K) (unipotentRadicalDefiningIdeal H))

/-- The unipotent-radical base-change isomorphism commutes with the coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).hom =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) := by
  apply hom_ext
  have hobj : (unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
      (unipotentRadicalBaseChangeIso (K := K) H).hom).hom =
      (baseChangeMap (K := K) (unipotentRadicalCoordinateMap H)).hom := by
    rw [unipotentRadicalBaseChangeIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
      unipotentRadicalCoordinateMap_def, unipotentRadicalCoordinateMap_def,
      mkQuotient_comp_eqToHom (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H)]
    exact CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom (K := K)
      (unipotentRadicalDefiningIdeal H)
  exact congrArg _root_.CommHopfAlgCat.Hom.hom hobj

/-- The inverse unipotent-radical base-change isomorphism commutes with the coordinate quotient
maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_inv
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).inv =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) := by
  rw [← unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- **Base-change isomorphism for the quotient by the unipotent radical.** For every separable
algebraic extension `K / k`, the scalar extension of the coinvariant Hopf algebra `O(G)^{R_u(G)}`
is canonically isomorphic to `O(G_K)^{R_u(G_K)}`, commuting with the quotient coordinate
inclusions. Contravariantly, `(G ⧸ R_u(G))_K ≅ G_K ⧸ R_u(G_K)`. -/
def coinvariantsUnipotentRadicalBaseChangeIso
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  have heq := baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H
  let hbase := CommHopfAlgCat.isNormal_baseChangeHopfIdeal (K := K)
    (isNormal_unipotentRadicalDefiningIdeal H)
  let htarget := isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)
  let e : CommHopfAlgCat.coinvariants hbase ≅ CommHopfAlgCat.coinvariants htarget :=
    { hom := CommHopfAlgCat.liftCoinvariants htarget (CommHopfAlgCat.coinvariantsι hbase)
        (heq ▸ CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hbase)
      inv := CommHopfAlgCat.liftCoinvariants hbase (CommHopfAlgCat.coinvariantsι htarget)
        (heq.symm ▸ CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le htarget)
      hom_inv_id :=
        (CommHopfAlgCat.liftCoinvariants_unique hbase (CommHopfAlgCat.coinvariantsι hbase)
          (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hbase) _
          (by rw [Category.assoc, CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι,
            CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι])).trans
        (CommHopfAlgCat.liftCoinvariants_unique hbase (CommHopfAlgCat.coinvariantsι hbase)
          (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hbase) (𝟙 _)
          (Category.id_comp _)).symm
      inv_hom_id :=
        (CommHopfAlgCat.liftCoinvariants_unique htarget (CommHopfAlgCat.coinvariantsι htarget)
          (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le htarget) _
          (by rw [Category.assoc, CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι,
            CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι])).trans
        (CommHopfAlgCat.liftCoinvariants_unique htarget (CommHopfAlgCat.coinvariantsι htarget)
          (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le htarget) (𝟙 _)
          (Category.id_comp _)).symm }
  exact CommHopfAlgCat.coinvariantsBaseChangeIso (K := K)
    (isNormal_unipotentRadicalDefiningIdeal H) ≪≫ e

/-- The quotient base-change isomorphism commutes with the coinvariant coordinate inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) H).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) := by
  dsimp only [coinvariantsUnipotentRadicalBaseChangeIso]
  rw [Iso.trans_hom, Category.assoc, CommHopfAlgCat.liftCoinvariants_comp_coinvariantsι,
    CommHopfAlgCat.coinvariantsBaseChangeIso_hom_comp_coinvariantsι]

/-- The inverse quotient base-change isomorphism commutes with the coinvariant coordinate
inclusions. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_inv_comp_baseChangeMap
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) H).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [← coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι, Iso.inv_hom_id_assoc]

end FiniteTypeCommHopfAlgCat

end

end TauCeti
