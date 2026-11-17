/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.HopfBaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.BaseChange
import Mathlib.FieldTheory.Normal.Closure
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Descent
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Descent
import TauCeti.Algebra.AlgebraicGroup.Unipotent.Radical.Isomorphism

/-!
# Separable and Galois descent of the unipotent radical

For a finite-type affine group over a field `k` and any field extension `K / k`, the three
conditions defining a unipotent-radical candidate — normality, geometric connectedness, and smooth
geometric unipotence of the closed subgroup — descend from `K ⊗[k] H` to `H`. Consequently, the
`K`-unipotent radical of `K ⊗[k] H` descends to a Hopf ideal over `k` if and only if it coincides
with the base change of the `k`-unipotent radical of `H`.

Along a surjective field map `k → K`, every Hopf ideal descends, so the unipotent radical commutes
with scalar extension. Twisting the scalar tower by any `k`-algebra equivalence `φ : K ≃ₐ[k] E`
shows that `φ ⊗ id` transports the unipotent radical of `K ⊗[k] H` to that of `E ⊗[k] H`. Taking
`E = K` gives stability of the unipotent radical under `Gal(L / k)` for any Galois extension
`L / k`, so Galois descent of Hopf ideals (`existsUnique_baseChangeHopfIdeal_eq_iff`) identifies
the `L`-unipotent radical with the base change of the `k`-unipotent radical.

For a general separable algebraic extension `K / k`, embedding `K` into its normal closure `L`
inside `AlgebraicClosure K` yields a Galois extension `L / k`. Applying the Galois case to `L / k`
sandwiches the base change of the `K`-unipotent radical to `L` between two equal ideals, and
faithful-flat injectivity of `baseChangeHopfIdeal` along `K → L` gives
`baseChangeHopfIdeal (unipotentRadicalDefiningIdeal H) = unipotentRadicalDefiningIdeal (K ⊗[k] H)`.
In particular, over a perfect field `k`, the `k`-unipotent radical base-changes to the geometric
unipotent radical over `AlgebraicClosure k`.

This file also packages the resulting base-change comparisons for the coordinate Hopf algebra of the
unipotent radical, its closed subgroup scheme, and the normal affine quotient `G ⧸ R_{u,k}(G)`.

The candidate-descent and surjective-extension pattern parallels
`TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Descent`, extended here to Galois and separable
algebraic extensions via `TauCeti.CommHopfAlgCat.existsUnique_baseChangeHopfIdeal_eq_iff`.

## Main declarations

* `TauCeti.HopfIdeal.IsUnipotentRadicalCandidate.of_baseChange` and `.baseChange_iff`:
  unipotent-radical candidatehood is reflected by and invariant under arbitrary field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    exists_baseChangeHopfIdeal_eq_unipotentRadicalDefiningIdeal_iff`:
  the unipotent radical after field extension descends to `k` exactly when it equals the base change
  of the `k`-unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_surjective`:
  the unipotent radical commutes with surjective field extensions.
* `TauCeti.FiniteTypeCommHopfAlgCat.map_mem_unipotentRadicalDefiningIdeal_baseChange_iff`:
  `k`-algebra equivalences of extension fields preserve the base-changed unipotent radical.
* `TauCeti.FiniteTypeCommHopfAlgCat.baseChangeHopfIdeal_unipotentRadicalDefiningIdeal` and
  `unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff`: the unipotent radical (and its
  triviality) commutes with every separable algebraic field extension.
* `TauCeti.FiniteTypeCommHopfAlgCat.unipotentRadicalBaseChangeIso`: the induced coordinate
  isomorphism on unipotent radicals, compatible with `unipotentRadicalCoordinateMap`.
* `TauCeti.FiniteTypeCommHopfAlgCat.
    mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal`:
  the closed subgroup scheme of the unipotent radical commutes with separable algebraic base change.
* `TauCeti.FiniteTypeCommHopfAlgCat.coinvariantsUnipotentRadicalBaseChangeIso`: the coordinate
  isomorphism identifying `(G ⧸ R_{u,k}(G))_K` with `G_K ⧸ R_{u,K}(G_K)` along separable algebraic
  extensions.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 6.42, §§6.45–6.46, and Propositions 19.9
  and 19.11.
* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, 2nd ed. (2015), Proposition 1.1.9.
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §§AG.14 and 11.21.
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

/-- The unipotent-radical candidate conditions descend along an arbitrary field extension. -/
theorem of_baseChange
    (hI : IsUnipotentRadicalCandidate
      (FiniteTypeCommHopfAlgCat.baseChange (K := K) H)
      (CommHopfAlgCat.baseChangeHopfIdeal (K := K) I)) :
    IsUnipotentRadicalCandidate H I := by
  let qIso := CommHopfAlgCat.quotientBaseChangeIso (K := K) I
  refine IsUnipotentRadicalCandidate.mk
    (CommHopfAlgCat.isNormal_of_baseChangeHopfIdeal hI.isNormal) ?_ ?_
  · apply geometricallyConnectedCommHopfAlgProperty.of_baseChange k K
      (FiniteTypeCommHopfAlgCat.quotient H I).obj
    exact (geometricallyConnectedCommHopfAlgProperty K).prop_of_iso qIso hI.geometricallyConnected
  · apply smoothUnipotentCommHopfAlgProperty.of_baseChange (K := K)
      (FiniteTypeCommHopfAlgCat.quotient H I)
    exact (smoothUnipotentCommHopfAlgProperty K).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty K) qIso) hI.smoothUnipotent

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

/-- **The unipotent radical commutes with separable algebraic field extensions.**

Along any separable algebraic extension `K / k` (including Galois extensions, separable closures,
and algebraic closures of perfect fields), the base change of the `k`-unipotent radical is the
`K`-unipotent radical of the base-changed group. -/
@[simp]
theorem baseChangeHopfIdeal_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H) =
      unipotentRadicalDefiningIdeal (baseChange (K := K) H) := by
  have _ : IsAlgClosure k (AlgebraicClosure K) :=
    ⟨AlgebraicClosure.isAlgClosed K, Algebra.IsAlgebraic.trans k K (AlgebraicClosure K)⟩
  let L := IntermediateField.normalClosure k K (AlgebraicClosure K)
  let t := baseChangeTowerIso (E := K) k L H
  have hcomp :
      CommHopfAlgCat.baseChangeHopfIdeal (K := L)
          (CommHopfAlgCat.baseChangeHopfIdeal (K := K) (unipotentRadicalDefiningIdeal H)) =
        unipotentRadicalDefiningIdeal (baseChange (K := L) (baseChange (K := K) H)) := by
    rw [CommHopfAlgCat.baseChangeHopfIdeal_baseChangeHopfIdeal (E := K) k L
        (unipotentRadicalDefiningIdeal H),
      baseChangeHopfIdeal_unipotentRadicalDefiningIdeal_of_isGalois (K := L) H,
      ← comapOfSurjective_unipotentRadicalDefiningIdeal t]
    ext z
    simp [HopfIdeal.mem_comapOfSurjective, t, baseChangeTowerIso_hom_hom, toBialgHom]
  apply CommHopfAlgCat.baseChangeHopfIdeal_injective (K := L)
  apply le_antisymm
  · rw [hcomp]
    exact unipotentRadicalDefiningIdeal_baseChange_le (baseChange (K := K) H)
  · exact CommHopfAlgCat.baseChangeHopfIdeal_mono (unipotentRadicalDefiningIdeal_baseChange_le H)

/-- Triviality of the unipotent radical is invariant under separable algebraic field extensions. -/
@[simp]
theorem unipotentRadicalDefiningIdeal_baseChange_eq_augmentation_iff
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalDefiningIdeal (baseChange (K := K) H) =
        HopfIdeal.augmentation K (baseChange (K := K) H) ↔
      unipotentRadicalDefiningIdeal H = HopfIdeal.augmentation k H := by
  rw [← baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H,
    ← CommHopfAlgCat.baseChangeHopfIdeal_augmentation]
  exact (CommHopfAlgCat.baseChangeHopfIdeal_injective (K := K)).eq_iff

/-- Along a separable algebraic field extension `K / k`, the coordinate Hopf algebra of the
`K`-unipotent radical of `K ⊗[k] H` is canonically isomorphic to the base change of the
`k`-unipotent radical of `H`. -/
def unipotentRadicalBaseChangeIso (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadical (baseChange (K := K) H) ≅
      baseChange (K := K) (unipotentRadical H) :=
  { hom := quotientMapOfLe (baseChange (K := K) H)
      (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H).ge
    inv := quotientMapOfLe (baseChange (K := K) H)
      (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H).le } ≪≫
    ObjectProperty.isoMk _
      (CommHopfAlgCat.quotientBaseChangeIso (K := K) (unipotentRadicalDefiningIdeal H))

/-- The separable base-change isomorphism on unipotent radicals commutes with the coordinate
quotient maps. -/
@[reassoc (attr := simp)]
theorem unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    unipotentRadicalCoordinateMap (baseChange (K := K) H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).hom =
      baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) := by
  apply ObjectProperty.hom_ext
  dsimp only [unipotentRadicalBaseChangeIso]
  rw [unipotentRadicalCoordinateMap_def, unipotentRadicalCoordinateMap_def,
    Iso.trans_hom, ObjectProperty.isoMk_hom, ← Category.assoc]
  exact (congrArg (· ≫ (CommHopfAlgCat.quotientBaseChangeIso (K := K)
    (unipotentRadicalDefiningIdeal H)).hom)
      (CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe
        (CommHopfAlgCat.baseChange (K := K) H.obj)
        (baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H).ge)).trans
          (CommHopfAlgCat.mkQuotient_comp_quotientBaseChangeIso_hom (K := K)
            (unipotentRadicalDefiningIdeal H))

/-- The inverse separable base-change isomorphism on unipotent radicals commutes with the
coordinate quotient maps. -/
@[reassoc (attr := simp)]
theorem baseChangeMap_unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_inv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    baseChangeMap (K := K) (unipotentRadicalCoordinateMap H) ≫
        (unipotentRadicalBaseChangeIso (K := K) H).inv =
      unipotentRadicalCoordinateMap (baseChange (K := K) H) := by
  rw [← cancel_mono (unipotentRadicalBaseChangeIso (K := K) H).hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id,
    unipotentRadicalCoordinateMap_comp_unipotentRadicalBaseChangeIso_hom]

/-- **Scheme-theoretic base change of the unipotent radical.** Along a separable algebraic
extension `K / k`, the base change of the closed subgroup scheme cut out by the `k`-unipotent
radical identifies with the closed subgroup scheme cut out by the `K`-unipotent radical of the
base-changed group. -/
theorem mapIso_baseChange_quotientClosedSubgroup_unipotentRadicalDefiningIdeal
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    ClosedSubgroupScheme.mapIso
        (AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (S := K) H.obj)
        ((CommHopfAlgCat.quotientClosedSubgroup H.obj
          (unipotentRadicalDefiningIdeal H)).baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))) =
      CommHopfAlgCat.quotientClosedSubgroup (baseChange (K := K) H).obj
        (unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [CommHopfAlgCat.mapIso_baseChange_quotientClosedSubgroup,
    baseChangeHopfIdeal_unipotentRadicalDefiningIdeal]

/-- Along a separable algebraic extension `K / k`, the scalar extension of the normal coinvariant
Hopf algebra of the `k`-unipotent radical is canonically isomorphic in `CommHopfAlgCat K` to the
normal coinvariant Hopf algebra of the `K`-unipotent radical of the base-changed group. -/
def coinvariantsUnipotentRadicalBaseChangeIso
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    CommHopfAlgCat.baseChange (K := K)
        (CommHopfAlgCat.coinvariants (isNormal_unipotentRadicalDefiningIdeal H)) ≅
      CommHopfAlgCat.coinvariants
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) :=
  let hR := isNormal_unipotentRadicalDefiningIdeal H
  let hRbase := CommHopfAlgCat.isNormal_baseChangeHopfIdeal (K := K) hR
  let hRK := isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)
  let heq := baseChangeHopfIdeal_unipotentRadicalDefiningIdeal (K := K) H
  CommHopfAlgCat.coinvariantsBaseChangeIso (K := K) hR ≪≫
    { hom := CommHopfAlgCat.liftCoinvariants hRK (CommHopfAlgCat.coinvariantsι hRbase)
        (heq ▸ CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRbase)
      inv := CommHopfAlgCat.liftCoinvariants hRbase (CommHopfAlgCat.coinvariantsι hRK)
        (heq.symm ▸ CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRK)
      hom_inv_id := (CommHopfAlgCat.liftCoinvariants_unique hRbase
        (CommHopfAlgCat.coinvariantsι hRbase)
        (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRbase) _ (by simp)).trans
          (CommHopfAlgCat.liftCoinvariants_unique hRbase
            (CommHopfAlgCat.coinvariantsι hRbase)
            (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRbase) (𝟙 _)
            (Category.id_comp _)).symm
      inv_hom_id := (CommHopfAlgCat.liftCoinvariants_unique hRK
        (CommHopfAlgCat.coinvariantsι hRK)
        (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRK) _ (by simp)).trans
          (CommHopfAlgCat.liftCoinvariants_unique hRK
            (CommHopfAlgCat.coinvariantsι hRK)
            (CommHopfAlgCat.kernelHopfIdeal_coinvariantsι_le hRK) (𝟙 _)
            (Category.id_comp _)).symm }

/-- The separable base-change isomorphism on `G ⧸ R_{u,k}(G)` commutes with the coordinate
inclusions of the coinvariants. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) H).hom ≫
        CommHopfAlgCat.coinvariantsι
          (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) =
      CommHopfAlgCat.baseChangeMap (K := K)
        (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) := by
  simp [coinvariantsUnipotentRadicalBaseChangeIso]

/-- The inverse separable base-change isomorphism on `G ⧸ R_{u,k}(G)` also commutes with the
coordinate inclusions of the coinvariants. -/
@[reassoc (attr := simp)]
theorem coinvariantsUnipotentRadicalBaseChangeIso_inv_comp_baseChangeMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (coinvariantsUnipotentRadicalBaseChangeIso (K := K) H).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K)
          (CommHopfAlgCat.coinvariantsι (isNormal_unipotentRadicalDefiningIdeal H)) =
      CommHopfAlgCat.coinvariantsι
        (isNormal_unipotentRadicalDefiningIdeal (baseChange (K := K) H)) := by
  rw [← coinvariantsUnipotentRadicalBaseChangeIso_hom_comp_coinvariantsι H,
    Iso.inv_hom_id_assoc]

end Separable

end FiniteTypeCommHopfAlgCat

end

end TauCeti
