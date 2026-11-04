/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Inertia
import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# Unramified places in composita and Galois closures

A place `P` of `F / k` is **unramified** in an algebraic extension `F' / k'` when some place of
`F'` lies above it and every place `P'` of `F'` above it has ramification index
`e(P' ∣ P) = 1` and separable residue extension `F'_{P'} / F_P`. Over a perfect residue field
the separability condition is automatic, and this is Stichtenoth's notion (Definition 3.1.13).
In general it cannot be dropped. Over `𝔽_p(s)(t)`, the Artin–Schreier extensions
`y^p - y = s t^{-p}` and `y^p - y = (s + t) t^{-p}` both have `e = 1` at `t = 0`, with residue
extension `𝔽_p(s^{1/p}) / 𝔽_p(s)`. Their compositum contains a root of `y^p - y = -t^{1 - p}`,
so it is ramified there.

In a finite Galois extension `M / F`, the restriction of a place `Q` of `M` to an intermediate
field `E` is unramified over `F` exactly when `E` lies in the inertia field of `Q`
(`TauCeti.Place.le_inertiaField_iff`). This file draws the two consequences of Stichtenoth's
Corollary 3.9.3, for arbitrary residue fields. The fixing subgroup of a compositum is the
intersection of the fixing subgroups, so a place is unramified in `E₁ E₂` exactly when it is
unramified in `E₁` and in `E₂`. The Galois group permutes the places above `P` and carries their
inertia fields along (`TauCeti.Place.inertiaField_smul`), so a place unramified in `E` is
unramified in every conjugate of `E`, hence in the Galois closure of `E`, which those conjugates
generate. Every finite separable extension of `F` embeds into a finite Galois one, and
unramifiedness is invariant under isomorphism over `F`
(`TauCeti.Place.isUnramified_iff_of_algEquiv`), so these statements cover the composita and
Galois closures of finite separable extensions. This transport through a finite Galois overfield
follows the proof of `TauCeti.Place.isSplitCompletely_sup_iff` in
`TauCeti/FieldTheory/FunctionField/Place/Extension/Splitting/Compositum.lean`.

Ramification indices multiply in a tower `F₀ ⊆ F₁ ⊆ F₂`, and residue extensions are separable for
the whole tower exactly when they are for both steps (`TauCeti.Place.ramificationIdx_restrict_mul`
and its companions in `TauCeti/FieldTheory/FunctionField/Place/Extension/Tower.lean`). So a place
of `F₀` is unramified in `F₂` exactly when it is unramified in `F₁` and every place of `F₁` above
it is unramified in `F₂`. The **branch places** of an extension are the places that are not
unramified in it; for finite maps of curves `f : X → Y` and `g : Y → Z` the tower statement reads
`Branch(g ∘ f) = g(Branch f) ∪ Branch g`.

## Main definitions

* `TauCeti.Place.IsUnramified`: a place is unramified in an extension, with the characteristic
  property `TauCeti.Place.isUnramified_iff` and the projections
  `IsUnramified.exists_restrict_eq`, `IsUnramified.ramificationIdx_eq_one` and
  `IsUnramified.isSeparable`.
* `TauCeti.Place.branchPlaces`: the places of the base field that are not unramified in an
  extension.

## Main results

* `TauCeti.Place.not_isUnramified_of_degree_eq_one`: a place of degree one is not unramified once
  the constants contain a purely inseparable element outside `k`, whatever the ramification
  indices are.
* `TauCeti.Place.isUnramified_iff_of_algEquiv`: unramifiedness is invariant under an isomorphism
  of the upstairs field over the base field.
* `TauCeti.Place.isUnramified_tower_iff`: **a place is unramified in a tower exactly when it is
  unramified in the lower step and every place above it is unramified in the upper step**.
* `TauCeti.Place.branchPlaces_eq_image_union`: the branch places of a tower are the branch places
  of the lower step together with the places below the branch places of the upper step.
* `TauCeti.Place.isUnramified_iff_forall_le_inertiaField`: a place is unramified in `E` exactly
  when `E` lies in the inertia field of every place of `M` above it.
* `TauCeti.Place.isUnramified_sup_iff`: **a place is unramified in a compositum of finite
  separable extensions exactly when it is unramified in both constituents**.
* `TauCeti.Place.isUnramified_normalClosure_iff`: **a place is unramified in the Galois closure
  of `E` exactly when it is unramified in `E`**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 3.1.6, Definition 3.1.13 and Corollary 3.9.3.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

section Definition

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [Algebra.IsIntegral F F']

/-- A place `P` of `F / k` is **unramified** in `F' / k'` when it has a place `P'` of `F'`
above it, and every such `P'` has ramification index `e(P' ∣ P) = 1` and a separable residue
extension `F'_{P'} / F_P` (Stichtenoth, Definition 3.1.13, where the residue extensions are
separable because the constant field is perfect). The existence clause keeps the predicate from
holding vacuously when no place of `F' / k'` lies above `P`, for instance when `k' = F' = F`. -/
def IsUnramified (P : Place k F) : Prop :=
  (∃ P' : Place k' F', P'.restrict k F = P) ∧
    ∀ P' : Place k' F', P'.restrict k F = P →
      ramificationIdx F P' = 1 ∧
        Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField

/-- The characteristic property of an unramified place. -/
theorem isUnramified_iff (P : Place k F) :
    P.IsUnramified (k' := k') (F' := F') ↔
      (∃ P' : Place k' F', P'.restrict k F = P) ∧
        ∀ P' : Place k' F', P'.restrict k F = P →
          ramificationIdx F P' = 1 ∧
            Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField :=
  Iff.rfl

/-- An unramified place has a place above it. -/
theorem IsUnramified.exists_restrict_eq {P : Place k F}
    (hP : P.IsUnramified (k' := k') (F' := F')) :
    ∃ P' : Place k' F', P'.restrict k F = P :=
  hP.1

/-- A place above an unramified place has ramification index one. -/
theorem IsUnramified.ramificationIdx_eq_one {P : Place k F}
    (hP : P.IsUnramified (k' := k') (F' := F')) {P' : Place k' F'}
    (hP' : P'.restrict k F = P) :
    ramificationIdx F P' = 1 :=
  (hP.2 P' hP').1

/-- A place above an unramified place has a separable residue extension. -/
theorem IsUnramified.isSeparable {P : Place k F}
    (hP : P.IsUnramified (k' := k') (F' := F')) {P' : Place k' F'}
    (hP' : P'.restrict k F = P) :
    Algebra.IsSeparable (P'.restrict k F).ResidueField P'.ResidueField :=
  (hP.2 P' hP').2

variable (k' F') in
/-- The **branch places** of `F' / k'` over `F / k`: the places of `F` that are not unramified in
`F'`. When every place of `F` lies below a place of `F'`, as for a finite extension of function
fields, these are the places of `F` lying below a place of `F'` with ramification index greater
than one or with an inseparable residue extension. When moreover the residue fields have
characteristic zero, only the ramification index matters. -/
def branchPlaces : Set (Place k F) :=
  {P | ¬P.IsUnramified (k' := k') (F' := F')}

@[simp]
theorem mem_branchPlaces_iff {P : Place k F} :
    P ∈ branchPlaces k' F' ↔ ¬P.IsUnramified (k' := k') (F' := F') :=
  Iff.rfl

/-- **A rational place is not unramified in a purely inseparable extension of constants**: if `P`
has degree one and `k'` contains `α ∉ k` with `α ^ (q ^ n) ∈ k`, then `P` is not unramified in
`F' / k'`, whatever the ramification indices are. -/
theorem not_isUnramified_of_degree_eq_one {P : Place k F} (hP : P.degree = 1) (q : ℕ)
    [ExpChar k q] {α : k'} (hα : α ∉ (algebraMap k k').range) {n : ℕ}
    (hn : α ^ q ^ n ∈ (algebraMap k k').range) :
    ¬ P.IsUnramified (k' := k') (F' := F') := by
  intro hU
  obtain ⟨P', hP'⟩ := hU.exists_restrict_eq
  exact not_isSeparable_residueField_of_degree_eq_one P' (hP' ▸ hP) q hα hn
    (hU.isSeparable hP')

end Definition

section Equiv

variable {k F L L' : Type*} [Field k] [Field F] [Field L] [Field L']
variable [Algebra k F] [Algebra k L] [Algebra k L'] [Algebra F L] [Algebra F L']
variable [IsScalarTower k F L] [IsScalarTower k F L']
variable [Algebra.IsIntegral F L] [Algebra.IsIntegral F L']

/-- Residues of equal places agree along the cast between their residue fields. -/
private theorem cast_residue {Q₁ Q₂ : Place k F} (hQ : Q₁ = Q₂) (x : Q₁.integers)
    (y : Q₂.integers) (hy : (y : F) = x) :
    RingEquiv.cast (R := fun R : Place k F ↦ R.ResidueField) hQ
        (IsLocalRing.residue Q₁.integers x) = IsLocalRing.residue Q₂.integers y := by
  subst hQ
  obtain rfl : y = x := Subtype.ext hy
  rfl

/-- Transport along an isomorphism `e : L ≃ L'` over `F` preserves both conditions defining an
unramified place, place by place. -/
private theorem unramified_map_iff (e : L ≃ₐ[F] L') (Q : Place k L) :
    (ramificationIdx F (Q.map (e.restrictScalars k)) = 1 ∧
      Algebra.IsSeparable ((Q.map (e.restrictScalars k)).restrict k F).ResidueField
        (Q.map (e.restrictScalars k)).ResidueField) ↔
    (ramificationIdx F Q = 1 ∧
      Algebra.IsSeparable (Q.restrict k F).ResidueField Q.ResidueField) := by
  set e' := e.restrictScalars k
  have halg (x : F) : e'.symm (algebraMap F L' x) = algebraMap F L x := e.symm.commutes x
  have hrestrict : (Q.map e').restrict k F = Q.restrict k F := restrict_map_restrictScalars Q e
  have hram : ramificationIdx F (Q.map e') = ramificationIdx F Q :=
    ramificationIdx_eq_of_forall_ord_eq k F _ fun f ↦ by
      rw [ord_map, halg, hrestrict, ord_algebraMap_restrict k F Q]
  refine and_congr (by rw [hram]) (Algebra.IsSeparable.iff_of_equiv_equiv
    (RingEquiv.cast (R := fun R : Place k F ↦ R.ResidueField) hrestrict)
    (residueFieldEquivMap e' Q).symm.toRingEquiv (RingHom.ext fun x ↦ ?_))
  -- The residue fields below are identified by the cast along `hrestrict`, those above by `e`.
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_coe, RingHom.coe_coe,
    cast_residue hrestrict x ⟨x, hrestrict ▸ x.2⟩ rfl, AlgEquiv.coe_toRingEquiv,
    AlgEquiv.eq_symm_apply, IsLocalRing.ResidueField.algebraMap_residue,
    IsLocalRing.ResidueField.algebraMap_residue, residueFieldEquivMap_residue]
  congr 1
  rw [Subtype.ext_iff, coe_integersEquivMap, coe_algebraMap_integers, coe_algebraMap_integers]
  exact e.commutes (x : F)

/-- **Unramifiedness depends only on the extension**: it is invariant under an isomorphism of the
upstairs field over the base field. This moves a finite separable extension into a finite Galois
overfield without changing which places are unramified in it. -/
theorem isUnramified_iff_of_algEquiv (P : Place k F) (e : L ≃ₐ[F] L') :
    P.IsUnramified (k' := k) (F' := L) ↔ P.IsUnramified (k' := k) (F' := L') := by
  rw [isUnramified_iff, isUnramified_iff]
  refine ⟨fun ⟨⟨Q, hQ⟩, h⟩ ↦ ⟨⟨Q.map (e.restrictScalars k), ?_⟩, fun R hR ↦ ?_⟩,
    fun ⟨⟨R, hR⟩, h⟩ ↦ ⟨⟨R.map (e.symm.restrictScalars k), ?_⟩, fun Q hQ ↦ ?_⟩⟩
  · rwa [restrict_map_restrictScalars]
  · rw [← map_map_symm (e.restrictScalars k) R] at hR ⊢
    rw [restrict_map_restrictScalars] at hR
    exact (unramified_map_iff e _).mpr (h _ hR)
  · rwa [restrict_map_restrictScalars]
  · exact (unramified_map_iff e Q).mp (h _ (by rw [restrict_map_restrictScalars, hQ]))

end Equiv

section Tower

variable {k₀ k₁ k₂ F₀ F₁ F₂ : Type*}
variable [Field k₀] [Field k₁] [Field k₂] [Field F₀] [Field F₁] [Field F₂]
variable [Algebra k₀ k₁] [Algebra k₁ k₂] [Algebra k₀ k₂]
variable [Algebra F₀ F₁] [Algebra F₁ F₂] [Algebra F₀ F₂] [IsScalarTower F₀ F₁ F₂]
variable [Algebra k₀ F₀] [Algebra k₁ F₁] [Algebra k₂ F₂]
variable [Algebra k₀ F₁] [Algebra k₁ F₂] [Algebra k₀ F₂]
variable [IsScalarTower k₀ k₁ F₁] [IsScalarTower k₁ k₂ F₂]
variable [IsScalarTower k₀ F₀ F₁] [IsScalarTower k₁ F₁ F₂]
variable [IsScalarTower k₀ k₂ F₂] [IsScalarTower k₀ F₀ F₂]
-- `Algebra.IsIntegral F₀ F₂` follows from the other two (`Algebra.IsIntegral.trans`), but it is not
-- found by instance search, and restricting places of `F₂` to `F₀` needs it.
variable [Algebra.IsIntegral F₀ F₁] [Algebra.IsIntegral F₁ F₂] [Algebra.IsIntegral F₀ F₂]

/-- A place `P₂` of `F₂` is unramified over `F₀` exactly when it is unramified over `F₁` and its
restriction `P₂ ∩ F₁` is unramified over `F₀`, both for the ramification index and for the
separability of the residue extension. -/
private theorem unramified_restrict_iff (P₂ : Place k₂ F₂) :
    (ramificationIdx F₀ P₂ = 1 ∧
        Algebra.IsSeparable (P₂.restrict k₀ F₀).ResidueField P₂.ResidueField) ↔
      (ramificationIdx F₁ P₂ = 1 ∧
          Algebra.IsSeparable (P₂.restrict k₁ F₁).ResidueField P₂.ResidueField) ∧
        (ramificationIdx F₀ (P₂.restrict k₁ F₁) = 1 ∧
          Algebra.IsSeparable ((P₂.restrict k₁ F₁).restrict k₀ F₀).ResidueField
            (P₂.restrict k₁ F₁).ResidueField) := by
  rw [ramificationIdx_restrict_mul (k₁ := k₁) (F₁ := F₁) P₂, mul_eq_one]
  refine ⟨fun ⟨⟨h₂, h₁⟩, _⟩ ↦ ⟨⟨h₂, isSeparable_residueField_restrict_top k₀ F₀ P₂⟩,
    h₁, isSeparable_residueField_restrict_bot P₂⟩, fun ⟨⟨h₂, _⟩, h₁, _⟩ ↦
    ⟨⟨h₂, h₁⟩, isSeparable_residueField_restrict_trans (k₁ := k₁) (F₁ := F₁) P₂⟩⟩

/-- **Unramifiedness in a tower** (Stichtenoth, Proposition 3.1.6 and Definition 3.1.13): for a
tower `F₀ ⊆ F₁ ⊆ F₂`, a place `P` of `F₀` is unramified in `F₂` exactly when it is unramified in
`F₁` and every place of `F₁` above it is unramified in `F₂`.

The function-field hypothesis on `F₂` provides a place of `F₂` above every place of `F₁`. -/
theorem isUnramified_tower_iff [Algebra.IsIntegral k₁ k₂] (hF₂ : IsFunctionField k₂ F₂)
    (P : Place k₀ F₀) :
    P.IsUnramified (k' := k₂) (F' := F₂) ↔
      P.IsUnramified (k' := k₁) (F' := F₁) ∧
        ∀ P₁ : Place k₁ F₁, P₁.restrict k₀ F₀ = P → P₁.IsUnramified (k' := k₂) (F' := F₂) := by
  have hsurj := restrict_surjective (k := k₁) (F := F₁) (k' := k₂) (F' := F₂) hF₂
  have hrestrict (P₂ : Place k₂ F₂) : (P₂.restrict k₁ F₁).restrict k₀ F₀ = P₂.restrict k₀ F₀ :=
    restrict_restrict P₂
  refine ⟨fun ⟨⟨P₂, hP₂⟩, h⟩ ↦ ⟨⟨⟨P₂.restrict k₁ F₁, (hrestrict P₂).trans hP₂⟩, fun P₁ hP₁ ↦ ?_⟩,
    fun P₁ hP₁ ↦ ⟨hsurj P₁, fun P₂ hP₂ ↦ ?_⟩⟩, fun ⟨⟨⟨P₁, hP₁⟩, h₁⟩, h⟩ ↦ ?_⟩
  · obtain ⟨P₂, rfl⟩ := hsurj P₁
    exact ((unramified_restrict_iff P₂).1 (h P₂ ((hrestrict P₂).symm.trans hP₁))).2
  · subst hP₂
    exact ((unramified_restrict_iff P₂).1 (h P₂ ((hrestrict P₂).symm.trans hP₁))).1
  · obtain ⟨Q, hQ⟩ := (h P₁ hP₁).exists_restrict_eq
    refine ⟨⟨Q, (hrestrict Q).symm.trans (hQ ▸ hP₁)⟩, fun P₂ hP₂ ↦ ?_⟩
    have hP₂' : (P₂.restrict k₁ F₁).restrict k₀ F₀ = P := (hrestrict P₂).trans hP₂
    exact (unramified_restrict_iff P₂).2 ⟨(h _ hP₂').2 P₂ rfl, h₁ _ hP₂'⟩

/-- **Branch places of a tower**: for a tower `F₀ ⊆ F₁ ⊆ F₂`, the branch places of `F₂ / F₀` are
the branch places of `F₁ / F₀` together with the places of `F₀` below the branch places of
`F₂ / F₁`. For finite maps of curves `f : X → Y` and `g : Y → Z` this is the formula
`Branch(g ∘ f) = g(Branch f) ∪ Branch g`. -/
theorem branchPlaces_eq_image_union [Algebra.IsIntegral k₁ k₂] (hF₂ : IsFunctionField k₂ F₂) :
    branchPlaces (k := k₀) (F := F₀) k₂ F₂ =
      (fun P₁ : Place k₁ F₁ ↦ P₁.restrict k₀ F₀) '' branchPlaces k₂ F₂ ∪ branchPlaces k₁ F₁ := by
  ext P
  rw [mem_branchPlaces_iff, isUnramified_tower_iff (k₁ := k₁) (F₁ := F₁) hF₂]
  simp only [Set.mem_union, Set.mem_image, mem_branchPlaces_iff]
  grind

end Tower

universe u v w

variable {k : Type u} {F : Type v} {M : Type w}
variable [Field k] [Field F] [Field M] [Algebra k F] [Algebra k M] [Algebra F M]
variable [IsScalarTower k F M]

section Galois

variable [FiniteDimensional F M] [IsGalois F M]

/-- A place is unramified in an intermediate field `E` of a finite Galois extension `M` exactly
when `E` lies in the inertia field of every place of `M` above it. -/
theorem isUnramified_iff_forall_le_inertiaField
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := E) ↔
      ∀ Q : Place k M, Q.restrict k F = P → E ≤ inertiaField F Q := by
  rw [isUnramified_iff]
  refine ⟨fun h Q hQ ↦ (le_inertiaField_iff F Q E).mpr (h.2 _ ?_),
    fun h ↦ ⟨restrict_surjective_of_finiteDimensional hF (hF.finite_extension (E := E)) P,
      fun R hR ↦ ?_⟩⟩
  · simpa only [restrict_restrict] using hQ
  · obtain ⟨Q, rfl⟩ := restrict_surjective_of_finiteDimensional
      (hF.finite_extension (E := E)) (hF.finite_extension (E := M)) R
    exact (le_inertiaField_iff F Q E).mp (h Q (by simpa only [restrict_restrict] using hR))

/-- A place is unramified in the compositum of two intermediate fields of a finite Galois
extension exactly when it is unramified in each of them. -/
private theorem isUnramified_sup_iff_of_isGalois
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsUnramified (k' := k) (F' := E₁) ∧ P.IsUnramified (k' := k) (F' := E₂) := by
  simp only [isUnramified_iff_forall_le_inertiaField hF, sup_le_iff, ← forall_and]

end Galois

/-- A place is unramified in the compositum of two intermediate fields of a finite separable
extension exactly when it is unramified in each of them. -/
private theorem isUnramified_sup_iff_of_isSeparable [FiniteDimensional F M]
    [Algebra.IsSeparable F M]
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsUnramified (k' := k) (F' := E₁) ∧ P.IsUnramified (k' := k) (F' := E₂) := by
  -- Embed the whole ambient extension into its finite Galois closure, then transport all three
  -- intermediate fields along the same embedding.
  let A := AlgebraicClosure F
  let N := IntermediateField.normalClosure F M A
  have : Algebra.IsSeparable F N := by
    have (f : M →ₐ[F] A) : Algebra.IsSeparable F f.fieldRange :=
      AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    apply (le_separableClosure_iff F A N).mp
    dsimp only [N]
    rw [normalClosure_def]
    exact iSup_le fun f ↦ le_separableClosure F A f.fieldRange
  have : IsGalois F N := ⟨⟩
  let g : M →ₐ[F] N := (IsAlgClosed.lift (R := F) (S := M) (M := A)).codRestrict N.toSubalgebra
    fun x ↦ (IsAlgClosed.lift (R := F) (S := M) (M := A)).fieldRange_le_normalClosure ⟨x, rfl⟩
  rw [isUnramified_iff_of_algEquiv P ((E₁ ⊔ E₂).equivMap g),
    isUnramified_iff_of_algEquiv P (E₁.equivMap g),
    isUnramified_iff_of_algEquiv P (E₂.equivMap g), IntermediateField.map_sup]
  exact isUnramified_sup_iff_of_isGalois hF P (E₁.map g) (E₂.map g)

/-- **Unramifiedness in a compositum** (Stichtenoth, Corollary 3.9.3): a place is unramified in
the compositum of two finite separable intermediate fields of `M / F` exactly when it is
unramified in each of them. The ambient extension `M / F` need not be finite or separable. -/
@[simp]
theorem isUnramified_sup_iff
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E₁ E₂ : IntermediateField F M)
    [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    [Algebra.IsSeparable F E₁] [Algebra.IsSeparable F E₂] :
    P.IsUnramified (k' := k) (F' := ↥(E₁ ⊔ E₂)) ↔
      P.IsUnramified (k' := k) (F' := E₁) ∧ P.IsUnramified (k' := k) (F' := E₂) := by
  -- Pass to the separable compositum `L = E₁ ⊔ E₂`, viewing `E₁` and `E₂` as intermediate
  -- fields of `L`; there they generate all of `L`.
  set L := E₁ ⊔ E₂
  have h₁ : E₁ ≤ L := le_sup_left
  have h₂ : E₂ ≤ L := le_sup_right
  have hsup : E₁.restrict h₁ ⊔ E₂.restrict h₂ = ⊤ := by
    apply IntermediateField.lift_injective L
    rw [IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict, IntermediateField.lift_top]
  rw [isUnramified_iff_of_algEquiv P (IntermediateField.restrictAlgEquiv h₁),
    isUnramified_iff_of_algEquiv P (IntermediateField.restrictAlgEquiv h₂),
    ← isUnramified_iff_of_algEquiv P (IntermediateField.topEquiv (F := F) (E := L)), ← hsup]
  exact isUnramified_sup_iff_of_isSeparable hF P _ _

variable [FiniteDimensional F M] [IsGalois F M] in
/-- **Unramifiedness in a Galois closure** (Stichtenoth, Corollary 3.9.3): a place is unramified
in the normal closure of an intermediate field `E` of a finite Galois extension `M / F` exactly
when it is unramified in `E`. -/
@[simp]
theorem isUnramified_normalClosure_iff
    (hF : TauCeti.IsFunctionField k F) (P : Place k F) (E : IntermediateField F M) :
    P.IsUnramified (k' := k) (F' := IntermediateField.normalClosure F E M) ↔
      P.IsUnramified (k' := k) (F' := E) := by
  simp only [isUnramified_iff_forall_le_inertiaField hF]
  refine ⟨fun h Q hQ ↦ (IntermediateField.le_normalClosure E).trans (h Q hQ),
    fun h Q hQ ↦ ?_⟩
  -- The normal closure is generated by the conjugates `σ E`, and `σ E` lies in the inertia field
  -- of `Q` because `E` lies in the inertia field of the conjugate place `σ⁻¹ • Q`.
  rw [IntermediateField.normalClosure_def'', iSup_le_iff]
  intro σ
  have hσ := IntermediateField.map_mono σ.toAlgHom (h (σ⁻¹ • Q) (by rw [restrict_smul, hQ]))
  rwa [← inertiaField_smul, smul_inv_smul] at hσ

end Place

end TauCeti
