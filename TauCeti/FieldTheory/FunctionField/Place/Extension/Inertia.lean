/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Invariant.Galois
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Decomposition
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Eisenstein

/-!
# The inertia group and inertia field of a place, and the residue action

Let `F' / F` be a finite Galois extension of fields, `k` a subfield of `F`, and `P` a place of
`F' / k`.  An automorphism in the decomposition group of `P` preserves the valuation ring `𝒪_P`
and hence its maximal ideal, so it descends to an automorphism of the residue field `F'_P`; since
it fixes `F` pointwise it fixes the residue field `F_{P ∩ F}` of the place below, so the descent
is a homomorphism
`TauCeti.Place.residueAut : G_Z(P) →* (F'_P ≃ₐ[F_{P ∩ F}] F'_P)`.
Its kernel is Mathlib's `ValuationSubring.inertiaSubgroup`, the **inertia group** of `P`.

The residue action distinguishes the automorphisms that become invisible after reduction from
those detected on the residue field.  Its surjectivity shows that every automorphism of the
residue extension arises this way, so the inertia quotient captures exactly the residue-field
symmetries and relates ramification to the separable and inseparable residue degrees.

Consequently `G_Z(P) / G_T(P)` is the automorphism group of the residue extension and of its
separable closure.  Its order is the separable residue degree, while the inertia group has order
the ramification index times the inseparable residue degree.  When the residue extension is
separable, these specialize to orders `f(P ∣ P ∩ F)` and `e(P ∣ P ∩ F)`, respectively.

The **inertia field** `T` of `P` is the subfield of `F'` fixed by the inertia group.  Over it the
Galois group is the whole inertia group, so it acts trivially on residues, and when the residue
extension is separable `[F' : T] = e(P ∣ P ∩ F)`.  The ramification and the residue extension then
separate: `P` is totally ramified over `T`, while `P ∩ T` is unramified over `F` with the full
residue extension.  Over both the decomposition and the inertia field the valuation ring of `P` is
the integral closure of the valuation ring below it.

This is Stichtenoth, Definition 3.8.1 and the second half of Theorem 3.8.2; the first half — the
order of the decomposition group, and the decomposition field — is in
`TauCeti/FieldTheory/FunctionField/Place/Extension/Decomposition.lean`.

## Main definitions

* `TauCeti.Place.residueAut`: the homomorphism from the decomposition group of a place to the
  automorphism group of the residue extension, with `TauCeti.Place.residueAut_residue` computing
  it on residues.
* `TauCeti.Place.decompositionQuotientInertiaEquiv`: the induced isomorphism of the decomposition
  group modulo the inertia group with the automorphism group of the residue extension, with
  `TauCeti.Place.decompositionQuotientInertiaEquiv_mk` computing it on classes.
* `TauCeti.Place.decompositionQuotientInertiaEquivSeparableClosure`: the corresponding
  identification with the automorphism group of the separable part of the residue extension.
* `TauCeti.Place.inertiaField`: the subfield of `F'` fixed by the inertia group of a place, with
  `TauCeti.Place.mem_inertiaField_iff` and `TauCeti.Place.fixingSubgroup_inertiaField`.
* `TauCeti.Place.inertiaFieldAutEquiv`: the identification of the Galois group over the inertia
  field with the inertia group, with `TauCeti.Place.coe_inertiaFieldAutEquiv_apply` computing it.

## Main results

* `TauCeti.Place.ker_residueAut`: the kernel of `TauCeti.Place.residueAut` is the inertia group,
  restated elementwise as `ValuationSubring.mem_inertiaSubgroup_iff`.
* `TauCeti.Place.residueAut_surjective`: **the decomposition group surjects onto the automorphism
  group of the residue extension**.
* `TauCeti.Place.card_inertiaSubgroup_mul_card_residueFieldAut`: the order of the inertia group
  times the order of the residue automorphism group is `e · f`.
* `TauCeti.Place.card_decompositionQuotientInertia_eq_finSepDegree` and
  `TauCeti.Place.card_inertiaSubgroup_eq_ramificationIdx_mul_finInsepDegree`: the unconditional
  formulas `|G_Z/G_T| = f_sep` and `|G_T| = e · f_ins`.
* `TauCeti.Place.normal_residueField`: the residue extension at a place of a Galois extension is
  normal; hence `TauCeti.Place.card_residueFieldAut` and
  `TauCeti.Place.card_inertiaSubgroup`, which give the residue automorphism group order
  `f(P ∣ P ∩ F)` and the inertia group order `e(P ∣ P ∩ F)` once the residue extension is
  separable.
* `TauCeti.Place.decompositionSubgroup_decompositionField_eq_top`: over its decomposition field a
  place is fixed by the whole Galois group.
* `TauCeti.Place.isIntegral_iff_mem_integers_of_decompositionSubgroup_eq_top`: if the whole
  Galois group fixes `P`, the valuation ring of `P` is the integral closure of the one below.
* `TauCeti.Place.decompositionSubgroup_inertiaField_eq_top`,
  `TauCeti.Place.inertiaSubgroup_inertiaField_eq_top` and
  `TauCeti.Place.eq_of_restrict_inertiaField_eq`: over its inertia field a place is fixed by the
  whole Galois group, which acts trivially on its residues, and it is the only place above its
  restriction.
* `TauCeti.Place.finrank_inertiaField`, `TauCeti.Place.ramificationIdx_inertiaField`,
  `TauCeti.Place.ramificationIdx_restrict_inertiaField`,
  `TauCeti.Place.isTotallyRamified_inertiaField`, `TauCeti.Place.relativeDegree_inertiaField` and
  `TauCeti.Place.relativeDegree_restrict_inertiaField`: with separable residue extension,
  `[F' : T] = e`, all of the ramification happens above `T` and all of the residue extension
  below it.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.8.1 and Theorem 3.8.2.
-/

public section

open scoped Pointwise

namespace TauCeti

namespace Place

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']

section ResidueAction

variable (F) [Algebra.IsIntegral F F'] (P : Place k F')

/-- The decomposition group of `P` fixes the valuation ring of the place below `P` pointwise, so
its action on `𝒪_P` is by `𝒪_{P ∩ F}`-algebra automorphisms. -/
instance instSMulCommClassIntegers : SMulCommClass (P.integers.decompositionSubgroup F)
    (P.restrict k F).integers P.integers where
  smul_comm g a b := Subtype.ext <| by
    rw [Algebra.smul_def, Algebra.smul_def, ValuationSubring.coe_decompositionSubgroup_smul,
      Submonoid.coe_mul, Submonoid.coe_mul, map_mul, coe_algebraMap_integers, AlgEquiv.commutes,
      ValuationSubring.coe_decompositionSubgroup_smul]

/-- The induced action of the decomposition group on the residue field of `P` is by
`F_{P ∩ F}`-algebra automorphisms. -/
instance instSMulCommClassResidueField : SMulCommClass (P.integers.decompositionSubgroup F)
    (P.restrict k F).ResidueField P.ResidueField where
  smul_comm g a b := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := (P.restrict k F).integers) a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := P.integers) b
    simp only [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_residue, ← map_mul,
      ← IsLocalRing.ResidueField.residue_smul]
    exact congrArg (IsLocalRing.residue P.integers) (by rw [smul_mul', smul_algebraMap])

/-- **The residue action of the decomposition group** (Stichtenoth, Theorem 3.8.2): an
automorphism of `F'` fixing the place `P` descends to an automorphism of the residue field `F'_P`
over the residue field of the place below `P`. -/
noncomputable def residueAut : P.integers.decompositionSubgroup F →*
    (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) :=
  MulSemiringAction.toAlgAut _ _ _

/-- **The residue action, on residues** (Stichtenoth, Theorem 3.8.2): the automorphism of `F'_P`
induced by `g` sends the residue of an element `x` of `𝒪_P` to the residue of `g x`. -/
@[simp]
theorem residueAut_residue (g : P.integers.decompositionSubgroup F) (x : P.integers) :
    residueAut F P g (IsLocalRing.residue P.integers x) =
      IsLocalRing.residue P.integers (g • x) := by
  rw [residueAut, MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply,
    IsLocalRing.ResidueField.residue_smul]

/-- **The inertia group is the kernel of the residue action** (Stichtenoth, Theorem 3.8.2): this
identifies Mathlib's `ValuationSubring.inertiaSubgroup`, defined as the kernel of the action on
the residue field, with the kernel of `TauCeti.Place.residueAut`, which records that the action
is by automorphisms over the residue field of the place below. -/
@[simp]
theorem ker_residueAut : (residueAut F P).ker = P.integers.inertiaSubgroup F := by
  ext g
  rw [MonoidHom.mem_ker, ValuationSubring.mem_inertiaSubgroup_iff]
  constructor
  · intro hg x
    rw [← residueAut_residue]
    exact DFunLike.congr_fun hg _
  · intro hg
    apply AlgEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := P.integers) z
    rw [residueAut_residue]
    exact hg x

omit [Algebra k F] [IsScalarTower k F F'] [Algebra.IsIntegral F F'] in
/-- The inertia group is normal in the decomposition group, being a kernel. -/
instance normal_inertiaSubgroup : (P.integers.inertiaSubgroup F).Normal :=
  MonoidHom.normal_ker _

end ResidueAction

section Galois

variable (F) [FiniteDimensional F F'] [IsGalois F F'] (P : Place k F')

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- If every automorphism of `F' / F` fixes `P`, the valuation ring of `P` is an invariant
extension of the valuation ring of the place below: an element fixed by every automorphism of
`F' / F` lies in `F`, and is integral at the place below because it is integral at `P`. -/
private theorem isInvariant_integers_of_decompositionSubgroup_eq_top
    (h : P.integers.decompositionSubgroup F = ⊤) :
    Algebra.IsInvariant (P.restrict k F).integers P.integers
      (P.integers.decompositionSubgroup F) := by
  refine ⟨fun b hb ↦ ?_⟩
  have hfix : ∀ τ : F' ≃ₐ[F] F', τ (b : F') = (b : F') := fun τ ↦
    congrArg (fun z : P.integers ↦ (z : F')) (hb ⟨τ, by rw [h]; trivial⟩)
  obtain ⟨z, hz⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := F) (b : F')).mpr hfix
  exact ⟨⟨z, (mem_integers_restrict_iff k F P z).mpr (hz ▸ b.2)⟩,
    Subtype.ext (by rw [coe_algebraMap_integers]; exact hz)⟩

/-- **A place fixed by the whole Galois group is the integral closure of the place below**
(Stichtenoth, Theorem 3.8.2): if every automorphism of `F' / F` fixes `P`, an element of `F'` is
integral over the valuation ring of `P ∩ F` exactly when it is regular at `P`.  This applies over
the decomposition field and over the inertia field of `P`. -/
theorem isIntegral_iff_mem_integers_of_decompositionSubgroup_eq_top
    (h : P.integers.decompositionSubgroup F = ⊤) {z : F'} :
    IsIntegral (P.restrict k F).integers z ↔ z ∈ P.integers := by
  refine ⟨P.mem_integers_of_isIntegral (R := (P.restrict k F).integers) fun a ↦
    (mem_integers_restrict_iff k F P (a : F)).mp a.2, fun hz ↦ ?_⟩
  have := isInvariant_integers_of_decompositionSubgroup_eq_top F P h
  have := Algebra.IsInvariant.isIntegral (P.restrict k F).integers P.integers
    (P.integers.decompositionSubgroup F)
  -- Both maps to `F'` are induced by `F → F'` on representatives.
  have : IsScalarTower (P.restrict k F).integers P.integers F' := .of_algebraMap_eq fun _ ↦ rfl
  exact (Algebra.IsIntegral.isIntegral (⟨z, hz⟩ : P.integers)).map
    (IsScalarTower.toAlgHom (P.restrict k F).integers P.integers F')

/-- **The residue field of the decomposition field is the residue field of `F`** (Stichtenoth,
Theorem 3.8.2), in the form used below: the two residue fields have the same image in `F'_P`.

Downwards this is because the residue extension below the decomposition field is trivial, and
upwards it is because `F` sits inside the decomposition field. -/
private theorem range_algebraMap_residueField_eq :
    (algebraMap (P.restrict k (decompositionField F P)).ResidueField P.ResidueField).range =
      (algebraMap (P.restrict k F).ResidueField P.ResidueField).range := by
  have hfinrank : Module.finrank
      ((P.restrict k (decompositionField F P)).restrict k F).ResidueField
      (P.restrict k (decompositionField F P)).ResidueField = 1 := by
    rw [← relativeDegree_def k F (P.restrict k (decompositionField F P))]
    exact relativeDegree_restrict_decompositionField F P
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨u, hu⟩ :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfinrank).surjective y
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective
      (R := ((P.restrict k (decompositionField F P)).restrict k F).integers) u
    have ha : (a : F) ∈ (P.restrict k F).integers := by
      rw [← restrict_restrict (k₁ := k) (F₁ := (decompositionField F P : Type v')) P]
      exact a.2
    refine ⟨IsLocalRing.residue (P.restrict k F).integers ⟨(a : F), ha⟩, ?_⟩
    rw [← hu, IsLocalRing.ResidueField.algebraMap_residue,
      IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.algebraMap_residue]
    refine congrArg (IsLocalRing.residue P.integers) (Subtype.ext ?_)
    rw [coe_algebraMap_integers, coe_algebraMap_integers, coe_algebraMap_integers,
      ← IsScalarTower.algebraMap_apply F (decompositionField F P : Type v') F']
  · rintro ⟨x, rfl⟩
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := (P.restrict k F).integers) x
    have hb : algebraMap F (decompositionField F P : Type v') (b : F) ∈
        (P.restrict k (decompositionField F P)).integers := by
      rw [mem_integers_restrict_iff, ← IsScalarTower.algebraMap_apply]
      exact (mem_integers_restrict_iff k F P (b : F)).mp b.2
    refine ⟨IsLocalRing.residue _ ⟨_, hb⟩, ?_⟩
    rw [IsLocalRing.ResidueField.algebraMap_residue, IsLocalRing.ResidueField.algebraMap_residue]
    refine congrArg (IsLocalRing.residue P.integers) (Subtype.ext ?_)
    rw [coe_algebraMap_integers, coe_algebraMap_integers, ← IsScalarTower.algebraMap_apply]

/-- **The decomposition group surjects onto the automorphisms of the residue extension**
(Stichtenoth, Theorem 3.8.2). -/
theorem residueAut_surjective : Function.Surjective (residueAut F P) := by
  intro τ
  have := isInvariant_integers_of_decompositionSubgroup_eq_top (decompositionField F P) P
    (decompositionSubgroup_decompositionField_eq_top F P)
  let τ₀ : P.ResidueField ≃ₐ[(P.restrict k (decompositionField F P)).ResidueField]
      P.ResidueField :=
    AlgEquiv.ofRingEquiv (f := (τ : P.ResidueField ≃+* P.ResidueField)) fun y ↦ by
      obtain ⟨x, hx⟩ : algebraMap (P.restrict k (decompositionField F P)).ResidueField
          P.ResidueField y ∈
          (algebraMap (P.restrict k F).ResidueField P.ResidueField).range := by
        rw [← range_algebraMap_residueField_eq F P]
        exact ⟨y, rfl⟩
      rw [← hx]
      exact τ.commutes x
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective
    (A := (P.restrict k (decompositionField F P)).integers) (B := P.integers)
    (P.integers.decompositionSubgroup (decompositionField F P))
    (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal _) τ₀
  refine ⟨⟨AlgEquiv.restrictScalars F
    (↑(g : ↥(P.integers.decompositionSubgroup (decompositionField F P))) :
      F' ≃ₐ[(decompositionField F P : Type v')] F'), ?_⟩, ?_⟩
  · rw [← stabilizer_eq_decompositionSubgroup]
    exact restrictScalars_smul_eq_self F P _
  · refine AlgEquiv.ext fun z ↦ ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := P.integers) z
    rw [residueAut_residue]
    exact congrArg (fun e ↦ e (IsLocalRing.residue P.integers x)) hg

/-- **The decomposition group modulo the inertia group is the automorphism group of the residue
extension** (Stichtenoth, Theorem 3.8.2). -/
noncomputable def decompositionQuotientInertiaEquiv :
    P.integers.decompositionSubgroup F ⧸ P.integers.inertiaSubgroup F ≃*
      (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) :=
  QuotientGroup.liftEquiv _ (residueAut_surjective F P) (ker_residueAut F P).symm

/-- The isomorphism of `TauCeti.Place.decompositionQuotientInertiaEquiv` is induced by the residue
action: it sends the class of `g` to the residue automorphism of `g`. -/
@[simp]
theorem decompositionQuotientInertiaEquiv_mk (g : P.integers.decompositionSubgroup F) :
    decompositionQuotientInertiaEquiv F P (QuotientGroup.mk g) = residueAut F P g := by
  rw [decompositionQuotientInertiaEquiv, QuotientGroup.liftEquiv_mk]

/-- **The order of the inertia group, unconditionally** (Stichtenoth, Theorem 3.8.2): together
with the residue automorphism group it accounts for the order `e · f` of the decomposition
group. -/
theorem card_inertiaSubgroup_mul_card_residueFieldAut :
    Nat.card (P.integers.inertiaSubgroup F) *
        Nat.card (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) =
      ramificationIdx F P * relativeDegree k F P := by
  rw [← card_decompositionSubgroup F P,
    ← Nat.card_congr (decompositionQuotientInertiaEquiv F P).toEquiv, mul_comm]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm

/-- **The residue extension at a place of a Galois extension is normal** (Stichtenoth,
Theorem 3.8.2).

Normality holds over the residue field of the decomposition field because the valuation ring of
`P` is an invariant extension there, and it descends to the residue field of `F` because the two
residue fields agree. -/
theorem normal_residueField : Normal (P.restrict k F).ResidueField P.ResidueField := by
  have hnormal : Normal (P.restrict k (decompositionField F P)).ResidueField P.ResidueField := by
    have := isInvariant_integers_of_decompositionSubgroup_eq_top (decompositionField F P) P
      (decompositionSubgroup_decompositionField_eq_top F P)
    exact Ideal.Quotient.normal (P.integers.decompositionSubgroup (decompositionField F P))
      (IsLocalRing.maximalIdeal _) (IsLocalRing.maximalIdeal _)
  have h := Function.leftInverse_invFun
    (algebraMap (P.restrict k F).ResidueField P.ResidueField).injective
  refine Normal.of_equiv_equiv
    (f := (RingEquiv.ofLeftInverse (Function.leftInverse_invFun
        (algebraMap (P.restrict k (decompositionField F P)).ResidueField
          P.ResidueField).injective)).trans
      ((RingEquiv.subringCongr (range_algebraMap_residueField_eq F P)).trans
        (RingEquiv.ofLeftInverse h).symm))
    (g := RingEquiv.refl P.ResidueField) (RingHom.ext fun y ↦ ?_)
  have hcoe : ∀ w : (algebraMap (P.restrict k F).ResidueField P.ResidueField).range,
      algebraMap (P.restrict k F).ResidueField P.ResidueField
          ((RingEquiv.ofLeftInverse h).symm w) = (w : P.ResidueField) := fun w ↦ by
    rw [← RingEquiv.ofLeftInverse_apply h, RingEquiv.apply_symm_apply]
  exact hcoe _

/-- **The residue automorphism group is the automorphism group of the separable part**
(Stichtenoth, Theorem 3.8.2).  Restriction to the separable closure is an isomorphism because the
remaining residue extension is purely inseparable. -/
noncomputable def residueFieldAutEquivSeparableClosure :
    (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) ≃*
      Gal(separableClosure (P.restrict k F).ResidueField P.ResidueField /
        (P.restrict k F).ResidueField) := by
  let := normal_residueField F P
  exact (separableClosureRestrictEquiv (P.restrict k F).ResidueField P.ResidueField).toMulEquiv

/-- `residueFieldAutEquivSeparableClosure` acts by restricting a residue automorphism to the
separable closure. -/
@[simp]
theorem coe_residueFieldAutEquivSeparableClosure_apply
    (σ : P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField)
    (x : separableClosure (P.restrict k F).ResidueField P.ResidueField) :
    ((residueFieldAutEquivSeparableClosure F P σ) x : P.ResidueField) = σ x := by
  let := normal_residueField F P
  exact coe_separableClosureRestrictEquiv_apply σ x

/-- The quotient of the decomposition group by inertia, identified with the automorphism group
of the separable part of the residue extension (Stichtenoth, Theorem 3.8.2). -/
noncomputable def decompositionQuotientInertiaEquivSeparableClosure :
    P.integers.decompositionSubgroup F ⧸ P.integers.inertiaSubgroup F ≃*
      Gal(separableClosure (P.restrict k F).ResidueField P.ResidueField /
        (P.restrict k F).ResidueField) :=
  (decompositionQuotientInertiaEquiv F P).trans (residueFieldAutEquivSeparableClosure F P)

/-- On the separable closure, the separable-part quotient equivalence sends the class of `g` to
the residue automorphism of `g`. -/
@[simp]
theorem coe_decompositionQuotientInertiaEquivSeparableClosure_mk_apply
    (g : P.integers.decompositionSubgroup F)
    (x : separableClosure (P.restrict k F).ResidueField P.ResidueField) :
    ((decompositionQuotientInertiaEquivSeparableClosure F P (QuotientGroup.mk g)) x :
        P.ResidueField) = residueAut F P g x := by
  rw [decompositionQuotientInertiaEquivSeparableClosure, MulEquiv.trans_apply,
    decompositionQuotientInertiaEquiv_mk, coe_residueFieldAutEquivSeparableClosure_apply]

/-- **The residue automorphism group has order equal to the separable residue degree**
(Stichtenoth, Theorem 3.8.2). -/
theorem card_residueFieldAut_eq_finSepDegree :
    Nat.card (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) =
      Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField := by
  let := normal_residueField F P
  rw [Nat.card_congr (residueFieldAutEquivSeparableClosure F P).toEquiv,
    IsGalois.card_aut_eq_finrank, Field.finSepDegree_eq, Field.sepDegree]
  rfl

/-- **The decomposition group modulo inertia has order equal to the separable residue degree**
(Stichtenoth, Theorem 3.8.2). -/
theorem card_decompositionQuotientInertia_eq_finSepDegree :
    Nat.card (P.integers.decompositionSubgroup F ⧸ P.integers.inertiaSubgroup F) =
      Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField := by
  rw [Nat.card_congr (decompositionQuotientInertiaEquiv F P).toEquiv,
    card_residueFieldAut_eq_finSepDegree F P]

/-- **The unconditional order of the inertia group** (Stichtenoth, Theorem 3.8.2): it is the
ramification index times the inseparable residue degree. -/
theorem card_inertiaSubgroup_eq_ramificationIdx_mul_finInsepDegree :
    Nat.card (P.integers.inertiaSubgroup F) =
      ramificationIdx F P *
        Field.finInsepDegree (P.restrict k F).ResidueField P.ResidueField := by
  have h := card_inertiaSubgroup_mul_card_residueFieldAut F P
  rw [card_residueFieldAut_eq_finSepDegree F P] at h
  refine Nat.eq_of_mul_eq_mul_right (NeZero.pos
    (Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField)) ?_
  calc
    Nat.card (P.integers.inertiaSubgroup F) *
          Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField =
        ramificationIdx F P * relativeDegree k F P := h
    _ = ramificationIdx F P *
          (Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField *
            Field.finInsepDegree (P.restrict k F).ResidueField P.ResidueField) := by
      rw [Field.finSepDegree_mul_finInsepDegree, relativeDegree_def]
    _ = (ramificationIdx F P *
          Field.finInsepDegree (P.restrict k F).ResidueField P.ResidueField) *
            Field.finSepDegree (P.restrict k F).ResidueField P.ResidueField := by
      ring

variable [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]

/-- **The residue automorphism group has order `f(P ∣ P ∩ F)`** (Stichtenoth, Theorem 3.8.2),
when the residue extension is separable: it is then Galois, since it is always normal. -/
theorem card_residueFieldAut :
    Nat.card (P.ResidueField ≃ₐ[(P.restrict k F).ResidueField] P.ResidueField) =
      relativeDegree k F P := by
  have := normal_residueField F P
  have : IsGalois (P.restrict k F).ResidueField P.ResidueField := ⟨⟩
  rw [relativeDegree_def]
  exact IsGalois.card_aut_eq_finrank _ _

/-- **The inertia group has order `e(P ∣ P ∩ F)`** (Stichtenoth, Theorem 3.8.2), when the residue
extension is separable. -/
theorem card_inertiaSubgroup :
    Nat.card (P.integers.inertiaSubgroup F) = ramificationIdx F P := by
  have h := card_inertiaSubgroup_mul_card_residueFieldAut F P
  rw [card_residueFieldAut F P] at h
  exact Nat.eq_of_mul_eq_mul_right (one_le_relativeDegree k F P) h

end Galois

section InertiaField

variable (F) [FiniteDimensional F F'] [IsGalois F F'] (P : Place k F')

/-- **The inertia field** of a place `P` of `F' / k` in a finite Galois extension `F' / F`
(Stichtenoth, Definition 3.8.1): the subfield of `F'` fixed by the inertia group of `P`. -/
noncomputable def inertiaField : IntermediateField F F' :=
  IntermediateField.fixedField
    ((P.integers.inertiaSubgroup F).map (P.integers.decompositionSubgroup F).subtype)

omit [Algebra k F] [IsScalarTower k F F'] [FiniteDimensional F F'] [IsGalois F F'] in
/-- An element of `F'` lies in the inertia field of `P` exactly when the inertia group of `P`
fixes it. -/
@[simp]
theorem mem_inertiaField_iff (x : F') :
    x ∈ inertiaField F P ↔ ∀ g ∈ P.integers.inertiaSubgroup F, (g : F' ≃ₐ[F] F') x = x := by
  simp [inertiaField, IntermediateField.mem_fixedField_iff]

omit [Algebra k F] [IsScalarTower k F F'] [IsGalois F F'] in
/-- **The Galois correspondence for the inertia field**: the automorphisms of `F'` fixing the
inertia field of `P` pointwise are exactly the inertia group of `P`. -/
@[simp]
theorem fixingSubgroup_inertiaField :
    (inertiaField F P).fixingSubgroup =
      (P.integers.inertiaSubgroup F).map (P.integers.decompositionSubgroup F).subtype :=
  IntermediateField.fixingSubgroup_fixedField _

omit [Algebra k F] [IsScalarTower k F F'] [FiniteDimensional F F'] [IsGalois F F'] in
/-- The decomposition field of `P` lies inside its inertia field. -/
theorem decompositionField_le_inertiaField : decompositionField F P ≤ inertiaField F P :=
  fun x hx ↦ (mem_inertiaField_iff F P x).mpr fun g _ ↦
    (mem_decompositionField_iff F P x).mp hx g g.2

omit [Algebra k F] [IsScalarTower k F F'] [IsGalois F F'] in
/-- An automorphism of `F'` over the inertia field of `P`, read as an automorphism over `F`, is an
element of the inertia group of `P`. -/
theorem exists_mem_inertiaSubgroup_coe_eq_restrictScalars (τ : F' ≃ₐ[inertiaField F P] F') :
    ∃ g ∈ P.integers.inertiaSubgroup F, (g : F' ≃ₐ[F] F') = τ.restrictScalars F := by
  have hτ : τ.restrictScalars F ∈ (inertiaField F P).fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ τ.commutes ⟨x, hx⟩
  rw [fixingSubgroup_inertiaField, Subgroup.mem_map] at hτ
  exact hτ

omit [IsGalois F F'] in
/-- An automorphism of `F'` over the inertia field of `P`, read as an automorphism over `F`, fixes
`P`. -/
-- The priority keeps this ahead of `TauCeti.Place.restrictScalars_smul`, which would otherwise
-- rewrite the left-hand side to `τ • P` before this can close it.
@[simp high]
theorem restrictScalars_smul_eq_self_of_inertiaField (τ : F' ≃ₐ[inertiaField F P] F') :
    τ.restrictScalars F • P = P := by
  obtain ⟨g, -, hg⟩ := exists_mem_inertiaSubgroup_coe_eq_restrictScalars F P τ
  rw [← hg, ← MulAction.mem_stabilizer_iff, stabilizer_eq_decompositionSubgroup]
  exact g.2

omit [IsGalois F F'] in
/-- **The Galois group over the inertia field is the inertia group**: reading an automorphism of
`F'` over the inertia field of `P` as an automorphism over `F` identifies the two groups. -/
noncomputable def inertiaFieldAutEquiv :
    (F' ≃ₐ[inertiaField F P] F') ≃* P.integers.inertiaSubgroup F := by
  have h₁ (σ : F' ≃ₐ[inertiaField F P] F') :
      σ.restrictScalars F ∈ P.integers.decompositionSubgroup F := by
    rw [← stabilizer_eq_decompositionSubgroup]
    exact restrictScalars_smul_eq_self_of_inertiaField F P σ
  have h₂ (σ : F' ≃ₐ[inertiaField F P] F') :
      (⟨σ.restrictScalars F, h₁ σ⟩ : P.integers.decompositionSubgroup F) ∈
        P.integers.inertiaSubgroup F := by
    obtain ⟨g, hg, hgσ⟩ := exists_mem_inertiaSubgroup_coe_eq_restrictScalars F P σ
    exact (Subtype.ext hgσ : g = ⟨σ.restrictScalars F, h₁ σ⟩) ▸ hg
  let f : (F' ≃ₐ[inertiaField F P] F') →* P.integers.inertiaSubgroup F :=
    { toFun σ := ⟨⟨σ.restrictScalars F, h₁ σ⟩, h₂ σ⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  refine MulEquiv.ofBijective f ⟨fun σ τ h ↦ ?_, fun g ↦ ?_⟩
  · exact AlgEquiv.restrictScalars_injective F (congrArg
      (fun g : P.integers.inertiaSubgroup F ↦
        ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F')) h)
  · have hg : ((g : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') ∈
        (inertiaField F P).fixingSubgroup := by
      rw [fixingSubgroup_inertiaField]
      exact Subgroup.mem_map_of_mem _ g.2
    exact ⟨(inertiaField F P).fixingSubgroupEquiv ⟨_, hg⟩, Subtype.ext (Subtype.ext (by ext; rfl))⟩

omit [IsGalois F F'] in
/-- The element of the inertia group attached by `TauCeti.Place.inertiaFieldAutEquiv` to an
automorphism over the inertia field is that automorphism read over `F`. -/
@[simp]
theorem coe_inertiaFieldAutEquiv_apply (σ : F' ≃ₐ[inertiaField F P] F') :
    ((inertiaFieldAutEquiv F P σ : P.integers.decompositionSubgroup F) : F' ≃ₐ[F] F') =
      σ.restrictScalars F :=
  -- `(rfl)`, not `rfl`: the body of `inertiaFieldAutEquiv` is not `@[expose]`d, so a bare `rfl`
  -- proof would be rechecked against the exported environment, where it is opaque.
  (rfl)

omit [IsGalois F F'] in
/-- Over its inertia field a place is fixed by the whole Galois group. -/
@[simp]
theorem decompositionSubgroup_inertiaField_eq_top :
    P.integers.decompositionSubgroup (inertiaField F P) = ⊤ := by
  rw [← stabilizer_eq_decompositionSubgroup]
  ext τ
  simp only [Subgroup.mem_top, iff_true, MulAction.mem_stabilizer_iff]
  rw [← restrictScalars_smul (inertiaField F P) τ P]
  exact restrictScalars_smul_eq_self_of_inertiaField F P τ

omit [Algebra k F] [IsScalarTower k F F'] [IsGalois F F'] in
/-- **Over its inertia field a place has the whole Galois group as inertia group**: every
automorphism of `F'` over the inertia field acts trivially on the residue field of `P`. -/
@[simp]
theorem inertiaSubgroup_inertiaField_eq_top :
    P.integers.inertiaSubgroup (inertiaField F P) = ⊤ := by
  refine top_unique fun g _ ↦ (ValuationSubring.mem_inertiaSubgroup_iff _ g).mpr fun x ↦ ?_
  obtain ⟨h, hh, hgh⟩ := exists_mem_inertiaSubgroup_coe_eq_restrictScalars F P g
  have hx : g • x = h • x := Subtype.ext <| by
    rw [ValuationSubring.coe_decompositionSubgroup_smul,
      ValuationSubring.coe_decompositionSubgroup_smul, hgh, AlgEquiv.restrictScalars_apply]
  rw [hx]
  exact (ValuationSubring.mem_inertiaSubgroup_iff _ h).mp hh x

/-- **A place is the only place of `F'` above its restriction to its inertia field**. -/
theorem eq_of_restrict_inertiaField_eq {Q : Place k F'}
    (h : restrict k (inertiaField F P) Q = restrict k (inertiaField F P) P) : Q = P := by
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_restrict_eq (F := (inertiaField F P : Type v')) h
  rw [← smul_left_cancel_iff (τ.restrictScalars F), restrictScalars_smul _ τ Q, hτ,
    restrictScalars_smul_eq_self_of_inertiaField F P τ]

omit [Algebra k F] [IsScalarTower k F F'] [IsGalois F F'] in
/-- **The degree of `F'` over the inertia field** is the order of the inertia group. -/
theorem finrank_inertiaField_eq_card :
    Module.finrank (inertiaField F P) F' = Nat.card (P.integers.inertiaSubgroup F) := by
  rw [inertiaField, IntermediateField.finrank_fixedField_eq_card,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

variable [Algebra.IsSeparable (P.restrict k F).ResidueField P.ResidueField]

/-- **The degree of `F'` over the inertia field is `e(P ∣ P ∩ F)`** (Stichtenoth, Theorem 3.8.2),
when the residue extension is separable. -/
theorem finrank_inertiaField : Module.finrank (inertiaField F P) F' = ramificationIdx F P := by
  rw [finrank_inertiaField_eq_card, card_inertiaSubgroup]

/-- **The ramification index is unchanged over the inertia field** (Stichtenoth, Theorem 3.8.2),
when the residue extension is separable. -/
@[simp]
theorem ramificationIdx_inertiaField :
    ramificationIdx (inertiaField F P) P = ramificationIdx F P := by
  have := isSeparable_residueField_restrict_top k F (k₁ := k) (F₁ := inertiaField F P) P
  rw [← card_inertiaSubgroup (inertiaField F P) P, inertiaSubgroup_inertiaField_eq_top,
    Subgroup.card_top, decompositionSubgroup_inertiaField_eq_top, Subgroup.card_top,
    IsGalois.card_aut_eq_finrank, finrank_inertiaField]

/-- **The restriction of a place to its inertia field is unramified over `F`** (Stichtenoth,
Theorem 3.8.2), when the residue extension is separable. -/
@[simp]
theorem ramificationIdx_restrict_inertiaField :
    ramificationIdx F (restrict k (inertiaField F P) P) = 1 := by
  have h := ramificationIdx_restrict_mul (k₁ := k) (F₀ := F)
    (F₁ := (inertiaField F P : Type v')) P
  rw [ramificationIdx_inertiaField] at h
  exact (Nat.mul_eq_left (ramificationIdx_pos F P).ne').mp h.symm

/-- **A place is totally ramified over its inertia field** (Stichtenoth, Theorem 3.8.2), when the
residue extension is separable. -/
theorem isTotallyRamified_inertiaField : IsTotallyRamified (inertiaField F P) P := by
  rw [isTotallyRamified_iff, ramificationIdx_inertiaField, finrank_inertiaField]

/-- **The residue extension above the inertia field is trivial** (Stichtenoth, Theorem 3.8.2),
when the residue extension is separable. -/
@[simp]
theorem relativeDegree_inertiaField : relativeDegree k (inertiaField F P) P = 1 :=
  relativeDegree_eq_one_of_isTotallyRamified _ _ (isTotallyRamified_inertiaField F P)

/-- **The whole residue extension happens below the inertia field** (Stichtenoth,
Theorem 3.8.2), when the residue extension is separable. -/
@[simp]
theorem relativeDegree_restrict_inertiaField :
    relativeDegree k F (restrict k (inertiaField F P) P) = relativeDegree k F P := by
  rw [relativeDegree_restrict_mul (k₀ := k) (k₁ := k) (F₀ := F)
    (F₁ := (inertiaField F P : Type v')) P, relativeDegree_inertiaField, one_mul]

end InertiaField

end Place

end TauCeti
