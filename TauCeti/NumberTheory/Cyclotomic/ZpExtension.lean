/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.NumberTheory.Cyclotomic.LogCharacter
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Procyclic
import Mathlib.Topology.Maps.Strict.Group
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Subgroup
import TauCeti.FieldTheory.Galois.FixedField
import TauCeti.Topology.Algebra.Group.Profinite.Hopfian
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.ClosedSubgroups

/-!
# The cyclotomic ℤ_p-extension of a number field

Inside the full cyclotomic tower `K(μ_{p^∞})`, take the fixed field of the finite-order
automorphisms. The logarithmic coordinate of the cyclotomic character identifies the
Galois group of this fixed field with a closed subgroup of the additive group of `ℤ_p`,
which is open over number fields. When this image is nontrivial, the fixed field is the
unique subextension of the full tower with Galois group topologically isomorphic to `ℤ_p`.
In any common overfield containing the roots of unity, the construction
commutes with base change by compositum.

The construction includes `p = 2`: a cyclotomic character value with nontrivial sign
can have infinite order. The subgroup used in the fixed field consists of the actual
torsion automorphisms.

The open image over a number field comes from
`TauCeti.relIndex_range_localCyclotomicCharacter_dvd_finrank`. The Galois-group identification
uses the Galois quotient `TauCeti.quotientFixingSubgroupEquiv` and the topological first
isomorphism theorem `ContinuousMulEquiv.quotientKerEquivRange`.

## Reference

* R. Sharifi, *Iwasawa Theory*, Remark 3.1.4, Lemma 3.1.7 and Definition 3.1.8.
-/

public section

open IntermediateField Multiplicative

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]
  [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

local notation "C" => cyclotomicTower p K L

/-- The fixed field of the torsion automorphisms of `K(μ_{p^∞})`.
Over a number field this is a ℤ_p-extension. -/
noncomputable def cyclotomicZpExtension : IntermediateField K C :=
  fixedField (torsionCharSubgroup p K L)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The cyclotomic ℤ_p-extension is the fixed field of the torsion subgroup. -/
theorem cyclotomicZpExtension_def :
    cyclotomicZpExtension p K L = fixedField (torsionCharSubgroup p K L) :=
  (rfl)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- An element of the full tower lies in the cyclotomic ℤ_p-extension if every torsion
automorphism fixes it. -/
@[simp]
theorem mem_cyclotomicZpExtension_iff {x : C} :
    x ∈ cyclotomicZpExtension p K L ↔ ∀ σ ∈ torsionCharSubgroup p K L, σ x = x :=
  mem_fixedField_iff (torsionCharSubgroup p K L) x

/-- The fixing subgroup in the full cyclotomic tower is exactly its torsion subgroup. -/
@[simp]
theorem fixingSubgroup_cyclotomicZpExtension :
    (cyclotomicZpExtension p K L).fixingSubgroup = torsionCharSubgroup p K L := by
  rw [cyclotomicZpExtension_def]
  exact IntermediateField.fixingSubgroup_fixedField_of_finite _

/-- The full cyclotomic tower is the cyclotomic ℤ_p-extension exactly when its
Galois group has trivial torsion. -/
@[simp]
theorem cyclotomicZpExtension_eq_top_iff :
    cyclotomicZpExtension p K L = ⊤ ↔ torsionCharSubgroup p K L = ⊥ := by
  rw [← fixingSubgroup_cyclotomicZpExtension, ← fixingSubgroup_top (F := K) (E := C)]
  exact ⟨congrArg fixingSubgroup, fun h ↦ by
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using congrArg fixedField h⟩

/-- Logarithmic coordinates of the Galois group of the cyclotomic ℤ_p-extension. -/
noncomputable def cyclotomicZpExtensionGaloisEquivRange :
    Gal(cyclotomicZpExtension p K L/K) ≃ₜ*
      (↑(cyclotomicTowerLogCharacter p K L) : Gal(C/K) →* Multiplicative ℤ_[p]).range :=
  let f := cyclotomicTowerLogCharacter p K L
  let F := cyclotomicZpExtension p K L
  let e := quotientFixingSubgroupEquiv K C F
  let e' := (ContinuousMulEquiv.refl Gal(C/K)).quotientCongr F.fixingSubgroup f.toMonoidHom.ker
    (by
      have hid : (ContinuousMulEquiv.refl Gal(C/K)).toMonoidHom = MonoidHom.id _ := rfl
      rw [hid, Subgroup.map_id]
      exact (fixingSubgroup_cyclotomicZpExtension p K L).trans
        (ker_cyclotomicTowerLogCharacter p K L).symm)
  e.symm.trans (e'.trans
    (ContinuousMulEquiv.quotientKerEquivRange (f.continuous.isClosedMap.isStrictMap f.continuous)))

/-- Restricting a full tower automorphism and taking its logarithmic coordinate recovers the
logarithmic character of that automorphism. -/
@[simp]
theorem coe_cyclotomicZpExtensionGaloisEquivRange_restrictNormalHom (σ : Gal(C/K)) :
    (cyclotomicZpExtensionGaloisEquivRange p K L
      (AlgEquiv.restrictNormalHom (cyclotomicZpExtension p K L) σ) : Multiplicative ℤ_[p]) =
      cyclotomicTowerLogCharacter p K L σ := by
  simp only [cyclotomicZpExtensionGaloisEquivRange, ContinuousMulEquiv.trans_apply,
    quotientFixingSubgroupEquiv_symm_restrictNormalHom, ContinuousMulEquiv.quotientCongr_mk,
    ContinuousMulEquiv.refl_apply]
  let f := (cyclotomicTowerLogCharacter p K L).toMonoidHom
  have hle : f.ker ≤ f.rangeRestrict.ker := (MonoidHom.ker_rangeRestrict f).symm.le
  -- The topological equivalence uses the algebraic range kernel lift, whose evaluation is a lift.
  exact congrArg Subtype.val (QuotientGroup.lift_mk' f.ker hle σ)

/-- The principal-unit part of the cyclotomic character descends to the torsion fixed field. -/
noncomputable def cyclotomicZpExtensionPrincipalCharacter :
    Gal(cyclotomicZpExtension p K L/K) →ₜ* unitsPrincipal p (padicUnitsDepth p) where
  toFun σ := (unitsPrincipalLogEquiv p).symm (cyclotomicZpExtensionGaloisEquivRange p K L σ)
  map_one' := by simp
  map_mul' σ τ := by simp
  continuous_toFun := (unitsPrincipalLogEquiv p).symm.continuous.comp
    (continuous_subtypeVal.comp (cyclotomicZpExtensionGaloisEquivRange p K L).continuous)

/-- The logarithm of the descended principal character is its logarithmic coordinate. -/
@[simp]
theorem unitsPrincipalLogEquiv_cyclotomicZpExtensionPrincipalCharacter
    (σ : Gal(cyclotomicZpExtension p K L/K)) :
    unitsPrincipalLogEquiv p (cyclotomicZpExtensionPrincipalCharacter p K L σ) =
      (cyclotomicZpExtensionGaloisEquivRange p K L σ : Multiplicative ℤ_[p]) := by
  simp only [cyclotomicZpExtensionPrincipalCharacter, ContinuousMonoidHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk, ContinuousMulEquiv.apply_symm_apply]

/-- On restriction from the full tower the descended character divides the full character
by the torsion section of its residue. -/
@[simp]
theorem coe_cyclotomicZpExtensionPrincipalCharacter_restrictNormalHom (σ : Gal(C/K)) :
    (cyclotomicZpExtensionPrincipalCharacter p K L
      (AlgEquiv.restrictNormalHom (cyclotomicZpExtension p K L) σ) : ℤ_[p]ˣ) =
      (padicUnitsSection p (PadicInt.unitsToZModPow (padicUnitsDepth p)
        (cyclotomicTowerCharacter p K L σ)))⁻¹ * cyclotomicTowerCharacter p K L σ := by
  have h := coe_cyclotomicZpExtensionGaloisEquivRange_restrictNormalHom p K L σ
  let u := cyclotomicTowerCharacter p K L σ
  have hu := (padicIntUnitsEquivZModUnitsProd p).symm_apply_apply u
  rw [padicIntUnitsEquivZModUnitsProd_symm_apply, padicIntUnitsEquivZModUnitsProd_apply_fst] at hu
  simp only [cyclotomicZpExtensionPrincipalCharacter, ContinuousMonoidHom.coe_mk,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h, cyclotomicTowerLogCharacter_apply, eq_inv_mul_iff_mul_eq]
  exact hu

/-- In the ambient field, an automorphism fixes the cyclotomic ℤ_p-extension precisely
when its cyclotomic character has finite order. -/
-- `IntermediateField.mem_fixingSubgroup_iff` already simplifies the left-hand side.
theorem mem_fixingSubgroup_lift_cyclotomicZpExtension_iff (σ : Gal(L/K)) :
    σ ∈ (IntermediateField.lift (cyclotomicZpExtension p K L)).fixingSubgroup ↔
      cyclotomicCharacter L p σ.toRingEquiv ∈ CommGroup.torsion ℤ_[p]ˣ := by
  have h : ((cyclotomicZpExtension p K L).map (cyclotomicTower p K L).val).fixingSubgroup = _ :=
    IntermediateField.map_fixingSubgroup (E' := L) (cyclotomicZpExtension p K L)
  rw [fixingSubgroup_cyclotomicZpExtension] at h
  rw [IntermediateField.lift, h, Subgroup.mem_comap, mem_torsionCharSubgroup_iff,
    cyclotomicTowerCharacter_restrictNormalHom]

variable {K L} in
/-- In any common overfield containing the `p`-power roots of unity, the cyclotomic
ℤ_p-extension of an intermediate field is its compositum with the cyclotomic
ℤ_p-extension of the base. -/
theorem cyclotomicZpExtension_baseChange (E : IntermediateField K L) :
    (IntermediateField.lift (cyclotomicZpExtension p E L)).restrictScalars K =
      E ⊔ IntermediateField.lift (cyclotomicZpExtension p K L) := by
  let T := cyclotomicTower p E L
  let D : IntermediateField K L := T.restrictScalars K
  have hCD : C ≤ D := cyclotomicTower_le_iff.mpr fun n _ hx ↦
    (mem_restrictScalars K).mpr (mem_cyclotomicTower_of_pow_eq_one (n := n) hx)
  let j : C →ₐ[K] T := inclusion hCD
  let F := cyclotomicZpExtension p K L
  let A := adjoin E (j '' (F : Set C))
  have hfix : (cyclotomicZpExtension p E L).fixingSubgroup = A.fixingSubgroup := by
    ext σ
    rw [fixingSubgroup_adjoin_image, Subgroup.mem_comap]
    simp only [F, fixingSubgroup_cyclotomicZpExtension, mem_torsionCharSubgroup_iff]
    rw [cyclotomicTowerCharacter_apply]
    let τ := j.restrictNormalHom (σ.restrictScalars K)
    have hχ : cyclotomicTowerCharacter p K L τ = cyclotomicCharacter T p σ.toRingEquiv := by
      rw [cyclotomicTowerCharacter_apply, ← AlgEquiv.toRingEquiv_restrictScalars K σ]
      exact cyclotomicCharacter_eq_of_injective (f := j.toRingHom) p j.injective
        (fun _ x _ ↦ (j.restrictNormalHom_commutes (σ.restrictScalars K) x).symm)
        (fun _ n ↦ HasEnoughRootsOfUnity.exists_isPrimitiveRoot C (p ^ n)) |>.symm
    exact Iff.of_eq (congrArg (· ∈ CommGroup.torsion ℤ_[p]ˣ) hχ).symm
  have hA := congrArg fixedField hfix
  rw [InfiniteGalois.fixedField_fixingSubgroup, InfiniteGalois.fixedField_fixingSubgroup] at hA
  rw [hA]
  dsimp only [A]
  rw [lift_adjoin, Set.image_image, restrictScalars_adjoin_eq_sup]
  congr 1
  -- The two inclusion maps compose to the inclusion of the original full tower into `L`.
  have hj : (fun x : C ↦ (j x : L)) = ((cyclotomicTower p K L).val : C → L) := by
    rw [IntermediateField.coe_val]
    funext x
    exact IntermediateField.coe_inclusion hCD x
  rw [hj, ← adjoin_map, adjoin_self]
  rw [IntermediateField.lift]

/-- If the logarithmic cyclotomic image is nontrivial, the torsion fixed field has Galois
group topologically isomorphic to `ℤ_p`. -/
theorem nonempty_cyclotomicZpExtensionGaloisEquiv_padicInt
    (hne : (cyclotomicTowerLogCharacter p K L).toMonoidHom.range ≠ ⊥) :
    Nonempty (Gal(cyclotomicZpExtension p K L/K) ≃ₜ* Multiplicative ℤ_[p]) := by
  let f := cyclotomicTowerLogCharacter p K L
  have hclosed : IsClosed (f.toMonoidHom.range : Set (Multiplicative ℤ_[p])) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range f.continuous).isClosed
  obtain ⟨e⟩ := f.toMonoidHom.range.nonempty_continuousMulEquiv_padicInt hclosed hne
  exact ⟨(cyclotomicZpExtensionGaloisEquivRange p K L).trans e⟩

/-- Over a number field, the cyclotomic ℤ_p-extension has Galois group isomorphic to `ℤ_p`. -/
theorem nonempty_cyclotomicZpExtensionGaloisEquiv_padicInt_of_finite_rat
    [Algebra ℚ K] [FiniteDimensional ℚ K] :
    Nonempty (Gal(cyclotomicZpExtension p K L/K) ≃ₜ* Multiplicative ℤ_[p]) := by
  let H : OpenSubgroup (Multiplicative ℤ_[p]) :=
    ⟨(cyclotomicTowerLogCharacter p K L).toMonoidHom.range,
      isOpen_range_cyclotomicTowerLogCharacter p K L
        (isOpen_range_cyclotomicTowerCharacter_of_finite_rat p K L)⟩
  obtain ⟨e⟩ := H.nonempty_continuousMulEquiv_padicInt
  exact ⟨(cyclotomicZpExtensionGaloisEquivRange p K L).trans e⟩

/-- The Galois group of the torsion fixed field is pro-`p`, even for trivial logarithmic image. -/
theorem isProP_cyclotomicZpExtensionGalois :
    IsProP p Gal(cyclotomicZpExtension p K L/K) :=
  ((isProP_multiplicative_padicInt p).subgroup _).of_equiv
    (cyclotomicZpExtensionGaloisEquivRange p K L).symm

/-- The coordinate attached to a nonidentity topological generator `γ` sends `γ` to `1`
in additive notation (`ofAdd 1`). -/
noncomputable def cyclotomicZpExtensionGaloisEquivPadicInt
    (γ : Gal(cyclotomicZpExtension p K L/K))
    (hγ : (Subgroup.closure {γ}).topologicalClosure = ⊤) (hne : γ ≠ 1) :
    Gal(cyclotomicZpExtension p K L/K) ≃ₜ* Multiplicative ℤ_[p] := by
  have hfin : ¬ IsOfFinOrder γ := by
    intro h
    apply hne
    apply (cyclotomicZpExtensionGaloisEquivRange p K L).injective
    exact (isOfFinOrder_iff_eq_one _).mp
      ((cyclotomicZpExtensionGaloisEquivRange p K L).toMulEquiv.toMonoidHom.isOfFinOrder h) |>.trans
        (map_one _).symm
  exact ((isProP_cyclotomicZpExtensionGalois p K L).padicPowEquiv hγ hfin).symm

/-- The inverse generator coordinate is the generator's `p`-adic power map. -/
@[simp]
theorem cyclotomicZpExtensionGaloisEquivPadicInt_symm_apply
    (γ : Gal(cyclotomicZpExtension p K L/K))
    (hγ : (Subgroup.closure {γ}).topologicalClosure = ⊤) (hne : γ ≠ 1)
    (l : Multiplicative ℤ_[p]) :
    (cyclotomicZpExtensionGaloisEquivPadicInt p K L γ hγ hne).symm l =
      (isProP_cyclotomicZpExtensionGalois p K L).padicPow γ l.toAdd := by
  simp only [cyclotomicZpExtensionGaloisEquivPadicInt, ContinuousMulEquiv.symm_symm,
    IsProP.padicPowEquiv_apply]

/-- The coordinate attached to a generator sends that generator to `1` in additive notation. -/
@[simp]
theorem cyclotomicZpExtensionGaloisEquivPadicInt_apply_generator
    (γ : Gal(cyclotomicZpExtension p K L/K))
    (hγ : (Subgroup.closure {γ}).topologicalClosure = ⊤) (hne : γ ≠ 1) :
    cyclotomicZpExtensionGaloisEquivPadicInt p K L γ hγ hne γ = ofAdd 1 := by
  apply (cyclotomicZpExtensionGaloisEquivPadicInt p K L γ hγ hne).symm.injective
  rw [ContinuousMulEquiv.symm_apply_apply,
    cyclotomicZpExtensionGaloisEquivPadicInt_symm_apply, toAdd_ofAdd, IsProP.padicPow_one]

variable {K L}

/-- A subextension of the full cyclotomic tower with Galois group topologically isomorphic to
`ℤ_p` equals the cyclotomic ℤ_p-extension. -/
theorem cyclotomicZpExtension_unique (M : IntermediateField K C)
    (e : Gal(M/K) ≃ₜ* Multiplicative ℤ_[p]) : M = cyclotomicZpExtension p K L := by
  let F := cyclotomicZpExtension p K L
  let f : Gal(C/K) →* Multiplicative ℤ_[p] :=
    e.toMulEquiv.toMonoidHom.comp (AlgEquiv.restrictNormalHom M)
  have hle : F.fixingSubgroup ≤ f.ker := by
    intro σ hσ
    have hfinite := (mem_torsionCharSubgroup_iff_isOfFinOrder p K L σ).mp
      ((fixingSubgroup_cyclotomicZpExtension p K L) ▸ hσ)
    exact MonoidHom.mem_ker.mpr ((isOfFinOrder_iff_eq_one _).mp (f.isOfFinOrder hfinite))
  let g := QuotientGroup.lift F.fixingSubgroup f hle
  have hg : Continuous g := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <| by
    refine (e.continuous.comp (InfiniteGalois.restrictNormalHom_continuous M)).congr fun σ ↦ ?_
    exact (QuotientGroup.lift_mk' F.fixingSubgroup hle σ).symm
  have hsurj : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ f
    (e.surjective.comp (AlgEquiv.restrictNormalHom_surjective C (F := K) (K₁ := M))) hle
  have hne : (cyclotomicTowerLogCharacter p K L).toMonoidHom.range ≠ ⊥ := by
    rw [← Subgroup.nontrivial_iff_ne_bot]
    let d := (quotientFixingSubgroupEquiv K C F).trans
      (cyclotomicZpExtensionGaloisEquivRange p K L)
    have : Nontrivial (Gal(C/K) ⧸ F.fixingSubgroup) := hsurj.nontrivial
    exact d.injective.nontrivial
  -- The induced surjection becomes an endomorphism of ℤ_p, so it is injective.
  obtain ⟨d⟩ := nonempty_cyclotomicZpExtensionGaloisEquiv_padicInt p K L hne
  let q := d.symm.trans (quotientFixingSubgroupEquiv K C F).symm
  have hinjComp : Function.Injective (g ∘ q) :=
    (isTopologicallyFinitelyGenerated_multiplicative_padicInt p).injective_of_surjective
      (f := g.comp q.toMulEquiv.toMonoidHom) (hg.comp q.continuous) (hsurj.comp q.surjective)
  have hinj := hinjComp.of_comp_right q.surjective
  have hker : F.fixingSubgroup = M.fixingSubgroup :=
    ((QuotientGroup.injective_lift_iff F.fixingSubgroup f hle).mp hinj).trans
      ((MonoidHom.ker_mulEquiv_comp _ e.toMulEquiv).trans M.restrictNormalHom_ker)
  rw [← InfiniteGalois.fixedField_fixingSubgroup M, ← hker,
    InfiniteGalois.fixedField_fixingSubgroup]

end TauCeti
