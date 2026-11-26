/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.Quotient
public import TauCeti.NumberTheory.Cyclotomic.Tower
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Quotient
import Mathlib.Topology.Maps.Strict.Group
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.FiniteExtension
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Range
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Rational
import TauCeti.Topology.Algebra.Group.Profinite.Hopfian
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.ClosedSubgroups

/-!
# The cyclotomic ℤ_p-extension of a number field

Inside the full cyclotomic tower `K(μ_{p^∞})`, take the fixed field of the finite-order
automorphisms. The logarithmic coordinate of the cyclotomic character identifies the
Galois group of this fixed field with an open subgroup of the additive group of `ℤ_p`.
Thus this is the unique subextension of the full tower with Galois group topologically
isomorphic to `ℤ_p`. In a common Galois overfield the construction commutes with base
change by compositum.

The construction includes `p = 2`: a cyclotomic character value with nontrivial sign
can have infinite order. The subgroup used in the fixed field consists of the actual
torsion automorphisms.

## Reference

* R. Sharifi, *Iwasawa Theory*, Remark 3.1.4, Lemma 3.1.7 and Definition 3.1.8.
-/

public section

open IntermediateField Multiplicative

namespace TauCeti

variable (p : ℕ) [Fact p.Prime] (K L : Type*) [Field K] [Field L] [Algebra K L]
  [∀ i, HasEnoughRootsOfUnity L (p ^ i)]

local notation "C" => cyclotomicTower p K L

/-- The normalized logarithmic coordinate of the full cyclotomic character. -/
noncomputable def cyclotomicTowerLogCharacter : Gal(C/K) →ₜ* Multiplicative ℤ_[p] :=
  (ContinuousMonoidHom.snd _ _).comp
    ((ContinuousMonoidHom.toContinuousMonoidHom (padicIntUnitsEquivZModUnitsProd p)).comp
      ⟨cyclotomicTowerCharacter p K L, continuous_cyclotomicTowerCharacter p K L⟩)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
@[simp]
theorem cyclotomicTowerLogCharacter_apply (σ : Gal(C/K)) :
    cyclotomicTowerLogCharacter p K L σ =
      (padicIntUnitsEquivZModUnitsProd p (cyclotomicTowerCharacter p K L σ)).2 :=
  (rfl)

/-- The subgroup of finite-order automorphisms of the full cyclotomic tower. -/
noncomputable def torsionCharSubgroup : Subgroup Gal(C/K) :=
  (CommGroup.torsion ℤ_[p]ˣ).comap (cyclotomicTowerCharacter p K L)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The torsion subgroup is the preimage of torsion in the p-adic units. -/
theorem mem_torsionCharSubgroup_iff (σ : Gal(C/K)) :
    σ ∈ torsionCharSubgroup p K L ↔
      cyclotomicTowerCharacter p K L σ ∈ CommGroup.torsion ℤ_[p]ˣ :=
  Iff.rfl

/-- A torsion automorphism is exactly an automorphism of finite order. -/
theorem mem_torsionCharSubgroup_iff_isOfFinOrder (σ : Gal(C/K)) :
    σ ∈ torsionCharSubgroup p K L ↔ IsOfFinOrder σ :=
  (mem_torsionCharSubgroup_iff p K L σ).trans <|
    (CommGroup.mem_torsion _).trans (cyclotomicTowerCharacter_injective p K L).isOfFinOrder_iff

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- The logarithmic coordinate kills exactly the torsion in the full cyclotomic group. -/
@[simp]
theorem ker_cyclotomicTowerLogCharacter :
    (↑(cyclotomicTowerLogCharacter p K L) : Gal(C/K) →* Multiplicative ℤ_[p]).ker =
      torsionCharSubgroup p K L := by
  ext σ
  rw [mem_torsionCharSubgroup_iff, mem_torsion_padicIntUnits_iff]
  rw [MonoidHom.mem_ker]
  exact Iff.of_eq (congrArg (· = 1) (cyclotomicTowerLogCharacter_apply p K L σ))

/-- The torsion in the full cyclotomic group embeds in the finite torsion in `ℤ_pˣ`. -/
instance finite_torsionCharSubgroup : Finite (torsionCharSubgroup p K L) := by
  have hfin : (↑(CommGroup.torsion ℤ_[p]ˣ) : Set ℤ_[p]ˣ).Finite := by
    rw [torsion_padicIntUnits_eq_range_section, MonoidHom.coe_range]
    exact Set.finite_range _
  have hset : (↑(torsionCharSubgroup p K L) : Set Gal(C/K)) =
      cyclotomicTowerCharacter p K L ⁻¹' (↑(CommGroup.torsion ℤ_[p]ˣ) : Set ℤ_[p]ˣ) :=
    Set.ext (mem_torsionCharSubgroup_iff p K L)
  apply Set.finite_coe_iff.mpr
  rw [hset]
  exact hfin.preimage (cyclotomicTowerCharacter_injective p K L).injOn

/-- The cyclotomic ℤ_p-extension is the subfield of `K(μ_{p^∞})` fixed by its torsion
automorphisms. -/
noncomputable def cyclotomicZpExtension : IntermediateField K C :=
  fixedField (torsionCharSubgroup p K L)

omit [∀ i, HasEnoughRootsOfUnity L (p ^ i)] in
/-- An element of the full tower lies in the cyclotomic ℤ_p-extension if every torsion
automorphism fixes it. -/
theorem mem_cyclotomicZpExtension_iff {x : C} :
    x ∈ cyclotomicZpExtension p K L ↔ ∀ σ ∈ torsionCharSubgroup p K L, σ x = x :=
  mem_fixedField_iff (torsionCharSubgroup p K L) x

@[simp]
theorem fixingSubgroup_cyclotomicZpExtension :
    (cyclotomicZpExtension p K L).fixingSubgroup = torsionCharSubgroup p K L := by
  have hclosed : IsClosed (↑(torsionCharSubgroup p K L) : Set Gal(C/K)) := by
    rw [← ker_cyclotomicTowerLogCharacter]
    exact isClosed_singleton.preimage (cyclotomicTowerLogCharacter p K L).continuous
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨torsionCharSubgroup p K L, hclosed⟩

/-- The full cyclotomic tower is the cyclotomic ℤ_p-extension exactly when its
Galois group has trivial torsion. -/
@[simp]
theorem cyclotomicZpExtension_eq_top_iff :
    cyclotomicZpExtension p K L = ⊤ ↔ torsionCharSubgroup p K L = ⊥ := by
  rw [← fixingSubgroup_cyclotomicZpExtension, ← fixingSubgroup_top (F := K) (E := C)]
  exact ⟨congrArg fixingSubgroup, fun h ↦ by
    simpa only [InfiniteGalois.fixedField_fixingSubgroup] using congrArg fixedField h⟩

/-- If the base contains a primitive root of unity of order `p` for odd `p`, or of order
four for `p = 2`, the full cyclotomic group is torsion-free. -/
theorem torsionCharSubgroup_eq_bot_of_isPrimitiveRoot {ζ : K}
    (hζ : IsPrimitiveRoot ζ (p ^ padicUnitsDepth p)) :
    torsionCharSubgroup p K L = ⊥ := by
  have hrange : (cyclotomicTowerCharacter p K L).range ≤ unitsPrincipal p (padicUnitsDepth p) := by
    rw [range_cyclotomicTowerCharacter]
    exact range_localCyclotomicCharacter_le_unitsPrincipal ⟨ζ, hζ⟩
  apply eq_bot_iff.mpr
  intro σ hσ
  let u := cyclotomicTowerCharacter p K L σ
  have hfst : (padicIntUnitsEquivZModUnitsProd p u).1 = 1 := by
    rw [padicIntUnitsEquivZModUnitsProd_apply_fst, unitsToZModPow_eq_one_iff]
    exact hrange ⟨σ, rfl⟩
  have hsnd : (padicIntUnitsEquivZModUnitsProd p u).2 = 1 :=
    (mem_torsion_padicIntUnits_iff p u).mp ((mem_torsionCharSubgroup_iff p K L σ).mp hσ)
  have hu : u = 1 := (padicIntUnitsEquivZModUnitsProd p).injective (by
    rw [map_one]
    exact Prod.ext hfst hsnd)
  exact Subgroup.mem_bot.mpr ((injective_iff_map_eq_one _).mp
    (cyclotomicTowerCharacter_injective p K L) σ hu)

section Dyadic

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [∀ i, HasEnoughRootsOfUnity L (2 ^ i)]

/-- If the base contains a square root of `-2`, its full dyadic cyclotomic group is
torsion-free. The sign unit `-1` is excluded by the character image modulo eight. -/
theorem torsionCharSubgroup_two_eq_bot_of_sq_eq_neg_two {s : K} (hs : s ^ 2 = -2) :
    torsionCharSubgroup 2 K L = ⊥ := by
  apply eq_bot_iff.mpr
  intro σ hσ
  have hχ := (mem_torsionCharSubgroup_iff 2 K L σ).mp hσ
  rw [torsion_padicIntUnits_two] at hχ
  have hu : cyclotomicTowerCharacter 2 K L σ = 1 := by
    rcases Subgroup.mem_zpowers_neg_one_iff.mp hχ with hu | hu
    · exact hu
    have hmem : cyclotomicTowerCharacter 2 K L σ ∈ (cyclotomicTowerCharacter 2 K L).range :=
      ⟨σ, rfl⟩
    rw [range_cyclotomicTowerCharacter] at hmem
    obtain ⟨τ, hτ⟩ := hmem
    have hmod := toZModPow_three_localCyclotomicCharacter_eq_one_or_eq_three hs τ
    rw [hτ, hu, Units.val_neg, Units.val_one, map_neg, map_one] at hmod
    have hne : (-1 : ZMod (2 ^ 3)) ≠ 1 ∧ (-1 : ZMod (2 ^ 3)) ≠ 3 := by decide
    exact (hmod.elim hne.1 hne.2).elim
  exact Subgroup.mem_bot.mpr ((injective_iff_map_eq_one _).mp
    (cyclotomicTowerCharacter_injective 2 K L) σ hu)

end Dyadic

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

@[simp]
theorem coe_cyclotomicZpExtensionGaloisEquivRange_restrictNormalHom (σ : Gal(C/K)) :
    (cyclotomicZpExtensionGaloisEquivRange p K L
      (AlgEquiv.restrictNormalHom (cyclotomicZpExtension p K L) σ) : Multiplicative ℤ_[p]) =
      cyclotomicTowerLogCharacter p K L σ := by
  simp only [cyclotomicZpExtensionGaloisEquivRange, ContinuousMulEquiv.trans_apply,
    quotientFixingSubgroupEquiv_symm_restrictNormalHom, ContinuousMulEquiv.quotientCongr_mk]
  rfl

/-- In the ambient field, an automorphism fixes the cyclotomic ℤ_p-extension precisely
when its cyclotomic character has finite order. -/
theorem mem_fixingSubgroup_lift_cyclotomicZpExtension_iff (σ : Gal(L/K)) :
    σ ∈ (IntermediateField.lift (cyclotomicZpExtension p K L)).fixingSubgroup ↔
      cyclotomicCharacter L p σ.toRingEquiv ∈ CommGroup.torsion ℤ_[p]ˣ := by
  have h : (IntermediateField.lift (cyclotomicZpExtension p K L)).fixingSubgroup = _ :=
    IntermediateField.map_fixingSubgroup (E' := L) (cyclotomicZpExtension p K L)
  rw [fixingSubgroup_cyclotomicZpExtension] at h
  rw [h, Subgroup.mem_comap, mem_torsionCharSubgroup_iff,
    cyclotomicTowerCharacter_restrictNormalHom]

variable {K L} in
/-- In a common Galois overfield, the cyclotomic ℤ_p-extension of an intermediate field
is its compositum with the cyclotomic ℤ_p-extension of the base. -/
theorem cyclotomicZpExtension_baseChange [IsGalois K L] (E : IntermediateField K L) :
    (IntermediateField.lift (cyclotomicZpExtension p E L)).restrictScalars K =
      E ⊔ IntermediateField.lift (cyclotomicZpExtension p K L) := by
  let A := IntermediateField.lift (cyclotomicZpExtension p K L)
  let B := IntermediateField.lift (cyclotomicZpExtension p E L)
  let r : Gal(L/E) →* Gal(L/K) := AlgEquiv.restrictScalarsHom K
  have hB : B.fixingSubgroup = A.fixingSubgroup.comap r := by
    ext σ
    rw [Subgroup.mem_comap, mem_fixingSubgroup_lift_cyclotomicZpExtension_iff,
      mem_fixingSubgroup_lift_cyclotomicZpExtension_iff]
    rfl
  have hmap : B.fixingSubgroup.map r = (E ⊔ A).fixingSubgroup := by
    rw [hB, Subgroup.map_comap_eq, fixingSubgroup_sup]
    have hr : r.range = E.fixingSubgroup :=
      (range_restrictScalarsHom_eq_embeddingSubgroup K E L).trans
        (embeddingSubgroup_intermediateField K L E)
    rw [hr]
  have hfixed : (fixedField B.fixingSubgroup).restrictScalars K =
      fixedField (B.fixingSubgroup.map r) := by
    ext x
    simp only [mem_restrictScalars, mem_fixedField_iff, Subgroup.mem_map]
    constructor
    · rintro h _ ⟨τ, hτ, rfl⟩
      exact h τ hτ
    · intro h τ hτ
      exact h (r τ) ⟨τ, hτ, rfl⟩
  rw [hmap, InfiniteGalois.fixedField_fixingSubgroup,
    InfiniteGalois.fixedField_fixingSubgroup] at hfixed
  exact hfixed

variable [Algebra ℚ K] [FiniteDimensional ℚ K]

/-- Over a number field the full cyclotomic character has open image in `ℤ_pˣ`. -/
theorem isOpen_range_cyclotomicTowerCharacter_of_finite_rat :
    IsOpen ((cyclotomicTowerCharacter p K L).range : Set ℤ_[p]ˣ) := by
  rw [range_cyclotomicTowerCharacter]
  have hindex := relIndex_range_localCyclotomicCharacter_dvd_finrank p ℚ K
  rw [MonoidHom.range_eq_top.mpr (surjective_localCyclotomicCharacter_rat p),
    Subgroup.relIndex_top_right] at hindex
  have : (localCyclotomicCharacter p K).range.FiniteIndex :=
    ⟨ne_zero_of_dvd_ne_zero Module.finrank_pos.ne' hindex⟩
  exact Subgroup.isOpen_of_isClosed_of_finiteIndex _ (isClosed_range_localCyclotomicCharacter p K)

/-- The logarithmic cyclotomic character of a number field has open image in `ℤ_p`. -/
theorem isOpen_range_cyclotomicTowerLogCharacter :
    IsOpen ((cyclotomicTowerLogCharacter p K L).toMonoidHom.range :
      Set (Multiplicative ℤ_[p])) := by
  rw [MonoidHom.coe_range]
  have hmap : IsOpenMap (Prod.snd ∘ padicIntUnitsEquivZModUnitsProd p) :=
    isOpenMap_snd.comp (padicIntUnitsEquivZModUnitsProd p).toHomeomorph.isOpenMap
  have heq : ⇑(cyclotomicTowerLogCharacter p K L).toMonoidHom =
      (Prod.snd ∘ padicIntUnitsEquivZModUnitsProd p) ∘ cyclotomicTowerCharacter p K L :=
    funext (cyclotomicTowerLogCharacter_apply p K L)
  rw [heq, Set.range_comp, ← MonoidHom.coe_range]
  exact hmap _ (isOpen_range_cyclotomicTowerCharacter_of_finite_rat p K L)

/-- The cyclotomic ℤ_p-extension has Galois group topologically isomorphic to `ℤ_p`. -/
theorem nonempty_cyclotomicZpExtensionGaloisEquiv :
    Nonempty (Gal(cyclotomicZpExtension p K L/K) ≃ₜ* Multiplicative ℤ_[p]) := by
  let H : OpenSubgroup (Multiplicative ℤ_[p]) :=
    ⟨(cyclotomicTowerLogCharacter p K L).toMonoidHom.range,
      isOpen_range_cyclotomicTowerLogCharacter p K L⟩
  obtain ⟨e⟩ := H.nonempty_continuousMulEquiv_padicInt
  exact ⟨(cyclotomicZpExtensionGaloisEquivRange p K L).trans e⟩

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
  have hg : Continuous g := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (e.continuous.comp (InfiniteGalois.restrictNormalHom_continuous M))
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨σ, hσ⟩ := (e.surjective.comp
      (AlgEquiv.restrictNormalHom_surjective C (F := K) (K₁ := M))) x
    exact ⟨QuotientGroup.mk σ, hσ⟩
  -- The induced surjection becomes an endomorphism of ℤ_p, so it is injective.
  obtain ⟨d⟩ := nonempty_cyclotomicZpExtensionGaloisEquiv p K L
  let q := d.symm.trans (quotientFixingSubgroupEquiv K C F).symm
  have hinjComp : Function.Injective (g ∘ q) :=
    (isTopologicallyFinitelyGenerated_multiplicative_padicInt p).injective_of_surjective
      (f := g.comp q.toMulEquiv.toMonoidHom) (hg.comp q.continuous) (hsurj.comp q.surjective)
  have hinj := hinjComp.of_comp_right q.surjective
  have hker : M.fixingSubgroup = F.fixingSubgroup := by
    ext σ
    rw [← M.restrictNormalHom_ker, MonoidHom.mem_ker, ← QuotientGroup.eq_one_iff]
    calc
      AlgEquiv.restrictNormalHom M σ = 1 ↔ e (AlgEquiv.restrictNormalHom M σ) = e 1 :=
        e.injective.eq_iff.symm
      _ ↔ g (QuotientGroup.mk σ) = g 1 := by simp [g, f]
      _ ↔ QuotientGroup.mk σ = (1 : Gal(C/K) ⧸ F.fixingSubgroup) := hinj.eq_iff
  rw [← InfiniteGalois.fixedField_fixingSubgroup M, hker,
    InfiniteGalois.fixedField_fixingSubgroup]

end TauCeti
