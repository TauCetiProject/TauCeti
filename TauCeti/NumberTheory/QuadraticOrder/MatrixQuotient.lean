/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import TauCeti.Algebra.QuadraticAlgebra.Discriminant
public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix
public import TauCeti.NumberTheory.QuadraticOrder.LevelTwoMatrix
public import TauCeti.NumberTheory.QuadraticOrder.Reduction

/-!
# Residue-unit quotients of quadratic multiplication matrices

Let `ℤ[ω] = QuadraticAlgebra ℤ a b`, so `ω² = a + bω` and `discr a b = b² + 4a`. Combining the
reduction isomorphism `quotientSpanNatCastEquiv : ℤ[ω]/(N) ≃+* (ℤ/N)[ω]` of
`TauCeti.NumberTheory.QuadraticOrder.Reduction` with the period-matrix representation
`periodUnitMatrixEquiv : ((ℤ/N)[ω])ˣ ≃* periodMatrixGroup (a : ZMod N) (b : ZMod N)` of
`TauCeti.Algebra.QuadraticAlgebra.UnitMatrix` identifies `(ℤ[ω]/(N))ˣ` with the group of
invertible multiplication matrices modulo `N`, and carries the image of the global units `(ℤ[ω])ˣ`
onto the actual reduced unit subgroup `unitPeriodMatrixSubgroup a b N`.

For any commutative ring `R` equipped with a ring isomorphism `e : R ≃+* QuadraticAlgebra ℤ a b`,
this induces a canonical group isomorphism (`residueUnitsQuotientPeriodMatrixEquiv`) between
`(R ⧸ (N))ˣ` modulo the image of `Rˣ` and the matrix quotient
`periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N`.

When `discr a b < -4`, the only integral units of `ℤ[ω]` are `±1`
(`units_eq_one_or_neg_one_of_discr_lt_neg_four`), so `unitPeriodMatrixSubgroup a b N` collapses to
the scalar sign subgroup `Subgroup.zpowers (-1)` (`unitPeriodMatrixSubgroup_eq_zpowers_neg_one`),
and at `N = 2` it is trivial (`unitPeriodMatrixSubgroup_two_of_discr_lt_neg_four`). By contrast,
at the Gaussian (`discr = -4`) and Eisenstein (`discr = -3`) discriminants every level-`2`
multiplication matrix lifts to an integral unit (`unitPeriodMatrixSubgroup_gaussian_two`,
`unitPeriodMatrixSubgroup_eisenstein_two`, `unitPeriodMatrixSubgroup_neg_three_three_two`), so the
level-`2` quotient is trivial whereas the scalar signs reduce trivially modulo `2`.

Finally, over `(a, b) = (0, 0)` in `ZMod 3` — the ramified reduction occurring when `3` divides
both `a` and `b` — the three lower-triangular unipotent matrices `!![1, 0; s, 1]` (`s : ZMod 3`)
form a subgroup isomorphic to `Multiplicative (ZMod 3)` that projects bijectively onto the cosets
modulo `{±I}` (`unipotentPeriodMatrixQuotientEquivZModThree`).

## References

* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §§2, 4.
-/

public noncomputable section

open Matrix

namespace QuadraticAlgebra

/-! ### Reduction of global units into the period-matrix group -/

/-- Reduction of integral units of `QuadraticAlgebra ℤ a b` into the level-`N`
multiplication-matrix group `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
def unitPeriodMatrixHom (a b : ℤ) (N : ℕ) :
    (QuadraticAlgebra ℤ a b)ˣ →* periodMatrixGroup (a : ZMod N) (b : ZMod N) :=
  periodUnitMatrixEquiv.toMonoidHom.comp
    (Units.map (mapRingHom (Int.castRingHom (ZMod N)) a b).toMonoidHom)

/-- Underlying matrix in `GL (Fin 2) (ZMod N)` of `unitPeriodMatrixHom a b N u`. -/
@[simp]
theorem coe_unitPeriodMatrixHom (a b : ℤ) (N : ℕ) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    (unitPeriodMatrixHom a b N u : GL (Fin 2) (ZMod N)) =
      GeneralLinearGroup.map (Int.castRingHom (ZMod N)) (periodUnitMatrix u) := by
  simpa [unitPeriodMatrixHom] using periodUnitMatrix_mapRingHom (Int.castRingHom (ZMod N)) u

/-- `unitPeriodMatrixHom` commutes with negation. -/
@[simp]
theorem unitPeriodMatrixHom_neg (a b : ℤ) (N : ℕ) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    unitPeriodMatrixHom a b N (-u) = -unitPeriodMatrixHom a b N u := by
  apply Subtype.ext
  apply Units.ext
  simp [coe_unitPeriodMatrixHom, GeneralLinearGroup.map]

/-- The subgroup of `periodMatrixGroup (a : ZMod N) (b : ZMod N)` consisting of reductions of
actual integral units of `QuadraticAlgebra ℤ a b`. -/
def unitPeriodMatrixSubgroup (a b : ℤ) (N : ℕ) :
    Subgroup (periodMatrixGroup (a : ZMod N) (b : ZMod N)) :=
  (unitPeriodMatrixHom a b N).range

/-- Unfolding lemma for `unitPeriodMatrixSubgroup`. -/
theorem unitPeriodMatrixSubgroup_def (a b : ℤ) (N : ℕ) :
    unitPeriodMatrixSubgroup a b N = (unitPeriodMatrixHom a b N).range :=
  (rfl)

/-- The units of `ℤ[ω]/(N)` are canonically isomorphic to the level-`N` multiplication-matrix
group `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
def unitsQuotientSpanNatCastPeriodEquiv (a b : ℤ) (N : ℕ) :
    (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})ˣ ≃*
      periodMatrixGroup (a : ZMod N) (b : ZMod N) :=
  (Units.mapEquiv (quotientSpanNatCastEquiv a b N).toMulEquiv).trans periodUnitMatrixEquiv

/-- `unitsQuotientSpanNatCastPeriodEquiv` sends the residue of an integral unit `u` to
`unitPeriodMatrixHom a b N u`. -/
@[simp]
theorem unitsQuotientSpanNatCastPeriodEquiv_map_mk (a b : ℤ) (N : ℕ)
    (u : (QuadraticAlgebra ℤ a b)ˣ) :
    unitsQuotientSpanNatCastPeriodEquiv a b N
        (Units.map (Ideal.Quotient.mk
          (Ideal.span {(N : QuadraticAlgebra ℤ a b)})) u) =
      unitPeriodMatrixHom a b N u := by
  apply Subtype.ext
  apply Units.ext
  simp [unitsQuotientSpanNatCastPeriodEquiv, unitPeriodMatrixHom]

/-- Given a ring isomorphism `e : R ≃+* QuadraticAlgebra ℤ a b`, the units of `R ⧸ (N)` are
canonically isomorphic to `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
def unitsQuotientSpanNatCastPeriodEquivOfRingEquiv {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) :
    (R ⧸ Ideal.span {(N : R)})ˣ ≃* periodMatrixGroup (a : ZMod N) (b : ZMod N) :=
  (Units.mapEquiv (Ideal.quotientEquiv (Ideal.span {(N : R)})
    (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).toMulEquiv).trans
    (unitsQuotientSpanNatCastPeriodEquiv a b N)

/-- `unitsQuotientSpanNatCastPeriodEquivOfRingEquiv` intertwines reduction of `Rˣ` modulo `(N)`
with `unitPeriodMatrixHom` along `e`. -/
@[simp]
theorem unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_map_mk {R : Type*} [CommRing R]
    {a b : ℤ} (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) (u : Rˣ) :
    unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : R)})) u) =
      unitPeriodMatrixHom a b N (Units.map e.toRingHom.toMonoidHom u) := by
  rw [← unitsQuotientSpanNatCastPeriodEquiv_map_mk]
  dsimp only [unitsQuotientSpanNatCastPeriodEquivOfRingEquiv, MulEquiv.trans_apply]
  congr 1

/-- Under `unitsQuotientSpanNatCastPeriodEquivOfRingEquiv`, the image of `Rˣ` in `(R ⧸ (N))ˣ`
maps onto `unitPeriodMatrixSubgroup a b N`. -/
theorem map_range_units_eq_unitPeriodMatrixSubgroup {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) :
    (Units.map (Ideal.Quotient.mk (Ideal.span {(N : R)}) :
        R →* R ⧸ Ideal.span {(N : R)})).range.map
        (unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).toMonoidHom =
      unitPeriodMatrixSubgroup a b N := by
  ext M
  simp only [Subgroup.mem_map, MonoidHom.mem_range, exists_exists_eq_and,
    MulEquiv.coe_toMonoidHom, unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_map_mk,
    unitPeriodMatrixSubgroup_def]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨Units.map e.toRingHom.toMonoidHom u, hu⟩,
    fun ⟨v, hv⟩ ↦ ⟨Units.map e.symm.toRingHom.toMonoidHom v, ?_⟩⟩
  rw [← hv]
  congr 1
  apply Units.ext
  simp

/-- **Matrix presentation of the residue-unit quotient**: any ring isomorphism
`e : R ≃+* QuadraticAlgebra ℤ a b` induces a canonical group isomorphism from `(R ⧸ (N))ˣ`
modulo the image of `Rˣ` onto
`periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N`. -/
def residueUnitsQuotientPeriodMatrixEquiv {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) :
    (R ⧸ Ideal.span {(N : R)})ˣ ⧸
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : R)}) :
          R →* R ⧸ Ideal.span {(N : R)})).range ≃*
      periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N :=
  QuotientGroup.congr _ _ (unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N)
    (map_range_units_eq_unitPeriodMatrixSubgroup e N)

/-- `residueUnitsQuotientPeriodMatrixEquiv` sends the coset of `u` to the coset of
`unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N u`. -/
@[simp]
theorem residueUnitsQuotientPeriodMatrixEquiv_mk {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) (u : (R ⧸ Ideal.span {(N : R)})ˣ) :
    residueUnitsQuotientPeriodMatrixEquiv e N u =
      (unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N u :
        periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N) :=
  (rfl)

/-- The inverse of `residueUnitsQuotientPeriodMatrixEquiv` sends the coset of `M` to the coset of
`(unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M`. -/
@[simp]
theorem residueUnitsQuotientPeriodMatrixEquiv_symm_mk {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ)
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    (residueUnitsQuotientPeriodMatrixEquiv e N).symm M =
      ((unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M :
        (R ⧸ Ideal.span {(N : R)})ˣ ⧸
          (Units.map (Ideal.Quotient.mk (Ideal.span {(N : R)}) :
            R →* R ⧸ Ideal.span {(N : R)})).range) :=
  (rfl)

/-! ### Discriminants strictly below `-4` versus the Gaussian and Eisenstein cases -/

/-- **Units for `discr a b < -4`**: in an integral quadratic algebra of discriminant strictly less
than `-4`, the only units are `1` and `-1`. -/
theorem units_eq_one_or_neg_one_of_discr_lt_neg_four {a b : ℤ} (hd : discr a b < -4)
    (u : (QuadraticAlgebra ℤ a b)ˣ) : u = 1 ∨ u = -1 := by
  have hnorm_unit : IsUnit (norm (u : QuadraticAlgebra ℤ a b)) :=
    isUnit_iff_norm_isUnit.mp u.isUnit
  have hnorm_nonneg : 0 ≤ norm (u : QuadraticAlgebra ℤ a b) :=
    norm_nonneg_of_discr_nonpos (by omega) _
  have hnorm : norm (u : QuadraticAlgebra ℤ a b) = 1 := by
    rcases Int.isUnit_iff.mp hnorm_unit with h1 | h1 <;> omega
  have h4 := four_mul_norm_eq (u : QuadraticAlgebra ℤ a b)
  rw [hnorm, mul_one] at h4
  have him : (u : QuadraticAlgebra ℤ a b).im = 0 := by
    by_contra hne
    have hpos : 0 < (u : QuadraticAlgebra ℤ a b).im ^ 2 := sq_pos_iff.mpr hne
    have : 1 ≤ (u : QuadraticAlgebra ℤ a b).im ^ 2 := by omega
    have : 0 ≤ trace (u : QuadraticAlgebra ℤ a b) ^ 2 := sq_nonneg _
    nlinarith
  rw [him, trace_def, him] at h4
  have hre : (u : QuadraticAlgebra ℤ a b).re = 1 ∨ (u : QuadraticAlgebra ℤ a b).re = -1 :=
    sq_eq_one_iff.mp (by nlinarith)
  rcases hre with h1 | h1
  · left; apply Units.ext; ext <;> simp [h1, him]
  · right; apply Units.ext; ext <;> simp [h1, him]

/-- When `discr a b < -4`, the reduced global-unit subgroup `unitPeriodMatrixSubgroup a b N` is the
scalar sign subgroup `{±I} = Subgroup.zpowers (-1)`. -/
theorem unitPeriodMatrixSubgroup_eq_zpowers_neg_one {a b : ℤ} (hd : discr a b < -4) (N : ℕ) :
    unitPeriodMatrixSubgroup a b N = Subgroup.zpowers (-1) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    rcases units_eq_one_or_neg_one_of_discr_lt_neg_four hd u with rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · rw [Subgroup.zpowers_le]
    exact ⟨-1, by simp⟩

/-- For `discr a b < -4`, rewriting `(a : ZMod N) = a'` and `(b : ZMod N) = b'` identifies
`periodMatrixGroup a' b' ⧸ Subgroup.zpowers (-1)` with
`periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N`. -/
def periodMatrixQuotientEquivZpowersNegOne {a b : ℤ} {N : ℕ} {a' b' : ZMod N}
    (hd : discr a b < -4) (ha : (a : ZMod N) = a') (hb : (b : ZMod N) = b') :
    periodMatrixGroup a' b' ⧸ Subgroup.zpowers (-1 : periodMatrixGroup a' b') ≃*
      periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N :=
  let hgrp : periodMatrixGroup a' b' = periodMatrixGroup (a : ZMod N) (b : ZMod N) := by
    rw [ha, hb]
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hgrp) <| by
    rw [unitPeriodMatrixSubgroup_eq_zpowers_neg_one hd N]
    subst ha
    subst hb
    rw [MonoidHom.map_zpowers]
    congr 1

/-- `periodMatrixQuotientEquivZpowersNegOne` sends the coset of `M` to the coset of the same
matrix viewed in `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
@[simp]
theorem periodMatrixQuotientEquivZpowersNegOne_mk {a b : ℤ} {N : ℕ} {a' b' : ZMod N}
    (hd : discr a b < -4) (ha : (a : ZMod N) = a') (hb : (b : ZMod N) = b')
    (M : periodMatrixGroup a' b') :
    periodMatrixQuotientEquivZpowersNegOne hd ha hb M =
      (⟨(M : GL (Fin 2) (ZMod N)), by rw [ha, hb]; exact M.2⟩ :
        periodMatrixGroup (a : ZMod N) (b : ZMod N)) :=
  (rfl)

/-- At level `2`, `-1 = 1` in `periodMatrixGroup`, so for `discr a b < -4` the reduced global-unit
subgroup is trivial and the quotient collapses to `periodMatrixGroup (a : ZMod 2) (b : ZMod 2)`
itself. -/
@[simp]
theorem unitPeriodMatrixSubgroup_two_of_discr_lt_neg_four {a b : ℤ} (hd : discr a b < -4) :
    unitPeriodMatrixSubgroup a b 2 = ⊥ := by
  rw [unitPeriodMatrixSubgroup_eq_zpowers_neg_one hd 2, Subgroup.zpowers_eq_bot]
  apply Subtype.ext
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ZMod.neg_eq_self_mod_two]

/-- In the Gaussian integer algebra (`a = -1`, `b = 0`, `discr = -4`), the reduced global-unit
subgroup at level `2` is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_gaussian_two :
    unitPeriodMatrixSubgroup (-1) 0 2 = ⊤ := by
  rw [unitPeriodMatrixSubgroup_def, MonoidHom.range_eq_top]
  exact periodUnitMatrixEquiv.surjective.comp units_map_zmod_two_gaussian_surjective

/-- In the Eisenstein integer algebra (`a = -1`, `b = 1`, `discr = -3`), the reduced global-unit
subgroup at level `2` is the entire multiplication-matrix group. -/
@[simp]
theorem unitPeriodMatrixSubgroup_eisenstein_two :
    unitPeriodMatrixSubgroup (-1) 1 2 = ⊤ := by
  rw [unitPeriodMatrixSubgroup_def, MonoidHom.range_eq_top]
  exact periodUnitMatrixEquiv.surjective.comp units_map_zmod_two_eisenstein_surjective

/-- In the `(1, (3 + i√3)/2)` presentation of the Eisenstein integers (`a = -3`, `b = 3`,
`discr = -3`), every level-`2` multiplication matrix likewise lifts to an integral unit (`1`,
`ω - 1`, or `(ω - 1)²`). -/
@[simp]
theorem unitPeriodMatrixSubgroup_neg_three_three_two :
    unitPeriodMatrixSubgroup (-3) 3 2 = ⊤ := by
  rw [unitPeriodMatrixSubgroup_def, MonoidHom.range_eq_top]
  refine periodUnitMatrixEquiv.surjective.comp fun u ↦ ?_
  have hζ : IsUnit (⟨-1, 1⟩ : QuadraticAlgebra ℤ (-3) 3) :=
    isUnit_iff_norm_isUnit.mpr (by norm_num [norm_def])
  have hu := isUnit_iff_norm_isUnit.mp u.isUnit
  have h3 : (3 : ZMod 2) = 1 := by decide
  have key : ∀ t s : ZMod 2, IsUnit (t ^ 2 + t * s + s ^ 2) →
      (t = 1 ∧ s = 0) ∨ (t = 1 ∧ s = 1) ∨ (t = 0 ∧ s = 1) := by decide
  have hn : IsUnit (u.val.re ^ 2 + u.val.re * u.val.im + u.val.im ^ 2) := by
    simpa [norm_def, sq, h3, sub_eq_add_neg, ZMod.neg_eq_self_mod_two] using hu
  rcases key _ _ hn with h | h | h
  · refine ⟨1, Units.ext ?_⟩
    ext <;> simp [h.1, h.2]
  · refine ⟨hζ.unit, Units.ext ?_⟩
    ext <;> simp [mapRingHom, h.1, h.2]
  · refine ⟨hζ.unit ^ 2, Units.ext ?_⟩
    ext <;> simp [mapRingHom, sq, h.1, h.2, h3, CharTwo.add_self_eq_zero]

/-! ### Unipotent coset representatives over `(0, 0)` at level `3` -/

/-- Over `(a, b) = (0, 0)` (where `ω² = 0`), the unipotent unit `1 + sω` has multiplication
matrix `!![1, 0; s, 1]`, giving `Multiplicative R →* periodMatrixGroup (0 : R) (0 : R)`. -/
def unipotentPeriodMatrixHom (R : Type*) [CommRing R] :
    Multiplicative R →* periodMatrixGroup (0 : R) (0 : R) where
  toFun s := periodUnitMatrixEquiv
    { val := ⟨1, s.toAdd⟩
      inv := ⟨1, -s.toAdd⟩
      val_inv := by ext <;> simp
      inv_val := by ext <;> simp }
  map_one' := by
    rw [← map_one periodUnitMatrixEquiv]
    congr 1
    apply Units.ext
    ext <;> simp
  map_mul' s t := by
    rw [← map_mul periodUnitMatrixEquiv]
    congr 1
    apply Units.ext
    ext <;> simp [add_comm]

/-- Underlying `2 × 2` matrix of `unipotentPeriodMatrixHom R (Multiplicative.ofAdd s)`. -/
@[simp]
theorem coe_unipotentPeriodMatrixHom {R : Type*} [CommRing R] (s : R) :
    (((unipotentPeriodMatrixHom R (Multiplicative.ofAdd s) :
        periodMatrixGroup (0 : R) (0 : R)) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      !![1, 0; s, 1] := by
  simp [unipotentPeriodMatrixHom, periodMulMatrix_eq]

/-- Injectivity of the composite `Multiplicative (ZMod 3) →* periodMatrixGroup 0 0 ⧸ {±I}`. -/
private theorem unipotentPeriodMatrixHom_mk_injective :
    Function.Injective
      ((QuotientGroup.mk'
          (Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)))).comp
        (unipotentPeriodMatrixHom (ZMod 3))) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro s hs
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hs
  obtain ⟨k, hk⟩ := hs
  have hneg1 : (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)) =
      periodUnitMatrixEquiv (-1) := by
    simp
  rw [hneg1, ← map_zpow] at hk
  have hu := periodUnitMatrixEquiv.injective hk
  have him := congrArg (fun u : (QuadraticAlgebra (ZMod 3) 0 0)ˣ ↦ u.val.im) hu
  have hneg_im :
      (((-1 : (QuadraticAlgebra (ZMod 3) 0 0)ˣ) ^ k :
        (QuadraticAlgebra (ZMod 3) 0 0)ˣ) : QuadraticAlgebra (ZMod 3) 0 0).im = 0 := by
    rcases Int.even_or_odd k with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · simp [← two_mul, zpow_mul]
    · simp [zpow_add, zpow_mul]
  rw [hneg_im] at him
  exact Multiplicative.toAdd.injective him.symm

/-- Surjectivity of the composite `Multiplicative (ZMod 3) →* periodMatrixGroup 0 0 ⧸ {±I}`. -/
private theorem unipotentPeriodMatrixHom_mk_surjective :
    Function.Surjective
      ((QuotientGroup.mk'
          (Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)))).comp
        (unipotentPeriodMatrixHom (ZMod 3))) := by
  intro x
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨u, rfl⟩ := periodUnitMatrixEquiv.surjective M
  have hu : IsUnit u.val.re := by
    simpa [norm_def, sq] using isUnit_iff_norm_isUnit.mp u.isUnit
  have hre : u.val.re = 1 ∨ u.val.re = -1 :=
    (show ∀ t : ZMod 3, IsUnit t → t = 1 ∨ t = -1 by decide) u.val.re hu
  rcases hre with h1 | h1
  · refine ⟨Multiplicative.ofAdd u.val.im, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    congr 1
    dsimp only [unipotentPeriodMatrixHom, MonoidHom.coe_mk, OneHom.coe_mk]
    congr 1
    apply Units.ext
    ext <;> simp [h1]
  · refine ⟨Multiplicative.ofAdd (-u.val.im), ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_zpowers_iff]
    refine ⟨1, ?_⟩
    rw [zpow_one, show (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)) =
      periodUnitMatrixEquiv (-1) by simp]
    dsimp only [unipotentPeriodMatrixHom, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← map_inv, ← map_mul]
    congr 1
    apply Units.ext
    ext <;> simp [h1]

/-- Bijectivity of the composite `Multiplicative (ZMod 3) →* periodMatrixGroup 0 0 ⧸ {±I}`. -/
private theorem unipotentPeriodMatrixHom_mk_bijective :
    Function.Bijective
      ((QuotientGroup.mk'
          (Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)))).comp
        (unipotentPeriodMatrixHom (ZMod 3))) :=
  ⟨unipotentPeriodMatrixHom_mk_injective, unipotentPeriodMatrixHom_mk_surjective⟩

/-- Over `ZMod 3` with `(a, b) = (0, 0)`, the three lower-triangular unipotent matrices
`!![1, 0; s, 1]` (`s : ZMod 3`) form a complete, irredundant set of coset representatives for
`periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸ Subgroup.zpowers (-1)`. -/
def unipotentPeriodMatrixQuotientEquivZModThree :
    Multiplicative (ZMod 3) ≃*
      periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸
        Subgroup.zpowers (-1 : periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3)) :=
  MulEquiv.ofBijective
    ((QuotientGroup.mk' _).comp (unipotentPeriodMatrixHom (ZMod 3)))
    unipotentPeriodMatrixHom_mk_bijective

/-- `unipotentPeriodMatrixQuotientEquivZModThree` sends `Multiplicative.ofAdd s` to the coset of
`unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s)`. -/
@[simp]
theorem unipotentPeriodMatrixQuotientEquivZModThree_ofAdd (s : ZMod 3) :
    unipotentPeriodMatrixQuotientEquivZModThree (Multiplicative.ofAdd s) =
      (unipotentPeriodMatrixHom (ZMod 3) (Multiplicative.ofAdd s) :
        periodMatrixGroup (0 : ZMod 3) (0 : ZMod 3) ⧸ Subgroup.zpowers (-1)) := by
  simp [unipotentPeriodMatrixQuotientEquivZModThree]

end QuadraticAlgebra
