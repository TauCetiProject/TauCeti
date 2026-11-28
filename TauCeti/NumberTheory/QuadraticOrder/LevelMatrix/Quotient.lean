/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.QuadraticAlgebra.Discriminant
public import TauCeti.Algebra.QuadraticAlgebra.UnitMatrix
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
the scalar sign subgroup `Subgroup.zpowers (-1)` (`unitPeriodMatrixSubgroup_eq_zpowers_neg_one`).
For every negative discriminant and `N ≥ 3`, reduction of units is injective
(`unitPeriodMatrixHom_injective`), so `unitPeriodMatrixSubgroup a b N` has as many elements as
`(ℤ[ω])ˣ` (`natCard_unitPeriodMatrixSubgroup_of_three_le`).
For equal discriminants, `unitPeriodMatrixSubgroup_eq_top_of_discr_eq` transports surjectivity
(`= ⊤`) across models. For the level-`2` specializations (including the Gaussian and Eisenstein
exceptions), see `TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Two.Quotient`; for the level-`3`
unipotent coset representatives over `(a, b) = (0, 0)` in `ZMod 3`, see
`TauCeti.NumberTheory.QuadraticOrder.LevelMatrix.Three`.

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

/-- Evaluation of `unitPeriodMatrixHom`. -/
theorem unitPeriodMatrixHom_apply (a b : ℤ) (N : ℕ) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    unitPeriodMatrixHom a b N u =
      periodUnitMatrixEquiv
        (Units.map (mapRingHom (Int.castRingHom (ZMod N)) a b).toMonoidHom u) :=
  (rfl)

/-- Underlying matrix in `GL (Fin 2) (ZMod N)` of `unitPeriodMatrixHom a b N u`. -/
@[simp]
theorem coe_unitPeriodMatrixHom (a b : ℤ) (N : ℕ) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    (unitPeriodMatrixHom a b N u : GL (Fin 2) (ZMod N)) =
      GeneralLinearGroup.map (Int.castRingHom (ZMod N)) (periodUnitMatrix u) := by
  simpa [unitPeriodMatrixHom] using periodUnitMatrix_mapRingHom (Int.castRingHom (ZMod N)) u

/-- For `discr a b ≤ 0`, `unitPeriodMatrixHom a b N u` is the reduction modulo `N` of the
`SL(2, ℤ)` matrix `periodUnitSLMatrix hd u`. -/
theorem coe_unitPeriodMatrixHom_eq_toGL_map {a b : ℤ} (hd : discr a b ≤ 0) (N : ℕ)
    (u : (QuadraticAlgebra ℤ a b)ˣ) :
    (unitPeriodMatrixHom a b N u : GL (Fin 2) (ZMod N)) =
      SpecialLinearGroup.toGL
        (SpecialLinearGroup.map (Int.castRingHom (ZMod N)) (periodUnitSLMatrix hd u)) :=
  Units.ext (by simp)

/-- `unitPeriodMatrixHom` commutes with negation. -/
@[simp]
theorem unitPeriodMatrixHom_neg (a b : ℤ) (N : ℕ) (u : (QuadraticAlgebra ℤ a b)ˣ) :
    unitPeriodMatrixHom a b N (-u) = -unitPeriodMatrixHom a b N u :=
  Subtype.ext <| Units.ext <| by simp [coe_unitPeriodMatrixHom, GeneralLinearGroup.map]

/-- The subgroup of `periodMatrixGroup (a : ZMod N) (b : ZMod N)` consisting of reductions of
actual integral units of `QuadraticAlgebra ℤ a b`. -/
def unitPeriodMatrixSubgroup (a b : ℤ) (N : ℕ) :
    Subgroup (periodMatrixGroup (a : ZMod N) (b : ZMod N)) :=
  (unitPeriodMatrixHom a b N).range

/-- Unfolding lemma for `unitPeriodMatrixSubgroup`. -/
theorem unitPeriodMatrixSubgroup_def (a b : ℤ) (N : ℕ) :
    unitPeriodMatrixSubgroup a b N = (unitPeriodMatrixHom a b N).range := (rfl)

/-- A period matrix lies in `unitPeriodMatrixSubgroup a b N` if and only if it is the reduction
of an integral unit of `QuadraticAlgebra ℤ a b`. -/
@[simp]
theorem mem_unitPeriodMatrixSubgroup_iff {a b : ℤ} {N : ℕ}
    {M : periodMatrixGroup (a : ZMod N) (b : ZMod N)} :
    M ∈ unitPeriodMatrixSubgroup a b N ↔ ∃ u, unitPeriodMatrixHom a b N u = M :=
  Iff.rfl

/-- **Reduction of units is injective at levels `N ≥ 3`**: for a negative discriminant, the only
integral unit whose multiplication matrix is the identity modulo `N` is `1`. -/
theorem unitPeriodMatrixHom_injective {a b : ℤ} (hd : discr a b < 0) {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (unitPeriodMatrixHom a b N) := by
  rw [injective_iff_map_eq_one]
  intro u hu
  have h := congrArg (fun M : periodMatrixGroup (a : ZMod N) (b : ZMod N) ↦
    ((M : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) hu
  have him : (N : ℤ) ∣ (u : QuadraticAlgebra ℤ a b).im :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp <| by
      simpa [periodMulMatrix_eq, GeneralLinearGroup.map] using congrFun (congrFun h 1) 0
  have hre : (N : ℤ) ∣ (u : QuadraticAlgebra ℤ a b).re - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp <| by
      simpa [periodMulMatrix_eq, GeneralLinearGroup.map, sub_eq_zero] using
        congrFun (congrFun h 1) 1
  -- a unit is `±1` or has `im = ±1`, and neither `-1` nor `im = ±1` is `1` modulo `N ≥ 3`
  rcases units_re_or_im_of_discr_lt_zero hd u with (h1 | h1) | h1
  · exact h1
  · subst h1
    have h2 : (N : ℤ) ∣ 2 := by
      rw [← dvd_neg]
      simpa using hre
    have := Int.le_of_dvd two_pos h2
    omega
  · have := Int.le_of_dvd one_pos (by rcases h1 with h1 | h1 <;> simpa [h1] using him)
    omega

/-- For a negative discriminant and `N ≥ 3`, the reduced global-unit subgroup
`unitPeriodMatrixSubgroup a b N` has as many elements as the unit group of
`QuadraticAlgebra ℤ a b`. -/
theorem natCard_unitPeriodMatrixSubgroup_of_three_le {a b : ℤ} (hd : discr a b < 0) {N : ℕ}
    (hN : 3 ≤ N) :
    Nat.card (unitPeriodMatrixSubgroup a b N) = Nat.card (QuadraticAlgebra ℤ a b)ˣ :=
  (Nat.card_congr (MonoidHom.ofInjective (unitPeriodMatrixHom_injective hd hN)).toEquiv).symm

/-- The units of `ℤ[ω]/(N)` are canonically isomorphic to the level-`N` multiplication-matrix
group `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
def unitsQuotientSpanNatCastPeriodEquiv (a b : ℤ) (N : ℕ) :
    (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})ˣ ≃*
      periodMatrixGroup (a : ZMod N) (b : ZMod N) :=
  (Units.mapEquiv (quotientSpanNatCastEquiv a b N).toMulEquiv).trans periodUnitMatrixEquiv

/-- Evaluation of `unitsQuotientSpanNatCastPeriodEquiv` on an arbitrary residue unit via
`quotientSpanNatCastEquiv` and `periodUnitMatrixEquiv`. -/
theorem unitsQuotientSpanNatCastPeriodEquiv_apply (a b : ℤ) (N : ℕ)
    (u : (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})ˣ) :
    unitsQuotientSpanNatCastPeriodEquiv a b N u =
      periodUnitMatrixEquiv (Units.map (quotientSpanNatCastEquiv a b N).toRingHom.toMonoidHom u) :=
  Subtype.ext <| Units.ext <| by simp [unitsQuotientSpanNatCastPeriodEquiv]

/-- Underlying matrix in `GL (Fin 2) (ZMod N)` of `unitsQuotientSpanNatCastPeriodEquiv a b N u`. -/
@[simp]
theorem coe_unitsQuotientSpanNatCastPeriodEquiv (a b : ℤ) (N : ℕ)
    (u : (QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)})ˣ) :
    (unitsQuotientSpanNatCastPeriodEquiv a b N u : GL (Fin 2) (ZMod N)) =
      periodUnitMatrix (Units.map (quotientSpanNatCastEquiv a b N).toRingHom.toMonoidHom u) := by
  rw [unitsQuotientSpanNatCastPeriodEquiv_apply, coe_periodUnitMatrixEquiv]

/-- The inverse of `unitsQuotientSpanNatCastPeriodEquiv` pulls back `periodUnitMatrixEquiv.symm`
along `quotientSpanNatCastEquiv`. -/
@[simp]
theorem unitsQuotientSpanNatCastPeriodEquiv_symm_apply (a b : ℤ) (N : ℕ)
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    (unitsQuotientSpanNatCastPeriodEquiv a b N).symm M =
      Units.map (quotientSpanNatCastEquiv a b N).symm.toRingHom.toMonoidHom
        (periodUnitMatrixEquiv.symm M) :=
  Units.ext <| by simp [unitsQuotientSpanNatCastPeriodEquiv]

/-- The residue element underlying `(unitsQuotientSpanNatCastPeriodEquiv a b N).symm M` is
obtained from the bottom row of `M` via `(quotientSpanNatCastEquiv a b N).symm`. -/
theorem coe_unitsQuotientSpanNatCastPeriodEquiv_symm (a b : ℤ) (N : ℕ)
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    ((unitsQuotientSpanNatCastPeriodEquiv a b N).symm M :
        QuadraticAlgebra ℤ a b ⧸ Ideal.span {(N : QuadraticAlgebra ℤ a b)}) =
      (quotientSpanNatCastEquiv a b N).symm
        ⟨(M : GL (Fin 2) (ZMod N)) 1 1, (M : GL (Fin 2) (ZMod N)) 1 0⟩ := by
  simp

/-- `unitsQuotientSpanNatCastPeriodEquiv` sends the residue of an integral unit `u` to
`unitPeriodMatrixHom a b N u`. -/
@[simp]
theorem unitsQuotientSpanNatCastPeriodEquiv_map_mk (a b : ℤ) (N : ℕ)
    (u : (QuadraticAlgebra ℤ a b)ˣ) :
    unitsQuotientSpanNatCastPeriodEquiv a b N
        (Units.map (Ideal.Quotient.mk (Ideal.span {(N : QuadraticAlgebra ℤ a b)})) u) =
      unitPeriodMatrixHom a b N u :=
  Subtype.ext <| Units.ext <| by simp [unitsQuotientSpanNatCastPeriodEquiv, unitPeriodMatrixHom]

/-- Given a ring isomorphism `e : R ≃+* QuadraticAlgebra ℤ a b`, the units of `R ⧸ (N)` are
canonically isomorphic to `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
def unitsQuotientSpanNatCastPeriodEquivOfRingEquiv {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) :
    (R ⧸ Ideal.span {(N : R)})ˣ ≃* periodMatrixGroup (a : ZMod N) (b : ZMod N) :=
  (Units.mapEquiv (Ideal.quotientEquiv (Ideal.span {(N : R)})
    (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
    (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).toMulEquiv).trans
    (unitsQuotientSpanNatCastPeriodEquiv a b N)

/-- Evaluation of `unitsQuotientSpanNatCastPeriodEquivOfRingEquiv` on an arbitrary residue unit
via `Ideal.quotientEquiv` and `unitsQuotientSpanNatCastPeriodEquiv`. -/
theorem unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_apply {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) (u : (R ⧸ Ideal.span {(N : R)})ˣ) :
    unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N u =
      unitsQuotientSpanNatCastPeriodEquiv a b N
        (Units.map (Ideal.quotientEquiv (Ideal.span {(N : R)})
          (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
          (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).toMonoidHom u) :=
  Subtype.ext <| Units.ext <| by
    simp [unitsQuotientSpanNatCastPeriodEquivOfRingEquiv, unitsQuotientSpanNatCastPeriodEquiv]

/-- Underlying matrix in `GL (Fin 2) (ZMod N)` of
`unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N u`. -/
@[simp]
theorem coe_unitsQuotientSpanNatCastPeriodEquivOfRingEquiv {R : Type*} [CommRing R] {a b : ℤ}
    (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ) (u : (R ⧸ Ideal.span {(N : R)})ˣ) :
    (unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N u : GL (Fin 2) (ZMod N)) =
      periodUnitMatrix
        (Units.map (quotientSpanNatCastEquiv a b N).toRingHom.toMonoidHom
          (Units.map (Ideal.quotientEquiv (Ideal.span {(N : R)})
            (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
            (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).toMonoidHom u)) := by
  rw [unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_apply, coe_unitsQuotientSpanNatCastPeriodEquiv]

/-- The inverse of `unitsQuotientSpanNatCastPeriodEquivOfRingEquiv` pulls back
`(unitsQuotientSpanNatCastPeriodEquiv a b N).symm` along `e`. -/
@[simp]
theorem unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_symm_apply {R : Type*} [CommRing R]
    {a b : ℤ} (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ)
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    (unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M =
      Units.map (Ideal.quotientEquiv (Ideal.span {(N : R)})
        (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
        (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm.toMonoidHom
        ((unitsQuotientSpanNatCastPeriodEquiv a b N).symm M) :=
  Units.ext <| by simp [unitsQuotientSpanNatCastPeriodEquivOfRingEquiv]

/-- The residue element underlying `(unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M`
is obtained from the bottom row of `M` via `(quotientSpanNatCastEquiv a b N).symm` and `e.symm`. -/
theorem coe_unitsQuotientSpanNatCastPeriodEquivOfRingEquiv_symm {R : Type*} [CommRing R]
    {a b : ℤ} (e : R ≃+* QuadraticAlgebra ℤ a b) (N : ℕ)
    (M : periodMatrixGroup (a : ZMod N) (b : ZMod N)) :
    ((unitsQuotientSpanNatCastPeriodEquivOfRingEquiv e N).symm M : R ⧸ Ideal.span {(N : R)}) =
      (Ideal.quotientEquiv (Ideal.span {(N : R)})
        (Ideal.span {(N : QuadraticAlgebra ℤ a b)}) e
        (by rw [Ideal.map_span, Set.image_singleton, map_natCast])).symm
        ((quotientSpanNatCastEquiv a b N).symm
          ⟨(M : GL (Fin 2) (ZMod N)) 1 1, (M : GL (Fin 2) (ZMod N)) 1 0⟩) := by
  simp

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
    mem_unitPeriodMatrixSubgroup_iff]
  exact ⟨fun ⟨u, hu⟩ ↦ ⟨Units.map e.toRingHom.toMonoidHom u, hu⟩,
    fun ⟨v, hv⟩ ↦ ⟨Units.map e.symm.toRingHom.toMonoidHom v,
      hv ▸ congrArg (unitPeriodMatrixHom a b N) (Units.ext (by simp))⟩⟩

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
        periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N) := (rfl)

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
            R →* R ⧸ Ideal.span {(N : R)})).range) := (rfl)

/-! ### Discriminants strictly below `-4` versus the Gaussian and Eisenstein cases -/

/-- When `discr a b < -4`, the reduced global-unit subgroup `unitPeriodMatrixSubgroup a b N` is the
scalar sign subgroup `{±I} = Subgroup.zpowers (-1)`. -/
theorem unitPeriodMatrixSubgroup_eq_zpowers_neg_one {a b : ℤ} (hd : discr a b < -4) (N : ℕ) :
    unitPeriodMatrixSubgroup a b N = Subgroup.zpowers (-1) := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr ⟨-1, by simp⟩)
  rintro _ ⟨u, rfl⟩
  rcases units_eq_one_or_neg_one_of_discr_lt_neg_four hd u with rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

/-- For `discr a b < -4`, rewriting `(a : ZMod N) = a'` and `(b : ZMod N) = b'` identifies
`periodMatrixGroup a' b' ⧸ Subgroup.zpowers (-1)` with
`periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N`. -/
def periodMatrixQuotientEquivZpowersNegOne {a b : ℤ} {N : ℕ} {a' b' : ZMod N}
    (hd : discr a b < -4) (ha : (a : ZMod N) = a') (hb : (b : ZMod N) = b') :
    periodMatrixGroup a' b' ⧸ Subgroup.zpowers (-1 : periodMatrixGroup a' b') ≃*
      periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (by rw [ha, hb])) <| by
    rw [unitPeriodMatrixSubgroup_eq_zpowers_neg_one hd N]
    subst ha; subst hb; rw [MonoidHom.map_zpowers]; congr 1

/-- `periodMatrixQuotientEquivZpowersNegOne` sends the coset of `M` to the coset of the same
matrix viewed in `periodMatrixGroup (a : ZMod N) (b : ZMod N)`. -/
@[simp]
theorem periodMatrixQuotientEquivZpowersNegOne_mk {a b : ℤ} {N : ℕ} {a' b' : ZMod N}
    (hd : discr a b < -4) (ha : (a : ZMod N) = a') (hb : (b : ZMod N) = b')
    (M : periodMatrixGroup a' b') :
    periodMatrixQuotientEquivZpowersNegOne hd ha hb M =
      (⟨(M : GL (Fin 2) (ZMod N)), by rw [ha, hb]; exact M.property⟩ :
        periodMatrixGroup (a : ZMod N) (b : ZMod N)) := (rfl)

/-- Transport `unitPeriodMatrixSubgroup a' b' N = ⊤` along equal discriminants using the
residue-unit quotient identification `residueUnitsQuotientPeriodMatrixEquiv`. -/
theorem unitPeriodMatrixSubgroup_eq_top_of_discr_eq {a b a' b' : ℤ} {N : ℕ}
    (hd : discr a b = discr a' b') (htop : unitPeriodMatrixSubgroup a' b' N = ⊤) :
    unitPeriodMatrixSubgroup a b N = ⊤ := by
  obtain ⟨e⟩ := nonempty_algEquiv_int_iff.mpr hd
  let φ :=
    (residueUnitsQuotientPeriodMatrixEquiv (RingEquiv.refl (QuadraticAlgebra ℤ a b)) N).symm.trans
      (residueUnitsQuotientPeriodMatrixEquiv e.toRingEquiv N)
  rw [eq_top_iff]
  rintro M -
  rw [← QuotientGroup.eq_one_iff]
  apply φ.injective
  rw [map_one]
  obtain ⟨M', hM'⟩ := QuotientGroup.mk_surjective
    (φ (M : periodMatrixGroup (a : ZMod N) (b : ZMod N) ⧸ unitPeriodMatrixSubgroup a b N))
  rw [← hM', QuotientGroup.eq_one_iff, htop]
  trivial

end QuadraticAlgebra
