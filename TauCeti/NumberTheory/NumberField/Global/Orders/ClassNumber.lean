/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Functoriality
public import TauCeti.NumberTheory.NumberField.Global.Orders.Maximal
public import TauCeti.NumberTheory.NumberField.Global.Orders.RayClass
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact

import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral

/-!
# The class number of an order

Let `O` be an order in a number field `K`, with conductor `𝔣`. Extending invertible ideals of `O`
to `𝓞 K` gives a surjection `Pic O → Cl(K)`, and its kernel is described by residues modulo the
conductor: there is an exact sequence

```text
1 → (𝓞 K)ˣ / Oˣ → (𝓞 K ⧸ 𝔣)ˣ / (O ⧸ 𝔣)ˣ → Pic O → Cl(K) → 1.
```

Here a residue unit `u` modulo `𝔣` goes to the Picard class of the contraction `β 𝓞 K ∩ O` for any
algebraic integer `β` reducing to `u`. Such a class is trivial exactly when `u` is the product of
the residue of a unit of `O ⧸ 𝔣` and the residue of a unit of `𝓞 K`, and a unit of `𝓞 K` has
residue in `(O ⧸ 𝔣)ˣ` exactly when it is a unit of `O`. Counting gives the class number formula
for orders

```text
#Pic O · [(𝓞 K)ˣ : Oˣ] · #(O ⧸ 𝔣)ˣ = h_K · #(𝓞 K ⧸ 𝔣)ˣ.
```

The proof runs through the congruence description of the Picard group
(`NumberFieldOrder.rayClassToPic`), which presents `Pic O` as a quotient of the ray class group
modulo `𝔣`, and through the ray class exact sequence of the conductor modulus, whose residue part
is `(𝓞 K ⧸ 𝔣)ˣ` since the conductor modulus has no real places. No hypothesis on the degree of `K`
is needed. For an order `ℤ + f 𝓞 K` in a quadratic field, where `𝔣 = f 𝓞 K`, this is the starting
point of the classical expression of the class number of the order of conductor `f` through `h_K`;
computing the two residue-unit counts there is a separate matter.

Inside `(𝓞 K ⧸ 𝔣)ˣ`, the units of `O ⧸ 𝔣` are the image `NumberFieldOrder.orderResidueUnits` of
the injective map induced by `O ⊆ 𝓞 K`, and the units of `O` inside `(𝓞 K)ˣ` are the image of
`Units.map` of the inclusion.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.picToClassGroup`: the extension map
  `Pic O → Cl(K)`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.residueUnitsToPic`: the map `(𝓞 K ⧸ 𝔣)ˣ → Pic O`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.orderResidueUnits`: the units of `O ⧸ 𝔣` as a
  subgroup of `(𝓞 K ⧸ 𝔣)ˣ`.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.picToClassGroup_picClass`: extension of the
  contraction of an ideal prime to the conductor recovers its ideal class.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.picToClassGroup_surjective`: every ideal class of
  `K` comes from `Pic O`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.range_residueUnitsToPic`: exactness at `Pic O`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.ker_residueUnitsToPic`: exactness at the residue
  units.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.comap_orderResidueUnits`: a unit of `𝓞 K` has
  residue in `(O ⧸ 𝔣)ˣ` exactly when it is a unit of `O`.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.card_pic_mul_index_mul_card_units`: the class
  number formula for orders.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12, Proposition 12.9 and Theorem 12.12.
* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.24 (the quadratic case).
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

namespace NumberFieldOrder

variable (O : NumberFieldOrder K)

/-! ### Extension of Picard classes to the maximal order -/

/-- **Extension of ideal classes to the maximal order.** The Picard class of an invertible
fractional ideal `I` of `O` goes to the ideal class of `I 𝓞 K`. -/
def picToClassGroup : Pic O →* ClassGroup (𝓞 K) :=
  (maximalOrderPicEquiv K).toMonoidHom.comp
    (Hom.ofLE (O.le_ringOfIntegers.trans_eq (maximalNumberFieldOrder_toSubalgebra K).symm)).mapPic

/-- On the class of an invertible ideal `I`, `picToClassGroup` gives the ideal class of the
extension of `I` to the maximal order. -/
@[simp]
theorem picToClassGroup_mkPic (I : O.invertibleProperFractionalIdeals) :
    O.picToClassGroup (O.mkPic I) = ClassGroup.mk K (maximalOrderUnitsEquiv K
      ((Hom.ofLE (O.le_ringOfIntegers.trans_eq
        (maximalNumberFieldOrder_toSubalgebra K).symm)).mapInvertible I)) := by
  rw [picToClassGroup, MonoidHom.comp_apply, Hom.mapPic_mkPic, MulEquiv.coe_toMonoidHom,
    maximalOrderPicEquiv_mkPic]

/-- The `𝓞 K`-span of the contraction `J ∩ O` of an ideal `J` of `𝓞 K` prime to the conductor is
`J`. -/
private theorem mem_span_contraction_iff (J : integralIdealsPrimeTo O.conductorModulus) (x : K) :
    x ∈ Submodule.span (maximalNumberFieldOrder K).toSubalgebra
        {y : K | ∃ z ∈ (J : Ideal (𝓞 K)).comap
          (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), ((z : 𝓞 K) : K) = y} ↔
      ∃ j ∈ (J : Ideal (𝓞 K)), (j : K) = x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz, rfl⟩
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add y y' _ _ hy hy' =>
      obtain ⟨j, hj, rfl⟩ := hy
      obtain ⟨j', hj', rfl⟩ := hy'
      exact ⟨j + j', add_mem hj hj', by simp⟩
    | smul a y _ hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      refine ⟨maximalOrderRingEquiv K a * j, Ideal.mul_mem_left _ _ hj, ?_⟩
      have ha := algebraMap_maximalOrderRingEquiv a
      rw [Subalgebra.smul_def, RingOfIntegers.coe_eq_algebraMap, map_mul, ha, smul_eq_mul,
        Subalgebra.algebraMap_apply]
  · rintro ⟨j, hj, rfl⟩
    -- `J` is the extension of its contraction, as `J` is prime to the conductor.
    have hJ : (J : Ideal (𝓞 K)) = ((J : Ideal (𝓞 K)).comap
        (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K)).map
          (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) := by
      conv_lhs => rw [← O.integralIdealsAwayConductorEquiv.apply_symm_apply J]
      rw [coe_integralIdealsAwayConductorEquiv_apply,
        coe_integralIdealsAwayConductorEquiv_symm_apply]
    rw [hJ, Ideal.map] at hj
    induction hj using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero => simp
    | add y y' _ _ hy hy' => simpa using add_mem hy hy'
    | smul a y _ hy =>
      have ha := algebraMap_maximalOrderRingEquiv ((maximalOrderRingEquiv K).symm a)
      rw [RingEquiv.apply_symm_apply] at ha
      have h := Submodule.smul_mem _ ((maximalOrderRingEquiv K).symm a) hy
      rw [Subalgebra.smul_def, smul_eq_mul] at h
      rwa [smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, ha, Subalgebra.algebraMap_apply,
        ← RingOfIntegers.coe_eq_algebraMap]

/-- **Extension recovers the ideal class.** For an ideal `J` of `𝓞 K` prime to the conductor, the
extension of the Picard class of its contraction `J ∩ O` is the ideal class of `J`. -/
@[simp]
theorem picToClassGroup_picClass (J : integralIdealsPrimeTo O.conductorModulus) :
    O.picToClassGroup (O.picClass J) =
      rayClassToClassGroup O.conductorModulus (idealClass O.conductorModulus J) := by
  rw [picClass_apply, picToClassGroup_mkPic, idealClass_apply, rayClassToClassGroup_rayClassMk]
  refine congrArg _ (Units.ext (FractionalIdeal.ext fun x => ?_))
  rw [coe_maximalOrderUnitsEquiv, mem_maximalOrderFractionalIdealEquiv, Hom.coe_mapInvertible,
    Hom.mem_mapFractionalIdeal_iff, NumberFieldArithmetic.coe_integralIdealsAwayHom,
    FractionalIdeal.mem_coeIdeal, ← O.mem_span_contraction_iff J x]
  congr! 2
  ext y
  simp only [Set.mem_image, Hom.ofLE_apply, exists_eq_right, SetLike.mem_coe,
    coe_integralIdealsAwayConductorToInvertible_apply, mem_coeIdeal_map_toRingOfIntegersEquiv,
    coe_integralIdealsAwayConductorEquiv_symm_apply, Set.mem_ofPred_eq]

/-- Extension of Picard classes after the congruence description of `Pic O` is the ordinary class
of a ray class. -/
theorem picToClassGroup_comp_rayClassToPic :
    O.picToClassGroup.comp O.rayClassToPic = rayClassToClassGroup O.conductorModulus := by
  refine MonoidHom.ext fun c => ?_
  obtain ⟨J, rfl⟩ := idealClass_surjective _ c
  rw [MonoidHom.comp_apply, rayClassToPic_idealClass, picToClassGroup_picClass]

/-- **Every ideal class of `K` is the extension of a Picard class of `O`.** -/
theorem picToClassGroup_surjective : Function.Surjective O.picToClassGroup := by
  intro c
  obtain ⟨r, rfl⟩ := rayClassToClassGroup_surjective O.conductorModulus c
  exact ⟨O.rayClassToPic r, by rw [← MonoidHom.comp_apply, picToClassGroup_comp_rayClassToPic]⟩

/-! ### Residue units modulo the conductor -/

/-- The conductor modulus has no real places, so it prescribes no signs. -/
private theorem conductorModulus_signs_eq_one (s : O.conductorModulus.infinitePart → ℤˣ) :
    s = 1 :=
  funext fun w => absurd w.2 (by simp)

/-- The residue units modulo the conductor, identified with the residue units modulo the finite
part of the conductor modulus. -/
private def residueEquiv :
    (𝓞 K ⧸ O.conductor)ˣ ≃* (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ :=
  Units.mapEquiv (Ideal.quotEquivOfEq O.conductorModulus_finitePart.symm).toMulEquiv

private theorem coe_residueEquiv_eq_mk_iff {w : (𝓞 K ⧸ O.conductor)ˣ} {β : 𝓞 K} :
    ((O.residueEquiv w : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ) :
        𝓞 K ⧸ O.conductorModulus.finitePart) = Ideal.Quotient.mk _ β ↔
      (w : 𝓞 K ⧸ O.conductor) = Ideal.Quotient.mk O.conductor β := by
  rw [residueEquiv, Units.coe_mapEquiv, RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv,
    ← Ideal.quotEquivOfEq_mk O.conductorModulus_finitePart.symm β, EquivLike.apply_eq_iff_eq]

/-- The residue of an integral unit, read off the residue-and-sign presentation. -/
private theorem unitsResidueSignHom_conductorModulus (ε : (𝓞 K)ˣ) :
    unitsResidueSignHom O.conductorModulus ε =
      (O.residueEquiv (Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom ε), 1) := by
  refine Prod.ext (Units.ext ?_) (O.conductorModulus_signs_eq_one _)
  rw [unitsResidueSignHom_apply, residueSignHom_fst, coe_residueHom,
    residue_eq _ (a := (ε : 𝓞 K)) (b := 1) (by simp) (by simp [coe_unitsToPrimeToSubgroup]),
    eq_comm, coe_residueEquiv_eq_mk_iff, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass]

/-- The residue of a principal ray class generator, read off the residue-and-sign presentation. -/
private theorem exists_residueSignHom_conductorModulus {x : primeToSubgroup O.conductorModulus}
    {β : 𝓞 K} (hx : ((x : Kˣ) : K) = β) :
    ∃ w : (𝓞 K ⧸ O.conductor)ˣ, (w : 𝓞 K ⧸ O.conductor) = Ideal.Quotient.mk O.conductor β ∧
      residueSignHom O.conductorModulus x = (O.residueEquiv w, 1) := by
  refine ⟨O.residueEquiv.symm (residueHom O.conductorModulus x), ?_, ?_⟩
  · rw [← coe_residueEquiv_eq_mk_iff, MulEquiv.apply_symm_apply, coe_residueHom,
      residue_eq x (a := β) (b := 1) (by simp) (by simp [hx])]
  · rw [MulEquiv.apply_symm_apply]
    exact Prod.ext (residueSignHom_fst _ x) (O.conductorModulus_signs_eq_one _)

/-- **The Picard class of a residue unit modulo the conductor.** A unit `u` of `𝓞 K ⧸ 𝔣` is the
residue of an algebraic integer `β` prime to the conductor `𝔣`, and it goes to the Picard class of
the contraction `β 𝓞 K ∩ O` (`residueUnitsToPic_eq_picClass`). It is the principal ray class of
`β` modulo `𝔣`, mapped to `Pic O`. -/
def residueUnitsToPic : (𝓞 K ⧸ O.conductor)ˣ →* Pic O :=
  O.rayClassToPic.comp ((residueSignRayClass O.conductorModulus).comp
    ((MonoidHom.inl _ _).comp O.residueEquiv.toMonoidHom))

private theorem residueUnitsToPic_apply (u : (𝓞 K ⧸ O.conductor)ˣ) :
    O.residueUnitsToPic u =
      O.rayClassToPic (residueSignRayClass O.conductorModulus (O.residueEquiv u, 1)) :=
  (rfl)

/-- **The Picard class of a residue unit is that of a principal ideal.** If the residue unit `u`
is the reduction of a generator `β` of an ideal `J` of `𝓞 K` prime to the conductor, then `u`
goes to the Picard class of the contraction `J ∩ O`. -/
theorem residueUnitsToPic_eq_picClass {u : (𝓞 K ⧸ O.conductor)ˣ}
    {J : integralIdealsPrimeTo O.conductorModulus} {β : 𝓞 K}
    (hJ : (J : Ideal (𝓞 K)) = Ideal.span {β})
    (hu : (u : 𝓞 K ⧸ O.conductor) = Ideal.Quotient.mk O.conductor β) :
    O.residueUnitsToPic u = O.picClass J := by
  obtain ⟨x, hxβ, hJx⟩ := exists_idealClass_eq_principalRayClass hJ
  obtain ⟨w, hw, hsign⟩ := O.exists_residueSignHom_conductorModulus hxβ
  obtain rfl : w = u := Units.ext (hw.trans hu.symm)
  rw [← rayClassToPic_idealClass, hJx, ← residueSignRayClass_residueSignHom, hsign,
    residueUnitsToPic_apply]

/-- **Exactness at `Pic O`.** A Picard class extends to the trivial ideal class of `K` exactly
when it is the class of a residue unit modulo the conductor. -/
theorem range_residueUnitsToPic : O.residueUnitsToPic.range = O.picToClassGroup.ker := by
  ext c
  constructor
  · rintro ⟨u, rfl⟩
    have hu : residueSignRayClass O.conductorModulus (O.residueEquiv u, 1) ∈
        (rayClassToClassGroup O.conductorModulus).ker := by
      rw [← range_residueSignRayClass]
      exact ⟨_, rfl⟩
    rw [MonoidHom.mem_ker, residueUnitsToPic_apply, ← MonoidHom.comp_apply,
      picToClassGroup_comp_rayClassToPic]
    exact hu
  · intro hc
    obtain ⟨r, rfl⟩ := O.rayClassToPic_surjective c
    rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, picToClassGroup_comp_rayClassToPic,
      ← MonoidHom.mem_ker, ← range_residueSignRayClass] at hc
    obtain ⟨⟨a, s⟩, rfl⟩ := hc
    refine ⟨O.residueEquiv.symm a, ?_⟩
    rw [residueUnitsToPic_apply, MulEquiv.apply_symm_apply, O.conductorModulus_signs_eq_one s]

/-- Exactness at `Pic O`, as a `Function.MulExact` statement. -/
theorem mulExact_residueUnitsToPic_picToClassGroup :
    Function.MulExact O.residueUnitsToPic O.picToClassGroup :=
  MonoidHom.mulExact_iff.mpr O.range_residueUnitsToPic.symm

/-! ### Residue units of the order -/

/-- **The residue units of the order.** The units of `O ⧸ 𝔣`, embedded in `(𝓞 K ⧸ 𝔣)ˣ` by the
injective map induced by the inclusion `O ⊆ 𝓞 K`; here `𝔣 = O.conductor`, viewed in `O` through
its contraction. -/
def orderResidueUnits : Subgroup (𝓞 K ⧸ O.conductor)ˣ :=
  (Units.map (Ideal.quotientMap O.conductor
    (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) le_rfl).toMonoidHom).range

/-- The residue units of the order are as many as the units of `O ⧸ 𝔣`. -/
theorem card_orderResidueUnits :
    Nat.card O.orderResidueUnits = Nat.card (O.toRingOfIntegers ⧸
      O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K))ˣ :=
  (Nat.card_congr (MonoidHom.ofInjective
    (Units.map_injective Ideal.quotientMap_injective)).toEquiv).symm

/-- **A residue unit modulo the conductor lies in `(O ⧸ 𝔣)ˣ` exactly when it is the residue of an
element of `O`.** -/
theorem mem_orderResidueUnits_iff {u : (𝓞 K ⧸ O.conductor)ˣ} :
    u ∈ O.orderResidueUnits ↔
      ∃ β ∈ O.toRingOfIntegers, (u : 𝓞 K ⧸ O.conductor) = Ideal.Quotient.mk O.conductor β := by
  set q := Ideal.quotientMap O.conductor
    (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) le_rfl
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨γ, hγ⟩ := Ideal.Quotient.mk_surjective v.1
    refine ⟨γ, γ.2, ?_⟩
    rw [Units.coe_map, ← hγ]
    exact Ideal.quotientMap_mk ..
  · rintro ⟨β, hβ, hu⟩
    have : Finite (𝓞 K ⧸ O.conductor) := Ideal.finiteQuotientOfFreeOfNeBot _ O.conductor_ne_bot
    have : Finite (O.toRingOfIntegers ⧸
        O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K)) :=
      Finite.of_injective q Ideal.quotientMap_injective
    set v := Ideal.Quotient.mk (O.conductor.comap
      (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K)) (⟨β, hβ⟩ : O.toRingOfIntegers)
    have hqv : q v = u := by
      rw [hu, Ideal.quotientMap_mk, AlgHom.coe_toRingHom, Subalgebra.coe_val]
    -- `v` is a nonzerodivisor, since `q` is injective and `q v` is a unit; in the finite ring
    -- `O ⧸ 𝔣` it is therefore a unit.
    have hv : IsUnit v := IsArtinianRing.isUnit_of_mem_nonZeroDivisors <|
      mem_nonZeroDivisors_iff_right.mpr fun a ha => by
        apply (injective_iff_map_eq_zero q).mp Ideal.quotientMap_injective
        have h := congrArg q ha
        rwa [map_mul, map_zero, hqv, Units.mul_left_eq_zero] at h
    exact ⟨hv.unit, Units.ext (by simpa using hqv)⟩

/-- **The units of the order are the units of `𝓞 K` with residue in `(O ⧸ 𝔣)ˣ`.** A unit `ε` of
`𝓞 K` whose residue modulo the conductor is the residue of an element of `O` lies in `O`, and so
does `ε⁻¹`. -/
theorem comap_orderResidueUnits :
    O.orderResidueUnits.comap (Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom) =
      (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range := by
  ext ε
  rw [Subgroup.mem_comap]
  constructor
  · intro hε
    obtain ⟨β, hβ, h⟩ := O.mem_orderResidueUnits_iff.mp hε
    obtain ⟨β', hβ', h'⟩ := O.mem_orderResidueUnits_iff.mp (inv_mem hε)
    rw [← map_inv] at h'
    have h₁ := O.mem_toRingOfIntegers_of_mk_eq hβ h
    have h₂ := O.mem_toRingOfIntegers_of_mk_eq hβ' h'
    refine ⟨⟨⟨ε, h₁⟩, ⟨_, h₂⟩, Subtype.ext ε.mul_inv, Subtype.ext ε.inv_mul⟩, Units.ext rfl⟩
  · rintro ⟨w, rfl⟩
    exact O.mem_orderResidueUnits_iff.mpr ⟨_, (w : O.toRingOfIntegers).2, rfl⟩

/-- A residue unit of the order has trivial Picard class: it is the residue of a generator in `O`
of an ideal prime to the conductor. -/
private theorem orderResidueUnits_le_ker_residueUnitsToPic :
    O.orderResidueUnits ≤ O.residueUnitsToPic.ker := by
  intro u hu
  obtain ⟨β, hβ, hu⟩ := O.mem_orderResidueUnits_iff.mp hu
  by_cases hβ0 : β = 0
  · -- The residue of `0` is a unit only when the residue ring is trivial.
    have h0 := u.isUnit
    rw [hu, hβ0, map_zero, isUnit_zero_iff] at h0
    have : Subsingleton (𝓞 K ⧸ O.conductor) := subsingleton_of_zero_eq_one h0
    rw [Subsingleton.elim u 1]
    exact one_mem _
  obtain ⟨a, ha⟩ := isUnit_iff_exists_inv.mp (hu ▸ u.isUnit)
  have hJ : Ideal.span {β} ∈ integralIdealsPrimeTo O.conductorModulus := by
    refine O.mem_integralIdealsPrimeTo_conductorModulus_iff.mpr
      ⟨Ideal.span_singleton_eq_bot.not.mpr hβ0, (Ideal.eq_top_iff_one _).mpr ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [← map_mul, ← map_one (Ideal.Quotient.mk O.conductor), Ideal.Quotient.eq] at ha
    exact Ideal.mem_span_singleton_sup.mpr ⟨a, -(β * a - 1), neg_mem ha, by ring⟩
  rw [MonoidHom.mem_ker, O.residueUnitsToPic_eq_picClass (J := ⟨_, hJ⟩) rfl hu,
    picClass_eq_one_iff]
  exact ⟨β, hβ, rfl⟩

/-- The residue of a unit of `𝓞 K` has trivial Picard class. -/
private theorem range_unitsMap_le_ker_residueUnitsToPic :
    (Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom).range ≤ O.residueUnitsToPic.ker := by
  rintro _ ⟨ε, rfl⟩
  have hε : unitsResidueSignHom O.conductorModulus ε ∈
      (residueSignRayClass O.conductorModulus).ker := by
    rw [ker_residueSignRayClass]
    exact ⟨ε, rfl⟩
  rw [MonoidHom.mem_ker, residueUnitsToPic_apply, ← O.unitsResidueSignHom_conductorModulus,
    MonoidHom.mem_ker.mp hε, map_one]

/-- **Exactness at the residue units.** A residue unit modulo the conductor has trivial Picard
class exactly when it is the product of a residue unit of the order and the residue of a unit of
`𝓞 K`. -/
theorem ker_residueUnitsToPic :
    O.residueUnitsToPic.ker = O.orderResidueUnits ⊔
      (Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom).range := by
  apply le_antisymm
  · intro u hu
    rw [MonoidHom.mem_ker, residueUnitsToPic_apply, ← MonoidHom.mem_ker,
      mem_ker_rayClassToPic] at hu
    obtain ⟨J, hJu, β, hβ, hJ⟩ := hu
    obtain ⟨x, hxβ, hJx⟩ := exists_idealClass_eq_principalRayClass hJ
    obtain ⟨w, hres, hsign⟩ := O.exists_residueSignHom_conductorModulus hxβ
    have hw : w ∈ O.orderResidueUnits := O.mem_orderResidueUnits_iff.mpr ⟨β, hβ, hres⟩
    -- The classes of `u` and of the residue `w` of `β` agree, so `w⁻¹ u` comes from a unit.
    have hwu : ((O.residueEquiv (w⁻¹ * u), 1) : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ ×
        (O.conductorModulus.infinitePart → ℤˣ)) ∈
          (residueSignRayClass O.conductorModulus).ker := by
      have h : residueSignRayClass O.conductorModulus (O.residueEquiv w, 1) =
          residueSignRayClass O.conductorModulus (O.residueEquiv u, 1) := by
        rw [← hsign, residueSignRayClass_residueSignHom, ← hJx, hJu]
      have hprod : ((O.residueEquiv (w⁻¹ * u), 1) : (𝓞 K ⧸ O.conductorModulus.finitePart)ˣ ×
          (O.conductorModulus.infinitePart → ℤˣ)) =
            (O.residueEquiv w, 1)⁻¹ * (O.residueEquiv u, 1) := by
        rw [map_mul, map_inv, Prod.inv_mk, Prod.mk_mul_mk, inv_one, one_mul]
      rw [MonoidHom.mem_ker, hprod, map_mul, map_inv, h, inv_mul_cancel]
    rw [ker_residueSignRayClass] at hwu
    obtain ⟨ε, hε⟩ := hwu
    rw [O.unitsResidueSignHom_conductorModulus, Prod.mk.injEq] at hε
    rw [← mul_inv_cancel_left w u]
    exact Subgroup.mul_mem_sup hw ⟨ε, O.residueEquiv.injective hε.1⟩
  · exact sup_le O.orderResidueUnits_le_ker_residueUnitsToPic
      O.range_unitsMap_le_ker_residueUnitsToPic

/-! ### The class number formula -/

/-- **The class number formula for orders.** For an order `O` with conductor `𝔣`,

`#Pic O · [(𝓞 K)ˣ : Oˣ] · #(O ⧸ 𝔣)ˣ = h_K · #(𝓞 K ⧸ 𝔣)ˣ`,

where `Oˣ` is the image of the units of `O` in `(𝓞 K)ˣ`. -/
theorem card_pic_mul_index_mul_card_units :
    Nat.card (Pic O) *
        (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index *
        Nat.card (O.toRingOfIntegers ⧸
          O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K))ˣ =
      Nat.card (ClassGroup (𝓞 K)) * Nat.card (𝓞 K ⧸ O.conductor)ˣ := by
  set H := O.orderResidueUnits
  set U := (Units.map (Ideal.Quotient.mk O.conductor).toMonoidHom).range
  have hpic :
      Nat.card (Pic O) = Nat.card O.picToClassGroup.ker * Nat.card (ClassGroup (𝓞 K)) := by
    rw [← O.picToClassGroup.ker.card_mul_index, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr O.picToClassGroup_surjective, Subgroup.card_top]
  have hker : Nat.card O.picToClassGroup.ker = (H ⊔ U).index := by
    rw [← range_residueUnitsToPic, ← Subgroup.index_ker, ker_residueUnitsToPic]
  have hunits : (Units.map (O.toRingOfIntegers.val : O.toRingOfIntegers →* 𝓞 K)).range.index =
      H.relIndex (H ⊔ U) := by
    rw [← comap_orderResidueUnits, Subgroup.index_comap, Subgroup.relIndex_sup_left]
  rw [hpic, hker, hunits, ← card_orderResidueUnits, ← H.index_mul_card,
    ← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ U)]
  ring

end NumberFieldOrder

end TauCeti.GlobalNumberFields
