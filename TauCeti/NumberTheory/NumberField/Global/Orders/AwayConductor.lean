/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Orders.Discriminant
public import TauCeti.NumberTheory.NumberField.Global.Orders.ProperIdeal
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Modulus
public import TauCeti.RingTheory.Ideal.Conductor

/-!
# Ideals of an order away from its conductor

Let `O` be an order in a number field `K` with conductor `𝔣`. Extension `I ↦ I 𝓞 K` and
contraction `J ↦ J ∩ O` are inverse monoid isomorphisms between the nonzero ideals of `O`
coprime to `𝔣` and the nonzero ideals of `𝓞 K` coprime to `𝔣`. On the maximal-order side the
carrier is the integral prime-to monoid `integralIdealsPrimeTo` of the conductor viewed as a
modulus, `NumberFieldOrder.conductorModulus`, the same monoid the ray class group is built on.

Every nonzero ideal `I` of `O` coprime to `𝔣` is invertible, even though `O` need not be a
Dedekind domain. If `J'` is the inverse of the extension `I 𝓞 K` as a fractional ideal of the
Dedekind domain `𝓞 K`, then `O + 𝔣 J'` is an inverse of `I`: indeed
`I (O + 𝔣 J') = I + 𝔣 (I 𝓞 K) J' = I + 𝔣 = O`, using that `𝔣` is an ideal of `𝓞 K` contained in
`O`. These ideals therefore map to the group of invertible fractional ideals of `O`, the carrier
of the Picard group `Pic O`; these are the order-side ideals used to describe `Pic O` by ideals
prime to the conductor.

## Main definitions

* `TauCeti.GlobalNumberFields.NumberFieldOrder.conductorModulus`: the conductor of an order as a
  modulus without real places.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.integralIdealsAwayConductor`: the monoid of nonzero
  ideals of an order coprime to its conductor.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.integralIdealsAwayConductorEquiv`: extension and
  contraction between ideals of the order and of the maximal order away from the conductor.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.integralIdealsAwayConductorToInvertible`: the
  invertible fractional ideal of an ideal of the order coprime to the conductor.

## Main results

* `TauCeti.GlobalNumberFields.NumberFieldOrder.isUnit_coeIdeal_of_mem_integralIdealsAwayConductor`:
  a nonzero ideal of an order coprime to the conductor is an invertible fractional ideal.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §12, Proposition 12.10.
* G. S. Kopp and J. C. Lagarias, *Class Field Theory for Orders of Number Fields*, §2.
* D. A. Cox, *Primes of the Form x² + ny²*, §7, Proposition 7.20 (the quadratic case).
-/

public section
noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace TauCeti.GlobalNumberFields

namespace NumberFieldOrder

variable {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K)

/-! ### The conductor as a modulus -/

/-- The conductor of an order as a modulus of `K`, with no real places. Its integral prime-to
monoid consists of the nonzero ideals of `𝓞 K` coprime to the conductor. -/
def conductorModulus : Modulus K where
  finitePart := O.conductor
  finitePart_ne_bot := O.conductor_ne_bot
  infinitePart := ∅

@[simp]
theorem conductorModulus_finitePart : O.conductorModulus.finitePart = O.conductor :=
  (rfl)

@[simp]
theorem conductorModulus_infinitePart : O.conductorModulus.infinitePart = ∅ :=
  (rfl)

/-- An ideal of `𝓞 K` is prime to the conductor modulus exactly when it is nonzero and coprime
to the conductor. -/
theorem mem_integralIdealsPrimeTo_conductorModulus_iff {J : Ideal (𝓞 K)} :
    J ∈ integralIdealsPrimeTo O.conductorModulus ↔ J ≠ ⊥ ∧ J ⊔ O.conductor = ⊤ :=
  Modulus.mem_integralIdealsPrimeTo.trans Modulus.isCoprimeTo_iff_sup_eq_top

/-! ### Ideals of the order coprime to the conductor -/

/-- The monoid of nonzero ideals of an order coprime to its conductor. The order is represented
by its copy `O.toRingOfIntegers` inside `𝓞 K`, and the conductor by its contraction to it. -/
def integralIdealsAwayConductor : Submonoid (Ideal O.toRingOfIntegers) where
  carrier := {I | I ≠ ⊥ ∧
    I ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' {I J} hI hJ := ⟨mul_ne_zero hI.1 hJ.1, Ideal.isCoprime_iff_sup_eq.mp <|
    (Ideal.isCoprime_iff_sup_eq.mpr hI.2).mul_left (Ideal.isCoprime_iff_sup_eq.mpr hJ.2)⟩

@[simp]
theorem mem_integralIdealsAwayConductor_iff {I : Ideal O.toRingOfIntegers} :
    I ∈ O.integralIdealsAwayConductor ↔ I ≠ ⊥ ∧
      I ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤ :=
  Iff.rfl

/-- **Extension and contraction away from the conductor.** Extending ideals from an order to
`𝓞 K` is a monoid isomorphism from the nonzero ideals of the order coprime to the conductor onto
the nonzero ideals of `𝓞 K` coprime to the conductor, whose inverse is contraction. -/
def integralIdealsAwayConductorEquiv :
    O.integralIdealsAwayConductor ≃* integralIdealsPrimeTo O.conductorModulus where
  toFun I := ⟨I.1.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), by
    rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
    refine ⟨fun h => I.2.1 ?_,
      map_sup_eq_top_of_coprime_comap (S := O.toRingOfIntegers.toSubring) I.2.2⟩
    exact (comap_map_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers I.2.2).symm.trans
        ((congrArg (Ideal.comap O.toRingOfIntegers.toSubring.subtype) h).trans
          (Ideal.comap_bot_of_injective _ Subtype.val_injective))⟩
  invFun J := ⟨J.1.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K), by
    have hJ := (O.mem_integralIdealsPrimeTo_conductorModulus_iff).mp J.2
    refine ⟨fun h => hJ.1 ?_, comap_sup_eq_top_of_le (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers hJ.2⟩
    exact (map_comap_of_coprime (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers hJ.2).symm.trans
        ((congrArg (Ideal.map O.toRingOfIntegers.toSubring.subtype) h).trans Ideal.map_bot)⟩
  left_inv I := Subtype.ext <|
    comap_map_of_coprime_comap (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers I.2.2
  right_inv J := Subtype.ext <|
    map_comap_of_coprime (S := O.toRingOfIntegers.toSubring)
      O.conductor_le_toRingOfIntegers ((O.mem_integralIdealsPrimeTo_conductorModulus_iff).mp J.2).2
  map_mul' I J := Subtype.ext (Ideal.map_mul _ _ _)

/-- The isomorphism `integralIdealsAwayConductorEquiv` extends an ideal of the order to `𝓞 K`. -/
@[simp]
theorem coe_integralIdealsAwayConductorEquiv_apply (I : O.integralIdealsAwayConductor) :
    (O.integralIdealsAwayConductorEquiv I : Ideal (𝓞 K)) =
      (I : Ideal O.toRingOfIntegers).map
        (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) :=
  (rfl)

/-- The inverse of `integralIdealsAwayConductorEquiv` contracts an ideal of `𝓞 K` to the
order. -/
@[simp]
theorem coe_integralIdealsAwayConductorEquiv_symm_apply
    (J : integralIdealsPrimeTo O.conductorModulus) :
    (O.integralIdealsAwayConductorEquiv.symm J : Ideal O.toRingOfIntegers) =
      (J : Ideal (𝓞 K)).comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) :=
  (rfl)

/-! ### Invertibility -/

variable {O}

/-- An element of `K` lies in the fractional ideal of `O` attached to an ideal `I` of
`O.toRingOfIntegers` exactly when it is an element of `I`. -/
theorem mem_coeIdeal_map_toRingOfIntegersEquiv {I : Ideal O.toRingOfIntegers} {y : K} :
    y ∈ ((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) ↔
      ∃ x ∈ I, ((x : 𝓞 K) : K) = y := by
  rw [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_of_equiv _ a).mp ha
    exact ⟨x, hx, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, Ideal.mem_map_of_mem _ hx, by simp⟩

/-- Over `ℤ`, the product of an ideal `I` of the order with `𝓞 K` is the extension of `I` to
`𝓞 K`. -/
private theorem restrictScalars_coeIdeal_mul_one (I : Ideal O.toRingOfIntegers) :
    (((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
          Submodule O.toSubalgebra K).restrictScalars ℤ *
        (1 : Submodule (𝓞 K) K).restrictScalars ℤ =
      (((I.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ := by
  set i := (((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
    FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
      Submodule O.toSubalgebra K).restrictScalars ℤ
  set b := (1 : Submodule (𝓞 K) K).restrictScalars ℤ
  have hb : b * b = b := by rw [← Submodule.restrictScalars_mul, one_mul]
  apply le_antisymm
  · refine Submodule.mul_le.mpr fun m hm n hn => ?_
    obtain ⟨x, hx, rfl⟩ := mem_coeIdeal_map_toRingOfIntegersEquiv.mp hm
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hn
    refine (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨(x : 𝓞 K) * r,
      Ideal.mul_mem_right r _ (Ideal.mem_map_of_mem _ hx), by simp⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    clear hy
    rw [Ideal.map, Ideal.span] at hz
    -- The elements of `𝓞 K` landing in `i * b` form an ideal containing the image of `I`.
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨x, hx, rfl⟩ := hz
        have hx' : ((x : 𝓞 K) : K) ∈ i := mem_coeIdeal_map_toRingOfIntegersEquiv.mpr ⟨x, hx, rfl⟩
        have h1 : (1 : K) ∈ b := Submodule.mem_one.mpr ⟨1, map_one _⟩
        have h := Submodule.mul_mem_mul hx' h1
        rwa [mul_one] at h
    | zero => rw [map_zero]; exact zero_mem _
    | add z w _ _ hz hw => rw [map_add]; exact add_mem hz hw
    | smul r z _ hz =>
        have hr : algebraMap (𝓞 K) K r ∈ b := Submodule.mem_one.mpr ⟨r, rfl⟩
        have h := Submodule.mul_mem_mul hr hz
        rw [mul_left_comm, hb] at h
        rwa [smul_eq_mul, map_mul]

/-- Over `ℤ`, an ideal `I` of the order coprime to the conductor `𝔣` satisfies `I + 𝔣 = O`. -/
private theorem restrictScalars_coeIdeal_sup_conductor {I : Ideal O.toRingOfIntegers}
    (hI : I ⊔ O.conductor.comap (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) = ⊤) :
    (((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
          Submodule O.toSubalgebra K).restrictScalars ℤ ⊔
        ((O.conductor : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ =
      (1 : Submodule O.toSubalgebra K).restrictScalars ℤ := by
  apply le_antisymm
  · refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · have h := FractionalIdeal.coeIdeal_le_one (S := O.toSubalgebra⁰) hy
      rwa [← FractionalIdeal.mem_coe, FractionalIdeal.coe_one] at h
    · obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
      exact Submodule.mem_one.mpr ⟨⟨_, O.conductor_le_order hc⟩, rfl⟩
  · intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hy
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp hI)
    -- Write `a = a u + a c` with `a u ∈ I` and `a c ∈ 𝔣`.
    let a' := O.toRingOfIntegersEquiv.symm a
    have ha : algebraMap O.toSubalgebra K a = ((a' * u : O.toRingOfIntegers) : 𝓞 K) +
        ((a' : 𝓞 K) * (c : 𝓞 K) : 𝓞 K) := by
      have := congrArg (fun t : O.toRingOfIntegers => (((a' * t : O.toRingOfIntegers) :
        𝓞 K) : K)) huc
      simp only [mul_add, mul_one, Subalgebra.coe_add, Subalgebra.coe_mul] at this
      simpa [a', RingOfIntegers.coe_eq_algebraMap] using this.symm
    rw [ha]
    refine Submodule.add_mem_sup
      (mem_coeIdeal_map_toRingOfIntegersEquiv.mpr ⟨_, I.mul_mem_left a' hu, rfl⟩) ?_
    exact (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨_, O.conductor.mul_mem_left _ hc, rfl⟩

/-- **Ideals coprime to the conductor are invertible.** A nonzero ideal of an order coprime to
its conductor is an invertible fractional ideal of the order. -/
theorem isUnit_coeIdeal_of_mem_integralIdealsAwayConductor {I : Ideal O.toRingOfIntegers}
    (hI : I ∈ O.integralIdealsAwayConductor) :
    IsUnit ((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
      FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) := by
  set Ifr : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K :=
    ((I.map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
      FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)
  set M : FractionalIdeal (𝓞 K)⁰ K :=
    ((I.map (O.toRingOfIntegers.val : O.toRingOfIntegers →+* 𝓞 K) : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K)
  have hM : M ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr
    ((O.mem_integralIdealsPrimeTo_conductorModulus_iff).mp
      (O.integralIdealsAwayConductorEquiv ⟨I, hI⟩).2).1
  -- Work with `ℤ`-submodules of `K`, where ideals of `O` and of `𝓞 K` can be multiplied.
  set i := (Ifr : Submodule O.toSubalgebra K).restrictScalars ℤ
  set one := (1 : Submodule O.toSubalgebra K).restrictScalars ℤ
  set b := (1 : Submodule (𝓞 K) K).restrictScalars ℤ
  set f := ((O.conductor : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
  set j := ((M⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).restrictScalars ℤ
  have hi : i * one = i := by rw [← Submodule.restrictScalars_mul, mul_one]
  have hbf : b * f = f := by rw [← Submodule.restrictScalars_mul, one_mul]
  have hMj : (M : Submodule (𝓞 K) K).restrictScalars ℤ * j = b := by
    rw [← Submodule.restrictScalars_mul, ← FractionalIdeal.coe_mul, mul_inv_cancel₀ hM,
      FractionalIdeal.coe_one]
  -- `I + 𝔣 = O`, since `I` is coprime to the conductor and `𝔣 ⊆ O`.
  have hif : i ⊔ f = one := restrictScalars_coeIdeal_sup_conductor hI.2
  -- The `ℤ`-submodule `O + 𝔣 M⁻¹` is an inverse of `I`; it lies in `I⁻¹`, so `I * I⁻¹ = O`.
  have hinv : i * (one ⊔ f * j) = one := by
    rw [Submodule.mul_sup, hi, ← hbf, ← mul_assoc, ← mul_assoc, restrictScalars_coeIdeal_mul_one,
      mul_right_comm, hMj, hbf, hif]
  have hIfr : Ifr ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr <|
    (Ideal.map_eq_bot_iff_of_injective O.toRingOfIntegersEquiv.injective).not.mpr hI.1
  have hle : one ⊔ f * j ≤ ((Ifr⁻¹ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
      Submodule O.toSubalgebra K).restrictScalars ℤ := by
    intro x hx
    rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
      FractionalIdeal.mem_inv_iff hIfr]
    intro y hy
    have h := Submodule.mul_mem_mul
      ((Submodule.restrictScalars_mem ℤ _ _).mpr (FractionalIdeal.mem_coe.mpr hy) : y ∈ i) hx
    rw [hinv, Submodule.restrictScalars_mem] at h
    rw [mul_comm, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_one]
    exact h
  have h1 : (1 : K) ∈ i * (one ⊔ f * j) := by
    rw [hinv]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have h2 : (1 : K) ∈ ((Ifr * Ifr⁻¹ : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :
      Submodule O.toSubalgebra K).restrictScalars ℤ := by
    rw [FractionalIdeal.coe_mul, Submodule.restrictScalars_mul]
    exact Submodule.mul_le.mpr (fun m hm n hn => Submodule.mul_mem_mul hm (hle hn)) h1
  refine (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp (le_antisymm
    FractionalIdeal.mul_one_div_le_one ?_)
  rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_one, Submodule.one_le,
    ← Submodule.restrictScalars_mem ℤ]
  exact h2

variable (O)

/-- The invertible fractional ideal of an order attached to a nonzero ideal coprime to the
conductor. -/
def integralIdealsAwayConductorToInvertible :
    O.integralIdealsAwayConductor →* O.invertibleProperFractionalIdeals where
  toFun I := (isUnit_coeIdeal_of_mem_integralIdealsAwayConductor I.2).unit
  map_one' := Units.ext <| by simp [Ideal.map_top]
  map_mul' I J := Units.ext <| by simp [Ideal.map_mul, FractionalIdeal.coeIdeal_mul]

/-- The invertible fractional ideal attached to `I` is `I` itself, as a fractional ideal of the
order. -/
@[simp]
theorem coe_integralIdealsAwayConductorToInvertible_apply (I : O.integralIdealsAwayConductor) :
    (O.integralIdealsAwayConductorToInvertible I :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) =
      (((I : Ideal O.toRingOfIntegers).map O.toRingOfIntegersEquiv : Ideal O.toSubalgebra) :
        FractionalIdeal (nonZeroDivisors O.toSubalgebra) K) :=
  (rfl)

/-- Distinct ideals coprime to the conductor give distinct invertible fractional ideals. -/
theorem integralIdealsAwayConductorToInvertible_injective :
    Function.Injective O.integralIdealsAwayConductorToInvertible := by
  intro I J h
  have h' := congrArg (fun u : O.invertibleProperFractionalIdeals =>
    (u : FractionalIdeal (nonZeroDivisors O.toSubalgebra) K)) h
  simp only [coe_integralIdealsAwayConductorToInvertible_apply] at h'
  have h'' := congrArg (Ideal.comap O.toRingOfIntegersEquiv) (FractionalIdeal.coeIdeal_injective h')
  rwa [Ideal.comap_map_of_bijective _ O.toRingOfIntegersEquiv.bijective,
    Ideal.comap_map_of_bijective _ O.toRingOfIntegersEquiv.bijective, SetLike.coe_eq_coe] at h''

end NumberFieldOrder

end TauCeti.GlobalNumberFields
