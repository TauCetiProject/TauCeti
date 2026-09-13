/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Approximation.Weak
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue
public import TauCeti.RingTheory.Ideal.Quotient.Representative

/-!
# The residue-and-sign presentation of the congruence quotient

Let `𝔪` be a modulus of a number field `K`.  Congruence to one modulo `𝔪` is two independent
conditions on an element of `primeToSubgroup 𝔪`: reduction to one in `(𝓞 K ⧸ 𝔪.finitePart)ˣ`, and
positivity at each real place selected by `𝔪.infinitePart`.  This file packages the two conditions
into one homomorphism

```text
residueSignHom 𝔪 :
  primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ)
```

and proves that it is surjective with kernel exactly `congruenceSubgroup 𝔪`.  The resulting
isomorphism `residueSignEquiv` computes the relative index

```text
(congruenceSubgroup 𝔪).relIndex (primeToSubgroup 𝔪)
  = Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card,
```

which is the residue-and-sign factor of the ray class number formula — the factor *before* the
image of the global units is divided out — and strengthens the bare finiteness recorded by
`congruenceSubgroup_finiteIndex`.

Surjectivity is the arithmetic content and is *not* a chinese-remainder statement: the residue
class and the signs have to be realized by one and the same element of `Kˣ`, so the proof runs
through weak approximation at the mixed set of places consisting of the primes dividing
`𝔪.finitePart` together with all real places
(`exists_fieldUnit_valuation_sub_lt_and_signHom_eq`).  An approximation to a chosen integral
representative of the residue class, to within `v.valuation K` at most `exp (-𝔪.exponent v)` at
each prime of the support, has the same reduction as that representative, because the quotient of
the two differs from one by exactly that much.

The global units of `K` are nowhere quotiented out here.  Their image in this quotient is the
obstruction that glues the residue-unit and sign factors to the ordinary class group inside the
ray class group, and it is why the ray class group is not the product of the three.

## Main definitions

* `TauCeti.GlobalNumberFields.residueSignHom`: the reduction-and-signs homomorphism.
* `TauCeti.GlobalNumberFields.residueSignEquiv`: the induced isomorphism from the congruence
  quotient.

## Main results

* `TauCeti.GlobalNumberFields.residueSignHom_eq_one_iff` and
  `TauCeti.GlobalNumberFields.ker_residueSignHom`: the kernel is the congruence subgroup.
* `TauCeti.GlobalNumberFields.residueSignHom_surjective`: every residue unit and sign pattern is
  realized, together with its two halves `TauCeti.GlobalNumberFields.residueHom_surjective` and
  `TauCeti.GlobalNumberFields.modulusSignHom_surjective`.
* `TauCeti.GlobalNumberFields.relIndex_congruenceSubgroup`: the exact relative index, and its
  narrow specialization `TauCeti.GlobalNumberFields.relIndex_congruenceSubgroup_narrowModulus`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-! ### The signs prescribed by a modulus -/

/-- **The signs of a field unit at the real places selected by a modulus.**  This is `signHom`
restricted to `𝔪.infinitePart`; the real places outside the modulus are unconstrained and are
forgotten. -/
noncomputable def modulusSignHom (𝔪 : Modulus K) : Kˣ →* (𝔪.infinitePart → ℤˣ) where
  toFun x w := signHom x w.1
  map_one' := funext fun w ↦ by rw [map_one, Pi.one_apply, Pi.one_apply]
  map_mul' x y := funext fun w ↦ by rw [map_mul, Pi.mul_apply, Pi.mul_apply]

@[simp] theorem modulusSignHom_apply (𝔪 : Modulus K) (x : Kˣ) (w : 𝔪.infinitePart) :
    modulusSignHom 𝔪 x w = signHom x w.1 := (rfl)

/-- **The prescribed signs are trivial exactly at an element positive on the infinite part.** -/
@[simp] theorem modulusSignHom_eq_one_iff {𝔪 : Modulus K} (x : Kˣ) :
    modulusSignHom 𝔪 x = 1 ↔
      ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K) := by
  rw [funext_iff]
  refine ⟨fun h w hw ↦ ?_, fun h w ↦ ?_⟩
  · exact (signHom_apply_eq_one_iff x ⟨w, w.2⟩).mp (h ⟨w, hw⟩)
  · exact (signHom_apply_eq_one_iff x w.1).mpr (h w.1 w.2)

/-! ### The reduction-and-signs homomorphism -/

/-- **The residue-and-sign presentation of a modulus.**  An element of `Kˣ` that is a unit at every
prime dividing `𝔪.finitePart` has both a reduction in `(𝓞 K ⧸ 𝔪.finitePart)ˣ` and a sign at each
real place selected by `𝔪`; congruence to one modulo `𝔪` is exactly the vanishing of both.

The two factors are the finite and the archimedean halves of the ray class number formula. -/
noncomputable def residueSignHom (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 →* (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (residueHom 𝔪).prod ((modulusSignHom 𝔪).comp (primeToSubgroup 𝔪).subtype)

@[simp] theorem residueSignHom_fst (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (residueSignHom 𝔪 x).1 = residueHom 𝔪 x := (rfl)

@[simp] theorem residueSignHom_snd (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    (residueSignHom 𝔪 x).2 = modulusSignHom 𝔪 (x : Kˣ) := (rfl)

/-- **Congruence to one is exactly trivial reduction together with trivial signs.** -/
@[simp] theorem residueSignHom_eq_one_iff {𝔪 : Modulus K} (x : primeToSubgroup 𝔪) :
    residueSignHom 𝔪 x = 1 ↔ (x : Kˣ) ∈ congruenceSubgroup 𝔪 := by
  rw [Prod.ext_iff, mem_congruenceSubgroup, isCongrOne_iff, Prod.fst_one, Prod.snd_one,
    residueSignHom_fst, residueSignHom_snd, modulusSignHom_eq_one_iff]
  refine and_congr_left fun hpos ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (residue_eq_one_iff x).mp ?_
    rw [← coe_residueHom 𝔪 x, h, Units.val_one]
  · exact residueHom_eq_one_of_mem_congruenceSubgroup
      (mem_congruenceSubgroup.mpr (isCongrOne_iff.mpr ⟨h, hpos⟩))

/-- **The kernel of the residue-and-sign presentation is the congruence subgroup.** -/
theorem ker_residueSignHom (𝔪 : Modulus K) :
    (residueSignHom 𝔪).ker = (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) := by
  ext x
  rw [MonoidHom.mem_ker, residueSignHom_eq_one_iff, Subgroup.mem_subgroupOf]

/-! ### Surjectivity -/

/-- An integral representative of a *unit* residue class lies outside every prime dividing the
finite part: a common prime factor would make `1` divisible by that prime. -/
private theorem notMem_of_quotient_mk_eq_unit {𝔪 : Modulus K} {a : 𝓞 K}
    {u : (𝓞 K ⧸ 𝔪.finitePart)ˣ} (ha : Ideal.Quotient.mk 𝔪.finitePart a = u)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪.finitePart) : a ∉ v.asIdeal := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (𝓞 K ⧸ 𝔪.finitePart)ˣ) :
    𝓞 K ⧸ 𝔪.finitePart)
  have hab : a * b - 1 ∈ 𝔪.finitePart := by
    refine Ideal.Quotient.eq.mp ?_
    rw [map_mul, ha, hb, map_one, Units.mul_inv]
  intro hav
  refine v.isPrime.ne_top (Ideal.eq_top_iff_one _ |>.mpr ?_)
  have hone : (1 : 𝓞 K) = a * b - (a * b - 1) := by ring
  rw [hone]
  exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hav) (Ideal.le_of_dvd hv hab)

/-- The image in `Kˣ` of an integral representative of a unit residue class is a unit at the
finite part, and reduces to the class it represents. -/
private theorem exists_mem_primeToSubgroup_residueHom_eq {𝔪 : Modulus K}
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) :
    ∃ (α : Kˣ) (hα : α ∈ primeToSubgroup 𝔪), residueHom 𝔪 ⟨α, hα⟩ = u := by
  obtain ⟨a, ha0, ha⟩ := Ideal.Quotient.exists_ne_zero_mk_eq 𝔪.finitePart_ne_bot
    ((u : 𝓞 K ⧸ 𝔪.finitePart))
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
  refine ⟨Units.mk0 _ haK, mem_primeToSubgroup.mpr fun v hv ↦ ?_, Units.ext ?_⟩
  · rw [Units.val_mk0, valuation_of_algebraMap]
    exact intValuation_eq_one_iff.mpr (notMem_of_quotient_mk_eq_unit ha hv)
  · rw [coe_residueHom, residue_eq (a := a) (b := 1) _ (by simp) (by simp), ha]

/-- **The residue-and-sign presentation is surjective.**  Every residue unit modulo the finite part
and every pattern of signs at the real places of the modulus are realized simultaneously by one
element of `Kˣ` that is a unit at the finite part.

The two prescriptions are independent: no compatibility between a residue class and a sign pattern
is required, which is what makes the congruence quotient a direct product. -/
theorem residueSignHom_surjective (𝔪 : Modulus K) : Function.Surjective (residueSignHom 𝔪) := by
  -- Weak approximation at the primes of `𝔪.support` together with all the real places: approximate
  -- an integral representative of `u` closely enough to share its reduction, with the signs of `ε`.
  classical
  rintro ⟨u, ε⟩
  obtain ⟨α, hα, hαu⟩ := exists_mem_primeToSubgroup_residueHom_eq u
  -- Extend the prescribed signs by `1` at the real places outside the modulus.
  obtain ⟨x, hxα, hxs⟩ := exists_fieldUnit_valuation_sub_lt_and_signHom_eq (S := 𝔪.support)
    (fun _ ↦ (α : K)) (fun v ↦ WithZero.exp (-(𝔪.exponent v : ℤ)))
    (fun _ _ ↦ WithZero.exp_ne_zero)
    (fun w ↦ if h : w ∈ 𝔪.infinitePart then ε ⟨w, h⟩ else 1)
  -- The approximation is close enough to `α` to have its valuation at the support.
  have hxα' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ 𝔪.finitePart →
      v.valuation K ((x : K) - (α : K)) < v.valuation K (α : K) := fun v hv ↦ by
    rw [mem_primeToSubgroup.mp hα v hv]
    exact lt_of_lt_of_le (hxα v ((Modulus.mem_support_iff 𝔪 v).mpr hv))
      (WithZero.exp_le_one_iff.mpr (neg_nonpos.mpr (Int.natCast_nonneg _)))
  have hx : x ∈ primeToSubgroup 𝔪 := mem_primeToSubgroup.mpr fun v hv ↦ by
    rw [Valuation.map_eq_of_sub_lt (v.valuation K) (hxα' v hv)]
    exact mem_primeToSubgroup.mp hα v hv
  refine ⟨⟨x, hx⟩, Prod.ext ?_ ?_⟩
  · -- The quotient of the approximation by the representative reduces to one.
    have hquot : residueHom 𝔪 (⟨x, hx⟩ * ⟨α, hα⟩⁻¹) = 1 := by
      refine Units.ext ?_
      rw [coe_residueHom, Units.val_one]
      refine (residue_eq_one_iff _).mpr fun v hv ↦ ?_
      have hval : (((⟨x, hx⟩ * ⟨α, hα⟩⁻¹ : primeToSubgroup 𝔪) : Kˣ) : K) - 1 =
          ((x : K) - (α : K)) / (α : K) := by
        rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv, Units.val_inv_eq_inv_val]
        field_simp
      rw [hval, map_div₀, mem_primeToSubgroup.mp hα v hv, div_one]
      exact le_of_lt (hxα v ((Modulus.mem_support_iff 𝔪 v).mpr hv))
    rw [map_mul, map_inv, hαu, mul_inv_eq_one] at hquot
    rw [residueSignHom_fst, hquot]
  · rw [residueSignHom_snd]
    funext w
    rw [modulusSignHom_apply, hxs]
    exact dite_eq_left w.2

/-- **Every residue unit modulo the finite part is the reduction of a field unit prime to it.**
This is the finite half of `residueSignHom_surjective`, and it is what makes the residue-unit
factor of the ray class number formula the *whole* of `(𝓞 K ⧸ 𝔪.finitePart)ˣ` rather than the
image of the algebraic integers prime to `𝔪`. -/
theorem residueHom_surjective (𝔪 : Modulus K) : Function.Surjective (residueHom 𝔪) := fun u ↦ by
  obtain ⟨x, hx⟩ := residueSignHom_surjective 𝔪 (u, 1)
  exact ⟨x, congrArg Prod.fst hx⟩

/-- **Every pattern of signs at the real places of a modulus is realized by a field unit prime to
its finite part.**  This is the archimedean half of `residueSignHom_surjective`.  Unlike
`signHom_surjective`, the realizing element is also constrained at the finite places: it is a unit
at every prime dividing `𝔪.finitePart`. -/
theorem modulusSignHom_surjective (𝔪 : Modulus K) :
    Function.Surjective ((modulusSignHom 𝔪).comp (primeToSubgroup 𝔪).subtype) := fun ε ↦ by
  obtain ⟨x, hx⟩ := residueSignHom_surjective 𝔪 (1, ε)
  exact ⟨x, congrArg Prod.snd hx⟩

/-! ### The congruence quotient and its order -/

/-- **The congruence quotient of a modulus is the residue units times the prescribed signs.**  This
is the presentation of `primeToSubgroup 𝔪 ⧸ congruenceSubgroup 𝔪` that the ray class number formula
is read off, and it is where the finite and the archimedean data of a modulus become independent
coordinates. -/
noncomputable def residueSignEquiv (𝔪 : Modulus K) :
    primeToSubgroup 𝔪 ⧸ (congruenceSubgroup 𝔪).subgroupOf (primeToSubgroup 𝔪) ≃*
      (𝓞 K ⧸ 𝔪.finitePart)ˣ × (𝔪.infinitePart → ℤˣ) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_residueSignHom 𝔪).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (residueSignHom_surjective 𝔪))

@[simp] theorem residueSignEquiv_mk (𝔪 : Modulus K) (x : primeToSubgroup 𝔪) :
    residueSignEquiv 𝔪 (QuotientGroup.mk x) = residueSignHom 𝔪 x := by
  rw [residueSignEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk]

/-- **The exact relative index of the congruence subgroup.**  The elements that are units at the
finite part of `𝔪`, modulo those congruent to one, are counted by the residue units modulo the
finite part times two for each real place of the infinite part.

This refines the finiteness statement `congruenceSubgroup_finiteIndex` to an equality.  It is the
residue-and-sign factor entering the ray class number formula, which multiplies the class number
only after the image of the global units in this quotient is divided out; that image is the
obstruction described in the module docstring. -/
theorem relIndex_congruenceSubgroup (𝔪 : Modulus K) :
    (congruenceSubgroup 𝔪).relIndex (primeToSubgroup 𝔪) =
      Nat.card (𝓞 K ⧸ 𝔪.finitePart)ˣ * 2 ^ 𝔪.infinitePart.card := by
  rw [Subgroup.relIndex, ← ker_residueSignHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (residueSignHom_surjective 𝔪),
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_prod, Nat.card_pi]
  congr 1
  rw [Finset.prod_const, Nat.card_eq_fintype_card, Fintype.card_units_int, Finset.card_univ,
    Fintype.card_coe]

variable (K) in
/-- **The narrow modulus is counted by the real places alone.**  Its finite part is the unit ideal,
so the residue-unit factor disappears and the congruence quotient is the sign group `{±1}^{r₁}`.

This is the nonempty-infinite-part specialization of `relIndex_congruenceSubgroup`: over a field
with a real place it is `2 ^ r₁ > 1`, so the narrow conditions do not collapse to the wide ones. -/
theorem relIndex_congruenceSubgroup_narrowModulus :
    (congruenceSubgroup (narrowModulus K)).relIndex (primeToSubgroup (narrowModulus K)) =
      2 ^ InfinitePlace.nrRealPlaces K := by
  classical
  have hcard : (narrowModulus K).infinitePart.card = InfinitePlace.nrRealPlaces K := by
    have huniv : (narrowModulus K).infinitePart = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr mem_narrowModulus_infinitePart
    rw [huniv, Finset.card_univ]
  have hunits : Nat.card (𝓞 K ⧸ (narrowModulus K).finitePart)ˣ = 1 := by
    have : Subsingleton (𝓞 K ⧸ (narrowModulus K).finitePart) :=
      Ideal.Quotient.subsingleton_iff.mpr narrowModulus_finitePart
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  rw [relIndex_congruenceSubgroup, hunits, hcard, one_mul]

end TauCeti.GlobalNumberFields
