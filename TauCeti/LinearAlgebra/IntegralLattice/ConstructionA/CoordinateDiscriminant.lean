/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Even
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic

/-!
# The coordinate alphabet as the discriminant module of `m ℤ^ι`

Construction A applied to the zero code produces the lattice `L₀` with carrier `m ℤ^ι` inside
`ℚ^ι` and form `B_m (x, y) = (∑ i, xᵢ yᵢ) / m`.  Its dual carrier is the full integer coordinate
lattice `ℤ^ι`, so its discriminant group is `ℤ^ι / m ℤ^ι`, which reduction modulo `m` identifies
with the word space `(ℤ/m)^ι`.

This file exhibits that identification as an isometry of finite bilinear modules

```text
A_{L₀} ≅ (ℤ/m)^ι,
```

where the right-hand side is the coordinate power of the standard alphabet
`TauCeti.FiniteBilinearModule.zmodStandard`, whose pairing is `xy / m`.  The class of an integer
vector `z` goes to its coordinatewise reduction, and the discriminant pairing of two such classes
is `(∑ i, zᵢ wᵢ) / m` modulo `ℤ`.  When `m` is even, `L₀` is an even lattice and the same map is
an isometry of finite quadratic modules for the half-norm convention: the discriminant quadratic
value of the class of `z` is `(∑ i, zᵢ²) / (2m)` modulo `ℤ`.

Through this identification an additive code over `ℤ/m` is literally a subgroup of the
discriminant module of an integral lattice, which is the form in which codes feed the
isotropic-subgroup and gluing constructions for lattices.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3, and
  Chapter 7, §§8–9, for codes in discriminant-glue coordinates.
* W. Ebeling, *Lattices and Codes*, §§1.3 and 3.3.
* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.1.
* `TauCeti.IntegralLattice.rankOne`, the formal rank-one analogue adapted here to coordinate
  powers with the Construction A normalization.
-/

public section

namespace TauCeti.ConstructionA

open Matrix

variable (m : ℕ+) (ι : Type*) [Fintype ι]

/-! ## The zero-code lattice and its dual carrier -/

/-- **The Construction A lattice of the zero code**: the lattice `L₀` with carrier `m ℤ^ι` in
`ℚ^ι`, carrying the normalized form `B_m`.

Its dual carrier is the full integer coordinate lattice, and its discriminant module is the
coordinate alphabet in which codes over `ℤ/m` live. -/
def zeroLattice : IntegralLattice (ι → ℚ) :=
  integralLattice m (⊥ : AddSubgroup (ι → ZMod m)) (by simp)

theorem zeroLattice_carrier :
    (zeroLattice m ι).carrier = lattice m (⊥ : AddSubgroup (ι → ZMod m)) := by
  simp [zeroLattice]

@[simp]
theorem zeroLattice_form : (zeroLattice m ι).form = form m := by
  simp [zeroLattice]

instance : (zeroLattice m ι).IsNondegenerate := by
  rw [zeroLattice]
  infer_instance

/-- **The carrier of the zero-code lattice is `m ℤ^ι`**: an integer vector lies in it exactly
when `m` divides each of its coordinates. -/
@[simp]
theorem intCast_mem_zeroLattice_carrier_iff (z : ι → ℤ) :
    (fun i ↦ (z i : ℚ)) ∈ (zeroLattice m ι).carrier ↔ ∀ i, ((m : ℕ) : ℤ) ∣ z i := by
  rw [zeroLattice_carrier, intCast_mem_lattice]
  simp [funext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The dual carrier of the zero-code lattice is `ℤ^ι`**, the Construction A carrier of the
whole word space. -/
@[simp]
theorem zeroLattice_dualCarrier :
    (zeroLattice m ι).dualCarrier = lattice m (⊤ : AddSubgroup (ι → ZMod m)) := by
  have hbot : AddSubgroup.toZModSubmodule (m : ℕ) (⊥ : AddSubgroup (ι → ZMod m)) = ⊥ := by
    ext x
    simp
  rw [IntegralLattice.dualCarrier, zeroLattice_form, zeroLattice_carrier, dualSubmodule_lattice,
    hbot, Submodule.euclideanDual_bot_eq_top]
  exact congrArg (lattice m) (Submodule.toAddSubgroup_eq_top.mpr rfl)

/-- **A rational vector is dual to the zero-code lattice exactly when it has integer
coordinates.** -/
theorem mem_zeroLattice_dualCarrier_iff {x : ι → ℚ} :
    x ∈ (zeroLattice m ι).dualCarrier ↔ ∃ z : ι → ℤ, (fun i ↦ (z i : ℚ)) = x := by
  rw [zeroLattice_dualCarrier, mem_lattice]
  simp

private theorem intCastPi_mem_dualCarrier (z : ι → ℤ) :
    (Int.castAddHom ℚ).toIntLinearMap.compLeft ι z ∈ (zeroLattice m ι).dualCarrier :=
  (mem_zeroLattice_dualCarrier_iff m ι).mpr ⟨z, rfl⟩

/-- **The dual carrier of the zero-code lattice is the integer coordinate lattice**, presented as
a `ℤ`-linear equivalence with `ℤ^ι` given by the coordinatewise integer cast. -/
noncomputable def dualCarrierIntEquiv : (ι → ℤ) ≃ₗ[ℤ] (zeroLattice m ι).dualCarrier :=
  LinearEquiv.ofBijective
    (((Int.castAddHom ℚ).toIntLinearMap.compLeft ι).codRestrict _
      (intCastPi_mem_dualCarrier m ι))
    ⟨fun _ _ h ↦ (Function.Injective.piMap fun _ ↦ Int.cast_injective)
        (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨z, hz⟩ := (mem_zeroLattice_dualCarrier_iff m ι).mp x.2
      exact ⟨z, Subtype.ext hz⟩⟩

@[simp]
theorem coe_dualCarrierIntEquiv_apply (z : ι → ℤ) :
    ((dualCarrierIntEquiv m ι z : (zeroLattice m ι).dualCarrier) : ι → ℚ) =
      fun i ↦ (z i : ℚ) := (rfl)

/-! ## The discriminant group as the word space over `ℤ/m` -/

/-- Reduction of a dual vector modulo `m`, read off its integer coordinates. -/
private noncomputable def toCoordinate :
    (zeroLattice m ι).dualCarrier →ₗ[ℤ] (ι → ZMod (m : ℕ)) :=
  ((Int.castAddHom (ZMod (m : ℕ))).toIntLinearMap.compLeft ι).comp
    (dualCarrierIntEquiv m ι).symm.toLinearMap

private theorem toCoordinate_dualCarrierIntEquiv (z : ι → ℤ) :
    toCoordinate m ι (dualCarrierIntEquiv m ι z) = fun i ↦ ((z i : ZMod (m : ℕ))) := by
  rw [toCoordinate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

private theorem toCoordinate_surjective : Function.Surjective (toCoordinate m ι) := fun c ↦ by
  obtain ⟨z, rfl⟩ := (Function.Surjective.piMap fun _ ↦ ZMod.intCast_surjective) c
  exact ⟨dualCarrierIntEquiv m ι z, toCoordinate_dualCarrierIntEquiv m ι z⟩

private theorem ker_toCoordinate :
    LinearMap.ker (toCoordinate m ι) = (zeroLattice m ι).carrierInDual := by
  ext x
  obtain ⟨z, rfl⟩ := (dualCarrierIntEquiv m ι).surjective x
  rw [LinearMap.mem_ker, toCoordinate_dualCarrierIntEquiv,
    IntegralLattice.mem_carrierInDual_iff, coe_dualCarrierIntEquiv_apply,
    intCast_mem_zeroLattice_carrier_iff]
  simp [funext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Reduction modulo `m` identifies the discriminant group of the zero-code lattice with the
word space `(ℤ/m)^ι`.** -/
noncomputable def discriminantEquiv :
    (zeroLattice m ι).DiscriminantGroup ≃ₗ[ℤ] (ι → ZMod (m : ℕ)) :=
  (Submodule.quotEquivOfEq _ _ (ker_toCoordinate m ι).symm).trans
    ((toCoordinate m ι).quotKerEquivOfSurjective (toCoordinate_surjective m ι))

private theorem discriminantEquiv_mk (x : (zeroLattice m ι).dualCarrier) :
    discriminantEquiv m ι (Submodule.Quotient.mk x) = toCoordinate m ι x := by
  rw [discriminantEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The discriminant class of an integer vector goes to its coordinatewise reduction modulo
`m`. -/
@[simp]
theorem discriminantEquiv_mk_intCast (z : ι → ℤ) :
    discriminantEquiv m ι (Submodule.Quotient.mk (dualCarrierIntEquiv m ι z)) =
      fun i ↦ ((z i : ZMod (m : ℕ))) := by
  rw [discriminantEquiv_mk, toCoordinate_dualCarrierIntEquiv]

/-- Reduction of a quotient representative whose underlying dual vector has integer coordinates.
This form is independent of the proof that the displayed vector belongs to the dual carrier. -/
theorem discriminantEquiv_mk_of_intCast (z : ι → ℤ)
    (hz : (fun i ↦ (z i : ℚ)) ∈ (zeroLattice m ι).dualCarrier) :
    discriminantEquiv m ι
        (Submodule.Quotient.mk (⟨(fun i ↦ (z i : ℚ)), hz⟩ : (zeroLattice m ι).dualCarrier)) =
      fun i ↦ ((z i : ZMod (m : ℕ))) := by
  have hrep : (⟨(fun i ↦ (z i : ℚ)), hz⟩ : (zeroLattice m ι).dualCarrier) =
      dualCarrierIntEquiv m ι z := by
    apply Subtype.ext
    exact (coe_dualCarrierIntEquiv_apply m ι z).symm
  rw [hrep, discriminantEquiv_mk_intCast]

/-- The inverse identification sends a word to the discriminant class of any coordinatewise
integer lift. -/
@[simp]
theorem discriminantEquiv_symm_intCast (z : ι → ℤ) :
    (discriminantEquiv m ι).symm (fun i ↦ ((z i : ZMod (m : ℕ)))) =
      Submodule.Quotient.mk (dualCarrierIntEquiv m ι z) :=
  (discriminantEquiv m ι).symm_apply_eq.mpr (discriminantEquiv_mk_intCast m ι z).symm

/-- **The discriminant pairing of the zero-code lattice is the normalized dot product of integer
lifts**, `(∑ i, zᵢ wᵢ) / m` modulo `ℤ`. -/
theorem zeroLattice_discriminantPairing_mk_intCast (z w : ι → ℤ) :
    (zeroLattice m ι).discriminantPairing
        (Submodule.Quotient.mk (dualCarrierIntEquiv m ι z))
        (Submodule.Quotient.mk (dualCarrierIntEquiv m ι w)) =
      (((∑ i, (z i : ℚ) * (w i : ℚ)) / m : ℚ) : AddCircle (1 : ℚ)) := by
  rw [IntegralLattice.discriminantPairing_mk, zeroLattice_form,
    coe_dualCarrierIntEquiv_apply, coe_dualCarrierIntEquiv_apply, form_apply, dotProduct]

private theorem pairing_discriminantEquiv (x y : (zeroLattice m ι).DiscriminantGroup) :
    ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι).pairing
        (discriminantEquiv m ι x) (discriminantEquiv m ι y) =
      (zeroLattice m ι).discriminantBilinearModule.pairing x y := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      obtain ⟨z, rfl⟩ := (dualCarrierIntEquiv m ι).surjective x
      obtain ⟨w, rfl⟩ := (dualCarrierIntEquiv m ι).surjective y
      rw [IntegralLattice.discriminantBilinearModule_pairing,
        zeroLattice_discriminantPairing_mk_intCast, discriminantEquiv_mk_intCast,
        discriminantEquiv_mk_intCast, coordinatePower_zmodStandard_pairing_intCast]

/-- **The discriminant module of the zero-code lattice is the coordinate alphabet over `ℤ/m`.**

The underlying equivalence is reduction modulo `m` of integer coordinates. -/
noncomputable def discriminantIsometry :
    FiniteBilinearModule.Isometry (zeroLattice m ι).discriminantBilinearModule
      ((FiniteBilinearModule.zmodStandard (m : ℕ)).coordinatePower ι) where
  toAddEquiv := (discriminantEquiv m ι).toAddEquiv
  map_pairing' := pairing_discriminantEquiv m ι

@[simp]
theorem discriminantIsometry_apply (x : (zeroLattice m ι).DiscriminantGroup) :
    discriminantIsometry m ι x = discriminantEquiv m ι x := (rfl)

/-! ## The quadratic refinement for an even modulus -/

/-- **Over an even modulus the zero-code lattice is even**: the code `⊥` is quadratically
isotropic for the coordinate alphabet. -/
theorem isEven_zeroLattice (hm : Even (m : ℕ)) : (zeroLattice m ι).IsEven := by
  rw [zeroLattice, isEven_integralLattice_iff m hm]
  intro x hx
  rw [AddSubgroup.mem_bot.mp hx]
  simp

/-- **The discriminant quadratic value of the zero-code lattice is the normalized sum of squares
of an integer lift**, `(∑ i, zᵢ²) / (2m)` modulo `ℤ`. -/
theorem zeroLattice_discriminantQuadraticMap_mk_intCast (hm : Even (m : ℕ)) (z : ι → ℤ) :
    (zeroLattice m ι).discriminantQuadraticMap (isEven_zeroLattice m ι hm)
        (Submodule.Quotient.mk (dualCarrierIntEquiv m ι z)) =
      (((∑ i, (z i : ℚ) ^ 2) / (2 * m) : ℚ) : AddCircle (1 : ℚ)) := by
  rw [IntegralLattice.discriminantQuadraticMap_mk, zeroLattice_form,
    coe_dualCarrierIntEquiv_apply, form_apply]
  congr 1
  rw [dotProduct]
  field_simp [Finset.sum_div]

private theorem quadratic_discriminantEquiv (hm : Even (m : ℕ))
    (x : (zeroLattice m ι).DiscriminantGroup) :
    ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι).quadratic
        (discriminantEquiv m ι x) =
      ((zeroLattice m ι).discriminantQuadraticModule (isEven_zeroLattice m ι hm)).quadratic x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    obtain ⟨z, rfl⟩ := (dualCarrierIntEquiv m ι).surjective x
    rw [IntegralLattice.discriminantQuadraticModule_quadratic,
      zeroLattice_discriminantQuadraticMap_mk_intCast m ι hm, discriminantEquiv_mk_intCast,
      coordinatePower_zmodStandard_quadratic_intCast (m : ℕ) hm]

/-- **Over an even modulus the discriminant quadratic module of the zero-code lattice is the
quadratic coordinate alphabet over `ℤ/m`**, in the half-norm convention. -/
noncomputable def discriminantQuadraticIsometry (hm : Even (m : ℕ)) :
    FiniteQuadraticModule.Isometry
      ((zeroLattice m ι).discriminantQuadraticModule (isEven_zeroLattice m ι hm))
      ((FiniteQuadraticModule.zmodStandard (m : ℕ) hm).coordinatePower ι) where
  __ := discriminantEquiv m ι
  map_app' := quadratic_discriminantEquiv m ι hm

@[simp]
theorem discriminantQuadraticIsometry_apply (hm : Even (m : ℕ))
    (x : (zeroLattice m ι).DiscriminantGroup) :
    discriminantQuadraticIsometry m ι hm x = discriminantEquiv m ι x := (rfl)

/-- Forgetting the quadratic map from the even-modulus isometry recovers the bilinear
identification of the discriminant module with the coordinate alphabet. -/
@[simp]
theorem discriminantQuadraticIsometry_toFiniteBilinearModule (hm : Even (m : ℕ)) :
    (discriminantQuadraticIsometry m ι hm).toFiniteBilinearModule =
      discriminantIsometry m ι := by
  apply FiniteBilinearModule.Isometry.toAddEquiv_injective
  rw [FiniteQuadraticModule.Isometry.toFiniteBilinearModule_toAddEquiv]
  rfl

end TauCeti.ConstructionA
