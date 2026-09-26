/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Prime
public import TauCeti.RingTheory.Localization.AsSubring

/-!
# The localization of a holomorphy ring away from a function

Let `F / k` be an algebraic function field, `S` a set of places of `F / k` and `𝒪_S` its
holomorphy ring. For a nonzero `x ∈ 𝒪_S`, inverting `x` gives the localization `𝒪_S[1/x]`,
realized inside `F` by Mathlib's `Localization.subalgebra.ofField`. This file identifies it:
`𝒪_S[1/x]` is the holomorphy ring of the places of `S` at which `x⁻¹` is regular. A function
regular at those places has its poles on `S` only among the finitely many zeros of `x`, so a
sufficiently high power of `x` clears them (`TauCeti.exists_pow_mul_mem_holomorphyRing`).

The identification is stated for a subalgebra `A` of `F` that is, as a set, the holomorphy ring of
`S`, so that it applies to the affine models of `F / k` as well as to `𝒪_S` itself. When `A` is a
Dedekind domain, the places of the localization's finite chart are its height one primes.

## Main results

* `TauCeti.coe_ofField_powers_eq_holomorphyRing`: if a subalgebra `A` of `F` is the holomorphy ring
  of a set `S` of places and `x ∈ A`, then the localization `A[1/x] ⊆ F` is the holomorphy ring of
  the places of `S` at which `x⁻¹` is regular; `TauCeti.mem_ofField_powers_iff_forall_mem_integers`
  is the membership form.
* `TauCeti.forall_algebraMap_mem_integers_ofField_powers_iff`: the finite chart of `A[1/x]` is the
  set of places of `S` at which `x⁻¹` is regular.
* `TauCeti.ofFieldPowersHeightOneSpectrumEquiv`: for a Dedekind `A`, the places of that chart are
  the height one primes of `A[1/x]`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2.
-/

public section

open IsDedekindDomain Localization.subalgebra

open scoped nonZeroDivisors

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]

variable {R : Type*} [CommRing R] [Algebra R F] {A : Subalgebra R F} [IsFractionRing A F]
  {S : Set (Place k F)}

/-- **`𝒪_S[1/x]` is the holomorphy ring of the places of `S` at which `x⁻¹` is regular.** Stated
for a subalgebra `A` of `F` that is, as a set, the holomorphy ring of `S`, so that it applies to the
affine model `R_x` as well as to `𝒪_S` itself. -/
theorem coe_ofField_powers_eq_holomorphyRing (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰) :
    (ofField F (Submonoid.powers x) hx : Set F) =
      holomorphyRing (S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers}) := by
  have hA' : ∀ y : F, y ∈ A ↔ y ∈ holomorphyRing S := fun y ↦ by
    rw [← SetLike.mem_coe, hA, SetLike.mem_coe]
  have hx0 : (x : F) ≠ 0 := fun h ↦
    nonZeroDivisors.ne_zero (hx (Submonoid.mem_powers x)) (Subtype.ext h)
  ext z
  rw [SetLike.mem_coe, mem_ofField_powers_iff, Subalgebra.range_algebraMap, SetLike.mem_coe,
    mem_holomorphyRing_iff]
  simp only [Subalgebra.mem_toSubring, Subalgebra.algebraMap_apply, hA', mem_holomorphyRing_iff,
    Set.mem_inter_iff, Set.mem_ofPred_eq, and_imp]
  constructor
  · rintro ⟨n, hn⟩ P hP hPx
    have hz : z = (x : F)⁻¹ ^ n * ((x : F) ^ n * z) := by
      rw [← mul_assoc, inv_pow, inv_mul_cancel₀ (pow_ne_zero n hx0), one_mul]
    rw [hz]
    exact mul_mem (pow_mem hPx n) (hn P hP)
  · intro h
    obtain ⟨n, hn⟩ :=
      exists_pow_mul_mem_holomorphyRing hF ((hA' x).mp x.2) fun P hP hPx ↦ h P hP hPx
    exact ⟨n, mem_holomorphyRing_iff.mp hn⟩

/-- **Membership in `𝒪_S[1/x]`**: a function lies in the localization exactly when it is regular
at every place of `S` at which `x⁻¹` is regular. -/
theorem mem_ofField_powers_iff_forall_mem_integers (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    {z : F} :
    z ∈ ofField F (Submonoid.powers x) hx ↔
      ∀ P ∈ S, (x : F)⁻¹ ∈ P.integers → z ∈ P.integers := by
  rw [← SetLike.mem_coe, coe_ofField_powers_eq_holomorphyRing hF hA x hx, SetLike.mem_coe,
    mem_holomorphyRing_iff]
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_imp]

/-- **The finite chart of `𝒪_S[1/x]`**: a place is finite on the localization exactly when it
belongs to `S` and `x⁻¹` is regular there. -/
theorem forall_algebraMap_mem_integers_ofField_powers_iff (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    {P : Place k F} :
    (∀ a : ofField F (Submonoid.powers x) hx, algebraMap _ F a ∈ P.integers) ↔
      P ∈ S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers} := by
  rw [← coe_holomorphyRing_subset_integers_iff hF,
    ← coe_ofField_powers_eq_holomorphyRing hF hA x hx]
  exact ⟨fun h a ha ↦ h ⟨a, ha⟩, fun h a ↦ h a.2⟩

variable [Algebra k A] [IsScalarTower k A F] [IsDedekindDomain A]

/-- **The height one primes of `𝒪_S[1/x]` are the places of `S` at which `x⁻¹` is regular**, for
a Dedekind `𝒪_S`: `TauCeti.Place.heightOneSpectrumEquiv` for the localization, read along the
identification of its finite chart. -/
noncomputable def ofFieldPowersHeightOneSpectrumEquiv (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰) :
    ↥(S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers}) ≃
      HeightOneSpectrum (ofField F (Submonoid.powers x) hx) :=
  (Equiv.subtypeEquivRight fun _ ↦
      (forall_algebraMap_mem_integers_ofField_powers_iff hF hA x hx).symm).trans
    (Place.heightOneSpectrumEquiv k F _)

@[simp]
theorem ofFieldPowersHeightOneSpectrumEquiv_apply (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    (P : ↥(S ∩ {P : Place k F | (x : F)⁻¹ ∈ P.integers})) :
    ofFieldPowersHeightOneSpectrumEquiv hF hA x hx P =
      (P : Place k F).center
        ((forall_algebraMap_mem_integers_ofField_powers_iff hF hA x hx).mpr P.2) :=
  Place.heightOneSpectrumEquiv_apply k F _

@[simp]
theorem coe_ofFieldPowersHeightOneSpectrumEquiv_symm_apply (hF : IsFunctionField k F)
    (hA : (A : Set F) = (holomorphyRing S : Set F)) (x : A) (hx : Submonoid.powers x ≤ A⁰)
    (𝔭 : HeightOneSpectrum (ofField F (Submonoid.powers x) hx)) :
    ((ofFieldPowersHeightOneSpectrumEquiv hF hA x hx).symm 𝔭 : Place k F) =
      Place.ofPrime k F 𝔭 :=
  Place.coe_heightOneSpectrumEquiv_symm_apply k F 𝔭

end TauCeti
