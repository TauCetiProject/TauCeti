/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Commutator.Basic
public import TauCeti.RingTheory.Nilpotent.RootString.G2.ShortPair

/-!
# The G₂ short-pair exponential relation from Lie brackets

This is the shared scaled-operator transport for the Kostant and pinned Chevalley short-pair
relations. It requires divided-power stability only for the five vectors involved, not stability
under a specified Kostant form.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L V : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
variable {ι : Type*} (e : ι → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V) (M : AddSubgroup V)
variable {A : Type*} [CommRing A] [Algebra ℤ A]

noncomputable section

/-- The three-factor integral exponential relation for a short pair, with the integer scalars
absorbed into the parameters. The scaled brackets retain the factors two and three. -/
theorem baseChangeExp_mul_baseChangeExp_of_g2_short_pair_lie
    {i j k l m : ι} {c d a : ℤ}
    (hij : ⁅e i, e j⁆ = (2 * c) • e k)
    (hik : c • ⁅e i, e k⁆ = (3 * d) • e l)
    (hkj : c • ⁅e k, e j⁆ = (3 * a) • e m)
    (hil : ⁅e i, e l⁆ = 0) (him : ⁅e i, e m⁆ = 0) (hjm : ⁅e j, e m⁆ = 0)
    (hkl : ⁅e k, e l⁆ = 0) (hkm : ⁅e k, e m⁆ = 0) (hlm : ⁅e l, e m⁆ = 0)
    (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
    (hk : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))
    (hl : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))))
    (hMi : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) • v ∈ M)
    (hMj : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) • v ∈ M)
    (hMk : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) • v ∈ M)
    (hMl : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))) • v ∈ M)
    (hMm : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))) • v ∈ M)
    (u v : A) :
    baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M hMi u *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) M hMj v =
      baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))) M hMj v *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))) M hMk
          ((c : A) * (2 * u * v)) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e l))) M hMl
          ((d : A) * (3 * u ^ 2 * v)) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e m))) M hMm
          ((a : A) * (3 * u * v ^ 2)) *
        baseChangeExp (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))) M hMi u := by
  let E r := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e r))
  have hxy : E i * E j = E j * E i + 2 • (c • E k) := by
    simpa only [one_zsmul, one_mul] using
      zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := 1) (q := 1) (r := c) (n := 2) (by simpa using hij)
  have hxz : E i * (c • E k) = (c • E k) * E i + 3 • (d • E l) := by
    simpa only [one_zsmul, one_mul] using
      zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := 1) (q := c) (r := d) (n := 3) (by simpa using hik)
  have hzy : (c • E k) * E j = E j * (c • E k) + 3 • (a • E m) := by
    simpa only [one_zsmul, one_mul] using
      zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ
        (p := c) (q := 1) (r := a) (n := 3) (by simpa using hkj)
  have hMck := fun n => Associative.dividedPower_zsmul_smul_mem c _ M (hMk n)
  have hMdl := fun n => Associative.dividedPower_zsmul_smul_mem d _ M (hMl n)
  have hMam := fun n => Associative.dividedPower_zsmul_smul_mem a _ M (hMm n)
  rw [← baseChangeExp_zsmul c M hMk hMck hk,
    ← baseChangeExp_zsmul d M hMl hMdl hl, ← baseChangeExp_zsmul a M hMm hMam hm]
  exact baseChangeExp_mul_baseChangeExp_of_g2_short_pair M hxy hxz hzy
    ((commute_of_lie_eq_zero ρ hil).smul_right d)
    ((commute_of_lie_eq_zero ρ him).smul_right a)
    ((commute_of_lie_eq_zero ρ hjm).smul_right a)
    (((commute_of_lie_eq_zero ρ hkl).smul_left c).smul_right d)
    (((commute_of_lie_eq_zero ρ hkm).smul_left c).smul_right a)
    (((commute_of_lie_eq_zero ρ hlm).smul_left d).smul_right a)
    hi hj (hk.smul c) hMi hMj hMck hMdl hMam u v

end

end TauCeti.UniversalEnvelopingAlgebra
