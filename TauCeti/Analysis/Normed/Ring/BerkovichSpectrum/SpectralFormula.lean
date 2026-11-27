/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.BerkovichSpectrum
public import TauCeti.Analysis.Normed.Unbundled.MulRingSeminorm.Smoothing

/-!
# Berkovich's spectral formula and nonemptiness of the Berkovich spectrum

Over a commutative seminormed ring `A`, combining `RingSeminorm.smoothing` with
Bosch–Güntzer–Remmert Theorem 1.3.2/3 (`RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`) yields
**Berkovich's spectral formula** (`TauCeti.Spectrum.smoothingFun_eq_sSup`): for every `a : A`,
`smoothingFun (normRingSeminorm A) a` is the supremum of `x a` over `x : Spectrum A`, and when
`normRingSeminorm A ≠ 0` (in particular on every nontrivial normed commutative ring) the spectrum
`TauCeti.Spectrum A` is nonempty (`TauCeti.Spectrum.instNonempty`) and the maximum is attained at a
point of `Spectrum A` (`TauCeti.Spectrum.exists_apply_eq_smoothingFun`).

## Main results

* `TauCeti.Spectrum.apply_le_smoothingFun`, `TauCeti.Spectrum.smoothingFun_eq_sSup`,
  `TauCeti.Spectrum.exists_apply_eq_smoothingFun_of_normRingSeminorm_ne_zero`,
  `TauCeti.Spectrum.exists_apply_eq_smoothingFun`, `TauCeti.Spectrum.isGreatest_range_eval`:
  Berkovich's spectral formula for `TauCeti.Spectrum A`.
* `TauCeti.Spectrum.smoothingFun_eq_zero_of_isNilpotent`,
  `TauCeti.Spectrum.sSup_range_eval_eq_zero_of_isNilpotent`: vanishing on nilpotents.
* `TauCeti.Spectrum.instNonempty`, `TauCeti.Spectrum.nonempty_iff_norm_one_ne_zero`,
  `TauCeti.Spectrum.nonempty_iff_nontrivial`: nonemptiness of the Berkovich spectrum on nontrivial
  normed commutative rings.

## References

* V. G. Berkovich, *Spectral Theory and Analytic Geometry over Non-Archimedean Fields*,
  Mathematical Surveys and Monographs 33, AMS, 1990, §1.2 (Theorem 1.2.1) and §1.3 (Theorem 1.3.1).
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.3 (Definition 2.3.2, Theorem 2.3.4, Theorem 2.3.10, Remark 2.3.11(b)).
* S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*, §1.3.2, Theorem 3 (and
  Proposition 2 for `seminormFromConst`).
-/

public section

namespace TauCeti.Spectrum

section SeminormedCommRing

variable {A : Type*} [SeminormedCommRing A]

private theorem normRingSeminorm_ne_zero_of_norm_one_ne_zero (h1 : ‖(1 : A)‖ ≠ 0) :
    normRingSeminorm A ≠ 0 :=
  RingSeminorm.ne_zero_iff.2 ⟨1, h1⟩

/-- Over a commutative seminormed ring, every `x : Spectrum A` is bounded above by the spectral
seminorm `smoothingFun (normRingSeminorm A)`. -/
theorem apply_le_smoothingFun (x : Spectrum A) (a : A) :
    x a ≤ smoothingFun (normRingSeminorm A) a := by
  rw [← coe_toMulRingSeminorm]
  exact x.toMulRingSeminorm.le_smoothingFun_of_le_mul (μ := normRingSeminorm A) (C := 1)
    (fun b ↦ (x.apply_le_norm b).trans_eq (one_mul _).symm) a

/-- If the ambient seminorm on a commutative ring is not identically zero, then for every `a : A`
there exists a point `x : Spectrum A` attaining `smoothingFun (normRingSeminorm A) a`. -/
theorem exists_apply_eq_smoothingFun_of_normRingSeminorm_ne_zero (h : normRingSeminorm A ≠ 0)
    (a : A) :
    ∃ x : Spectrum A, x a = smoothingFun (normRingSeminorm A) a := by
  have hsm : (normRingSeminorm A).smoothing ≠ 0 :=
    RingSeminorm.smoothing_eq_zero_iff.not.2 h
  obtain ⟨α₀, hα₀, hα₀a⟩ :=
    RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq
      (normRingSeminorm A).isPowMul_smoothing hsm a
  refine ⟨⟨α₀, fun b ↦ (hα₀ b).trans ((normRingSeminorm A).smoothing_le_self b)⟩, ?_⟩
  rw [coe_mk, hα₀a, (normRingSeminorm A).smoothing_apply a]

/-- Over a commutative seminormed ring, `Spectrum A` is nonempty if and only if
`‖(1 : A)‖ ≠ 0`. -/
theorem nonempty_iff_norm_one_ne_zero :
    Nonempty (Spectrum A) ↔ ‖(1 : A)‖ ≠ 0 := by
  refine ⟨fun ⟨x⟩ h1 ↦ (isEmpty_of_norm_one_eq_zero h1).false x, fun h1 ↦ ?_⟩
  obtain ⟨x, -⟩ := exists_apply_eq_smoothingFun_of_normRingSeminorm_ne_zero
    (normRingSeminorm_ne_zero_of_norm_one_ne_zero h1) 1
  exact ⟨x⟩

/-- On a commutative seminormed ring with nonempty Berkovich spectrum (in particular on every
nontrivial normed commutative ring), every `a : A` attains its spectral seminorm at some point of
`Spectrum A` (Berkovich Theorem 1.3.1; Kedlaya–Liu Theorem 2.3.10). -/
theorem exists_apply_eq_smoothingFun [Nonempty (Spectrum A)] (a : A) :
    ∃ x : Spectrum A, x a = smoothingFun (normRingSeminorm A) a :=
  exists_apply_eq_smoothingFun_of_normRingSeminorm_ne_zero
    (normRingSeminorm_ne_zero_of_norm_one_ne_zero (nonempty_iff_norm_one_ne_zero.1 ‹_›)) a

/-- On a commutative seminormed ring with nonempty Berkovich spectrum (in particular on every
nontrivial normed commutative ring), `smoothingFun (normRingSeminorm A) a` is the greatest element
of `{x a | x : Spectrum A}`. -/
theorem isGreatest_range_eval [Nonempty (Spectrum A)] (a : A) :
    IsGreatest (Set.range fun x : Spectrum A ↦ x a)
      (smoothingFun (normRingSeminorm A) a) := by
  obtain ⟨x, hx⟩ := exists_apply_eq_smoothingFun a
  exact ⟨⟨x, hx⟩, by rintro _ ⟨y, rfl⟩; exact y.apply_le_smoothingFun a⟩

/-- **Berkovich's spectral formula** (Berkovich Theorem 1.3.1; Kedlaya–Liu Theorem 2.3.10 and
Remark 2.3.11(b)). For every commutative seminormed ring `A` and every `a : A`, the spectral
seminorm `smoothingFun (normRingSeminorm A) a` equals the supremum of `x a` over
`x : Spectrum A` (including when `Spectrum A` is empty, where both sides are `0`). -/
theorem smoothingFun_eq_sSup (a : A) :
    smoothingFun (normRingSeminorm A) a = sSup (Set.range fun x : Spectrum A ↦ x a) := by
  rw [← (normRingSeminorm A).smoothing_apply,
    (normRingSeminorm A).smoothing_eq_sSup_mulRingSeminorm a]
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq, Set.mem_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨α₀, hα₀, rfl⟩
    exact ⟨⟨α₀, hα₀⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMulRingSeminorm, x.apply_le_norm, rfl⟩

/-- The spectral seminorm of a commutative seminormed ring vanishes on nilpotent elements. -/
theorem smoothingFun_eq_zero_of_isNilpotent {a : A} (ha : IsNilpotent a) :
    smoothingFun (normRingSeminorm A) a = 0 := by
  rw [← (normRingSeminorm A).smoothing_apply]
  exact (normRingSeminorm A).smoothing_eq_zero_of_isNilpotent ha

/-- Over a commutative seminormed ring, the supremum over `Spectrum A` vanishes on nilpotent
elements. -/
theorem sSup_range_eval_eq_zero_of_isNilpotent {a : A} (ha : IsNilpotent a) :
    sSup (Set.range fun x : Spectrum A ↦ x a) = 0 := by
  rw [← smoothingFun_eq_sSup, smoothingFun_eq_zero_of_isNilpotent ha]

end SeminormedCommRing

section NormedCommRing

variable {A : Type*} [NormedCommRing A]

/-- **Nonemptiness of the Berkovich spectrum** (Berkovich Theorem 1.2.1(i); Kedlaya–Liu
Theorem 2.3.4): every nontrivial normed commutative ring has a nonempty Berkovich spectrum. -/
instance instNonempty [Nontrivial A] : Nonempty (Spectrum A) :=
  nonempty_iff_norm_one_ne_zero.2 (norm_ne_zero_iff.2 one_ne_zero)

/-- Over a normed commutative ring, `Spectrum A` is nonempty if and only if `A` is
nontrivial. -/
theorem nonempty_iff_nontrivial : Nonempty (Spectrum A) ↔ Nontrivial A :=
  ⟨fun ⟨x⟩ ↦ x.nontrivial, fun _ ↦ inferInstance⟩

end NormedCommRing

end TauCeti.Spectrum
