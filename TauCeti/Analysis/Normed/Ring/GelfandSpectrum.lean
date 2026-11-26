/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.BerkovichSpectrum
public import TauCeti.Analysis.Normed.Unbundled.MulRingSeminorm

/-!
# Berkovich's spectral formula and nonemptiness of the Berkovich spectrum

Over a commutative seminormed ring `A`, combining `RingSeminorm.smoothing` with
Bosch–Güntzer–Remmert Theorem 1.3.2/3 (`RingSeminorm.exists_mulRingSeminorm_le_and_apply_eq`) yields
**Berkovich's spectral formula** (`TauCeti.Spectrum.smoothingFun_eq_sSup`): for every `a : A`,
`smoothingFun (normRingSeminorm A) a` is the supremum of `x a` over `x : Spectrum A`, and when
`normRingSeminorm A ≠ 0` (in particular on every nontrivial normed commutative ring) the spectrum
`TauCeti.Spectrum A` is nonempty (`TauCeti.Spectrum.instNonempty`) and the maximum is attained at a
point of `Spectrum A` (`TauCeti.Spectrum.exists_apply_eq_smoothingFun`).

This file also equips `TauCeti.Spectrum A` with the pointwise domination partial order
(`TauCeti.Spectrum.instPartialOrder`, with `TauCeti.Spectrum.normPoint` as top element under
`[NormOneClass A] [NormMulClass A]`), nilpotent-vanishing lemmas, and nilpotent-kernel retraction
homeomorphisms (`TauCeti.Spectrum.retractHomeomorph`).

## Main results

* `TauCeti.Spectrum.eq_zero_of_isNilpotent`, `TauCeti.Spectrum.map_add_eq_left_of_isNilpotent`:
  spectrum points vanish on nilpotents and are invariant under nilpotent perturbations.
* `TauCeti.Spectrum.retractHomeomorph`: homeomorphism `Spectrum B ≃ₜ Spectrum A` for a bounded
  retraction modulo nilpotents.
* `TauCeti.Spectrum.instOrderTop`: `normPoint` is the top element when `[NormOneClass A]` and
  `[NormMulClass A]`.
* `TauCeti.Spectrum.apply_le_smoothingFun`, `TauCeti.Spectrum.smoothingFun_eq_sSup`,
  `TauCeti.Spectrum.exists_apply_eq_smoothingFun`, `TauCeti.Spectrum.isGreatest_range_eval`:
  Berkovich's spectral formula for `TauCeti.Spectrum A`.
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

section SeminormedRing

variable {A B : Type*} [SeminormedRing A] [SeminormedRing B]

/-- If `‖(1 : A)‖ = 0`, then `Spectrum A` is empty. -/
theorem isEmpty_of_norm_one_eq_zero (h : ‖(1 : A)‖ = 0) : IsEmpty (Spectrum A) :=
  ⟨fun x ↦ by linarith [x.one_le_norm_one]⟩

/-- Every point of `Spectrum A` vanishes on nilpotent elements. -/
theorem eq_zero_of_isNilpotent (x : Spectrum A) {a : A} (ha : IsNilpotent a) : x a = 0 :=
  x.toMulRingSeminorm.eq_zero_of_isNilpotent ha

/-- Adding a nilpotent element leaves every point of `Spectrum A` unchanged. -/
theorem map_add_eq_left_of_isNilpotent (x : Spectrum A) (a : A) {b : A} (hb : IsNilpotent b) :
    x (a + b) = x a :=
  x.toMulRingSeminorm.map_add_eq_left_of_map_eq_zero a (x.eq_zero_of_isNilpotent hb)

/-- The pointwise domination order on `Spectrum A`, given by `x ≤ y ↔ ∀ a, x a ≤ y a`
(distinct from the trivial topological specialization order of the Hausdorff topology on
`Spectrum A`). -/
instance instPartialOrder : PartialOrder (Spectrum A) :=
  PartialOrder.lift (⇑·) DFunLike.coe_injective

/-- Pointwise characterization of the order on `Spectrum A`. -/
@[simp]
theorem le_def {x y : Spectrum A} : x ≤ y ↔ ∀ a, x a ≤ y a :=
  Iff.rfl

/-- If `φ : A →+* B` and `ψ : B →+* A` are bounded ring homomorphisms with `ψ ∘ φ = id` such that
`b - φ (ψ b)` is nilpotent for every `b : B`, then `comap φ` and `comap ψ` form a homeomorphism
`Spectrum B ≃ₜ Spectrum A`. -/
noncomputable def retractHomeomorph (φ : A →+* B) (hφ : φ.IsBounded) (ψ : B →+* A)
    (hψ : ψ.IsBounded) (hψφ : ∀ a : A, ψ (φ a) = a)
    (hnil : ∀ b : B, IsNilpotent (b - φ (ψ b))) :
    Spectrum B ≃ₜ Spectrum A where
  toFun := comap φ hφ
  invFun := comap ψ hψ
  left_inv y := ext fun b ↦ by
    simp only [comap_apply]
    conv_rhs => rw [(add_sub_cancel (φ (ψ b)) b).symm]
    exact (y.map_add_eq_left_of_isNilpotent (φ (ψ b)) (hnil b)).symm
  right_inv x := ext fun a ↦ by simp [hψφ a]
  continuous_toFun := (comap φ hφ).continuous
  continuous_invFun := (comap ψ hψ).continuous

/-- Applying `retractHomeomorph` pulls back along `φ`. -/
@[simp]
theorem retractHomeomorph_apply (φ : A →+* B) (hφ : φ.IsBounded) (ψ : B →+* A)
    (hψ : ψ.IsBounded) (hψφ : ∀ a : A, ψ (φ a) = a)
    (hnil : ∀ b : B, IsNilpotent (b - φ (ψ b))) (y : Spectrum B) (a : A) :
    retractHomeomorph φ hφ ψ hψ hψφ hnil y a = y (φ a) :=
  comap_apply φ hφ y a

/-- Applying `(retractHomeomorph ...).symm` pulls back along `ψ`. -/
@[simp]
theorem retractHomeomorph_symm_apply (φ : A →+* B) (hφ : φ.IsBounded) (ψ : B →+* A)
    (hψ : ψ.IsBounded) (hψφ : ∀ a : A, ψ (φ a) = a)
    (hnil : ∀ b : B, IsNilpotent (b - φ (ψ b))) (x : Spectrum A) (b : B) :
    (retractHomeomorph φ hφ ψ hψ hψφ hnil).symm x b = x (ψ b) :=
  comap_apply ψ hψ x b

section NormMulClass

variable [NormOneClass A] [NormMulClass A]

/-- When the ambient norm is multiplicative and normalized, `normPoint` is the greatest element
of `Spectrum A`. -/
noncomputable instance instOrderTop : OrderTop (Spectrum A) where
  top := normPoint
  le_top x := le_def.2 fun a ↦ by
    rw [normPoint_apply]
    exact x.apply_le_norm a

/-- The top element of `Spectrum A` is `normPoint`. -/
@[simp]
theorem top_eq_normPoint : (⊤ : Spectrum A) = normPoint :=
  (rfl)

/-- Every point of `Spectrum A` is bounded above by `normPoint`. -/
theorem le_normPoint (x : Spectrum A) : x ≤ normPoint :=
  top_eq_normPoint (A := A) ▸ le_top

/-- When the ambient norm is multiplicative and normalized, `normPoint` attains the maximum of
`x a` over `Spectrum A` for every `a : A` simultaneously. -/
theorem isGreatest_range_eval_of_normMulClass (a : A) :
    IsGreatest (Set.range fun x : Spectrum A ↦ x a) ‖a‖ :=
  ⟨⟨normPoint, normPoint_apply a⟩, by rintro _ ⟨x, rfl⟩; exact x.apply_le_norm a⟩

/-- When the ambient norm is multiplicative and normalized, the supremum over `Spectrum A` at `a`
equals `‖a‖`. -/
theorem sSup_range_eval_of_normMulClass (a : A) :
    sSup (Set.range fun x : Spectrum A ↦ x a) = ‖a‖ :=
  (isGreatest_range_eval_of_normMulClass a).csSup_eq

end NormMulClass

end SeminormedRing

/-! ### Berkovich's spectral formula and nonemptiness -/

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
theorem exists_apply_eq_smoothingFun_of_norm_ne_zero (h : normRingSeminorm A ≠ 0) (a : A) :
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
  obtain ⟨x, -⟩ := exists_apply_eq_smoothingFun_of_norm_ne_zero
    (normRingSeminorm_ne_zero_of_norm_one_ne_zero h1) 1
  exact ⟨x⟩

/-- On a commutative seminormed ring with nonempty Berkovich spectrum (in particular on every
nontrivial normed commutative ring), every `a : A` attains its spectral seminorm at some point of
`Spectrum A` (Berkovich Theorem 1.3.1; Kedlaya–Liu Theorem 2.3.10). -/
theorem exists_apply_eq_smoothingFun [Nonempty (Spectrum A)] (a : A) :
    ∃ x : Spectrum A, x a = smoothingFun (normRingSeminorm A) a :=
  exists_apply_eq_smoothingFun_of_norm_ne_zero
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
