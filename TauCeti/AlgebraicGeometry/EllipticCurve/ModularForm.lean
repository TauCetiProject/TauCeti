/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# Integral modular forms of the Weierstrass coordinate-change action

A polynomial `f ∈ ℤ[a₁, a₂, a₃, a₄, a₆]` in the coefficients of the universal Weierstrass curve
is an *integral modular form of weight `k`* (`WeierstrassCurve.IsIntegralModularForm`) when
`f(C • W) = u⁻ᵏ f(W)` for every Weierstrass curve `W` and every admissible change of variables
`C = (u, r, s, t)` over every commutative ring. These are the weight-`k` invariants of the
Weierstrass Hopf algebroid, the integral modular forms of level one of Deligne's formulaire. The
invariants `c₄`, `c₆` and `Δ` of the universal curve are such forms, of weights `4`, `6` and `12`.

The weight of a coefficient `aᵢ` is `i` (`WeierstrassCurve.coefficientWeight`): the scaling
`C = (u, 0, 0, 0)` sends `aᵢ` to `u⁻ⁱ aᵢ`. Since the definition quantifies over all coefficient
rings, it can be tested on the scaling by a unit `u` with `u⁻¹ = 2` over `ℚ[a₁, ⋯, a₆]`, which
multiplies every monomial of weight `n` by `2ⁿ`: an integral modular form of weight `k` is
weighted homogeneous of weight `k`. Over `ℤ` alone the only units are `±1`, which separate
weights only modulo `2`, so this quantification is essential.

On the subring `ℤ[c₄, c₆, Δ]` every change of variables acts through its `u` alone, so there the
weight-`k` modular forms are exactly the weighted homogeneous elements of weight `k`
(`WeierstrassCurve.isIntegralModularForm_iff_of_mem_adjoin`). Deligne's theorem, that every
integral modular form lies in `ℤ[c₄, c₆, Δ]`, is the remaining inclusion of the invariant ring.

## Main definitions

* `WeierstrassCurve.IsIntegralModularForm`: the predicate of being an integral modular form of
  weight `k`.

## Main results

* `WeierstrassCurve.IsIntegralModularForm.add`, `.smul`, `.mul`, `.pow`: integral modular forms
  of a fixed weight form a `ℤ`-module, and weights add under multiplication.
* `WeierstrassCurve.isIntegralModularForm_c₄`, `isIntegralModularForm_c₆`,
  `isIntegralModularForm_Δ`: the invariants `c₄`, `c₆` and `Δ` of the universal curve are
  integral modular forms of weights `4`, `6` and `12`.
* `WeierstrassCurve.IsIntegralModularForm.isWeightedHomogeneous`: an integral modular form of
  weight `k` is weighted homogeneous of weight `k`; in particular a nonzero integral modular form
  has a unique weight (`WeierstrassCurve.IsIntegralModularForm.inj_right`).
* `WeierstrassCurve.isIntegralModularForm_iff_of_mem_adjoin`: an element of `ℤ[c₄, c₆, Δ]` is an
  integral modular form of weight `k` exactly when it is weighted homogeneous of weight `k`.

## References

* P. Deligne, *Courbes elliptiques : formulaire d'après J. Tate*, in *Modular functions of one
  variable IV*, Lecture Notes in Math. 476, Springer, 1975.
* T. Bauer, *Computation of the homotopy of the spectrum tmf*, in *Groups, homotopy and
  configuration spaces*, Geom. Topol. Monogr. 13 (2008), §3.
-/

public section

namespace WeierstrassCurve

open MvPolynomial Universal

/-- A polynomial `f` in the coefficients of the universal Weierstrass curve is an *integral
modular form of weight `k`* if `f(C • W) = u⁻ᵏ f(W)` for every Weierstrass curve `W` and every
change of variables `C = (u, r, s, t)` over every commutative ring `R` (in `Type`). Here `f(W)`
is the specialization `W.specialize f`. -/
def IsIntegralModularForm (k : ℕ) (f : MvPolynomial Coeff ℤ) : Prop :=
  ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R),
    (C • W).specialize f = ↑C.u⁻¹ ^ k * W.specialize f

variable {k l : ℕ} {f g : MvPolynomial Coeff ℤ}

lemma isIntegralModularForm_def : IsIntegralModularForm k f ↔
    ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (C : VariableChange R),
      (C • W).specialize f = ↑C.u⁻¹ ^ k * W.specialize f :=
  Iff.rfl

namespace IsIntegralModularForm

/-- The transformation law of an integral modular form of weight `k` under a change of
variables. -/
lemma specialize_smul (hf : IsIntegralModularForm k f) {R : Type} [CommRing R]
    (W : WeierstrassCurve R) (C : VariableChange R) :
    (C • W).specialize f = ↑C.u⁻¹ ^ k * W.specialize f :=
  hf R W C

lemma add (hf : IsIntegralModularForm k f) (hg : IsIntegralModularForm k g) :
    IsIntegralModularForm k (f + g) := fun R _ W C ↦ by
  rw [map_add, map_add, hf.specialize_smul, hg.specialize_smul, mul_add]

lemma neg (hf : IsIntegralModularForm k f) : IsIntegralModularForm k (-f) := fun R _ W C ↦ by
  rw [map_neg, map_neg, hf.specialize_smul, mul_neg]

lemma sub (hf : IsIntegralModularForm k f) (hg : IsIntegralModularForm k g) :
    IsIntegralModularForm k (f - g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma smul (hf : IsIntegralModularForm k f) (n : ℤ) : IsIntegralModularForm k (n • f) :=
  fun R _ W C ↦ by
    rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, hf.specialize_smul]
    ring

/-- The product of integral modular forms of weights `k` and `l` has weight `k + l`. -/
lemma mul (hf : IsIntegralModularForm k f) (hg : IsIntegralModularForm l g) :
    IsIntegralModularForm (k + l) (f * g) := fun R _ W C ↦ by
  rw [map_mul, map_mul, hf.specialize_smul, hg.specialize_smul]
  ring

/-- The `n`-th power of an integral modular form of weight `k` has weight `k * n`. -/
lemma pow (hf : IsIntegralModularForm k f) (n : ℕ) : IsIntegralModularForm (k * n) (f ^ n) :=
  fun R _ W C ↦ by
    rw [map_pow, map_pow, hf.specialize_smul]
    ring

end IsIntegralModularForm

variable (k) in
@[simp]
lemma isIntegralModularForm_zero : IsIntegralModularForm k 0 := fun R _ W C ↦ by
  rw [map_zero, map_zero, mul_zero]

/-- Every integer is an integral modular form of weight `0`. This is the simp normal form of
`isIntegralModularForm_C`. -/
@[simp]
lemma isIntegralModularForm_intCast (n : ℤ) :
    IsIntegralModularForm 0 (n : MvPolynomial Coeff ℤ) := fun R _ W _ ↦ by
  rw [map_intCast, map_intCast, pow_zero, one_mul]

/-- Every integer constant is an integral modular form of weight `0`. -/
lemma isIntegralModularForm_C (n : ℤ) : IsIntegralModularForm 0 (C n) := by
  simp

@[simp]
lemma isIntegralModularForm_one : IsIntegralModularForm 0 1 := by
  simpa using isIntegralModularForm_intCast 1

/-- The invariant `c₄` of the universal curve is an integral modular form of weight `4`. -/
theorem isIntegralModularForm_c₄ : IsIntegralModularForm 4 Universal.curve.c₄ :=
  fun R _ W C ↦ by rw [specialize_c₄, specialize_c₄, variableChange_c₄]

/-- The invariant `c₆` of the universal curve is an integral modular form of weight `6`. -/
theorem isIntegralModularForm_c₆ : IsIntegralModularForm 6 Universal.curve.c₆ :=
  fun R _ W C ↦ by rw [specialize_c₆, specialize_c₆, variableChange_c₆]

/-- The discriminant `Δ` of the universal curve is an integral modular form of weight `12`. -/
theorem isIntegralModularForm_Δ : IsIntegralModularForm 12 Universal.curve.Δ :=
  fun R _ W C ↦ by rw [specialize_Δ, specialize_Δ, variableChange_Δ]

/-- **The weight of an integral modular form.** An integral modular form of weight `k` is
weighted homogeneous of weight `k` for the weights `coefficientWeight`. -/
theorem IsIntegralModularForm.isWeightedHomogeneous (hf : IsIntegralModularForm k f) :
    f.IsWeightedHomogeneous coefficientWeight k := by
  -- Test `hf` on the universal curve over `ℚ[a₁, ⋯, a₆]` and the scaling with `u⁻¹ = 2`, which
  -- multiplies each monomial of weight `n` by `2 ^ n`; these powers are pairwise distinct.
  set φ := MvPolynomial.map (Int.castRingHom ℚ) f
  set W := Universal.curve.map (MvPolynomial.map (Int.castRingHom ℚ))
  set v : (MvPolynomial Coeff ℚ)ˣ :=
    Units.map (algebraMap ℚ _).toMonoidHom (Units.mk0 2 two_ne_zero)
  have hv : (v : MvPolynomial Coeff ℚ) = C 2 := (rfl)
  have hW (g : MvPolynomial Coeff ℤ) : W.specialize g = MvPolynomial.map (Int.castRingHom ℚ) g := by
    refine congrFun (congrArg DFunLike.coe (ringHom_ext (fun n ↦ ?_) fun i ↦ ?_)) g
    · rw [eq_intCast C, map_intCast, map_intCast]
    · cases i <;> simp [W]
  have hvW (g : MvPolynomial Coeff ℤ) :
      ((⟨v⁻¹, 0, 0, 0⟩ : VariableChange _) • W).specialize g =
        (aeval fun i ↦ C (2 ^ coefficientWeight i) * X i).toRingHom
          (MvPolynomial.map (Int.castRingHom ℚ) g) := by
    rw [specialize_mk_smul, inv_inv, hv, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def,
      aeval_def, eval₂_map,
      RingHom.ext_int (algebraMap ℤ _) ((algebraMap ℚ _).comp (Int.castRingHom ℚ))]
    simp only [hW, map_X, map_pow]
  have h := hf.specialize_smul W ⟨v⁻¹, 0, 0, 0⟩
  rw [hvW, hW, inv_inv, hv, ← map_pow] at h
  have hφ : φ.IsWeightedHomogeneous coefficientWeight k :=
    isWeightedHomogeneous_of_aeval_C_pow_mul_X_eq (t := (2 : ℚ))
      (pow_right_injective₀ two_pos (by norm_num)) h
  intro d hd
  refine hφ ?_
  rwa [coeff_map, eq_intCast, Int.cast_ne_zero]

/-- A nonzero integral modular form has a unique weight. -/
theorem IsIntegralModularForm.inj_right (hf : f ≠ 0) (hk : IsIntegralModularForm k f)
    (hl : IsIntegralModularForm l f) : k = l :=
  hk.isWeightedHomogeneous.inj_right hf hl.isWeightedHomogeneous

/-- On the subring `ℤ[c₄, c₆, Δ]`, being an integral modular form of weight `k` is weighted
homogeneity of weight `k`: there a change of variables `(u, r, s, t)` acts as the scaling
`(u, 0, 0, 0)`. -/
theorem isIntegralModularForm_iff_of_mem_adjoin
    (hf : f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    IsIntegralModularForm k f ↔ f.IsWeightedHomogeneous coefficientWeight k := by
  refine ⟨IsIntegralModularForm.isWeightedHomogeneous, fun hk R _ W C ↦ ?_⟩
  -- `C` and the scaling `(C.u, 0, 0, 0)` agree on `c₄`, `c₆` and `Δ`, hence on `f`.
  have h : (C • W).specialize f = ((⟨C.u, 0, 0, 0⟩ : VariableChange R) • W).specialize f := by
    refine AlgHom.adjoin_le_equalizer (C • W).specialize.toIntAlgHom
      ((⟨C.u, 0, 0, 0⟩ : VariableChange R) • W).specialize.toIntAlgHom ?_ hf
    rintro _ (rfl | rfl | rfl) <;>
      simp [variableChange_c₄, variableChange_c₆, variableChange_Δ]
  rw [h, specialize_mk_smul, hk.aeval_pow_mul]
  exact congrArg _ (DFunLike.congr_fun (aeval_unique W.specialize.toIntAlgHom) f).symm

end WeierstrassCurve
