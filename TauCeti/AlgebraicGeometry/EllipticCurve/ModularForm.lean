/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.ShortWeierstrass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.Basic
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
(`WeierstrassCurve.isIntegralModularForm_iff_of_mem_adjoin`).

After inverting `6`, every Weierstrass equation is carried by a change of variables
`(1/6, r, s, t)` to the short equation `y² = x³ - 27c₄x - 54c₆`. Hence an integral modular form
`f` of weight `k` satisfies `6ᵏ f = f(0, 0, 0, -27c₄, -54c₆)`, a polynomial in `c₄` and `c₆`.
Conversely, since the universal curve and change of variables are defined together over the
torsion-free ring `ℤ[u, u⁻¹, r, s, t][a₁, ⋯, a₆]`, the transformation law of `n • f` for a
nonzero integer `n` implies that of `f`. Together these describe the integral modular forms of
weight `k` as the weighted homogeneous `f` of weight `k` with `6ⁿ f ∈ ℤ[c₄, c₆]` for some `n`
(`WeierstrassCurve.isIntegralModularForm_iff_exists_six_pow_mul_mem_adjoin`).

By Deligne's theorem every integral modular form lies in `ℤ[c₄, c₆, Δ]`
(`WeierstrassCurve.IsIntegralModularForm.mem_adjoin`). Together with the description of the
modular forms in `ℤ[c₄, c₆, Δ]` above, this determines the ring of
integral modular forms of level one: an integral modular form of weight `k` is exactly a weighted
homogeneous element of weight `k` of `ℤ[c₄, c₆, Δ]` (`WeierstrassCurve.isIntegralModularForm_iff`),
and this subring is presented by the single relation `c₄³ - c₆² = 1728Δ`
(`WeierstrassCurve.Universal.adjoinC₄C₆ΔEquiv`).

Deligne's theorem follows from the description after inverting `6`, because `ℤ[c₄, c₆, Δ]` is
saturated with respect to `6`: every element of it is `α(c₄, Δ) + c₆ β(c₄, Δ)`, and reducing
modulo `6` on the curve with `a₁ = x` and `a₆ = -y` over `(ℤ/6)[x, y]`, whose invariants are the
monomials `x⁴`, `-x⁶` and `x⁶y`, shows that if this element is divisible by `6` then so are `α`
and `β`.

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
* `WeierstrassCurve.isIntegralModularForm_iff_universal`: the transformation law need only be
  checked for the universal curve and change of variables over `ℤ[u, u⁻¹, r, s, t][a₁, ⋯, a₆]`.
* `WeierstrassCurve.isIntegralModularForm_smul_iff`: for a nonzero integer `n`, `n • f` is an
  integral modular form of weight `k` exactly when `f` is.
* `WeierstrassCurve.IsIntegralModularForm.six_pow_mul_eq_specialize_shortCurve`: an integral
  modular form `f` of weight `k` satisfies `6ᵏ f = f(0, 0, 0, -27c₄, -54c₆)`.
* `WeierstrassCurve.isIntegralModularForm_iff_exists_six_pow_mul_mem_adjoin`: the integral
  modular forms of weight `k` are the weighted homogeneous `f` of weight `k` with
  `6ⁿ f ∈ ℤ[c₄, c₆]` for some `n`.
* `WeierstrassCurve.IsIntegralModularForm.mem_adjoin`: **Deligne's theorem**, every integral
  modular form lies in `ℤ[c₄, c₆, Δ]`.
* `WeierstrassCurve.isIntegralModularForm_iff`: the integral modular forms of weight `k` are the
  weighted homogeneous elements of weight `k` of `ℤ[c₄, c₆, Δ]`.

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

open TauCeti.WeierstrassChange.Universal (CoordinateRing change) in
/-- **The universal transformation law.** It suffices to check the transformation law of an
integral modular form once, for the universal Weierstrass curve and the universal change of
variables over `Γ = ℤ[u, u⁻¹, r, s, t][a₁, ⋯, a₆]`, the polynomial ring in the Weierstrass
coefficients over the coordinate ring `TauCeti.WeierstrassChange.Universal.CoordinateRing` of
the changes of variables: every pair `(W, C)` is a specialization of that one. -/
theorem isIntegralModularForm_iff_universal : IsIntegralModularForm k f ↔
    (change.map (algebraMap CoordinateRing (MvPolynomial Coeff CoordinateRing)) •
        Universal.curve.map (MvPolynomial.map (Int.castRingHom CoordinateRing))).specialize f =
      ↑(change.map (algebraMap CoordinateRing (MvPolynomial Coeff CoordinateRing))).u⁻¹ ^ k *
        (Universal.curve.map (MvPolynomial.map (Int.castRingHom CoordinateRing))).specialize f := by
  refine ⟨fun hf ↦ hf.specialize_smul _ _, fun h R _ W C ↦ ?_⟩
  -- Specialize `h` along the classifying homomorphism `ψ` of `(W, C)`.
  set ψ := eval₂Hom C.specialize (Coeff.rec W.a₁ W.a₂ W.a₃ W.a₄ W.a₆) with hψ
  have hW : (Universal.curve.map (MvPolynomial.map (Int.castRingHom _))).map ψ = W := by
    ext <;> simp [hψ]
  have hC : (change.map (algebraMap _ _)).map ψ = C := by
    ext <;> simp [hψ]
  clear_value ψ
  rw [← hW, ← hC, map_variableChange, specialize_map, specialize_map, RingHom.comp_apply, h,
    map_mul, map_pow]
  simp

/-- Multiplying by a nonzero integer neither creates nor destroys integral modular forms. -/
theorem isIntegralModularForm_smul_iff {n : ℤ} (hn : n ≠ 0) :
    IsIntegralModularForm k (n • f) ↔ IsIntegralModularForm k f := by
  refine ⟨fun h ↦ isIntegralModularForm_iff_universal.2 ?_, fun hf ↦ hf.smul n⟩
  -- The ring `Γ = ℤ[u, u⁻¹, r, s, t][a₁, ⋯, a₆]` has no additive torsion, so the universal
  -- transformation law of `n • f` can be divided by `n`.
  have : CharZero TauCeti.WeierstrassChange.Universal.CoordinateRing :=
    charZero_of_injective_algebraMap (IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero (R := ℤ) (σ := Fin 4) 0)))
  have := isIntegralModularForm_iff_universal.1 h
  rw [zsmul_eq_mul, map_mul, map_mul, map_intCast, map_intCast, mul_left_comm] at this
  exact mul_left_cancel₀ (Int.cast_ne_zero.mpr hn) this

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
    rw [specialize_map, Universal.specialize_curve, RingHom.comp_id]
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

/-- **Integral modular forms after inverting `6`.** If `f` is an integral modular form of weight
`k`, then `6ᵏ f` is the value of `f` at the short Weierstrass equation
`y² = x³ - 27c₄x - 54c₆` of the universal curve. Over `ℤ[1/6]` every Weierstrass equation is
carried to this one by the change of variables `(1/6, r, s, t)` for suitable `r`, `s`, `t`. -/
theorem IsIntegralModularForm.six_pow_mul_eq_specialize_shortCurve
    (hf : IsIntegralModularForm k f) :
    6 ^ k * f =
      (shortCurve (-27 * Universal.curve.c₄) (-54 * Universal.curve.c₆)).specialize f := by
  -- Compare both sides in the fraction field `K` of `ℤ[a₁, ⋯, a₆]`, where `2` and `3` are units.
  let K := FractionRing (MvPolynomial Coeff ℤ)
  let φ := algebraMap (MvPolynomial Coeff ℤ) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ K
  have : CharZero K := charZero_of_injective_algebraMap hφ
  let : Invertible (2 : K) := invertibleOfNonzero (by norm_num)
  let : Invertible (3 : K) := invertibleOfNonzero (by norm_num)
  have h6 : (6 : K) ≠ 0 := by norm_num
  set W : WeierstrassCurve K := Universal.curve.map φ
  -- `W` is a translate of `ofCInvariants W.c₄ W.c₆` with `u = 1`, so `f` takes the same value at
  -- both.
  have hW₀ : W.specialize f = (ofCInvariants W.c₄ W.c₆).specialize f := by
    conv_lhs => rw [← smul_ofCInvariants W]
    rw [hf.specialize_smul, inv_one, Units.val_one, one_pow, one_mul]
  -- The scaling by `u = 1/6` carries `ofCInvariants W.c₄ W.c₆` to `y² = x³ - 27c₄x - 54c₆`.
  have hS : (⟨(Units.mk0 6 h6)⁻¹, 0, 0, 0⟩ : VariableChange K) • ofCInvariants W.c₄ W.c₆ =
      (shortCurve (-27 * Universal.curve.c₄) (-54 * Universal.curve.c₆)).map φ := by
    rw [ofCInvariants_eq_shortCurve, smul_shortCurve, map_shortCurve, inv_inv, Units.val_mk0]
    simp only [W, map_c₄, map_c₆, map_mul, map_neg, map_ofNat]
    congr 1 <;> field_simp <;> ring
  have h := hf.specialize_smul (ofCInvariants W.c₄ W.c₆) ⟨(Units.mk0 6 h6)⁻¹, 0, 0, 0⟩
  rw [hS, specialize_map, inv_inv, Units.val_mk0, ← hW₀, specialize_map,
    Universal.specialize_curve] at h
  apply hφ
  rw [map_mul, map_pow, map_ofNat]
  exact h.symm

/-- After inverting `6`, an integral modular form is a polynomial in `c₄` and `c₆`: if `f` has
weight `k` then `6ᵏ f` lies in the subring `ℤ[c₄, c₆]`. -/
theorem IsIntegralModularForm.six_pow_mul_mem_adjoin (hf : IsIntegralModularForm k f) :
    6 ^ k * f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆} := by
  rw [hf.six_pow_mul_eq_specialize_shortCurve]
  -- The specialization is an `aeval`, with values `0`, `-27c₄` and `-54c₆` in `ℤ[c₄, c₆]`.
  set S := shortCurve (-27 * Universal.curve.c₄) (-54 * Universal.curve.c₆)
  have h : S.specialize f ∈ (aeval fun i ↦ S.specialize.toIntAlgHom (X i)).range :=
    ⟨f, (DFunLike.congr_fun (aeval_unique S.specialize.toIntAlgHom) f).symm⟩
  rw [aeval_range] at h
  refine Algebra.adjoin_le (Set.range_subset_iff.2 fun i ↦ ?_) h
  have h₄ : Universal.curve.c₄ ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆} :=
    Algebra.subset_adjoin (by simp)
  have h₆ : Universal.curve.c₆ ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆} :=
    Algebra.subset_adjoin (by simp)
  cases i <;> simp [S, mul_mem, h₄, h₆]

/-- **Integral modular forms after inverting `6`.** A polynomial in the Weierstrass coefficients is
an integral modular form of weight `k` exactly when it is weighted homogeneous of weight `k` and
becomes a polynomial in `c₄` and `c₆` after multiplication by a power of `6`. This describes the
modular forms without reference to changes of variables; Deligne's theorem refines the second
condition to membership in `ℤ[c₄, c₆, Δ]`. -/
theorem isIntegralModularForm_iff_exists_six_pow_mul_mem_adjoin :
    IsIntegralModularForm k f ↔ f.IsWeightedHomogeneous coefficientWeight k ∧
      ∃ n : ℕ, 6 ^ n * f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆} := by
  refine ⟨fun hf ↦ ⟨hf.isWeightedHomogeneous, k, hf.six_pow_mul_mem_adjoin⟩, ?_⟩
  rintro ⟨hk, n, hn⟩
  have h6 : (6 ^ n : ℤ) • f = C (6 ^ n) * f := by rw [zsmul_eq_mul, ← eq_intCast C]
  rw [← isIntegralModularForm_smul_iff (pow_ne_zero n (by norm_num : (6 : ℤ) ≠ 0)), h6,
    isIntegralModularForm_iff_of_mem_adjoin, ← zero_add k]
  · exact (isWeightedHomogeneous_C _ _).mul hk
  · rw [map_pow, map_ofNat]
    exact Algebra.adjoin_mono (Set.insert_subset_insert (by simp)) hn

/-! ### Deligne's theorem -/

/-- Every element of `ℤ[c₄, c₆, Δ]` has the form `α(c₄, Δ) + c₆ β(c₄, Δ)`, because
`c₆² = c₄³ - 1728Δ`. -/
private lemma exists_eq_aeval_add_c₆_mul_aeval
    (hf : f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    ∃ α β : MvPolynomial (Fin 2) ℤ, f = aeval ![curve.c₄, curve.Δ] α +
      curve.c₆ * aeval ![curve.c₄, curve.Δ] β := by
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨X 0, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨X 1, 0, by simp⟩
  | algebraMap n => exact ⟨C n, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨α, β, rfl⟩ := hx
    obtain ⟨α', β', rfl⟩ := hy
    exact ⟨α + α', β + β', by simp only [map_add]; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨α, β, rfl⟩ := hx
    obtain ⟨α', β', rfl⟩ := hy
    refine ⟨α * α' + (X 0 ^ 3 - 1728 * X 1) * β * β', α * β' + α' * β, ?_⟩
    simp only [map_add, map_mul, map_sub, map_pow, map_ofNat, aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination (aeval ![curve.c₄, curve.Δ] β * aeval ![curve.c₄, curve.Δ] β') *
      curve.c_relation

/-- A polynomial in `c₄` and `Δ` lies in `ℤ[c₄, c₆, Δ]`. -/
private lemma aeval_mem_adjoin (γ : MvPolynomial (Fin 2) ℤ) :
    aeval ![curve.c₄, curve.Δ] γ ∈
      Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} := by
  refine Algebra.adjoin_mono ?_ ((Algebra.adjoin_range_eq_range_aeval ℤ _).ge ⟨γ, rfl⟩)
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp

/-- The exponents of the monomials `x⁴` and `x⁶y` in the variables `x = X 0` and `y = X 1`. -/
private noncomputable abbrev expo : Fin 2 → Fin 2 →₀ ℕ := ![.single 0 4, .single 0 6 + .single 1 1]

private lemma linearCombination_expo_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.linearCombination ℕ expo d = .single 0 (4 * d 0 + 6 * d 1) + .single 1 (d 1) := by
  ext i
  fin_cases i <;> simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, mul_comm]

/-- Substitute `x⁴` and `x⁶y` for the two variables. The polynomials `α(x⁴, x⁶y)` and
`x⁶ β(x⁴, x⁶y)` agree only if `α = β = 0`: the substitution is injective on monomials, and in a
monomial `xᵃyᵇ` of the first `a ≡ 2b` modulo `4`, while in one of the second `a ≡ 2b + 2`. -/
private lemma eq_zero_of_aeval_eq_X_pow_mul_aeval {R : Type*} [CommSemiring R]
    {α β : MvPolynomial (Fin 2) R}
    (h : aeval (![X 0 ^ 4, X 0 ^ 6 * X 1] : Fin 2 → MvPolynomial (Fin 2) R) α =
      X 0 ^ 6 * aeval ![X 0 ^ 4, X 0 ^ 6 * X 1] β) :
    α = 0 ∧ β = 0 := by
  -- The substitution sends the monomial with exponent `d` to the one with exponent `A d`, and
  -- `A d + (6, 0)` is never of the form `A d'`. Comparing coefficients at `A d` gives `α = 0`,
  -- and then comparing them at `A d + (6, 0)` gives `β = 0`.
  set A := Finsupp.linearCombination ℕ expo
  have hA (d : Fin 2 →₀ ℕ) : A d 0 = 4 * d 0 + 6 * d 1 ∧ A d 1 = d 1 := by
    simp [A, linearCombination_expo_apply]
  have hAinj : Function.Injective A := fun d d' hd ↦ by
    have h0 := DFunLike.congr_fun hd 0
    have h1 := DFunLike.congr_fun hd 1
    rw [(hA d).1, (hA d').1] at h0
    rw [(hA d).2, (hA d').2] at h1
    ext i
    fin_cases i <;> simp <;> omega
  have hshift (d d' : Fin 2 →₀ ℕ) : A d + .single 0 6 ≠ A d' := fun hd ↦ by
    have h0 := DFunLike.congr_fun hd 0
    have h1 := DFunLike.congr_fun hd 1
    simp only [Finsupp.add_apply, (hA d).1, (hA d).2, (hA d').1, (hA d').2] at h0 h1
    simp at h0 h1
    omega
  have hg : (![X 0 ^ 4, X 0 ^ 6 * X 1] : Fin 2 → MvPolynomial (Fin 2) R) =
      fun i ↦ AddMonoidAlgebra.single (expo i) 1 := by
    funext i
    fin_cases i <;> simp [single_eq_monomial, monomial_single_add, ← X_pow_eq_monomial]
  have hX : (X 0 ^ 6 : MvPolynomial (Fin 2) R) = monomial (.single 0 6) 1 := X_pow_eq_monomial
  rw [hg, hX] at h
  constructor
  · ext d
    rw [← TauCeti.coeff_aeval_single_linearCombination hAinj, h, coeff_monomial_mul',
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    split_ifs with h6
    · rw [TauCeti.coeff_aeval_single_of_notMem_range, mul_zero]
      rintro ⟨d', hd'⟩
      exact hshift d' d (by rw [hd', tsub_add_cancel_of_le h6])
    · rfl
  · ext d
    have h' := congrArg (·.coeff (A d + .single 0 6)) h
    simp only [coeff_monomial_mul', le_add_self, ↓reduceIte, add_tsub_cancel_right, one_mul] at h'
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
      ← TauCeti.coeff_aeval_single_linearCombination hAinj, ← h',
      TauCeti.coeff_aeval_single_of_notMem_range _ fun ⟨d', hd'⟩ ↦ hshift d d' hd'.symm]

/-- The Weierstrass curve with `a₁ = x`, `a₆ = -y` and all other coefficients zero, over the
polynomial ring `(ℤ/6)[x, y]`. Its invariants are `c₄ = x⁴`, `c₆ = -x⁶` and `Δ = x⁶y`, since the
remaining terms have coefficients divisible by `6`. -/
private noncomputable abbrev mod6Curve : WeierstrassCurve (MvPolynomial (Fin 2) (ZMod 6)) :=
  ⟨X 0, 0, 0, 0, -X 1⟩

private lemma six_eq_zero : (6 : MvPolynomial (Fin 2) (ZMod 6)) = 0 := by
  rw [← map_ofNat C 6]
  exact C_eq_zero.mpr (by decide)

private lemma mod6Curve_c₄ : mod6Curve.c₄ = X 0 ^ 4 := by
  simp [c₄, b₂, b₄, ← pow_mul]

private lemma mod6Curve_c₆ : mod6Curve.c₆ = -X 0 ^ 6 := by
  simp only [c₆, b₂, b₄, b₆]
  linear_combination (144 * X 1) * six_eq_zero

private lemma mod6Curve_Δ : mod6Curve.Δ = X 0 ^ 6 * X 1 := by
  simp only [Δ, b₂, b₄, b₆, b₈]
  linear_combination (-72 * X 1 ^ 2) * six_eq_zero

/-- The subring `ℤ[c₄, c₆, Δ]` is saturated with respect to `6`: if `6 f` lies in it, so does
`f`. -/
private lemma mem_adjoin_of_six_mul_mem
    (hf : 6 * f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ}) :
    f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} := by
  obtain ⟨α, β, hαβ⟩ := exists_eq_aeval_add_c₆_mul_aeval hf
  -- Reduce modulo `6` and specialize to `mod6Curve`, where `c₄, c₆, Δ ↦ x⁴, -x⁶, x⁶y`.
  set ψ := Int.castRingHom (ZMod 6)
  have hspec : mod6Curve.specialize.comp (aeval ![curve.c₄, curve.Δ]).toRingHom =
      (aeval ![X 0 ^ 4, X 0 ^ 6 * X 1]).toRingHom.comp (MvPolynomial.map ψ) := by
    refine ringHom_ext (fun n ↦ ?_) (fun i ↦ ?_)
    · simp
    · fin_cases i <;> simp [mod6Curve_c₄, mod6Curve_Δ]
  have hs (γ : MvPolynomial (Fin 2) ℤ) : mod6Curve.specialize (aeval ![curve.c₄, curve.Δ] γ) =
      aeval ![X 0 ^ 4, X 0 ^ 6 * X 1] (MvPolynomial.map ψ γ) :=
    DFunLike.congr_fun hspec γ
  have h : aeval (![X 0 ^ 4, X 0 ^ 6 * X 1] : Fin 2 → MvPolynomial (Fin 2) (ZMod 6))
      (MvPolynomial.map ψ α) =
      X 0 ^ 6 * aeval ![X 0 ^ 4, X 0 ^ 6 * X 1] (MvPolynomial.map ψ β) := by
    have h := congrArg mod6Curve.specialize hαβ
    simp only [map_mul, map_add, map_ofNat, hs, specialize_c₆, mod6Curve_c₆] at h
    linear_combination -h + mod6Curve.specialize f * six_eq_zero
  obtain ⟨hα, hβ⟩ := eq_zero_of_aeval_eq_X_pow_mul_aeval h
  have hψ (n : ℤ) : ψ n = 0 ↔ 6 ∣ n := by
    simpa using ZMod.intCast_zmod_eq_zero_iff_dvd n 6
  obtain ⟨α', rfl⟩ := (C_dvd_iff_map_hom_eq_zero ψ 6 hψ α).mpr hα
  obtain ⟨β', rfl⟩ := (C_dvd_iff_map_hom_eq_zero ψ 6 hψ β).mpr hβ
  have hf' : f = aeval ![curve.c₄, curve.Δ] α' + curve.c₆ * aeval ![curve.c₄, curve.Δ] β' := by
    refine mul_left_cancel₀ (show (6 : MvPolynomial Coeff ℤ) ≠ 0 by norm_num) ?_
    rw [hαβ]
    simp only [map_mul, map_ofNat]
    ring
  rw [hf']
  exact add_mem (aeval_mem_adjoin α') (mul_mem (Algebra.subset_adjoin (by simp))
    (aeval_mem_adjoin β'))

/-- **Deligne's theorem.** Every integral modular form lies in the subring `ℤ[c₄, c₆, Δ]`. -/
theorem IsIntegralModularForm.mem_adjoin (hf : IsIntegralModularForm k f) :
    f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} := by
  have h : 6 ^ k * f ∈
      Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} :=
    Algebra.adjoin_mono (Set.insert_subset_insert
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))) hf.six_pow_mul_mem_adjoin
  clear hf
  induction k generalizing f with
  | zero => simpa using h
  | succ k ih => exact ih (mem_adjoin_of_six_mul_mem (by rwa [pow_succ', mul_assoc] at h))

/-- **The ring of integral modular forms.** A polynomial in the coefficients of the universal
Weierstrass curve is an integral modular form of weight `k` exactly when it lies in
`ℤ[c₄, c₆, Δ]` and is weighted homogeneous of weight `k`. -/
theorem isIntegralModularForm_iff : IsIntegralModularForm k f ↔
    f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆, Universal.curve.Δ} ∧
      f.IsWeightedHomogeneous coefficientWeight k :=
  ⟨fun hf ↦ ⟨hf.mem_adjoin, hf.isWeightedHomogeneous⟩,
    fun h ↦ (isIntegralModularForm_iff_of_mem_adjoin h.1).mpr h.2⟩

end WeierstrassCurve
