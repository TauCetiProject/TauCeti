/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
public import TauCeti.RingTheory.MvPolynomial.ToricIdeal
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
(`WeierstrassCurve.isIntegralModularForm_iff_of_mem_adjoin`). Conversely, by Deligne's theorem
every integral modular form lies in `ℤ[c₄, c₆, Δ]`
(`WeierstrassCurve.IsIntegralModularForm.mem_adjoin`).
Together these determine the ring of integral modular forms of level one: an integral modular form
of weight `k` is exactly a weighted homogeneous element of weight `k` of `ℤ[c₄, c₆, Δ]`
(`WeierstrassCurve.isIntegralModularForm_iff`), and this subring is presented by the single
relation `c₄³ - c₆² = 1728Δ` (`WeierstrassCurve.Universal.adjoinC₄C₆ΔEquiv`).

Deligne's theorem is proved in two steps. First, after inverting `6` a change of variables with
`u⁻¹ = 6` carries every Weierstrass curve to `y² = x³ - 27c₄x - 54c₆`
(`WeierstrassCurve.exists_variableChange_smul_eq_c₄_c₆`); evaluating an integral modular form `f`
of weight `k` there shows that `6ᵏ f` is a polynomial in `c₄` and `c₆`. Second, `ℤ[c₄, c₆, Δ]`
is saturated with respect to `6`: every element of it is `α(c₄, Δ) + c₆ β(c₄, Δ)`, and reducing
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
* `WeierstrassCurve.IsIntegralModularForm.six_pow_mul_mem_adjoin`: if `f` is an integral modular
  form of weight `k`, then `6ᵏ f` lies in `ℤ[c₄, c₆]`.
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
    simp [W, specialize_map]
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
  set g : Fin 2 → MvPolynomial (Fin 2) R := ![X 0 ^ 4, X 0 ^ 6 * X 1]
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
  have hg : g = fun i ↦ AddMonoidAlgebra.single (expo i) 1 := by
    funext i
    fin_cases i <;> simp [g, ← single_eq_monomial, X]
  -- The substitution maps the monomial with exponent `d` to the one with exponent `A d`.
  have hcoeff (p : MvPolynomial (Fin 2) R) (d : Fin 2 →₀ ℕ) :
      (aeval g p).coeff (A d) = p.coeff d := by
    rw [hg, TauCeti.aeval_single_eq_mapDomainAlgHom, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_apply_of_injective hAinj _ _
  have hzero (p : MvPolynomial (Fin 2) R) {m : Fin 2 →₀ ℕ} (hm : m ∉ Set.range A) :
      (aeval g p).coeff m = 0 := by
    rw [hg, TauCeti.aeval_single_eq_mapDomainAlgHom, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.coeff_mapDomain]
    exact Finsupp.mapDomain_of_notMem_range _ _ hm
  have hX : (X 0 ^ 6 : MvPolynomial (Fin 2) R) = monomial (.single 0 6) 1 := X_pow_eq_monomial
  constructor
  · ext d
    rw [← hcoeff, h, hX, coeff_monomial_mul']
    split_ifs with h6
    · rw [hzero, mul_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      rintro ⟨d', hd'⟩
      have h0 := DFunLike.congr_fun hd' 0
      have h1 := DFunLike.congr_fun hd' 1
      have h6' : 6 ≤ A d 0 := by simpa using h6
      simp only [Finsupp.tsub_apply, (hA d).1, (hA d).2, (hA d').1, (hA d').2] at h0 h1 h6'
      simp at h0 h1
      omega
    · rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · ext d
    have hle : Finsupp.single (0 : Fin 2) 6 ≤ A d + .single 0 6 := le_add_self
    have h' := congrArg (fun p : MvPolynomial (Fin 2) R ↦ p.coeff (A d + .single 0 6)) h
    simp only [hX, coeff_monomial_mul', hle, ↓reduceIte, add_tsub_cancel_right, one_mul,
      hcoeff] at h'
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ← h', hzero]
    rintro ⟨d', hd'⟩
    have h0 := DFunLike.congr_fun hd' 0
    have h1 := DFunLike.congr_fun hd' 1
    simp only [Finsupp.add_apply, (hA d).1, (hA d).2, (hA d').1, (hA d').2] at h0 h1
    simp at h0 h1
    omega

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
  have h := congrArg mod6Curve.specialize hαβ
  rw [map_mul, map_add, map_mul, hs, hs, specialize_c₆, mod6Curve_c₆, map_ofNat,
    six_eq_zero, zero_mul, eq_comm, neg_mul, ← sub_eq_add_neg, sub_eq_zero] at h
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

/-- **Integral modular forms are polynomials in `c₄` and `c₆` after inverting `6`.** If `f` is
an integral modular form of weight `k`, then `6ᵏ f` is a polynomial in `c₄` and `c₆` with integer
coefficients. -/
theorem IsIntegralModularForm.six_pow_mul_mem_adjoin (hf : IsIntegralModularForm k f) :
    6 ^ k * f ∈ Algebra.adjoin ℤ {Universal.curve.c₄, Universal.curve.c₆} := by
  -- Over `ℚ[a₁, ⋯, a₆]`, a change of variables with `u⁻¹ = 6` carries the universal curve to
  -- `y² = x³ - 27c₄x - 54c₆`, the base change of the curve `W₀` with this equation over
  -- `ℤ[c₄, c₆]`.
  set φ := MvPolynomial.map (σ := Coeff) (Int.castRingHom ℚ)
  have hinv {n : ℚ} (hn : n ≠ 0) : C n⁻¹ * C n = (1 : MvPolynomial Coeff ℚ) := by
    rw [← map_mul, inv_mul_cancel₀ hn, map_one]
  let : Invertible (2 : MvPolynomial Coeff ℚ) :=
    ⟨C 2⁻¹, by rw [← map_ofNat C, hinv two_ne_zero],
      by rw [← map_ofNat C, mul_comm, hinv two_ne_zero]⟩
  let : Invertible (3 : MvPolynomial Coeff ℚ) :=
    ⟨C 3⁻¹, by rw [← map_ofNat C, hinv three_ne_zero],
      by rw [← map_ofNat C, mul_comm, hinv three_ne_zero]⟩
  obtain ⟨C, hu, hC⟩ := exists_variableChange_smul_eq_c₄_c₆ (Universal.curve.map φ)
  set W₀ : WeierstrassCurve (MvPolynomial Coeff ℤ) :=
    ⟨0, 0, 0, -27 * Universal.curve.c₄, -54 * Universal.curve.c₆⟩
  have hW₀ : C • Universal.curve.map φ = W₀.map φ := by
    rw [hC]
    ext : 1 <;> simp [W₀, map_ofNat φ]
  have h := hf.specialize_smul (Universal.curve.map φ) C
  rw [hW₀, hu, specialize_map, specialize_map, specialize_curve, RingHom.comp_apply,
    RingHom.comp_apply, RingHom.id_apply] at h
  have hφ : φ (W₀.specialize f) = φ (6 ^ k * f) := by
    rw [h, map_mul, map_pow, map_ofNat]
  have hW₀f : W₀.specialize f = aeval (fun i ↦ W₀.specialize (X i)) f :=
    DFunLike.congr_fun (aeval_unique W₀.specialize.toIntAlgHom) f
  rw [← MvPolynomial.map_injective _ Int.cast_injective hφ, hW₀f]
  -- The coefficients of `W₀` lie in `ℤ[c₄, c₆]`.
  refine Algebra.adjoin_le ?_ ((Algebra.adjoin_range_eq_range_aeval ℤ _).ge ⟨f, rfl⟩)
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe]
  cases i <;> simp only [specialize_X]
  iterate 3 exact zero_mem _
  · exact mul_mem (neg_mem (ofNat_mem _ 27)) (Algebra.subset_adjoin (by simp))
  · exact mul_mem (neg_mem (ofNat_mem _ 54)) (Algebra.subset_adjoin (by simp))

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
