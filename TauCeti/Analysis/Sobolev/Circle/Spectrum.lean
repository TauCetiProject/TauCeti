/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Spectrum
public import TauCeti.Analysis.Sobolev.Circle.Algebra
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.ContinuousMap.Units
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Units and spectrum of the circle Sobolev algebras `H^s`, `s > 1/2`

For `s > 1/2` and a complete normed `ℂ`-algebra `A`, the Fourier-coefficient Sobolev space
`H^s(A)` of the circle is an algebra under the pointwise product
(`TauCeti.CircleSobolev.toContinuousMapAlgHom`). This file proves Wiener's lemma for it when `A`
is commutative: an element of `H^s(A)` is invertible in `H^s(A)` as soon as its continuous
representative takes invertible values everywhere. For `A = ℂ` this says that `1 / u ∈ H^s` for
every nowhere-vanishing `u ∈ H^s`; that is, the holomorphic map `z ↦ 1 / z` on `ℂ \ {0}` acts on
the elements of `H^s` with values in `ℂ \ {0}`, and the resolvents `(z - u)⁻¹` exist in `H^s` for
every `z` off the range of `u`.

The proof is Gelfand's. The multiplication operators `b ↦ a * b` form a closed subalgebra of the
bounded operators on `H^s(A)`, isomorphic to `H^s(A)`; it is a Banach algebra, commutative when
`A` is. A non-invertible element of `H^s(A)` is therefore annihilated by an algebra homomorphism
`φ : H^s(A) → ℂ`. Such a `φ` is continuous, and it is determined by the value `w = φ(e^{iθ})`
together with its restriction to the constant functions; the polynomial growth
`‖e^{inθ}‖ = (1 + |n|) ^ s` of the monomials in `H^s` forces `|w| = 1`, so `φ` is evaluation at
the point `x` of the circle with `e^{ix} = w`, followed by an algebra homomorphism `A → ℂ`.

## Main statements

* `TauCeti.CircleSobolev.continuous_algHom`: every algebra homomorphism `H^s(A) → ℂ` is
  continuous.
* `TauCeti.CircleSobolev.exists_forall_apply_eq_apply_single_zero`: every algebra homomorphism
  `φ : H^s(A) → ℂ` factors through evaluation at a point `x` of the circle, as
  `φ a = φ (a(x))`, with `a(x)` regarded as a constant function; for `A = ℂ`,
  `TauCeti.CircleSobolev.exists_forall_apply_eq_toContinuousMap_apply` says that `φ` is
  evaluation at `x`.
* `TauCeti.CircleSobolev.isUnit_iff_forall_isUnit` (**Wiener's lemma**): for commutative `A`, `a`
  is a unit of `H^s(A)` if and only if `a(x)` is a unit of `A` for every `x`. Equivalently,
  `toContinuousMap` is a local homomorphism `H^s(A) → C(AddCircle T, A)`
  (`TauCeti.CircleSobolev.isLocalHom_toContinuousMapAlgHom`), so it commutes with
  `Ring.inverse` (`TauCeti.CircleSobolev.toContinuousMap_ringInverse`).
* `TauCeti.CircleSobolev.spectrum_toContinuousMap`: for commutative `A`, `a` and its continuous
  representative have the same spectrum. For `A = ℂ`, `TauCeti.CircleSobolev.spectrum_eq_range`
  identifies it with the range of the continuous representative, and
  `TauCeti.CircleSobolev.isUnit_iff_forall_ne_zero` says that the units are the
  nowhere-vanishing elements.

## References

* N. Wiener, *Tauberian theorems*, Ann. of Math. **33** (1932), 1–100, for the corresponding
  statement for absolutely convergent Fourier series.
* I. M. Gelfand, *Normierte Ringe*, Rec. Math. [Mat. Sbornik] N. S. **9** (1941), 3–24, and
  Y. Katznelson, *An Introduction to Harmonic Analysis*, 3rd ed., Chapter VIII, for the proof
  through the maximal ideals of a commutative Banach algebra.
-/

public section

noncomputable section

namespace TauCeti

namespace CircleSobolev

variable {s : ℝ} {A : Type*}

section NormedRing

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [hs : Fact (1 / 2 < s)]

/-! ### The algebra of multiplication operators -/

/-- The multiplication operators `b ↦ a * b` of `H^s(A)`, as an algebra homomorphism into the
bounded operators on `H^s(A)`. -/
private def mulOperator :
    CircleSobolev s A →ₐ[ℂ] (CircleSobolev s A →L[ℂ] CircleSobolev s A) where
  toFun a := convolution hs.out (.mul ℂ A) a
  map_one' := ContinuousLinearMap.ext fun b ↦ by simp [← mul_def]
  map_mul' a b := ContinuousLinearMap.ext fun c ↦ by simp [← mul_def, mul_assoc]
  map_zero' := map_zero _
  map_add' := map_add _
  commutes' c := ContinuousLinearMap.ext fun b ↦ by
    simp [← mul_def, Algebra.algebraMap_eq_smul_one]

private theorem mulOperator_apply_apply (a b : CircleSobolev s A) : mulOperator a b = a * b :=
  (rfl)

private theorem continuous_mulOperator : Continuous (mulOperator (s := s) (A := A)) :=
  (convolution hs.out (.mul ℂ A)).continuous

private theorem mulOperator_injective : Function.Injective (mulOperator (s := s) (A := A)) :=
  fun a b h ↦ by simpa [mulOperator_apply_apply] using congr($h 1)

/-- The algebra of multiplication operators is closed: an element is recovered from its
multiplication operator by evaluation at `1`, so `mulOperator` is bounded below. -/
private theorem isClosed_range_mulOperator :
    IsClosed ((mulOperator (s := s) (A := A)).range :
      Set (CircleSobolev s A →L[ℂ] CircleSobolev s A)) := by
  rw [AlgHom.coe_range]
  refine ((convolution hs.out (.mul ℂ A)).antilipschitz_of_bound
    (K := ‖(1 : CircleSobolev s A)‖₊) fun a ↦ ?_).isClosed_range
    (convolution hs.out (.mul ℂ A)).uniformContinuous
  calc ‖a‖ = ‖convolution hs.out (.mul ℂ A) a 1‖ := by rw [← mul_def, mul_one]
    _ ≤ ‖convolution hs.out (.mul ℂ A) a‖ * ‖(1 : CircleSobolev s A)‖ :=
      (convolution hs.out (.mul ℂ A) a).le_opNorm 1
    _ = _ := mul_comm _ _

private instance : CompleteSpace (mulOperator (s := s) (A := A)).range :=
  IsClosed.completeSpace_coe (hs := isClosed_range_mulOperator)

/-- `H^s(A)` is isomorphic, as an algebra, to the algebra of its multiplication operators. -/
private def mulOperatorEquiv : CircleSobolev s A ≃ₐ[ℂ] (mulOperator (s := s) (A := A)).range :=
  AlgEquiv.ofInjective _ mulOperator_injective

private theorem coe_mulOperatorEquiv (a : CircleSobolev s A) :
    (mulOperatorEquiv a : CircleSobolev s A →L[ℂ] CircleSobolev s A) = mulOperator a :=
  (rfl)

private theorem continuous_mulOperatorEquiv :
    Continuous (mulOperatorEquiv (s := s) (A := A)) :=
  continuous_induced_rng.2 <| by simpa only [Function.comp_def, coe_mulOperatorEquiv]
    using continuous_mulOperator

private theorem continuous_mulOperatorEquiv_symm :
    Continuous (mulOperatorEquiv (s := s) (A := A)).symm := by
  have h (S : (mulOperator (s := s) (A := A)).range) :
      mulOperatorEquiv.symm S = (S : CircleSobolev s A →L[ℂ] _) 1 := by
    conv_rhs => rw [← mulOperatorEquiv.apply_symm_apply S]
    rw [coe_mulOperatorEquiv, mulOperator_apply_apply, mul_one]
  exact (continuous_congr h).2 <|
    (ContinuousLinearMap.apply ℂ (CircleSobolev s A) 1).continuous.comp continuous_subtype_val

/-! ### Characters of `H^s(A)` -/

/-- Every algebra homomorphism `H^s(A) → ℂ` is continuous. -/
theorem continuous_algHom (φ : CircleSobolev s A →ₐ[ℂ] ℂ) : Continuous φ := by
  have h : Continuous (φ.comp (mulOperatorEquiv (s := s) (A := A)).symm.toAlgHom) :=
    map_continuous _
  exact (continuous_congr fun a ↦ by simp).1 (h.comp continuous_mulOperatorEquiv)

/-- An algebra homomorphism `H^s(A) → ℂ`, as a continuous linear functional. -/
private def algHomCLM (φ : CircleSobolev s A →ₐ[ℂ] ℂ) : CircleSobolev s A →L[ℂ] ℂ :=
  { φ.toLinearMap with cont := continuous_algHom φ }

private theorem algHomCLM_apply (φ : CircleSobolev s A →ₐ[ℂ] ℂ) (b : CircleSobolev s A) :
    algHomCLM φ b = φ b :=
  (rfl)

/-- An algebra homomorphism `H^s(A) → ℂ` does not vanish on the invertible monomial `e^{iθ}`. -/
private theorem algHom_single_one_ne_zero (φ : CircleSobolev s A →ₐ[ℂ] ℂ) :
    φ (single 1 1) ≠ 0 :=
  right_ne_zero_of_mul_eq_one (M₀ := ℂ) (a := φ (single (-1) 1)) <| by
    rw [← map_mul, single_mul_single, neg_add_cancel, mul_one, ← one_def, map_one]

/-- The value of an algebra homomorphism `H^s(A) → ℂ` on the monomial `e^{inθ}` is the `n`-th
power of its value on `e^{iθ}`. -/
private theorem algHom_single_one (φ : CircleSobolev s A →ₐ[ℂ] ℂ) (n : ℤ) :
    φ (single n 1) = φ (single 1 1) ^ n := by
  have hne := algHom_single_one_ne_zero φ
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, ← one_def, map_one]
  | succ i ih => rw [zpow_add_one₀ hne, ← ih, ← map_mul, single_mul_single, mul_one]
  | pred i ih =>
    have h := congr(φ $(single_mul_single (s := s) (-(i : ℤ) - 1) 1 (1 : A) 1))
    rw [map_mul, sub_add_cancel, mul_one, ih] at h
    rw [zpow_sub_one₀ hne, ← h, mul_inv_cancel_right₀ hne]

/-- An algebra homomorphism `φ : H^s(A) → ℂ` takes a value of modulus one on `e^{iθ}`: `φ` is
bounded, while the norms `‖e^{inθ}‖ = (1 + |n|) ^ s` of the monomials grow only polynomially in
`n ∈ ℤ`. -/
private theorem norm_algHom_single_one (φ : CircleSobolev s A →ₐ[ℂ] ℂ) :
    ‖φ (single 1 1)‖ = 1 := by
  set w := φ (single 1 1)
  set C := ‖algHomCLM φ‖ * ‖(1 : A)‖
  have hbound (n : ℤ) : ‖w‖ ^ n ≤ C * (1 + |(n : ℝ)|) ^ s :=
    calc ‖w‖ ^ n = ‖algHomCLM φ (single n 1)‖ := by
          rw [← norm_zpow, algHomCLM_apply, algHom_single_one]
      _ ≤ ‖algHomCLM φ‖ * ‖single (s := s) n (1 : A)‖ := (algHomCLM φ).le_opNorm _
      _ = _ := by rw [norm_single, weight_def]; ring
  refine le_antisymm (Real.le_one_of_forall_pow_le_mul_rpow fun n ↦ by simpa using hbound n) ?_
  have := Real.le_one_of_forall_pow_le_mul_rpow (r := ‖w‖⁻¹) fun n ↦ by simpa using hbound (-n)
  exact (inv_le_one₀ (norm_pos_iff.2 (algHom_single_one_ne_zero φ))).1 this

variable (T : ℝ) [Fact (0 < T)]

/-- **Characters of `H^s(A)`.** Every algebra homomorphism `φ : H^s(A) → ℂ` factors through
evaluation at a point `x` of the circle: `φ a = φ (a(x))`, where the value `a(x) ∈ A` is regarded
as a constant function. -/
theorem exists_forall_apply_eq_apply_single_zero (φ : CircleSobolev s A →ₐ[ℂ] ℂ) :
    ∃ x : AddCircle T, ∀ a, φ a = φ (single 0 (toContinuousMap T hs.out a x)) := by
  set w := φ (single 1 1)
  have hw : ‖w‖ = 1 := norm_algHom_single_one φ
  -- `w` is the value at some point `x` of the circle of the first Fourier character.
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (Fact.out : 0 < T).ne').surjective
    ⟨w, mem_sphere_zero_iff_norm.2 hw⟩
  rw [AddCircle.homeomorphCircle_apply] at hx
  have hfourier (n : ℤ) : fourier n x = w ^ n := by
    rw [fourier_apply, AddCircle.toCircle_zsmul, hx]
    exact Circle.coe_zpow _ n
  -- Both sides are continuous linear functionals that agree on the monomials.
  refine ⟨x, fun a ↦ ?_⟩
  let Ψ : CircleSobolev s A →L[ℂ] ℂ := (algHomCLM φ).comp
    ((single 0).comp ((ContinuousMap.evalCLM ℂ x).comp (toContinuousMap T hs.out)))
  have hΦΨ : algHomCLM φ = Ψ := continuousLinearMap_ext_single fun n c ↦ by
    have h : single (s := s) n c = single n 1 * single 0 c := by
      rw [single_mul_single, add_zero, one_mul]
    simp only [Ψ, ContinuousLinearMap.coe_comp, Function.comp_apply, algHomCLM_apply,
      ContinuousMap.evalCLM_apply, toContinuousMap_single]
    rw [h, map_mul, algHom_single_one φ n]
    simp [ContinuousMap.smul_apply', hfourier, w]
  simpa only [Ψ, ContinuousLinearMap.coe_comp, Function.comp_apply, algHomCLM_apply,
    ContinuousMap.evalCLM_apply] using congr($hΦΨ a)

end NormedRing

section NormedCommRing

variable [NormedCommRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [hs : Fact (1 / 2 < s)]
  (T : ℝ) [Fact (0 < T)]

/-- The algebra of multiplication operators is a commutative Banach algebra. -/
private instance : NormedCommRing (mulOperator (s := s) (A := A)).range where
  mul_comm := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext <| by simp only [Subalgebra.coe_mul, ← map_mul, mul_comm a b]

/-- A non-unit of `H^s(A)` is annihilated by some algebra homomorphism `H^s(A) → ℂ`. -/
private theorem exists_algHom_apply_eq_zero {a : CircleSobolev s A} (ha : ¬IsUnit a) :
    ∃ φ : CircleSobolev s A →ₐ[ℂ] ℂ, φ a = 0 := by
  have he : ¬IsUnit (mulOperatorEquiv a) := fun h ↦ ha <| by
    simpa using h.map (mulOperatorEquiv (s := s) (A := A)).symm
  obtain ⟨χ, hχ⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero he
  exact ⟨(WeakDual.CharacterSpace.equivAlgHom χ).comp mulOperatorEquiv.toAlgHom, hχ⟩

/-! ### Wiener's lemma -/

/-- **Wiener's lemma for `H^s(A)`, `s > 1/2`.** An element of `H^s(A)` is a unit if and only if
its continuous representative takes invertible values at every point of the circle. -/
theorem isUnit_iff_forall_isUnit {a : CircleSobolev s A} :
    IsUnit a ↔ ∀ x, IsUnit (toContinuousMap T hs.out a x) := by
  refine ⟨fun h ↦ (ContinuousMap.isUnit_iff_forall_isUnit _).1 <| by
    simpa using h.map (toContinuousMapAlgHom (s := s) (A := A) T), fun h ↦ ?_⟩
  by_contra ha
  obtain ⟨φ, hφ⟩ := exists_algHom_apply_eq_zero ha
  obtain ⟨x, hx⟩ := exists_forall_apply_eq_apply_single_zero T φ
  obtain ⟨u, hu⟩ := h x
  -- The constant function `a(x)` is a unit of `H^s(A)`, so `φ` cannot vanish on it.
  have hc : IsUnit (single (s := s) 0 (toContinuousMap T hs.out a x)) :=
    ⟨⟨single 0 u, single 0 ↑u⁻¹, by simp [← one_def], by simp [← one_def]⟩, by rw [← hu]⟩
  exact (hc.map φ).ne_zero (by rw [← hx, hφ])

/-- `toContinuousMap` reflects units: an element of `H^s(A)` whose continuous representative is a
unit of `C(AddCircle T, A)` is a unit of `H^s(A)`. -/
instance isLocalHom_toContinuousMapAlgHom :
    IsLocalHom (toContinuousMapAlgHom (s := s) (A := A) T) where
  map_nonunit a ha := (isUnit_iff_forall_isUnit T).2 <|
    (ContinuousMap.isUnit_iff_forall_isUnit _).1 (by simpa using ha)

/-- An element of `H^s(A)` is a unit exactly when its continuous representative is a unit of
`C(AddCircle T, A)`. -/
@[simp]
theorem isUnit_toContinuousMap_iff {a : CircleSobolev s A} :
    IsUnit (toContinuousMap T hs.out a) ↔ IsUnit a :=
  coe_toContinuousMapAlgHom (s := s) (A := A) T ▸ isUnit_map_iff (toContinuousMapAlgHom T) a

/-- The continuous representative of the inverse `1 / a` is the inverse of the continuous
representative of `a`; both sides are `0` when `a` is not a unit. -/
@[simp]
theorem toContinuousMap_ringInverse (a : CircleSobolev s A) :
    toContinuousMap T hs.out (Ring.inverse a) = Ring.inverse (toContinuousMap T hs.out a) :=
  coe_toContinuousMapAlgHom (s := s) (A := A) T ▸ map_ringInverse (toContinuousMapAlgHom T) a

/-- An element of `H^s(A)` and its continuous representative have the same spectrum. -/
@[simp]
theorem spectrum_toContinuousMap (a : CircleSobolev s A) :
    spectrum ℂ (toContinuousMap T hs.out a) = spectrum ℂ a :=
  coe_toContinuousMapAlgHom (s := s) (A := A) T ▸
    AlgHom.spectrum_apply_eq (toContinuousMapAlgHom T) a

end NormedCommRing

section Complex

variable [hs : Fact (1 / 2 < s)] (T : ℝ) [Fact (0 < T)]

/-- **Characters of `H^s`.** Every algebra homomorphism `H^s(ℂ) → ℂ` is evaluation of the
continuous representative at a point of the circle. -/
theorem exists_forall_apply_eq_toContinuousMap_apply (φ : CircleSobolev s ℂ →ₐ[ℂ] ℂ) :
    ∃ x : AddCircle T, ∀ a, φ a = toContinuousMap T hs.out a x := by
  obtain ⟨x, hx⟩ := exists_forall_apply_eq_apply_single_zero T φ
  refine ⟨x, fun a ↦ ?_⟩
  rw [hx, ← Algebra.algebraMap_self_apply (toContinuousMap T hs.out a x), ← algebraMap_eq_single,
    AlgHom.commutes, Algebra.algebraMap_self_apply]

/-- **Wiener's lemma for `H^s`, `s > 1/2`.** An element of `H^s(ℂ)` is a unit if and only if its
continuous representative vanishes nowhere. -/
theorem isUnit_iff_forall_ne_zero {a : CircleSobolev s ℂ} :
    IsUnit a ↔ ∀ x, toContinuousMap T hs.out a x ≠ 0 := by
  simp only [isUnit_iff_forall_isUnit T, isUnit_iff_ne_zero]

/-- The spectrum of an element of `H^s(ℂ)`, `s > 1/2`, is the range of its continuous
representative. -/
theorem spectrum_eq_range (a : CircleSobolev s ℂ) :
    spectrum ℂ a = Set.range (toContinuousMap T hs.out a) := by
  rw [← spectrum_toContinuousMap T, ContinuousMap.spectrum_eq_range]

end Complex

end CircleSobolev

end TauCeti
