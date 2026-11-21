/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Newform
public import TauCeti.NumberTheory.ModularForms.Newforms.Fricke
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Classification
import TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Primes
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne.Basic
import TauCeti.NumberTheory.ModularForms.Petersson.AtkinLehner
import TauCeti.NumberTheory.ModularForms.Petersson.Conjugate
import TauCeti.NumberTheory.ModularForms.Petersson.RankinSelberg

/-!
# The Atkin–Li pseudo-eigenvalue of a newform at an exact divisor

Let `f` be a newform of level `N`, weight `k` and nebentypus `χ = χ_Q · χ_{N/Q}`, split along an
exact divisor `Q ∥ N`. Write `𝒲_Q = (√Q) ^ (2 - k) • (· ∣[k] W)` for the normalized slash by the
Atkin–Li matrix `W = atkinLiMatrix N Q`, whose lower-right entry is `1` modulo `N / Q`. Then
`𝒲_Q f = λ_Q(f) • g`, where `g = f.atkinLehnerTransform h` is the newform of nebentypus
`χ_Q⁻¹ · χ_{N/Q}` on the line of `𝒲_Q f`. The scalar `λ_Q(f)` is the **pseudo-eigenvalue** of
Atkin and Li. The choice of `W` matters: another Atkin–Lehner matrix for `Q` changes `λ_Q(f)` by a
value of `χ`, and under the Atkin–Li normalization `𝒲_Q ∘ 𝒲_Q` is the constant
`χ_Q(-1) χ_{N/Q}(Q)⁻¹` on `S_k(N, χ)`.

The operator identities give:

* The product law `λ_Q(f) · λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹`, from the square of `𝒲_Q` and the fact
  that transporting twice returns `f`.
* The two endpoints: at `Q = 1` the Atkin–Li matrix lies in `Γ₁(N)`, so `λ_1(f) = 1`; at `Q = N` it
  is `γ W_N` for the Fricke matrix `W_N` and some `γ ∈ Γ₀(N)` of diamond label `-1`, so `g = f_ρ`
  and `λ_N(f)` is `χ(-1)` times the Fricke pseudo-eigenvalue.
* The norm identity `|λ_Q(f)|² ⟪g, g⟫ = ⟪f, f⟫`, from the Petersson unitarity of `𝒲_Q`. Hence
  `|λ_Q(f)| = 1` exactly when `f` and `g` have the same Petersson norm.
* Explicit identification of `g` in the two split cases: if `χ_Q` is trivial then `g = f`, and `f`
  is a genuine `𝒲_Q`-eigenform with `λ_Q(f)² = χ_{N/Q}(Q)⁻¹`; if `χ_{N/Q}` is trivial then
  `g = f_ρ` is the conjugate newform.

For a general nebentypus, `|λ_Q(f)| = 1` follows from the equality of Petersson norms
`⟪g, g⟫ = ⟪f, f⟫`. First, `|a_n(g)| = |a_n(f)|` for every `n`: at good primes `p ∤ N` the Hecke
recurrence yields `a_{p^r}(g) = χ_Q(p)⁻ʳ a_{p^r}(f)`; at bad primes `p ∣ N` transport preserves
the conductor of the nebentypus so Li's classification fixes `|a_p|` and `a_{p^r} = a_p^r` extends
this to prime powers; multiplicativity then covers all `n`. Rankin–Selberg unfolding
(`CuspForm.peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq`) then forces `⟪g, g⟫ = ⟪f, f⟫`,
and hence `|λ_Q(f)| = 1` and `λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹ · conj λ_Q(f)`.

## Main definitions

All declarations are in the namespace `HeckeRing.GL2.Newform`.

* `atkinLehnerPseudoEigenvalue`: the pseudo-eigenvalue `λ_Q(f)`.

## Main results

* `smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul`: `𝒲_Q f = λ_Q(f) • g`,
  with uniqueness of the scalar in
  `atkinLehnerPseudoEigenvalue_eq_of_atkinLehnerOperatorGamma1Cusp_eq_smul`.
* `atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform`: the product
  law, with the two factors of the nebentypus read off as values of `χ` at CRT units; and
  `atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform_of_χ_eq_mul`
  for a given splitting `χ = χ_Q · χ_{N/Q}`.
* `atkinLehnerPseudoEigenvalue_one`: `λ_1(f) = 1`.
* `atkinLehnerTransform_self`, `atkinLehnerPseudoEigenvalue_self`: at `Q = N` the transported
  newform is `f_ρ` and `λ_N(f) = χ(-1) · frickePseudoEigenvalue f`.
* `norm_atkinLehnerPseudoEigenvalue_eq_one_iff`: `|λ_Q(f)| = 1` if and only if `⟪g, g⟫ = ⟪f, f⟫`.
* `conductor_dirichletLift_atkinLehnerTransform`: Atkin–Lehner transport preserves the conductor of
  the nebentypus.
* `norm_qExpansion_coeff_atkinLehnerTransform`: `|a_n(g)| = |a_n(f)|` for every `n`.
* `peterssonInnerCosets_atkinLehnerTransform`: `⟪g, g⟫ = ⟪f, f⟫` for every nebentypus.
* `norm_atkinLehnerPseudoEigenvalue`: `|λ_Q(f)| = 1` for every nebentypus.
* `atkinLehnerPseudoEigenvalue_atkinLehnerTransform`:
  `λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹ · conj λ_Q(f)`.
* `atkinLehnerTransform_eq_self_of_χ_eq_comp_right`: if `χ` is pulled back from a character
  modulo `N / Q`, then `g = f`, so `|λ_Q(f)| = 1`
  (`norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_right`) and `λ_Q(f)² = χ_{N/Q}(Q)⁻¹`
  (`atkinLehnerPseudoEigenvalue_sq_of_χ_eq_comp_right`).
* `atkinLehnerTransform_eq_conj_of_χ_eq_comp_left`: if `χ` is pulled back from a character
  modulo `Q`, then `g = f_ρ`, so `|λ_Q(f)| = 1`
  (`norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_left`).

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of W-operators*,
  Invent. Math. **48** (1978), 221–243, §1 (Theorem 1.1).
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.16.
-/

public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane TauCeti
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor ComplexConjugate

namespace HeckeRing.GL2.Newform

variable {N Q : ℕ} [NeZero N] {k : ℤ}

/-- **The Atkin–Li pseudo-eigenvalue** `λ_Q(f)` of a newform `f` at an exact divisor `Q` of the
level: the scalar with `𝒲_Q f = λ_Q(f) • g`, where `𝒲_Q` is the slash by the Atkin–Li matrix
`atkinLiMatrix N Q` normalized by `(√Q) ^ (2 - k)` and `g = f.atkinLehnerTransform h` is the
transported newform. Since `g` has first Fourier coefficient `1`, it is the first Fourier
coefficient of `𝒲_Q f`. -/
def atkinLehnerPseudoEigenvalue (f : Newform N k) (h : Q ∥ N) : ℂ :=
  atkinLehnerNormalizer Q k * (qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd
    (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm)).coeff 1

/-- Defining equation for `atkinLehnerPseudoEigenvalue`: it is `(√Q) ^ (2 - k)` times the first
Fourier coefficient of the slash of `f` by the Atkin–Li matrix. -/
theorem atkinLehnerPseudoEigenvalue_def (f : Newform N k) (h : Q ∥ N) :
    f.atkinLehnerPseudoEigenvalue h =
      atkinLehnerNormalizer Q k * (qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd
        (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm)).coeff 1 := (rfl)

/-- **`𝒲_Q f = λ_Q(f) • g`**: the normalized slash of a newform by the Atkin–Li matrix is its
pseudo-eigenvalue times the transported newform. -/
theorem smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul
    (f : Newform N k) (h : Q ∥ N) :
    atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp h.pos h.dvd
        (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm =
      f.atkinLehnerPseudoEigenvalue h • (f.atkinLehnerTransform h).toCuspForm :=
  f.atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp_eq_smul h _

/-- A scalar `c` with `𝒲_Q f = c • g` is the pseudo-eigenvalue. -/
theorem atkinLehnerPseudoEigenvalue_eq_of_atkinLehnerOperatorGamma1Cusp_eq_smul
    (f : Newform N k) (h : Q ∥ N) {c : ℂ}
    (hc : atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp h.pos h.dvd
        (isAtkinLehnerMatrix_atkinLiMatrix h) k f.toCuspForm =
      c • (f.atkinLehnerTransform h).toCuspForm) :
    f.atkinLehnerPseudoEigenvalue h = c :=
  smul_left_injective ℂ (f.atkinLehnerTransform h).ne_zero
    ((f.smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul
      h).symm.trans hc)

/-- The pseudo-eigenvalue is nonzero, `𝒲_Q` being injective. -/
theorem atkinLehnerPseudoEigenvalue_ne_zero (f : Newform N k) (h : Q ∥ N) :
    f.atkinLehnerPseudoEigenvalue h ≠ 0 :=
  mul_ne_zero (atkinLehnerNormalizer_ne_zero h.ne_zero k)
    (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero h.pos h.dvd _)

/-- **The product law of Atkin and Li**: if the nebentypus of `f` is `χ_Q · χ_{N/Q}` along
`N = Q · (N / Q)`, then `λ_Q(f) · λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹`, where `g` is the transported
newform. Indeed `𝒲_Q g = λ_Q(g) • f` because transporting twice returns `f`, so both sides are the
constant by which `𝒲_Q ∘ 𝒲_Q` acts on `f`. -/
theorem atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform_of_χ_eq_mul
    (f : Newform N k) (h : Q ∥ N) (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)
    (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    f.atkinLehnerPseudoEigenvalue h * (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h =
      ↑(ψ (-1) * (φ (ZMod.unitOfCoprime Q h.coprime))⁻¹) := by
  have hf := f.smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul h
  have hg := smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul
    (f.atkinLehnerTransform h) h
  rw [atkinLehnerTransform_atkinLehnerTransform] at hg
  -- apply `𝒲_Q` to `𝒲_Q f = λ_Q(f) • g` and compare with the square of `𝒲_Q`
  have key : (↑(ψ (-1) * (φ (ZMod.unitOfCoprime Q h.coprime))⁻¹) : ℂ) • f.toCuspForm =
      (f.atkinLehnerPseudoEigenvalue h * (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h) •
        f.toCuspForm := by
    rw [← atkinLehnerNormalizer_sq_smul_atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp
        h.pos h.dvd (isAtkinLehnerMatrix_atkinLiMatrix h) (intCast_atkinLiMatrix_one_one h) ψ φ
        (hχ ▸ f.mem_charSpace),
      pow_two, ← smul_smul, ← map_smul, hf, map_smul, smul_comm (atkinLehnerNormalizer Q k), hg,
      smul_smul]
  exact (smul_left_injective ℂ f.ne_zero key).symm

/-- **The product law of Atkin and Li, for an arbitrary nebentypus**: `λ_Q(f) · λ_Q(g)` is
`χ(u) χ(v)⁻¹`, where the CRT units `u` and `v` have components `(-1, 1)` and `(1, Q)` modulo `Q` and
modulo `N / Q`. These are the values `χ_Q(-1)` and `χ_{N/Q}(Q)` of the two factors of the canonical
splitting of `χ` along `N = Q · (N / Q)` (`TauCeti.Nat.IsExactDivisor.eq_mul_comp_unitsMap`). -/
theorem atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N) :
    f.atkinLehnerPseudoEigenvalue h * (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h =
      ↑(f.χ (h.unitsEquivProd.symm (-1, 1)) *
        (f.χ (h.unitsEquivProd.symm (1, ZMod.unitOfCoprime Q h.coprime)))⁻¹) :=
  f.atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform_of_χ_eq_mul
    h _ _ (h.eq_mul_comp_unitsMap f.χ)

/-- **The norm identity** `|λ_Q(f)|² ⟪g, g⟫ = ⟪f, f⟫`, for `g` the transported newform: the
normalized operator `𝒲_Q` preserves the Petersson product. -/
theorem sq_norm_atkinLehnerPseudoEigenvalue_mul_peterssonInnerCosets
    (f : Newform N k) (h : Q ∥ N) :
    (‖f.atkinLehnerPseudoEigenvalue h‖ ^ 2 : ℂ) *
        CuspForm.peterssonInnerCosets (f.atkinLehnerTransform h).toCuspForm
          (f.atkinLehnerTransform h).toCuspForm =
      CuspForm.peterssonInnerCosets f.toCuspForm f.toCuspForm := by
  rw [← peterssonInnerCosets_atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp h.pos h.dvd
      (isAtkinLehnerMatrix_atkinLiMatrix h) f.toCuspForm f.toCuspForm,
    f.smul_atkinLehnerOperatorGamma1Cusp_eq_atkinLehnerPseudoEigenvalue_smul h,
    CuspForm.peterssonInnerCosets_smul_left, CuspForm.peterssonInnerCosets_smul_right,
    ← mul_assoc, Complex.conj_mul']

/-- **`|λ_Q(f)| = 1` exactly when `f` and the transported newform `g` have the same Petersson
norm.** -/
theorem norm_atkinLehnerPseudoEigenvalue_eq_one_iff (f : Newform N k) (h : Q ∥ N) :
    ‖f.atkinLehnerPseudoEigenvalue h‖ = 1 ↔
      CuspForm.peterssonInnerCosets (f.atkinLehnerTransform h).toCuspForm
          (f.atkinLehnerTransform h).toCuspForm =
        CuspForm.peterssonInnerCosets f.toCuspForm f.toCuspForm := by
  have key := f.sq_norm_atkinLehnerPseudoEigenvalue_mul_peterssonInnerCosets h
  have hf : CuspForm.peterssonInnerCosets f.toCuspForm f.toCuspForm ≠ 0 :=
    mt (CuspForm.peterssonInnerCosets_self_eq_zero _).mp f.ne_zero
  constructor
  · intro h1
    rwa [h1, Complex.ofReal_one, one_pow, one_mul] at key
  · intro heq
    rw [heq] at key
    have hsq : ‖f.atkinLehnerPseudoEigenvalue h‖ ^ 2 = 1 := by
      exact_mod_cast mul_right_cancel₀ hf (key.trans (one_mul _).symm)
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp hsq

/-- **If the `Q`-part of the nebentypus is trivial, transport fixes the newform**: `𝒲_Q f` is then a
multiple of `f` itself. Transport changes neither the nebentypus nor any good eigenvalue, so strong
multiplicity one applies. -/
theorem atkinLehnerTransform_eq_self_of_χ_eq_comp_right (f : Newform N k) (h : Q ∥ N)
    (φ : (ZMod (N / Q))ˣ →* ℂˣ) (hχ : f.χ = φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    f.atkinLehnerTransform h = f := by
  refine eq_of_forall_prime_eigenvalue_eq ?_ fun p hp hpN ↦ ?_
  · rw [χ_atkinLehnerTransform, hχ]
    ext u
    simp
  · rw [eigenvalue_atkinLehnerTransform f h hp hpN, hχ]
    simp [← Nat.IsExactDivisor.unitsEquivProd_apply_snd h]

/-- **If the `Q`-part of the nebentypus is trivial, `λ_Q(f) ^ 2 = χ_{N/Q}(Q)⁻¹`.** Here
`𝒲_Q f = λ_Q(f) • f` (`atkinLehnerTransform_eq_self_of_χ_eq_comp_right`), so `λ_Q(f)` is a genuine
eigenvalue of `𝒲_Q`, and the product law reads `λ_Q(f) ^ 2 = χ_{N/Q}(Q)⁻¹`. -/
theorem atkinLehnerPseudoEigenvalue_sq_of_χ_eq_comp_right (f : Newform N k) (h : Q ∥ N)
    (φ : (ZMod (N / Q))ˣ →* ℂˣ) (hχ : f.χ = φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    f.atkinLehnerPseudoEigenvalue h ^ 2 = ↑(φ (ZMod.unitOfCoprime Q h.coprime))⁻¹ := by
  have key :=
    f.atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform_of_χ_eq_mul
      h 1 φ (by rw [hχ]; ext u; simp)
  rw [atkinLehnerTransform_eq_self_of_χ_eq_comp_right f h φ hχ, ← pow_two] at key
  rw [key]
  simp

/-- **If the `Q`-part of the nebentypus is trivial, `|λ_Q(f)| = 1`.** -/
theorem norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_right (f : Newform N k) (h : Q ∥ N)
    (φ : (ZMod (N / Q))ˣ →* ℂˣ) (hχ : f.χ = φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd))) :
    ‖f.atkinLehnerPseudoEigenvalue h‖ = 1 := by
  rw [norm_atkinLehnerPseudoEigenvalue_eq_one_iff,
    atkinLehnerTransform_eq_self_of_χ_eq_comp_right f h φ hχ]

/-- **If the nebentypus is trivial away from `Q`, transport is conjugation**: the transported
newform is the conjugate newform `f_ρ`. Both have nebentypus `χ⁻¹` and good eigenvalues
`χ(p)⁻¹ a_p = conj a_p`, so strong multiplicity one applies. -/
theorem atkinLehnerTransform_eq_conj_of_χ_eq_comp_left (f : Newform N k) (h : Q ∥ N)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd)) :
    f.atkinLehnerTransform h = f.conj := by
  refine eq_of_forall_prime_eigenvalue_eq ?_ fun p hp hpN ↦ ?_
  · rw [χ_atkinLehnerTransform, χ_conj, hχ]
    ext u
    simp
  · refine (eigenvalue_atkinLehnerTransform f h hp hpN).trans
      (Eq.trans ?_ (eigenvalue_conj f ⟨p, hp.pos⟩ hpN).symm)
    -- the CRT unit `(p, 1)` and `p` itself have the same residue modulo `Q`
    have hu : f.χ (h.unitsEquivProd.symm
        (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)) =
          f.χ (ZMod.unitOfCoprime p hpN) := by
      rw [hχ, MonoidHom.comp_apply, MonoidHom.comp_apply,
        ← Nat.IsExactDivisor.unitsEquivProd_apply_fst h, MulEquiv.apply_symm_apply,
        ZMod.unitsMap_unitOfCoprime]
    rw [hu, inv_mul_eq_iff_eq_mul₀ (Units.ne_zero _)]
    exact f.toEigenformAwayFromLevel.eigenvalue_eq_mul_conj hp hpN

/-- **If the nebentypus is trivial away from `Q`, `|λ_Q(f)| = 1`**: the transported newform is the
conjugate newform, whose Petersson norm is that of `f`. -/
theorem norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_left (f : Newform N k) (h : Q ∥ N)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd)) :
    ‖f.atkinLehnerPseudoEigenvalue h‖ = 1 := by
  rw [norm_atkinLehnerPseudoEigenvalue_eq_one_iff,
    atkinLehnerTransform_eq_conj_of_χ_eq_comp_left f h ψ hχ, toCuspForm_conj,
    CuspForm.peterssonInnerCosets_conj_conj, CuspForm.peterssonInnerCosets_conj_symm]

/-! ### The endpoints `Q = 1` and `Q = N` -/

/-- **At `Q = 1` the pseudo-eigenvalue is `1`**: the Atkin–Li matrix `atkinLiMatrix N 1` lies in
`Γ₁(N)`, so `𝒲_1` is the identity on `S_k(Γ₁(N))` and `λ_1(f)` is the first Fourier coefficient
of `f`. -/
@[simp]
theorem atkinLehnerPseudoEigenvalue_one (f : Newform N k) (h : 1 ∥ N) :
    f.atkinLehnerPseudoEigenvalue h = 1 := by
  have hW := isAtkinLehnerMatrix_atkinLiMatrix h
  let γ : SL(2, ℤ) := ⟨atkinLiMatrix N 1, by simpa using hW.det_eq⟩
  have hγ : γ ∈ Gamma1 N := by
    rw [Gamma1_mem]
    refine ⟨by simp [γ, atkinLiMatrix_def], ?_, by simp [γ, atkinLiMatrix_def]⟩
    have h11 := intCast_atkinLiMatrix_one_one h
    rw [Nat.div_one] at h11
    exact h11
  have hf : atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm = f.toCuspForm := by
    have hGL : atkinLehnerGL h.pos hW = mapGL ℝ γ := by
      refine Units.ext ?_
      rw [coe_atkinLehnerGL, mapGL_coe_matrix]
      rfl
    apply DFunLike.coe_injective
    rw [coe_atkinLehnerOperatorGamma1Cusp, hGL,
      SlashInvariantFormClass.slash_action_eq _ _ (Subgroup.mem_map_of_mem _ hγ)]
  rw [atkinLehnerPseudoEigenvalue_def, hf, atkinLehnerNormalizer_one, qExpansion_coeff_one,
    mul_one]

/-- **At `Q = N` transport is conjugation**: the Fricke matrix is an Atkin–Lehner matrix for `N`,
and the normalized Fricke operator sends `f` to a multiple of the conjugate newform `f_ρ`. -/
@[simp]
theorem atkinLehnerTransform_self (f : Newform N k) (h : N ∥ N) :
    f.atkinLehnerTransform h = f.conj := by
  refine (f.atkinLehnerTransform_eq_iff f.conj h isAtkinLehnerMatrix_fricke).mpr
    ⟨(atkinLehnerNormalizer N k)⁻¹ * f.frickePseudoEigenvalue, ?_⟩
  rw [atkinLehnerOperatorGamma1Cusp_fricke, mul_smul,
    ← f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul,
    normalizedFrickeOperatorCusp_def, LinearMap.smul_apply,
    inv_smul_smul₀ (atkinLehnerNormalizer_ne_zero h.ne_zero k)]

/-- **At `Q = N` the pseudo-eigenvalue is `χ(-1)` times the Fricke pseudo-eigenvalue**: the
Atkin–Li matrix `atkinLiMatrix N N` is `γ W_N` for the Fricke matrix `W_N` and a matrix
`γ ∈ Γ₀(N)` with lower-right entry `-1` modulo `N`, so `𝒲_N f` computed with the Atkin–Li matrix
is `χ(-1)` times the normalized Fricke operator applied to `f`. -/
@[simp]
theorem atkinLehnerPseudoEigenvalue_self (f : Newform N k) (h : N ∥ N) :
    f.atkinLehnerPseudoEigenvalue h = f.χ (-1) * f.frickePseudoEigenvalue := by
  have hbez : (1 : ℤ) = N * Nat.gcdA N (N / N) + Nat.gcdB N (N / N) := by
    have := Nat.gcd_eq_gcd_ab N (N / N)
    have hNN : ((N / N : ℕ) : ℤ) = 1 := by rw [Nat.div_self h.pos, Nat.cast_one]
    rwa [h.coprime, Nat.cast_one, hNN, one_mul] at this
  let γ : SL(2, ℤ) := ⟨!![-1, 1; -N * Nat.gcdA N (N / N), -Nat.gcdB N (N / N)], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hbez⟩
  have hγ : γ ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp [γ]
  have hd : (Gamma0Map N).toHomUnits ⟨γ, hγ⟩ = -1 := by
    refine Units.ext ?_
    rw [MonoidHom.coe_toHomUnits, Gamma0Map_apply]
    have : (Nat.gcdB N (N / N) : ℤ) = 1 - N * Nat.gcdA N (N / N) := by linear_combination -hbez
    simp [γ, this]
  have hM : atkinLiMatrix N N = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; (N : ℤ), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ, atkinLiMatrix_def, Matrix.mul_apply, mul_comm]
  -- the Atkin–Li slash is `χ(-1)` times the Fricke slash
  have key : ∀ {M : Matrix (Fin 2) (Fin 2) ℤ} (hM' : IsAtkinLehnerMatrix N N M),
      M = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![0, -1; (N : ℤ), 0] →
      atkinLehnerOperatorGamma1Cusp h.pos h.dvd hM' k f.toCuspForm =
        (f.χ (-1) : ℂ) • frickeOperatorCusp k f.toCuspForm := by
    rintro M hM' rfl
    rw [atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace h.pos h.dvd
      isAtkinLehnerMatrix_fricke hγ f.mem_charSpace, hd, atkinLehnerOperatorGamma1Cusp_fricke]
  refine f.atkinLehnerPseudoEigenvalue_eq_of_atkinLehnerOperatorGamma1Cusp_eq_smul h ?_
  rw [key _ hM, atkinLehnerTransform_self, smul_comm, ← LinearMap.smul_apply,
    ← normalizedFrickeOperatorCusp_def,
    f.normalizedFrickeOperatorCusp_eq_frickePseudoEigenvalue_smul, smul_smul]

/-! ### Modulus one at general nebentypus -/

/-- **Atkin–Lehner transport preserves the conductor of the nebentypus**: inverting the `Q`-part
of `χ = χ_Q · χ_{N/Q}` preserves the conductor of the `Q`-factor and leaves the complementary
factor unchanged, and the two factors have coprime conductors. -/
theorem conductor_dirichletLift_atkinLehnerTransform (f : Newform N k) (h : Q ∥ N) :
    (f.atkinLehnerTransform h).dirichletLift.conductor = f.dirichletLift.conductor := by
  let ψ₀ : (ZMod Q)ˣ →* ℂˣ :=
    (f.χ.comp h.unitsEquivProd.symm.toMonoidHom).comp
      (MonoidHom.inl (ZMod Q)ˣ (ZMod (N / Q))ˣ)
  let φ₀ : (ZMod (N / Q))ˣ →* ℂˣ :=
    (f.χ.comp h.unitsEquivProd.symm.toMonoidHom).comp
      (MonoidHom.inr (ZMod Q)ˣ (ZMod (N / Q))ˣ)
  let ψ : DirichletCharacter ℂ N :=
    DirichletCharacter.changeLevel h.dvd (MulChar.ofUnitHom ψ₀ : DirichletCharacter ℂ Q)
  let φ : DirichletCharacter ℂ N :=
    DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd h.dvd)
      (MulChar.ofUnitHom φ₀ : DirichletCharacter ℂ (N / Q))
  have hf : f.dirichletLift = ψ * φ := by
    refine MulChar.ext fun u ↦ ?_
    have hu := congrArg Units.val (DFunLike.congr_fun (h.eq_mul_comp_unitsMap f.χ) u)
    simpa [ψ, φ, ψ₀, φ₀, dirichletLift_def, DirichletCharacter.changeLevel_def] using hu
  have hg : (f.atkinLehnerTransform h).dirichletLift = ψ⁻¹ * φ := by
    refine MulChar.ext fun u ↦ ?_
    have hχg : (f.atkinLehnerTransform h).χ =
        ψ₀⁻¹.comp (ZMod.unitsMap h.dvd) *
          φ₀.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)) := by
      rw [χ_atkinLehnerTransform, ← h.comp_unitsInvPart ψ₀ φ₀, ← h.eq_mul_comp_unitsMap f.χ]
      rfl
    have hu := congrArg Units.val (DFunLike.congr_fun hχg u)
    simpa [ψ, φ, ψ₀, φ₀, dirichletLift_def, DirichletCharacter.changeLevel_def,
      MulChar.inv_apply_eq_inv'] using hu
  have hcop : ψ.conductor.Coprime φ.conductor := by
    have hψ : ψ.conductor ∣ Q := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact DirichletCharacter.conductor_dvd_level _
    have hφ : φ.conductor ∣ N / Q := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact DirichletCharacter.conductor_dvd_level _
    exact (h.coprime.coprime_dvd_left hψ).coprime_dvd_right hφ
  have hcop_inv : ψ⁻¹.conductor.Coprime φ.conductor := by
    rwa [DirichletCharacter.conductor_inv]
  rw [hg, hf, DirichletCharacter.conductor_mul_of_coprime hcop_inv,
    DirichletCharacter.conductor_mul_of_coprime hcop, DirichletCharacter.conductor_inv]

/-- At a good prime power `p^r` (`p ∤ N`), Atkin–Lehner transport scales `a_{p^r}(f)` by
`χ_Q(p)⁻ʳ`, by induction on the Hecke prime-power recurrence. -/
private theorem qExpansion_coeff_prime_pow_atkinLehnerTransform (f : Newform N k) (h : Q ∥ N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (r : ℕ) :
    (qExpansion 1 (f.atkinLehnerTransform h).toCuspForm).coeff (p ^ r) =
      ((f.χ (h.unitsEquivProd.symm
        (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)) : ℂ)⁻¹) ^ r *
        (qExpansion 1 f.toCuspForm).coeff (p ^ r) := by
  let g := f.atkinLehnerTransform h
  let u : (ZMod N)ˣ :=
    h.unitsEquivProd.symm (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)
  let ζ : ℂ := (f.χ u : ℂ)⁻¹
  have hχg : g.dirichletLift p = ζ ^ 2 * f.dirichletLift p := by
    let up : (ZMod N)ˣ := ZMod.unitOfCoprime p hpN
    have hrel : h.unitsInvPart up = u⁻¹ ^ 2 * up := by
      apply h.unitsEquivProd.injective
      refine Prod.ext ?_ ?_
      · simp [u, up, ZMod.unitsMap_unitOfCoprime, sq, mul_assoc]
      · simp [u, up]
    rw [g.dirichletLift_apply_of_coprime hpN, f.dirichletLift_apply_of_coprime hpN]
    change (g.χ up : ℂ) = ζ ^ 2 * (f.χ up : ℂ)
    rw [χ_atkinLehnerTransform, MonoidHom.comp_apply]
    change (f.χ (h.unitsInvPart up) : ℂ) = ζ ^ 2 * (f.χ up : ℂ)
    rw [hrel, map_mul, map_pow, map_inv]
    simp [ζ]
  induction r using Nat.twoStepInduction with
  | zero =>
    simp
  | one =>
    simpa [g, ζ, u] using f.qExpansion_coeff_prime_atkinLehnerTransform h hp hpN
  | more r ih0 ih1 =>
    have hfg := g.toEigenform.qExpansion_coeff_prime_pow_add_two
      g.toEigenform_qExpansion_coeff_one hp r
    have hff := f.toEigenform.qExpansion_coeff_prime_pow_add_two
      f.toEigenform_qExpansion_coeff_one hp r
    simp only [toEigenform_toCuspForm, toEigenform_χ, ← dirichletLift_def] at hfg hff
    have h1 : (qExpansion 1 g.toCuspForm).coeff p = ζ * (qExpansion 1 f.toCuspForm).coeff p :=
      f.qExpansion_coeff_prime_atkinLehnerTransform h hp hpN
    rw [hfg, hff, h1, ih0, ih1, hχg]
    ring

/-- At a bad prime `p ∣ N`, Atkin–Lehner transport preserves `|a_p(f)|`, by Li's bad-prime
classification and conductor preservation. -/
private theorem norm_qExpansion_coeff_prime_atkinLehnerTransform_of_dvd (f : Newform N k)
    (h : Q ∥ N) {p : ℕ} (hp : p.Prime) (hpN : p ∣ N) :
    ‖(qExpansion 1 (f.atkinLehnerTransform h).toCuspForm).coeff p‖ =
      ‖(qExpansion 1 f.toCuspForm).coeff p‖ := by
  let g := f.atkinLehnerTransform h
  have hcond : g.dirichletLift.conductor = f.dirichletLift.conductor :=
    f.conductor_dirichletLift_atkinLehnerTransform h
  have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd (NeZero.ne N) hpN
  have hle : f.dirichletLift.conductor.factorization p ≤ N.factorization p :=
    (Nat.factorization_le_iff_dvd f.dirichletLift.conductor_ne_zero (NeZero.ne N)).mpr
      f.dirichletLift.conductor_dvd_level p
  rcases hle.lt_or_eq with hc | hc
  · by_cases hN : N.factorization p = 1
    · have hcf : f.dirichletLift.conductor.factorization p = 0 := by omega
      have hcg : g.dirichletLift.conductor.factorization p = 0 := by rwa [hcond]
      have hsqf := f.qExpansion_coeff_prime_sq_of_factorization_eq_one hp hN hcf
      have hsqg := g.qExpansion_coeff_prime_sq_of_factorization_eq_one hp hN hcg
      have hnorm_ptp : ∀ χ : DirichletCharacter ℂ N,
          ‖primeToPart p χ (p : ZMod (ordCompl[p] χ.conductor))‖ = 1 := fun χ ↦ by
        have hu := ZMod.coe_unitOfCoprime p (Nat.coprime_ordCompl hp χ.conductor_ne_zero)
        rw [← hu]
        exact DirichletCharacter.unit_norm_eq_one (primeToPart p χ) _
      have hsq : ‖(qExpansion 1 g.toCuspForm).coeff p‖ ^ 2 =
          ‖(qExpansion 1 f.toCuspForm).coeff p‖ ^ 2 := by
        rw [← norm_pow, ← norm_pow, hsqg, hsqf, norm_mul, norm_mul,
          hnorm_ptp g.dirichletLift, hnorm_ptp f.dirichletLift]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    · have hN2 : 2 ≤ N.factorization p := by omega
      have hcg : g.dirichletLift.conductor.factorization p < N.factorization p := by
        rwa [hcond]
      rw [g.qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt hp hN2 hcg,
        f.qExpansion_coeff_prime_eq_zero_of_factorization_conductor_lt hp hN2 hc]
  · have hcg : g.dirichletLift.conductor.factorization p = N.factorization p := by rwa [hcond]
    rw [g.norm_qExpansion_coeff_prime_of_factorization_conductor_eq hp hpN hcg,
      f.norm_qExpansion_coeff_prime_of_factorization_conductor_eq hp hpN hc]

/-- **Atkin–Lehner transport preserves the moduli of all Fourier coefficients**: for every `n`,
`|a_n(g)| = |a_n(f)|`, where `g = f.atkinLehnerTransform h`. At good primes `p ∤ N`,
`a_{p^r}(g) = χ_Q(p)⁻ʳ a_{p^r}(f)`; at bad primes `p ∣ N`, transport preserves the conductor of
the nebentypus, so Li's classification fixes `|a_p|` and `a_{p^r} = a_p^r` propagates it to all
prime powers; multiplicativity then gives all `n`. -/
theorem norm_qExpansion_coeff_atkinLehnerTransform (f : Newform N k) (h : Q ∥ N) (n : ℕ) :
    ‖(qExpansion 1 (f.atkinLehnerTransform h).toCuspForm).coeff n‖ =
      ‖(qExpansion 1 f.toCuspForm).coeff n‖ := by
  let g := f.atkinLehnerTransform h
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero =>
    rw [CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
        (one_mem_strictPeriods_Gamma1_map N),
      CuspFormClass.qExpansion_coeff_zero f.toCuspForm one_pos
        (one_mem_strictPeriods_Gamma1_map N)]
  | one =>
    rw [g.qExpansion_coeff_one, f.qExpansion_coeff_one]
  | prime_pow p r hp _ =>
    by_cases hpN : p ∣ N
    · have hpf : p ∈ f.badPrimes := f.mem_badPrimes_iff_dvd.mpr ⟨hp, hpN⟩
      have hpg : p ∈ g.badPrimes := g.mem_badPrimes_iff_dvd.mpr ⟨hp, hpN⟩
      rw [g.qExpansion_coeff_prime_pow_of_mem_badPrimes hpg r,
        f.qExpansion_coeff_prime_pow_of_mem_badPrimes hpf r, norm_pow, norm_pow,
        f.norm_qExpansion_coeff_prime_atkinLehnerTransform_of_dvd h hp hpN]
    · have hcop : p.Coprime N := hp.coprime_iff_not_dvd.mpr hpN
      rw [f.qExpansion_coeff_prime_pow_atkinLehnerTransform h hp hcop r, norm_mul, norm_pow,
        norm_inv]
      have hnorm : ‖(f.χ (h.unitsEquivProd.symm
          (ZMod.unitOfCoprime p (hcop.coprime_dvd_right h.dvd), 1)) : ℂ)‖ = 1 := by
        simpa [dirichletLift_def] using DirichletCharacter.unit_norm_eq_one f.dirichletLift
          (h.unitsEquivProd.symm (ZMod.unitOfCoprime p (hcop.coprime_dvd_right h.dvd), 1))
      rw [hnorm, inv_one, one_pow, one_mul]
  | coprime m n _ _ hmn ihm ihn =>
    have hmg := g.toEigenform.qExpansion_coeff_mul g.toEigenform_qExpansion_coeff_one hmn
    have hmf := f.toEigenform.qExpansion_coeff_mul f.toEigenform_qExpansion_coeff_one hmn
    simp only [toEigenform_toCuspForm] at hmg hmf
    rw [hmg, hmf, norm_mul, norm_mul, ihm, ihn]

/-- **Atkin–Lehner transport preserves the Petersson norm**: `⟪g, g⟫ = ⟪f, f⟫`, where
`g = f.atkinLehnerTransform h`. Both forms have the same Fourier coefficient moduli
(`norm_qExpansion_coeff_atkinLehnerTransform`), so Rankin–Selberg unfolding forces their
Petersson norms to agree. -/
theorem peterssonInnerCosets_atkinLehnerTransform (f : Newform N k) (h : Q ∥ N) :
    CuspForm.peterssonInnerCosets (f.atkinLehnerTransform h).toCuspForm
        (f.atkinLehnerTransform h).toCuspForm =
      CuspForm.peterssonInnerCosets f.toCuspForm f.toCuspForm :=
  CuspForm.peterssonInnerCosets_self_eq_of_norm_qExpansion_coeff_eq
    (f.atkinLehnerTransform h).mem_charSpace f.mem_charSpace
    (f.norm_qExpansion_coeff_atkinLehnerTransform h)

/-- **The Atkin–Li pseudo-eigenvalue has modulus `1`**, for an arbitrary nebentypus
(Atkin–Li, Theorem 1.1; Miyake, Theorem 4.6.16). -/
theorem norm_atkinLehnerPseudoEigenvalue (f : Newform N k) (h : Q ∥ N) :
    ‖f.atkinLehnerPseudoEigenvalue h‖ = 1 :=
  (f.norm_atkinLehnerPseudoEigenvalue_eq_one_iff h).mpr
    (f.peterssonInnerCosets_atkinLehnerTransform h)

/-- **The pseudo-eigenvalue of the transported newform**:
`λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹ · conj λ_Q(f)`. Since `|λ_Q(f)| = 1`, the inverse of `λ_Q(f)` is
its complex conjugate. -/
theorem atkinLehnerPseudoEigenvalue_atkinLehnerTransform (f : Newform N k) (h : Q ∥ N) :
    (f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h =
      ↑(f.χ (h.unitsEquivProd.symm (-1, 1)) *
        (f.χ (h.unitsEquivProd.symm (1, ZMod.unitOfCoprime Q h.coprime)))⁻¹) *
        starRingEnd ℂ (f.atkinLehnerPseudoEigenvalue h) := by
  have hnorm : starRingEnd ℂ (f.atkinLehnerPseudoEigenvalue h) *
      f.atkinLehnerPseudoEigenvalue h = 1 := by
    rw [mul_comm, Complex.mul_conj', f.norm_atkinLehnerPseudoEigenvalue h, Complex.ofReal_one,
      one_pow]
  linear_combination -((f.atkinLehnerTransform h).atkinLehnerPseudoEigenvalue h) * hnorm +
    starRingEnd ℂ (f.atkinLehnerPseudoEigenvalue h) *
      f.atkinLehnerPseudoEigenvalue_mul_atkinLehnerPseudoEigenvalue_atkinLehnerTransform h

end HeckeRing.GL2.Newform
