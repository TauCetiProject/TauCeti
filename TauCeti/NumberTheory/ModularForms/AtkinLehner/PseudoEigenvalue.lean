/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.Newform
public import TauCeti.NumberTheory.ModularForms.Newforms.Fricke
public import TauCeti.NumberTheory.ModularForms.Petersson.FiniteIndex
import TauCeti.Data.ZMod.Units
import TauCeti.NumberTheory.ModularForms.Newforms.PeterssonAdjoint
import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne
import TauCeti.NumberTheory.ModularForms.Petersson.AtkinLehner
import TauCeti.NumberTheory.ModularForms.Petersson.Conjugate

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

The results here are what the operator identities give without further analytic input.

* The product law `λ_Q(f) · λ_Q(g) = χ_Q(-1) χ_{N/Q}(Q)⁻¹`, from the square of `𝒲_Q` and the fact
  that transporting twice returns `f`.
* The two endpoints: at `Q = 1` the Atkin–Li matrix lies in `Γ₁(N)`, so `λ_1(f) = 1`; at `Q = N` it
  is `γ W_N` for the Fricke matrix `W_N` and some `γ ∈ Γ₀(N)` of diamond label `-1`, so `g = f_ρ`
  and `λ_N(f)` is `χ(-1)` times the Fricke pseudo-eigenvalue.
* The norm identity `|λ_Q(f)|² ⟪g, g⟫ = ⟪f, f⟫`, from the Petersson unitarity of `𝒲_Q`. Hence
  `|λ_Q(f)| = 1` exactly when `f` and `g` have the same Petersson norm.
* That equality of norms, and so `|λ_Q(f)| = 1`, in the two cases where `g` is identified with a
  newform of known norm. If `χ_Q` is trivial then `g = f`, and `f` is a genuine `𝒲_Q`-eigenform with
  `λ_Q(f)² = χ_{N/Q}(Q)⁻¹`. If `χ_{N/Q}` is trivial then `g = f_ρ` is the conjugate newform, whose
  norm is that of `f`.

For a general nebentypus, both factors nontrivial, the equality `⟪g, g⟫ = ⟪f, f⟫` is not proved
here.

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
* `atkinLehnerTransform_eq_self_of_χ_eq_comp_right`: if `χ` is pulled back from a character
  modulo `N / Q`, then `g = f`, so `|λ_Q(f)| = 1`
  (`norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_right`) and `λ_Q(f)² = χ_{N/Q}(Q)⁻¹`
  (`atkinLehnerPseudoEigenvalue_sq_of_χ_eq_comp_right`).
* `atkinLehnerTransform_eq_conj_of_χ_eq_comp_left`: if `χ` is pulled back from a character
  modulo `Q`, then `g = f_ρ`, so `|λ_Q(f)| = 1`
  (`norm_atkinLehnerPseudoEigenvalue_of_χ_eq_comp_left`).

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of W-operators*,
  Invent. Math. **48** (1978), 221–243, §1.
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

end HeckeRing.GL2.Newform
