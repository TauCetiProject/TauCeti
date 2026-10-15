/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.NewSpace
public import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient

/-!
# Atkin–Lehner transport of newforms

For an exact divisor `Q` of `N`, slashing a newform by an Atkin–Lehner matrix gives a
nonzero new eigenvector. Its first Fourier coefficient is therefore nonzero, and dividing
by that coefficient gives a uniquely determined normalized newform. Its nebentypus is
`χ ∘ ι_Q`, where `ι_Q` inverts the residue modulo `Q` and fixes the residue modulo `N / Q`.
Its good-prime coefficient at `p` is `χ(u)⁻¹ a_p(f)`, where the CRT unit `u` has
components `p` modulo `Q` and `1` modulo `N / Q`. If `χ = ψ φ` is split along these
two moduli, this is `ψ(p)⁻¹ a_p(f)`.

`HeckeRing.GL2.Newform.atkinLehnerTransform` constructs this normalized newform from
the exact divisor using the canonical matrix. The equation
`atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp_eq_smul` identifies the scalar relating it
to the Petersson-normalized slash, without asserting that this scalar has modulus one.
The characterization `atkinLehnerTransform_eq_iff` uniquely identifies the newform on that
line and makes it independent of the choice of Atkin–Lehner matrix.

The construction uses the good-prime Hecke intertwining relation, newspace stability, and
`HeckeRing.GL2.Newform.ofForallPrime` to normalize a new eigenvector.

## References

* A. O. L. Atkin and W.-C. W. Li, *Twists of newforms and pseudo-eigenvalues of
  W-operators*, Invent. Math. **48** (1978), 221–243, §1.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public noncomputable section

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open scoped MatrixGroups ModularForm TauCeti.ExactDivisor

namespace TauCeti

variable {N Q : ℕ} [NeZero N] {k : ℤ} {W W' : Matrix (Fin 2) (Fin 2) ℤ}

private theorem atkinLehner_newform_prime_eigen (f : Newform N k)
    (h : Q ∥ N) (hW : IsAtkinLehnerMatrix N Q W)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩)
      (atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm) =
      ((f.χ (h.unitsEquivProd.symm
        (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)) : ℂ)⁻¹ *
        f.eigenvalue ⟨p, hp.pos⟩ hpN) •
          atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let χ := f.χ.comp h.unitsEquivProd.symm.toMonoidHom
  let ψ := χ.comp (MonoidHom.inl (ZMod Q)ˣ (ZMod (N / Q))ˣ)
  let φ := χ.comp (MonoidHom.inr (ZMod Q)ˣ (ZMod (N / Q))ˣ)
  have hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)) :=
    h.eq_mul_comp_unitsMap f.χ
  exact (heckeTCuspNat_atkinLehnerOperatorGamma1Cusp_eq_smul_iff_heckeTCuspNat_eq_smul
    ψ φ h.pos h.dvd hW hpN (hχ ▸ f.mem_charSpace)
    (f.eigenvalue ⟨p, hp.pos⟩ hpN)).mpr (f.heckeTCuspNat_eq_eigenvalue_smul hp hpN)

private theorem atkinLehner_newform_ring_eigen (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    ∀ p : ℕ, p.Prime → p.Coprime N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k
        (f.χ.comp ((hW.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ))
        (heckeTGeneratorGamma0 N p)
        ⟨_, atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace⟩ =
      c • ⟨_, atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace⟩ := by
  intro p hp hpN
  have : NeZero p := ⟨hp.ne_zero⟩
  have hc := atkinLehner_newform_prime_eigen f (hW.isExactDivisor hQ.ne' hQN) hW hp hpN
  rw [← heckeTCompositeGamma0_prime N hp]
  exact ⟨_, heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp hc⟩

/-- The Atkin–Lehner slash of a newform is nonzero. -/
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerOperatorGamma1Cusp_ne_zero
    (f : Newform N k) (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm ≠ 0 :=
  fun hzero ↦ f.ne_zero (atkinLehnerOperatorGamma1Cusp_injective hQ hQN hW k
    (hzero.trans (map_zero _).symm))

/-- The first Fourier coefficient of the Atkin–Lehner slash of a newform is nonzero.
Thus the slash can be normalized without changing its eigenline. -/
theorem _root_.HeckeRing.GL2.Newform.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero
    (f : Newform N k) (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1 ≠ 0 := by
  exact qExpansion_coeff_one_ne_zero_of_mem_cuspFormsNew
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace)
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ hQN hW f.isNew)
    (f.atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)
    (atkinLehner_newform_ring_eigen f hQ hQN hW)

/-- The normalized newform on the Atkin–Lehner image line of `f`. The underlying cusp form
is the slash by `W` divided by its first Fourier coefficient, and its character is `χ ∘ ι_Q`.
The result is independent of the choice of matrix for `Q`. -/
private def atkinLehner_newform (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) : Newform N k :=
  Newform.ofForallPrime
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace)
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ hQN hW f.isNew)
    (f.atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)
    (atkinLehner_newform_ring_eigen f hQ hQN hW)

/-- The cusp form underlying Atkin–Lehner transport is the normalized slash. -/
private theorem atkinLehner_newform_toCuspForm (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (atkinLehner_newform f hQ hQN hW).toCuspForm =
      ((qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1)⁻¹ •
        atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm := by
  unfold atkinLehner_newform
  exact Newform.ofForallPrime_toCuspForm _ _ _ _

/-- A newform is the Atkin–Lehner transform exactly when its line contains the slash.
Normalization determines the scalar and the newform uniquely. -/
private theorem atkinLehner_newform_eq_iff (f g : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    atkinLehner_newform f hQ hQN hW = g ↔
      ∃ c : ℂ, atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm = c • g.toCuspForm := by
  constructor
  · rintro rfl
    refine ⟨(qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1, ?_⟩
    rw [atkinLehner_newform_toCuspForm f,
      smul_inv_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)]
  · rintro ⟨c, hc⟩
    have ha := congrArg (CuspForm.qExpansionCoeffₗ one_pos
      (one_mem_strictPeriods_Gamma1_map N) k 1) hc
    simp only [CuspForm.qExpansionCoeffₗ_apply, map_smul, g.qExpansion_coeff_one,
      smul_eq_mul, mul_one] at ha
    apply Newform.ext
    rw [atkinLehner_newform_toCuspForm f]
    nth_rw 2 [hc]
    rw [← ha,
      inv_smul_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)]

/-- The normalized transported newform does not depend on the Atkin–Lehner matrix. -/
private theorem atkinLehner_newform_eq (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    (hW' : IsAtkinLehnerMatrix N Q W') :
    atkinLehner_newform f hQ hQN hW = atkinLehner_newform f hQ hQN hW' := by
  obtain ⟨γ, hγ, rfl⟩ := hW'.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN hW
  obtain ⟨c, hc⟩ := (atkinLehner_newform_eq_iff f
    (atkinLehner_newform f hQ hQN hW') hQ hQN hW').mp rfl
  apply (atkinLehner_newform_eq_iff f _ hQ hQN _).mpr
  exact ⟨(f.χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) * c, by
    rw [atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace hQ hQN hW'
      hγ f.mem_charSpace, hc, smul_smul]⟩

/-- The normalized newform on the Atkin–Lehner image line of `f` for the exact divisor `Q`.
It uses `atkinLehnerMatrix N Q`; arbitrary matrices give the same normalized slash. -/
def _root_.HeckeRing.GL2.Newform.atkinLehnerTransform (f : Newform N k)
    (h : Q ∥ N) : Newform N k :=
  atkinLehner_newform f h.pos h.dvd (isAtkinLehnerMatrix_atkinLehnerMatrix h)

/-- The cusp form underlying Atkin–Lehner transport is the canonical normalized slash. -/
theorem _root_.HeckeRing.GL2.Newform.toCuspForm_atkinLehnerTransform (f : Newform N k)
    (h : Q ∥ N) :
    (f.atkinLehnerTransform h).toCuspForm =
      ((qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd
        (isAtkinLehnerMatrix_atkinLehnerMatrix h) k f.toCuspForm)).coeff 1)⁻¹ •
        atkinLehnerOperatorGamma1Cusp h.pos h.dvd
          (isAtkinLehnerMatrix_atkinLehnerMatrix h) k f.toCuspForm :=
  atkinLehner_newform_toCuspForm f h.pos h.dvd _

/-- Every Atkin–Lehner matrix gives the canonical transported newform after normalization. -/
theorem _root_.HeckeRing.GL2.Newform.toCuspForm_atkinLehnerTransform_of_isAtkinLehnerMatrix
    (f : Newform N k) (h : Q ∥ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (f.atkinLehnerTransform h).toCuspForm =
      ((qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm)).coeff 1)⁻¹ •
        atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm := by
  unfold Newform.atkinLehnerTransform
  rw [atkinLehner_newform_eq f h.pos h.dvd _ hW]
  exact atkinLehner_newform_toCuspForm f h.pos h.dvd hW

/-- Atkin–Lehner transport inverts the `Q`-part of the nebentypus. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.χ_atkinLehnerTransform (f : Newform N k)
    (h : Q ∥ N) :
    (f.atkinLehnerTransform h).χ =
      f.χ.comp (h.unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ) := by
  unfold Newform.atkinLehnerTransform atkinLehner_newform
  exact Newform.ofForallPrime_χ _ _ _ _

/-- The Petersson-normalized slash by any matrix is its first Fourier coefficient times
the canonical transported newform. This specifies the scalar without a modulus-one claim. -/
theorem
    _root_.HeckeRing.GL2.Newform.atkinLehnerNormalizer_smul_atkinLehnerOperatorGamma1Cusp_eq_smul
    (f : Newform N k) (h : Q ∥ N) (hW : IsAtkinLehnerMatrix N Q W) :
    atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm =
      (atkinLehnerNormalizer Q k *
        (qExpansion 1 (atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm)).coeff 1) •
          (f.atkinLehnerTransform h).toCuspForm := by
  rw [f.toCuspForm_atkinLehnerTransform_of_isAtkinLehnerMatrix h hW, mul_smul,
    smul_inv_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero h.pos h.dvd hW)]

/-- A newform is the canonical Atkin–Lehner transform exactly when its line contains the
slash by any chosen Atkin–Lehner matrix. Normalization determines the newform uniquely. -/
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerTransform_eq_iff (f g : Newform N k)
    (h : Q ∥ N) (hW : IsAtkinLehnerMatrix N Q W) :
    f.atkinLehnerTransform h = g ↔
      ∃ c : ℂ, atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm = c • g.toCuspForm := by
  unfold Newform.atkinLehnerTransform
  rw [atkinLehner_newform_eq f h.pos h.dvd _ hW]
  exact atkinLehner_newform_eq_iff f g h.pos h.dvd hW

/-- Atkin–Lehner transport at the exact divisor `1` fixes every newform. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerTransform_one (f : Newform N k)
    (h : 1 ∥ N) : f.atkinLehnerTransform h = f := by
  have hW : IsAtkinLehnerMatrix N 1 (1 : Matrix (Fin 2) (Fin 2) ℤ) :=
    (isAtkinLehnerMatrix_one_iff_mem_Gamma0 (1 : SL(2, ℤ))).mpr (one_mem _)
  apply (f.atkinLehnerTransform_eq_iff f h hW).mpr
  refine ⟨1, ?_⟩
  have hGL : atkinLehnerGL h.pos hW = 1 := by
    apply Units.ext
    simp [coe_atkinLehnerGL]
  rw [one_smul]
  apply DFunLike.coe_injective
  rw [coe_atkinLehnerOperatorGamma1Cusp, hGL, SlashAction.slash_one]

/-- Transporting twice by the same exact divisor fixes every newform. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerTransform_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N) :
    (f.atkinLehnerTransform h).atkinLehnerTransform h = f := by
  let hW := isAtkinLehnerMatrix_atkinLehnerMatrix h
  obtain ⟨γ, hγ, hsq⟩ := hW.exists_mem_Gamma0_mul_self h.ne_zero h.dvd
  let u : (ZMod N)ˣ := (Gamma0Map N).toHomUnits ⟨γ, hγ⟩
  have hu : ZMod.unitsMap h.dvd u = -1 :=
    hW.unitsMap_toHomUnits_gamma0Map_of_mul_self_eq h.ne_zero h.dvd hγ hsq
  have hu' : (Q : ZMod N) * u = (((atkinLehnerMatrix N Q) 1 1 : ℤ) : ZMod N) ^ 2 :=
    hW.natCast_mul_toHomUnits_gamma0Map_of_mul_self_eq hγ hsq
  apply ((f.atkinLehnerTransform h).atkinLehnerTransform_eq_iff f h hW).mpr
  refine ⟨((qExpansion 1
    (atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW k f.toCuspForm)).coeff 1)⁻¹ *
      (Q : ℂ) ^ (k - 2) * (f.χ u : ℂ), ?_⟩
  rw [f.toCuspForm_atkinLehnerTransform h, map_smul,
    atkinLehnerOperatorGamma1Cusp_atkinLehnerOperatorGamma1Cusp h.pos h.dvd hW hu hu',
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k f.χ u f.mem_charSpace,
    smul_smul, smul_smul]

/-- At a good prime `p`, transport multiplies the Hecke eigenvalue by the inverse of
`f.χ` at the CRT unit with components `p` modulo `Q` and `1` modulo `N / Q`. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.eigenvalue_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    (f.atkinLehnerTransform h).eigenvalue ⟨p, hp.pos⟩ hpN =
      (f.χ (h.unitsEquivProd.symm
        (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)) : ℂ)⁻¹ *
        f.eigenvalue ⟨p, hp.pos⟩ hpN := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let g := f.atkinLehnerTransform h
  obtain ⟨c, hc⟩ :=
    (f.atkinLehnerTransform_eq_iff g h (isAtkinLehnerMatrix_atkinLehnerMatrix h)).mp rfl
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hc
    exact f.atkinLehnerOperatorGamma1Cusp_ne_zero h.pos h.dvd
      (isAtkinLehnerMatrix_atkinLehnerMatrix h) hc
  have hT := atkinLehner_newform_prime_eigen f h
    (isAtkinLehnerMatrix_atkinLehnerMatrix h) hp hpN
  rw [hc, map_smul, g.heckeTCuspNat_eq_eigenvalue_smul hp hpN, smul_smul, smul_smul] at hT
  apply mul_left_cancel₀ hc0
  simpa only [mul_comm c] using smul_left_injective ℂ g.ne_zero hT

/-- At a good prime `p`, transport multiplies the Fourier coefficient by the inverse of
`f.χ` at the CRT unit with components `p` modulo `Q` and `1` modulo `N / Q`. -/
theorem _root_.HeckeRing.GL2.Newform.qExpansion_coeff_prime_atkinLehnerTransform
    (f : Newform N k) (h : Q ∥ N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    (qExpansion 1 (f.atkinLehnerTransform h).toCuspForm).coeff p =
      (f.χ (h.unitsEquivProd.symm
        (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd), 1)) : ℂ)⁻¹ *
        (qExpansion 1 f.toCuspForm).coeff p := by
  have heig := f.eigenvalue_atkinLehnerTransform h hp hpN
  rw [← (f.atkinLehnerTransform h).toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue
      (f.atkinLehnerTransform h).isNorm ⟨p, hp.pos⟩ hpN,
    ← f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN] at heig
  exact heig

/-- If the nebentypus is `ψ φ` along `N = Q · (N / Q)`, the Fourier coefficient of the
transported newform at a good prime `p` is `ψ(p)⁻¹ a_p(f)`. -/
theorem _root_.HeckeRing.GL2.Newform.qExpansion_coeff_prime_atkinLehnerTransform_of_split
    (f : Newform N k) (h : Q ∥ N)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)
    (hχ : f.χ = ψ.comp (ZMod.unitsMap h.dvd) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h.dvd)))
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    (qExpansion 1 (f.atkinLehnerTransform h).toCuspForm).coeff p =
      (ψ (ZMod.unitOfCoprime p (hpN.coprime_dvd_right h.dvd)) : ℂ)⁻¹ *
        (qExpansion 1 f.toCuspForm).coeff p := by
  rw [f.qExpansion_coeff_prime_atkinLehnerTransform h hp hpN, hχ]
  simp [← Nat.IsExactDivisor.unitsEquivProd_apply_fst h,
    ← Nat.IsExactDivisor.unitsEquivProd_apply_snd h]

end TauCeti
