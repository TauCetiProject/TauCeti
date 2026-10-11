/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.AtkinLehner.NewSpace
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.NumberTheory.ModularForms.AtkinLehner.Hecke
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient

/-!
# Atkin–Lehner transport of newforms

For an exact divisor `Q` of `N`, slashing a newform by an Atkin–Lehner matrix gives a
nonzero new eigenvector. Its first Fourier coefficient is therefore nonzero, and dividing
by that coefficient gives a uniquely determined normalized newform. Its nebentypus is
`χ ∘ ι_Q`, where `ι_Q` inverts the residue modulo `Q` and fixes the residue modulo `N / Q`.
If `χ = ψ φ` is split along these two moduli, its good-prime coefficients are
`ψ(p)⁻¹ a_p(f)`.

`HeckeRing.GL2.Newform.atkinLehnerTransform` is this normalized newform. The equation
`normalizedAtkinLehnerOperatorGamma1Cusp_eq_coeff_smul` identifies the scalar relating it
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
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    ∃ c : ℂ, heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩)
      (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm) =
      c • atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let h := hW.isExactDivisor hQ.ne' hQN
  let u := h.unitsEquivProd.symm
    ((ZMod.unitOfCoprime p (hpN.coprime_dvd_right hQN))⁻¹, 1)
  have hu : ZMod.unitsMap hQN u =
      (ZMod.unitOfCoprime p (hpN.coprime_dvd_right hQN))⁻¹ := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_fst h, MulEquiv.apply_symm_apply]
  have hu' : ZMod.unitsMap (Nat.div_dvd_of_dvd hQN) u = 1 := by
    rw [← Nat.IsExactDivisor.unitsEquivProd_apply_snd h, MulEquiv.apply_symm_apply]
  let χ := f.χ.comp (h.unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ)
  have hχ := atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace
  have heq := atkinLehnerOperatorGamma1Cusp_heckeTCuspNat hQ hQN hW hpN hu hu' f.toCuspForm
  have hc := DFunLike.congr_fun (commute_heckeTCuspNat_diamondOpCusp k hpN u).eq
    (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)
  simp only [Module.End.mul_apply] at hc
  rw [f.heckeTCuspNat_eq_eigenvalue_smul hp hpN, map_smul, ← hc,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ u hχ, map_smul] at heq
  refine ⟨(χ u : ℂ)⁻¹ * f.eigenvalue ⟨p, hp.pos⟩ hpN, ?_⟩
  rw [← smul_smul, heq, inv_smul_smul₀ (Units.ne_zero _)]

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
  obtain ⟨c, hc⟩ := atkinLehner_newform_prime_eigen f hQ hQN hW hp hpN
  refine ⟨c, ?_⟩
  rw [← heckeTCompositeGamma0_prime N hp]
  exact heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp hc

/-- The first Fourier coefficient of the Atkin–Lehner slash of a newform is nonzero.
Thus the slash can be normalized without changing its eigenline. -/
theorem _root_.HeckeRing.GL2.Newform.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero
    (f : Newform N k) (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1 ≠ 0 := by
  intro hzero
  have heig := atkinLehner_newform_ring_eigen f hQ hQN hW
  have hF := eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew
    (F := ⟨_, atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace⟩)
    (fun p hp hpN ↦ by rw [heckeTCompositeGamma0_prime N hp]; exact heig p hp hpN)
    hzero (atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ hQN hW f.isNew)
  exact f.ne_zero (atkinLehnerOperatorGamma1Cusp_injective hQ hQN hW k
    (hF.trans (map_zero _).symm))

/-- The normalized newform on the Atkin–Lehner image line of `f`. The underlying cusp form
is the slash by `W` divided by its first Fourier coefficient, and its character is `χ ∘ ι_Q`.
The result is independent of the choice of matrix for `Q`. -/
def _root_.HeckeRing.GL2.Newform.atkinLehnerTransform (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) : Newform N k :=
  Newform.ofForallPrime
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormCharSpace hQ hQN hW f.mem_charSpace)
    (atkinLehnerOperatorGamma1Cusp_mem_cuspFormsNew hQ hQN hW f.isNew)
    (fun hzero ↦ f.ne_zero (atkinLehnerOperatorGamma1Cusp_injective hQ hQN hW k
      (hzero.trans (map_zero _).symm)))
    (atkinLehner_newform_ring_eigen f hQ hQN hW)

/-- The cusp form underlying Atkin–Lehner transport is the normalized slash. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.toCuspForm_atkinLehnerTransform (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (f.atkinLehnerTransform hQ hQN hW).toCuspForm =
      ((qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1)⁻¹ •
        atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm := by
  unfold Newform.atkinLehnerTransform
  exact Newform.ofForallPrime_toCuspForm _ _ _ _

/-- Atkin–Lehner transport inverts the `Q`-part of the nebentypus. -/
@[simp]
theorem _root_.HeckeRing.GL2.Newform.χ_atkinLehnerTransform (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    (f.atkinLehnerTransform hQ hQN hW).χ =
      f.χ.comp ((hW.isExactDivisor hQ.ne' hQN).unitsInvPart : (ZMod N)ˣ →* (ZMod N)ˣ) := by
  unfold Newform.atkinLehnerTransform
  exact Newform.ofForallPrime_χ _ _ _ _

/-- The Petersson-normalized slash is its first Fourier coefficient times the transported
newform. This specifies the scalar without making a modulus-one assertion. -/
theorem _root_.HeckeRing.GL2.Newform.normalizedAtkinLehnerOperatorGamma1Cusp_eq_coeff_smul
    (f : Newform N k) (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    atkinLehnerNormalizer Q k • atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm =
      (atkinLehnerNormalizer Q k *
        (qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1) •
          (f.atkinLehnerTransform hQ hQN hW).toCuspForm := by
  rw [f.toCuspForm_atkinLehnerTransform, mul_smul,
    smul_inv_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)]

/-- A newform is the Atkin–Lehner transform exactly when its line contains the slash.
Normalization determines the scalar and the newform uniquely. -/
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerTransform_eq_iff (f g : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W) :
    f.atkinLehnerTransform hQ hQN hW = g ↔
      ∃ c : ℂ, atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm = c • g.toCuspForm := by
  constructor
  · rintro rfl
    refine ⟨(qExpansion 1 (atkinLehnerOperatorGamma1Cusp hQ hQN hW k f.toCuspForm)).coeff 1, ?_⟩
    rw [f.toCuspForm_atkinLehnerTransform,
      smul_inv_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)]
  · rintro ⟨c, hc⟩
    have ha := congrArg (CuspForm.qExpansionCoeffₗ one_pos
      (one_mem_strictPeriods_Gamma1_map N) k 1) hc
    simp only [CuspForm.qExpansionCoeffₗ_apply, map_smul, g.qExpansion_coeff_one,
      smul_eq_mul, mul_one] at ha
    apply Newform.ext
    rw [f.toCuspForm_atkinLehnerTransform]
    nth_rw 2 [hc]
    rw [← ha,
      inv_smul_smul₀ (f.qExpansion_coeff_one_atkinLehnerOperatorGamma1Cusp_ne_zero hQ hQN hW)]

/-- The normalized transported newform does not depend on the Atkin–Lehner matrix. -/
theorem _root_.HeckeRing.GL2.Newform.atkinLehnerTransform_eq (f : Newform N k)
    (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    (hW' : IsAtkinLehnerMatrix N Q W') :
    f.atkinLehnerTransform hQ hQN hW = f.atkinLehnerTransform hQ hQN hW' := by
  obtain ⟨γ, hγ, rfl⟩ := hW'.exists_mem_Gamma0_eq_mul_left hQ.ne' hQN hW
  obtain ⟨c, hc⟩ := (f.atkinLehnerTransform_eq_iff
    (f.atkinLehnerTransform hQ hQN hW') hQ hQN hW').mp rfl
  apply (f.atkinLehnerTransform_eq_iff _ hQ hQN _).mpr
  exact ⟨(f.χ ((Gamma0Map N).toHomUnits ⟨γ, hγ⟩) : ℂ) * c, by
    rw [atkinLehnerOperatorGamma1Cusp_mul_left_of_mem_cuspFormCharSpace hQ hQN hW'
      hγ f.mem_charSpace, hc, smul_smul]⟩

/-- If the nebentypus is `ψ φ` along `N = Q · (N / Q)`, the Fourier coefficient of the
transported newform at a good prime `p` is `ψ(p)⁻¹ a_p(f)`. -/
theorem _root_.HeckeRing.GL2.Newform.qExpansion_coeff_prime_atkinLehnerTransform
    (f : Newform N k) (hQ : 0 < Q) (hQN : Q ∣ N) (hW : IsAtkinLehnerMatrix N Q W)
    (ψ : (ZMod Q)ˣ →* ℂˣ) (φ : (ZMod (N / Q))ˣ →* ℂˣ)
    (hχ : f.χ = ψ.comp (ZMod.unitsMap hQN) *
      φ.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hQN)))
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) :
    (qExpansion 1 (f.atkinLehnerTransform hQ hQN hW).toCuspForm).coeff p =
      (ψ (ZMod.unitOfCoprime p (hpN.coprime_dvd_right hQN)) : ℂ)⁻¹ *
        (qExpansion 1 f.toCuspForm).coeff p := by
  have : NeZero p := ⟨hp.ne_zero⟩
  let g := f.atkinLehnerTransform hQ hQN hW
  obtain ⟨c, hc⟩ := (f.atkinLehnerTransform_eq_iff g hQ hQN hW).mp rfl
  have hc0 : c ≠ 0 := by
    intro hzero
    rw [hzero, zero_smul] at hc
    exact f.ne_zero (atkinLehnerOperatorGamma1Cusp_injective hQ hQN hW k
      (hc.trans (map_zero _).symm))
  have hT :=
    (heckeTCuspNat_atkinLehnerOperatorGamma1Cusp_eq_smul_iff_heckeTCuspNat_eq_smul
      ψ φ hQ hQN hW hpN (hχ ▸ f.mem_charSpace) (f.eigenvalue ⟨p, hp.pos⟩ hpN)).mpr
      (f.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  rw [hc, map_smul, g.heckeTCuspNat_eq_eigenvalue_smul hp hpN, smul_smul, smul_smul] at hT
  have heig : g.eigenvalue ⟨p, hp.pos⟩ hpN =
      (ψ (ZMod.unitOfCoprime p (hpN.coprime_dvd_right hQN)) : ℂ)⁻¹ *
        f.eigenvalue ⟨p, hp.pos⟩ hpN := by
    apply mul_left_cancel₀ hc0
    simpa only [mul_comm c] using smul_left_injective ℂ g.ne_zero hT
  rw [← g.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ hpN,
    ← f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm ⟨p, hp.pos⟩ hpN] at heig
  exact heig

end TauCeti
