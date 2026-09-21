/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Scalar

/-!
# The prime-power recurrence of the Hecke ring on the character spaces

For `p` coprime to `N` the Hecke ring satisfies `T_{p^{r+2}} = Tₚ T_{p^{r+1}} − p S_p T_{p^r}`
(`heckeTGeneratorRecGamma0_succ_succ`). The scalar coset `S_p` acts on the character space by
`χ(p) p^{k−2}` (`heckeRingHomCharSpace_heckeTScalarGamma0`, `Nebentypus/Scalar.lean`), so `p • S_p`
acts by `χ(p) p^{k−1}` and transporting the recurrence along the ring homomorphism gives
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}` on `M_k(N, χ)` and on `S_k(N, χ)`.

`Prime/Power.lean` consumes the pointwise forms to compute Fourier coefficients of `T_{p^r}`, and
`Newforms/RingEigenvalue.lean` to derive the recurrence for the eigenvalues of a newform.

## Main results

* `HeckeRing.GL2.heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ` and its pointwise form
  `..._succ_succ_apply`: the two-step recurrence on `M_k(N, χ)`.
* `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ` and its pointwise
  form `..._succ_succ_apply`: the same recurrence on `S_k(N, χ)`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {p : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- **The recurrence, transported to the character space.** For `p` coprime to `N`,
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}` as endomorphisms of `M_k(N, χ)`: the
image of `heckeTGeneratorRecGamma0_succ_succ` under the ring homomorphism, with the scalar coset
acting by `χ(p) p^{k−2}` (`heckeRingHomCharSpace_heckeTScalarGamma0`), so that `p • S_p` acts
by `χ(p) p^{k−1}`. Only positivity of `p` is used. -/
theorem heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ (hp : 0 < p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) =
      heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) *
          heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) := by
  refine LinearMap.ext fun F ↦ ?_
  rw [heckeTGeneratorRecGamma0_succ_succ, map_sub, map_mul, map_mul, map_zsmul,
    heckeRingHomCharSpace_heckeTScalarGamma0 k χ p hp hpN]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
  congr 2
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hk : k - 1 = k - 2 + 1 := by ring
  rw [hk, zpow_add_one₀ hp0]
  push_cast
  ring

/-- **The recurrence at a form**: `heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ`
evaluated. This is the pointwise interface — the shape the coefficient formula of
`Prime/Power.lean` and the eigenvalue recurrence of `Newforms/RingEigenvalue.lean` consume. -/
theorem heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply (hp : 0 < p)
    (hpN : Nat.Coprime p N) (F : modFormCharSpace k χ) (r : ℕ) :
    heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) F =
      heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p)
          (heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) F) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F := by
  rw [heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ k χ hp hpN r]
  rfl

/-- **The recurrence on `S_k(N, χ)`**, as an equality of endomorphisms:
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}` on the cusp-form character space. The
modular statement transported along the inclusion of character spaces
(`cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap`), which is injective. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ (hp : 0 < p)
    (hpN : Nat.Coprime p N) (r : ℕ) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) *
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) := by
  refine LinearMap.ext fun F ↦ ?_
  refine cuspToModFormCharSpace_injective k χ ?_
  simpa only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, map_sub, map_smul,
    heckeRingHomCuspCharSpace_apply, heckeRingHomCharSpace_apply,
    cuspToModFormCharSpace_twistedHeckeSlashCuspFormCharLinearMap]
    using heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply k χ hp hpN _ r

/-- **The recurrence at a cusp form**:
`heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ` evaluated. This is the pointwise
interface, the shape the coefficient formulas of `Prime/Power.lean` and
`Newforms/RingEigenvalue.lean` consume. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ_apply (hp : 0 < p)
    (hpN : Nat.Coprime p N) (F : cuspFormCharSpace k χ) (r : ℕ) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 2)) F =
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)
          (heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p (r + 1)) F) -
        ((χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1)) •
          heckeRingHomCuspCharSpace k χ (heckeTGeneratorRecGamma0 N p r) F := by
  have h := heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ k χ hp hpN r
  exact congrArg (fun T : Module.End ℂ (cuspFormCharSpace k χ) ↦ T F) h
end HeckeRing.GL2

end
