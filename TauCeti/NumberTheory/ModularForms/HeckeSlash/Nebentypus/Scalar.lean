/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diagonal.Basic
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action

/-!
# Scalar cosets in the nebentypus Hecke action

This file identifies the action of the scalar double coset
`Γ₀(N) diag(c, c) Γ₀(N)` on functions, modular forms, and cusp forms of nebentypus `χ`.
Since the scalar matrix
normalizes `Γ₀(N)`, its double coset has one right coset. The twisting character reads its
upper-left entry as `χ(c)`, while the weight-`k` slash action contributes `c ^ (k - 2)`.
Consequently the scalar Hecke generator acts by

```lean
(χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2).
```

The factor is `χ(c)`, not `χ(c)⁻¹`: the twisted slash sum is written using right-coset
representatives in `Δ₀(N)` and weights them by `delta0NebentypusChar`, whose value on the
scalar representative is its upper-left unit `c`.

That scalar is what turns the Hecke ring's prime-power recurrence into a recurrence of
operators on the character spaces. For `p` coprime to `N` the ring satisfies
`T_{p^{r+2}} = Tₚ T_{p^{r+1}} − p S_p T_{p^r}` (`heckeTGeneratorRecGamma0_succ_succ`); since
`S_p` acts by `χ(p) p^{k−2}`, the element `p • S_p` acts by `χ(p) p^{k−1}`. Transporting along
the ring homomorphism therefore gives
`T_{p^{r+2}} = Tₚ ∘ T_{p^{r+1}} − χ(p) p^{k−1} • T_{p^r}` on `M_k(N, χ)` and on `S_k(N, χ)`,
each in an operator form and a pointwise `_apply` form.
`Prime/Power.lean` uses the pointwise forms to compute Fourier coefficients of `T_{p^r}`, and
`Newforms/RingEigenvalue.lean` to derive the recurrence for the eigenvalues of a newform.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSumCharEnd_diagCosetGamma0_const`: the scalar double coset
  acts by the expected scalar on the function character space.
* `HeckeRing.GL2.twistedHeckeSlashModularFormCharEnd_diagCosetGamma0_const`: the scalar
  double coset acts by the expected scalar on modular forms.
* `HeckeRing.GL2.twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_const`: the corresponding
  statement for cusp forms.
* `HeckeRing.GL2.heckeRingHomFunctionCharSpace_heckeTScalarGamma0`: the scalar generator under
  the function-space Hecke-ring action.
* `HeckeRing.GL2.heckeRingHomCharSpace_heckeTScalarGamma0`: the scalar generator under the
  modular-form Hecke-ring action.
* `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTScalarGamma0`: the cusp-form counterpart.
* `HeckeRing.GL2.heckeRingHomCharSpace_heckeTGeneratorRecGamma0_succ_succ` and its pointwise
  form `..._succ_succ_apply`: the two-step prime-power recurrence on `M_k(N, χ)`.
* `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTGeneratorRecGamma0_succ_succ` and its
  pointwise form `..._succ_succ_apply`: the same recurrence on `S_k(N, χ)`.

## Provenance

The scalar-slash calculation is adapted from `slash_diag_scalar` in the AINTLIB
`LeanModularForms` project (Chris Birkbeck, Apache-2.0), file
`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean` at commit
`2baa76f742bdb4fb8ee323fabba41203bd390e08`. The coset decomposition here instead uses Tau
Ceti's normalizer API and its representative-independent right-coset sum.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.3 and §3.5.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset
  HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

variable [NeZero N]

/-- The constant diagonal double coset acts on the function character space by
`χ(c) * c ^ (k - 2)`. -/
theorem twistedHeckeSlashSum_diagCosetGamma0_const (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) (f : ℍ → ℂ) (hf : f ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ
        (diagCosetGamma0 N ![c, c] fun _ ↦ by simpa using hcN) f =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • f := by
  let _ : NeZero c := ⟨hc.ne'⟩
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ _
    (fun _ : Unit ↦ natDiagGL 2 ![c, c])
    (doubleCoset_out_diagCosetGamma0_const_eq_iUnion_rightCosets N c fun _ ↦ hcN)
    (fun _ _ _ ↦ Subsingleton.elim _ _) f hf]
  simp [delta0NebentypusChar_natDiagGL N χ ![c, c]
    (fun i ↦ by fin_cases i <;> simpa using hc) hcN, smul_smul]

/-- The constant diagonal double coset acts by `χ(c) * c ^ (k - 2)` as an endomorphism of
the function character space. -/
theorem twistedHeckeSlashSumCharEnd_diagCosetGamma0_const (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) :
    twistedHeckeSlashSumCharEnd k χ
        (diagCosetGamma0 N ![c, c] fun _ ↦ by simpa using hcN) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  rw [coe_twistedHeckeSlashSumCharEnd, LinearMap.smul_apply, Module.End.one_apply]
  exact twistedHeckeSlashSum_diagCosetGamma0_const k χ c hc hcN f f.2

/-- The constant diagonal double coset acts on modular forms by
`χ(c) * c ^ (k - 2)`. -/
theorem twistedHeckeSlashModularFormCharEnd_diagCosetGamma0_const
    (c : ℕ) (hc : 0 < c) (hcN : Nat.Coprime c N) :
    twistedHeckeSlashModularFormCharEnd k χ
        (diagCosetGamma0 N ![c, c] fun _ ↦ by simpa using hcN) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply ModularForm.ext
  intro z
  rw [coe_twistedHeckeSlashModularFormCharEnd]
  have h := congrFun (twistedHeckeSlashSum_diagCosetGamma0_const k χ c hc hcN
    (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    ((coe_mem_functionCharSpace_iff k χ _).mpr f.2)) z
  -- This exposes only scalar multiplication through the endomorphism, subtype, bundled form,
  -- and function coercions; `h` is the function-space mathematical statement.
  change twistedHeckeSlashSum k χ _
      (⇑(f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) z =
    ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) *
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) z
  exact h

/-- The constant diagonal double coset has the same scalar action on cusp forms. -/
theorem twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_const
    (c : ℕ) (hc : 0 < c) (hcN : Nat.Coprime c N) :
    twistedHeckeSlashCuspFormCharEnd k χ
        (diagCosetGamma0 N ![c, c] fun _ ↦ by simpa using hcN) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply CuspForm.ext
  intro z
  rw [coe_twistedHeckeSlashCuspFormCharEnd]
  have hmem : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ functionCharSpace k χ :=
    (coe_mem_functionCharSpace_iff k χ _).mpr
      ((coe_mem_modFormCharSpace_iff k χ _).mpr f.2)
  have h := congrFun (twistedHeckeSlashSum_diagCosetGamma0_const k χ c hc hcN
    (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) hmem) z
  -- As above, this exposes only the bundled scalar/coercion layers before applying the
  -- function-space statement.
  change twistedHeckeSlashSum k χ _
      (⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) z =
    ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) *
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) z
  exact h

/-- The scalar Hecke generator acts on the function character space by
`χ(c) * c ^ (k - 2)`. -/
theorem heckeRingHomFunctionCharSpace_heckeTScalarGamma0 (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) :
    heckeRingHomFunctionCharSpace k χ (heckeTScalarGamma0 N c) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  rw [heckeTScalarGamma0_of_coprime N hc hcN, heckeRingHomFunctionCharSpace_apply,
    twistedHeckeSlashRingCharLinearMap_single, one_smul]
  exact twistedHeckeSlashSumCharEnd_diagCosetGamma0_const k χ c hc hcN

/-- The scalar Hecke generator acts on modular forms by
`χ(c) * c ^ (k - 2)`. -/
theorem heckeRingHomCharSpace_heckeTScalarGamma0 (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) :
    heckeRingHomCharSpace k χ (heckeTScalarGamma0 N c) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  rw [heckeTScalarGamma0_of_coprime N hc hcN, heckeRingHomCharSpace_apply,
    twistedHeckeSlashModularFormCharLinearMap_single, one_smul]
  rw [twistedHeckeSlashModularFormCharEnd_diagCosetGamma0_const k χ c hc hcN]

/-- The scalar Hecke generator acts on cusp forms by
`χ(c) * c ^ (k - 2)`. -/
theorem heckeRingHomCuspCharSpace_heckeTScalarGamma0 (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) :
    heckeRingHomCuspCharSpace k χ (heckeTScalarGamma0 N c) =
      ((χ (ZMod.unitOfCoprime c hcN) : ℂ) * (c : ℂ) ^ (k - 2)) • 1 := by
  rw [heckeTScalarGamma0_of_coprime N hc hcN, heckeRingHomCuspCharSpace_apply,
    twistedHeckeSlashCuspFormCharLinearMap_single, one_smul]
  rw [twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_const k χ c hc hcN]

/-! ### The prime-power recurrence of the Hecke ring on the character spaces -/

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
