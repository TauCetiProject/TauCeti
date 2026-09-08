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

end HeckeRing.GL2

end
