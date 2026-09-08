/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
public import TauCeti.NumberTheory.HeckeRing.Normalizer
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action

/-!
# Scalar cosets in the nebentypus Hecke action

This file identifies the action of the scalar double coset
`Γ₀(N) diag(c, c) Γ₀(N)` on modular and cusp forms of nebentypus `χ`. Since the scalar matrix
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

* `HeckeRing.GL2.twistedHeckeSlashModularFormCharEnd_diagCosetGamma0_const`: the scalar
  double coset acts by the expected scalar on modular forms.
* `HeckeRing.GL2.twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0_const`: the corresponding
  statement for cusp forms.
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

omit [NeZero N] in
/-- The twisting character reads the constant diagonal representative as its scalar entry. -/
lemma delta0NebentypusChar_natDiagGL_const (c : ℕ) (hc : 0 < c)
    (hcN : Nat.Coprime c N) :
    delta0NebentypusChar N χ
        ⟨natDiagGL 2 ![c, c],
          natDiagGL_mem_Delta0_of_coprime N _ fun _ ↦ by simpa using hcN⟩ =
      χ (ZMod.unitOfCoprime c hcN) := by
  rw [delta0NebentypusChar_apply]
  apply congrArg χ
  apply Units.ext
  rw [Delta0UpperUnit_apply_val N
    (A := Matrix.diagonal (fun _ : Fin 2 ↦ (c : ℤ)))
    (by
      rw [natDiagGL_coe_eq_map_intCast 2 _
        (fun i ↦ by fin_cases i <;> simpa using hc)]
      congr 2
      funext i
      fin_cases i <;> rfl)]
  simp [ZMod.coe_unitOfCoprime]

/-- A positive rational scalar matrix acts trivially on the upper half-plane and its
weight-`k` slash is multiplication by `c ^ (k - 2)`. -/
lemma rat_slash_natDiagGL_const (c : ℕ) (hc : 0 < c) (f : ℍ → ℂ) :
    f ∣[k] natDiagGL 2 ![c, c] = (c : ℂ) ^ (k - 2) • f := by
  have hcpos : ∀ i : Fin 2, 0 < ![c, c] i := by
    intro i
    fin_cases i <;> simpa using hc
  have hdetpos : 0 <
      (natDiagGL 2 ![c, c] : Matrix (Fin 2) (Fin 2) ℚ).det :=
    natDiagGL_det_pos 2 _ hcpos
  have hcne : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  ext z
  rw [ModularForm.rat_slash_apply_of_det_pos k hdetpos]
  have hsmul :
      Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (natDiagGL 2 ![c, c]) • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (ModularForm.det_map_ratCast_pos hdetpos)]
    change
      ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (natDiagGL 2 ![c, c])) 0 0 * (z : ℂ) +
          (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (natDiagGL 2 ![c, c])) 0 1) /
          ((Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (natDiagGL 2 ![c, c])) 1 0 * (z : ℂ) +
            (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
              (natDiagGL 2 ![c, c])) 1 1) = (z : ℂ)
    simp [Matrix.GeneralLinearGroup.map, natDiagGL_coe 2 _ hcpos, Matrix.map_apply]
    field_simp
  have hdenom :
      denom (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (natDiagGL 2 ![c, c])) z = (c : ℂ) := by
    change
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (natDiagGL 2 ![c, c])) 1 0 * (z : ℂ) +
          (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
            (natDiagGL 2 ![c, c])) 1 1 = (c : ℂ)
    simp [Matrix.GeneralLinearGroup.map, natDiagGL_coe 2 _ hcpos, Matrix.map_apply]
  have habsdet :
      (↑|(Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (natDiagGL 2 ![c, c])).det.val| : ℂ) = (c : ℂ) ^ 2 := by
    have hdet :
        (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
          (natDiagGL 2 ![c, c])).det.val =
            algebraMap ℚ ℝ
              (natDiagGL 2 ![c, c]).det.val :=
      congrArg Units.val
        (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ)
          (natDiagGL 2 ![c, c]))
    rw [hdet, Matrix.GeneralLinearGroup.val_det_apply,
      natDiagGL_coe 2 _ hcpos, Matrix.det_diagonal, Fin.prod_univ_two]
    simp only [map_mul, map_natCast]
    rw [abs_of_nonneg (by positivity)]
    push_cast
    ring
  rw [hsmul, hdenom, habsdet]
  change f z * ((c : ℂ) ^ 2) ^ (k - 1) * (c : ℂ) ^ (-k) =
    (c : ℂ) ^ (k - 2) * f z
  rw [show ((c : ℂ) ^ 2) = (c : ℂ) ^ (2 : ℤ) by norm_cast, ← _root_.zpow_mul,
    mul_assoc, ← zpow_add₀ hcne, mul_comm]
  congr 1
  ring_nf

omit [NeZero N] in
private lemma scalarCoset_cover (c : ℕ) (hcN : Nat.Coprime c N) :
    doubleCoset
        ((diagCosetGamma0 N ![c, c] fun _ ↦ by simpa using hcN).out : GL (Fin 2) ℚ)
        ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      ⋃ _ : Unit, MulOpposite.op (natDiagGL 2 ![c, c]) •
        ((Gamma0 N).map (mapGL ℚ) : Set (GL (Fin 2) ℚ)) := by
  rw [Set.iUnion_const, diagCosetGamma0_def]
  apply HeckeCoset.doubleCoset_out_mk_eq_rightCoset_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ (Gamma0 N).map (mapGL ℚ) ↔
    natDiagGL 2 ![c, c] * x * (natDiagGL 2 ![c, c])⁻¹ ∈
      (Gamma0 N).map (mapGL ℚ)
  have hconst : natDiagGL 2 ![c, c] = natDiagGL 2 (fun _ : Fin 2 ↦ c) := by
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hconst]
  rw [natDiagGL_const_comm 2 c x, mul_assoc, mul_inv_cancel, mul_one]

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
  rw [congrFun (coe_twistedHeckeSlashModularFormCharEnd_eq_sum k χ _
    (fun _ : Unit ↦ natDiagGL 2 ![c, c])
    (scalarCoset_cover c hcN) (fun _ _ _ ↦ Subsingleton.elim _ _) f) z]
  simp [delta0NebentypusChar_natDiagGL_const χ c hc hcN,
    rat_slash_natDiagGL_const k c hc, mul_assoc]

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
  rw [congrFun (coe_twistedHeckeSlashCuspFormCharEnd_eq_sum k χ _
    (fun _ : Unit ↦ natDiagGL 2 ![c, c])
    (scalarCoset_cover c hcN) (fun _ _ _ ↦ Subsingleton.elim _ _) f) z]
  simp [delta0NebentypusChar_natDiagGL_const χ c hc hcN,
    rat_slash_natDiagGL_const k c hc, mul_assoc]

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
