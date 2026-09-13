/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimeCosets
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Diagonal.PrimePower
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.Action
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators

/-!
# The twisted operator of `diag(1, p)` is the classical `Tₚ` on `M_k(N, χ)` and `S_k(N, χ)`

The `Γ₀(N)` Hecke ring acts on the nebentypus spaces `M_k(N, χ)` and `S_k(N, χ)` through the
`χ`-twisted slash sums (`HeckeSlash/Nebentypus/*`), while the classical `Tₚ` on `M_k(Γ₁(N))` and
`S_k(Γ₁(N))` is the untwisted sum over `Γ₁(N)` cosets (`HeckeSlash/Prime.lean`). This file
identifies the two at every prime `p`: on the nebentypus spaces the twisted operator of the
generator `diag(1, p)` **is** the classical `Tₚ`.

## Why the twist disappears

At a prime `p ∤ N`, the `Γ₀(N)` right cosets of `diag(1, p)` are named by the same `p + 1`
representatives as over `Γ₁(N)` (`Gamma0/Diagonal/PrimeCosets.lean`): `!![1, j; 0, p]` and
`σ · diag(p, 1)` with `σ ∈ Γ₀(N)` of bottom row `(N, p)`. The twisting character reads the
upper-left unit of a representative: it is `1` on the upper-triangular ones, and on
`σ · diag(p, 1)` it is `χ(σ₀₀ p)`, which is `1` because `σ₀₀ p ≡ 1 (mod N)` by the determinant
(`Delta0UpperUnit_upperTriRep`, `Delta0UpperUnit_mapGL_mul_scaleRep`). So every weight is `1`,
and the only character that survives is the nebentypus factor `χ(p)` produced by slashing `f` by
`σ` — exactly the factor the classical formula carries on the `Γ₁(N)` side. At a prime `p ∣ N`
there are only the `p` upper-triangular representatives, all of weight `1`, and both operators
are the upper-triangular `Uₚ`.

The computation happens once, on functions with the nebentypus `χ`
(`twistedHeckeSlashSum_diagCosetGamma0_of_prime`, `…_of_dvd`); the modular-form and cusp-form
statements read it through the coercions to functions.

## Main results

* `HeckeRing.GL2.twistedHeckeSlashSum_diagCosetGamma0_of_prime`,
  `HeckeRing.GL2.twistedHeckeSlashSum_diagCosetGamma0_of_dvd`: on a function with nebentypus
  `χ`, the twisted slash sum of `diag(1, p)` is the classical `Tₚ` formula.
* `HeckeRing.GL2.coe_twistedHeckeSlashModularFormCharEnd_diagCosetGamma0` and
  `HeckeRing.GL2.coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0`: at every prime `p`, the
  twisted operator of `diagCosetGamma0 N ![1, p]` is `heckeTNat k p`, resp. `heckeTCuspNat k p`,
  as functions on `ℍ`.
* `HeckeRing.GL2.heckeTNat_mem_modFormCharSpace` and
  `HeckeRing.GL2.heckeTCuspNat_mem_cuspFormCharSpace`: the classical `Tₚ` preserves the nebentypus
  spaces.
* `HeckeRing.GL2.heckeRingHomCharSpace_heckeTGeneratorGamma0` and
  `HeckeRing.GL2.heckeRingHomCuspCharSpace_heckeTGeneratorGamma0`: **the Hecke-ring action of the
  generator `heckeTGeneratorGamma0 N p` on `M_k(N, χ)`, resp. `S_k(N, χ)`, is the classical
  operator restricted to the space**, as an equality of endomorphisms; the `coe_…` companions
  read the same identity on a single form.

## Scope

This file treats prime indices only.

## Provenance

The prime case of `heckeRingHomCharSpace_D_p_eq_scalar_charRestrict` of the AINTLIB
`LeanModularForms` project (`LeanModularForms/HeckeRIngs/GL2/Unified/NebentypusHeckeRingHom.lean`,
Chris Birkbeck, commit `2baa76f742bdb4fb8ee323fabba41203bd390e08`, Apache-2.0,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>). In the source the
twist runs the other way, so its statement carries a factor `χ(p)⁻¹`; with this repository's
convention (`Nebentypus/Basic.lean`, "Which way the character goes") the factor is `1` and the
identification is exact.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup DoubleCoset HeckeRing.GLn

open scoped MatrixGroups ModularForm Pointwise

namespace HeckeRing.GL2

variable {N p : ℕ} (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- The double coset of the chosen representative of `diagCosetGamma0 N ![1, p]` is that of
`diag(1, p)`: `HeckeCoset.toSet_eq_doubleCoset_rep` read against `diagCosetGamma0_toSet`. Kept
private: the public decompositions of `Gamma0/Diagonal/PrimeCosets.lean` are stated at
`diag(1, p)` itself, and this is only the adaptor to the representative the twisted slash sums
carry. -/
private theorem doubleCoset_out_diagCosetGamma0 (p : ℕ) :
    doubleCoset ((diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N).out :
        GL (Fin 2) ℚ) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) =
      doubleCoset (natDiagGL 2 ![1, p]) ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) := by
  rw [← HeckeCoset.rep_def]
  exact (HeckeCoset.toSet_eq_doubleCoset_rep _).symm.trans (diagCosetGamma0_toSet N _ _)

/-- **The twisted slash sum of `diag(1, p)` at a prime `p ∤ N`, on a function with nebentypus
`χ`**: `Uₚ f + χ(p) • (f ∣[k] diag(p, 1))`, the classical `Tₚ` formula. -/
theorem twistedHeckeSlashSum_diagCosetGamma0_of_prime [NeZero N] (hp : p.Prime)
    (h : Nat.Coprime p N) {F : ℍ → ℂ} (hF : F ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) F =
      heckeSlashUpperTri k p F + (χ (ZMod.unitOfCoprime p h) : ℂ) • (F ∣[k] scaleRep p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ _ (primeRep (gamma0Twist N p h) p)
      ((doubleCoset_out_diagCosetGamma0 p).trans
        (doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_prime hp
          (gamma0Twist_apply_one_zero h) (gamma0Twist_apply_one_one h)))
      (op_primeRep_smul_injective (G := Gamma0 N) hp.one_lt (gamma0Twist_apply_one_one h)) F hF,
    Fintype.sum_option, heckeSlashUpperTri_def]
  simp only [primeRep_some, primeRep_none, delta0NebentypusChar_apply,
    Delta0UpperUnit_upperTriRep, Delta0UpperUnit_mapGL_mul_scaleRep hp.pos
      (gamma0Twist_apply_one_zero h) (gamma0Twist_apply_one_one h), map_one, Units.val_one,
    one_smul]
  have hslash : F ∣[k] (mapGL ℚ (gamma0Twist N p h) * scaleRep p)
      = (χ (ZMod.unitOfCoprime p h) : ℂ) • (F ∣[k] scaleRep p) := by
    rw [SlashAction.slash_mul, ModularForm.rat_slash k (mapGL ℚ (gamma0Twist N p h)), map_mapGL,
      (mem_functionCharSpace_iff k χ F).mp hF ⟨gamma0Twist N p h, gamma0Twist_mem_Gamma0 h⟩,
      Gamma0Map_toHomUnits_gamma0Twist h,
      ModularForm.rat_smul_slash_of_det_pos k (det_scaleRep_pos p)]
  rw [hslash]
  exact add_comm _ _

/-- **The twisted slash sum of `diag(1, p)` at a prime `p ∣ N`, on a function with nebentypus
`χ`**: the upper-triangular operator `Uₚ`. -/
theorem twistedHeckeSlashSum_diagCosetGamma0_of_dvd [NeZero N] (hp : p.Prime) (hpN : p ∣ N)
    {F : ℍ → ℂ} (hF : F ∈ functionCharSpace k χ) :
    twistedHeckeSlashSum k χ (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) F =
      heckeSlashUpperTri k p F := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [twistedHeckeSlashSum_eq_sum_of_rightCosets k χ _ (upperTriRep p)
      ((doubleCoset_out_diagCosetGamma0 p).trans
        (doubleCoset_natDiagGL_Gamma0_eq_iUnion_rightCosets_of_dvd hp hpN))
      (op_upperTriRep_smul_injective (G := Gamma0 N)) F hF, heckeSlashUpperTri_def]
  simp only [delta0NebentypusChar_apply, Delta0UpperUnit_upperTriRep, map_one, Units.val_one,
    one_smul]

/-- **At every prime, the twisted operator of `diag(1, p)` on `M_k(N, χ)` is the classical `Tₚ`**,
as functions on `ℍ`: `Uₚ f + χ(p) • (f ∣[k] diag(p, 1))` when `p ∤ N`, and `Uₚ f` when `p ∣ N`. -/
theorem coe_twistedHeckeSlashModularFormCharEnd_diagCosetGamma0 [NeZero N] (hp : p.Prime)
    (f : modFormCharSpace k χ) :
    ⇑((twistedHeckeSlashModularFormCharEnd k χ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) f :
          ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(heckeTNat k p (_hn := ⟨hp.ne_zero⟩) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hF := (coe_mem_functionCharSpace_iff k χ _).mpr f.2
  rw [coe_twistedHeckeSlashModularFormCharEnd]
  by_cases hpN : p ∣ N
  · rw [twistedHeckeSlashSum_diagCosetGamma0_of_dvd k χ hp hpN hF, heckeTNat_eq_upperTri k hpN,
      coe_heckeSlashUpperTriModularFormEnd]
  · have h := hp.coprime_iff_not_dvd.mpr hpN
    rw [twistedHeckeSlashSum_diagCosetGamma0_of_prime k χ hp h hF, heckeTNat_def,
      coe_heckeSlashGamma1ModularFormEnd_diagCosetGamma1_of_mem_modFormCharSpace k hp h χ f.2]

/-- **At every prime, the twisted operator of `diag(1, p)` on `S_k(N, χ)` is the classical `Tₚ`**,
as functions on `ℍ`: `Uₚ f + χ(p) • (f ∣[k] diag(p, 1))` when `p ∤ N`, and `Uₚ f` when `p ∣ N`. -/
theorem coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0 [NeZero N] (hp : p.Prime)
    (f : cuspFormCharSpace k χ) :
    ⇑((twistedHeckeSlashCuspFormCharEnd k χ
        (diagCosetGamma0 N ![1, p] fun _ ↦ Nat.coprime_one_left N) f :
          CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ⇑(heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hF : ⇑(f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ functionCharSpace k χ :=
    (mem_functionCharSpace_iff k χ _).mpr ((mem_cuspFormCharSpace_iff_nebentypus k χ _).mp f.2)
  rw [coe_twistedHeckeSlashCuspFormCharEnd]
  by_cases hpN : p ∣ N
  · rw [twistedHeckeSlashSum_diagCosetGamma0_of_dvd k χ hp hpN hF, heckeTCuspNat_eq_upperTri k hpN,
      coe_heckeSlashUpperTriCuspFormEnd]
  · have h := hp.coprime_iff_not_dvd.mpr hpN
    rw [twistedHeckeSlashSum_diagCosetGamma0_of_prime k χ hp h hF, heckeTCuspNat_def,
      coe_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_mem_cuspFormCharSpace k hp h χ f.2]

/-- **The Hecke-ring generator at a prime acts on `M_k(N, χ)` as the classical `Tₚ`**, on each
form. -/
theorem coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 [NeZero N] (hp : p.Prime)
    (f : modFormCharSpace k χ) :
    (heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) f :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeTNat k p (_hn := ⟨hp.ne_zero⟩) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [heckeTGeneratorGamma0_eq_single N hp.pos, heckeRingHomCharSpace_apply,
    twistedHeckeSlashModularFormCharLinearMap_single, one_smul]
  exact DFunLike.coe_injective
    (coe_twistedHeckeSlashModularFormCharEnd_diagCosetGamma0 k χ hp f)

/-- **The Hecke-ring generator at a prime acts on `S_k(N, χ)` as the classical `Tₚ`**, on each
form. -/
theorem coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 [NeZero N] (hp : p.Prime)
    (f : cuspFormCharSpace k χ) :
    (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) f :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [heckeTGeneratorGamma0_eq_single N hp.pos, heckeRingHomCuspCharSpace_apply,
    twistedHeckeSlashCuspFormCharLinearMap_single, one_smul]
  exact DFunLike.coe_injective
    (coe_twistedHeckeSlashCuspFormCharEnd_diagCosetGamma0 k χ hp f)

/-- **The classical `Tₚ` preserves `M_k(N, χ)`**: it agrees there with the Hecke-ring action. -/
theorem heckeTNat_mem_modFormCharSpace [NeZero N] (hp : p.Prime)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeTNat k p (_hn := ⟨hp.ne_zero⟩) f ∈ modFormCharSpace k χ :=
  coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp ⟨f, hf⟩ ▸
    (heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hf⟩).2

/-- **The classical `Tₚ` preserves `S_k(N, χ)`**: it agrees there with the Hecke-ring action. -/
theorem heckeTCuspNat_mem_cuspFormCharSpace [NeZero N] (hp : p.Prime)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) f ∈ cuspFormCharSpace k χ :=
  coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp ⟨f, hf⟩ ▸
    (heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨f, hf⟩).2

/-- **The Hecke-ring generator at a prime acts on `M_k(N, χ)` as the classical `Tₚ`**, as an
equality of endomorphisms of the space. -/
theorem heckeRingHomCharSpace_heckeTGeneratorGamma0 [NeZero N] (hp : p.Prime) :
    heckeRingHomCharSpace k χ (heckeTGeneratorGamma0 N p) =
      (heckeTNat k p (_hn := ⟨hp.ne_zero⟩)).restrict
        fun _ hf ↦ heckeTNat_mem_modFormCharSpace k χ hp hf :=
  LinearMap.ext fun f ↦ Subtype.ext (coe_heckeRingHomCharSpace_heckeTGeneratorGamma0 k χ hp f)

/-- **The Hecke-ring generator at a prime acts on `S_k(N, χ)` as the classical `Tₚ`**, as an
equality of endomorphisms of the space. -/
theorem heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 [NeZero N] (hp : p.Prime) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) =
      (heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩)).restrict
        fun _ hf ↦ heckeTCuspNat_mem_cuspFormCharSpace k χ hp hf :=
  LinearMap.ext fun f ↦
    Subtype.ext (coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 k χ hp f)

end HeckeRing.GL2
