/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Crystal.Connected
public import TauCeti.RepresentationTheory.LSPath.Crystal.Operations

/-!
# Concatenation powers of `B(λ)` and the inclusion `B(n • λ) ↪ B(λ)^n`

For a dominant weight `λ`, an injective additive realization `f : M →+ V`, and height forms
`F i` inducing the simple coroot pairings on `f(M)`, the `n`-fold concatenation power `B(λ)^n` of
the realized Lakshmibai–Seshadri path crystal is crystal-admissible
(`TauCeti.LSPath.isCrystalSet_pow_range_toPLPath`). Because the straight path of shape `n • λ` is
the `n`-fold concatenation of the straight path of shape `λ` and every element of `B(n • λ)` is
reached from `straight (n • λ)` by lowering operators, `B(n • λ)` is contained in `B(λ)^n`
(`TauCeti.LSPath.range_toPLPath_nsmul_subset_pow`) and embeds into it by a strict crystal morphism
(`TauCeti.LSPath.nsmulInclusionHom`).

## Main definitions

* `TauCeti.LSPath.nsmulInclusionHom`: strict embedding of `B(n • λ)` into the `n`-fold
  concatenation crystal on `B(λ)^n`.

## Main results

* `TauCeti.LSPath.isCrystalSet_pow_range_toPLPath`: `B(λ)^n` is crystal-admissible.
* `TauCeti.LSPath.range_toPLPath_nsmul_subset_pow`: tensor-power containment `B(n • λ) ⊆ B(λ)^n`.

## References

* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, §§2, 4.
-/

public section

namespace TauCeti.LSPath

open RootPairing
open scoped Pointwise

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}
  [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V]
  {f : M →+ V}

/-- The `n`-fold concatenation power of the realized LS crystal `B(λ)` is crystal-admissible. -/
theorem isCrystalSet_pow_range_toPLPath (hlam : lam ∈ dominantChamber P b) (f : M →+ V)
    {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (n : ℕ) :
    PLPath.IsCrystalSet b f F ((Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, ← Set.singleton_one]
    simpa [map_zero, PLPath.straight_zero] using
      PLPath.isCrystalSet_singleton_straight (𝕜 := 𝕜) hF (χ := 0) (by simp)
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hF (isCrystalSet_range_toPLPath hlam f hF)

/-- **Tensor-power containment `B(n • λ) ⊆ B(λ)^n`**: for dominant `λ` and every `n : ℕ`, every
realized LS path of shape `n • λ` is a concatenation of `n` realized LS paths of shape `λ`. -/
theorem range_toPLPath_nsmul_subset_pow (hlam : lam ∈ dominantChamber P b)
    (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (n : ℕ) :
    Set.range (fun π : LSPath P b (n • lam) ↦ π.toPLPath 𝕜 f) ⊆
      (Set.range fun π : LSPath P b lam ↦ π.toPLPath 𝕜 f) ^ n := by
  rintro _ ⟨π, rfl⟩
  have hstraight : PLPath.straight 𝕜 (f (n • lam)) ∈
      (Set.range fun ρ : LSPath P b lam ↦ ρ.toPLPath 𝕜 f) ^ n := by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul 𝕜, PLPath.straight_natCast_smul]
    exact Set.pow_mem_pow ⟨straight lam, toPLPath_straight 𝕜 f⟩
  refine (isCrystalSet_pow_range_toPLPath hlam f hF n).mem_of_reflTransGen_rootStep ?_ hstraight
  exact Relation.ReflTransGen.mono (fun _ _ ⟨i, hi⟩ ↦ PLPath.RootStep.of_lower_eq_some hi) _ _
    (reflTransGen_lower_toPLPath_straight (nsmul_mem_dominantChamber P b n hlam) hf hF π)

/-- **Strict embedding `B(n • λ) ↪ B(λ)^n`** into the `n`-fold concatenation crystal of `B(λ)`. -/
noncomputable def nsmulInclusionHom (hlam : lam ∈ dominantChamber P b)
    (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (n : ℕ) :
    NormalCrystal.StrictHom
      (normalCrystal (nsmul_mem_dominantChamber P b n hlam) hf hF)
      (PLPath.normalCrystalOn hf hF (isCrystalSet_pow_range_toPLPath hlam f hF n)) :=
  PLPath.inclusionHom
    (isCrystalSet_range_toPLPath (nsmul_mem_dominantChamber P b n hlam) f hF)
    (isCrystalSet_pow_range_toPLPath hlam f hF n)
    (range_toPLPath_nsmul_subset_pow hlam hf hF n)

@[simp]
theorem nsmulInclusionHom_apply (hlam : lam ∈ dominantChamber P b)
    (hf : Function.Injective f) {F : b.support → Module.Dual 𝕜 V}
    (hF : ∀ (i : b.support) (m : M), F i (f m) = P.coroot' i m) (n : ℕ)
    (x : Set.range fun π : LSPath P b (n • lam) ↦ π.toPLPath 𝕜 f) :
    (nsmulInclusionHom hlam hf hF n x).val = x.val :=
  PLPath.inclusionHom_apply _ _ _ x

end TauCeti.LSPath
