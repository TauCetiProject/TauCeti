/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Diamond
public import TauCeti.NumberTheory.ModularForms.Petersson.Trace

/-!
# The Petersson adjoint of the Hecke operators `Tₙ` at indices prime to the level

For `n` coprime to `N`, the Hecke operator `Tₙ` on `S_k(Γ₁(N))` has Petersson adjoint
`⟨n⟩⁻¹ Tₙ`:

```text
⟪Tₙ f, g⟫ = ⟪f, ⟨n⟩⁻¹ (Tₙ g)⟫.
```

When the second argument has nebentypus `χ`, the inverse diamond acts by the scalar `χ(n)⁻¹`,
so the formula simplifies to `⟪Tₙ f, g⟫ = ⟪f, χ(n)⁻¹ Tₙ g⟫`. This is the adjoint input for
the subsequent character-space stability, normality, and simultaneous-diagonalization results.

The purely Hecke-theoretic identification of the adjugate double coset, including the
commutation of `Tₙ` with `⟨n⟩⁻¹`, is in `HeckeSlash/Diamond.lean`. This module only applies the
Petersson trace adjunction and specializes the result to a character space.

## Main results

* `HeckeRing.GL2.peterssonInnerCosets_heckeTCuspNat`: the adjoint formula on
  `S_k(Γ₁(N))`.
* `HeckeRing.GL2.peterssonInnerCosets_heckeTCuspNat_of_mem_cuspFormCharSpace`: the formula when
  the second argument has nebentypus `χ`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.5.3.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.4.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open HeckeRing.GLn
open TauCeti (adjugateGL)

open scoped MatrixGroups ModularForm

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

namespace HeckeRing.GL2

variable {N n : ℕ} [NeZero N] [NeZero n] (k : ℤ)

/-- **The Petersson adjoint of `Tₙ`** (Diamond–Shurman, Theorem 5.5.3). For `n` coprime to the
level `N` and cusp forms `f`, `g` on `Γ₁(N)`,

`⟪Tₙ f, g⟫ = ⟪f, ⟨n⟩⁻¹ (Tₙ g)⟫`. -/
theorem peterssonInnerCosets_heckeTCuspNat (hn : n.Coprime N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm.peterssonInnerCosets (heckeTCuspNat k n f) g =
      CuspForm.peterssonInnerCosets f
        (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTCuspNat k n g)) := by
  have := isFiniteRelIndex_adjugateGL_natDiagGL hn
  have hdet : 0 < ((φ (natDiagGL 2 ![1, n]) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [coe_map_natDiagGL_one, Matrix.det_fin_two_of]
    simpa using Nat.pos_of_neZero n
  rw [TauCeti.heckeTCuspNat_eq_trace_translate,
    CuspForm.peterssonInnerCosets_trace_translate hdet Iff.rfl,
    trace_translate_adjugateGL_natDiagGL_eq_diamond_heckeT k hn]

/-- For `g` of nebentypus `χ`, the adjoint formula simplifies to
`⟪Tₙ f, g⟫ = ⟪f, χ(n)⁻¹ Tₙ g⟫`. -/
theorem peterssonInnerCosets_heckeTCuspNat_of_mem_cuspFormCharSpace
    {χ : (ZMod N)ˣ →* ℂˣ} (hn : n.Coprime N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k χ) :
    CuspForm.peterssonInnerCosets (heckeTCuspNat k n f) g =
      CuspForm.peterssonInnerCosets f
        ((χ (ZMod.unitOfCoprime n hn) : ℂ)⁻¹ • heckeTCuspNat k n g) := by
  rw [peterssonInnerCosets_heckeTCuspNat k hn, ← heckeTCuspNat_diamondOpCusp_inv k hn,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hg, map_smul, map_inv,
    Units.val_inv_eq_inv_val]

end HeckeRing.GL2
