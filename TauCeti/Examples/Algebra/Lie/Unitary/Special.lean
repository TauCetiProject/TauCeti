/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Unitary.Special
public import TauCeti.RepresentationTheory.SU2.Weyl.Basic

/-!
# Checks: the Cartan three-form on a root `𝔰𝔲(2)` of `𝔰𝔲(3)`

A homomorphism `f : SU(2) → K` attached to a root of a compact semisimple group `K` is detected on
`π₃` by the Cartan three-form `ω(X, Y, Z) = B(X, ⁅Y, Z⁆)` of the Killing form `B` of `𝔨`: on a
basis `e₁, e₂, e₃` of `𝔰𝔲(2)` with `⁅e₂, e₃⁆ = e₁`, the pulled-back form takes the value
`f^*ω(e₁, e₂, e₃) = B(df e₁, df e₁) < 0`. This file checks the Lie-algebra content of this for
`K = SU(3)`, with matrices indexed by `Fin 2 ⊕ Fin 1`, its diagonal torus and the root
`α = ε₁ - ε₂`, where the rank-one representative is the block inclusion of `SU(2)` onto the
upper-left `2 × 2` block. The Checks are stated for the Lie algebra block inclusion
`df = TauCeti.specialUnitaryBlockInclusion` and the Lie algebras only: the group homomorphism
`SU(2) → SU(3)` and the identification of its differential with `df` are not formalized here.

* The differential sends `diag(i, -i)` to the coroot `α^∨ = diag(i, -i, 0)`, and `α(α^∨) = 2`.
* With `B(X, Y) = 6 Re tr(X Y)` on `𝔰𝔲(3)` and `e₁ = ½ diag(i, -i)`,
  `e₂ = ½ [[0, 1], [-1, 0]]`, `e₃ = ½ [[0, i], [i, 0]]`, the pulled-back form takes the value
  `B(df e₁, df e₁) = 6 Re tr(¼ diag(-1, -1, 0)) = -3`.
* The Killing form `4 Re tr(X Y)` of `𝔰𝔲(2)` itself gives `4 Re tr(e₁²) = -2` instead: the value
  depends on the ambient group, its sign does not
  (`TauCeti.card_smul_cartanThreeForm_compLinearMap_specialUnitaryBlockInclusion`).
* The representative `f ∘ c_w`, for the conjugation `c_w` by the Weyl element
  `w = [[0, 1], [-1, 0]]` of `SU(2)`, has differential sending `diag(i, -i)` to `-α^∨`, and gives
  the same value `-3`.

## References

* R. Bott, *An application of the Morse theory to the topology of Lie-groups*, Bull. Soc. Math.
  France 84 (1956), 251–281, §1.
* E. Meinrenken, *Lie groups and Lie algebras*, lecture notes, Theorem 12.4, Proposition 12.5
  and Remark 12.6.
-/

public section

noncomputable section

open LieAlgebra Matrix Complex

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

/-- The coroot generator `diag(i, -i)` of the diagonal torus of `SU(2)`. -/
def suTwoCoroot : specialUnitaryLieAlgebra (Fin 2) :=
  ⟨!![I, 0; 0, -I], mem_specialUnitaryLieAlgebra_iff.mpr <| by
    refine ⟨?_, by simp [trace_fin_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp⟩

/-- `e₁ = ½ diag(i, -i)`. -/
def suTwoE₁ : specialUnitaryLieAlgebra (Fin 2) := (1 / 2 : ℝ) • suTwoCoroot

/-- `e₂ = ½ [[0, 1], [-1, 0]]`. -/
def suTwoE₂ : specialUnitaryLieAlgebra (Fin 2) :=
  ⟨!![0, 1 / 2; -1 / 2, 0], mem_specialUnitaryLieAlgebra_iff.mpr <| by
    refine ⟨?_, by simp [trace_fin_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [neg_div]⟩

/-- `e₃ = ½ [[0, i], [i, 0]]`. -/
def suTwoE₃ : specialUnitaryLieAlgebra (Fin 2) :=
  ⟨!![0, I / 2; I / 2, 0], mem_specialUnitaryLieAlgebra_iff.mpr <| by
    refine ⟨?_, by simp [trace_fin_two]⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [neg_div]⟩

theorem coe_suTwoE₁ :
    (suTwoE₁ : Matrix (Fin 2) (Fin 2) ℂ) = !![I / 2, 0; 0, -I / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suTwoE₁, suTwoCoroot, neg_div] <;> ring

/-- `⁅e₂, e₃⁆ = e₁`. -/
theorem lie_suTwoE₂_suTwoE₃ : ⁅suTwoE₂, suTwoE₃⁆ = suTwoE₁ := by
  ext1
  rw [LieSubalgebra.coe_bracket, Ring.lie_def, coe_suTwoE₁]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoE₂, suTwoE₃] <;> ring

/-- The Lie algebra block inclusion `𝔰𝔲(2) → 𝔰𝔲(3)`, standing in for the differential of the
block inclusion `SU(2) → SU(3)` (that identification is not formalized here). -/
private abbrev df :
    specialUnitaryLieAlgebra (Fin 2) →ₗ⁅ℝ⁆ specialUnitaryLieAlgebra (Fin 2 ⊕ Fin 1) :=
  specialUnitaryBlockInclusion (Fin 2) (Fin 1)

/-- The Cartan three-form of the Killing form of `𝔰𝔲(3)`. -/
private abbrev ω₃ : specialUnitaryLieAlgebra (Fin 2 ⊕ Fin 1) [⋀^Fin 3]→ₗ[ℝ] ℝ :=
  (killingForm ℝ (specialUnitaryLieAlgebra (Fin 2 ⊕ Fin 1))).cartanThreeForm fun x y z ↦
    LieModule.traceForm_lieInvariant ℝ _ _ x y z

/-! ### The coroot -/

/-- **The block inclusion sends `diag(i, -i)` to the coroot `α^∨ = diag(i, -i, 0)`.** -/
example : (df suTwoCoroot : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ) =
    diagonal (Sum.elim ![I, -I] 0) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [suTwoCoroot]

/-- **`α(α^∨) = 2`** for the root `α = ε₁ - ε₂`, read on the diagonal entries as
`(α^∨₁₁ - α^∨₂₂) / i`. -/
example : ((df suTwoCoroot : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ) (.inl 0) (.inl 0) -
    (df suTwoCoroot : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ) (.inl 1) (.inl 1)) / I = 2 := by
  norm_num [suTwoCoroot, ← two_mul, mul_div_assoc]

/-! ### The value of the pulled-back Cartan three-form -/

/-- The Killing form of `𝔰𝔲(3)` at `df e₁` is `6 Re tr(¼ diag(-1, -1, 0)) = -3`. -/
theorem killingForm_specialUnitaryBlockInclusion_suTwoE₁ :
    killingForm ℝ (specialUnitaryLieAlgebra (Fin 2 ⊕ Fin 1))
      (specialUnitaryBlockInclusion (Fin 2) (Fin 1) suTwoE₁)
      (specialUnitaryBlockInclusion (Fin 2) (Fin 1) suTwoE₁) = -3 := by
  rw [killingForm_specialUnitaryBlockInclusion_apply, coe_suTwoE₁]
  norm_num [trace_fin_two]

/-- **`f^*ω(e₁, e₂, e₃) = B(df e₁, df e₁) = -3`** for the Cartan three-form of the Killing form
`B(X, Y) = 6 Re tr(X Y)` of `𝔰𝔲(3)`. -/
example : ω₃.compLinearMap df.toLinearMap ![suTwoE₁, suTwoE₂, suTwoE₃] = -3 := by
  rw [← LinearMap.BilinMap.cartanThreeForm_compl₁₂,
    LinearMap.BilinMap.cartanThreeForm_apply_of_lie_eq lie_suTwoE₂_suTwoE₃,
    LinearMap.compl₁₂_apply]
  exact killingForm_specialUnitaryBlockInclusion_suTwoE₁

/-- **The Killing form of `𝔰𝔲(2)` itself gives `4 Re tr(e₁²) = -2`**, so its own Cartan
three-form takes the value `-2` on `(e₁, e₂, e₃)`: the value depends on the ambient group, the sign
does not. -/
example : (killingForm ℝ (specialUnitaryLieAlgebra (Fin 2))).cartanThreeForm
    (fun x y z ↦ LieModule.traceForm_lieInvariant ℝ _ _ x y z)
      ![suTwoE₁, suTwoE₂, suTwoE₃] = -2 := by
  rw [LinearMap.BilinMap.cartanThreeForm_apply_of_lie_eq lie_suTwoE₂_suTwoE₃,
    killingForm_specialUnitaryLieAlgebra_apply, coe_suTwoE₁]
  norm_num [trace_fin_two]

/-! ### The other representative -/

/-- The Weyl element `w = [[0, 1], [-1, 0]]` of `SU(2)`, the inverse of `TauCeti.SU2.weylElement`,
as a unitary matrix. -/
def suTwoWeyl : unitaryGroup (Fin 2) ℂ :=
  ⟨_, specialUnitaryGroup_le_unitaryGroup (SU2.weylElement⁻¹).property⟩

/-- Conjugation by the Weyl element reverses the coroot: `w diag(i, -i) wᴴ = -diag(i, -i)`. -/
theorem specialUnitaryAdjoint_suTwoWeyl_suTwoCoroot :
    specialUnitaryAdjoint suTwoWeyl suTwoCoroot = -suTwoCoroot := by
  ext1
  rw [coe_specialUnitaryAdjoint_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [suTwoWeyl, SU2.coe_weylElement_inv, suTwoCoroot, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The representative `f ∘ c_w` sends `diag(i, -i)` to `-α^∨`.** -/
example : (df (specialUnitaryAdjoint suTwoWeyl suTwoCoroot) :
    Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℂ) = -diagonal (Sum.elim ![I, -I] 0) := by
  rw [specialUnitaryAdjoint_suTwoWeyl_suTwoCoroot]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [suTwoCoroot]

/-- **The representative `f ∘ c_w` gives the same value `-3`**: its differential is
`df ∘ Ad_w`, and `Ad_w e₁ = -e₁`. -/
example : ω₃.compLinearMap (df.comp (specialUnitaryAdjoint suTwoWeyl)).toLinearMap
    ![suTwoE₁, suTwoE₂, suTwoE₃] = -3 := by
  have hw : specialUnitaryAdjoint suTwoWeyl suTwoE₁ = -suTwoE₁ := by
    rw [suTwoE₁, map_smul, specialUnitaryAdjoint_suTwoWeyl_suTwoCoroot, smul_neg]
  rw [← LinearMap.BilinMap.cartanThreeForm_compl₁₂,
    LinearMap.BilinMap.cartanThreeForm_apply_of_lie_eq lie_suTwoE₂_suTwoE₃,
    LinearMap.compl₁₂_apply, LieHom.coe_toLinearMap, LieHom.comp_apply, hw, map_neg,
    LinearMap.map_neg₂, LinearMap.map_neg, neg_neg]
  exact killingForm_specialUnitaryBlockInclusion_suTwoE₁

end TauCeti
