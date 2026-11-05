/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.BigOperators
public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling
public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Weight

import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Quantum `6j` symbols, coupled `F`-ladder bases, and change-of-decomposition matrices

Building on `ClebschGordan.Recoupling` and `ClebschGordan.Weight`, this file defines the
weight-indexed quantum `6j` change-of-decomposition symbols and square fixed-total-weight `6j`
matrices on triple tensor products of signed `U_q(sl₂)` ladder modules, constructs the coupled
normalized `F`-ladder bases in which the matrix of `BialgebraModule.assoc` is block-diagonal with
diagonal entries `sixJSymbol`, proves operator reassociation and two-sided invertibility, and
evaluates all four `2 × 2` spin-`1/2` entries on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ`.

## Main definitions

* `TauCeti.UqSl2.sixJSymbol`, `TauCeti.UqSl2.sixJSymbolSymm`: quantum `6j` change-of-decomposition
  scalars and their inverses in the normalized `α₀ = 1` / `F`-ladder convention.
* `TauCeti.UqSl2.clebschGordanLeftBasis`, `TauCeti.UqSl2.clebschGordanRightBasis`: coupled
  normalized `F`-ladder bases of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` and `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`.
* `TauCeti.UqSl2.sixJMatrix`, `TauCeti.UqSl2.sixJMatrixSymm`: fixed-total-weight `6j` matrices.

## Main results

* `TauCeti.UqSl2.toMatrix_assoc_clebschGordanBasis`,
  `TauCeti.UqSl2.toMatrix_assoc_symm_clebschGordanBasis`: matrix of `BialgebraModule.assoc` and
  `assoc.symm` in the coupled normalized `F`-ladder bases.
* `TauCeti.UqSl2.assoc_comp_clebschGordanWeightInclusion`: operator reassociation of a left-coupled
  channel as a `sixJSymbol`-linear combination of right-coupled channels.
* `TauCeti.UqSl2.sixJMatrixSymm_mul_sixJMatrix`, `TauCeti.UqSl2.sixJMatrix_mul_sixJMatrixSymm`:
  two-sided invertibility of the fixed-total-weight `6j` matrix.
* `TauCeti.UqSl2.sixJSymbol_one_one_one_zero_zero`, `sixJSymbol_one_one_one_zero_two`,
  `sixJSymbol_one_one_one_two_zero`, `sixJSymbol_one_one_one_two_two`: closed-form entries on
  `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ`.

## References

* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, World Scientific, 1989, pp. 285–339.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* J. S. Carter, D. E. Flath, and M. Saito, *The Classical and Quantum 6j-symbols*, 1995.
* P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*, Sections 4.9 and 9.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule Module

variable {q : ℂ} [Fact (q ≠ 0)]

private theorem eq_homScalar_weightProjection_smul_weightInclusion
    (hq : IsGenericQuantumParameter q) {a b d : ℕ} {η : ℤˣ} (ε δ : ℤˣ) (hη : η = ε * δ)
    (f : LadderModule q d η →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)) :
    f = homScalar ((clebschGordanWeightProjection hq a ε b δ d).comp f) •
      ((clebschGordanWeightInclusion hq a ε b δ d).comp
        (LadderModule.congr rfl hη).toLinearMap) := by
  conv_lhs => rw [← LinearMap.id_comp f,
    ← sum_clebschGordanWeightInclusion_comp_projection hq a ε b δ, LinearMap.finsetSum_comp]
  by_cases hd : d ∈ Finset.range (a + b + 1)
  · rw [Finset.sum_eq_single d]
    · conv_lhs => rw [LinearMap.comp_assoc,
        eq_homScalar_smul_congr hq rfl hη ((clebschGordanWeightProjection hq a ε b δ d).comp f),
        LinearMap.comp_smul]
    · intro d' _ hne
      rw [LinearMap.comp_assoc,
        hom_eq_zero_of_weight_ne hq hne.symm ((clebschGordanWeightProjection hq a ε b δ d').comp f),
        LinearMap.comp_zero]
    · exact fun h => (h hd).elim
  · have hnot : ¬ IsClebschGordanTriple a b d := fun htr => hd htr.mem_range
    rw [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ε δ hnot,
      LinearMap.zero_comp, smul_zero]
    refine Finset.sum_eq_zero fun d' hd' => ?_
    have hne : d' ≠ d := fun h => hd (h ▸ hd')
    rw [LinearMap.comp_assoc,
      hom_eq_zero_of_weight_ne hq hne.symm ((clebschGordanWeightProjection hq a ε b δ d').comp f),
      LinearMap.comp_zero]

/-- Weight-indexed recoupling intertwiner `L_d^((εδ)ζ) →ₗ[UqSl2 q] L_d^(ε(δζ))` from left
intermediate weight `u` to right intermediate weight `v` through `BialgebraModule.assoc`. -/
def sixJRecouplingHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d u v : ℕ) :
    LadderModule q d ((ε * δ) * ζ) →ₗ[UqSl2 q] LadderModule q d (ε * (δ * ζ)) :=
  (clebschGordanWeightProjection hq a ε v (δ * ζ) d).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)).comp <|
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap.comp <|
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d)

/-- Weight-indexed inverse recoupling intertwiner `L_d^(ε(δζ)) →ₗ[UqSl2 q] L_d^((εδ)ζ)` from right
intermediate weight `v` to left intermediate weight `u` through `(BialgebraModule.assoc).symm`. -/
def sixJRecouplingSymmHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d v u : ℕ) :
    LadderModule q d (ε * (δ * ζ)) →ₗ[UqSl2 q] LadderModule q d ((ε * δ) * ζ) :=
  (clebschGordanWeightProjection hq u (ε * δ) c ζ d).comp <|
    (tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u) LinearMap.id).comp <|
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).symm.toLinearMap.comp <|
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
          (clebschGordanWeightInclusion hq a ε v (δ * ζ) d)

/-- The quantum `6j` change-of-decomposition symbol from left intermediate weight `u` in
`(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` to right intermediate weight `v` in `L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` at total
weight `d`, in the normalized `α₀ = 1` / `F`-ladder Clebsch–Gordan convention. -/
def sixJSymbol (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d u v : ℕ) : ℂ :=
  homScalar (sixJRecouplingHom hq ε δ ζ a b c d u v)

/-- The inverse quantum `6j` change-of-decomposition symbol from right intermediate weight `v` to
left intermediate weight `u` at total weight `d`. -/
def sixJSymbolSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d v u : ℕ) : ℂ :=
  homScalar (sixJRecouplingSymmHom hq ε δ ζ a b c d v u)

/-- Selection rule for `sixJSymbol`: it vanishes unless all four binary couplings are admissible
Clebsch–Gordan triples. -/
theorem sixJSymbol_eq_zero_of_not_isClebschGordanTriple (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) {a b c d u v : ℕ}
    (h : ¬ (IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d ∧
      IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)) :
    sixJSymbol hq ε δ ζ a b c d u v = 0 := by
  rw [sixJSymbol, sixJRecouplingHom]
  rcases not_and_or.mp h with h₁ | h
  · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ε δ h₁]
  rcases not_and_or.mp h with h₂ | h
  · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq (ε * δ) ζ h₂]
  rcases not_and_or.mp h with h₃ | h₄
  · simp [clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple hq δ ζ h₃]
  · simp [clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple hq ε (δ * ζ) h₄]

/-- Selection rule for `sixJSymbolSymm`: it vanishes unless all four binary couplings are
admissible Clebsch–Gordan triples. -/
theorem sixJSymbolSymm_eq_zero_of_not_isClebschGordanTriple (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) {a b c d v u : ℕ}
    (h : ¬ (IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d ∧
      IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)) :
    sixJSymbolSymm hq ε δ ζ a b c d v u = 0 := by
  rw [sixJSymbolSymm, sixJRecouplingSymmHom]
  rcases not_and_or.mp h with h₁ | h
  · simp [clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple hq ε δ h₁]
  rcases not_and_or.mp h with h₂ | h
  · simp [clebschGordanWeightProjection_eq_zero_of_not_isClebschGordanTriple hq (ε * δ) ζ h₂]
  rcases not_and_or.mp h with h₃ | h₄
  · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq δ ζ h₃]
  · simp [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ε (δ * ζ) h₄]

/-! ### Coupled normalized `F`-ladder bases -/

/-- Index type for the coupled normalized `F`-ladder basis of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
abbrev ClebschGordanLeftBasisIndex (m n p : ℕ) : Type :=
  Σ i : Fin (min m n + 1),
    Σ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1), Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)

/-- Index type for the coupled normalized `F`-ladder basis of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
abbrev ClebschGordanRightBasisIndex (m n p : ℕ) : Type :=
  Σ r : Fin (min n p + 1),
    Σ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1), Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)

/-- The coupled normalized `F`-ladder basis of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
def clebschGordanLeftBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Basis (ClebschGordanLeftBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q) (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ)) :=
  (Pi.basis fun i : Fin (min m n + 1) =>
    Pi.basis fun j : Fin (min (m + n - 2 * (i : ℕ)) p + 1) =>
      basis q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)).map
    ((clebschGordanLeftEquiv hq).restrictScalars ℂ)

/-- The coupled normalized `F`-ladder basis of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
def clebschGordanRightBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Basis (ClebschGordanRightBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ))) :=
  (Pi.basis fun r : Fin (min n p + 1) =>
    Pi.basis fun s : Fin (min m (n + p - 2 * (r : ℕ)) + 1) =>
      basis q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))).map
    ((clebschGordanRightEquiv hq).restrictScalars ℂ)

/-- Explicit formula for the left-coupled normalized `F`-ladder basis elements. -/
@[simp] theorem clebschGordanLeftBasis_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    clebschGordanLeftBasis hq m n p ε δ ζ ⟨i, j, k⟩ =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanInclusion hq j (vec q _ ((ε * δ) * ζ) k)) := by
  simp [clebschGordanLeftBasis, Pi.basis_apply, vec_coe]

/-- Explicit formula for the right-coupled normalized `F`-ladder basis elements. -/
@[simp] theorem clebschGordanRightBasis_apply (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    clebschGordanRightBasis hq m n p ε δ ζ ⟨r, s, l⟩ =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
        (clebschGordanInclusion hq s (vec q _ (ε * (δ * ζ)) l)) := by
  simp [clebschGordanRightBasis, Pi.basis_apply, vec_coe]

private theorem toMatrix_coupledBasis_apply (hq : IsGenericQuantumParameter q)
    {I₁ : Type} [Fintype I₁] [DecidableEq I₁] {J₁ : I₁ → Type} [∀ i, Fintype (J₁ i)]
    [∀ i, DecidableEq (J₁ i)] {w₁ : (i : I₁) → J₁ i → ℕ} {η₁ : ℤˣ}
    {I₂ : Type} [Fintype I₂] {J₂ : I₂ → Type} [∀ r, Fintype (J₂ r)]
    {w₂ : (r : I₂) → J₂ r → ℕ} {η₂ : ℤˣ}
    {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [Module (UqSl2 q) M₁]
    [IsScalarTower ℂ (UqSl2 q) M₁] [AddCommGroup M₂] [Module ℂ M₂] [Module (UqSl2 q) M₂]
    [IsScalarTower ℂ (UqSl2 q) M₂]
    (e₁ : (∀ i, ∀ j, LadderModule q (w₁ i j) η₁) ≃ₗ[UqSl2 q] M₁)
    (e₂ : (∀ r, ∀ s, LadderModule q (w₂ r s) η₂) ≃ₗ[UqSl2 q] M₂)
    (f : M₁ →ₗ[UqSl2 q] M₂)
    (r : I₂) (s : J₂ r) (l : Fin (w₂ r s + 1))
    (i : I₁) (j : J₁ i) (k : Fin (w₁ i j + 1)) :
    LinearMap.toMatrix
        ((Pi.basis fun i => Pi.basis fun j => basis q (w₁ i j) η₁).map (e₁.restrictScalars ℂ))
        ((Pi.basis fun r => Pi.basis fun s => basis q (w₂ r s) η₂).map (e₂.restrictScalars ℂ))
        (f.restrictScalars ℂ) ⟨r, s, l⟩ ⟨i, j, k⟩ =
      if (l : ℕ) = (k : ℕ) then
        homScalar ((LinearMap.proj s).comp <| (LinearMap.proj r).comp <|
          e₂.symm.toLinearMap.comp <| f.comp <| e₁.toLinearMap.comp <|
            (LinearMap.single _ _ i).comp (LinearMap.single _ _ j))
      else 0 := by
  rw [LinearMap.toMatrix_apply]
  simp only [Basis.map_repr, Basis.map_apply, LinearEquiv.trans_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearMap.restrictScalars_apply, Pi.basis_repr, Pi.basis_apply, ← vec_coe]
  set φ : LadderModule q (w₁ i j) η₁ →ₗ[UqSl2 q] LadderModule q (w₂ r s) η₂ :=
    (LinearMap.proj s).comp <| (LinearMap.proj r).comp <|
      e₂.symm.toLinearMap.comp <| f.comp <| e₁.toLinearMap.comp <|
        (LinearMap.single _ _ i).comp (LinearMap.single _ _ j)
  have hφ : e₂.symm (f (e₁ (Pi.single i (Pi.single j (vec q (w₁ i j) η₁ k))))) r s =
      φ (vec q (w₁ i j) η₁ k) := by simp [φ]
  rw [hφ, apply_vec_eq_homScalar_smul hq φ, map_smul, Finsupp.smul_apply, basis_repr_vec,
    smul_eq_mul]
  norm_cast; simp [mul_ite]

/-- Matrix of the coproduct tensor associator in the coupled normalized `F`-ladder bases: entries
are block-diagonal in total highest weight and `F`-ladder index, with diagonal entries given by
`sixJSymbol`. -/
theorem toMatrix_assoc_clebschGordanBasis (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanLeftBasis hq m n p ε δ ζ)
        (clebschGordanRightBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).toLinearMap.restrictScalars ℂ) ⟨r, s, l⟩ ⟨i, j, k⟩ =
      if m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) ∧
          (l : ℕ) = (k : ℕ) then
        sixJSymbol hq ε δ ζ m n p (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ))
          (m + n - 2 * (i : ℕ)) (n + p - 2 * (r : ℕ))
      else 0 := by
  rw [clebschGordanLeftBasis, clebschGordanRightBasis, toMatrix_coupledBasis_apply hq]
  have hφ : ((LinearMap.proj s).comp <| (LinearMap.proj r).comp <|
      (clebschGordanRightEquiv hq).symm.toLinearMap.comp <|
        (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
            (LadderModule q p ζ)).toLinearMap.comp <|
          (clebschGordanLeftEquiv hq).toLinearMap.comp <|
            (LinearMap.single _ _ i).comp (LinearMap.single _ _ j)) =
      (clebschGordanProjection hq s).comp
        ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanProjection hq r)).comp
          ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
              (LadderModule q p ζ)).toLinearMap.comp
            ((tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id).comp
              (clebschGordanInclusion hq j)))) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
      LinearMap.single_apply, ← clebschGordanRightEquiv_recoupling, LinearEquiv.symm_apply_apply]
    exact clebschGordanRecouplingEquiv_single_apply hq i j r s x
  rw [hφ]
  by_cases hd : m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) = m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)
  · rw [sixJSymbol, sixJRecouplingHom,
      clebschGordanWeightProjection_congr_right hq m ε (n + p - 2 * (r : ℕ)) (δ * ζ) hd]
    simp [hd, LinearMap.comp_assoc, homScalar_comp hq]
  · simp [hd, homScalar_eq_zero_of_ne hq (.inl (Ne.symm hd))]

/-- Matrix of `assoc.symm` in the coupled normalized `F`-ladder bases: entries are block-diagonal
in total highest weight and `F`-ladder index, with diagonal entries given by `sixJSymbolSymm`. -/
theorem toMatrix_assoc_symm_clebschGordanBasis (hq : IsGenericQuantumParameter q)
    {m n p : ℕ} (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanRightBasis hq m n p ε δ ζ)
        (clebschGordanLeftBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).symm.toLinearMap.restrictScalars ℂ) ⟨i, j, k⟩ ⟨r, s, l⟩ =
      if m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) ∧
          (k : ℕ) = (l : ℕ) then
        sixJSymbolSymm hq ε δ ζ m n p (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ))
          (n + p - 2 * (r : ℕ)) (m + n - 2 * (i : ℕ))
      else 0 := by
  rw [clebschGordanRightBasis, clebschGordanLeftBasis, toMatrix_coupledBasis_apply hq]
  have hφ : ((LinearMap.proj j).comp <| (LinearMap.proj i).comp <|
      (clebschGordanLeftEquiv hq).symm.toLinearMap.comp <|
        (assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
            (LadderModule q p ζ)).symm.toLinearMap.comp <|
          (clebschGordanRightEquiv hq).toLinearMap.comp <|
            (LinearMap.single _ _ r).comp (LinearMap.single _ _ s)) =
      (clebschGordanProjection hq j).comp
        ((tensorMap ℂ (UqSl2 q) (clebschGordanProjection hq i) LinearMap.id).comp
          ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
              (LadderModule q p ζ)).symm.toLinearMap.comp
            ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)).comp
              (clebschGordanInclusion hq s)))) := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
      LinearMap.single_apply, ← clebschGordanLeftEquiv_recoupling_symm,
      LinearEquiv.symm_apply_apply]
    exact clebschGordanRecouplingEquiv_symm_single_apply hq i j r s x
  rw [hφ]
  by_cases hd : m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) = m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)
  · rw [sixJSymbolSymm, sixJRecouplingSymmHom,
      clebschGordanWeightProjection_congr_right hq (m + n - 2 * (i : ℕ)) (ε * δ) p ζ hd]
    simp [hd, LinearMap.comp_assoc, homScalar_comp hq]
  · simp [hd, homScalar_eq_zero_of_ne hq (.inl (Ne.symm hd))]

/-! ### Operator reassociation and fixed-total-weight `6j` matrices -/

/-- Operator reassociation of a left-coupled binary Clebsch–Gordan channel into a linear
combination of right-coupled channels weighted by `sixJSymbol`. -/
theorem assoc_comp_clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u : ℕ) :
    (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap.comp
      ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
        (clebschGordanWeightInclusion hq u (ε * δ) c ζ d)) =
      ∑ v ∈ Finset.range (b + c + 1),
        sixJSymbol hq ε δ ζ a b c d u v •
          ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
            ((clebschGordanWeightInclusion hq a ε v (δ * ζ) d).comp
              (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap)) := by
  set L := (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
      (LadderModule q c ζ)).toLinearMap.comp
    ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
      (clebschGordanWeightInclusion hq u (ε * δ) c ζ d))
  have hid : (LinearMap.id : Tensor ℂ (UqSl2 q) (LadderModule q a ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)) →ₗ[UqSl2 q] _) =
      ∑ v ∈ Finset.range (b + c + 1),
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)) := by
    rw [← tensorMap_id, ← sum_clebschGordanWeightInclusion_comp_projection hq b δ c ζ,
      tensorMap_sum_right]
    exact Finset.sum_congr rfl fun v _ => by simp
  conv_lhs => rw [← LinearMap.id_comp L, hid, LinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [LinearMap.comp_assoc,
    eq_homScalar_weightProjection_smul_weightInclusion hq ε (δ * ζ) (mul_assoc ε δ ζ)
      ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)).comp L),
    LinearMap.comp_smul]
  simp only [L, sixJSymbol, sixJRecouplingHom]

/-- Operator reassociation of a right-coupled binary Clebsch–Gordan channel under `assoc.symm` into
a linear combination of left-coupled channels weighted by `sixJSymbolSymm`. -/
theorem assoc_symm_comp_clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d v : ℕ) :
    (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).symm.toLinearMap.comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
        (clebschGordanWeightInclusion hq a ε v (δ * ζ) d)) =
      ∑ u ∈ Finset.range (a + b + 1),
        sixJSymbolSymm hq ε δ ζ a b c d v u •
          ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
            ((clebschGordanWeightInclusion hq u (ε * δ) c ζ d).comp
              (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap)) := by
  set R := (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
      (LadderModule q c ζ)).symm.toLinearMap.comp
    ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
      (clebschGordanWeightInclusion hq a ε v (δ * ζ) d))
  have hid : (LinearMap.id : Tensor ℂ (UqSl2 q)
      (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
      (LadderModule q c ζ) →ₗ[UqSl2 q] _) =
      ∑ u ∈ Finset.range (a + b + 1),
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u) LinearMap.id) := by
    rw [← tensorMap_id, ← sum_clebschGordanWeightInclusion_comp_projection hq a ε b δ,
      tensorMap_sum_left]
    exact Finset.sum_congr rfl fun u _ => by simp
  conv_lhs => rw [← LinearMap.id_comp R, hid, LinearMap.finsetSum_comp]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.comp_assoc,
    eq_homScalar_weightProjection_smul_weightInclusion hq (ε * δ) ζ (mul_assoc ε δ ζ).symm
      ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u) LinearMap.id).comp R),
    LinearMap.comp_smul]
  simp only [R, sixJSymbolSymm, sixJRecouplingSymmHom]

/-- Vector form of reassociation on normalized `F`-ladder vectors (`k : ℤ`) in weight
coordinates. -/
theorem assoc_clebschGordanWeightInclusion_vec (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u : ℕ) (k : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) (LadderModule q c ζ)
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d (vec q d ((ε * δ) * ζ) k))) =
      ∑ v ∈ Finset.range (b + c + 1),
        sixJSymbol hq ε δ ζ a b c d u v •
          tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)
            (clebschGordanWeightInclusion hq a ε v (δ * ζ) d (vec q d (ε * (δ * ζ)) k)) := by
  simpa [LinearMap.sum_apply] using congrArg (fun f => f (vec q d ((ε * δ) * ζ) k))
    (assoc_comp_clebschGordanWeightInclusion hq ε δ ζ a b c d u)

/-- Left orthogonality relation between `sixJSymbolSymm` and `sixJSymbol`. -/
theorem sum_sixJSymbolSymm_mul_sixJSymbol (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u u' : ℕ) :
    ∑ v ∈ Finset.range (b + c + 1),
        sixJSymbolSymm hq ε δ ζ a b c d v u' * sixJSymbol hq ε δ ζ a b c d u v =
      if u = u' ∧ IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d then 1 else 0 := by
  set P := (clebschGordanWeightProjection hq u' (ε * δ) c ζ d).comp
    ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u') LinearMap.id).comp
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).symm.toLinearMap)
  trans homScalar (P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap.comp
      ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
        (clebschGordanWeightInclusion hq u (ε * δ) c ζ d))))
  · symm
    rw [assoc_comp_clebschGordanWeightInclusion hq ε δ ζ a b c d u,
      LinearMap.comp_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [LinearMap.comp_smul, map_smul, smul_eq_mul]
    have hcomp : P.comp ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (clebschGordanWeightInclusion hq b δ c ζ v)).comp
        ((clebschGordanWeightInclusion hq a ε v (δ * ζ) d).comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap)) =
        (sixJRecouplingSymmHom hq ε δ ζ a b c d v u').comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap := by
      simp only [P, sixJRecouplingSymmHom, LinearMap.comp_assoc]
    rw [hcomp, homScalar_comp hq, homScalar_congr, mul_one, ← sixJSymbolSymm, mul_comm]
  · have hlhs : P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap.comp
        ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d))) =
        (clebschGordanWeightProjection hq u' (ε * δ) c ζ d).comp
          ((tensorMap ℂ (UqSl2 q)
              ((clebschGordanWeightProjection hq a ε b δ u').comp
                (clebschGordanWeightInclusion hq a ε b δ u)) LinearMap.id).comp
            (clebschGordanWeightInclusion hq u (ε * δ) c ζ d)) := by ext x; simp [P]
    rw [hlhs]
    by_cases h₁ : u' = u ∧ IsClebschGordanTriple a b u'
    · rcases h₁ with ⟨rfl, hab⟩
      simp only [clebschGordanWeightProjection_comp_inclusion_self, hab, tensorMap_id,
        LinearMap.id_comp, true_and]
      by_cases h₂ : IsClebschGordanTriple u' c d <;>
        simp [clebschGordanWeightProjection_comp_inclusion, h₂]
    · simp [clebschGordanWeightProjection_comp_inclusion, h₁,
        show ¬(u = u' ∧ IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d) by
          rintro ⟨rfl, hab, _⟩; exact h₁ ⟨rfl, hab⟩]

/-- Right orthogonality relation between `sixJSymbol` and `sixJSymbolSymm`. -/
theorem sum_sixJSymbol_mul_sixJSymbolSymm (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d v v' : ℕ) :
    ∑ u ∈ Finset.range (a + b + 1),
        sixJSymbol hq ε δ ζ a b c d u v' * sixJSymbolSymm hq ε δ ζ a b c d v u =
      if v = v' ∧ IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d then 1 else 0 := by
  set P := (clebschGordanWeightProjection hq a ε v' (δ * ζ) d).comp
    ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v')).comp
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap)
  trans homScalar (P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).symm.toLinearMap.comp
      ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
        (clebschGordanWeightInclusion hq a ε v (δ * ζ) d))))
  · symm
    rw [assoc_symm_comp_clebschGordanWeightInclusion hq ε δ ζ a b c d v,
      LinearMap.comp_finsetSum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearMap.comp_smul, map_smul, smul_eq_mul]
    have hcomp : P.comp ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u)
          LinearMap.id).comp
        ((clebschGordanWeightInclusion hq u (ε * δ) c ζ d).comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap)) =
        (sixJRecouplingHom hq ε δ ζ a b c d u v').comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap := by
      simp only [P, sixJRecouplingHom, LinearMap.comp_assoc]
    rw [hcomp, homScalar_comp hq, homScalar_congr, mul_one, ← sixJSymbol, mul_comm]
  · have hlhs : P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).symm.toLinearMap.comp
        ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
          (clebschGordanWeightInclusion hq a ε v (δ * ζ) d))) =
        (clebschGordanWeightProjection hq a ε v' (δ * ζ) d).comp
          ((tensorMap ℂ (UqSl2 q) LinearMap.id
              ((clebschGordanWeightProjection hq b δ c ζ v').comp
                (clebschGordanWeightInclusion hq b δ c ζ v))).comp
            (clebschGordanWeightInclusion hq a ε v (δ * ζ) d)) := by ext x; simp [P]
    rw [hlhs]
    by_cases h₁ : v' = v ∧ IsClebschGordanTriple b c v'
    · rcases h₁ with ⟨rfl, hbc⟩
      simp only [clebschGordanWeightProjection_comp_inclusion_self, hbc, tensorMap_id,
        LinearMap.id_comp, true_and]
      by_cases h₂ : IsClebschGordanTriple a v' d <;>
        simp [clebschGordanWeightProjection_comp_inclusion, h₂]
    · simp [clebschGordanWeightProjection_comp_inclusion, h₁,
        show ¬(v = v' ∧ IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d) by
          rintro ⟨rfl, hbc, _⟩; exact h₁ ⟨rfl, hbc⟩]

/-- Admissible left intermediate weights `u` for `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` at total weight `d`. -/
abbrev SixJLeftIndex (a b c d : ℕ) : Type :=
  { u : ℕ // IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d }

/-- Admissible right intermediate weights `v` for `L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` at total weight `d`. -/
abbrev SixJRightIndex (a b c d : ℕ) : Type :=
  { v : ℕ // IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d }

instance (a b c d : ℕ) : Fintype (SixJLeftIndex a b c d) :=
  Fintype.subtype ((Finset.range (a + b + 1)).filter fun u =>
    IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d)
    fun _ => mem_filter_range_isClebschGordanTriple_and

instance (a b c d : ℕ) : Fintype (SixJRightIndex a b c d) :=
  Fintype.subtype ((Finset.range (b + c + 1)).filter fun v =>
    IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)
    fun _ => mem_filter_range_isClebschGordanTriple_and

/-- Summing over `SixJLeftIndex a b c d` agrees with summing over `Finset.range (a + b + 1)` for
any function vanishing outside admissible left intermediate weights. -/
theorem sum_sixJLeftIndex_eq_sum_range {M : Type*} [AddCommMonoid M] (a b c d : ℕ) (f : ℕ → M)
    (hf : ∀ u, ¬ (IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d) → f u = 0) :
    (∑ u : SixJLeftIndex a b c d, f u.1) = ∑ u ∈ Finset.range (a + b + 1), f u := by
  rw [← Finset.sum_subtype _ (fun _ => mem_filter_range_isClebschGordanTriple_and) f,
    Finset.sum_filter_of_ne fun u _ => Not.imp_symm (hf u)]

/-- Summing over `SixJRightIndex a b c d` agrees with summing over `Finset.range (b + c + 1)` for
any function vanishing outside admissible right intermediate weights. -/
theorem sum_sixJRightIndex_eq_sum_range {M : Type*} [AddCommMonoid M] (a b c d : ℕ) (f : ℕ → M)
    (hf : ∀ v, ¬ (IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d) → f v = 0) :
    (∑ v : SixJRightIndex a b c d, f v.1) = ∑ v ∈ Finset.range (b + c + 1), f v := by
  rw [← Finset.sum_subtype _ (fun _ => mem_filter_range_isClebschGordanTriple_and) f,
    Finset.sum_filter_of_ne fun v _ => Not.imp_symm (hf v)]

/-- The fixed-total-weight quantum `6j` change-of-decomposition matrix, with rows indexed by right
intermediate weights `v` and columns indexed by left intermediate weights `u`. -/
def sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    Matrix (SixJRightIndex a b c d) (SixJLeftIndex a b c d) ℂ :=
  Matrix.of fun v u => sixJSymbol hq ε δ ζ a b c d u.1 v.1

/-- The inverse fixed-total-weight quantum `6j` change-of-decomposition matrix. -/
def sixJMatrixSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    Matrix (SixJLeftIndex a b c d) (SixJRightIndex a b c d) ℂ :=
  Matrix.of fun u v => sixJSymbolSymm hq ε δ ζ a b c d v.1 u.1

/-- Entries of `sixJMatrix` are given by `sixJSymbol`. -/
@[simp] theorem sixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ} (v : SixJRightIndex a b c d) (u : SixJLeftIndex a b c d) :
    sixJMatrix hq ε δ ζ a b c d v u = sixJSymbol hq ε δ ζ a b c d u.1 v.1 := (rfl)

/-- Entries of `sixJMatrixSymm` are given by `sixJSymbolSymm`. -/
@[simp] theorem sixJMatrixSymm_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ} (u : SixJLeftIndex a b c d) (v : SixJRightIndex a b c d) :
    sixJMatrixSymm hq ε δ ζ a b c d u v = sixJSymbolSymm hq ε δ ζ a b c d v.1 u.1 := (rfl)

/-- `sixJMatrixSymm` is a left inverse of `sixJMatrix`. -/
@[simp] theorem sixJMatrixSymm_mul_sixJMatrix (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    sixJMatrixSymm hq ε δ ζ a b c d * sixJMatrix hq ε δ ζ a b c d = 1 := by
  ext u' u
  have hsum := sum_sixJRightIndex_eq_sum_range a b c d
    (fun v => sixJSymbolSymm hq ε δ ζ a b c d v u'.1 * sixJSymbol hq ε δ ζ a b c d u.1 v)
    fun v hv => by
      rw [sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq ε δ ζ
        (fun h => hv ⟨h.2.2.1, h.2.2.2⟩), mul_zero]
  rw [Matrix.mul_apply, Matrix.one_apply, sixJMatrixSymm, sixJMatrix]
  simp only [Matrix.of_apply, hsum, sum_sixJSymbolSymm_mul_sixJSymbol]
  rcases eq_or_ne u' u with rfl | huu
  · simp [u'.2.1, u'.2.2]
  · simp [huu, show u.1 ≠ u'.1 from fun h => huu (Subtype.ext h.symm)]

/-- `sixJMatrixSymm` is a right inverse of `sixJMatrix`. -/
@[simp] theorem sixJMatrix_mul_sixJMatrixSymm (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    sixJMatrix hq ε δ ζ a b c d * sixJMatrixSymm hq ε δ ζ a b c d = 1 := by
  ext v' v
  have hsum := sum_sixJLeftIndex_eq_sum_range a b c d
    (fun u => sixJSymbol hq ε δ ζ a b c d u v'.1 * sixJSymbolSymm hq ε δ ζ a b c d v.1 u)
    fun u hu => by
      rw [sixJSymbolSymm_eq_zero_of_not_isClebschGordanTriple hq ε δ ζ
        (fun h => hu ⟨h.1, h.2.1⟩), mul_zero]
  rw [Matrix.mul_apply, Matrix.one_apply, sixJMatrix, sixJMatrixSymm]
  simp only [Matrix.of_apply, hsum, sum_sixJSymbol_mul_sixJSymbolSymm]
  rcases eq_or_ne v' v with rfl | hvv
  · simp [v'.2.1, v'.2.2]
  · simp [hvv, show v.1 ≠ v'.1 from fun h => hvv (Subtype.ext h.symm)]

/-- The numbers of admissible left and right intermediate weights at total weight `d` coincide. -/
theorem card_sixJLeftIndex_eq_card_sixJRightIndex (a b c d : ℕ) :
    Fintype.card (SixJLeftIndex a b c d) = Fintype.card (SixJRightIndex a b c d) := by
  -- Specialize `U_q(sl₂)` to the generic parameter `q = 2` with trivial signs: `sixJMatrix` and
  -- `sixJMatrixSymm` then form a mutually inverse pair of matrices between the `ℂ`-vector spaces on
  -- the two index types, so the resulting `LinearEquiv` equates their `finrank`s and hence the
  -- index cardinalities.
  have : Fact ((2 : ℂ) ≠ 0) := ⟨by norm_num⟩
  have hq2 : IsGenericQuantumParameter (2 : ℂ) :=
    isGenericQuantumParameter_iff.mpr ⟨by norm_num, fun n hn hpow => by
      have hnat : 2 ^ n = 1 := Nat.cast_injective (R := ℂ) (by simpa using hpow)
      have := Nat.pow_le_pow_right (by omega : 0 < 2) hn; omega⟩
  simpa using (LinearEquiv.ofLinearMap
    (Matrix.toLin' (sixJMatrix hq2 1 1 1 a b c d))
    (Matrix.toLin' (sixJMatrixSymm hq2 1 1 1 a b c d))
    (by rw [← Matrix.toLin'_mul, sixJMatrix_mul_sixJMatrixSymm, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, sixJMatrixSymm_mul_sixJMatrix, Matrix.toLin'_one])).finrank_eq

/-! ### Explicit `2 × 2` spin-`1/2` evaluation on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at `d = 1` -/

private def tripleRightCoord (q : ℂ) [Fact (q ≠ 0)] (ε δ ζ : ℤˣ) (i j k : Fin 2) :
    Tensor ℂ (UqSl2 q) (LadderModule q 1 ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ)) →ₗ[ℂ] ℂ :=
  ((Finsupp.lapply (i, (j, k))).comp
    ((basis q 1 ε).tensorProduct ((basis q 1 δ).tensorProduct (basis q 1 ζ))).repr.toLinearMap).comp
    (((TensorProduct.congr (LinearEquiv.refl ℂ _)
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ))).toLinearMap).comp
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 ε) _).toLinearMap)

private theorem tripleRightCoord_tmul (ε δ ζ : ℤˣ) (i j k : Fin 2) (a b c : ℤ) :
    tripleRightCoord q ε δ ζ i j k
        (tmul ℂ (UqSl2 q) (vec q 1 ε a) (tmul ℂ (UqSl2 q) (vec q 1 δ b) (vec q 1 ζ c))) =
      (if (i : ℤ) = a then 1 else 0) *
        ((if (j : ℤ) = b then 1 else 0) * (if (k : ℤ) = c then 1 else 0)) := by
  simp only [tripleRightCoord, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, tensorEquiv_tmul,
    Basis.tensorProduct_repr_tmul_apply, basis_repr_vec, smul_eq_mul]
  split_ifs <;> simp_all

private def rightVecZero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :=
  tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q 1 ε →ₗ[UqSl2 q] _)
    (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1)))
    (clebschGordanInclusion hq (0 : Fin (min 1 0 + 1)) (vec q 1 (ε * (δ * ζ)) 0))

private def rightVecTwo (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :=
  tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q 1 ε →ₗ[UqSl2 q] _)
    (clebschGordanInclusion hq (0 : Fin (min 1 1 + 1)))
    (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 2 + 1)) (vec q 1 (ε * (δ * ζ)) 0))

private theorem assoc_spinHalf_vec_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (u : ℕ) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ)
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq 1 ε 1 δ u) LinearMap.id
          (clebschGordanWeightInclusion hq u (ε * δ) 1 ζ 1 (vec q 1 ((ε * δ) * ζ) 0))) =
      sixJSymbol hq ε δ ζ 1 1 1 1 u 0 • rightVecZero hq ε δ ζ +
        sixJSymbol hq ε δ ζ 1 1 1 1 u 2 • rightVecTwo hq ε δ ζ := by
  rw [assoc_clebschGordanWeightInclusion_vec hq ε δ ζ 1 1 1 1 u 0,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hv1 : sixJSymbol hq ε δ ζ 1 1 1 1 u 1 = 0 :=
    sixJSymbol_eq_zero_of_not_isClebschGordanTriple hq ε δ ζ fun ⟨_, _, h, _⟩ => by
      have := h.even_add_sub; simp at this
  rw [hv1, zero_smul, add_zero]
  have h01 := clebschGordanWeightInclusion_sub_two_mul hq 1 δ 1 ζ ⟨1, by omega⟩
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 0 (δ * ζ) 0
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 δ 1 ζ 0
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 2 (δ * ζ) ⟨1, by omega⟩
  simp only [Fin.val_zero] at h00 h20
  simp only [rightVecZero, rightVecTwo]
  dsimp only at h01 h00 h20 h21 ⊢; rw [h01, h00, h20, h21]

private theorem clebschGordanInclusion_one_vec_zero (hq : IsGenericQuantumParameter q)
    {m n : ℕ} (ε δ : ℤˣ) (h : 1 < min m n + 1) :
    clebschGordanInclusion hq (⟨1, h⟩ : Fin (min m n + 1)) (vec q (m + n - 2) (ε * δ) 0) =
      tmul ℂ (UqSl2 q) (vec q m ε 0) (vec q n δ 1) +
        (-(δ : ℂ) * q ^ (m : ℤ) * quantumInteger q n / quantumInteger q m) •
          tmul ℂ (UqSl2 q) (vec q m ε 1) (vec q n δ 0) := by
  refine (clebschGordanInclusion_vec_zero hq ⟨1, h⟩).trans ?_
  dsimp only
  rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
  simp [clebschGordanCoeff_succ]

private theorem spinHalfAlt_vec_zero (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1)) (vec q 0 (ε₁ * ε₂) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) +
        (-(ε₂ : ℂ) * q) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) := by
  simpa [quantumInteger_one hq.sub_inv_ne_zero] using
    clebschGordanInclusion_one_vec_zero hq ε₁ ε₂ (m := 1) (n := 1) (by omega)

private theorem spinHalfSym_vec_one (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (0 : Fin (min 1 1 + 1)) (vec q 2 (ε₁ * ε₂) 1) =
      ((ε₂ : ℂ) * q⁻¹) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) +
        tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) := by
  refine (clebschGordanInclusion_vec (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq 0 1).trans ?_
  rw [Finset.prod_range_one, clebschGordanVector_def, Fin.val_zero, Finset.sum_range_one]
  simp [quantumInteger_one hq.sub_inv_ne_zero, f_smul_tmul, f_smul_vec, kInv_smul_vec]

private theorem rightVecZero_coords (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord q ε δ ζ 0 0 1 (rightVecZero hq ε δ ζ) = 1 ∧
      tripleRightCoord q ε δ ζ 1 0 0 (rightVecZero hq ε δ ζ) = 0 := by
  rw [rightVecZero, clebschGordanInclusion_zero_vec_zero, tensorMap_tmul, LinearMap.id_apply,
    spinHalfAlt_vec_zero]
  simp only [tmul_add, tmul_smul, map_add, map_smul, tripleRightCoord_tmul, smul_eq_mul]
  norm_num

private theorem rightVecTwo_coords (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord q ε δ ζ 0 0 1 (rightVecTwo hq ε δ ζ) = 1 ∧
      tripleRightCoord q ε δ ζ 1 0 0 (rightVecTwo hq ε δ ζ) =
        -(δ : ℂ) * (ζ : ℂ) * q * quantumInteger q 2 := by
  have hin : clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 2 + 1))
      (vec q 1 (ε * (δ * ζ)) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (vec q 2 (δ * ζ) 1) +
        (-(δ : ℂ) * (ζ : ℂ) * q * quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (vec q 2 (δ * ζ) 0) := by
    simpa [quantumInteger_one hq.sub_inv_ne_zero, mul_assoc] using
      clebschGordanInclusion_one_vec_zero hq ε (δ * ζ) (m := 1) (n := 2) (by omega)
  simp only [rightVecTwo, hin, map_add, LinearMap.map_smul_of_tower, tensorMap_tmul,
    LinearMap.id_apply]
  rw [spinHalfSym_vec_one, clebschGordanInclusion_zero_vec_zero]
  simp only [tmul_add, tmul_smul, map_add, map_smul, tripleRightCoord_tmul, smul_eq_mul]
  constructor <;> norm_num

private theorem spinHalf_zero_eq (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0)) +
        (-(δ : ℂ) * q) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) =
      sixJSymbol hq ε δ ζ 1 1 1 1 0 0 • rightVecZero hq ε δ ζ +
        sixJSymbol hq ε δ ζ 1 1 1 1 0 2 • rightVecTwo hq ε δ ζ := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 0
  have h01 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ ⟨1, by omega⟩
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 0 (ε * δ) 1 ζ 0
  simp only [Fin.val_zero] at h00
  dsimp only at h01 h00
  rw [h01, h00, clebschGordanInclusion_zero_vec_zero, tensorMap_tmul, LinearMap.id_apply,
    spinHalfAlt_vec_zero] at hexp
  simpa only [add_tmul, ← smul_tmul', map_add, LinearMapClass.map_smul_of_tower (S := UqSl2 q),
    assoc_tmul] using hexp

private theorem spinHalf_two_eq (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          (((δ : ℂ) * q⁻¹) •
              tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) +
            tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0))) =
      sixJSymbol hq ε δ ζ 1 1 1 1 2 0 • rightVecZero hq ε δ ζ +
        sixJSymbol hq ε δ ζ 1 1 1 1 2 2 • rightVecTwo hq ε δ ζ := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 2
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ 0
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 2 (ε * δ) 1 ζ ⟨1, by omega⟩
  have hin : clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 2 1 + 1))
      (vec q 1 ((ε * δ) * ζ) 0) =
      tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 0) (vec q 1 ζ 1) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 1) (vec q 1 ζ 0) := by
    simpa [quantumInteger_one hq.sub_inv_ne_zero] using
      clebschGordanInclusion_one_vec_zero hq (ε * δ) ζ (m := 2) (n := 1) (by omega)
  simp only [Fin.val_zero] at h20
  dsimp only at h20 h21
  simp only [h20, h21, hin, map_add, LinearMap.map_smul_of_tower, tensorMap_tmul,
    LinearMap.id_apply] at hexp
  rw [clebschGordanInclusion_zero_vec_zero, spinHalfSym_vec_one] at hexp
  simpa only [add_tmul, ← smul_tmul', map_add, LinearMapClass.map_smul_of_tower (S := UqSl2 q),
    assoc_tmul] using hexp

/-- Entry `(u = 0, v = 2)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_zero_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 0 2 = (ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  have hc := congrArg (tripleRightCoord q ε δ ζ 1 0 0) (spinHalf_zero_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).2,
    (rightVecTwo_coords hq ε δ ζ).2, tripleRightCoord_tmul, smul_eq_mul] at hc
  norm_num at hc
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  have hζ2 : (ζ : ℂ) * (ζ : ℂ) = 1 := by rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num
  rw [eq_mul_inv_iff_mul_eq₀ hq2]
  apply mul_left_cancel₀ (mul_ne_zero
    (mul_ne_zero (Int.cast_ne_zero.mpr δ.ne_zero) (Int.cast_ne_zero.mpr ζ.ne_zero)) hq.ne_zero)
  linear_combination -hc - (δ : ℂ) * q * hζ2

/-- Entry `(u = 0, v = 0)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_zero_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 0 0 = -(ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  have hc := congrArg (tripleRightCoord q ε δ ζ 0 0 1) (spinHalf_zero_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).1,
    (rightVecTwo_coords hq ε δ ζ).1, tripleRightCoord_tmul,
    sixJSymbol_one_one_one_zero_two hq ε δ ζ, smul_eq_mul] at hc
  norm_num at hc; linear_combination -hc

/-- Entry `(u = 2, v = 2)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_two_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 2 2 = ((quantumInteger q 2)⁻¹) ^ 2 := by
  have hc := congrArg (tripleRightCoord q ε δ ζ 1 0 0) (spinHalf_two_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).2,
    (rightVecTwo_coords hq ε δ ζ).2, tripleRightCoord_tmul, smul_eq_mul] at hc
  norm_num at hc
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  apply mul_left_cancel₀ (mul_ne_zero
    (mul_ne_zero (Int.cast_ne_zero.mpr δ.ne_zero) (Int.cast_ne_zero.mpr ζ.ne_zero))
    (mul_ne_zero hq0 hq2))
  field_simp [hq0, hq2] at hc ⊢; linear_combination hc

/-- Entry `(u = 2, v = 0)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_two_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 2 0 = 1 - ((quantumInteger q 2)⁻¹) ^ 2 := by
  have hc := congrArg (tripleRightCoord q ε δ ζ 0 0 1) (spinHalf_two_eq hq ε δ ζ)
  simp only [map_add, map_smul, (rightVecZero_coords hq ε δ ζ).1,
    (rightVecTwo_coords hq ε δ ζ).1, tripleRightCoord_tmul,
    sixJSymbol_one_one_one_two_two hq ε δ ζ, smul_eq_mul] at hc
  norm_num at hc; linear_combination -hc

end TauCeti.UqSl2
