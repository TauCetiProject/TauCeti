/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.LinearMap.BigOperators
public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Channel
public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Weight

import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Quantum `6j` symbols and change-of-decomposition matrices

Building on `ClebschGordan.Channel` and `ClebschGordan.Weight`, this file defines the weight-indexed
quantum `6j` change-of-decomposition symbols and square fixed-total-weight `6j` matrices on triple
tensor products of signed `U_q(sl₂)` ladder modules, proves operator reassociation and two-sided
invertibility, and evaluates all four `2 × 2` spin-`1/2` entries on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ`.

## Main definitions

* `TauCeti.UqSl2.sixJSymbol`, `TauCeti.UqSl2.sixJSymbolSymm`: quantum `6j` change-of-decomposition
  scalars and their inverses in the normalized `α₀ = 1` / `F`-ladder convention.
* `TauCeti.UqSl2.sixJMatrix`, `TauCeti.UqSl2.sixJMatrixSymm`: fixed-total-weight `6j` matrices.

## Main results

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
        hom_eq_zero_of_ne_left hq hne.symm ((clebschGordanWeightProjection hq a ε b δ d').comp f),
        LinearMap.comp_zero]
    · exact fun h => (h hd).elim
  · have hnot : ¬ IsClebschGordanTriple a b d := fun htr =>
      hd (Finset.mem_range.mpr (Nat.lt_succ_of_le htr.le_add))
    rw [clebschGordanWeightInclusion_eq_zero_of_not_isClebschGordanTriple hq ε δ hnot,
      LinearMap.zero_comp, smul_zero]
    refine Finset.sum_eq_zero fun d' hd' => ?_
    have hne : d' ≠ d := fun h => hd (h ▸ hd')
    rw [LinearMap.comp_assoc,
      hom_eq_zero_of_ne_left hq hne.symm ((clebschGordanWeightProjection hq a ε b δ d').comp f),
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

/-- On matching `Fin` channel indices, `sixJSymbol` coincides with `sixJChannel`. -/
theorem sixJSymbol_eq_sixJChannel (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) {a b c d : ℕ}
    (i : Fin (min a b + 1)) (j : Fin (min (a + b - 2 * (i : ℕ)) c + 1))
    (r : Fin (min b c + 1)) (s : Fin (min a (b + c - 2 * (r : ℕ)) + 1))
    (hd₁ : a + b - 2 * (i : ℕ) + c - 2 * (j : ℕ) = d)
    (hd₂ : a + (b + c - 2 * (r : ℕ)) - 2 * (s : ℕ) = d) :
    sixJSymbol hq ε δ ζ a b c d (a + b - 2 * (i : ℕ)) (b + c - 2 * (r : ℕ)) =
      sixJChannel hq ε δ ζ i j r s := by
  rw [sixJSymbol, sixJRecouplingHom,
    clebschGordanWeightProjection_congr_right hq a ε (b + c - 2 * (r : ℕ)) (δ * ζ) hd₂,
    clebschGordanWeightInclusion_congr_right hq (a + b - 2 * (i : ℕ)) (ε * δ) c ζ hd₁,
    clebschGordanWeightProjection_sub_two_mul, clebschGordanWeightProjection_sub_two_mul,
    clebschGordanWeightInclusion_sub_two_mul, clebschGordanWeightInclusion_sub_two_mul,
    LinearMap.comp_assoc, homScalar_comp hq, homScalar_congr, one_mul]
  simp only [← LinearMap.comp_assoc]
  rw [homScalar_comp hq, homScalar_congr, mul_one, homScalar_apply]
  have h := (clebschGordanRecouplingEquiv_single_apply (ε := ε) (δ := δ) (ζ := ζ)
    hq i j r s (vec q _ ((ε * δ) * ζ) 0)).symm
  rw [← clebschGordanRecouplingHom_apply, clebschGordanRecouplingHom_vec] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h]; simp

/-- On matching `Fin` channel indices, `sixJSymbolSymm` coincides with `sixJChannelSymm`. -/
theorem sixJSymbolSymm_eq_sixJChannelSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ} (r : Fin (min b c + 1)) (s : Fin (min a (b + c - 2 * (r : ℕ)) + 1))
    (i : Fin (min a b + 1)) (j : Fin (min (a + b - 2 * (i : ℕ)) c + 1))
    (hd₁ : a + b - 2 * (i : ℕ) + c - 2 * (j : ℕ) = d)
    (hd₂ : a + (b + c - 2 * (r : ℕ)) - 2 * (s : ℕ) = d) :
    sixJSymbolSymm hq ε δ ζ a b c d (b + c - 2 * (r : ℕ)) (a + b - 2 * (i : ℕ)) =
      sixJChannelSymm hq ε δ ζ r s i j := by
  rw [sixJSymbolSymm, sixJRecouplingSymmHom,
    clebschGordanWeightProjection_congr_right hq (a + b - 2 * (i : ℕ)) (ε * δ) c ζ hd₁,
    clebschGordanWeightInclusion_congr_right hq a ε (b + c - 2 * (r : ℕ)) (δ * ζ) hd₂,
    clebschGordanWeightProjection_sub_two_mul, clebschGordanWeightProjection_sub_two_mul,
    clebschGordanWeightInclusion_sub_two_mul, clebschGordanWeightInclusion_sub_two_mul,
    LinearMap.comp_assoc, homScalar_comp hq, homScalar_congr, one_mul]
  simp only [← LinearMap.comp_assoc]
  rw [homScalar_comp hq, homScalar_congr, mul_one, homScalar_apply]
  have h := (clebschGordanRecouplingEquiv_symm_single_apply (ε := ε) (δ := δ) (ζ := ζ)
    hq i j r s (vec q _ (ε * (δ * ζ)) 0)).symm
  rw [← clebschGordanRecouplingSymmHom_apply, clebschGordanRecouplingSymmHom_vec] at h
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h]; simp

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
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun u _ => by
    by_cases hu : IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d <;> simp [hu, hf]

/-- Summing over `SixJRightIndex a b c d` agrees with summing over `Finset.range (b + c + 1)` for
any function vanishing outside admissible right intermediate weights. -/
theorem sum_sixJRightIndex_eq_sum_range {M : Type*} [AddCommMonoid M] (a b c d : ℕ) (f : ℕ → M)
    (hf : ∀ v, ¬ (IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d) → f v = 0) :
    (∑ v : SixJRightIndex a b c d, f v.1) = ∑ v ∈ Finset.range (b + c + 1), f v := by
  rw [← Finset.sum_subtype _ (fun _ => mem_filter_range_isClebschGordanTriple_and) f,
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun v _ => by
    by_cases hv : IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d <;> simp [hv, hf]

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
    (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 0 + 1)) (vec q 1 (ε * (δ * ζ)) 0))

private def rightVecTwo (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :=
  tensorMap ℂ (UqSl2 q) (LinearMap.id : LadderModule q 1 ε →ₗ[UqSl2 q] _)
    (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1)))
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
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 0 (δ * ζ) ⟨0, by omega⟩
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 δ 1 ζ ⟨0, by omega⟩
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 2 (δ * ζ) ⟨1, by omega⟩
  simp only [rightVecZero, rightVecTwo]
  dsimp only at h01 h00 h20 h21; rw [h01, h00, h20, h21]

private theorem spinHalfAlt_vec_zero (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1)) (vec q 0 (ε₁ * ε₂) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) +
        (-(ε₂ : ℂ) * q) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) := by
  refine (clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    ⟨1, by omega⟩).trans ?_
  rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
  simp [clebschGordanCoeff_succ, quantumInteger_one hq.sub_inv_ne_zero]

private theorem spinHalfSym_vec_zero (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1)) (vec q 2 (ε₁ * ε₂) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 0) :=
  (clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    ⟨0, by omega⟩).trans (by simp [clebschGordanVector_def])

private theorem spinHalfSym_vec_one (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1)) (vec q 2 (ε₁ * ε₂) 1) =
      ((ε₂ : ℂ) * q⁻¹) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) +
        tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) := by
  refine (clebschGordanInclusion_vec (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    ⟨0, by omega⟩ 1).trans ?_
  rw [Finset.prod_range_one, clebschGordanVector_def, Finset.sum_range_one]
  simp [quantumInteger_one hq.sub_inv_ne_zero, f_smul_tmul, f_smul_vec, kInv_smul_vec]

private theorem assoc_spinHalf_smul (ε δ ζ : ℤˣ) (c : ℂ) (x) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ) (c • x) =
      c • assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ) x :=
  LinearMapClass.map_smul_of_tower _ _ _

private theorem rightVecZero_coords (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord q ε δ ζ 0 0 1 (rightVecZero hq ε δ ζ) = 1 ∧
      tripleRightCoord q ε δ ζ 1 0 0 (rightVecZero hq ε δ ζ) = 0 := by
  have hin : clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 0 + 1))
      (vec q 1 (ε * (δ * ζ)) 0) = tmul ℂ (UqSl2 q) (vec q 1 ε 0) (vec q 0 (δ * ζ) 0) :=
    (clebschGordanInclusion_vec_zero (m := 1) (n := 0) (ε := ε) (δ := δ * ζ) hq
      ⟨0, by omega⟩).trans (by simp [clebschGordanVector_def])
  rw [rightVecZero, hin, tensorMap_tmul, LinearMap.id_apply, spinHalfAlt_vec_zero]
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
    refine (clebschGordanInclusion_vec_zero (m := 1) (n := 2) (ε := ε) (δ := δ * ζ) hq
      ⟨1, by omega⟩).trans ?_
    rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [clebschGordanCoeff_zero, clebschGordanCoeff_succ, one_smul, Nat.cast_zero,
      sub_zero, Nat.cast_one, sub_self]
    congr 2; norm_num [quantumInteger_one hq.sub_inv_ne_zero]
  simp only [rightVecTwo, hin, map_add, LinearMap.map_smul_of_tower, tensorMap_tmul,
    LinearMap.id_apply]
  rw [spinHalfSym_vec_one, spinHalfSym_vec_zero]
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
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 0 (ε * δ) 1 ζ ⟨0, by omega⟩
  have hin : clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 0 1 + 1))
      (vec q 1 ((ε * δ) * ζ) 0) = tmul ℂ (UqSl2 q) (vec q 0 (ε * δ) 0) (vec q 1 ζ 0) :=
    (clebschGordanInclusion_vec_zero (m := 0) (n := 1) (ε := ε * δ) (δ := ζ) hq
      ⟨0, by omega⟩).trans (by simp [clebschGordanVector_def])
  dsimp only at h01 h00
  rw [h01, h00, hin, tensorMap_tmul, LinearMap.id_apply, spinHalfAlt_vec_zero] at hexp
  simpa only [add_tmul, ← smul_tmul', map_add, assoc_spinHalf_smul, assoc_tmul] using hexp

private theorem spinHalf_two_eq (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          (((δ : ℂ) * q⁻¹) •
              tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) +
            tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0))) =
      sixJSymbol hq ε δ ζ 1 1 1 1 2 0 • rightVecZero hq ε δ ζ +
        sixJSymbol hq ε δ ζ 1 1 1 1 2 2 • rightVecTwo hq ε δ ζ := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 2
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ ⟨0, by omega⟩
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 2 (ε * δ) 1 ζ ⟨1, by omega⟩
  have hin : clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 2 1 + 1))
      (vec q 1 ((ε * δ) * ζ) 0) =
      tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 0) (vec q 1 ζ 1) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 1) (vec q 1 ζ 0) := by
    refine (clebschGordanInclusion_vec_zero (m := 2) (n := 1) (ε := ε * δ) (δ := ζ) hq
      ⟨1, by omega⟩).trans ?_
    rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [clebschGordanCoeff_zero, clebschGordanCoeff_succ, one_smul, Nat.cast_zero,
      sub_zero, Nat.cast_one, sub_self]
    congr 2; norm_num [quantumInteger_one hq.sub_inv_ne_zero]
  dsimp only at h20 h21
  simp only [h20, h21, hin, map_add, LinearMap.map_smul_of_tower, tensorMap_tmul,
    LinearMap.id_apply] at hexp
  rw [spinHalfSym_vec_zero, spinHalfSym_vec_one] at hexp
  simpa only [add_tmul, ← smul_tmul', map_add, assoc_spinHalf_smul, assoc_tmul] using hexp

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
