/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.PowerSum
public import TauCeti.RepresentationTheory.Symmetric.Specht.Ideal.Character
public import TauCeti.RepresentationTheory.Symmetric.Specht.Orthogonality

/-!
# The Schur-Weyl decomposition of the character of a tensor power

The symmetric group `S_d` and the general linear group `GL n k` act on the tensor power
`(kⁿ)^{⊗d}` with commuting actions, and Schur-Weyl duality decomposes it under their product as

`(kⁿ)^{⊗d} ≅ ⊕_{μ ⊢ d} S^μ ⊗ 𝕊^μ(kⁿ)`,

with `S^μ` the Specht module and `𝕊^μ(kⁿ)` the Weyl module. This file proves the shadow of that
decomposition on characters of `GL n k`, over a field `k` of characteristic zero: for every
`g ∈ GL n k`,

`char (kⁿ)^{⊗d} (g) = ∑_{μ ⊢ d} f^μ · char 𝕊^μ(kⁿ) (g)`,

where `f^μ = dim S^μ`, and at `g = 1` the dimension count `n^d = ∑_{μ ⊢ d} f^μ · dim 𝕊^μ(kⁿ)`.
Only the partitions with at most `n` parts contribute, the other Weyl modules being zero
(`TauCeti.weylModuleOfShape_eq_bot_iff`).

The route is through the Specht characters `χ^μ`. The character of the Weyl module
`𝕊_t(kⁿ) = c_t · (kⁿ)^{⊗d}` of a `μ`-tableau `t` is `f^μ / d!` times the pairing of the coefficients
of the Young symmetrizer `c_t` with the class function `σ ↦ tr(σ ∘ g^{⊗d})` of `S_d`
(`TauCeti.YoungTableau.char_weylRep_eq_sum`), and pairing `c_t` with a class function is pairing
`χ^μ` with it up to the factor `f^μ` (`TauCeti.YoungTableau.sum_char_spechtSubrepresentation_smul`).
So

`char 𝕊^μ(kⁿ) (g) = (1 / d!) · ∑_{σ ∈ S_d} χ^μ(σ) · tr(σ ∘ g^{⊗d})`,

which on the diagonal torus is the Frobenius-characteristic expression
`(1 / d!) · ∑_σ χ^μ(σ) · p_{ρ(σ)}(x)` in the power sums. Summing against the degrees `f^μ`, column
orthogonality against the identity class (`TauCeti.sum_finrank_spechtModule_mul_spechtChar`)
leaves only `σ = 1`, whose term is the character of the tensor power.

That the character of `𝕊^μ(kⁿ)` on the torus is the Schur polynomial `s_μ` is the identity
`(1 / d!) · ∑_σ χ^μ(σ) · p_{ρ(σ)} = s_μ` of Frobenius (`TauCeti.sum_spechtChar_smul_psumPart`);
the conclusion is drawn in
`TauCeti/RepresentationTheory/ClassicalGroups/WeylModule/Character.lean`
(`TauCeti.char_weylRepOfShape_diagramOf_diagonal`).

## Main results

* `TauCeti.YoungTableau.char_weylRep_eq_sum_character`: the character of the Weyl module of a
  tableau as the pairing of the Specht character with traces on the tensor power.
* `TauCeti.char_weylRepOfShape_diagramOf_eq_sum_spechtChar`: the same for the Weyl module of a
  partition, with the integer character `χ^μ` of `S_d`.
* `TauCeti.char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar`: **the character of
  `𝕊^μ(kⁿ)` on the diagonal torus is `(1 / d!) · ∑_σ χ^μ(σ) · p_{ρ(σ)}`**.
* `TauCeti.sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf`: **the character of
  `(kⁿ)^{⊗d}` is `∑_{μ ⊢ d} f^μ · char 𝕊^μ(kⁿ)`**.
* `TauCeti.char_weylFDRepOfShape_diagramOf_eq_sum_spechtChar`,
  `TauCeti.char_weylFDRepOfShape_diagramOf_diagonal_eq_sum_spechtChar` and
  `TauCeti.sum_finrank_spechtModule_mul_char_weylFDRepOfShape_diagramOf`: the bundled forms of the
  last three, for `TauCeti.weylFDRepOfShape` and `TauCeti.tensorPowerFDRep`.
* `TauCeti.sum_finrank_spechtModule_mul_finrank_weylModuleOfShape`: **`∑_{μ ⊢ d} f^μ · dim 𝕊^μ(kⁿ)
  = n^d`**.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6, §6.1.
* I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Chapter I, Section 7.
-/

public section

open Module MvPolynomial

universe u

namespace TauCeti

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}

namespace YoungTableau

variable {μ : YoungDiagram}

/-- **The character of a Weyl module through the Specht character.** For a `μ`-tableau `t` with
`d` cells and `g ∈ GL n k`,

`char 𝕊_t(kⁿ) (g) = (1 / d!) · ∑_{σ ∈ S_d} χ^μ(σ) · tr(σ ∘ g^{⊗d})`,

where `χ^μ` is the character of the Specht module `S^μ`. -/
theorem char_weylRep_eq_sum_character (t : YoungTableau μ) (g : GL (Fin n) k) :
    Representation.character (V := (weylModule k n t).toSubmodule) (weylRep k n t) g =
      (μ.card.factorial : k)⁻¹ *
        ∑ σ, (spechtSubrepresentation μ).toRepresentation.character σ •
          LinearMap.trace k _ (permTensorAction k n μ.card σ * tensorPowerRep k n μ.card g) := by
  rw [sum_char_spechtSubrepresentation_smul t _
      fun σ τ => trace_permTensorAction_conj_mul_tensorPowerRep σ τ g,
    char_weylRep_eq_sum]
  simp_rw [youngSymmetrizerOver_coeff, ← smul_eq_mul (algebraMap ℚ k _), algebraMap_smul]
  rw [← algebraMap_smul k, smul_eq_mul, map_natCast,
    finrank_spechtIdeal_eq_spechtSubrepresentation]
  ring

end YoungTableau

/-- Transporting the symmetric group along `Fin m ≃ Fin d` does not change the normalized pairing
of a function on `S_m` with the traces on the tensor power. -/
private theorem factorial_inv_mul_sum_permCongr {m d : ℕ} (h : m = d)
    (χ : Equiv.Perm (Fin m) → ℚ) (g : GL (Fin n) k) :
    (m.factorial : k)⁻¹ * ∑ σ, χ σ •
        LinearMap.trace k _ (permTensorAction k n m σ * tensorPowerRep k n m g) =
      (d.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin d), χ ((finCongr h.symm).permCongr σ) •
        LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) := by
  subst h
  simp only [finCongr_refl, Equiv.permCongr_def, Equiv.refl_symm, Equiv.refl_trans,
    Equiv.trans_refl]

/-- **The character of the Weyl module of a partition through the Specht character.** For a
partition `μ` of `d` and `g ∈ GL n k`,

`char 𝕊^μ(kⁿ) (g) = (1 / d!) · ∑_{σ ∈ S_d} χ^μ(σ) · tr(σ ∘ g^{⊗d})`. -/
theorem char_weylRepOfShape_diagramOf_eq_sum_spechtChar {d : ℕ} (μ : d.Partition)
    (g : GL (Fin n) k) :
    Representation.character (V := (weylModuleOfShape k n (diagramOf μ)).toSubmodule)
        (weylRepOfShape k n (diagramOf μ)) g =
      (d.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin d), spechtChar μ σ •
        LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) := by
  let t := (StandardYoungTableau.rowSuperstandard (diagramOf μ)).toTableau
  rw [← Representation.char_iso (V := (YoungTableau.weylModule k n t).toSubmodule)
      (W := (weylModuleOfShape k n (diagramOf μ)).toSubmodule)
      (YoungTableau.weylRepEquivOfShape k n t),
    YoungTableau.char_weylRep_eq_sum_character,
    factorial_inv_mul_sum_permCongr (card_diagramOf μ)]
  simp_rw [← Int.cast_smul_eq_zsmul ℚ, spechtChar_cast, character_spechtModule_apply]

/-- **The character of the bundled Weyl module of a partition through the Specht character**: the
`FDRep` form of `TauCeti.char_weylRepOfShape_diagramOf_eq_sum_spechtChar`. -/
theorem char_weylFDRepOfShape_diagramOf_eq_sum_spechtChar {d : ℕ} (μ : d.Partition)
    (g : GL (Fin n) k) :
    (weylFDRepOfShape k n (diagramOf μ)).character g =
      (d.factorial : k)⁻¹ * ∑ σ : Equiv.Perm (Fin d), spechtChar μ σ •
        LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g) :=
  char_weylRepOfShape_diagramOf_eq_sum_spechtChar μ g

/-- **The character of the Weyl module of a partition on the diagonal torus** is the
Frobenius-characteristic expression in the power sums: for a partition `μ` of `d`,

`char 𝕊^μ(kⁿ) (diag x) = (1 / d!) · ∑_{σ ∈ S_d} χ^μ(σ) · p_{ρ(σ)}(x)`,

where `ρ(σ)` is the cycle type of `σ`. -/
theorem char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar {d : ℕ} (μ : d.Partition)
    (x : Fin n → kˣ) :
    Representation.character (V := (weylModuleOfShape k n (diagramOf μ)).toSubmodule)
        (weylRepOfShape k n (diagramOf μ)) (diagGL x) =
      (d.factorial : k)⁻¹ * eval (fun i => (x i : k))
        (∑ σ : Equiv.Perm (Fin d), spechtChar μ σ • psumPart (Fin n) k σ.partition) := by
  simp_rw [char_weylRepOfShape_diagramOf_eq_sum_spechtChar,
    trace_permTensorAction_mul_tensorPowerRep_diagGL, map_sum, map_zsmul]

/-- **The character of the bundled Weyl module of a partition on the diagonal torus** is the
Frobenius-characteristic expression in the power sums: the `FDRep` form of
`TauCeti.char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar`. -/
theorem char_weylFDRepOfShape_diagramOf_diagonal_eq_sum_spechtChar {d : ℕ} (μ : d.Partition)
    (x : Fin n → kˣ) :
    (weylFDRepOfShape k n (diagramOf μ)).character (diagGL x) =
      (d.factorial : k)⁻¹ * eval (fun i => (x i : k))
        (∑ σ : Equiv.Perm (Fin d), spechtChar μ σ • psumPart (Fin n) k σ.partition) :=
  char_weylRepOfShape_diagramOf_diagonal_eq_sum_spechtChar μ x

/-- **The Schur-Weyl decomposition of the character of a tensor power.** For every `g ∈ GL n k`,
the character of `(kⁿ)^{⊗d}` at `g` is the sum over the partitions `μ` of `d` of the characters of
the Weyl modules `𝕊^μ(kⁿ)` at `g`, each weighted by the dimension `f^μ` of the Specht module
`S^μ`. -/
theorem sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf (d : ℕ) (g : GL (Fin n) k) :
    ∑ μ : d.Partition, (finrank ℚ (spechtModule μ) : k) *
        Representation.character (V := (weylModuleOfShape k n (diagramOf μ)).toSubmodule)
          (weylRepOfShape k n (diagramOf μ)) g =
      (tensorPowerRep k n d).character g := by
  have hd : (d.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr d.factorial_ne_zero
  set T := fun σ : Equiv.Perm (Fin d) =>
    LinearMap.trace k _ (permTensorAction k n d σ * tensorPowerRep k n d g)
  simp_rw [char_weylRepOfShape_diagramOf_eq_sum_spechtChar]
  calc ∑ μ : d.Partition, (finrank ℚ (spechtModule μ) : k) *
        ((d.factorial : k)⁻¹ * ∑ σ, spechtChar μ σ • T σ)
      _ = (d.factorial : k)⁻¹ *
          ∑ σ, (∑ μ : d.Partition, (finrank ℚ (spechtModule μ) : ℤ) * spechtChar μ σ) • T σ := by
        simp_rw [Finset.sum_smul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun σ _ => ?_
        simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
        ring
      _ = (tensorPowerRep k n d).character g := by
        -- column orthogonality leaves only the identity permutation
        simp_rw [sum_finrank_spechtModule_mul_spechtChar, ite_smul, zero_smul,
          Finset.sum_ite_eq', Finset.mem_univ, ite_true, T, map_one, one_mul, zsmul_eq_mul,
          Int.cast_natCast, inv_mul_cancel_left₀ hd, Representation.character]

/-- **The Schur-Weyl decomposition of the character of the bundled tensor power**: the `FDRep` form
of `TauCeti.sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf`. -/
theorem sum_finrank_spechtModule_mul_char_weylFDRepOfShape_diagramOf (d : ℕ) (g : GL (Fin n) k) :
    ∑ μ : d.Partition, (finrank ℚ (spechtModule μ) : k) *
        (weylFDRepOfShape k n (diagramOf μ)).character g =
      (tensorPowerFDRep k n d).character g :=
  sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf d g

variable (k) in
/-- **The Schur-Weyl dimension count**: `∑_{μ ⊢ d} f^μ · dim 𝕊^μ(kⁿ) = n^d`, where `f^μ` is the
dimension of the Specht module `S^μ`. -/
theorem sum_finrank_spechtModule_mul_finrank_weylModuleOfShape (n d : ℕ) :
    ∑ μ : d.Partition, finrank ℚ (spechtModule μ) *
        finrank k (weylModuleOfShape k n (diagramOf μ)).toSubmodule = n ^ d := by
  have h := sum_finrank_spechtModule_mul_char_weylRepOfShape_diagramOf (k := k) (n := n) d 1
  simp only [Representation.char_one, finrank_eq_card_basis (tensorPowerBasis k n d),
    Fintype.card_fun, Fintype.card_fin] at h
  exact_mod_cast h

end TauCeti
