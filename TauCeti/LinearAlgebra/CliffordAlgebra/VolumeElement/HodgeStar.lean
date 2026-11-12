/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Complex
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Complex
public import TauCeti.LinearAlgebra.ExteriorAlgebra.CliffordAction
-- Private: the shuffle signs of complementary index sets are used only inside proofs.
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# The volume element acts on forms by the Hodge star

Let `V` be an oriented real inner product space of dimension `n` and `Q v = -‖v‖²`, so that the
Clifford algebra acts on the exterior algebra by `c(v) = ε(v) - ι(v)`
(`CliffordAlgebra.exteriorAction`). This file computes the action of the volume element
`vol = c(e₁) ⋯ c(eₙ)` (`CliffordAlgebra.volumeElement`) on a `k`-form `ω`: it is the Hodge star up
to a sign depending only on the degrees,

  `vol · ω = (-1) ^ ((k + 1).choose 2 + k l) ⋆ω`,  `k + l = n`.

Both sides change sign with the orientation, so the identity holds for every orientation,
including the negative orientation in rank zero.

After complexification the normalized complex volume element
`Γ = i ^ ⌊(n + 1) / 2⌋ vol` (`CliffordAlgebra.complexVolume`) acts on complex-valued forms
`ℂ ⊗[ℝ] ⋀ᵏ V` through the complex-linear Hodge star `Orientation.complexHodgeStar`. In even
dimension `n = 2ℓ` the sign becomes a power of `i`:

  `Γ ω = i ^ (ℓ + k (k - 1)) ⋆ω`.

This relates the chirality operator of the Clifford module of forms to the Hodge star. In dimension
`n = 4m` and middle degree `k = 2m` the power is `i ^ (4 m²) = 1`, so `Γ` and `⋆` agree on
middle-degree forms, as used for the signature operator.

## Main results

* `CliffordAlgebra.exteriorAction_volumeElement`: `vol · ω = (-1) ^ ((k + 1).choose 2 + k l) ⋆ω`.
* `CliffordAlgebra.baseChangeExteriorAction_complexVolume`: the same for `Γ` on complex-valued
  forms, with the factor `i ^ ⌊(n + 1) / 2⌋`.
* `CliffordAlgebra.baseChangeExteriorAction_complexVolume_of_eq_two_mul`: in dimension `2ℓ`,
  `Γ ω = i ^ (ℓ + k (k - 1)) ⋆ω`.

## Implementation notes

For a basis form `e_I` of a positively oriented orthonormal basis, with `Iᶜ` the complementary
indices, `vol = ε(Iᶜ) e_{Iᶜ} e_I` for the shuffle sign `ε(Iᶜ)`, while
`e_I² = (-1) ^ ((k + 1).choose 2)` and `⋆e_I = ε(I) e_{Iᶜ}`; the two shuffle signs differ by
`(-1) ^ (k l)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapters I and II.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, the chapter on Clifford modules and
  Dirac operators.
-/

public section

noncomputable section

open Module exteriorPower Set
open scoped TensorProduct

namespace CliffordAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {n : ℕ} [Fact (finrank ℝ V = n)] {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin n))

section Real

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- The volume element acts on basis forms of a positively oriented orthonormal basis by the
signed Hodge star. -/
private theorem exteriorAction_volumeElement_of_orientation (b : OrthonormalBasis (Fin n) ℝ V)
    (hb : b.toBasis.orientation = o) {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ⋀[ℝ]^k V) :
    exteriorAction Q (volumeElement Q o) x =
      (-1 : ℝ) ^ ((k + 1).choose 2 + k * l) • (o.hodgeStar hkl x : ExteriorAlgebra ℝ V) := by
  have hcard : l + k = Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← (Fact.out : finrank ℝ V = n)]; omega
  -- Compare both sides as linear maps on the basis `e_s` of `⋀ᵏ V`.
  refine LinearMap.congr_fun ((b.toBasis.exteriorPower k).ext
    (f₁ := exteriorAction Q (volumeElement Q o) ∘ₗ (⋀[ℝ]^k V).subtype)
    (f₂ := (-1 : ℝ) ^ ((k + 1).choose 2 + k * l) •
      (⋀[ℝ]^l V).subtype ∘ₗ (o.hodgeStar hkl).toLinearMap) fun s ↦ ?_) x
  have hsign := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (powersetCard.sign_mul_sign_compl hcard s)
  have hsq := congrArg (fun u : ℤˣ ↦ ((u : ℤ) : ℝ)) (Int.units_mul_self (powersetCard.sign s))
  push_cast at hsign hsq
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
    Submodule.subtype_apply]
  rw [o.hodgeStar_basis b hb hkl s, ← ExteriorAlgebra.basis_eq_coe_basis,
    ← equivExterior_basis Q, exteriorAction_equivExterior, volumeElement_mul_basis o hQ b hb hcard,
    map_smul, equivExterior_basis, ExteriorAlgebra.basis_eq_coe_basis]
  -- Both sides are real multiples of `e_{sᶜ}`; compare the coefficients.
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, Submodule.coe_smul, smul_smul]
  congr 1
  set ε := ((powersetCard.sign s : ℤ) : ℝ)
  set ε' := ((powersetCard.sign (powersetCard.compl hcard s) : ℤ) : ℝ)
  rw [pow_add]
  linear_combination (-(-1 : ℝ) ^ (k + 1).choose 2 * ε') * hsq +
    ((-1 : ℝ) ^ (k + 1).choose 2 * ε) * hsign

/-- **The volume element acts on forms by the signed Hodge star**: for a `k`-form `ω` and
`k + l = n`, `vol · ω = (-1) ^ ((k + 1).choose 2 + k l) ⋆ω`, where `vol = c(e₁) ⋯ c(eₙ)` acts by
`c(v) = ε(v) - ι(v)`. This holds for both orientations, in every dimension. -/
theorem exteriorAction_volumeElement {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ⋀[ℝ]^k V) :
    exteriorAction Q (volumeElement Q o) x =
      (-1 : ℝ) ^ ((k + 1).choose 2 + k * l) • (o.hodgeStar hkl x : ExteriorAlgebra ℝ V) := by
  set b : OrthonormalBasis (Fin n) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr Fact.out)
  rcases b.toBasis.orientation_eq_or_eq_neg o with h | h
  · exact exteriorAction_volumeElement_of_orientation o hQ b h.symm hkl x
  · rw [h, volumeElement_neg_orientation, Orientation.hodgeStar_neg_orientation, map_neg,
      LinearMap.neg_apply, exteriorAction_volumeElement_of_orientation _ hQ b rfl hkl x,
      Submodule.coe_neg, smul_neg]

end Real

/-! ### The normalized complex volume element on complex-valued forms -/

section Complex

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

/-- **`Γ` acts on complex-valued forms by the signed complex Hodge star**: for
`ω ∈ ℂ ⊗[ℝ] ⋀ᵏ V` and `k + l = n`,
`Γ ω = i ^ ⌊(n + 1) / 2⌋ (-1) ^ ((k + 1).choose 2 + k l) ⋆ω`. -/
theorem baseChangeExteriorAction_complexVolume {k l : ℕ} (hkl : k + l = finrank ℝ V)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    baseChangeExteriorAction ℂ Q (complexVolume Q o) ((⋀[ℝ]^k V).subtype.baseChange ℂ x) =
      (Complex.I ^ ((n + 1) / 2) * (-1) ^ ((k + 1).choose 2 + k * l)) •
        (⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z y =>
    rw [complexVolume_def, map_smul, LinearMap.smul_apply, LinearMap.baseChange_tmul,
      baseChangeExteriorAction_ofBaseChangeAux_tmul, Submodule.subtype_apply,
      exteriorAction_volumeElement o hQ hkl, Orientation.complexHodgeStar_tmul,
      LinearMap.baseChange_tmul, Submodule.subtype_apply, TensorProduct.tmul_smul, mul_smul]
    rw [← algebraMap_smul ℂ ((-1 : ℝ) ^ ((k + 1).choose 2 + k * l)), map_pow, map_neg, map_one]
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- **In even dimension `Γ` acts on complex-valued forms by `i ^ (ℓ + k (k - 1))` times the
Hodge star**: for `n = 2ℓ`, `ω ∈ ℂ ⊗[ℝ] ⋀ᵏ V` and `k + l = n`, `Γ ω = i ^ (ℓ + k (k - 1)) ⋆ω`. -/
theorem baseChangeExteriorAction_complexVolume_of_eq_two_mul {ℓ : ℕ} (hn : n = 2 * ℓ) {k l : ℕ}
    (hkl : k + l = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    baseChangeExteriorAction ℂ Q (complexVolume Q o) ((⋀[ℝ]^k V).subtype.baseChange ℂ x) =
      Complex.I ^ (ℓ + k * (k - 1)) •
        (⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x) := by
  rw [baseChangeExteriorAction_complexVolume o hQ hkl]
  congr 1
  have hkl' : k + l = 2 * ℓ := by rw [hkl, Fact.out (p := finrank ℝ V = n), hn]
  -- `i ^ (k (k - 1)) = (-1) ^ (k.choose 2)`, and `(k + 1).choose 2 + k l ≡ k.choose 2 (mod 2)`.
  have hchoose : k * (k - 1) = 2 * k.choose 2 := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd]
  have hI : Complex.I ^ (k * (k - 1)) = (-1) ^ k.choose 2 := by
    rw [hchoose, pow_mul, Complex.I_sq]
  have hsucc : (k + 1).choose 2 = k.choose 2 + k := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
  have heven : Even (k + k * l) := by
    rw [add_comm, ← mul_add_one]
    rcases Nat.even_or_odd k with hk | hk
    · exact hk.mul_right _
    · refine Even.mul_left (Nat.even_add_one.2 fun hl ↦ ?_) _
      exact Nat.not_even_iff_odd.2 hk ((Nat.even_add.1 (hkl' ▸ even_two_mul ℓ)).2 hl)
  have hhalf : (n + 1) / 2 = ℓ := by omega
  rw [hhalf, pow_add Complex.I, hI]
  congr 1
  refine neg_one_pow_congr ?_
  rw [hsucc, add_assoc, Nat.even_add]
  simp only [heven, iff_true]

end Complex

end CliffordAlgebra
