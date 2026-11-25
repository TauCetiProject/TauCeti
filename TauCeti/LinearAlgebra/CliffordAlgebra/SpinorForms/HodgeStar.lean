/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.SpinorForms.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.Dual
public import TauCeti.LinearAlgebra.CliffordAlgebra.VolumeElement.HodgeStar
-- Private: existence of a full spinor module forces even dimension.
import TauCeti.LinearAlgebra.CliffordAlgebra.Dimension

/-!
# Hodge duality and chiralities on spinor endomorphisms and spinor tensors

Let `V` be an oriented real inner product space of dimension `n` with `Q v = -‖v‖²`, and let
`ρ : Cℓ(ℂ ⊗ V, Q_ℂ) ≃ₐ[ℂ] End_ℂ S` be a full spinor representation. Because the existence of `ρ`
already forces `n` to be even (`CliffordAlgebra.even_finrank_of_algEquiv_end`), no separate parity
assumption on `n` is needed.

Under `AlgEquiv.cliffordFormsEquivEnd`, left multiplication by spinor chirality
`ρ (complexVolume Q o)` corresponds to `i ^ (n / 2 + k (k - 1))` times the complex Hodge star
`Orientation.complexHodgeStar` on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`; equivalently, the complex Hodge star acts on
spinor tensors `S ⊗[ℂ] Dual ℂ S` by `(-i) ^ (n / 2 + k (k - 1))` times `Γ_S ⊗ Id` on the first
spinor factor alone. When `4 ∣ n` and `k` is the middle degree `k + k = n`, the scalar factor is
`1`, so the complex Hodge star acts directly as `Γ_S ⊗ Id` (as used for the signature operator).

By contrast, exterior parity `ExteriorAlgebra.involute` acts on `S ⊗[ℂ] Dual ℂ S` by `Γ_S ⊗ Γ_Sᵀ`
(`AlgEquiv.cliffordFormsEquivTensor_involute`), using the induced dual parity `Γ_Sᵀ`. On `Dual ℂ S`
viewed as the reverse-dual Clifford module (`AlgHom.cliffordReverseDual`), chirality is instead
`Γ_(S*) = (-1) ^ (n / 2) Γ_Sᵀ`, so the tensor chirality `Γ_S ⊗ Γ_(S*)` differs from exterior
parity by the sign `(-1) ^ (n / 2)`
(`AlgEquiv.map_cliffordReverseDual_complexVolume_cliffordFormsEquivTensor`).

## Main results

* `AlgEquiv.mul_complexVolume_cliffordFormsEquivEnd` and
  `AlgEquiv.cliffordFormsEquivEnd_complexHodgeStar`: comparison between left multiplication by
  spinor chirality and the complex Hodge star on `End ℂ S`.
* `AlgEquiv.cliffordFormsEquivTensor_complexHodgeStar`: on `S ⊗[ℂ] Dual ℂ S`, the complex Hodge
  star is `(-i) ^ (n / 2 + k (k - 1))` times `Γ_S ⊗ Id`.
* `AlgEquiv.cliffordFormsEquivEnd_complexHodgeStar_of_four_dvd` and
  `AlgEquiv.cliffordFormsEquivTensor_complexHodgeStar_of_four_dvd`: in dimension divisible by `4`
  and middle degree `k + k = finrank ℝ V`, the complex Hodge star acts with sign `+1` by left
  chirality `Γ_S` (respectively `Γ_S ⊗ Id`).
* `AlgEquiv.map_cliffordReverseDual_complexVolume_cliffordFormsEquivTensor`: the tensor chirality
  `Γ_S ⊗ Γ_(S*)` using the reverse-dual Clifford action equals `(-1) ^ (n / 2)` times exterior
  parity on `S ⊗[ℂ] Dual ℂ S`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Chapter II, §6.
* L. Nicolaescu, *Lectures on the Geometry of Manifolds*, §2.2.4.
-/

public section

noncomputable section

open scoped TensorProduct
open CliffordAlgebra Module

namespace AlgEquiv

private theorem neg_I_pow_mul_I_pow (m : ℕ) : (-Complex.I) ^ m * Complex.I ^ m = 1 := by
  rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow]

variable {V S : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup S] [Module ℂ S]
  {n : ℕ} [Fact (Module.finrank ℝ V = n)] {Q : QuadraticForm ℝ V}

private theorem even_of_algEquiv_end
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S) : Even n := by
  have h := even_finrank_of_algEquiv_end (Q.baseChange ℂ) ρ
  rwa [Module.finrank_baseChange, Fact.out (p := finrank ℝ V = n)] at h

/-- **Left multiplication by spinor chirality is the signed complex Hodge star**: for `k + l = n`
and `x ∈ ℂ ⊗[ℝ] ⋀[ℝ]^k V`, multiplying `ρ.cliffordFormsEquivEnd` on the left by
`ρ (complexVolume Q o)` multiplies the complex Hodge star by `i ^ (n / 2 + k (k - 1))`. -/
theorem mul_complexVolume_cliffordFormsEquivEnd
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    ρ (complexVolume Q o) * ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x) =
      Complex.I ^ (n / 2 + k * (k - 1)) •
        ρ.cliffordFormsEquivEnd ((⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x)) := by
  obtain ⟨_, _⟩ : Even n := even_of_algEquiv_end ρ
  rw [← ρ.cliffordFormsEquivEnd_action,
    baseChangeExteriorAction_complexVolume_of_eq_two_mul o hQ (by omega : n = 2 * (n / 2)) hkl,
    map_smul]

/-- **The complex Hodge star on spinor endomorphisms**: for `k + l = n`,
`Orientation.complexHodgeStar` acts under `cliffordFormsEquivEnd` by `(-i) ^ (n / 2 + k (k - 1))`
times left multiplication by spinor chirality `ρ (complexVolume Q o)`. -/
theorem cliffordFormsEquivEnd_complexHodgeStar
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    ρ.cliffordFormsEquivEnd ((⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x)) =
      (-Complex.I) ^ (n / 2 + k * (k - 1)) •
        (ρ (complexVolume Q o) * ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x)) := by
  rw [ρ.mul_complexVolume_cliffordFormsEquivEnd o hQ hkl, smul_smul, neg_I_pow_mul_I_pow, one_smul]

/-- **Middle-degree Hodge star in dimension divisible by `4`**: when `4 ∣ n` and `k + k = n`,
the complex Hodge star on `ℂ ⊗[ℝ] ⋀[ℝ]^k V` corresponds with sign `+1` to left multiplication by
spinor chirality `ρ (complexVolume Q o)` (including `n = 0`, `k = 0`). -/
theorem cliffordFormsEquivEnd_complexHodgeStar_of_four_dvd
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : 4 ∣ n)
    {k : ℕ} (hk : k + k = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ (o.complexHodgeStar hk x)) =
      ρ (complexVolume Q o) * ρ.cliffordFormsEquivEnd ((⋀[ℝ]^k V).subtype.baseChange ℂ x) := by
  obtain ⟨m, hm⟩ := hn
  have hkm : k = 2 * m := by
    have := Fact.out (p := finrank ℝ V = n)
    omega
  have hexp : n / 2 + k * (k - 1) = 4 * m ^ 2 := by
    rw [hm, hkm]
    rcases m with _ | m
    · simp
    · have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      have hdiv : 4 * (m + 1) / 2 = 2 * (m + 1) := by omega
      rw [hsub, hdiv]
      ring
  have hI4 : (-Complex.I) ^ 4 = 1 := by
    rw [neg_pow, Complex.I_pow_four]
    norm_num
  rw [ρ.cliffordFormsEquivEnd_complexHodgeStar o hQ hk, hexp, pow_mul, hI4, one_pow, one_smul]

section Tensor

variable [FiniteDimensional ℂ S]

/-- **Spinor chirality on the first tensor factor is the signed complex Hodge star**: for
`k + l = n`, applying `Γ_S ⊗ Id` on `S ⊗[ℂ] Dual ℂ S` multiplies the complex Hodge star by
`i ^ (n / 2 + k (k - 1))`. -/
theorem map_complexVolume_id_cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    TensorProduct.map (ρ (complexVolume Q o)) LinearMap.id
        (ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ x)) =
      Complex.I ^ (n / 2 + k * (k - 1)) •
        ρ.cliffordFormsEquivTensor
          ((⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x)) := by
  obtain ⟨_, _⟩ : Even n := even_of_algEquiv_end ρ
  rw [← ρ.cliffordFormsEquivTensor_action,
    baseChangeExteriorAction_complexVolume_of_eq_two_mul o hQ (by omega : n = 2 * (n / 2)) hkl,
    map_smul]

/-- **The complex Hodge star on spinor tensors**: for `k + l = n`, `Orientation.complexHodgeStar`
acts on `S ⊗[ℂ] Dual ℂ S` by `(-i) ^ (n / 2 + k (k - 1))` times `Γ_S ⊗ Id` on the first spinor
factor, leaving the dual factor untouched. -/
theorem cliffordFormsEquivTensor_complexHodgeStar
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    {k l : ℕ} (hkl : k + l = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    ρ.cliffordFormsEquivTensor ((⋀[ℝ]^l V).subtype.baseChange ℂ (o.complexHodgeStar hkl x)) =
      (-Complex.I) ^ (n / 2 + k * (k - 1)) •
        TensorProduct.map (ρ (complexVolume Q o)) LinearMap.id
          (ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ x)) := by
  rw [ρ.map_complexVolume_id_cliffordFormsEquivTensor o hQ hkl, smul_smul, neg_I_pow_mul_I_pow,
    one_smul]

/-- **Middle-degree Hodge star on spinor tensors in dimension divisible by `4`**: when `4 ∣ n` and
`k + k = n`, the complex Hodge star on `ℂ ⊗[ℝ] ⋀[ℝ]^k V` corresponds on `S ⊗[ℂ] Dual ℂ S` to
`Γ_S ⊗ Id` without any sign. -/
theorem cliffordFormsEquivTensor_complexHodgeStar_of_four_dvd
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hn : 4 ∣ n)
    {k : ℕ} (hk : k + k = finrank ℝ V) (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ (o.complexHodgeStar hk x)) =
      TensorProduct.map (ρ (complexVolume Q o)) LinearMap.id
        (ρ.cliffordFormsEquivTensor ((⋀[ℝ]^k V).subtype.baseChange ℂ x)) := by
  have h := ρ.cliffordFormsEquivEnd_complexHodgeStar_of_four_dvd o hQ hn hk x
  exact (ρ.cliffordFormsEquivTensor_eq_map_iff ρ (ρ (complexVolume Q o)) LinearMap.id
    ((⋀[ℝ]^k V).subtype.baseChange ℂ x)
    ((⋀[ℝ]^k V).subtype.baseChange ℂ (o.complexHodgeStar hk x))).mpr
    (by simpa [Module.End.mul_eq_comp] using h)

/-- **Reverse-dual chirality versus exterior parity on `S ⊗[ℂ] Dual ℂ S`**: acting by spinor
chirality `Γ_S` on `S` and by the reverse-dual chirality `Γ_(S*)` (`AlgHom.cliffordReverseDual`)
on `Dual ℂ S` differs from exterior parity (`ExteriorAlgebra.involute`, which acts by `Γ_S ⊗ Γ_Sᵀ`)
by the factor `(-1) ^ (n / 2)`. -/
theorem map_cliffordReverseDual_complexVolume_cliffordFormsEquivTensor
    (ρ : CliffordAlgebra (Q.baseChange ℂ) ≃ₐ[ℂ] Module.End ℂ S)
    (o : Orientation ℝ V (Fin n)) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (x : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    TensorProduct.map (ρ (complexVolume Q o))
        (ρ.toAlgHom.cliffordReverseDual (complexVolume Q o))
        (ρ.cliffordFormsEquivTensor x) =
      (-1 : ℂ) ^ (n / 2) •
        ρ.cliffordFormsEquivTensor (involute.toLinearMap.baseChange ℂ x) := by
  rw [AlgHom.cliffordReverseDual_complexVolume, AlgEquiv.toAlgHom_apply,
    TensorProduct.map_smul_right, LinearMap.smul_apply,
    ρ.cliffordFormsEquivTensor_involute o hQ]

end Tensor

end AlgEquiv
