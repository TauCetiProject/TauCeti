/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Hom

/-!
# Channel recoupling and coupled normalized `F`-ladder bases

At a generic parameter `q`, a triple tensor product of signed ladder modules of `U_q(sl₂)` carries
two normalized Clebsch–Gordan decompositions linked through `BialgebraModule.assoc` by
`clebschGordanRecouplingEquiv`. This file extracts the channel-level recoupling scalars
`sixJChannel` and `sixJChannelSymm` and constructs the coupled normalized `F`-ladder bases of
`(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` and `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`, in which the matrix of `assoc` is
block-diagonal in the `F`-ladder index with diagonal entries `sixJChannel`.

## Main definitions

* `TauCeti.UqSl2.clebschGordanRecouplingHom`, `TauCeti.UqSl2.sixJChannel`: channel-indexed
  recoupling intertwiners and their Schur scalars.
* `TauCeti.UqSl2.clebschGordanLeftBasis`, `TauCeti.UqSl2.clebschGordanRightBasis`: coupled
  normalized `F`-ladder bases of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` and `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule Module

variable {q : ℂ} [Fact (q ≠ 0)] {m n p : ℕ}

/-- The `UqSl2 q`-linear component of `clebschGordanRecouplingEquiv` from left channel `(i, j)` to
right channel `(r, s)`. -/
def clebschGordanRecouplingHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (LinearMap.proj s).comp <| (LinearMap.proj r).comp <|
    (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).toLinearMap.comp <|
      (LinearMap.single _ _ i).comp (LinearMap.single _ _ j)

/-- The `UqSl2 q`-linear component of `(clebschGordanRecouplingEquiv hq).symm` from right channel
`(r, s)` to left channel `(i, j)`. -/
def clebschGordanRecouplingSymmHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (LinearMap.proj j).comp <| (LinearMap.proj i).comp <|
    (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm.toLinearMap.comp <|
      (LinearMap.single _ _ r).comp (LinearMap.single _ _ s)

/-- Pointwise formula for `clebschGordanRecouplingHom`. -/
theorem clebschGordanRecouplingHom_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanRecouplingHom hq ε δ ζ i j r s x =
      clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)) r s := (rfl)

/-- Pointwise formula for `clebschGordanRecouplingSymmHom`. -/
theorem clebschGordanRecouplingSymmHom_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRecouplingSymmHom hq ε δ ζ r s i j x =
      (clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)) i j := (rfl)

/-- The quantum `6j` recoupling scalar from left channel `(i, j)` to right channel `(r, s)`. -/
def sixJChannel (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) : ℂ :=
  homScalar (clebschGordanRecouplingHom hq ε δ ζ i j r s)

/-- The inverse quantum `6j` recoupling scalar from right channel `(r, s)` to left channel
`(i, j)`. -/
def sixJChannelSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) : ℂ :=
  homScalar (clebschGordanRecouplingSymmHom hq ε δ ζ r s i j)

/-- Channel recoupling acts on every normalized `F`-ladder vector `v_k` by `sixJChannel`. -/
@[simp] theorem clebschGordanRecouplingHom_vec (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (k : ℤ) :
    clebschGordanRecouplingHom hq ε δ ζ i j r s (vec q _ _ k) =
      sixJChannel hq ε δ ζ i j r s • vec q _ _ k :=
  apply_vec_eq_homScalar_smul hq _ k

/-- Inverse channel recoupling acts on every normalized `F`-ladder vector `v_k` by
`sixJChannelSymm`. -/
@[simp] theorem clebschGordanRecouplingSymmHom_vec (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (k : ℤ) :
    clebschGordanRecouplingSymmHom hq ε δ ζ r s i j (vec q _ _ k) =
      sixJChannelSymm hq ε δ ζ r s i j • vec q _ _ k :=
  apply_vec_eq_homScalar_smul hq _ k

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
@[simp] theorem clebschGordanLeftBasis_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    clebschGordanLeftBasis hq m n p ε δ ζ ⟨i, j, k⟩ =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanInclusion hq j (vec q _ ((ε * δ) * ζ) k)) := by
  simp [clebschGordanLeftBasis, Pi.basis_apply, vec_coe]

/-- Explicit formula for the right-coupled normalized `F`-ladder basis elements. -/
@[simp] theorem clebschGordanRightBasis_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    clebschGordanRightBasis hq m n p ε δ ζ ⟨r, s, l⟩ =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
        (clebschGordanInclusion hq s (vec q _ (ε * (δ * ζ)) l)) := by
  simp [clebschGordanRightBasis, Pi.basis_apply, vec_coe]

/-- Matrix of the coproduct tensor associator in the coupled normalized `F`-ladder bases: entries
vanish off `l = k` and equal `sixJChannel hq ε δ ζ i j r s` along `l = k`. -/
theorem toMatrix_assoc_clebschGordanBasis (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanLeftBasis hq m n p ε δ ζ)
        (clebschGordanRightBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).toLinearMap.restrictScalars ℂ) ⟨r, s, l⟩ ⟨i, j, k⟩ =
      if (l : ℕ) = (k : ℕ) then sixJChannel hq ε δ ζ i j r s else 0 := by
  rw [LinearMap.toMatrix_apply]
  simp only [clebschGordanRightBasis, clebschGordanLeftBasis, Basis.map_repr, Basis.map_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Pi.basis_apply, Pi.basis_repr, ← vec_coe]
  rw [← clebschGordanRightEquiv_recoupling, LinearEquiv.symm_apply_apply,
    ← clebschGordanRecouplingHom_apply, clebschGordanRecouplingHom_vec,
    map_smul, Finsupp.smul_apply, basis_repr_vec, smul_eq_mul]
  norm_cast; simp [mul_ite]

/-- Matrix of `assoc.symm` in the coupled normalized `F`-ladder bases. -/
theorem toMatrix_assoc_symm_clebschGordanBasis (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    LinearMap.toMatrix (clebschGordanRightBasis hq m n p ε δ ζ)
        (clebschGordanLeftBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).symm.toLinearMap.restrictScalars ℂ) ⟨i, j, k⟩ ⟨r, s, l⟩ =
      if (k : ℕ) = (l : ℕ) then sixJChannelSymm hq ε δ ζ r s i j else 0 := by
  rw [LinearMap.toMatrix_apply]
  simp only [clebschGordanRightBasis, clebschGordanLeftBasis, Basis.map_repr, Basis.map_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Pi.basis_apply, Pi.basis_repr, ← vec_coe]
  rw [← clebschGordanLeftEquiv_recoupling_symm, LinearEquiv.symm_apply_apply,
    ← clebschGordanRecouplingSymmHom_apply, clebschGordanRecouplingSymmHom_vec,
    map_smul, Finsupp.smul_apply, basis_repr_vec, smul_eq_mul]
  norm_cast; simp [mul_ite]

end TauCeti.UqSl2
