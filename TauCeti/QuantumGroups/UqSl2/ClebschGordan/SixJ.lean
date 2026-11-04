/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Hom

import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Quantum `6j` symbols and change-of-decomposition matrices

At a generic parameter `q`, a triple tensor product of signed ladder modules of `U_q(sl₂)` carries
two normalized Clebsch–Gordan decompositions, linked through the coproduct tensor associator by
`clebschGordanRecouplingEquiv` (`TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling`). Because
each summand `L_d^η` is simple with scalar endomorphisms (`LadderModule.homScalar`), each channel
component of `clebschGordanRecouplingEquiv` acts on all normalized `F`-ladder vectors `v_k` — and
in particular on the `α₀ = 1` highest vectors `v₀` — by a single complex scalar, and vanishes
whenever the left and right total weights differ.

This file develops the resulting change-of-decomposition theory in both channel coordinates and
weight coordinates:

* **Channel coordinates and coupled bases**: `clebschGordanRecouplingHom` and `sixJChannel` extract
  the scalar between left channel `(i, j)` and right channel `(r, s)`. The coupled normalized
  `F`-ladder bases `clebschGordanLeftBasis` and `clebschGordanRightBasis` turn
  `BialgebraModule.assoc` into an explicit block-scalar matrix (`toMatrix_assoc_clebschGordanBasis`)
  diagonal in the lowering index `k`.
* **Weight coordinates and square `6j` matrices**: `IsClebschGordanTriple a b c` characterizes the
  highest weights `c` occurring in `L_a^ε ⊗ L_b^δ`, `clebschGordanWeightInclusion` and
  `clebschGordanWeightProjection` extend the normalized binary intertwiners by zero outside
  admissible triples, and `sixJSymbol hq ε δ ζ a b c d u v` records the recoupling scalar from
  intermediate weight `u` in `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` to intermediate weight `v` in
  `L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` at total weight `d`. Restricting `u` and `v` to the admissible index
  sets `SixJLeftIndex a b c d` and `SixJRightIndex a b c d` yields mutually inverse matrices
  `sixJMatrix` and `sixJMatrixSymm`.
* **Explicit `2 × 2` spin-`1/2` evaluation**: on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at total weight `d = 1`,
  the four entries at `(u, v) ∈ {0, 2} × {0, 2}` are computed in closed form in terms of `[2]_q`
  and the sign `ζ`.

## Main definitions

* `TauCeti.UqSl2.clebschGordanRecouplingHom`, `TauCeti.UqSl2.sixJChannel`: channel-indexed
  recoupling intertwiners and their Schur scalars.
* `TauCeti.UqSl2.clebschGordanLeftBasis`, `TauCeti.UqSl2.clebschGordanRightBasis`: coupled
  normalized `F`-ladder bases of `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` and `L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)`.
* `TauCeti.UqSl2.IsClebschGordanTriple`: admissibility predicate for binary Clebsch–Gordan triples.
* `TauCeti.UqSl2.clebschGordanWeightInclusion`, `TauCeti.UqSl2.clebschGordanWeightProjection`:
  weight-indexed binary Clebsch–Gordan inclusions and projections, zero outside admissible triples.
* `TauCeti.UqSl2.sixJSymbol`, `TauCeti.UqSl2.sixJSymbolSymm`: quantum `6j` change-of-decomposition
  scalars for `assoc` and `assoc.symm`.
* `TauCeti.UqSl2.sixJMatrix`, `TauCeti.UqSl2.sixJMatrixSymm`: the fixed-total-weight `6j` matrices.

## Main results

* `TauCeti.UqSl2.toMatrix_assoc_clebschGordanBasis`: matrix of `BialgebraModule.assoc` in the
  coupled normalized `F`-ladder bases.
* `TauCeti.UqSl2.assoc_comp_clebschGordanWeightInclusion`: operator reassociation of a left-coupled
  channel as a `sixJSymbol`-linear combination of right-coupled channels.
* `TauCeti.UqSl2.sixJMatrixSymm_mul_sixJMatrix`, `TauCeti.UqSl2.sixJMatrix_mul_sixJMatrixSymm`:
  two-sided invertibility of the fixed-total-weight `6j` matrix.
* `TauCeti.UqSl2.sixJSymbol_one_one_one_zero_zero`,
  `TauCeti.UqSl2.sixJSymbol_one_one_one_zero_two`,
  `TauCeti.UqSl2.sixJSymbol_one_one_one_two_zero`,
  `TauCeti.UqSl2.sixJSymbol_one_one_one_two_two`: closed-form entries on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ`.

## References

* A. N. Kirillov and N. Yu. Reshetikhin, *Representations of the algebra `U_q(sl(2))`,
  `q`-orthogonal polynomials and invariants of links*, in *Infinite-Dimensional Lie Algebras and
  Groups*, World Scientific, 1989, pp. 285–339.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters VII and XII.
* J. S. Carter, D. E. Flath, and M. Saito, *The Classical and Quantum 6j-symbols*, Mathematical
  Notes 43, Princeton University Press, 1995.
* P. Etingof, S. Gelaki, D. Nikshych, and V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Sections 4.9 and 9.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule Module

/-! ### Channel-level recoupling and coupled normalized `F`-ladder bases -/

section Channel

variable {q : ℂ} [Fact (q ≠ 0)] {m n p : ℕ}

/-- The `UqSl2 q`-linear component of `clebschGordanRecouplingEquiv` from left channel `(i, j)` to
right channel `(r, s)`. -/
def clebschGordanRecouplingHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) :
    LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) →ₗ[UqSl2 q]
      LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) :=
  (LinearMap.proj s).comp <|
    (LinearMap.proj r).comp <|
      (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).toLinearMap.comp <|
        (LinearMap.single _ _ i).comp (LinearMap.single _ _ j)

/-- The `UqSl2 q`-linear component of `(clebschGordanRecouplingEquiv hq).symm` from right channel
`(r, s)` to left channel `(i, j)`. -/
def clebschGordanRecouplingSymmHom (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) :
    LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ)) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ) :=
  (LinearMap.proj j).comp <|
    (LinearMap.proj i).comp <|
      (clebschGordanRecouplingEquiv (ε := ε) (δ := δ) (ζ := ζ) hq).symm.toLinearMap.comp <|
        (LinearMap.single _ _ r).comp (LinearMap.single _ _ s)

/-- Pointwise formula for `clebschGordanRecouplingHom` in terms of
`clebschGordanRecouplingEquiv`. -/
theorem clebschGordanRecouplingHom_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (x : LadderModule q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)) :
    clebschGordanRecouplingHom hq ε δ ζ i j r s x =
      clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j x)) r s :=
  (rfl)

/-- Pointwise formula for `clebschGordanRecouplingSymmHom` in terms of
`clebschGordanRecouplingEquiv.symm`. -/
theorem clebschGordanRecouplingSymmHom_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (x : LadderModule q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))) :
    clebschGordanRecouplingSymmHom hq ε δ ζ r s i j x =
      (clebschGordanRecouplingEquiv hq).symm (Pi.single r (Pi.single s x)) i j :=
  (rfl)

/-- The quantum `6j` recoupling scalar from left channel `(i, j)` to right channel `(r, s)` on
`(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ → L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
def sixJChannel (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) : ℂ :=
  homScalar (clebschGordanRecouplingHom hq ε δ ζ i j r s)

/-- The inverse quantum `6j` recoupling scalar from right channel `(r, s)` to left channel `(i, j)`
on `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ) → (L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
def sixJChannelSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) : ℂ :=
  homScalar (clebschGordanRecouplingSymmHom hq ε δ ζ r s i j)

/-- Channel recoupling acts on every normalized `F`-ladder vector `v_k` (`k : ℤ`) by
`sixJChannel`. -/
@[simp]
theorem clebschGordanRecouplingHom_vec (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)) (k : ℤ) :
    clebschGordanRecouplingHom hq ε δ ζ i j r s (vec q _ _ k) =
      sixJChannel hq ε δ ζ i j r s • vec q _ _ k :=
  apply_vec_eq_homScalar_smul hq _ k

/-- Inverse channel recoupling acts on every normalized `F`-ladder vector `v_k` (`k : ℤ`) by
`sixJChannelSymm`. -/
@[simp]
theorem clebschGordanRecouplingSymmHom_vec (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (k : ℤ) :
    clebschGordanRecouplingSymmHom hq ε δ ζ r s i j (vec q _ _ k) =
      sixJChannelSymm hq ε δ ζ r s i j • vec q _ _ k :=
  apply_vec_eq_homScalar_smul hq _ k

/-- `sixJChannel` vanishes whenever the total lowering steps `(i : ℕ) + j` and `(r : ℕ) + s`
differ, since the corresponding channels have distinct highest weights. -/
theorem sixJChannel_eq_zero_of_add_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    (hne : (i : ℕ) + (j : ℕ) ≠ (r : ℕ) + (s : ℕ)) :
    sixJChannel hq ε δ ζ i j r s = 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hr := r.isLt
  have hs := s.isLt
  exact homScalar_eq_zero_of_ne hq (.inl (by omega)) _

/-- Expansion of the associator on the normalized `F`-ladder vectors (`k : ℤ`, including `k = 0`
for the `α₀ = 1` highest vectors) of a left-coupled channel into right-coupled channels. -/
theorem assoc_clebschGordanInclusion_vec (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)) (k : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) (LadderModule q p ζ)
        (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
          (clebschGordanInclusion hq j (vec q _ ((ε * δ) * ζ) k))) =
      ∑ r : Fin (min n p + 1), ∑ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
        sixJChannel hq ε δ ζ i j r s •
          tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
            (clebschGordanInclusion hq s (vec q _ (ε * (δ * ζ)) k)) := by
  rw [← clebschGordanLeftEquiv_single, ← clebschGordanRightEquiv_recoupling]
  set y := clebschGordanRecouplingEquiv hq
    (Pi.single i (Pi.single j (vec q _ ((ε * δ) * ζ) k)))
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_lhs => rw [← Finset.univ_sum_single (y r)]
  rw [← LinearMap.single_apply (R := ℂ), map_sum, map_sum]
  simp only [LinearMap.single_apply, clebschGordanRightEquiv_single]
  refine Finset.sum_congr rfl fun s _ => ?_
  dsimp only [y]
  rw [← clebschGordanRecouplingHom_apply, clebschGordanRecouplingHom_vec,
    LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower]

/-- Index type for the coupled normalized `F`-ladder basis of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`. -/
abbrev ClebschGordanLeftBasisIndex (m n p : ℕ) : Type :=
  Σ i : Fin (min m n + 1),
    Σ j : Fin (min (m + n - 2 * (i : ℕ)) p + 1),
      Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)

/-- Index type for the coupled normalized `F`-ladder basis of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`. -/
abbrev ClebschGordanRightBasisIndex (m n p : ℕ) : Type :=
  Σ r : Fin (min n p + 1),
    Σ s : Fin (min m (n + p - 2 * (r : ℕ)) + 1),
      Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)

/-- The coupled normalized `F`-ladder basis of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ`, obtained by transporting
the ladder bases along `clebschGordanLeftEquiv`. At ladder index `k = 0` these are the `α₀ = 1`
coupled highest vectors. -/
def clebschGordanLeftBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Basis (ClebschGordanLeftBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q)
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (LadderModule q p ζ)) :=
  (Pi.basis fun i : Fin (min m n + 1) =>
    Pi.basis fun j : Fin (min (m + n - 2 * (i : ℕ)) p + 1) =>
      basis q (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ)) ((ε * δ) * ζ)).map
    ((clebschGordanLeftEquiv hq).restrictScalars ℂ)

/-- The coupled normalized `F`-ladder basis of `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`, obtained by transporting
the ladder bases along `clebschGordanRightEquiv`. At ladder index `k = 0` these are the `α₀ = 1`
coupled highest vectors. -/
def clebschGordanRightBasis (hq : IsGenericQuantumParameter q) (m n p : ℕ) (ε δ ζ : ℤˣ) :
    Basis (ClebschGordanRightBasisIndex m n p) ℂ
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε)
        (Tensor ℂ (UqSl2 q) (LadderModule q n δ) (LadderModule q p ζ))) :=
  (Pi.basis fun r : Fin (min n p + 1) =>
    Pi.basis fun s : Fin (min m (n + p - 2 * (r : ℕ)) + 1) =>
      basis q (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ)) (ε * (δ * ζ))).map
    ((clebschGordanRightEquiv hq).restrictScalars ℂ)

/-- Explicit formula for the left-coupled normalized `F`-ladder basis elements. -/
@[simp]
theorem clebschGordanLeftBasis_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    clebschGordanLeftBasis hq m n p ε δ ζ ⟨i, j, k⟩ =
      tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq i) LinearMap.id
        (clebschGordanInclusion hq j (vec q _ ((ε * δ) * ζ) k)) := by
  simp [clebschGordanLeftBasis, Pi.basis_apply, vec_coe]

/-- Explicit formula for the right-coupled normalized `F`-ladder basis elements. -/
@[simp]
theorem clebschGordanRightBasis_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    clebschGordanRightBasis hq m n p ε δ ζ ⟨r, s, l⟩ =
      tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanInclusion hq r)
        (clebschGordanInclusion hq s (vec q _ (ε * (δ * ζ)) l)) := by
  simp [clebschGordanRightBasis, Pi.basis_apply, vec_coe]

/-- Matrix of the coproduct tensor associator in the coupled normalized `F`-ladder bases: entries
vanish off the `F`-ladder diagonal `l = k`, and equal `sixJChannel hq ε δ ζ i j r s` along `l = k`
(in particular matching the `k = 0`, `α₀ = 1` highest-vector change-of-basis scalars). -/
theorem toMatrix_assoc_clebschGordanBasis (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1))
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1)) :
    LinearMap.toMatrix
        (clebschGordanLeftBasis hq m n p ε δ ζ)
        (clebschGordanRightBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).toLinearMap.restrictScalars ℂ)
        ⟨r, s, l⟩ ⟨i, j, k⟩ =
      if (l : ℕ) = (k : ℕ) then sixJChannel hq ε δ ζ i j r s else 0 := by
  rw [LinearMap.toMatrix_apply]
  simp only [clebschGordanRightBasis, clebschGordanLeftBasis, Basis.map_repr, Basis.map_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Pi.basis_apply, Pi.basis_repr, ← vec_coe]
  rw [← clebschGordanRightEquiv_recoupling, LinearEquiv.symm_apply_apply,
    ← clebschGordanRecouplingHom_apply, clebschGordanRecouplingHom_vec,
    map_smul, Finsupp.smul_apply, basis_repr_vec, smul_eq_mul]
  norm_cast
  simp [mul_ite]

/-- Matrix of `assoc.symm` in the coupled normalized `F`-ladder bases. -/
theorem toMatrix_assoc_symm_clebschGordanBasis (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    (i : Fin (min m n + 1)) (j : Fin (min (m + n - 2 * (i : ℕ)) p + 1))
    (k : Fin (m + n - 2 * (i : ℕ) + p - 2 * (j : ℕ) + 1))
    (r : Fin (min n p + 1)) (s : Fin (min m (n + p - 2 * (r : ℕ)) + 1))
    (l : Fin (m + (n + p - 2 * (r : ℕ)) - 2 * (s : ℕ) + 1)) :
    LinearMap.toMatrix
        (clebschGordanRightBasis hq m n p ε δ ζ)
        (clebschGordanLeftBasis hq m n p ε δ ζ)
        ((assoc ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)
          (LadderModule q p ζ)).symm.toLinearMap.restrictScalars ℂ)
        ⟨i, j, k⟩ ⟨r, s, l⟩ =
      if (k : ℕ) = (l : ℕ) then sixJChannelSymm hq ε δ ζ r s i j else 0 := by
  rw [LinearMap.toMatrix_apply]
  simp only [clebschGordanRightBasis, clebschGordanLeftBasis, Basis.map_repr, Basis.map_apply,
    LinearEquiv.restrictScalars_apply, LinearEquiv.restrictScalars_symm_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
    Pi.basis_apply, Pi.basis_repr, ← vec_coe]
  rw [← clebschGordanLeftEquiv_recoupling_symm, LinearEquiv.symm_apply_apply,
    ← clebschGordanRecouplingSymmHom_apply, clebschGordanRecouplingSymmHom_vec,
    map_smul, Finsupp.smul_apply, basis_repr_vec, smul_eq_mul]
  norm_cast
  simp [mul_ite]

end Channel

/-! ### Admissible Clebsch–Gordan triples and weight-indexed binary intertwiners -/

section WeightBinary

/-- A natural number `c` is an admissible Clebsch–Gordan summand highest weight for `L_a^ε ⊗ L_b^δ`
if `a`, `b`, `c` satisfy the triangle inequalities and `a + b - c` is even, i.e., `c = a + b - 2j`
for some `0 ≤ j ≤ min a b`. -/
def IsClebschGordanTriple (a b c : ℕ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c)

/-- Unfolded characterization of `IsClebschGordanTriple`. -/
theorem isClebschGordanTriple_iff (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c) :=
  Iff.rfl

instance (a b c : ℕ) : Decidable (IsClebschGordanTriple a b c) :=
  inferInstanceAs (Decidable (a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c)))

/-- First triangle inequality `a ≤ b + c` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add_right {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    a ≤ b + c := h.1

/-- Second triangle inequality `b ≤ a + c` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add_left {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    b ≤ a + c := h.2.1

/-- Upper bound `c ≤ a + b` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.le_add {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    c ≤ a + b := h.2.2.1

/-- Parity condition `Even (a + b - c)` of an admissible Clebsch–Gordan triple. -/
theorem IsClebschGordanTriple.even_add_sub {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    Even (a + b - c) := h.2.2.2

/-- Every lowering step `j : Fin (min a b + 1)` yields an admissible triple weight
`a + b - 2 * j`. -/
theorem isClebschGordanTriple_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    IsClebschGordanTriple a b (a + b - 2 * (j : ℕ)) := by
  have hj := j.isLt
  refine ⟨by omega, by omega, by omega, ⟨j, by omega⟩⟩

/-- Equivalence between admissible Clebsch–Gordan summand weights `c` in `L_a^ε ⊗ L_b^δ` and
lowering-step indices `j : Fin (min a b + 1)` via `c = a + b - 2j` and `j = (a + b - c) / 2`. -/
def clebschGordanTripleEquiv (a b : ℕ) :
    { c : ℕ // IsClebschGordanTriple a b c } ≃ Fin (min a b + 1) where
  toFun c := ⟨(a + b - c.1) / 2, by
    obtain ⟨ha, hb, hc, ⟨k, hk⟩⟩ := c.2
    omega⟩
  invFun j := ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩
  left_inv c := by
    ext
    obtain ⟨ha, hb, hc, ⟨k, hk⟩⟩ := c.2
    dsimp only
    omega
  right_inv j := by
    ext
    have hj := j.isLt
    dsimp only
    omega

/-- Recovery of `c = a + b - 2 * j` from `j = clebschGordanTripleEquiv a b ⟨c, h⟩`. -/
theorem clebschGordanTriple_sub_eq {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    c = a + b - 2 * (clebschGordanTripleEquiv a b ⟨c, h⟩ : ℕ) :=
  (congrArg Subtype.val ((clebschGordanTripleEquiv a b).symm_apply_apply ⟨c, h⟩)).symm

/-- `clebschGordanTripleEquiv` sends `a + b - 2 * j` back to `j`. -/
@[simp]
theorem clebschGordanTripleEquiv_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    clebschGordanTripleEquiv a b ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩ = j :=
  (clebschGordanTripleEquiv a b).apply_symm_apply j

/-- `IsClebschGordanTriple a b c` holds iff `c = a + b - 2 * j` for some `j : Fin (min a b + 1)`. -/
theorem isClebschGordanTriple_iff_exists_fin (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ ∃ j : Fin (min a b + 1), c = a + b - 2 * (j : ℕ) :=
  ⟨fun h => ⟨clebschGordanTripleEquiv a b ⟨c, h⟩, clebschGordanTriple_sub_eq h⟩,
    fun ⟨j, hj⟩ => hj ▸ isClebschGordanTriple_sub_two_mul j⟩

/-- Summing a function vanishing outside admissible Clebsch–Gordan triples over
`Finset.range (a + b + 1)` is equivalent to summing over lowering steps `j : Fin (min a b + 1)` at
`c = a + b - 2 * j`. -/
theorem sum_range_of_not_isClebschGordanTriple {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (f : ℕ → M) (hf : ∀ c, ¬ IsClebschGordanTriple a b c → f c = 0) :
    ∑ c ∈ Finset.range (a + b + 1), f c =
      ∑ j : Fin (min a b + 1), f (a + b - 2 * (j : ℕ)) := by
  have hfilter : ∑ c ∈ Finset.range (a + b + 1), f c =
      ∑ c ∈ (Finset.range (a + b + 1)).filter (IsClebschGordanTriple a b), f c := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : IsClebschGordanTriple a b c <;> simp [h, hf]
  rw [hfilter]
  symm
  refine Finset.sum_nbij (fun j : Fin (min a b + 1) => a + b - 2 * (j : ℕ)) ?_ ?_ ?_ ?_
  · intro j _
    have := j.isLt
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, isClebschGordanTriple_sub_two_mul j⟩
  · intro j₁ _ j₂ _ heq
    have := j₁.isLt
    have := j₂.isLt
    dsimp only at heq
    ext
    omega
  · intro c hc
    simp only [Finset.mem_coe, Finset.mem_filter] at hc
    exact ⟨clebschGordanTripleEquiv a b ⟨c, hc.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _),
      (clebschGordanTriple_sub_eq hc.2).symm⟩
  · intro _ _
    rfl

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Weight-indexed binary Clebsch–Gordan inclusion `L_c^(εδ) →ₗ[UqSl2 q] L_a^ε ⊗ L_b^δ`, equal to
the normalized inclusion when `IsClebschGordanTriple a b c` and `0` otherwise. -/
def clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c : ℕ) :
    LadderModule q c (ε * δ) →ₗ[UqSl2 q]
      Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) :=
  if h : IsClebschGordanTriple a b c then
    (clebschGordanInclusion hq (clebschGordanTripleEquiv a b ⟨c, h⟩)).comp
      (LadderModule.congr (clebschGordanTriple_sub_eq h) rfl).toLinearMap
  else 0

/-- Weight-indexed binary Clebsch–Gordan projection `L_a^ε ⊗ L_b^δ →ₗ[UqSl2 q] L_c^(εδ)`, equal to
the normalized projection when `IsClebschGordanTriple a b c` and `0` otherwise. -/
def clebschGordanWeightProjection (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c : ℕ) :
    Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) →ₗ[UqSl2 q]
      LadderModule q c (ε * δ) :=
  if h : IsClebschGordanTriple a b c then
    (LadderModule.congr (clebschGordanTriple_sub_eq h).symm rfl).toLinearMap.comp
      (clebschGordanProjection hq (clebschGordanTripleEquiv a b ⟨c, h⟩))
  else 0

/-- `clebschGordanWeightInclusion` vanishes outside admissible Clebsch–Gordan triples. -/
theorem clebschGordanWeightInclusion_of_not_triple (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : ¬ IsClebschGordanTriple a b c) :
    clebschGordanWeightInclusion hq a ε b δ c = 0 := by
  simp [clebschGordanWeightInclusion, h]

/-- `clebschGordanWeightProjection` vanishes outside admissible Clebsch–Gordan triples. -/
theorem clebschGordanWeightProjection_of_not_triple (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : ¬ IsClebschGordanTriple a b c) :
    clebschGordanWeightProjection hq a ε b δ c = 0 := by
  simp [clebschGordanWeightProjection, h]

/-- At `c = a + b - 2 * j`, `clebschGordanWeightInclusion` agrees with `clebschGordanInclusion`. -/
@[simp]
theorem clebschGordanWeightInclusion_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightInclusion hq a ε b δ (a + b - 2 * (j : ℕ)) =
      clebschGordanInclusion hq j := by
  refine LadderModule.hom_ext hq ?_
  simp [clebschGordanWeightInclusion, isClebschGordanTriple_sub_two_mul j]

/-- `clebschGordanWeightProjection` is a left inverse to `clebschGordanWeightInclusion` on any
admissible triple. -/
theorem clebschGordanWeightProjection_comp_inclusion_self (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : IsClebschGordanTriple a b c) :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simp only [clebschGordanWeightProjection, clebschGordanWeightInclusion, dite_eq_left h,
    LinearMap.comp_apply, LinearEquiv.coe_coe, clebschGordanProjection_inclusion_self,
    LinearMap.id_apply]
  rw [← LinearEquiv.trans_apply, congr_trans, congr_refl]
  rfl

/-- Weight-indexed Clebsch–Gordan inclusions and projections at distinct weights are orthogonal. -/
theorem clebschGordanWeightProjection_comp_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {a b c c' : ℕ} (ε δ : ℤˣ) (hne : c ≠ c') :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c') = 0 :=
  hom_eq_zero_of_ne_left hq hne.symm _

/-- At `c = a + b - 2 * j`, `clebschGordanWeightProjection` agrees with
`clebschGordanProjection`. -/
@[simp]
theorem clebschGordanWeightProjection_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightProjection hq a ε b δ (a + b - 2 * (j : ℕ)) =
      clebschGordanProjection hq j := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← sum_clebschGordanInclusion_projection hq x]
  conv_rhs => rw [← sum_clebschGordanInclusion_projection hq x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hij : i = j
  · subst hij
    have hself := congrArg (· (clebschGordanProjection hq i x))
      (clebschGordanWeightProjection_comp_inclusion_self hq ε δ
        (isClebschGordanTriple_sub_two_mul i))
    simpa using hself
  · have hne : a + b - 2 * (j : ℕ) ≠ a + b - 2 * (i : ℕ) := by
      have := i.isLt
      have := j.isLt
      intro h
      apply hij
      ext
      omega
    have hzero := congrArg (· (clebschGordanProjection hq i x))
      (clebschGordanWeightProjection_comp_inclusion_of_ne (a := a) (b := b) hq ε δ hne)
    simpa [clebschGordanProjection_inclusion_of_ne hq (Ne.symm hij)] using hzero

/-- Weight-indexed Clebsch–Gordan inclusions and projections resolve the identity on
`L_a^ε ⊗ L_b^δ` over `Finset.range (a + b + 1)`. -/
theorem sum_clebschGordanWeightInclusion_comp_projection (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) :
    ∑ c ∈ Finset.range (a + b + 1),
      (clebschGordanWeightInclusion hq a ε b δ c).comp
        (clebschGordanWeightProjection hq a ε b δ c) = LinearMap.id := by
  rw [sum_range_of_not_isClebschGordanTriple a b _ fun c htr => by
    simp [clebschGordanWeightInclusion_of_not_triple hq ε δ htr]]
  simpa using sum_clebschGordanInclusion_comp_projection (m := a) (n := b) (ε := ε) (δ := δ) hq

/-- Transporting the summand weight of `clebschGordanWeightInclusion` along `c = c'`. -/
theorem clebschGordanWeightInclusion_congr_right (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) {c c' : ℕ} (hc : c = c') :
    clebschGordanWeightInclusion hq a ε b δ c' =
      (clebschGordanWeightInclusion hq a ε b δ c).comp
        (LadderModule.congr hc.symm rfl).toLinearMap := by
  subst hc
  simp

/-- Transporting the summand weight of `clebschGordanWeightProjection` along `c = c'`. -/
theorem clebschGordanWeightProjection_congr_right (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) {c c' : ℕ} (hc : c = c') :
    clebschGordanWeightProjection hq a ε b δ c' =
      (LadderModule.congr hc rfl).toLinearMap.comp
        (clebschGordanWeightProjection hq a ε b δ c) := by
  subst hc
  simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightInclusion`. -/
theorem tensorMap_congr_comp_clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap).comp
      (clebschGordanWeightInclusion hq a ε₁ b δ₁ c) =
    (clebschGordanWeightInclusion hq a' ε₂ b' δ₂ c).comp
      (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap := by
  subst ha hb hε hδ
  simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightProjection`. -/
theorem clebschGordanWeightProjection_comp_tensorMap_congr (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (clebschGordanWeightProjection hq a' ε₂ b' δ₂ c).comp
      (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap) =
    (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap.comp
      (clebschGordanWeightProjection hq a ε₁ b δ₁ c) := by
  subst ha hb hε hδ
  simp

end WeightBinary

/-! ### Weight-indexed quantum `6j` symbols, operator reassociation, and square `6j` matrices -/

section SixJSymbol

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Weight-indexed recoupling intertwiner `L_d^((εδ)ζ) →ₗ[UqSl2 q] L_d^(ε(δζ))` from left
intermediate weight `u` in `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` to right intermediate weight `v` in
`L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` through `BialgebraModule.assoc`. -/
def sixJRecouplingHom (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u v : ℕ) :
    LadderModule q d ((ε * δ) * ζ) →ₗ[UqSl2 q] LadderModule q d (ε * (δ * ζ)) :=
  (clebschGordanWeightProjection hq a ε v (δ * ζ) d).comp <|
    (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)).comp <|
      (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
        (LadderModule q c ζ)).toLinearMap.comp <|
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d)

/-- Weight-indexed inverse recoupling intertwiner `L_d^(ε(δζ)) →ₗ[UqSl2 q] L_d^((εδ)ζ)` from right
intermediate weight `v` to left intermediate weight `u` through `(BialgebraModule.assoc).symm`. -/
def sixJRecouplingSymmHom (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d v u : ℕ) :
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
def sixJSymbol (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u v : ℕ) : ℂ :=
  homScalar (sixJRecouplingHom hq ε δ ζ a b c d u v)

/-- The inverse quantum `6j` change-of-decomposition symbol from right intermediate weight `v` in
`L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` to left intermediate weight `u` in `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` at total
weight `d`. -/
def sixJSymbolSymm (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d v u : ℕ) : ℂ :=
  homScalar (sixJRecouplingSymmHom hq ε δ ζ a b c d v u)

/-- Selection rule for `sixJSymbol`: it vanishes unless all four binary couplings `(a, b, u)`,
`(u, c, d)`, `(b, c, v)`, and `(a, v, d)` are admissible Clebsch–Gordan triples. -/
theorem sixJSymbol_eq_zero_of_not_triple (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) {a b c d u v : ℕ}
    (h : ¬ (IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d ∧
      IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)) :
    sixJSymbol hq ε δ ζ a b c d u v = 0 := by
  rw [sixJSymbol, sixJRecouplingHom]
  by_cases h₁ : IsClebschGordanTriple a b u
  · by_cases h₂ : IsClebschGordanTriple u c d
    · by_cases h₃ : IsClebschGordanTriple b c v
      · have h₄ : ¬ IsClebschGordanTriple a v d := fun h₄ => h ⟨h₁, h₂, h₃, h₄⟩
        simp [clebschGordanWeightProjection_of_not_triple hq ε (δ * ζ) h₄]
      · simp [clebschGordanWeightProjection_of_not_triple hq δ ζ h₃]
    · simp [clebschGordanWeightInclusion_of_not_triple hq (ε * δ) ζ h₂]
  · simp [clebschGordanWeightInclusion_of_not_triple hq ε δ h₁]

/-- Selection rule for `sixJSymbolSymm`: it vanishes unless all four binary couplings `(a, b, u)`,
`(u, c, d)`, `(b, c, v)`, and `(a, v, d)` are admissible Clebsch–Gordan triples. -/
theorem sixJSymbolSymm_eq_zero_of_not_triple (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) {a b c d v u : ℕ}
    (h : ¬ (IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d ∧
      IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)) :
    sixJSymbolSymm hq ε δ ζ a b c d v u = 0 := by
  rw [sixJSymbolSymm, sixJRecouplingSymmHom]
  by_cases h₁ : IsClebschGordanTriple a b u
  · by_cases h₂ : IsClebschGordanTriple u c d
    · by_cases h₃ : IsClebschGordanTriple b c v
      · have h₄ : ¬ IsClebschGordanTriple a v d := fun h₄ => h ⟨h₁, h₂, h₃, h₄⟩
        simp [clebschGordanWeightInclusion_of_not_triple hq ε (δ * ζ) h₄]
      · simp [clebschGordanWeightInclusion_of_not_triple hq δ ζ h₃]
    · simp [clebschGordanWeightProjection_of_not_triple hq (ε * δ) ζ h₂]
  · simp [clebschGordanWeightProjection_of_not_triple hq ε δ h₁]

/-- On matching `Fin` channel indices, `sixJSymbol` coincides with `sixJChannel`. -/
theorem sixJSymbol_eq_sixJChannel (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ}
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
  rw [homScalar_comp hq, homScalar_congr, mul_one]
  congr 1
  ext x
  exact (clebschGordanRecouplingEquiv_single_apply hq i j r s x).symm

/-- On matching `Fin` channel indices, `sixJSymbolSymm` coincides with `sixJChannelSymm`. -/
theorem sixJSymbolSymm_eq_sixJChannelSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ}
    (r : Fin (min b c + 1)) (s : Fin (min a (b + c - 2 * (r : ℕ)) + 1))
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
  rw [homScalar_comp hq, homScalar_congr, mul_one]
  congr 1
  ext x
  exact (clebschGordanRecouplingEquiv_symm_single_apply hq i j r s x).symm

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
          ((tensorMap ℂ (UqSl2 q) LinearMap.id
              (clebschGordanWeightInclusion hq b δ c ζ v)).comp
            ((clebschGordanWeightInclusion hq a ε v (δ * ζ) d).comp
              (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap)) := by
  set L := (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
      (LadderModule q c ζ)).toLinearMap.comp
    ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
      (clebschGordanWeightInclusion hq u (ε * δ) c ζ d))
  have hid₁ : (LinearMap.id : Tensor ℂ (UqSl2 q) (LadderModule q a ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q b δ) (LadderModule q c ζ)) →ₗ[UqSl2 q] _) =
      ∑ v ∈ Finset.range (b + c + 1),
        (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
          (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)) := by
    rw [← tensorMap_id, ← sum_clebschGordanWeightInclusion_comp_projection hq b δ c ζ,
      tensorMap_sum_right]
    exact Finset.sum_congr rfl fun v _ => by simp
  conv_lhs => rw [← LinearMap.id_comp L, hid₁, ← LinearMap.lcomp_apply' (S := ℕ) L, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
  set Mv := (tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightProjection hq b δ c ζ v)).comp L
  rw [← LinearMap.comp_smul]
  congr 1
  have hid₂ := sum_clebschGordanWeightInclusion_comp_projection hq a ε v (δ * ζ)
  rw [← LinearMap.id_comp Mv, ← hid₂, ← LinearMap.lcomp_apply' (S := ℕ) Mv, map_sum]
  by_cases hd : d ∈ Finset.range (a + v + 1)
  · rw [Finset.sum_eq_single d]
    · rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
      have hrec : (clebschGordanWeightProjection hq a ε v (δ * ζ) d).comp Mv =
          sixJRecouplingHom hq ε δ ζ a b c d u v := rfl
      rw [hrec, eq_homScalar_smul_congr hq rfl (mul_assoc ε δ ζ)
          (sixJRecouplingHom hq ε δ ζ a b c d u v),
        LinearMap.comp_smul]
      rfl
    · intro d' _ hne
      rw [LinearMap.lcomp_apply', LinearMap.comp_assoc,
        hom_eq_zero_of_ne_left hq hne.symm
          ((clebschGordanWeightProjection hq a ε v (δ * ζ) d').comp Mv),
        LinearMap.comp_zero]
    · intro hnot
      exact (hnot hd).elim
  · have hnot : ¬ IsClebschGordanTriple a v d := fun htr =>
      hd (Finset.mem_range.mpr (Nat.lt_succ_of_le htr.le_add))
    rw [sixJSymbol_eq_zero_of_not_triple hq ε δ ζ (fun h => hnot h.2.2.2), zero_smul]
    refine Finset.sum_eq_zero fun d' hd' => ?_
    have hne : d' ≠ d := fun h => hd (h ▸ hd')
    rw [LinearMap.lcomp_apply', LinearMap.comp_assoc,
      hom_eq_zero_of_ne_left hq hne.symm
        ((clebschGordanWeightProjection hq a ε v (δ * ζ) d').comp Mv),
      LinearMap.comp_zero]

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
          ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u)
              LinearMap.id).comp
            ((clebschGordanWeightInclusion hq u (ε * δ) c ζ d).comp
              (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap)) := by
  set R := (assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
      (LadderModule q c ζ)).symm.toLinearMap.comp
    ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
      (clebschGordanWeightInclusion hq a ε v (δ * ζ) d))
  have hid₁ : (LinearMap.id : Tensor ℂ (UqSl2 q)
      (Tensor ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ))
      (LadderModule q c ζ) →ₗ[UqSl2 q] _) =
      ∑ u ∈ Finset.range (a + b + 1),
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u) LinearMap.id) := by
    rw [← tensorMap_id, ← sum_clebschGordanWeightInclusion_comp_projection hq a ε b δ,
      tensorMap_sum_left]
    exact Finset.sum_congr rfl fun u _ => by simp
  conv_lhs => rw [← LinearMap.id_comp R, hid₁, ← LinearMap.lcomp_apply' (S := ℕ) R, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
  set Mu := (tensorMap ℂ (UqSl2 q) (clebschGordanWeightProjection hq a ε b δ u) LinearMap.id).comp R
  rw [← LinearMap.comp_smul]
  congr 1
  have hid₂ := sum_clebschGordanWeightInclusion_comp_projection hq u (ε * δ) c ζ
  rw [← LinearMap.id_comp Mu, ← hid₂, ← LinearMap.lcomp_apply' (S := ℕ) Mu, map_sum]
  by_cases hd : d ∈ Finset.range (u + c + 1)
  · rw [Finset.sum_eq_single d]
    · rw [LinearMap.lcomp_apply', LinearMap.comp_assoc]
      have hrec : (clebschGordanWeightProjection hq u (ε * δ) c ζ d).comp Mu =
          sixJRecouplingSymmHom hq ε δ ζ a b c d v u := rfl
      rw [hrec, eq_homScalar_smul_congr hq rfl (mul_assoc ε δ ζ).symm
          (sixJRecouplingSymmHom hq ε δ ζ a b c d v u),
        LinearMap.comp_smul]
      rfl
    · intro d' _ hne
      rw [LinearMap.lcomp_apply', LinearMap.comp_assoc,
        hom_eq_zero_of_ne_left hq hne.symm
          ((clebschGordanWeightProjection hq u (ε * δ) c ζ d').comp Mu),
        LinearMap.comp_zero]
    · intro hnot
      exact (hnot hd).elim
  · have hnot : ¬ IsClebschGordanTriple u c d := fun htr =>
      hd (Finset.mem_range.mpr (Nat.lt_succ_of_le htr.le_add))
    rw [sixJSymbolSymm_eq_zero_of_not_triple hq ε δ ζ (fun h => hnot h.2.1), zero_smul]
    refine Finset.sum_eq_zero fun d' hd' => ?_
    have hne : d' ≠ d := fun h => hd (h ▸ hd')
    rw [LinearMap.lcomp_apply', LinearMap.comp_assoc,
      hom_eq_zero_of_ne_left hq hne.symm
        ((clebschGordanWeightProjection hq u (ε * δ) c ζ d').comp Mu),
      LinearMap.comp_zero]

/-- Vector form of reassociation on normalized `F`-ladder vectors (`k : ℤ`, including `k = 0` for
the `α₀ = 1` highest vectors) in weight coordinates. -/
theorem assoc_clebschGordanWeightInclusion_vec (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d u : ℕ) (k : ℤ) :
    assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ) (LadderModule q c ζ)
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d (vec q d ((ε * δ) * ζ) k))) =
      ∑ v ∈ Finset.range (b + c + 1),
        sixJSymbol hq ε δ ζ a b c d u v •
          tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)
            (clebschGordanWeightInclusion hq a ε v (δ * ζ) d (vec q d (ε * (δ * ζ)) k)) := by
  have h := congrArg (fun f => f (vec q d ((ε * δ) * ζ) k))
    (assoc_comp_clebschGordanWeightInclusion hq ε δ ζ a b c d u)
  simpa [LinearMap.sum_apply] using h

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
      ← LinearMap.compRight_apply (S := ℕ) P, map_sum, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [LinearMap.compRight_apply, LinearMap.comp_smul, map_smul, smul_eq_mul]
    have hcomp : P.comp ((tensorMap ℂ (UqSl2 q) LinearMap.id
          (clebschGordanWeightInclusion hq b δ c ζ v)).comp
        ((clebschGordanWeightInclusion hq a ε v (δ * ζ) d).comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap)) =
        (sixJRecouplingSymmHom hq ε δ ζ a b c d v u').comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ)).toLinearMap := by
      simp only [P, sixJRecouplingSymmHom, LinearMap.comp_assoc]
    rw [hcomp, homScalar_comp hq, homScalar_congr, mul_one, mul_comm]
    rfl
  · have hlhs : P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).toLinearMap.comp
        ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u) LinearMap.id).comp
          (clebschGordanWeightInclusion hq u (ε * δ) c ζ d))) =
        (clebschGordanWeightProjection hq u' (ε * δ) c ζ d).comp
          ((tensorMap ℂ (UqSl2 q)
              ((clebschGordanWeightProjection hq a ε b δ u').comp
                (clebschGordanWeightInclusion hq a ε b δ u)) LinearMap.id).comp
            (clebschGordanWeightInclusion hq u (ε * δ) c ζ d)) := by
      ext x
      simp [P]
    rw [hlhs]
    by_cases hu : u = u' ∧ IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d
    · obtain ⟨rfl, hab, huc⟩ := hu
      simp [hab, huc, clebschGordanWeightProjection_comp_inclusion_self hq ε δ hab,
        clebschGordanWeightProjection_comp_inclusion_self hq (ε * δ) ζ huc]
    · rw [ite_eq_right hu]
      by_cases huu : u = u'
      · subst huu
        by_cases hab : IsClebschGordanTriple a b u
        · have huc : ¬ IsClebschGordanTriple u c d := fun huc => hu ⟨rfl, hab, huc⟩
          simp [clebschGordanWeightInclusion_of_not_triple hq (ε * δ) ζ huc]
        · simp [clebschGordanWeightInclusion_of_not_triple hq ε δ hab]
      · simp [clebschGordanWeightProjection_comp_inclusion_of_ne hq ε δ (Ne.symm huu)]

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
      ← LinearMap.compRight_apply (S := ℕ) P, map_sum, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearMap.compRight_apply, LinearMap.comp_smul, map_smul, smul_eq_mul]
    have hcomp : P.comp ((tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq a ε b δ u)
          LinearMap.id).comp
        ((clebschGordanWeightInclusion hq u (ε * δ) c ζ d).comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap)) =
        (sixJRecouplingHom hq ε δ ζ a b c d u v').comp
          (LadderModule.congr rfl (mul_assoc ε δ ζ).symm).toLinearMap := by
      simp only [P, sixJRecouplingHom, LinearMap.comp_assoc]
    rw [hcomp, homScalar_comp hq, homScalar_congr, mul_one, mul_comm]
    rfl
  · have hlhs : P.comp ((assoc ℂ (UqSl2 q) (LadderModule q a ε) (LadderModule q b δ)
          (LadderModule q c ζ)).symm.toLinearMap.comp
        ((tensorMap ℂ (UqSl2 q) LinearMap.id (clebschGordanWeightInclusion hq b δ c ζ v)).comp
          (clebschGordanWeightInclusion hq a ε v (δ * ζ) d))) =
        (clebschGordanWeightProjection hq a ε v' (δ * ζ) d).comp
          ((tensorMap ℂ (UqSl2 q) LinearMap.id
              ((clebschGordanWeightProjection hq b δ c ζ v').comp
                (clebschGordanWeightInclusion hq b δ c ζ v))).comp
            (clebschGordanWeightInclusion hq a ε v (δ * ζ) d)) := by
      ext x
      simp [P]
    rw [hlhs]
    by_cases hv : v = v' ∧ IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d
    · obtain ⟨rfl, hbc, hav⟩ := hv
      simp [hbc, hav, clebschGordanWeightProjection_comp_inclusion_self hq δ ζ hbc,
        clebschGordanWeightProjection_comp_inclusion_self hq ε (δ * ζ) hav]
    · rw [ite_eq_right hv]
      by_cases hvv : v = v'
      · subst hvv
        by_cases hbc : IsClebschGordanTriple b c v
        · have hav : ¬ IsClebschGordanTriple a v d := fun hav => hv ⟨rfl, hbc, hav⟩
          simp [clebschGordanWeightInclusion_of_not_triple hq ε (δ * ζ) hav]
        · simp [clebschGordanWeightInclusion_of_not_triple hq δ ζ hbc]
      · simp [clebschGordanWeightProjection_comp_inclusion_of_ne hq δ ζ (Ne.symm hvv)]

/-- Admissible left intermediate weights `u` for `(L_a^ε ⊗ L_b^δ) ⊗ L_c^ζ` at total weight `d`. -/
abbrev SixJLeftIndex (a b c d : ℕ) : Type :=
  { u : ℕ // IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d }

/-- Admissible right intermediate weights `v` for `L_a^ε ⊗ (L_b^δ ⊗ L_c^ζ)` at total weight `d`. -/
abbrev SixJRightIndex (a b c d : ℕ) : Type :=
  { v : ℕ // IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d }

instance (a b c d : ℕ) : Fintype (SixJLeftIndex a b c d) :=
  Fintype.subtype
    ((Finset.range (a + b + 1)).filter fun u =>
      IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d)
    fun u => by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

instance (a b c d : ℕ) : Fintype (SixJRightIndex a b c d) :=
  Fintype.subtype
    ((Finset.range (b + c + 1)).filter fun v =>
      IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)
    fun v => by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩

/-- The fixed-total-weight quantum `6j` change-of-decomposition matrix, with rows indexed by right
intermediate weights `v : SixJRightIndex a b c d` and columns indexed by left intermediate weights
`u : SixJLeftIndex a b c d`. -/
def sixJMatrix (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    Matrix (SixJRightIndex a b c d) (SixJLeftIndex a b c d) ℂ :=
  Matrix.of fun v u => sixJSymbol hq ε δ ζ a b c d u.1 v.1

/-- The inverse fixed-total-weight quantum `6j` change-of-decomposition matrix. -/
def sixJMatrixSymm (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    Matrix (SixJLeftIndex a b c d) (SixJRightIndex a b c d) ℂ :=
  Matrix.of fun u v => sixJSymbolSymm hq ε δ ζ a b c d v.1 u.1

/-- Entries of `sixJMatrix` are given by `sixJSymbol`. -/
@[simp]
theorem sixJMatrix_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ} (v : SixJRightIndex a b c d) (u : SixJLeftIndex a b c d) :
    sixJMatrix hq ε δ ζ a b c d v u = sixJSymbol hq ε δ ζ a b c d u.1 v.1 :=
  (rfl)

/-- Entries of `sixJMatrixSymm` are given by `sixJSymbolSymm`. -/
@[simp]
theorem sixJMatrixSymm_apply (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {a b c d : ℕ} (u : SixJLeftIndex a b c d) (v : SixJRightIndex a b c d) :
    sixJMatrixSymm hq ε δ ζ a b c d u v = sixJSymbolSymm hq ε δ ζ a b c d v.1 u.1 :=
  (rfl)

/-- `sixJMatrixSymm` is a left inverse of `sixJMatrix`. -/
@[simp]
theorem sixJMatrixSymm_mul_sixJMatrix (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    sixJMatrixSymm hq ε δ ζ a b c d * sixJMatrix hq ε δ ζ a b c d = 1 := by
  ext u' u
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsum : (∑ v : SixJRightIndex a b c d,
        sixJSymbolSymm hq ε δ ζ a b c d v.1 u'.1 * sixJSymbol hq ε δ ζ a b c d u.1 v.1) =
      ∑ v ∈ Finset.range (b + c + 1),
        sixJSymbolSymm hq ε δ ζ a b c d v u'.1 * sixJSymbol hq ε δ ζ a b c d u.1 v := by
    refine (Finset.sum_subtype
      ((Finset.range (b + c + 1)).filter fun v =>
        IsClebschGordanTriple b c v ∧ IsClebschGordanTriple a v d)
      (fun v => by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩)
      (fun v => sixJSymbolSymm hq ε δ ζ a b c d v u'.1 *
        sixJSymbol hq ε δ ζ a b c d u.1 v)).symm.trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs with hv
    · rfl
    · rw [sixJSymbol_eq_zero_of_not_triple hq ε δ ζ (fun h => hv ⟨h.2.2.1, h.2.2.2⟩), mul_zero]
  rw [sixJMatrixSymm, sixJMatrix]
  simp only [Matrix.of_apply, hsum, sum_sixJSymbolSymm_mul_sixJSymbol]
  by_cases huu : u' = u
  · subst huu
    simp [u'.2.1, u'.2.2]
  · have hval : u.1 ≠ u'.1 := fun h => huu (Subtype.ext h.symm)
    simp [huu, hval]

/-- `sixJMatrixSymm` is a right inverse of `sixJMatrix`. -/
@[simp]
theorem sixJMatrix_mul_sixJMatrixSymm (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (a b c d : ℕ) :
    sixJMatrix hq ε δ ζ a b c d * sixJMatrixSymm hq ε δ ζ a b c d = 1 := by
  ext v' v
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsum : (∑ u : SixJLeftIndex a b c d,
        sixJSymbol hq ε δ ζ a b c d u.1 v'.1 * sixJSymbolSymm hq ε δ ζ a b c d v.1 u.1) =
      ∑ u ∈ Finset.range (a + b + 1),
        sixJSymbol hq ε δ ζ a b c d u v'.1 * sixJSymbolSymm hq ε δ ζ a b c d v.1 u := by
    refine (Finset.sum_subtype
      ((Finset.range (a + b + 1)).filter fun u =>
        IsClebschGordanTriple a b u ∧ IsClebschGordanTriple u c d)
      (fun u => by
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨Nat.lt_succ_of_le h.1.le_add, h⟩⟩)
      (fun u => sixJSymbol hq ε δ ζ a b c d u v'.1 *
        sixJSymbolSymm hq ε δ ζ a b c d v.1 u)).symm.trans ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hu
    · rfl
    · rw [sixJSymbolSymm_eq_zero_of_not_triple hq ε δ ζ (fun h => hu ⟨h.1, h.2.1⟩), mul_zero]
  rw [sixJMatrix, sixJMatrixSymm]
  simp only [Matrix.of_apply, hsum, sum_sixJSymbol_mul_sixJSymbolSymm]
  by_cases hvv : v' = v
  · subst hvv
    simp [v'.2.1, v'.2.2]
  · have hval : v.1 ≠ v'.1 := fun h => hvv (Subtype.ext h.symm)
    simp [hvv, hval]

/-- The numbers of admissible left and right intermediate weights at total weight `d` coincide. -/
theorem card_sixJLeftIndex_eq_card_sixJRightIndex (a b c d : ℕ) :
    Fintype.card (SixJLeftIndex a b c d) = Fintype.card (SixJRightIndex a b c d) := by
  -- Evaluate at the generic parameter `q = 2` (`2` is nonzero and no positive power of `2` is `1`).
  have h20 : Fact ((2 : ℂ) ≠ 0) := ⟨by norm_num⟩
  have hq2 : IsGenericQuantumParameter (2 : ℂ) :=
    isGenericQuantumParameter_iff.mpr ⟨by norm_num, fun n hn hpow => by
      have hcast : ((2 ^ n : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by simpa using hpow
      have hnat : 2 ^ n = 1 := Nat.cast_injective hcast
      have hle : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      omega⟩
  let e : (SixJLeftIndex a b c d → ℂ) ≃ₗ[ℂ] (SixJRightIndex a b c d → ℂ) :=
    LinearEquiv.ofLinearMap
      (Matrix.toLin' (sixJMatrix hq2 1 1 1 a b c d))
      (Matrix.toLin' (sixJMatrixSymm hq2 1 1 1 a b c d))
      (by rw [← Matrix.toLin'_mul, sixJMatrix_mul_sixJMatrixSymm, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, sixJMatrixSymm_mul_sixJMatrix, Matrix.toLin'_one])
  simpa using e.finrank_eq

end SixJSymbol

/-! ### Explicit `2 × 2` spin-`1/2` evaluation on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at `d = 1` -/

section SpinHalf

variable {q : ℂ} [Fact (q ≠ 0)]

/-- Coordinate functional `(i, j, k)` in the pure-tensor ladder basis of
`L_1^ε ⊗ (L_1^δ ⊗ L_1^ζ)`. -/
private def tripleRightCoord (q : ℂ) [Fact (q ≠ 0)] (ε δ ζ : ℤˣ)
    (i j k : Fin 2) :
    Tensor ℂ (UqSl2 q) (LadderModule q 1 ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ)) →ₗ[ℂ] ℂ :=
  ((Finsupp.lapply (i, (j, k))).comp
    ((basis q 1 ε).tensorProduct ((basis q 1 δ).tensorProduct (basis q 1 ζ))).repr.toLinearMap).comp
    (((TensorProduct.congr (LinearEquiv.refl ℂ _)
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ))).toLinearMap).comp
      (tensorEquiv ℂ (UqSl2 q) (LadderModule q 1 ε) _).toLinearMap)

private theorem tripleRightCoord_tmul (ε δ ζ : ℤˣ) (i j k : Fin 2) (a b c : ℤ) :
    tripleRightCoord q ε δ ζ i j k
        (tmul ℂ (UqSl2 q) (vec q 1 ε a)
          (tmul ℂ (UqSl2 q) (vec q 1 δ b) (vec q 1 ζ c))) =
      (if (i : ℤ) = a then 1 else 0) *
        ((if (j : ℤ) = b then 1 else 0) * (if (k : ℤ) = c then 1 else 0)) := by
  simp only [tripleRightCoord, LinearMap.comp_apply, Finsupp.lapply_apply, LinearEquiv.coe_coe,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, tensorEquiv_tmul,
    Basis.tensorProduct_repr_tmul_apply, basis_repr_vec, smul_eq_mul]
  split_ifs <;> simp_all

private theorem not_isClebschGordanTriple_one_one_one : ¬ IsClebschGordanTriple 1 1 1 := by
  rintro ⟨_, _, _, h⟩
  simp at h

/-- Right-coupled highest vector at `v = 0` (`d = 1`) in `L_1^ε ⊗ (L_1^δ ⊗ L_1^ζ)`. -/
private def rightVecZero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    Tensor ℂ (UqSl2 q) (LadderModule q 1 ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ)) :=
  tensorMap ℂ (UqSl2 q) LinearMap.id
    (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1)))
    (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 0 + 1))
      (vec q 1 (ε * (δ * ζ)) 0))

/-- Right-coupled highest vector at `v = 2` (`d = 1`) in `L_1^ε ⊗ (L_1^δ ⊗ L_1^ζ)`. -/
private def rightVecTwo (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    Tensor ℂ (UqSl2 q) (LadderModule q 1 ε)
      (Tensor ℂ (UqSl2 q) (LadderModule q 1 δ) (LadderModule q 1 ζ)) :=
  tensorMap ℂ (UqSl2 q) LinearMap.id
    (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1)))
    (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 2 + 1))
      (vec q 1 (ε * (δ * ζ)) 0))

private theorem assoc_spinHalf_vec_zero (hq : IsGenericQuantumParameter q)
    (ε δ ζ : ℤˣ) (u : ℕ) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ)
        (tensorMap ℂ (UqSl2 q) (clebschGordanWeightInclusion hq 1 ε 1 δ u) LinearMap.id
          (clebschGordanWeightInclusion hq u (ε * δ) 1 ζ 1 (vec q 1 ((ε * δ) * ζ) 0))) =
      sixJSymbol hq ε δ ζ 1 1 1 1 u 0 • rightVecZero hq ε δ ζ +
        sixJSymbol hq ε δ ζ 1 1 1 1 u 2 • rightVecTwo hq ε δ ζ := by
  rw [assoc_clebschGordanWeightInclusion_vec hq ε δ ζ 1 1 1 1 u 0,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  have hv1 : sixJSymbol hq ε δ ζ 1 1 1 1 u 1 = 0 :=
    sixJSymbol_eq_zero_of_not_triple hq ε δ ζ
      (fun h => not_isClebschGordanTriple_one_one_one h.2.2.1)
  rw [hv1, zero_smul, add_zero]
  have h01 := clebschGordanWeightInclusion_sub_two_mul hq 1 δ 1 ζ
    (⟨1, by omega⟩ : Fin (min 1 1 + 1))
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 0 (δ * ζ)
    (⟨0, by omega⟩ : Fin (min 1 0 + 1))
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 δ 1 ζ
    (⟨0, by omega⟩ : Fin (min 1 1 + 1))
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 2 (δ * ζ)
    (⟨1, by omega⟩ : Fin (min 1 2 + 1))
  dsimp only at h01 h00 h20 h21
  rw [h01, h00, h20, h21]
  rfl

private theorem spinHalfAlt_vec_zero (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1))
      (vec q 0 (ε₁ * ε₂) 0) =
      tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) +
        (-(ε₂ : ℂ) * q) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) := by
  refine (clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    (⟨1, by omega⟩ : Fin (min 1 1 + 1))).trans ?_
  rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
  simp [clebschGordanCoeff_succ, quantumInteger_one hq.sub_inv_ne_zero]

private theorem spinHalfSym_vec_zero (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1))
      (vec q 2 (ε₁ * ε₂) 0) = tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 0) :=
  (clebschGordanInclusion_vec_zero (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    (⟨0, by omega⟩ : Fin (min 1 1 + 1))).trans (by simp [clebschGordanVector_def])

private theorem spinHalfSym_vec_one (hq : IsGenericQuantumParameter q) (ε₁ ε₂ : ℤˣ) :
    clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1))
      (vec q 2 (ε₁ * ε₂) 1) =
      ((ε₂ : ℂ) * q⁻¹) • tmul ℂ (UqSl2 q) (vec q 1 ε₁ 1) (vec q 1 ε₂ 0) +
        tmul ℂ (UqSl2 q) (vec q 1 ε₁ 0) (vec q 1 ε₂ 1) := by
  refine (clebschGordanInclusion_vec (m := 1) (n := 1) (ε := ε₁) (δ := ε₂) hq
    (⟨0, by omega⟩ : Fin (min 1 1 + 1)) 1).trans ?_
  rw [Finset.prod_range_one, clebschGordanVector_def, Finset.sum_range_one]
  simp [quantumInteger_one hq.sub_inv_ne_zero, f_smul_tmul, f_smul_vec, kInv_smul_vec]

private theorem rightVecZero_coords (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    tripleRightCoord q ε δ ζ 0 0 1 (rightVecZero hq ε δ ζ) = 1 ∧
      tripleRightCoord q ε δ ζ 1 0 0 (rightVecZero hq ε δ ζ) = 0 := by
  have hin : clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 0 + 1))
      (vec q 1 (ε * (δ * ζ)) 0) = tmul ℂ (UqSl2 q) (vec q 1 ε 0) (vec q 0 (δ * ζ) 0) :=
    (clebschGordanInclusion_vec_zero (m := 1) (n := 0) (ε := ε) (δ := δ * ζ) hq
      (⟨0, by omega⟩ : Fin (min 1 0 + 1))).trans (by simp [clebschGordanVector_def])
  have hR₀ : rightVecZero hq ε δ ζ =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(ζ : ℂ) * q) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0)) := by
    rw [rightVecZero, hin, tensorMap_tmul, LinearMap.id_apply, spinHalfAlt_vec_zero,
      tmul_add, tmul_smul]
  rw [hR₀, map_add, map_smul, map_add, map_smul, tripleRightCoord_tmul, tripleRightCoord_tmul,
    tripleRightCoord_tmul, tripleRightCoord_tmul]
  simp

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
      (⟨1, by omega⟩ : Fin (min 1 2 + 1))).trans ?_
    rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [clebschGordanCoeff_zero, clebschGordanCoeff_succ, one_smul, Nat.cast_zero,
      sub_zero, Nat.cast_one, sub_self]
    congr 2
    norm_num [quantumInteger_one hq.sub_inv_ne_zero]
  have hR₂ : rightVecTwo hq ε δ ζ =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0)
        (((ζ : ℂ) * q⁻¹) • tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0) +
          tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(δ : ℂ) * (ζ : ℂ) * q * quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) := by
    rw [rightVecTwo, hin, map_add, LinearMapClass.map_smul_of_tower, tensorMap_tmul,
      tensorMap_tmul, LinearMap.id_apply, LinearMap.id_apply, spinHalfSym_vec_one,
      spinHalfSym_vec_zero]
  rw [hR₂]
  simp only [tmul_add, tmul_smul, map_add, map_smul, tripleRightCoord_tmul, smul_eq_mul]
  constructor <;> norm_num

private theorem leftVecZero_assoc (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ)
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 1 1 + 1)))
        LinearMap.id (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 0 1 + 1))
          (vec q 1 ((ε * δ) * ζ) 0))) =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0)) +
        (-(δ : ℂ) * q) •
          tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) := by
  have hin : clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 0 1 + 1))
      (vec q 1 ((ε * δ) * ζ) 0) = tmul ℂ (UqSl2 q) (vec q 0 (ε * δ) 0) (vec q 1 ζ 0) :=
    (clebschGordanInclusion_vec_zero (m := 0) (n := 1) (ε := ε * δ) (δ := ζ) hq
      (⟨0, by omega⟩ : Fin (min 0 1 + 1))).trans (by simp [clebschGordanVector_def])
  rw [hin, tensorMap_tmul, LinearMap.id_apply, spinHalfAlt_vec_zero, add_tmul, ← smul_tmul',
    map_add, LinearMapClass.map_smul_of_tower, assoc_tmul, assoc_tmul]

private theorem leftVecTwo_assoc (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    assoc ℂ (UqSl2 q) (LadderModule q 1 ε) (LadderModule q 1 δ) (LadderModule q 1 ζ)
      (tensorMap ℂ (UqSl2 q) (clebschGordanInclusion hq (⟨0, by omega⟩ : Fin (min 1 1 + 1)))
        LinearMap.id (clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 2 1 + 1))
          (vec q 1 ((ε * δ) * ζ) 0))) =
      tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 1)) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          (((δ : ℂ) * q⁻¹) •
              tmul ℂ (UqSl2 q) (vec q 1 ε 1) (tmul ℂ (UqSl2 q) (vec q 1 δ 0) (vec q 1 ζ 0)) +
            tmul ℂ (UqSl2 q) (vec q 1 ε 0) (tmul ℂ (UqSl2 q) (vec q 1 δ 1) (vec q 1 ζ 0))) := by
  have hin : clebschGordanInclusion hq (⟨1, by omega⟩ : Fin (min 2 1 + 1))
      (vec q 1 ((ε * δ) * ζ) 0) =
      tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 0) (vec q 1 ζ 1) +
        (-(ζ : ℂ) * q ^ 2 / quantumInteger q 2) •
          tmul ℂ (UqSl2 q) (vec q 2 (ε * δ) 1) (vec q 1 ζ 0) := by
    refine (clebschGordanInclusion_vec_zero (m := 2) (n := 1) (ε := ε * δ) (δ := ζ) hq
      (⟨1, by omega⟩ : Fin (min 2 1 + 1))).trans ?_
    rw [clebschGordanVector_def, Finset.sum_range_succ, Finset.sum_range_one]
    simp only [clebschGordanCoeff_zero, clebschGordanCoeff_succ, one_smul, Nat.cast_zero,
      sub_zero, Nat.cast_one, sub_self]
    congr 2
    norm_num [quantumInteger_one hq.sub_inv_ne_zero]
  rw [hin, map_add, LinearMapClass.map_smul_of_tower, tensorMap_tmul, tensorMap_tmul,
    LinearMap.id_apply, LinearMap.id_apply, spinHalfSym_vec_zero, spinHalfSym_vec_one, add_tmul,
    ← smul_tmul', map_add, LinearMapClass.map_smul_of_tower, map_add,
    LinearMapClass.map_smul_of_tower, assoc_tmul, assoc_tmul, assoc_tmul]

/-- Entry `(u = 0, v = 2)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_zero_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 0 2 = (ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 0
  have h01 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ
    (⟨1, by omega⟩ : Fin (min 1 1 + 1))
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 0 (ε * δ) 1 ζ
    (⟨0, by omega⟩ : Fin (min 0 1 + 1))
  dsimp only at h01 h00
  rw [h01, h00, leftVecZero_assoc] at hexp
  have hc := congrArg (tripleRightCoord q ε δ ζ 1 0 0) hexp
  rw [map_add, map_smul, map_add, map_smul, map_smul, (rightVecZero_coords hq ε δ ζ).2,
    (rightVecTwo_coords hq ε δ ζ).2, tripleRightCoord_tmul, tripleRightCoord_tmul] at hc
  simp only [smul_eq_mul] at hc
  norm_num at hc
  have hq0 : q ≠ 0 := hq.ne_zero
  have hδ0 : (δ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr δ.ne_zero
  have hζ0 : (ζ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr ζ.ne_zero
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  have hζ2 : (ζ : ℂ) * (ζ : ℂ) = 1 := by
    rcases Int.units_eq_one_or ζ with rfl | rfl <;> norm_num
  rw [eq_mul_inv_iff_mul_eq₀ hq2]
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hδ0 hζ0) hq0)
  linear_combination -hc - (δ : ℂ) * q * hζ2

/-- Entry `(u = 0, v = 0)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_zero_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 0 0 = -(ζ : ℂ) * (quantumInteger q 2)⁻¹ := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 0
  have h01 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ
    (⟨1, by omega⟩ : Fin (min 1 1 + 1))
  have h00 := clebschGordanWeightInclusion_sub_two_mul hq 0 (ε * δ) 1 ζ
    (⟨0, by omega⟩ : Fin (min 0 1 + 1))
  dsimp only at h01 h00
  rw [h01, h00, leftVecZero_assoc] at hexp
  have hc := congrArg (tripleRightCoord q ε δ ζ 0 0 1) hexp
  rw [map_add, map_smul, map_add, map_smul, map_smul, (rightVecZero_coords hq ε δ ζ).1,
    (rightVecTwo_coords hq ε δ ζ).1, tripleRightCoord_tmul, tripleRightCoord_tmul,
    sixJSymbol_one_one_one_zero_two hq ε δ ζ] at hc
  simp only [smul_eq_mul] at hc
  norm_num at hc
  linear_combination -hc

/-- Entry `(u = 2, v = 2)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_two_two (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 2 2 = ((quantumInteger q 2)⁻¹) ^ 2 := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 2
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ
    (⟨0, by omega⟩ : Fin (min 1 1 + 1))
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 2 (ε * δ) 1 ζ
    (⟨1, by omega⟩ : Fin (min 2 1 + 1))
  dsimp only at h20 h21
  rw [h20, h21, leftVecTwo_assoc] at hexp
  have hc := congrArg (tripleRightCoord q ε δ ζ 1 0 0) hexp
  rw [map_add, map_smul, map_add, map_smul, map_add, map_smul, map_smul,
    (rightVecZero_coords hq ε δ ζ).2, (rightVecTwo_coords hq ε δ ζ).2,
    tripleRightCoord_tmul, tripleRightCoord_tmul, tripleRightCoord_tmul] at hc
  simp only [smul_eq_mul] at hc
  norm_num at hc
  have hq0 : q ≠ 0 := hq.ne_zero
  have hδ0 : (δ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr δ.ne_zero
  have hζ0 : (ζ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr ζ.ne_zero
  have hq2 : quantumInteger q 2 ≠ 0 := quantumInteger_ne_zero hq (by omega)
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hδ0 hζ0) (mul_ne_zero hq0 hq2))
  field_simp [hq0, hq2] at hc ⊢
  linear_combination hc

/-- Entry `(u = 2, v = 0)` of the `2 × 2` spin-`1/2` `6j` matrix on `L_1^ε ⊗ L_1^δ ⊗ L_1^ζ` at
total weight `d = 1`. -/
theorem sixJSymbol_one_one_one_two_zero (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ) :
    sixJSymbol hq ε δ ζ 1 1 1 1 2 0 = 1 - ((quantumInteger q 2)⁻¹) ^ 2 := by
  have hexp := assoc_spinHalf_vec_zero hq ε δ ζ 2
  have h20 := clebschGordanWeightInclusion_sub_two_mul hq 1 ε 1 δ
    (⟨0, by omega⟩ : Fin (min 1 1 + 1))
  have h21 := clebschGordanWeightInclusion_sub_two_mul hq 2 (ε * δ) 1 ζ
    (⟨1, by omega⟩ : Fin (min 2 1 + 1))
  dsimp only at h20 h21
  rw [h20, h21, leftVecTwo_assoc] at hexp
  have hc := congrArg (tripleRightCoord q ε δ ζ 0 0 1) hexp
  rw [map_add, map_smul, map_add, map_smul, map_add, map_smul, map_smul,
    (rightVecZero_coords hq ε δ ζ).1, (rightVecTwo_coords hq ε δ ζ).1,
    tripleRightCoord_tmul, tripleRightCoord_tmul, tripleRightCoord_tmul,
    sixJSymbol_one_one_one_two_two hq ε δ ζ] at hc
  simp only [smul_eq_mul] at hc
  norm_num at hc
  linear_combination -hc

end SpinHalf

end TauCeti.UqSl2
