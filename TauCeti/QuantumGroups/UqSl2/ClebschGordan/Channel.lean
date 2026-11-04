/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Recoupling
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Hom

/-!
# Channel recoupling, coupled ladder bases, and weight-indexed binary Clebsch–Gordan maps

At a generic parameter `q`, a triple tensor product of signed ladder modules of `U_q(sl₂)` carries
two normalized Clebsch–Gordan decompositions linked through `BialgebraModule.assoc` by
`clebschGordanRecouplingEquiv`. This file extracts the channel-level recoupling scalars
`sixJChannel`, constructs the coupled normalized `F`-ladder bases of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` and
`L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)` together with the block-diagonal matrix of `assoc`, and packages binary
Clebsch–Gordan inclusions and projections indexed directly by summand weight via
`IsClebschGordanTriple`.

## Main definitions

* `TauCeti.UqSl2.clebschGordanRecouplingHom`, `TauCeti.UqSl2.sixJChannel`: channel-indexed
  recoupling intertwiners and their Schur scalars.
* `TauCeti.UqSl2.clebschGordanLeftBasis`, `TauCeti.UqSl2.clebschGordanRightBasis`: coupled
  normalized `F`-ladder bases of `(L_m^ε ⊗ L_n^δ) ⊗ L_p^ζ` and `L_m^ε ⊗ (L_n^δ ⊗ L_p^ζ)`.
* `TauCeti.UqSl2.IsClebschGordanTriple`: admissibility predicate for binary Clebsch–Gordan triples.
* `TauCeti.UqSl2.clebschGordanWeightInclusion`, `TauCeti.UqSl2.clebschGordanWeightProjection`:
  weight-indexed binary Clebsch–Gordan inclusions and projections, zero outside admissible triples.
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

/-- `sixJChannel` vanishes whenever the total lowering steps `(i : ℕ) + j` and `(r : ℕ) + s`
differ. -/
theorem sixJChannel_eq_zero_of_add_ne (hq : IsGenericQuantumParameter q) (ε δ ζ : ℤˣ)
    {i : Fin (min m n + 1)} {j : Fin (min (m + n - 2 * (i : ℕ)) p + 1)}
    {r : Fin (min n p + 1)} {s : Fin (min m (n + p - 2 * (r : ℕ)) + 1)}
    (hne : (i : ℕ) + (j : ℕ) ≠ (r : ℕ) + (s : ℕ)) : sixJChannel hq ε δ ζ i j r s = 0 := by
  have := i.isLt; have := j.isLt; have := r.isLt; have := s.isLt
  exact homScalar_eq_zero_of_ne hq (.inl (by omega)) _

/-- Expansion of the associator on the normalized `F`-ladder vectors (`k : ℤ`) of a left-coupled
channel into right-coupled channels. -/
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
  set y := clebschGordanRecouplingEquiv hq (Pi.single i (Pi.single j (vec q _ ((ε * δ) * ζ) k)))
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  conv_lhs => rw [← Finset.univ_sum_single (y r)]
  rw [← LinearMap.single_apply (R := ℂ), map_sum, map_sum]
  simp only [LinearMap.single_apply, clebschGordanRightEquiv_single]
  refine Finset.sum_congr rfl fun s _ => ?_
  dsimp only [y]; rw [← clebschGordanRecouplingHom_apply, clebschGordanRecouplingHom_vec,
    LinearMapClass.map_smul_of_tower, LinearMapClass.map_smul_of_tower]

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

end Channel

/-! ### Admissible Clebsch–Gordan triples and weight-indexed binary intertwiners -/

section WeightBinary

/-- A natural number `c` is an admissible Clebsch–Gordan summand highest weight for `L_a^ε ⊗ L_b^δ`
if `a`, `b`, `c` satisfy the triangle inequalities and `a + b - c` is even. -/
def IsClebschGordanTriple (a b c : ℕ) : Prop :=
  a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c)

/-- Unfolded characterization of `IsClebschGordanTriple`. -/
theorem isClebschGordanTriple_iff (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ a ≤ b + c ∧ b ≤ a + c ∧ c ≤ a + b ∧ Even (a + b - c) := Iff.rfl

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

/-- Every lowering step `j : Fin (min a b + 1)` yields an admissible weight `a + b - 2 * j`. -/
theorem isClebschGordanTriple_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    IsClebschGordanTriple a b (a + b - 2 * (j : ℕ)) := by
  have := j.isLt; exact ⟨by omega, by omega, by omega, ⟨j, by omega⟩⟩

/-- Equivalence between admissible Clebsch–Gordan summand weights `c` in `L_a^ε ⊗ L_b^δ` and
lowering-step indices `j : Fin (min a b + 1)` via `c = a + b - 2j` and `j = (a + b - c) / 2`. -/
def clebschGordanTripleEquiv (a b : ℕ) :
    { c : ℕ // IsClebschGordanTriple a b c } ≃ Fin (min a b + 1) where
  toFun c := ⟨(a + b - c.1) / 2, by obtain ⟨_, _, _, _, _⟩ := c.2; omega⟩
  invFun j := ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩
  left_inv c := by obtain ⟨_, _, _, _, _⟩ := c.2; ext; dsimp only; omega
  right_inv j := by have := j.isLt; ext; dsimp only; omega

/-- Recovery of `c = a + b - 2 * j` from `j = clebschGordanTripleEquiv a b ⟨c, h⟩`. -/
theorem clebschGordanTriple_sub_eq {a b c : ℕ} (h : IsClebschGordanTriple a b c) :
    c = a + b - 2 * (clebschGordanTripleEquiv a b ⟨c, h⟩ : ℕ) :=
  (congrArg Subtype.val ((clebschGordanTripleEquiv a b).symm_apply_apply ⟨c, h⟩)).symm

/-- `clebschGordanTripleEquiv` sends `a + b - 2 * j` back to `j`. -/
@[simp] theorem clebschGordanTripleEquiv_sub_two_mul {a b : ℕ} (j : Fin (min a b + 1)) :
    clebschGordanTripleEquiv a b ⟨a + b - 2 * (j : ℕ), isClebschGordanTriple_sub_two_mul j⟩ = j :=
  (clebschGordanTripleEquiv a b).apply_symm_apply j

/-- `IsClebschGordanTriple a b c` holds iff `c = a + b - 2 * j` for some `j : Fin (min a b + 1)`. -/
theorem isClebschGordanTriple_iff_exists_fin (a b c : ℕ) :
    IsClebschGordanTriple a b c ↔ ∃ j : Fin (min a b + 1), c = a + b - 2 * (j : ℕ) :=
  ⟨fun h => ⟨clebschGordanTripleEquiv a b ⟨c, h⟩, clebschGordanTriple_sub_eq h⟩,
    fun ⟨j, hj⟩ => hj ▸ isClebschGordanTriple_sub_two_mul j⟩

/-- Summing a function vanishing outside admissible Clebsch–Gordan triples over
`Finset.range (a + b + 1)` equals summing over lowering steps `j : Fin (min a b + 1)`. -/
theorem sum_range_of_not_isClebschGordanTriple {M : Type*} [AddCommMonoid M] (a b : ℕ)
    (f : ℕ → M) (hf : ∀ c, ¬ IsClebschGordanTriple a b c → f c = 0) :
    ∑ c ∈ Finset.range (a + b + 1), f c = ∑ j : Fin (min a b + 1), f (a + b - 2 * (j : ℕ)) := by
  have hfilter : ∑ c ∈ Finset.range (a + b + 1), f c =
      ∑ c ∈ (Finset.range (a + b + 1)).filter (IsClebschGordanTriple a b), f c := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun c _ => by
      by_cases h : IsClebschGordanTriple a b c <;> simp [h, hf]
  rw [hfilter]
  refine (Finset.sum_nbij (fun j : Fin (min a b + 1) => a + b - 2 * (j : ℕ))
    (fun j _ => by
      have := j.isLt; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, isClebschGordanTriple_sub_two_mul j⟩)
    (fun j₁ _ j₂ _ h => by have := j₁.isLt; have := j₂.isLt; dsimp only at h; ext; omega)
    (fun c hc => ?_) fun _ _ => rfl).symm
  simp only [Finset.mem_coe, Finset.mem_filter] at hc
  exact ⟨clebschGordanTripleEquiv a b ⟨c, hc.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _),
    (clebschGordanTriple_sub_eq hc.2).symm⟩

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
    clebschGordanWeightInclusion hq a ε b δ c = 0 := by simp [clebschGordanWeightInclusion, h]

/-- `clebschGordanWeightProjection` vanishes outside admissible Clebsch–Gordan triples. -/
theorem clebschGordanWeightProjection_of_not_triple (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : ¬ IsClebschGordanTriple a b c) :
    clebschGordanWeightProjection hq a ε b δ c = 0 := by simp [clebschGordanWeightProjection, h]

/-- At `c = a + b - 2 * j`, `clebschGordanWeightInclusion` agrees with `clebschGordanInclusion`. -/
@[simp] theorem clebschGordanWeightInclusion_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightInclusion hq a ε b δ (a + b - 2 * (j : ℕ)) =
      clebschGordanInclusion hq j :=
  LadderModule.hom_ext hq <| by
    simp [clebschGordanWeightInclusion, isClebschGordanTriple_sub_two_mul j]

/-- `clebschGordanWeightProjection` is a left inverse to `clebschGordanWeightInclusion` on any
admissible triple. -/
theorem clebschGordanWeightProjection_comp_inclusion_self (hq : IsGenericQuantumParameter q)
    {a b c : ℕ} (ε δ : ℤˣ) (h : IsClebschGordanTriple a b c) :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  simp only [clebschGordanWeightProjection, clebschGordanWeightInclusion, dite_eq_left h,
    LinearMap.comp_apply, LinearEquiv.coe_coe, clebschGordanProjection_inclusion_self,
    LinearMap.id_apply]
  rw [← LinearEquiv.trans_apply, congr_trans, congr_refl]; rfl

/-- Weight-indexed Clebsch–Gordan inclusions and projections at distinct weights are orthogonal. -/
theorem clebschGordanWeightProjection_comp_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {a b c c' : ℕ} (ε δ : ℤˣ) (hne : c ≠ c') :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c') = 0 :=
  hom_eq_zero_of_ne_left hq hne.symm _

/-- Combined orthogonality formula for weight-indexed binary Clebsch–Gordan maps. -/
theorem clebschGordanWeightProjection_comp_inclusion (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (c c' : ℕ) :
    (clebschGordanWeightProjection hq a ε b δ c).comp
      (clebschGordanWeightInclusion hq a ε b δ c') =
      if h : c = c' ∧ IsClebschGordanTriple a b c then
        (LadderModule.congr h.1.symm rfl).toLinearMap
      else 0 := by
  split_ifs with h
  · rcases h with ⟨rfl, hc⟩
    simpa using clebschGordanWeightProjection_comp_inclusion_self hq ε δ hc
  · by_cases hcc : c = c'
    · subst hcc; simp [clebschGordanWeightProjection_of_not_triple hq ε δ fun hc => h ⟨rfl, hc⟩]
    · exact clebschGordanWeightProjection_comp_inclusion_of_ne hq ε δ hcc

/-- At `c = a + b - 2 * j`, `clebschGordanWeightProjection` agrees with
`clebschGordanProjection`. -/
@[simp] theorem clebschGordanWeightProjection_sub_two_mul (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) (j : Fin (min a b + 1)) :
    clebschGordanWeightProjection hq a ε b δ (a + b - 2 * (j : ℕ)) =
      clebschGordanProjection hq j := by
  refine LinearMap.ext fun x => ?_
  conv_lhs => rw [← sum_clebschGordanInclusion_projection hq x]
  conv_rhs => rw [← sum_clebschGordanInclusion_projection hq x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases eq_or_ne i j with rfl | hij
  · simpa using congrArg (· (clebschGordanProjection hq i x))
      (clebschGordanWeightProjection_comp_inclusion_self hq ε δ
        (isClebschGordanTriple_sub_two_mul i))
  · have hne : a + b - 2 * (j : ℕ) ≠ a + b - 2 * (i : ℕ) := by
      have := i.isLt; have := j.isLt; exact fun h => hij (Fin.ext (by omega))
    simpa [clebschGordanProjection_inclusion_of_ne hq (Ne.symm hij)] using
      congrArg (· (clebschGordanProjection hq i x))
        (clebschGordanWeightProjection_comp_inclusion_of_ne (a := a) (b := b) hq ε δ hne)

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
        (LadderModule.congr hc.symm rfl).toLinearMap := by subst hc; simp

/-- Transporting the summand weight of `clebschGordanWeightProjection` along `c = c'`. -/
theorem clebschGordanWeightProjection_congr_right (hq : IsGenericQuantumParameter q)
    (a : ℕ) (ε : ℤˣ) (b : ℕ) (δ : ℤˣ) {c c' : ℕ} (hc : c = c') :
    clebschGordanWeightProjection hq a ε b δ c' =
      (LadderModule.congr hc rfl).toLinearMap.comp
        (clebschGordanWeightProjection hq a ε b δ c) := by subst hc; simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightInclusion`. -/
theorem tensorMap_congr_comp_clebschGordanWeightInclusion (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap).comp
      (clebschGordanWeightInclusion hq a ε₁ b δ₁ c) =
    (clebschGordanWeightInclusion hq a' ε₂ b' δ₂ c).comp
      (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap := by
  subst ha hb hε hδ; simp

/-- `LadderModule.congr` commutes past `clebschGordanWeightProjection`. -/
theorem clebschGordanWeightProjection_comp_tensorMap_congr (hq : IsGenericQuantumParameter q)
    {a a' b b' : ℕ} (ha : a = a') (hb : b = b')
    {ε₁ ε₂ δ₁ δ₂ : ℤˣ} (hε : ε₁ = ε₂) (hδ : δ₁ = δ₂) (c : ℕ) :
    (clebschGordanWeightProjection hq a' ε₂ b' δ₂ c).comp
      (tensorMap ℂ (UqSl2 q) (LadderModule.congr ha hε).toLinearMap
        (LadderModule.congr hb hδ).toLinearMap) =
    (LadderModule.congr rfl (congrArg₂ (· * ·) hε hδ)).toLinearMap.comp
      (clebschGordanWeightProjection hq a ε₁ b δ₁ c) := by
  subst ha hb hε hδ; simp

end WeightBinary

end TauCeti.UqSl2
