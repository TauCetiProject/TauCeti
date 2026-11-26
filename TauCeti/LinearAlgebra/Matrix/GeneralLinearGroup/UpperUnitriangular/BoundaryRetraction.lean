/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZMod
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Center
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.Transvection
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperUnitriangular.TwoBoundary
import Mathlib.Tactic.NoncommRing

/-!
# Boundary retractions of the two-boundary subgroups and their stabilizers

Index `(n + 1) × (n + 1)` matrices over a ring `R` by `0, …, n`, let `U = Uₙ₊₁(R)` be the
upper-unitriangular group, `Z` its centre (the corner transvections `e₀ₙ(t)`), and `P = P_(r,s)`
the two-boundary subgroup: the matrices that differ from the identity only in row `0` at columns
`j ≥ n - s` and in column `n` at rows `i ≤ r`.

For a row vector `u` and a column vector `v`, Harpaz and Wittenberg consider

```text
ρ_(u,v)(Q) = u (Q - 1) v.
```

When `r + s < n`, the product of two matrices supported where `Q - 1` is vanishes, so `ρ_(u,v)` is
a homomorphism `P → (R, +)` (`TauCeti.UpperUnitriangularGroup.twoBoundaryRetraction`). It sends
the transvection `e_ij(t)` of `P` to `u i * t * v j`, the row vector staying on the left. Over a
commutative ring it restricts to the corner coordinate on `Z ≅ R`, so is a retraction of `P` onto
`Z`, exactly when `u 0 * v n = 1`. Two normalized pairs (`u 0 = v n = 1`) give the same map exactly
when the rows agree at the indices `≤ r` and the columns at the indices `≥ n - s`. Over `ℤ/m`, in
particular over `𝔽_p`, every retraction of `P` onto `Z` is `ρ_(u,v)` for a normalized pair.

Conjugation by `M ∈ U` carries `ρ_(u,v)` to `ρ_(uM, M⁻¹v)`. Let `S` be the stabilizer of
`ρ_(u,v)` under conjugation (`TauCeti.UpperUnitriangularGroup.twoBoundaryStabilizer`). For a
normalized pair, `M ∈ S` exactly when the row `u (M - 1)` vanishes at the indices `≤ r` and the
column `(M - 1) v` vanishes at the indices `≥ n - s`. When moreover `n ≤ r + s + 1`, every index is
in one of these two ranges, so `u (M - 1) (N - 1) v = 0` for `M, N ∈ S`, and
`ρ'(M) = u (M - 1) v` is a homomorphism `S → (R, +)`
(`TauCeti.UpperUnitriangularGroup.twoBoundaryStabilizerRetraction`). It extends `ρ_(u,v)` and
restricts to the corner coordinate on `Z`. Its kernel therefore maps isomorphically onto the image
of `S` in `U/Z`, and every homomorphism into `U/Z` with values in that image lifts to `U`, with the
same kernel. This is the case of an equivariantly split boundary sequence in Harpaz and
Wittenberg's refined lifting through `P_(r,s)` for `n = r + s + 1`.

## Main declarations

* `TauCeti.UpperUnitriangularGroup.transvection_mem_twoBoundarySubgroup`: the transvections at
  the two-boundary positions lie in `P_(r,s)`.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryRetraction`: the homomorphism
  `ρ_(u,v) : P_(r,s) → R` for `r + s < n`.
* `TauCeti.UpperUnitriangularGroup.forall_mem_center_twoBoundaryRetraction_iff`: `ρ_(u,v)` is the
  corner coordinate on `Z` exactly when `u 0 * v n = 1`.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryRetraction_eq_iff`: when two normalized pairs give
  the same retraction.
* `TauCeti.UpperUnitriangularGroup.exists_twoBoundaryRetraction_eq`: over `ℤ/m` every retraction
  of `P_(r,s)` onto `Z` is `ρ_(u,v)` for a normalized pair.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryStabilizer` and
  `TauCeti.UpperUnitriangularGroup.mem_twoBoundaryStabilizer_iff`: the stabilizer `S` of
  `ρ_(u,v)` and its description by two support conditions.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryStabilizerRetraction`: the homomorphism
  `ρ' : S → R` for `n ≤ r + s + 1`.
* `TauCeti.UpperUnitriangularGroup.exists_lift_of_range_le_map_twoBoundaryStabilizer`: a
  homomorphism into `U/Z` with values in the image of `S` lifts to `U` with the same kernel.

## References

* Y. Harpaz and O. Wittenberg, *The Massey vanishing conjecture for number fields*, Duke Math. J.
  172 (2023), §5, (5.5) and the proof of Proposition 5.3.
-/

public section

open Matrix

namespace TauCeti.UpperUnitriangularGroup

variable {R : Type*} {n r s : ℕ}

section Ring

variable [Ring R]

/-! ### Values of `u (Q - 1) v` -/

/-- The value of `u (Q - 1) v` at a transvection `Q = e_ij(t)`. -/
private theorem dotProduct_transvection_sub_one_mulVec {i j : Fin (n + 1)} (hij : i < j) (t : R)
    (u v : Fin (n + 1) → R) :
    u ⬝ᵥ (((((transvection hij t : upperUnitriangularGroup (Fin (n + 1)) R) :
      GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) = u i * t * v j := by
  rw [coe_transvection, coe_transvectionUnit_eq_one_add_single, add_sub_cancel_left,
    single_mulVec]
  simp [dotProduct, Function.update_apply, mul_assoc]

/-- The value of `u (M - 1) v` at a central element `M = 1 + t E₀ₙ` of `Uₙ₊₁(R)`, `n ≥ 1`. -/
private theorem dotProduct_sub_one_mulVec_of_mem_center (hn : 0 < n)
    {M : upperUnitriangularGroup (Fin (n + 1)) R}
    (hM : M ∈ Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) (u v : Fin (n + 1) → R) :
    u ⬝ᵥ ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
      u 0 * ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) *
        v (Fin.last n) := by
  conv_lhs => rw [(isUpperUnitriangular M).eq_one_add_single_zero_last hn (mem_center_iff.1 hM)]
  rw [add_sub_cancel_left, single_mulVec]
  simp [dotProduct, Function.update_apply, mul_assoc]

/-- The corner transvection `e₀ₙ(t)` is central in `Uₙ₊₁(R)`. -/
private theorem transvection_zero_last_mem_center (h0 : (0 : Fin (n + 1)) < Fin.last n) (t : R) :
    transvection h0 t ∈ Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) := by
  rw [mem_center_iff]
  intro i j hij hc
  rw [coe_transvection, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
    Matrix.one_apply_ne hij.ne, single_apply_of_ne _ _ _ _ _ fun h ↦ hc ⟨h.1.symm, h.2.symm⟩,
    add_zero]

/-- A transvection `e_ij(t)` lies in the two-boundary subgroup `P_(r,s)` when `(i, j)` is a
two-boundary position: in row `0` at a column `j ≥ n - s`, or in column `n` at a row `i ≤ r`. -/
theorem transvection_mem_twoBoundarySubgroup {i j : Fin (n + 1)} (hij : i < j)
    (hP : (i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r)) (t : R) :
    transvection hij t ∈ twoBoundarySubgroup (R := R) n r s := by
  rw [mem_twoBoundarySubgroup_iff, isTwoBoundary_iff]
  intro a b hab
  rw [coe_transvection, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
    add_ne_left] at hab
  obtain ⟨rfl, rfl⟩ : i = a ∧ j = b := by
    by_contra hne
    exact hab (single_apply_of_ne _ _ _ _ _ hne)
  exact ⟨hij, hP⟩

/-- For `s < n`, a column `j ≥ n - s` comes after the column `0`. -/
private theorem zero_lt_of_le_add (hs : s < n) {j : Fin (n + 1)} (hj : n ≤ (j : ℕ) + s) :
    (0 : Fin (n + 1)) < j :=
  Fin.lt_def.2 (by simp only [Fin.val_zero]; omega)

/-- For `r < n`, a row `i ≤ r` comes before the row `n`. -/
private theorem lt_last_of_le (hr : r < n) {i : Fin (n + 1)} (hi : (i : ℕ) ≤ r) :
    i < Fin.last n :=
  Fin.lt_def.2 (by simp only [Fin.val_last]; omega)

/-- Two normalized pairs give the same values `u (Q - 1) v` on `P_(r,s)`, for `r, s < n`, exactly
when the rows agree at the indices `≤ r` and the columns at the indices `≥ n - s`. -/
private theorem forall_dotProduct_eq_iff (hr : r < n) (hs : s < n) {u v u' v' : Fin (n + 1) → R}
    (hu : u 0 = 1) (hv : v (Fin.last n) = 1) (hu' : u' 0 = 1) (hv' : v' (Fin.last n) = 1) :
    (∀ Q ∈ twoBoundarySubgroup (R := R) n r s,
      u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
        u' ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v')) ↔
      (∀ i : Fin (n + 1), (i : ℕ) ≤ r → u i = u' i) ∧
        ∀ j : Fin (n + 1), n ≤ (j : ℕ) + s → v j = v' j := by
  constructor
  · intro hQ
    refine ⟨fun i hi ↦ ?_, fun j hj ↦ ?_⟩
    · -- Evaluate at `e_in(1)`; the row `0` is normalized.
      rcases eq_or_ne i 0 with rfl | -
      · rw [hu, hu']
      have hP : (i = 0 ∧ n ≤ ((Fin.last n : Fin (n + 1)) : ℕ) + s) ∨
          (Fin.last n = Fin.last n ∧ (i : ℕ) ≤ r) := Or.inr ⟨rfl, hi⟩
      have := hQ _ (transvection_mem_twoBoundarySubgroup (lt_last_of_le hr hi) hP 1)
      rw [dotProduct_transvection_sub_one_mulVec, dotProduct_transvection_sub_one_mulVec, hv,
        hv'] at this
      simpa only [mul_one] using this
    · -- Evaluate at `e₀ⱼ(1)`; the column `n` is normalized.
      rcases eq_or_ne j (Fin.last n) with rfl | -
      · rw [hv, hv']
      have hP : ((0 : Fin (n + 1)) = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (0 : ℕ) ≤ r) :=
        Or.inl ⟨rfl, hj⟩
      have := hQ _ (transvection_mem_twoBoundarySubgroup (zero_lt_of_le_add hs hj) hP 1)
      rw [dotProduct_transvection_sub_one_mulVec, dotProduct_transvection_sub_one_mulVec, hu,
        hu'] at this
      simpa only [one_mul, mul_one] using this
  · -- Every entry of `Q - 1` off the two-boundary positions vanishes, and at those positions the
    -- relevant coordinates of the two pairs agree.
    rintro ⟨hrow, hcol⟩ Q hQ
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hij : ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i j
    · simp [hij]
    obtain ⟨-, ⟨rfl, hj⟩ | ⟨rfl, hi⟩⟩ :=
      isTwoBoundary_iff.1 (mem_twoBoundarySubgroup_iff.1 hQ) i j hij
    · rw [hcol j hj, hu, hu']
    · rw [hrow i hi, hcol (Fin.last n) (by simp only [Fin.val_last]; omega)]

/-! ### The boundary retractions `ρ_(u,v)` -/

/-- **The boundary retraction** `ρ_(u,v)(Q) = u (Q - 1) v` of Harpaz and Wittenberg, for a row
vector `u` and a column vector `v`, as a homomorphism from the two-boundary subgroup `P_(r,s)` to
`(R, +)` when `r + s < n`. It is the corner coordinate on the centre exactly when
`u 0 * v n = 1` (`forall_mem_center_twoBoundaryRetraction_iff`), and over `ℤ/m` every retraction
of `P_(r,s)` onto the centre is of this form (`exists_twoBoundaryRetraction_eq`). -/
def twoBoundaryRetraction (h : r + s < n) (u v : Fin (n + 1) → R) :
    twoBoundarySubgroup (R := R) n r s →* Multiplicative R where
  toFun Q := Multiplicative.ofAdd
    (u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v))
  map_one' := by simp
  map_mul' Q Q' := by
    rw [← ofAdd_add, ← dotProduct_add, ← add_mulVec]
    congr 3
    set A := ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    set B := ((Q' : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hAB : (A - 1) * (B - 1) = 0 :=
      (mem_twoBoundarySubgroup_iff.1 Q.property).sub_one_mul_sub_one_eq_zero h
        (mem_twoBoundarySubgroup_iff.1 Q'.property)
    calc (((Q * Q' : twoBoundarySubgroup (R := R) n r s) : GL (Fin (n + 1)) R) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1 = A - 1 + (B - 1) + (A - 1) * (B - 1) := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul]
          noncomm_ring
      _ = A - 1 + (B - 1) := by rw [hAB, add_zero]

variable (h : r + s < n) (u v : Fin (n + 1) → R)

/-- The value of `ρ_(u,v)` at `Q` is `u (Q - 1) v`. -/
@[simp]
theorem toAdd_twoBoundaryRetraction_apply (Q : twoBoundarySubgroup (R := R) n r s) :
    (twoBoundaryRetraction h u v Q).toAdd =
      u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) :=
  (rfl)

/-- The value of `ρ_(u,v)` at a transvection `e_ij(t)` of `P_(r,s)` is `u i * t * v j`. In
particular `ρ_(u,v)(e_in(t)) = u i * t * v n` and `ρ_(u,v)(e₀ⱼ(t)) = u 0 * t * v j`. -/
@[simp]
theorem twoBoundaryRetraction_transvection {i j : Fin (n + 1)} (hij : i < j)
    (hP : (i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r)) (t : R) :
    twoBoundaryRetraction h u v
        ⟨transvection hij t, transvection_mem_twoBoundarySubgroup hij hP t⟩ =
      Multiplicative.ofAdd (u i * t * v j) :=
  congrArg Multiplicative.ofAdd (dotProduct_transvection_sub_one_mulVec hij t u v)

/-- On the centre, `ρ_(u,v)` multiplies the corner entry by `u 0` on the left and `v n` on the
right. -/
theorem toAdd_twoBoundaryRetraction_of_mem_center {Q : twoBoundarySubgroup (R := R) n r s}
    (hQ : (Q : upperUnitriangularGroup (Fin (n + 1)) R) ∈
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) :
    (twoBoundaryRetraction h u v Q).toAdd =
      u 0 * ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) *
        v (Fin.last n) :=
  dotProduct_sub_one_mulVec_of_mem_center (by omega) hQ u v

variable {h u v}

/-- **Equality of boundary retractions.** Two normalized pairs, `u 0 = v n = 1` and
`u' 0 = v' n = 1`, give the same retraction `ρ_(u,v) = ρ_(u',v')` exactly when `u` and `u'` agree
at the indices `≤ r` and `v` and `v'` agree at the indices `≥ n - s`. -/
theorem twoBoundaryRetraction_eq_iff {u' v' : Fin (n + 1) → R} (hu : u 0 = 1)
    (hv : v (Fin.last n) = 1) (hu' : u' 0 = 1) (hv' : v' (Fin.last n) = 1) :
    twoBoundaryRetraction h u v = twoBoundaryRetraction h u' v' ↔
      (∀ i : Fin (n + 1), (i : ℕ) ≤ r → u i = u' i) ∧
        ∀ j : Fin (n + 1), n ≤ (j : ℕ) + s → v j = v' j := by
  rw [← forall_dotProduct_eq_iff (by omega) (by omega) hu hv hu' hv', DFunLike.ext_iff,
    Subtype.forall]
  exact forall₂_congr fun Q hQ ↦ by
    rw [← Multiplicative.toAdd.injective.eq_iff, toAdd_twoBoundaryRetraction_apply,
      toAdd_twoBoundaryRetraction_apply]

end Ring

section CommRing

variable [CommRing R] (h : r + s < n) (u v : Fin (n + 1) → R)

/-- **`ρ_(u,v)` is a retraction onto the centre exactly when `u 0 * v n = 1`**: it agrees with the
corner coordinate on the centre `Z ≅ R` of `Uₙ₊₁(R)`, which lies in `P_(r,s)`, exactly when
`u 0 * v n = 1`. -/
theorem forall_mem_center_twoBoundaryRetraction_iff :
    (∀ Q : twoBoundarySubgroup (R := R) n r s,
      (Q : upperUnitriangularGroup (Fin (n + 1)) R) ∈
          Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) →
        (twoBoundaryRetraction h u v Q).toAdd =
          ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n)) ↔
      u 0 * v (Fin.last n) = 1 := by
  constructor
  · -- Evaluate at the central transvection `e₀ₙ(1)`.
    intro hQ
    have h0 : (0 : Fin (n + 1)) < Fin.last n :=
      Fin.lt_def.2 (by simp only [Fin.val_zero, Fin.val_last]; omega)
    have hP : ((0 : Fin (n + 1)) = 0 ∧ n ≤ ((Fin.last n : Fin (n + 1)) : ℕ) + s) ∨
        (Fin.last n = Fin.last n ∧ ((0 : Fin (n + 1)) : ℕ) ≤ r) := Or.inr ⟨rfl, by simp⟩
    have := hQ ⟨_, transvection_mem_twoBoundarySubgroup h0 hP 1⟩
      (transvection_zero_last_mem_center h0 1)
    rw [twoBoundaryRetraction_transvection h u v h0 hP, toAdd_ofAdd, mul_one] at this
    rw [this, coe_transvection, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
      Matrix.one_apply_ne h0.ne, single_apply_same, zero_add]
  · intro huv Q hQ
    rw [toAdd_twoBoundaryRetraction_of_mem_center h u v hQ, mul_right_comm, huv, one_mul]

end CommRing

/-! ### Every retraction over `ℤ/m` is a boundary retraction -/

/-- A coordinate vector `(c, a, b)` is the product of the vectors with a single nonzero
coordinate. -/
private theorem eq_ofAdd_mul_prod_mul_prod [AddCommMonoid R]
    (x : Multiplicative (R × (Fin s → R) × (Fin r → R))) :
    x = Multiplicative.ofAdd (x.toAdd.1, 0, 0) *
      (∏ k, Multiplicative.ofAdd (0, Pi.single k (x.toAdd.2.1 k), 0)) *
        ∏ k, Multiplicative.ofAdd (0, 0, Pi.single k (x.toAdd.2.2 k)) := by
  refine Multiplicative.toAdd.injective ?_
  simp only [toAdd_mul, toAdd_prod, toAdd_ofAdd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp [Prod.fst_sum, Prod.snd_sum, Finset.univ_sum_single]

section HomExt

variable [Ring R] (h : r + s < n)

/-- The coordinates of the corner transvection `e₀ₙ(t)` are `(t, 0, 0)`. -/
private theorem twoBoundaryEquiv_transvection_corner (t : R) :
    Multiplicative.ofAdd (t, 0, 0) = twoBoundaryEquiv h ⟨_,
      transvection_mem_twoBoundarySubgroup (lt_last_of_le (i := 0) (r := r) (by omega)
        (by simp)) (Or.inr ⟨rfl, by simp⟩) t⟩ := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_twoBoundaryEquiv_apply]
  refine Prod.ext ?_ (Prod.ext (funext fun k ↦ ?_) (funext fun k ↦ ?_)) <;>
    simp only [toAdd_ofAdd, coe_transvection, coe_transvectionUnit_eq_one_add_single,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.zero_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_last] <;>
    split_ifs <;> first | (exfalso; omega) | simp_all

/-- The coordinates of the first-row transvection `e₀,ₙ₋ₛ₊ₖ(t)` are `(0, tδₖ, 0)`. -/
private theorem twoBoundaryEquiv_transvection_row (k : Fin s) (t : R) :
    Multiplicative.ofAdd (0, Pi.single k t, 0) = twoBoundaryEquiv h ⟨_,
      transvection_mem_twoBoundarySubgroup (zero_lt_of_le_add (j := ⟨n - s + k, by omega⟩)
        (by omega) (by simp only; omega)) (Or.inl ⟨rfl, by simp only; omega⟩) t⟩ := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_twoBoundaryEquiv_apply]
  refine Prod.ext ?_ (Prod.ext (funext fun k' ↦ ?_) (funext fun k' ↦ ?_)) <;>
    simp only [toAdd_ofAdd, coe_transvection, coe_transvectionUnit_eq_one_add_single,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.single_apply, Pi.zero_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_last] <;>
    split_ifs <;> first | (exfalso; omega) | simp_all

/-- The coordinates of the last-column transvection `eₖ₊₁,ₙ(t)` are `(0, 0, tδₖ)`. -/
private theorem twoBoundaryEquiv_transvection_col (k : Fin r) (t : R) :
    Multiplicative.ofAdd (0, 0, Pi.single k t) = twoBoundaryEquiv h ⟨_,
      transvection_mem_twoBoundarySubgroup (lt_last_of_le (i := ⟨k + 1, by omega⟩) (r := r)
        (by omega) (by simp only; omega)) (Or.inr ⟨rfl, by simp only; omega⟩) t⟩ := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_twoBoundaryEquiv_apply]
  refine Prod.ext ?_ (Prod.ext (funext fun k' ↦ ?_) (funext fun k' ↦ ?_)) <;>
    simp only [toAdd_ofAdd, coe_transvection, coe_transvectionUnit_eq_one_add_single,
      Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.single_apply, Pi.zero_apply,
      Fin.ext_iff, Fin.val_zero, Fin.val_last] <;>
    split_ifs <;> first | (exfalso; omega) | simp_all

/-- For `r + s < n`, an element of `P_(r,s)` with coordinates `(c, a, b)` is the product of the
transvections `e₀ₙ(c)`, `e₀,ₙ₋ₛ₊ₖ(a k)` and `eₖ₊₁,ₙ(b k)`. Hence two homomorphisms from `P_(r,s)` to
a commutative monoid that agree on the transvections at the two-boundary positions are equal. -/
private theorem twoBoundary_hom_ext {M : Type*} [CommMonoid M] (h : r + s < n)
    {f₁ f₂ : twoBoundarySubgroup (R := R) n r s →* M}
    (hf : ∀ (i j : Fin (n + 1)) (hij : i < j)
      (hP : (i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r)) (t : R),
      f₁ ⟨_, transvection_mem_twoBoundarySubgroup hij hP t⟩ =
        f₂ ⟨_, transvection_mem_twoBoundarySubgroup hij hP t⟩) : f₁ = f₂ := by
  have hg : f₁.comp (twoBoundaryEquiv h).symm.toMonoidHom =
      f₂.comp (twoBoundaryEquiv h).symm.toMonoidHom := by
    refine MonoidHom.ext fun x ↦ ?_
    rw [eq_ofAdd_mul_prod_mul_prod x, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod,
      map_prod, map_prod]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      twoBoundaryEquiv_transvection_corner h, twoBoundaryEquiv_transvection_row h,
      twoBoundaryEquiv_transvection_col h, MulEquiv.symm_apply_apply]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (hf _ _ _ ?_ _)
      (Finset.prod_congr rfl fun k _ ↦ hf _ _ _ ?_ _))
      (Finset.prod_congr rfl fun k _ ↦ hf _ _ _ ?_ _)
    · exact Or.inr ⟨rfl, by simp⟩
    · exact Or.inl ⟨rfl, by simp only; omega⟩
    · exact Or.inr ⟨rfl, by simp only; omega⟩
  ext Q
  simpa using congrArg (· (twoBoundaryEquiv h Q)) hg

end HomExt

section ZMod

variable {m : ℕ}

/-- Over `ℤ/m` a homomorphism `f : P_(r,s) → ℤ/m` is linear along each root line:
`f (e_ij(t)) = t * f (e_ij(1))`, since `t ↦ f (e_ij(t))` is additive. -/
private theorem toAdd_apply_transvection
    (f : twoBoundarySubgroup (R := ZMod m) n r s →* Multiplicative (ZMod m))
    {i j : Fin (n + 1)} (hij : i < j)
    (hP : (i = 0 ∧ n ≤ (j : ℕ) + s) ∨ (j = Fin.last n ∧ (i : ℕ) ≤ r)) (t : ZMod m) :
    (f ⟨_, transvection_mem_twoBoundarySubgroup hij hP t⟩).toAdd =
      t * (f ⟨_, transvection_mem_twoBoundarySubgroup hij hP 1⟩).toAdd := by
  let φ : ZMod m →+ ZMod m := AddMonoidHom.mk'
    (fun t ↦ (f ⟨_, transvection_mem_twoBoundarySubgroup hij hP t⟩).toAdd) fun a b ↦ by
      rw [← toAdd_mul, ← map_mul]
      exact congrArg (fun Q ↦ (f Q).toAdd) (Subtype.ext (transvection_add hij a b))
  simpa [φ] using ZMod.map_smul φ t 1

/-- **Every retraction of `P_(r,s)` onto the centre is a boundary retraction**, over `ℤ/m` and for
`r + s < n`: a homomorphism `f : P_(r,s) → ℤ/m` that agrees with the corner coordinate on the
centre `Z` is `ρ_(u,v)` for a normalized pair `u 0 = v n = 1`. Over `ℤ/m` every additive map is
linear, which is what makes `f` determined by its values at the transvections `e_ij(1)`. -/
theorem exists_twoBoundaryRetraction_eq (h : r + s < n)
    (f : twoBoundarySubgroup (R := ZMod m) n r s →* Multiplicative (ZMod m))
    (hf : ∀ Q : twoBoundarySubgroup (R := ZMod m) n r s,
      (Q : upperUnitriangularGroup (Fin (n + 1)) (ZMod m)) ∈
          Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) (ZMod m)) →
        (f Q).toAdd =
          ((Q : GL (Fin (n + 1)) (ZMod m)) : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod m)) 0
            (Fin.last n)) :
    ∃ u v : Fin (n + 1) → ZMod m,
      u 0 = 1 ∧ v (Fin.last n) = 1 ∧ twoBoundaryRetraction h u v = f := by
  -- The rows `u` and columns `v` read off from `f` at the transvections `e_in(1)` and `e₀ⱼ(1)`.
  let u : Fin (n + 1) → ZMod m := fun i ↦
    if hi : 0 < (i : ℕ) ∧ (i : ℕ) ≤ r then
      (f ⟨_, transvection_mem_twoBoundarySubgroup (lt_last_of_le (by omega) hi.2)
        (Or.inr ⟨rfl, hi.2⟩) 1⟩).toAdd
    else 1
  let v : Fin (n + 1) → ZMod m := fun j ↦
    if hj : (j : ℕ) < n ∧ n ≤ (j : ℕ) + s then
      (f ⟨_, transvection_mem_twoBoundarySubgroup (zero_lt_of_le_add (by omega) hj.2)
        (Or.inl ⟨rfl, hj.2⟩) 1⟩).toAdd
    else 1
  have hu : u 0 = 1 := by simp [u]
  have hv : v (Fin.last n) = 1 := by simp [v]
  refine ⟨u, v, hu, hv, twoBoundary_hom_ext h fun i j hij hP t ↦ ?_⟩
  refine Multiplicative.toAdd.injective ?_
  rw [twoBoundaryRetraction_transvection h u v hij hP, toAdd_ofAdd,
    toAdd_apply_transvection f hij hP t]
  by_cases hc : i = 0 ∧ j = Fin.last n
  · -- At the corner `f` is the corner coordinate.
    obtain ⟨rfl, rfl⟩ := hc
    have h1 := hf ⟨_, transvection_mem_twoBoundarySubgroup hij (Or.inr ⟨rfl, by simp⟩) 1⟩
      (transvection_zero_last_mem_center (R := ZMod m) hij 1)
    rw [coe_transvection, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
      Matrix.one_apply_ne hij.ne, single_apply_same, zero_add] at h1
    rw [hu, hv, h1, one_mul, mul_one]
  rcases hP with ⟨rfl, hj⟩ | ⟨rfl, hi⟩
  · have hj' : (j : ℕ) < n ∧ n ≤ (j : ℕ) + s :=
      ⟨lt_of_le_of_ne (Nat.lt_succ_iff.1 j.isLt) fun h ↦ hc ⟨rfl, Fin.ext h⟩, hj⟩
    simp only [u, v, Fin.val_zero, lt_irrefl, false_and, hj'.1, hj'.2, and_self, ↓reduceDIte,
      one_mul]
  · have hi' : 0 < (i : ℕ) ∧ (i : ℕ) ≤ r :=
      ⟨Nat.pos_of_ne_zero fun h ↦ hc ⟨Fin.ext h, rfl⟩, hi⟩
    simp only [u, hv, hi'.1, hi'.2, and_self, ↓reduceDIte, mul_one]
    exact mul_comm _ _

end ZMod

/-! ### The stabilizer of a boundary retraction -/

section Stabilizer

variable [Ring R] (u v : Fin (n + 1) → R)

/-- **The stabilizer of a boundary retraction**: the elements `M ∈ Uₙ₊₁(R)` such that
`u (M Q M⁻¹ - 1) v = u (Q - 1) v` for every `Q` in the two-boundary subgroup `P_(r,s)`, that is,
conjugation by `M` preserves `ρ_(u,v)`. -/
def twoBoundaryStabilizer : Subgroup (upperUnitriangularGroup (Fin (n + 1)) R) where
  carrier := {M | ∀ Q ∈ twoBoundarySubgroup (R := R) n r s,
    u ⬝ᵥ (((((M * Q * M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
      u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v)}
  one_mem' := by simp
  mul_mem' {M N} hM hN Q hQ := by
    rw [show M * N * Q * (M * N)⁻¹ = M * (N * Q * N⁻¹) * M⁻¹ by group,
      hM _ ((twoBoundarySubgroup_normal).conj_mem Q hQ N), hN Q hQ]
  inv_mem' {M} hM Q hQ := by
    have hQ' := (twoBoundarySubgroup_normal).conj_mem Q hQ M⁻¹
    rw [← hM _ hQ', show M * (M⁻¹ * Q * M⁻¹⁻¹) * M⁻¹ = Q by group]

/-- Membership in the stabilizer of `ρ_(u,v)`. -/
theorem mem_twoBoundaryStabilizer {M : upperUnitriangularGroup (Fin (n + 1)) R} :
    M ∈ twoBoundaryStabilizer (r := r) (s := s) u v ↔ ∀ Q ∈ twoBoundarySubgroup (R := R) n r s,
      u ⬝ᵥ (((((M * Q * M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
        u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) :=
  Iff.rfl

/-- The centre of `Uₙ₊₁(R)` stabilizes every `ρ_(u,v)`. -/
theorem center_le_twoBoundaryStabilizer :
    Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) ≤
      twoBoundaryStabilizer (r := r) (s := s) u v := fun M hM Q _ ↦ by
  rw [(Subgroup.mem_center_iff.1 hM Q).symm, mul_inv_cancel_right]

/-- For `r + s < n` the two-boundary subgroup `P_(r,s)`, being abelian, stabilizes `ρ_(u,v)`. -/
theorem twoBoundarySubgroup_le_twoBoundaryStabilizer (h : r + s < n) :
    twoBoundarySubgroup (R := R) n r s ≤ twoBoundaryStabilizer (r := r) (s := s) u v :=
    fun M hM Q hQ ↦ by
  have hc := congrArg Subtype.val ((isMulCommutative_twoBoundarySubgroup (R := R) h).is_comm.comm
    (⟨M, hM⟩ : twoBoundarySubgroup (R := R) n r s) ⟨Q, hQ⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at hc
  rw [hc, mul_inv_cancel_right]

/-- Conjugation by `M` carries `u (Q - 1) v` to `(u M) (Q - 1) (M⁻¹ v)`. -/
private theorem dotProduct_conj_sub_one_mulVec (M Q : upperUnitriangularGroup (Fin (n + 1)) R) :
    u ⬝ᵥ (((((M * Q * M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
      (u ᵥ* ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) ⬝ᵥ
        ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ
          ((((M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v)) := by
  set A := ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set B := (((M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set X := ((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have hAB : A * B = 1 := by
    simp only [A, B, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      Units.val_one]
  have hconj : (((M * Q * M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1 = A * ((X - 1) * B) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, sub_mul, one_mul,
      mul_sub, ← hAB, ← mul_assoc]
  rw [hconj, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

/-- The column `0` and the row `n` of `M - 1` vanish for `M ∈ Uₙ₊₁(R)`, so `(u M) 0 = u 0` and
`(M v) n = v n`. -/
private theorem vecMul_apply_zero (M : upperUnitriangularGroup (Fin (n + 1)) R) :
    (u ᵥ* ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)) 0 = u 0 := by
  conv_rhs => rw [← vecMul_one u]
  simp only [vecMul, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ congrArg (u i * ·) ?_
  rcases eq_or_ne i 0 with rfl | hi
  · rw [apply_diag, Matrix.one_apply_eq]
  · rw [isUpperTriangular M (Fin.pos_iff_ne_zero.2 hi), Matrix.one_apply_ne hi]

private theorem mulVec_apply_last (M : upperUnitriangularGroup (Fin (n + 1)) R) :
    (((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) *ᵥ v) (Fin.last n) =
      v (Fin.last n) := by
  conv_rhs => rw [← one_mulVec v]
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun j _ ↦ congrArg (· * v j) ?_
  rcases eq_or_ne j (Fin.last n) with rfl | hj
  · rw [apply_diag, Matrix.one_apply_eq]
  · exact (isUpperTriangular M (Fin.lt_last_iff_ne_last.2 hj)).trans
      (Matrix.one_apply_ne hj.symm).symm

/-- An upper triangular matrix preserves the column vectors vanishing at the indices `≥ n - s`. -/
private theorem mulVec_apply_eq_zero {T : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (hT : T.IsUpperTriangular) {w : Fin (n + 1) → R}
    (hw : ∀ k : Fin (n + 1), n ≤ (k : ℕ) + s → w k = 0)
    {j : Fin (n + 1)} (hj : n ≤ (j : ℕ) + s) : (T *ᵥ w) j = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rcases lt_or_ge k j with hkj | hjk
  · rw [hT hkj, zero_mul]
  · rw [hw k (by rw [Fin.le_def] at hjk; omega), mul_zero]

/-- **The stabilizer of a boundary retraction**, for `r, s < n` and a normalized pair
`u 0 = v n = 1`: `M ∈ Uₙ₊₁(R)` stabilizes `ρ_(u,v)` exactly when the row `u (M - 1)` vanishes at the
indices `≤ r` and the column `(M - 1) v` vanishes at the indices `≥ n - s`. -/
theorem mem_twoBoundaryStabilizer_iff (hr : r < n) (hs : s < n) (hu : u 0 = 1)
    (hv : v (Fin.last n) = 1) {M : upperUnitriangularGroup (Fin (n + 1)) R} :
    M ∈ twoBoundaryStabilizer (r := r) (s := s) u v ↔
      (∀ i : Fin (n + 1), (i : ℕ) ≤ r →
        (u ᵥ* (((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1)) i = 0) ∧
      ∀ j : Fin (n + 1), n ≤ (j : ℕ) + s →
        ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) j = 0 := by
  set A := ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set B := (((M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have hBA : B * A = 1 := by
    simp only [A, B, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, OneMemClass.coe_one,
      Units.val_one]
  have hAB : A * B = 1 := by
    simp only [A, B, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
      Units.val_one]
  rw [mem_twoBoundaryStabilizer]
  simp_rw [dotProduct_conj_sub_one_mulVec]
  rw [forall_dotProduct_eq_iff hr hs (by rw [vecMul_apply_zero, hu]) (by rw [mulVec_apply_last, hv])
    hu hv]
  refine and_congr (forall₂_congr fun i _ ↦ ?_) ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
  · rw [vecMul_sub, vecMul_one, Pi.sub_apply, sub_eq_zero]
  · -- `(A - 1) v = -A ((B - 1) v)`, and `(B - 1) v` vanishes at the indices `≥ n - s`.
    have hw : (A - 1) *ᵥ v = -(A *ᵥ ((B - 1) *ᵥ v)) := by
      rw [mulVec_mulVec, mul_sub, hAB, mul_one, ← neg_mulVec, neg_sub]
    rw [hw, Pi.neg_apply, mulVec_apply_eq_zero (isUpperTriangular M) (fun k hk ↦ ?_) hj, neg_zero]
    rw [sub_mulVec, one_mulVec, Pi.sub_apply, h k hk, sub_self]
  · -- `(B - 1) v = -B ((A - 1) v)`, and `(A - 1) v` vanishes at the indices `≥ n - s`.
    have hw : (B - 1) *ᵥ v = -(B *ᵥ ((A - 1) *ᵥ v)) := by
      rw [mulVec_mulVec, mul_sub, hBA, mul_one, ← neg_mulVec, neg_sub]
    have hB : (B *ᵥ v) j - v j = ((B - 1) *ᵥ v) j := by
      rw [sub_mulVec, one_mulVec, Pi.sub_apply]
    rw [← sub_eq_zero, hB, hw, Pi.neg_apply, mulVec_apply_eq_zero (isUpperTriangular M⁻¹) h hj,
      neg_zero]

end Stabilizer

/-! ### The stabilizer splits over the centre -/

section Splitting

variable [Ring R] {u v : Fin (n + 1) → R} (hr : r < n) (hs : s < n) (hrs : n ≤ r + s + 1)
  (hu : u 0 = 1) (hv : v (Fin.last n) = 1)

/-- **The retraction of the stabilizer.** For `r, s < n` with `n ≤ r + s + 1` and a normalized pair,
`ρ'(M) = u (M - 1) v` is a homomorphism from the stabilizer `S` of `ρ_(u,v)` to `(R, +)`: for
`M, N ∈ S` the row `u (M - 1)` vanishes at the indices `≤ r` and the column `(N - 1) v` at the
indices `≥ n - s`, which together are all indices, so `u (M - 1) (N - 1) v = 0`. It extends
`ρ_(u,v)` (`twoBoundaryStabilizerRetraction_apply_of_mem`) and is the corner coordinate on the
centre (`toAdd_twoBoundaryStabilizerRetraction_of_mem_center`). -/
def twoBoundaryStabilizerRetraction :
    twoBoundaryStabilizer (r := r) (s := s) u v →* Multiplicative R where
  toFun M := Multiplicative.ofAdd
    (u ⬝ᵥ ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v))
  map_one' := by simp
  map_mul' M N := by
    rw [← ofAdd_add, ← dotProduct_add, ← add_mulVec]
    set A := ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    set B := ((N : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hM := (mem_twoBoundaryStabilizer_iff u v hr hs hu hv).1 M.property
    have hN := (mem_twoBoundaryStabilizer_iff u v hr hs hu hv).1 N.property
    have hAB : u ⬝ᵥ (((A - 1) * (B - 1)) *ᵥ v) = 0 := by
      rw [← mulVec_mulVec, dotProduct_mulVec]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      by_cases hk : (k : ℕ) ≤ r
      · rw [hM.1 k hk, zero_mul]
      · rw [hN.2 k (by omega), mul_zero]
    have hmul : (((M * N : twoBoundaryStabilizer (r := r) (s := s) u v) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1 = A - 1 + (B - 1) + (A - 1) * (B - 1) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul]
      noncomm_ring
    rw [hmul, add_mulVec _ ((A - 1) * (B - 1)), dotProduct_add, hAB, add_zero]

/-- The value of `ρ'` at `M` is `u (M - 1) v`. -/
@[simp]
theorem toAdd_twoBoundaryStabilizerRetraction_apply
    (M : twoBoundaryStabilizer (r := r) (s := s) u v) :
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv M).toAdd =
      u ⬝ᵥ ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) :=
  (rfl)

/-- `ρ'` extends `ρ_(u,v)` from `P_(r,s)` to the stabilizer, for `n = r + s + 1`. -/
theorem twoBoundaryStabilizerRetraction_apply_of_mem (h : r + s < n)
    (Q : twoBoundarySubgroup (R := R) n r s) :
    twoBoundaryStabilizerRetraction hr hs hrs hu hv
        ⟨Q, twoBoundarySubgroup_le_twoBoundaryStabilizer u v h Q.property⟩ =
      twoBoundaryRetraction h u v Q :=
  (rfl)

/-- `ρ'` is the corner coordinate on the centre: it retracts the stabilizer onto the centre. -/
theorem toAdd_twoBoundaryStabilizerRetraction_of_mem_center
    {M : twoBoundaryStabilizer (r := r) (s := s) u v}
    (hM : (M : upperUnitriangularGroup (Fin (n + 1)) R) ∈
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) :
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv M).toAdd =
      ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) := by
  rw [toAdd_twoBoundaryStabilizerRetraction_apply,
    dotProduct_sub_one_mulVec_of_mem_center (by omega) hM, hu, hv, one_mul, mul_one]

/-- The kernel of `ρ'` meets the centre trivially: a central element is determined by its corner
entry, which `ρ'` reads off. -/
private theorem coe_eq_one_of_mem_center {M : twoBoundaryStabilizer (r := r) (s := s) u v}
    (hMZ : (M : upperUnitriangularGroup (Fin (n + 1)) R) ∈
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R))
    (hM : twoBoundaryStabilizerRetraction hr hs hrs hu hv M = 1) :
    (M : upperUnitriangularGroup (Fin (n + 1)) R) = 1 := by
  have hc := toAdd_twoBoundaryStabilizerRetraction_of_mem_center hr hs hrs hu hv hMZ
  rw [hM, toAdd_one] at hc
  refine ext fun i j hij ↦ ?_
  rw [OneMemClass.coe_one, Units.val_one, Matrix.one_apply_ne hij.ne]
  by_cases hcor : i = 0 ∧ j = Fin.last n
  · obtain ⟨rfl, rfl⟩ := hcor
    exact hc.symm
  · exact mem_center_iff.1 hMZ i j hij hcor

include hr hs hrs hu hv in
/-- **Homomorphisms into the image of the stabilizer lift.** For `r, s < n` with
`n ≤ r + s + 1` and a normalized pair `u 0 = v n = 1`, every homomorphism `φ : G → Uₙ₊₁(R)/Z`
with values in the image of the stabilizer `S` of `ρ_(u,v)` lifts to a homomorphism
`ψ : G → Uₙ₊₁(R)` with the same kernel; in particular `ψ` has open kernel whenever `φ` does. The
lift takes values in the kernel of `ρ'`, which maps isomorphically onto the image of `S`. -/
theorem exists_lift_of_range_le_map_twoBoundaryStabilizer {G : Type*} [Group G]
    (φ : G →* upperUnitriangularGroup (Fin (n + 1)) R ⧸
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R))
    (hφ : φ.range ≤ (twoBoundaryStabilizer (r := r) (s := s) u v).map (QuotientGroup.mk' _)) :
    ∃ ψ : G →* upperUnitriangularGroup (Fin (n + 1)) R,
      (QuotientGroup.mk' _).comp ψ = φ ∧ ψ.ker = φ.ker := by
  have h0 : (0 : Fin (n + 1)) < Fin.last n :=
    Fin.lt_def.2 (by simp only [Fin.val_zero, Fin.val_last]; omega)
  -- The kernel `K` of `ρ'`, viewed in `Uₙ₊₁(R)`, maps injectively to `Uₙ₊₁(R)/Z`.
  let K : Subgroup (upperUnitriangularGroup (Fin (n + 1)) R) :=
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv).ker.map
      (twoBoundaryStabilizer (r := r) (s := s) u v).subtype
  let ι : K →* upperUnitriangularGroup (Fin (n + 1)) R ⧸
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) :=
    (QuotientGroup.mk' _).comp K.subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    rintro ⟨k, hk⟩ hk1
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.1 hk
    rw [Subgroup.mk_eq_one, Subgroup.coe_subtype]
    exact coe_eq_one_of_mem_center hr hs hrs hu hv ((QuotientGroup.eq_one_iff _).1 hk1)
      (MonoidHom.mem_ker.1 hM)
  -- Its image contains the image of `S`: `M e₀ₙ(-ρ' M)` lies in `K` and is congruent to `M`.
  have hrange : φ.range ≤ ι.range := by
    intro x hx
    obtain ⟨M, hM, rfl⟩ := Subgroup.mem_map.1 (hφ hx)
    set c := (twoBoundaryStabilizerRetraction hr hs hrs hu hv ⟨M, hM⟩).toAdd
    have hz := transvection_zero_last_mem_center h0 (-c)
    have hzS := center_le_twoBoundaryStabilizer (r := r) (s := s) u v hz
    have hρz := toAdd_twoBoundaryStabilizerRetraction_of_mem_center hr hs hrs hu hv
      (M := ⟨_, hzS⟩) hz
    rw [coe_transvection, coe_transvectionUnit_eq_one_add_single, Matrix.add_apply,
      Matrix.one_apply_ne h0.ne, single_apply_same, zero_add] at hρz
    refine ⟨⟨M * transvection h0 (-c), Subgroup.mem_map.2 ⟨⟨M, hM⟩ * ⟨_, hzS⟩, ?_, rfl⟩⟩, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul]
      refine Multiplicative.toAdd.injective ?_
      rw [toAdd_mul, hρz, toAdd_one]
      exact add_neg_cancel c
    · exact QuotientGroup.mk_mul_of_mem M hz
  let e := MonoidHom.ofInjective hι
  refine ⟨K.subtype.comp (e.symm.toMonoidHom.comp (φ.codRestrict ι.range fun g ↦
    hrange ⟨g, rfl⟩)), MonoidHom.ext fun g ↦ ?_, ?_⟩
  · have := congrArg Subtype.val (e.apply_symm_apply ⟨φ g, hrange ⟨g, rfl⟩⟩)
    rwa [MonoidHom.ofInjective_apply] at this
  · ext g
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]
    rw [← Subtype.coe_inj, MonoidHom.codRestrict_apply, OneMemClass.coe_one]

end Splitting

end TauCeti.UpperUnitriangularGroup
