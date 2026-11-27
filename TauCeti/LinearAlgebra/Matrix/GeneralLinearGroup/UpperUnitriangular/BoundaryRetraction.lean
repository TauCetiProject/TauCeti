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
-- Non-public: the product and conjugation identities below are used only in proofs.
import TauCeti.Algebra.Algebra.Quasiregular
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Conjugation

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

* `TauCeti.UpperUnitriangularGroup.twoBoundaryRetraction`: the homomorphism
  `ρ_(u,v) : P_(r,s) → R` for `r + s < n`.
* `TauCeti.UpperUnitriangularGroup.forall_mem_center_twoBoundaryRetraction_iff`: `ρ_(u,v)` is the
  corner coordinate on `Z` exactly when `u 0 * v n = 1`.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryRetraction_eq_iff`: when two normalized pairs give
  the same retraction.
* `TauCeti.UpperUnitriangularGroup.exists_twoBoundaryRetraction_eq`: over `ℤ/m` every retraction
  of `P_(r,s)` onto `Z` is `ρ_(u,v)` for a normalized pair.
* `TauCeti.UpperUnitriangularGroup.twoBoundaryStabilizer` and
  `TauCeti.UpperUnitriangularGroup.mem_twoBoundaryStabilizer_iff_vecMul_sub_one_and_sub_one_mulVec`:
  the stabilizer `S` of `ρ_(u,v)` and its description by two support conditions.
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
    rw [Subgroup.coe_mul, coe_mul, mul_sub_one_eq_add_add_mul, hAB, add_zero]

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
    rw [this, coe_transvection_apply_same]
  · intro huv Q hQ
    rw [toAdd_twoBoundaryRetraction_of_mem_center h u v hQ, mul_right_comm, huv, one_mul]

end CommRing

/-! ### Every retraction over `ℤ/m` is a boundary retraction -/

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
  refine ⟨u, v, hu, hv, twoBoundarySubgroup_hom_ext h fun i j hij hP t ↦ ?_⟩
  refine Multiplicative.toAdd.injective ?_
  rw [twoBoundaryRetraction_transvection h u v hij hP, toAdd_ofAdd,
    toAdd_apply_transvection f hij hP t]
  by_cases hc : i = 0 ∧ j = Fin.last n
  · -- At the corner `f` is the corner coordinate.
    obtain ⟨rfl, rfl⟩ := hc
    have h1 := hf ⟨_, transvection_mem_twoBoundarySubgroup hij (Or.inr ⟨rfl, by simp⟩) 1⟩
      (transvection_zero_last_mem_center (R := ZMod m) hij 1)
    rw [coe_transvection_apply_same] at h1
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
def twoBoundaryStabilizer (n r s : ℕ) (u v : Fin (n + 1) → R) :
    Subgroup (upperUnitriangularGroup (Fin (n + 1)) R) where
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
theorem mem_twoBoundaryStabilizer_iff {M : upperUnitriangularGroup (Fin (n + 1)) R} :
    M ∈ twoBoundaryStabilizer n r s u v ↔ ∀ Q ∈ twoBoundarySubgroup (R := R) n r s,
      u ⬝ᵥ (((((M * Q * M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) =
        u ⬝ᵥ ((((Q : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) :=
  Iff.rfl

/-- The centre of `Uₙ₊₁(R)` stabilizes every `ρ_(u,v)`. -/
theorem center_le_twoBoundaryStabilizer :
    Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R) ≤
      twoBoundaryStabilizer n r s u v := fun M hM Q _ ↦ by
  rw [(Subgroup.mem_center_iff.1 hM Q).symm, mul_inv_cancel_right]

/-- For `r + s < n` the two-boundary subgroup `P_(r,s)`, being abelian, stabilizes `ρ_(u,v)`. -/
theorem twoBoundarySubgroup_le_twoBoundaryStabilizer (h : r + s < n) :
    twoBoundarySubgroup (R := R) n r s ≤ twoBoundaryStabilizer n r s u v :=
    fun M hM Q hQ ↦ by
  have hc := congrArg Subtype.val ((isMulCommutative_twoBoundarySubgroup (R := R) h).is_comm.comm
    (⟨M, hM⟩ : twoBoundarySubgroup (R := R) n r s) ⟨Q, hQ⟩)
  rw [Subgroup.coe_mul, Subgroup.coe_mul] at hc
  rw [hc, mul_inv_cancel_right]

/-- **The stabilizer of a boundary retraction**, for `r, s < n` and a normalized pair
`u 0 = v n = 1`: `M ∈ Uₙ₊₁(R)` stabilizes `ρ_(u,v)` exactly when the row `u (M - 1)` vanishes at the
indices `≤ r` and the column `(M - 1) v` vanishes at the indices `≥ n - s`. -/
theorem mem_twoBoundaryStabilizer_iff_vecMul_sub_one_and_sub_one_mulVec (hr : r < n) (hs : s < n)
    (hu : u 0 = 1)
    (hv : v (Fin.last n) = 1) {M : upperUnitriangularGroup (Fin (n + 1)) R} :
    M ∈ twoBoundaryStabilizer n r s u v ↔
      (∀ i : Fin (n + 1), (i : ℕ) ≤ r →
        (u ᵥ* (((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1)) i = 0) ∧
      ∀ j : Fin (n + 1), n ≤ (j : ℕ) + s →
        ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) j = 0 := by
  set A := ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  set B := (((M⁻¹ : upperUnitriangularGroup (Fin (n + 1)) R) : GL (Fin (n + 1)) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R)
  have hBA : B * A = 1 := coe_inv_mul_coe M
  have hAB : A * B = 1 := coe_mul_coe_inv M
  rw [mem_twoBoundaryStabilizer_iff]
  simp_rw [Subgroup.coe_mul, Subgroup.coe_inv,
    Matrix.GeneralLinearGroup.dotProduct_conj_sub_one_mulVec, ← Subgroup.coe_inv]
  rw [forall_dotProduct_eq_iff hr hs
    (by rw [vecMul_coe_apply_of_isBot M u fun _ ↦ Fin.zero_le _, hu])
    (by rw [coe_mulVec_apply_of_isTop M⁻¹ v fun _ ↦ Fin.le_last _, hv]) hu hv]
  refine and_congr (forall₂_congr fun i _ ↦ ?_) ⟨fun h j hj ↦ ?_, fun h j hj ↦ ?_⟩
  · rw [vecMul_sub, vecMul_one, Pi.sub_apply, sub_eq_zero]
  · -- `(A - 1) v = -A ((B - 1) v)`, and `(B - 1) v` vanishes at the indices `≥ n - s`.
    have hw : (A - 1) *ᵥ v = -(A *ᵥ ((B - 1) *ᵥ v)) := by
      rw [mulVec_mulVec, mul_sub, hAB, mul_one, ← neg_mulVec, neg_sub]
    rw [hw, Pi.neg_apply,
      (isUpperTriangular M).mulVec_apply_eq_zero fun k hk ↦ ?_, neg_zero]
    rw [sub_mulVec, one_mulVec, Pi.sub_apply, h k (by rw [Fin.le_def] at hk; omega), sub_self]
  · -- `(B - 1) v = -B ((A - 1) v)`, and `(A - 1) v` vanishes at the indices `≥ n - s`.
    have hw : (B - 1) *ᵥ v = -(B *ᵥ ((A - 1) *ᵥ v)) := by
      rw [mulVec_mulVec, mul_sub, hBA, mul_one, ← neg_mulVec, neg_sub]
    have hB : (B *ᵥ v) j - v j = ((B - 1) *ᵥ v) j := by
      rw [sub_mulVec, one_mulVec, Pi.sub_apply]
    rw [← sub_eq_zero, hB, hw, Pi.neg_apply, (isUpperTriangular M⁻¹).mulVec_apply_eq_zero
      fun k hk ↦ h k (by rw [Fin.le_def] at hk; omega), neg_zero]

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
    twoBoundaryStabilizer n r s u v →* Multiplicative R where
  toFun M := Multiplicative.ofAdd
    (u ⬝ᵥ ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v))
  map_one' := by simp
  map_mul' M N := by
    rw [← ofAdd_add, ← dotProduct_add, ← add_mulVec]
    set A := ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    set B := ((N : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    have hM := (mem_twoBoundaryStabilizer_iff_vecMul_sub_one_and_sub_one_mulVec u v hr hs hu hv).1
      M.property
    have hN := (mem_twoBoundaryStabilizer_iff_vecMul_sub_one_and_sub_one_mulVec u v hr hs hu hv).1
      N.property
    have hAB : u ⬝ᵥ (((A - 1) * (B - 1)) *ᵥ v) = 0 := by
      rw [← mulVec_mulVec, dotProduct_mulVec]
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      by_cases hk : (k : ℕ) ≤ r
      · rw [hM.1 k hk, zero_mul]
      · rw [hN.2 k (by omega), mul_zero]
    rw [Subgroup.coe_mul, coe_mul, mul_sub_one_eq_add_add_mul, add_mulVec _ ((A - 1) * (B - 1)),
      dotProduct_add, hAB, add_zero]

/-- The value of `ρ'` at `M` is `u (M - 1) v`. -/
@[simp]
theorem toAdd_twoBoundaryStabilizerRetraction_apply
    (M : twoBoundaryStabilizer n r s u v) :
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv M).toAdd =
      u ⬝ᵥ ((((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) - 1) *ᵥ v) :=
  (rfl)

/-- `ρ'` extends `ρ_(u,v)` from `P_(r,s)` to the stabilizer, for `n = r + s + 1`. -/
theorem twoBoundaryStabilizerRetraction_apply_of_mem (h : r + s < n)
    (Q : twoBoundarySubgroup (R := R) n r s) :
    twoBoundaryStabilizerRetraction hr hs hrs hu hv
        ⟨Q, twoBoundarySubgroup_le_twoBoundaryStabilizer u v h Q.property⟩ =
      twoBoundaryRetraction h u v Q :=
  Multiplicative.toAdd.injective <| by
    rw [toAdd_twoBoundaryStabilizerRetraction_apply, toAdd_twoBoundaryRetraction_apply]

/-- `ρ'` is the corner coordinate on the centre: it retracts the stabilizer onto the centre. -/
theorem toAdd_twoBoundaryStabilizerRetraction_of_mem_center
    {M : twoBoundaryStabilizer n r s u v}
    (hM : (M : upperUnitriangularGroup (Fin (n + 1)) R) ∈
      Subgroup.center (upperUnitriangularGroup (Fin (n + 1)) R)) :
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv M).toAdd =
      ((M : GL (Fin (n + 1)) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R) 0 (Fin.last n) := by
  rw [toAdd_twoBoundaryStabilizerRetraction_apply,
    dotProduct_sub_one_mulVec_of_mem_center (by omega) hM, hu, hv, one_mul, mul_one]

/-- The kernel of `ρ'` meets the centre trivially: a central element is determined by its corner
entry, which `ρ'` reads off. -/
private theorem coe_eq_one_of_mem_center {M : twoBoundaryStabilizer n r s u v}
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
    (hφ : φ.range ≤ (twoBoundaryStabilizer n r s u v).map (QuotientGroup.mk' _)) :
    ∃ ψ : G →* upperUnitriangularGroup (Fin (n + 1)) R,
      (QuotientGroup.mk' _).comp ψ = φ ∧ ψ.ker = φ.ker := by
  have h0 : (0 : Fin (n + 1)) < Fin.last n :=
    Fin.lt_def.2 (by simp only [Fin.val_zero, Fin.val_last]; omega)
  -- The kernel `K` of `ρ'`, viewed in `Uₙ₊₁(R)`, maps injectively to `Uₙ₊₁(R)/Z`.
  let K : Subgroup (upperUnitriangularGroup (Fin (n + 1)) R) :=
    (twoBoundaryStabilizerRetraction hr hs hrs hu hv).ker.map
      (twoBoundaryStabilizer n r s u v).subtype
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
    rw [coe_transvection_apply_same] at hρz
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
