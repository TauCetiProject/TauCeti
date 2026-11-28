/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup.Bessel

/-!
# The coordinates `(ω, μ)` of the group `U⁰` of the split form

Let `R` be a commutative ring with involution, and let `TauCeti.besselU0 ϱ T` be the group of
isometries of the split form `TauCeti.splitGram ϱ T` (basis `e_a`, `x_i`, `z`, `e*_a`) that are
block unitriangular for the levels and fix the frame `(e₀, …, e_{ϱ-1}, z)`. For a matrix `u` write

`u e*_b = e*_b - Σ_i ω_{ib} x_i - Σ_a μ_{ab} e_a`,

that is `ω_{ib} = -u (x_i, e*_b)` (`Matrix.besselOmega`) and `μ_{ab} = -u (e_a, e*_b)`
(`Matrix.besselMu`). For `u ∈ U⁰` and the middle Gram matrix `T = diag(1_κ, -N)` this is the whole
column of `u` at `e*_b`: its entry at `e*_c` is `δ_{cb}`, and its entry at `z` is `0` when `N` is
not a zero divisor. The column of `u` at `x_i` is `x_i + Σ_a star (ω_{ia}) e_a`, and the
composition law of `U⁰` reads

`ω(uv) = ω(u) + ω(v)`, `μ(uv) = μ(u) + μ(v) + ω(u)ᴴ ω(v)`.

Moreover `μ + μᴴ = ωᴴ ω`, `ω(u⁻¹) = -ω(u)` and `μ(u⁻¹) = μ(u)ᴴ`. All of these are entries of the
identity `uᴴ (G u) = G` for `G` the split Gram matrix, mostly read off at the columns of the
frame.

## Main definitions

* `Matrix.besselOmega u`, `Matrix.besselMu u`: the coordinates `ω` and `μ` of a matrix `u` on the
  basis of the split form.

## Main results

* `TauCeti.apply_inl_of_mem_frameFixingSubgroup`, `TauCeti.apply_z_of_mem_frameFixingSubgroup`,
  `TauCeti.apply_middle_middle_of_mem_besselU`: the entries of `u` fixed by the frame and by the
  levels.
* `TauCeti.apply_eStar_of_mem_frameFixingSubgroup`: the rows of `u` at the `e*_c` are those of
  `1`, so the column of `u` at `e*_b` has the entry `δ_{cb}` at `e*_c`.
* `TauCeti.mul_apply_z_eStar_of_mem_frameFixingSubgroup`,
  `TauCeti.apply_z_eStar_of_mem_frameFixingSubgroup`: its entry at `z` is killed by `N`, and is
  `0` when `N` is not a zero divisor.
* `TauCeti.apply_inl_x_of_mem_besselU0`: `u (e_a, x_i) = star (ω_{ia})`.
* `TauCeti.besselOmega_mul`, `TauCeti.besselMu_mul`: the composition law.
* `TauCeti.besselMu_add_conjTranspose`: `μ + μᴴ = ωᴴ ω`.
* `TauCeti.besselOmega_inv`, `TauCeti.besselMu_inv`: the coordinates of `u⁻¹`.

## References

* the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207, declaration `New.RealPlace.besselHaar₀_homogeneousBall`.
* H. Xue, *Bessel models for real unitary groups: the tempered case*, Duke Math. J. 172 (2023).
-/

public section

open Matrix

namespace Matrix

open TauCeti

variable {R : Type*} {ϱ : ℕ} {κ : Type*}

section Neg

variable [Neg R]

/-- The `x`-coordinates `ω` of a matrix `u` on the basis of the split form: minus the entries of
its columns at the `e*_b` along the vectors `x_i`, so that `ω i b = -u (x_i, e*_b)`. -/
def besselOmega (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) : Matrix κ (Fin ϱ) R :=
  of fun i b ↦ -u (.inr (.inl (.inl i))) (.inr (.inr b))

@[simp] lemma besselOmega_apply (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (i : κ)
    (b : Fin ϱ) : besselOmega u i b = -u (.inr (.inl (.inl i))) (.inr (.inr b)) := (rfl)

/-- The `e`-coordinates `μ` of a matrix `u` on the basis of the split form: minus the entries of
its columns at the `e*_b` along the vectors `e_a`, so that `μ a b = -u (e_a, e*_b)`. -/
def besselMu (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) : Matrix (Fin ϱ) (Fin ϱ) R :=
  of fun a b ↦ -u (.inl a) (.inr (.inr b))

@[simp] lemma besselMu_apply (u : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (a b : Fin ϱ) :
    besselMu u a b = -u (.inl a) (.inr (.inr b)) := (rfl)

end Neg

section One

variable [NegZeroClass R] [One R] [DecidableEq κ]

/-- The identity matrix has `x`-coordinates `ω = 0`. -/
@[simp] lemma besselOmega_one :
    besselOmega (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) = 0 := by
  ext i b
  simp

/-- The identity matrix has `e`-coordinates `μ = 0`. -/
@[simp] lemma besselMu_one : besselMu (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) = 0 := by
  ext a b
  simp

end One

end Matrix

namespace TauCeti

variable {R : Type*} [CommRing R] [StarRing R] {ϱ : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

section FrameFixing

variable {T : Matrix (κ ⊕ Unit) (κ ⊕ Unit) R} {u : unitaryGroupOf (splitGram ϱ T)}

/-- The columns at the `e_a` of a frame-fixing matrix are those of `1`. -/
theorem apply_inl_of_mem_frameFixingSubgroup (hu : u ∈ frameFixingSubgroup ϱ T)
    (i : BesselIndex ϱ κ) (a : Fin ϱ) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (.inl a) =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (.inl a) :=
  (mem_frameFixingSubgroup ϱ T).mp hu i _ ⟨a.castSucc, besselFrame_castSucc a⟩

/-- The column at `z` of a frame-fixing matrix is that of `1`. -/
theorem apply_z_of_mem_frameFixingSubgroup (hu : u ∈ frameFixingSubgroup ϱ T)
    (i : BesselIndex ϱ κ) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i
        (BesselIndex.z ϱ κ) =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i (BesselIndex.z ϱ κ) :=
  (mem_frameFixingSubgroup ϱ T).mp hu i _ ⟨Fin.last ϱ, besselFrame_last⟩

/-- On the middle block, an element of `U` agrees with `1`: the middle indices share the level
`ϱ`. -/
theorem apply_middle_middle_of_mem_besselU (hu : u ∈ besselU ϱ T) (m m' : κ ⊕ Unit) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (.inr (.inl m)) (.inr (.inl m')) =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inl m)) (.inr (.inl m')) :=
  ((mem_besselU ϱ T).mp hu).apply_of_eq (by simp only [splitLevel_middle])

/-- **The rows at the `e*_c` of a frame-fixing isometry.** For an isometry `u` of the split form
fixing the frame, the row of `u` at `e*_c` is that of `1`. In particular the column of `u` at
`e*_b` has the entry `δ_{cb}` at `e*_c`. -/
theorem apply_eStar_of_mem_frameFixingSubgroup (hu : u ∈ frameFixingSubgroup ϱ T) (c : Fin ϱ)
    (j : BesselIndex ϱ κ) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (.inr (.inr c)) j =
      (1 : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) (.inr (.inr c)) j := by
  -- the entry `(e_c, j)` of `uᴴ G u = G`, where the column of `u` at `e_c` is that of `1`
  have h := congrFun (congrFun (unitaryGroupOf.conjTranspose_mul_mul_cancel u) (.inl c)) j
  rcases j with b | m | b
  · exact apply_inl_of_mem_frameFixingSubgroup hu _ b
  all_goals simpa [Matrix.mul_apply, Fintype.sum_sum_type, apply_inl_of_mem_frameFixingSubgroup hu,
      Matrix.one_apply, apply_ite (star : R → R)] using h

/-- **The `e`-coordinates of `u⁻¹`.** For every isometry `u` of the split form,
`μ(u⁻¹) = μ(u)ᴴ`. -/
theorem besselMu_inv (u : unitaryGroupOf (splitGram ϱ T)) :
    besselMu (((u⁻¹ : unitaryGroupOf _) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      (besselMu ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R))ᴴ := by
  -- the entry `(e*_a, e*_b)` of `uᴴ G = G u⁻¹`
  have h := unitaryGroupOf.conjTranspose_mul_mul_mul_cancel u
    (((u⁻¹ : unitaryGroupOf _) : GL (BesselIndex ϱ κ) R) :
      Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
  rw [InvMemClass.coe_inv, Units.mul_inv, Matrix.mul_one] at h
  ext a b
  have hab := congrFun (congrFun h (.inr (.inr a))) (.inr (.inr b))
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, Matrix.one_apply,
    splitGram_inl_eStar, splitGram_middle_eStar, splitGram_eStar_eStar, splitGram_eStar_inl,
    splitGram_eStar_middle, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero,
    add_zero] at hab
  simpa [InvMemClass.coe_inv] using hab.symm

end FrameFixing

variable {N : R} {u v : unitaryGroupOf (splitGram ϱ (middleGram (κ := κ) N))}

/-- For an isometry `u` of the split form of `diag(1_κ, -N)` fixing the frame, the entry of `u` at
`(z, e*_b)` is killed by `N`. -/
theorem mul_apply_z_eStar_of_mem_frameFixingSubgroup
    (hu : u ∈ frameFixingSubgroup ϱ (middleGram N)) (b : Fin ϱ) :
    N * ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (BesselIndex.z ϱ κ) (.inr (.inr b)) = 0 := by
  -- the entry `(z, e*_b)` of `uᴴ G u = G`, where the column of `u` at `z` is that of `1`
  have h := congrFun (congrFun (unitaryGroupOf.conjTranspose_mul_mul_cancel u)
    (BesselIndex.z ϱ κ)) (.inr (.inr b))
  simpa [Matrix.mul_apply, Fintype.sum_sum_type, apply_z_of_mem_frameFixingSubgroup hu,
    Matrix.one_apply, apply_ite (star : R → R)] using h

/-- For an isometry `u` of the split form of `diag(1_κ, -N)` fixing the frame, the column of `u`
at `e*_b` has the entry `0` at `z`, when `N` is not a zero divisor. -/
theorem apply_z_eStar_of_mem_frameFixingSubgroup (hN : IsLeftRegular N)
    (hu : u ∈ frameFixingSubgroup ϱ (middleGram N)) (b : Fin ϱ) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (BesselIndex.z ϱ κ) (.inr (.inr b)) = 0 :=
  hN ((mul_apply_z_eStar_of_mem_frameFixingSubgroup hu b).trans (mul_zero N).symm)

/-- **The column of `u ∈ U⁰` at `x_i`.** Its entry at `e_a` is `star (ω_{ia})`. -/
theorem apply_inl_x_of_mem_besselU0 (hu : u ∈ besselU0 ϱ (middleGram N)) (a : Fin ϱ) (i : κ) :
    ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R)
        (.inl a) (.inr (.inl (.inl i))) =
      star (besselOmega ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) i a) := by
  have hU := (mem_besselU0 ϱ _).mp hu
  -- the entry `(x_i, e*_a)` of `uᴴ G u = G`: `star (u (e_a, x_i)) + u (x_i, e*_a) = 0`
  have h := congrFun (congrFun (unitaryGroupOf.conjTranspose_mul_mul_cancel u)
    (.inr (.inl (.inl i)))) (.inr (.inr a))
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, Finset.univ_unique,
    PUnit.default_eq_unit, Finset.sum_singleton, apply_eStar_of_mem_frameFixingSubgroup hU.2,
    Matrix.one_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, splitGram_inl_inl, zero_mul, Finset.sum_const_zero,
    splitGram_inl_middle, add_zero, splitGram_inl_eStar, zero_add,
    apply_middle_middle_of_mem_besselU hU.1, Sum.inl.injEq, apply_ite (star : R → R), star_one,
    star_zero, splitGram_middle_inl, splitGram_middle_middle, splitGram_middle_eStar, ite_mul,
    one_mul, middleGram_inl_inl, Finset.sum_ite_eq, middleGram_inl_inr, reduceCtorEq,
    splitGram_eStar_inl, splitGram_eStar_middle,
    splitGram_eStar_eStar] at h
  rw [besselOmega_apply, ← neg_eq_of_add_eq_zero_right h]
  simp

/-- **The composition law of `ω`.** For `u ∈ U⁰` and `v` an isometry fixing the frame,
`ω(uv) = ω(u) + ω(v)`. -/
theorem besselOmega_mul (hu : u ∈ besselU0 ϱ (middleGram N))
    (hv : v ∈ frameFixingSubgroup ϱ (middleGram N)) :
    besselOmega (((u * v : unitaryGroupOf _) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      besselOmega ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) +
        besselOmega ((v : GL (BesselIndex ϱ κ) R) :
          Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
  have hU := (mem_besselU0 ϱ _).mp hu
  ext i b
  simp [Matrix.mul_apply, Fintype.sum_sum_type, apply_inl_of_mem_frameFixingSubgroup hU.2,
    apply_middle_middle_of_mem_besselU hU.1, apply_eStar_of_mem_frameFixingSubgroup hv,
    Matrix.one_apply]

/-- **The composition law of `μ`.** For `u ∈ U⁰` and `v` an isometry fixing the frame,
`μ(uv) = μ(u) + μ(v) + ω(u)ᴴ ω(v)`. -/
theorem besselMu_mul (hu : u ∈ besselU0 ϱ (middleGram N))
    (hv : v ∈ frameFixingSubgroup ϱ (middleGram N)) :
    besselMu (((u * v : unitaryGroupOf _) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      besselMu ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) +
        besselMu ((v : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) +
        (besselOmega ((u : GL (BesselIndex ϱ κ) R) :
          Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R))ᴴ *
          besselOmega ((v : GL (BesselIndex ϱ κ) R) :
            Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
  have hU := (mem_besselU0 ϱ _).mp hu
  ext a b
  simp [Matrix.mul_apply, Fintype.sum_sum_type, apply_inl_of_mem_frameFixingSubgroup hU.2,
    apply_z_of_mem_frameFixingSubgroup hU.2, apply_inl_x_of_mem_besselU0 hu,
    apply_eStar_of_mem_frameFixingSubgroup hv, Matrix.one_apply, add_right_comm]

/-- **The hermitian part of `μ`.** For an isometry `u` of the split form of `diag(1_κ, -N)` fixing
the frame, `μ + μᴴ = ωᴴ ω`. -/
theorem besselMu_add_conjTranspose (hu : u ∈ frameFixingSubgroup ϱ (middleGram N)) :
    besselMu ((u : GL (BesselIndex ϱ κ) R) : Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) +
        (besselMu ((u : GL (BesselIndex ϱ κ) R) :
          Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R))ᴴ =
      (besselOmega ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R))ᴴ *
        besselOmega ((u : GL (BesselIndex ϱ κ) R) :
          Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
  ext a b
  -- the entry `(e*_a, e*_b)` of `uᴴ G u = G`; the `z`-term vanishes since `N u (z, e*_b) = 0`
  have h := congrFun (congrFun (unitaryGroupOf.conjTranspose_mul_mul_cancel u)
    (.inr (.inr a))) (.inr (.inr b))
  simp only [Matrix.mul_apply, conjTranspose_apply, Fintype.sum_sum_type, Finset.univ_unique,
    PUnit.default_eq_unit, Finset.sum_singleton, apply_eStar_of_mem_frameFixingSubgroup hu,
    Matrix.one_apply, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, splitGram_inl_inl, zero_mul, Finset.sum_const_zero,
    splitGram_inl_middle, add_zero, splitGram_inl_eStar, zero_add, splitGram_middle_inl,
    splitGram_middle_middle, splitGram_middle_eStar, middleGram_inl_inl, ite_mul, one_mul,
    Finset.sum_ite_eq, middleGram_inl_inr, middleGram_inr_inl, middleGram_inr_inr, neg_mul,
    mul_apply_z_eStar_of_mem_frameFixingSubgroup hu, neg_zero, apply_ite (star : R → R),
    star_one, star_zero, splitGram_eStar_inl, splitGram_eStar_middle, splitGram_eStar_eStar] at h
  simp only [Matrix.add_apply, besselMu_apply, conjTranspose_apply, star_neg, Matrix.mul_apply,
    besselOmega_apply, mul_neg, neg_mul, neg_neg]
  linear_combination -h

/-- The `x`-coordinates of `u⁻¹` for `u ∈ U⁰`: `ω(u⁻¹) = -ω(u)`. -/
theorem besselOmega_inv (hu : u ∈ besselU0 ϱ (middleGram N)) :
    besselOmega (((u⁻¹ : unitaryGroupOf _) : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) =
      -besselOmega ((u : GL (BesselIndex ϱ κ) R) :
        Matrix (BesselIndex ϱ κ) (BesselIndex ϱ κ) R) := by
  have h := besselOmega_mul hu ((mem_besselU0 ϱ _).mp (inv_mem hu)).2
  simp only [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, besselOmega_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

end TauCeti
