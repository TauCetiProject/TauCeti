/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Embedding

/-!
# Jucys–Murphy elements in the finite Hecke tower

The elements `jucysMurphy q i` and `additiveJucysMurphy q i`, for `i : Fin n`, live in the
finite presentation on `n` strands. They are the preimages of the corresponding infinite
Jucys–Murphy elements under the proved stage isomorphism. Their recursion, pairwise
commutation and compatibility with adding a last strand are consequently independent of any
choice of reduced words or basis.

With `Q = q²`, the additive elements satisfy `J_i = 1 + (Q - 1) L_i`. They are defined even
at `Q = 1`, without dividing by `Q - 1`. The last element centralizes the preceding stage;
these are the commuting elements used to distinguish successive branches of finite Hecke
modules. Self-adjointness for the real-parameter involution is proved in
`TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Star`.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}

variable (q) in
/-- The normalized Jucys–Murphy element attached to strand `i`, counted from zero, in the
finite Hecke algebra. Its image in the infinite algebra is `J_i`. -/
noncomputable def jucysMurphy (i : Fin n) : TypeAHeckeAlgebra R q n :=
  (stageEquiv R q n).symm ⟨InfiniteTypeAHeckeAlgebra.jucysMurphy q i,
    InfiniteTypeAHeckeAlgebra.stage_mono (Nat.succ_le_of_lt i.isLt)
      (InfiniteTypeAHeckeAlgebra.jucysMurphy_mem_stage i)⟩

variable (q) in
/-- The additive Jucys–Murphy element attached to strand `i`, counted from zero. Unlike the
expression `(J_i - 1) / (q² - 1)`, this definition is valid also at `q² = 1`. -/
noncomputable def additiveJucysMurphy (i : Fin n) : TypeAHeckeAlgebra R q n :=
  (stageEquiv R q n).symm ⟨InfiniteTypeAHeckeAlgebra.additiveJucysMurphy q i,
    InfiniteTypeAHeckeAlgebra.stage_mono (Nat.succ_le_of_lt i.isLt)
      (InfiniteTypeAHeckeAlgebra.additiveJucysMurphy_mem_stage i)⟩

/-- The embedding in the infinite algebra preserves the normalized Jucys–Murphy elements. -/
@[simp]
theorem toInfinite_jucysMurphy (i : Fin n) :
    toInfinite R q n (jucysMurphy q i) = InfiniteTypeAHeckeAlgebra.jucysMurphy q i := by
  simp [jucysMurphy]

/-- The embedding in the infinite algebra preserves the additive Jucys–Murphy elements. -/
@[simp]
theorem toInfinite_additiveJucysMurphy (i : Fin n) :
    toInfinite R q n (additiveJucysMurphy q i) =
      InfiniteTypeAHeckeAlgebra.additiveJucysMurphy q i := by
  simp [additiveJucysMurphy]

/-- The normalized Jucys–Murphy element of the first strand is `1`. -/
@[simp]
theorem jucysMurphy_zero [NeZero n] : jucysMurphy q (0 : Fin n) = 1 := by
  apply toInfinite_injective R q n
  simp

/-- The additive Jucys–Murphy element of the first strand is `0`. -/
@[simp]
theorem additiveJucysMurphy_zero [NeZero n] : additiveJucysMurphy q (0 : Fin n) = 0 := by
  apply toInfinite_injective R q n
  simp

/-- The finite normalized recursion `J_(k+1) = T_k J_k T_k`. -/
theorem jucysMurphy_succ (k : ℕ) (hk : k + 1 < n) :
    jucysMurphy q ⟨k + 1, hk⟩ =
      T q ⟨k, by omega⟩ * jucysMurphy q ⟨k, by omega⟩ * T q ⟨k, by omega⟩ := by
  apply toInfinite_injective R q n
  simp only [map_mul, toInfinite_jucysMurphy, toInfinite_T,
    InfiniteTypeAHeckeAlgebra.jucysMurphy_succ]

/-- Every finite normalized Jucys–Murphy element is a unit. -/
theorem isUnit_jucysMurphy (i : Fin n) : IsUnit (jucysMurphy q i) := by
  have hunit : ∀ k (hk : k < n), IsUnit (jucysMurphy q ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk
      let : NeZero n := ⟨by omega⟩
      simp
    | succ k ih =>
      intro hk
      rw [jucysMurphy_succ k hk]
      exact ((isUnit_T _).mul (ih (by omega))).mul (isUnit_T _)
  exact hunit i i.isLt

/-- The finite additive recursion, with no denominator `q² - 1`. -/
theorem additiveJucysMurphy_succ (k : ℕ) (hk : k + 1 < n) :
    additiveJucysMurphy q ⟨k + 1, hk⟩ =
      T q ⟨k, by omega⟩ * additiveJucysMurphy q ⟨k, by omega⟩ * T q ⟨k, by omega⟩ +
        (↑q⁻¹ : R) • T q ⟨k, by omega⟩ := by
  apply toInfinite_injective R q n
  simp only [map_add, map_mul, map_smul, toInfinite_additiveJucysMurphy, toInfinite_T,
    InfiniteTypeAHeckeAlgebra.additiveJucysMurphy_succ]

/-- The normalized and additive finite elements satisfy `J_i = 1 + (q² - 1) L_i`. -/
theorem jucysMurphy_eq_one_add_smul_additiveJucysMurphy (i : Fin n) :
    jucysMurphy q i = 1 + ((q : R) ^ 2 - 1) • additiveJucysMurphy q i := by
  apply toInfinite_injective R q n
  simpa only [map_add, map_one, map_smul, toInfinite_jucysMurphy,
    toInfinite_additiveJucysMurphy] using
    InfiniteTypeAHeckeAlgebra.jucysMurphy_eq_one_add_smul_additiveJucysMurphy i.val

/-- At `q² = 1` the normalized elements collapse to `1`, while the additive family remains
defined without division. -/
@[simp]
theorem jucysMurphy_eq_one_of_sq_eq_one (h : (q : R) ^ 2 = 1) (i : Fin n) :
    jucysMurphy q i = 1 := by
  rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy, h, sub_self, zero_smul, add_zero]

/-- Adding a last strand preserves the normalized Jucys–Murphy elements. -/
@[simp]
theorem strandIncl_jucysMurphy (i : Fin n) :
    strandIncl R q n (jucysMurphy q i) = jucysMurphy q i.castSucc := by
  apply toInfinite_injective R q (n + 1)
  simp

/-- Adding a last strand preserves the additive Jucys–Murphy elements. -/
@[simp]
theorem strandIncl_additiveJucysMurphy (i : Fin n) :
    strandIncl R q n (additiveJucysMurphy q i) = additiveJucysMurphy q i.castSucc := by
  apply toInfinite_injective R q (n + 1)
  simp

/-- The finite normalized Jucys–Murphy elements commute pairwise. -/
theorem commute_jucysMurphy (i j : Fin n) :
    Commute (jucysMurphy q i) (jucysMurphy q j) := by
  rw [commute_iff_eq]
  apply toInfinite_injective R q n
  simpa only [map_mul, toInfinite_jucysMurphy] using
    (InfiniteTypeAHeckeAlgebra.commute_jucysMurphy (q := q) i j).eq

/-- The finite additive Jucys–Murphy elements commute pairwise. -/
theorem commute_additiveJucysMurphy (i j : Fin n) :
    Commute (additiveJucysMurphy q i) (additiveJucysMurphy q j) := by
  rw [commute_iff_eq]
  apply toInfinite_injective R q n
  simpa only [map_mul, toInfinite_additiveJucysMurphy] using
    (InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy (q := q) i j).eq

/-- The last additive Jucys–Murphy element centralizes the preceding finite stage. -/
theorem commute_additiveJucysMurphy_last_strandIncl (x : TypeAHeckeAlgebra R q n) :
    Commute (additiveJucysMurphy q (Fin.last n)) (strandIncl R q n x) := by
  rw [commute_iff_eq]
  apply toInfinite_injective R q (n + 1)
  have hx : toInfinite R q n x ∈ InfiniteTypeAHeckeAlgebra.stage R q n := by
    rw [← range_toInfinite]
    exact ⟨x, rfl⟩
  simpa only [map_mul, toInfinite_additiveJucysMurphy, toInfinite_strandIncl, Fin.val_last] using
    (InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy_of_mem_stage hx).eq

/-- The last normalized Jucys–Murphy element centralizes the preceding finite stage. -/
theorem commute_jucysMurphy_last_strandIncl (x : TypeAHeckeAlgebra R q n) :
    Commute (jucysMurphy q (Fin.last n)) (strandIncl R q n x) := by
  rw [jucysMurphy_eq_one_add_smul_additiveJucysMurphy]
  exact (Commute.one_left _).add_left
    ((commute_additiveJucysMurphy_last_strandIncl x).smul_left _)

end TauCeti.TypeAHeckeAlgebra
