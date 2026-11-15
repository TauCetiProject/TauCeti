/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Star
public import TauCeti.Algebra.TypeAHeckeAlgebra.Turnover

/-!
# Reversed (tail) Jucys–Murphy elements and first-site recursion

The standard Jucys–Murphy family `jucysMurphy q i` (`i : Fin n`) is adapted to the prefix tower
`strandIncl`: it starts at `1` on strand `0` and steps toward the last strand, so
`jucysMurphy q (Fin.last n)` centralizes the prefix subalgebra `(strandIncl R q n).range`.

Applying the diagram-turnover automorphism `strandRevEquiv q n` (`T q i ↦ T q i.rev`) produces the
dual family `tailJucysMurphy q i = strandRevEquiv q n (jucysMurphy q i.rev)` and its
denominator-free additive companion `tailAdditiveJucysMurphy q i`, adapted to the shifted-tail
inclusion `tailIncl`:

* `tailJucysMurphy q (Fin.last n) = 1` and `tailAdditiveJucysMurphy q (Fin.last n) = 0`;
* `tailIncl q n (tailJucysMurphy q i) = tailJucysMurphy q i.succ` (and likewise for the additive
  family);
* stepping downward across crossing `i : Fin n` in `TypeAHeckeAlgebra R q (n + 1)` conjugates by
  `T q i`, giving at strand `0` the first-site recursion
  `tailJucysMurphy q (0 : Fin (n + 2)) = T q 0 * tailIncl q (n + 1) (tailJucysMurphy q 0) * T q 0`
  and its additive counterpart valid also at `q² = 1`;
* `tailJucysMurphy q (0 : Fin (n + 1))` centralizes `(tailIncl q n).range` and is conjugate to the
  last prefix Jucys–Murphy element `jucysMurphy q (Fin.last n)` by the longest-element basis unit
  `Tw q (permCoxeterSystem (n + 1)) Fin.revPerm`.

## Main definitions

* `TauCeti.TypeAHeckeAlgebra.tailJucysMurphy`: reversed normalized Jucys–Murphy elements in
  `TypeAHeckeAlgebra R q n`.
* `TauCeti.TypeAHeckeAlgebra.tailAdditiveJucysMurphy`: reversed additive Jucys–Murphy elements,
  defined without dividing by `q² - 1`.

## Main results

* `TauCeti.TypeAHeckeAlgebra.tailIncl_tailJucysMurphy` and
  `TauCeti.TypeAHeckeAlgebra.tailIncl_tailAdditiveJucysMurphy`: compatibility with `tailIncl`.
* `TauCeti.TypeAHeckeAlgebra.tailJucysMurphy_zero_succ` and
  `TauCeti.TypeAHeckeAlgebra.tailAdditiveJucysMurphy_zero_succ`: first-site recursion along
  `tailIncl`.
* `TauCeti.TypeAHeckeAlgebra.commute_tailJucysMurphy_zero_tailIncl` and
  `TauCeti.TypeAHeckeAlgebra.commute_tailAdditiveJucysMurphy_zero_tailIncl`: the first-site
  elements centralize the shifted-tail subalgebra.
* `TauCeti.TypeAHeckeAlgebra.Tw_revPerm_mul_jucysMurphy_last` and
  `TauCeti.TypeAHeckeAlgebra.apply_tailJucysMurphy_of_mul_comm`: longest-element conjugacy and
  tracial agreement with the prefix Jucys–Murphy elements.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* M. Geck and G. Pfeiffer, *Characters of Finite Coxeter Groups and Iwahori-Hecke Algebras*,
  OUP (2000), Chapter 7.
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ} {n : ℕ}

variable (q) in
/-- The reversed (tail) normalized Jucys–Murphy element attached to strand `i` in
`TypeAHeckeAlgebra R q n`, defined as `strandRevEquiv q n (jucysMurphy q i.rev)`. At `i = 0` this
is the first-site Jucys–Murphy element centralizing the shifted-tail subalgebra. -/
noncomputable def tailJucysMurphy (i : Fin n) : TypeAHeckeAlgebra R q n :=
  strandRevEquiv q n (jucysMurphy q i.rev)

variable (q) in
/-- The reversed (tail) additive Jucys–Murphy element attached to strand `i` in
`TypeAHeckeAlgebra R q n`, defined as `strandRevEquiv q n (additiveJucysMurphy q i.rev)`. Unlike
`(tailJucysMurphy q i - 1) / (q² - 1)`, this definition requires no invertibility of `q² - 1` and
reduces at `q² = 1` to the reversed Jucys–Murphy element of the symmetric group. -/
noncomputable def tailAdditiveJucysMurphy (i : Fin n) : TypeAHeckeAlgebra R q n :=
  strandRevEquiv q n (additiveJucysMurphy q i.rev)

/-- Diagram turnover exchanges prefix and tail normalized Jucys–Murphy elements. -/
@[simp]
theorem strandRevEquiv_jucysMurphy (i : Fin n) :
    strandRevEquiv q n (jucysMurphy q i) = tailJucysMurphy q i.rev := by
  simp [tailJucysMurphy]

/-- Diagram turnover sends a tail normalized Jucys–Murphy element back to the reversed prefix
element. -/
@[simp]
theorem strandRevEquiv_tailJucysMurphy (i : Fin n) :
    strandRevEquiv q n (tailJucysMurphy q i) = jucysMurphy q i.rev := by
  rw [tailJucysMurphy, strandRevEquiv_strandRevEquiv]

/-- Diagram turnover exchanges prefix and tail additive Jucys–Murphy elements. -/
@[simp]
theorem strandRevEquiv_additiveJucysMurphy (i : Fin n) :
    strandRevEquiv q n (additiveJucysMurphy q i) = tailAdditiveJucysMurphy q i.rev := by
  simp [tailAdditiveJucysMurphy]

/-- Diagram turnover sends a tail additive Jucys–Murphy element back to the reversed prefix
element. -/
@[simp]
theorem strandRevEquiv_tailAdditiveJucysMurphy (i : Fin n) :
    strandRevEquiv q n (tailAdditiveJucysMurphy q i) = additiveJucysMurphy q i.rev := by
  rw [tailAdditiveJucysMurphy, strandRevEquiv_strandRevEquiv]

/-- The tail normalized Jucys–Murphy element of the last strand is `1`. -/
@[simp]
theorem tailJucysMurphy_last :
    tailJucysMurphy q (Fin.last n) = (1 : TypeAHeckeAlgebra R q (n + 1)) := by
  simp [tailJucysMurphy]

/-- The tail additive Jucys–Murphy element of the last strand is `0`. -/
@[simp]
theorem tailAdditiveJucysMurphy_last :
    tailAdditiveJucysMurphy q (Fin.last n) = (0 : TypeAHeckeAlgebra R q (n + 1)) := by
  simp [tailAdditiveJucysMurphy]

/-- On a single strand, the first-site normalized Jucys–Murphy element is `1`. -/
@[simp]
theorem tailJucysMurphy_zero_one :
    tailJucysMurphy q (0 : Fin 1) = (1 : TypeAHeckeAlgebra R q 1) :=
  tailJucysMurphy_last

/-- On a single strand, the first-site additive Jucys–Murphy element is `0`. -/
@[simp]
theorem tailAdditiveJucysMurphy_zero_one :
    tailAdditiveJucysMurphy q (0 : Fin 1) = (0 : TypeAHeckeAlgebra R q 1) :=
  tailAdditiveJucysMurphy_last

/-- Adding an uncrossed first strand via `tailIncl` shifts the indices of the tail normalized
Jucys–Murphy elements by `Fin.succ`. -/
@[simp]
theorem tailIncl_tailJucysMurphy (i : Fin n) :
    tailIncl q n (tailJucysMurphy q i) = tailJucysMurphy q i.succ := by
  rw [tailJucysMurphy, ← strandRevEquiv_strandIncl, strandIncl_jucysMurphy, ← Fin.rev_succ,
    tailJucysMurphy]

/-- Adding an uncrossed first strand via `tailIncl` shifts the indices of the tail additive
Jucys–Murphy elements by `Fin.succ`. -/
@[simp]
theorem tailIncl_tailAdditiveJucysMurphy (i : Fin n) :
    tailIncl q n (tailAdditiveJucysMurphy q i) = tailAdditiveJucysMurphy q i.succ := by
  rw [tailAdditiveJucysMurphy, ← strandRevEquiv_strandIncl, strandIncl_additiveJucysMurphy,
    ← Fin.rev_succ, tailAdditiveJucysMurphy]

/-- Downward recursion `X_i = T_i X_(i+1) T_i` for the tail normalized Jucys–Murphy elements in
`TypeAHeckeAlgebra R q (n + 1)`. -/
theorem tailJucysMurphy_castSucc (i : Fin n) :
    tailJucysMurphy q i.castSucc =
      T (n := n + 1) q i * tailJucysMurphy q i.succ * T (n := n + 1) q i := by
  have hrev : (i.castSucc.rev : Fin (n + 1)) = ⟨i.rev.val + 1, by omega⟩ := by
    ext
    simp [Fin.rev_castSucc]
  have hsucc : (⟨i.rev.val, by omega⟩ : Fin (n + 1)) = i.succ.rev := by
    ext
    simp [Fin.rev_succ]
  have hT : (⟨i.rev.val, by omega⟩ : Fin n) = i.rev := Fin.ext rfl
  rw [tailJucysMurphy, hrev, jucysMurphy_succ i.rev.val (by omega), hsucc, hT, map_mul, map_mul,
    strandRevEquiv_T, Fin.rev_rev, ← tailJucysMurphy]

/-- Downward recursion `L^tail_i = T_i L^tail_(i+1) T_i + q⁻¹ • T_i` for the tail additive
Jucys–Murphy elements in `TypeAHeckeAlgebra R q (n + 1)`. -/
theorem tailAdditiveJucysMurphy_castSucc (i : Fin n) :
    tailAdditiveJucysMurphy q i.castSucc =
      T (n := n + 1) q i * tailAdditiveJucysMurphy q i.succ * T (n := n + 1) q i +
        (↑q⁻¹ : R) • T (n := n + 1) q i := by
  have hrev : (i.castSucc.rev : Fin (n + 1)) = ⟨i.rev.val + 1, by omega⟩ := by
    ext
    simp [Fin.rev_castSucc]
  have hsucc : (⟨i.rev.val, by omega⟩ : Fin (n + 1)) = i.succ.rev := by
    ext
    simp [Fin.rev_succ]
  have hT : (⟨i.rev.val, by omega⟩ : Fin n) = i.rev := Fin.ext rfl
  rw [tailAdditiveJucysMurphy, hrev, additiveJucysMurphy_succ i.rev.val (by omega), hsucc, hT,
    map_add, map_mul, map_mul, map_smul, strandRevEquiv_T, Fin.rev_rev, ← tailAdditiveJucysMurphy]

/-- For arbitrary `n`, the tail normalized Jucys–Murphy element at the last index `n - 1` is `1`. -/
theorem tailJucysMurphy_eq_one_of_val {i : Fin n} (hi : (i : ℕ) + 1 = n) :
    tailJucysMurphy q i = (1 : TypeAHeckeAlgebra R q n) := by
  have : NeZero n := ⟨by omega⟩
  have hrev : i.rev = (0 : Fin n) := Fin.ext (by simp [Fin.val_rev]; omega)
  rw [tailJucysMurphy, hrev, jucysMurphy_zero, map_one]

/-- For arbitrary `n`, the tail additive Jucys–Murphy element at the last index `n - 1` is `0`. -/
theorem tailAdditiveJucysMurphy_eq_zero_of_val {i : Fin n} (hi : (i : ℕ) + 1 = n) :
    tailAdditiveJucysMurphy q i = (0 : TypeAHeckeAlgebra R q n) := by
  have : NeZero n := ⟨by omega⟩
  have hrev : i.rev = (0 : Fin n) := Fin.ext (by simp [Fin.val_rev]; omega)
  rw [tailAdditiveJucysMurphy, hrev, additiveJucysMurphy_zero, map_zero]

/-- Downward recursion for `tailJucysMurphy` at any non-final strand `(i : ℕ) + 1 < n`. -/
theorem tailJucysMurphy_of_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    tailJucysMurphy q i =
      T q ⟨i.val, by omega⟩ * tailJucysMurphy q ⟨i.val + 1, hi⟩ * T q ⟨i.val, by omega⟩ := by
  have hrev : i.rev = ⟨n - 2 - i.val + 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have hnext : (⟨n - 2 - i.val, by omega⟩ : Fin n) = (⟨i.val + 1, hi⟩ : Fin n).rev :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  have hT : (⟨n - 2 - i.val, by omega⟩ : Fin (n - 1)).rev = ⟨i.val, by omega⟩ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  rw [tailJucysMurphy, hrev, jucysMurphy_succ (n - 2 - i.val) (by omega), hnext, map_mul, map_mul,
    strandRevEquiv_T, hT, ← tailJucysMurphy]

/-- Downward recursion for `tailAdditiveJucysMurphy` at any non-final strand `(i : ℕ) + 1 < n`. -/
theorem tailAdditiveJucysMurphy_of_lt {i : Fin n} (hi : (i : ℕ) + 1 < n) :
    tailAdditiveJucysMurphy q i =
      T q ⟨i.val, by omega⟩ * tailAdditiveJucysMurphy q ⟨i.val + 1, hi⟩ * T q ⟨i.val, by omega⟩ +
        (↑q⁻¹ : R) • T q ⟨i.val, by omega⟩ := by
  have hrev : i.rev = ⟨n - 2 - i.val + 1, by omega⟩ := Fin.ext (by simp [Fin.val_rev]; omega)
  have hnext : (⟨n - 2 - i.val, by omega⟩ : Fin n) = (⟨i.val + 1, hi⟩ : Fin n).rev :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  have hT : (⟨n - 2 - i.val, by omega⟩ : Fin (n - 1)).rev = ⟨i.val, by omega⟩ :=
    Fin.ext (by simp [Fin.val_rev]; omega)
  rw [tailAdditiveJucysMurphy, hrev, additiveJucysMurphy_succ (n - 2 - i.val) (by omega), hnext,
    map_add, map_mul, map_mul, map_smul, strandRevEquiv_T, hT, ← tailAdditiveJucysMurphy]

/-- Downward recursion for `tailJucysMurphy` in the quadratic normalization `g_i = q • T i`,
`Q = q²`, where `(g_i + 1) * (g_i - Q) = 0`. -/
theorem tailJucysMurphy_castSucc_eq_smul (i : Fin n) :
    tailJucysMurphy q i.castSucc =
      ((↑q⁻¹ : R) ^ 2) •
        (((q : R) • T (n := n + 1) q i) * tailJucysMurphy q i.succ *
          ((q : R) • T (n := n + 1) q i)) := by
  rw [tailJucysMurphy_castSucc, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
    smul_smul]
  simp [sq]

/-- Downward recursion for `tailAdditiveJucysMurphy` in the quadratic normalization
`g_i = q • T i`, `Q = q²`. -/
theorem tailAdditiveJucysMurphy_castSucc_eq_smul (i : Fin n) :
    tailAdditiveJucysMurphy q i.castSucc =
      ((↑q⁻¹ : R) ^ 2) •
        (((q : R) • T (n := n + 1) q i) * tailAdditiveJucysMurphy q i.succ *
          ((q : R) • T (n := n + 1) q i) + (q : R) • T (n := n + 1) q i) := by
  rw [tailAdditiveJucysMurphy_castSucc, smul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_smul, smul_smul]
  simp [sq, mul_assoc]

/-- **First-site normalized Jucys–Murphy recursion**: `X_(n+2) = T_0 * tailIncl(X_(n+1)) * T_0`. -/
theorem tailJucysMurphy_zero_succ (n : ℕ) :
    tailJucysMurphy q (0 : Fin (n + 2)) =
      T (n := n + 2) q (0 : Fin (n + 1)) *
        tailIncl q (n + 1) (tailJucysMurphy q (0 : Fin (n + 1))) *
          T (n := n + 2) q (0 : Fin (n + 1)) := by
  have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
  rw [h0, tailJucysMurphy_castSucc, tailIncl_tailJucysMurphy]

/-- **First-site additive Jucys–Murphy recursion**:
`L^tail_(n+2) = T_0 * tailIncl(L^tail_(n+1)) * T_0 + q⁻¹ • T_0`. -/
theorem tailAdditiveJucysMurphy_zero_succ (n : ℕ) :
    tailAdditiveJucysMurphy q (0 : Fin (n + 2)) =
      T (n := n + 2) q (0 : Fin (n + 1)) *
        tailIncl q (n + 1) (tailAdditiveJucysMurphy q (0 : Fin (n + 1))) *
          T (n := n + 2) q (0 : Fin (n + 1)) +
        (↑q⁻¹ : R) • T (n := n + 2) q (0 : Fin (n + 1)) := by
  have h0 : (0 : Fin (n + 2)) = (0 : Fin (n + 1)).castSucc := rfl
  rw [h0, tailAdditiveJucysMurphy_castSucc, tailIncl_tailAdditiveJucysMurphy]

/-- Every tail normalized Jucys–Murphy element is a unit. -/
theorem isUnit_tailJucysMurphy (i : Fin n) : IsUnit (tailJucysMurphy q i) :=
  (isUnit_jucysMurphy i.rev).map (strandRevEquiv q n).toMonoidHom

/-- The tail normalized and additive elements satisfy `X_i = 1 + (q² - 1) • L^tail_i`. -/
theorem tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy (i : Fin n) :
    tailJucysMurphy q i = 1 + ((q : R) ^ 2 - 1) • tailAdditiveJucysMurphy q i := by
  rw [tailJucysMurphy, jucysMurphy_eq_one_add_smul_additiveJucysMurphy, map_add, map_one,
    map_smul, tailAdditiveJucysMurphy]

/-- At `q² = 1` the tail normalized elements collapse to `1`. -/
@[simp]
theorem tailJucysMurphy_eq_one_of_sq_eq_one (h : (q : R) ^ 2 = 1) (i : Fin n) :
    tailJucysMurphy q i = 1 := by
  rw [tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy, h, sub_self, zero_smul, add_zero]

/-- The tail normalized Jucys–Murphy elements commute pairwise. -/
theorem commute_tailJucysMurphy (i j : Fin n) :
    Commute (tailJucysMurphy q i) (tailJucysMurphy q j) :=
  (commute_jucysMurphy i.rev j.rev).map (strandRevEquiv q n).toMonoidHom

/-- The tail additive Jucys–Murphy elements commute pairwise. -/
theorem commute_tailAdditiveJucysMurphy (i j : Fin n) :
    Commute (tailAdditiveJucysMurphy q i) (tailAdditiveJucysMurphy q j) :=
  (commute_additiveJucysMurphy i.rev j.rev).map (strandRevEquiv q n).toMonoidHom

/-- **The first-site additive Jucys–Murphy element centralizes the shifted-tail subalgebra.** -/
theorem commute_tailAdditiveJucysMurphy_zero_tailIncl (x : TypeAHeckeAlgebra R q n) :
    Commute (tailAdditiveJucysMurphy q (0 : Fin (n + 1))) (tailIncl q n x) := by
  rw [commute_iff_eq]
  apply (strandRevEquiv (R := R) q (n + 1)).injective
  simpa only [map_mul, strandRevEquiv_tailAdditiveJucysMurphy, Fin.rev_zero,
    strandRevEquiv_tailIncl] using
    (commute_additiveJucysMurphy_last_strandIncl (strandRevEquiv q n x)).eq

/-- **The first-site normalized Jucys–Murphy element centralizes the shifted-tail subalgebra.** -/
theorem commute_tailJucysMurphy_zero_tailIncl (x : TypeAHeckeAlgebra R q n) :
    Commute (tailJucysMurphy q (0 : Fin (n + 1))) (tailIncl q n x) := by
  rw [tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy]
  exact (Commute.one_left _).add_left
    ((commute_tailAdditiveJucysMurphy_zero_tailIncl x).smul_left _)

/-- A simple generator commutes with a tail additive Jucys–Murphy element unless it crosses its
strand. -/
theorem commute_T_tailAdditiveJucysMurphy {i : Fin (n - 1)} {k : Fin n}
    (h : (i : ℕ) + 1 < k ∨ (k : ℕ) < i) :
    Commute (T q i) (tailAdditiveJucysMurphy q k) := by
  have hrev : (i.rev : ℕ) + 1 < k.rev ∨ (k.rev : ℕ) < i.rev := by
    simp only [Fin.val_rev]
    omega
  rw [commute_iff_eq]
  apply (strandRevEquiv (R := R) q n).injective
  simpa only [map_mul, strandRevEquiv_T, strandRevEquiv_tailAdditiveJucysMurphy] using
    (commute_T_additiveJucysMurphy (R := R) (q := q) hrev).eq

/-- A simple generator commutes with a tail normalized Jucys–Murphy element unless it crosses its
strand. -/
theorem commute_T_tailJucysMurphy {i : Fin (n - 1)} {k : Fin n}
    (h : (i : ℕ) + 1 < k ∨ (k : ℕ) < i) :
    Commute (T q i) (tailJucysMurphy q k) := by
  rw [tailJucysMurphy_eq_one_add_smul_tailAdditiveJucysMurphy]
  exact (Commute.one_right _).add_right ((commute_T_tailAdditiveJucysMurphy h).smul_right _)

/-- The longest-element basis unit `Tw q (permCoxeterSystem n) Fin.revPerm` intertwines each prefix
normalized Jucys–Murphy element with the reversed tail element. -/
theorem Tw_revPerm_mul_jucysMurphy (i : Fin n) :
    Tw q (permCoxeterSystem n) Fin.revPerm * jucysMurphy q i =
      tailJucysMurphy q i.rev * Tw q (permCoxeterSystem n) Fin.revPerm := by
  rw [Tw_revPerm_mul, strandRevEquiv_jucysMurphy]

/-- The longest-element basis unit conjugates the last prefix Jucys–Murphy element
`jucysMurphy q (Fin.last n)` to the first-site tail element `tailJucysMurphy q 0`. -/
theorem Tw_revPerm_mul_jucysMurphy_last (n : ℕ) :
    Tw q (permCoxeterSystem (n + 1)) Fin.revPerm * jucysMurphy q (Fin.last n) =
      tailJucysMurphy q (0 : Fin (n + 1)) * Tw q (permCoxeterSystem (n + 1)) Fin.revPerm := by
  simpa using Tw_revPerm_mul_jucysMurphy (R := R) (q := q) (Fin.last n)

/-- The longest-element basis unit intertwines each prefix additive Jucys–Murphy element with the
reversed tail additive element. -/
theorem Tw_revPerm_mul_additiveJucysMurphy (i : Fin n) :
    Tw q (permCoxeterSystem n) Fin.revPerm * additiveJucysMurphy q i =
      tailAdditiveJucysMurphy q i.rev * Tw q (permCoxeterSystem n) Fin.revPerm := by
  rw [Tw_revPerm_mul, strandRevEquiv_additiveJucysMurphy]

/-- The longest-element basis unit conjugates the last prefix additive Jucys–Murphy element to the
first-site tail additive element `tailAdditiveJucysMurphy q 0`. -/
theorem Tw_revPerm_mul_additiveJucysMurphy_last (n : ℕ) :
    Tw q (permCoxeterSystem (n + 1)) Fin.revPerm * additiveJucysMurphy q (Fin.last n) =
      tailAdditiveJucysMurphy q (0 : Fin (n + 1)) *
        Tw q (permCoxeterSystem (n + 1)) Fin.revPerm := by
  simpa using Tw_revPerm_mul_additiveJucysMurphy (R := R) (q := q) (Fin.last n)

/-- Every tracial map takes the same value on `tailJucysMurphy q i` and `jucysMurphy q i.rev`. -/
theorem apply_tailJucysMurphy_of_mul_comm {α : Type*} {f : TypeAHeckeAlgebra R q n → α}
    (hf : ∀ x y, f (x * y) = f (y * x)) (i : Fin n) :
    f (tailJucysMurphy q i) = f (jucysMurphy q i.rev) :=
  apply_strandRevEquiv_of_mul_comm hf _

/-- Every tracial map takes the same value on `tailAdditiveJucysMurphy q i` and
`additiveJucysMurphy q i.rev`. -/
theorem apply_tailAdditiveJucysMurphy_of_mul_comm {α : Type*} {f : TypeAHeckeAlgebra R q n → α}
    (hf : ∀ x y, f (x * y) = f (y * x)) (i : Fin n) :
    f (tailAdditiveJucysMurphy q i) = f (additiveJucysMurphy q i.rev) :=
  apply_strandRevEquiv_of_mul_comm hf _

section Star

variable [StarRing R] [Fact (IsSelfAdjoint (q : R))]

/-- The real-parameter involution fixes every tail normalized Jucys–Murphy element. -/
@[simp]
theorem star_tailJucysMurphy (i : Fin n) : star (tailJucysMurphy q i) = tailJucysMurphy q i := by
  rw [tailJucysMurphy, ← strandRevEquiv_star, star_jucysMurphy]

/-- Tail normalized Jucys–Murphy elements are self-adjoint for a star-fixed parameter. -/
theorem isSelfAdjoint_tailJucysMurphy (i : Fin n) : IsSelfAdjoint (tailJucysMurphy q i) :=
  star_tailJucysMurphy i

/-- The real-parameter involution fixes every tail additive Jucys–Murphy element. -/
@[simp]
theorem star_tailAdditiveJucysMurphy (i : Fin n) :
    star (tailAdditiveJucysMurphy q i) = tailAdditiveJucysMurphy q i := by
  rw [tailAdditiveJucysMurphy, ← strandRevEquiv_star, star_additiveJucysMurphy]

/-- Tail additive Jucys–Murphy elements are self-adjoint, including at `q² = 1`. -/
theorem isSelfAdjoint_tailAdditiveJucysMurphy (i : Fin n) :
    IsSelfAdjoint (tailAdditiveJucysMurphy q i) :=
  star_tailAdditiveJucysMurphy i

end Star

end TauCeti.TypeAHeckeAlgebra
