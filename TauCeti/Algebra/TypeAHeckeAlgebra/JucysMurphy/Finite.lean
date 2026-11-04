/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.JucysMurphy.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Embedding

/-!
# Additive Jucys–Murphy elements in finite Hecke algebras

The additive elements in the infinite algebra restrict to every finite presentation through
`stageEquiv`. The strand index is a member of `Fin n`, so no unused indices are carried.
We provide their recursion, compatibility with the tower, and commutation laws. Unlike a
quotient by `q² - 1`, this construction also works at `q = 1`, where the elements become
the ordinary additive Jucys–Murphy elements of the symmetric group algebra.

## References

* G. E. Murphy, *On the representation theory of the symmetric groups and associated Hecke
  algebras*, J. Algebra 152 (1992), 492–513.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999).
-/

public section

namespace TauCeti.TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] (q : Rˣ) {n : ℕ}

/-- The additive Jucys–Murphy element attached to strand `k`, counted from zero, in the
finite Hecke algebra on `n` strands. It is defined without dividing by `q² - 1`. -/
noncomputable def additiveJucysMurphy (k : Fin n) : TypeAHeckeAlgebra R q n :=
  (stageEquiv R q n).symm
    ⟨InfiniteTypeAHeckeAlgebra.additiveJucysMurphy q k,
      InfiniteTypeAHeckeAlgebra.stage_mono (by omega)
        (InfiniteTypeAHeckeAlgebra.additiveJucysMurphy_mem_stage k)⟩

/-- The finite element maps to the additive Jucys–Murphy element of the infinite algebra. -/
@[simp]
theorem toInfinite_additiveJucysMurphy (k : Fin n) :
    toInfinite R q n (additiveJucysMurphy q k) =
      InfiniteTypeAHeckeAlgebra.additiveJucysMurphy q k :=
  toInfinite_stageEquiv_symm_apply _

/-- The additive element of the first strand is zero. -/
@[simp]
theorem additiveJucysMurphy_zero : additiveJucysMurphy q (0 : Fin (n + 1)) = 0 := by
  apply toInfinite_injective R q (n + 1)
  simp

/-- The finite recursion: multiply the preceding additive element on both sides by the adjacent
generator and add `q⁻¹ • T i`. The two strands of that generator are `i.castSucc` and `i.succ`. -/
theorem additiveJucysMurphy_succ (i : Fin n) :
    additiveJucysMurphy q i.succ =
      T (n := n + 1) q i * additiveJucysMurphy q i.castSucc * T (n := n + 1) q i +
        (↑q⁻¹ : R) • T (n := n + 1) q i := by
  apply toInfinite_injective R q (n + 1)
  simp only [map_add, map_mul, map_smul, toInfinite_T, toInfinite_additiveJucysMurphy,
    Fin.val_castSucc, Fin.val_succ, InfiniteTypeAHeckeAlgebra.additiveJucysMurphy_succ]

/-- The additive elements are compatible with adjoining a last strand. -/
@[simp]
theorem strandIncl_additiveJucysMurphy (k : Fin n) :
    strandIncl R q n (additiveJucysMurphy q k) = additiveJucysMurphy q k.castSucc := by
  apply toInfinite_injective R q (n + 1)
  simp

/-- The last-strand additive element centralizes the image of the preceding finite algebra. -/
theorem commute_additiveJucysMurphy_last_strandIncl (x : TypeAHeckeAlgebra R q n) :
    Commute (additiveJucysMurphy q (Fin.last n)) (strandIncl R q n x) := by
  apply toInfinite_injective R q (n + 1)
  have hx : toInfinite R q n x ∈ InfiniteTypeAHeckeAlgebra.stage R q n := by
    rw [← range_toInfinite]
    exact ⟨x, rfl⟩
  simpa only [map_mul, toInfinite_additiveJucysMurphy, toInfinite_strandIncl, Fin.val_last]
    using (InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy_of_mem_stage hx).eq

/-- The additive Jucys–Murphy elements in a finite stage commute pairwise. -/
theorem commute_additiveJucysMurphy (i j : Fin n) :
    Commute (additiveJucysMurphy q i) (additiveJucysMurphy q j) := by
  apply (toInfinite_injective R q n)
  simpa only [map_mul, toInfinite_additiveJucysMurphy] using
    (InfiniteTypeAHeckeAlgebra.commute_additiveJucysMurphy (q := q) i j).eq

/-- A simple generator commutes with an additive element unless it crosses its strand. -/
theorem commute_T_additiveJucysMurphy {i : Fin (n - 1)} {k : Fin n}
    (h : (i : ℕ) + 1 < k ∨ (k : ℕ) < i) :
    Commute (T q i) (additiveJucysMurphy q k) := by
  apply (toInfinite_injective R q n)
  simpa only [map_mul, toInfinite_T, toInfinite_additiveJucysMurphy] using
    (InfiniteTypeAHeckeAlgebra.commute_T_additiveJucysMurphy (q := q) h).eq

/-- A simple generator commutes with the sum of the additive elements of the two strands
it crosses. -/
theorem commute_T_additiveJucysMurphy_add (i : Fin n) :
    Commute (T (n := n + 1) q i)
      (additiveJucysMurphy q i.castSucc + additiveJucysMurphy q i.succ) := by
  apply toInfinite_injective R q (n + 1)
  simpa only [map_mul, map_add, toInfinite_T, toInfinite_additiveJucysMurphy,
    Fin.val_castSucc, Fin.val_succ] using
    (InfiniteTypeAHeckeAlgebra.commute_T_additiveJucysMurphy_add (q := q) i).eq

end TauCeti.TypeAHeckeAlgebra
