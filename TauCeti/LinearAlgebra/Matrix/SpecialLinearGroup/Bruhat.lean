/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Borel
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Unique Bruhat coordinates and fixed-point descent for `SL₂`

The big cell of `SL₂(R)` has unique coordinates `u(x) S b`, where `u(x)` is upper
unipotent, `S = !![0, -1; 1, 0]`, and `b` is upper triangular. These coordinates work over
any commutative ring, with the big cell detected by an invertible lower-left entry.

The coordinate map commutes with every ring homomorphism. In particular, a matrix in the big
cell is fixed by an entrywise ring endomorphism exactly when both factors are fixed. This gives
a Bruhat decomposition of the fixed subgroup over a field, without a surjectivity assumption
on the endomorphism. Uniqueness of the factors, rather than just uniqueness of the Bruhat cell,
is essential to this descent.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 11, Theorem 33, for descent by
  uniqueness of Bruhat factors.
-/

public section

open scoped MatrixGroups

namespace TauCeti.SL2Borel

variable {R A : Type*} [CommRing R] [CommRing A]

/-- The normalized big-cell product `u(x) S b`, with left factor upper unipotent. -/
def bruhat (x : R) (b : SL2Borel R) : SL(2, R) :=
  (mk 1 x : SL(2, R)) * ((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) * b

/-- The normalized big-cell product is the product of its unipotent, Weyl and Borel factors. -/
theorem bruhat_def (x : R) (b : SL2Borel R) :
    bruhat x b =
      (mk 1 x : SL(2, R)) * ((ModularGroup.S : SL(2, ℤ)) : SL(2, R)) * b :=
  (rfl)

/-- The matrix entries of the normalized big-cell product. -/
@[simp]
theorem coe_bruhat (x : R) (b : SL2Borel R) :
    (bruhat x b : Matrix (Fin 2) (Fin 2) R) =
      !![x * (diag b : R), -(↑((diag b)⁻¹) : R) + x * upperRight b;
        (diag b : R), upperRight b] := by
  have hb : (b : Matrix (Fin 2) (Fin 2) R) =
      !![(diag b : R), upperRight b; 0, (↑((diag b)⁻¹) : R)] := by
    rw [← coe_mk, mk_diag_upperRight]
  rw [bruhat_def, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    TauCeti.Matrix.SpecialLinearGroup.coe_modularGroup_S, coe_mk, hb,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [add_comm]

/-- The upper-left entry of a normalized Bruhat product. -/
@[simp]
theorem bruhat_apply_zero_zero (x : R) (b : SL2Borel R) :
    bruhat x b 0 0 = x * (diag b : R) := by
  simp [coe_bruhat]

/-- The lower-left entry of a normalized Bruhat product is the Borel diagonal parameter. -/
@[simp]
theorem bruhat_apply_one_zero (x : R) (b : SL2Borel R) :
    bruhat x b 1 0 = (diag b : R) := by
  simp [coe_bruhat]

/-- The lower-right entry of a normalized Bruhat product is the Borel upper-right parameter. -/
@[simp]
theorem bruhat_apply_one_one (x : R) (b : SL2Borel R) :
    bruhat x b 1 1 = upperRight b := by
  simp [coe_bruhat]

/-- Normalized big-cell coordinates are unique. -/
theorem bruhat_injective :
    Function.Injective (fun p : R × SL2Borel R => bruhat p.1 p.2) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ h
  have hd : diag b = diag c := Units.ext (by
    simpa only [bruhat_apply_one_zero] using congrArg (fun g : SL(2, R) => g 1 0) h)
  have hu : upperRight b = upperRight c := by
    simpa only [bruhat_apply_one_one] using congrArg (fun g : SL(2, R) => g 1 1) h
  have hb : b = c := by rw [← mk_diag_upperRight b, ← mk_diag_upperRight c, hd, hu]
  subst c
  have hx : x * (diag b : R) = y * (diag b : R) := by
    simpa only [bruhat_apply_zero_zero] using congrArg (fun g : SL(2, R) => g 0 0) h
  have hxy : x = y := (diag b).mul_left_inj.mp hx
  exact Prod.ext hxy rfl

/-- A matrix has normalized big-cell coordinates exactly when its lower-left entry is a unit. -/
theorem exists_bruhat_iff (g : SL(2, R)) :
    (∃ p : R × SL2Borel R, bruhat p.1 p.2 = g) ↔ IsUnit (g 1 0) := by
  constructor
  · rintro ⟨⟨x, b⟩, rfl⟩
    rw [bruhat_apply_one_zero]
    exact (diag b).isUnit
  · rintro ⟨c, hc⟩
    refine ⟨(g 0 0 * (↑(c⁻¹) : R), mk c (g 1 1)), ?_⟩
    rw [bruhat_def]
    exact mk_mul_modularGroup_S_mul_mk g c hc

/-- Every matrix in the big cell has exactly one normalized pair of Bruhat factors. -/
theorem existsUnique_bruhat (g : SL(2, R)) (hg : IsUnit (g 1 0)) :
    ∃! p : R × SL2Borel R, bruhat p.1 p.2 = g :=
  bruhat_injective.existsUnique_iff_exists.mpr ((exists_bruhat_iff g).mpr hg)

/-- Entrywise coefficient mapping preserves normalized Bruhat coordinates; in particular, the
chosen Weyl representative `S` is preserved. -/
@[simp]
theorem map_bruhat (φ : R →+* A) (x : R) (b : SL2Borel R) :
    Matrix.SpecialLinearGroup.map φ (bruhat x b) = bruhat (φ x) (map φ b) := by
  simp only [bruhat_def, map_mul, ← coe_map, map_mk, map_one,
    Matrix.SpecialLinearGroup.map_intCast_coe]

/-- Two normalized Bruhat products are equal exactly when both coordinates agree. -/
@[simp]
theorem bruhat_inj (x y : R) (b c : SL2Borel R) :
    bruhat x b = bruhat y c ↔ x = y ∧ b = c :=
  (bruhat_injective.eq_iff (a := (x, b)) (b := (y, c))).trans Prod.mk_inj

/-- A fixed matrix in the big cell has unique Bruhat coordinates fixed by the same
endomorphism. No surjectivity or finite-order hypothesis on the endomorphism is required. -/
theorem existsUnique_fixed_bruhat (φ : R →+* R) (g : SL(2, R))
    (hfix : Matrix.SpecialLinearGroup.map φ g = g) (hg : IsUnit (g 1 0)) :
    ∃! p : R × SL2Borel R,
      φ p.1 = p.1 ∧ map φ p.2 = p.2 ∧ bruhat p.1 p.2 = g := by
  obtain ⟨p, hp, huniq⟩ := existsUnique_bruhat g hg
  have hf : φ p.1 = p.1 ∧ map φ p.2 = p.2 := by
    apply (bruhat_inj (φ p.1) p.1 (map φ p.2) p.2).mp
    rw [← map_bruhat, hp, hfix]
  exact ⟨p, ⟨hf.1, hf.2, hp⟩, fun q hq => huniq q hq.2.2⟩

/-- The two Bruhat cells descend to the fixed subgroup of `SL₂` over a field: a fixed matrix
is either in the fixed Borel, or has unique fixed unipotent and Borel factors in the big cell. -/
theorem mem_or_existsUnique_fixed_bruhat {K : Type*} [Field K] (φ : K →+* K) (g : SL(2, K))
    (hfix : Matrix.SpecialLinearGroup.map φ g = g) :
    g ∈ SL2Borel K ∨ ∃! p : K × SL2Borel K,
      φ p.1 = p.1 ∧ map φ p.2 = p.2 ∧ bruhat p.1 p.2 = g := by
  by_cases hg : g ∈ SL2Borel K
  · exact Or.inl hg
  · exact Or.inr (existsUnique_fixed_bruhat φ g hfix
      (isUnit_iff_ne_zero.mpr (mem_iff.not.mp hg)))

end TauCeti.SL2Borel
