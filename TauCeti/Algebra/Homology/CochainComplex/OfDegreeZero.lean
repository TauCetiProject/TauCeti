/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Contractions of `ℕ`-indexed cochain complexes onto degree `0`

Let `K` be a cochain complex indexed by `ℕ` in a preadditive category, and let
`h n : Kⁿ⁺¹ ⟶ Kⁿ` be maps lowering the degree with
$$d \circ h + h \circ d = 1 \text{ on } K^{n + 1}, \qquad h \circ d = 1 - P \text{ on } K^0$$
for an endomorphism `P` of `K⁰`. Then the composite of `P` with the differential vanishes
(`CochainComplex.comp_d_zero_eq_zero_of_d_comp_eq`), so `P` placed in degree `0` is an endomorphism
of `K` (`CochainComplex.ofDegreeZero`), and the maps `h` form a homotopy from the identity of `K`
to it (`CochainComplex.homotopyOfDCompEq`). For a complex of modules, every positive-degree
cocycle `φ` is the coboundary of `h φ` (`CochainComplex.d_hom_apply_of_d_comp_eq`).

This is the formal part shared by the contractions of cochain complexes that insert an argument
weighted by an averaging or cutoff function: the contraction of the cochains of a groupoid nerve
`TauCeti.nerveCochainComplex.cutoffHomotopy`, and those of inhomogeneous group cochains
`TauCeti.groupCohomology.homotopyOfDCompEq`.

## Main declarations

* `CochainComplex.ofDegreeZero`: an endomorphism of `K⁰` whose composite with the differential
  vanishes, placed in degree `0`, as an endomorphism of `K`.
* `CochainComplex.homotopyOfDCompEq`: the homotopy from the identity to
  `CochainComplex.ofDegreeZero`.
* `CochainComplex.d_hom_apply_of_d_comp_eq`: the explicit primitive of a positive-degree cocycle.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace CochainComplex

variable {V : Type u} [Category.{v} V] [Preadditive V] (K : CochainComplex V ℕ)

/-- An endomorphism `P` of `K⁰` with `P ≫ d = 0`, placed in degree `0`, as an endomorphism of
the cochain complex `K`: it is `P` in degree `0` and zero in positive degrees. -/
def ofDegreeZero (P : K.X 0 ⟶ K.X 0) (hP : P ≫ K.d 0 1 = 0) : K ⟶ K where
  f
    | 0 => P
    | _ + 1 => 0
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rcases i with _ | i
    · exact hP.trans comp_zero.symm
    · exact zero_comp.trans comp_zero.symm

variable {K} {P : K.X 0 ⟶ K.X 0}

/-- In degree `0`, `CochainComplex.ofDegreeZero K P hP` is `P`. -/
@[simp]
theorem ofDegreeZero_f_zero (hP : P ≫ K.d 0 1 = 0) : (K.ofDegreeZero P hP).f 0 = P :=
  (rfl)

/-- In positive degrees, `CochainComplex.ofDegreeZero K P hP` is zero. -/
@[simp]
theorem ofDegreeZero_f_succ (hP : P ≫ K.d 0 1 = 0) (n : ℕ) :
    (K.ofDegreeZero P hP).f (n + 1) = 0 :=
  (rfl)

variable {h : ∀ n : ℕ, K.X (n + 1) ⟶ K.X n}
variable (hd : ∀ n : ℕ, K.d (n + 1) (n + 2) ≫ h (n + 1) + h n ≫ K.d n (n + 1) = 𝟙 _)
  (hd₀ : K.d 0 1 ≫ h 0 = 𝟙 _ - P)

include hd hd₀ in
/-- If `d ∘ h + h ∘ d = 1` in positive degrees and `h ∘ d = 1 - P` in degree `0`, then the
composite of `P` with the differential vanishes. -/
theorem comp_d_zero_eq_zero_of_d_comp_eq : P ≫ K.d 0 1 = 0 := by
  have hP : P = 𝟙 _ - K.d 0 1 ≫ h 0 := by rw [hd₀, sub_sub_cancel]
  have hh : h 0 ≫ K.d 0 1 = 𝟙 _ - K.d 1 2 ≫ h 1 := by rw [← hd 0, add_sub_cancel_left]
  simp [hP, hh, Preadditive.sub_comp, Preadditive.comp_sub]

/-- The components `h j` of the homotopy, from degree `j + 1` to degree `j`. -/
private def homotopyOfDCompEqHom (i j : ℕ) (hji : (ComplexShape.up ℕ).Rel j i) : K.X i ⟶ K.X j :=
  (K.XIsoOfEq hji.symm).hom ≫ h j

include hd hd₀ in
private theorem sub_ofDegreeZero_eq_nullHomotopicMap' :
    𝟙 _ - K.ofDegreeZero P (comp_d_zero_eq_zero_of_d_comp_eq hd hd₀) =
      Homotopy.nullHomotopicMap' (homotopyOfDCompEqHom (h := h)) := by
  ext n : 1
  rcases n with _ | n
  · -- Degree `0` has no incoming differential, so only `d ≫ h` contributes.
    rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
      (fun l ↦ by simp)]
    simp [homotopyOfDCompEqHom, hd₀]
  · rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
      (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl)]
    simp [homotopyOfDCompEqHom, hd n]

/-- **The contraction defined by maps lowering the degree.** If `d ∘ h + h ∘ d = 1` in positive
degrees and `h ∘ d = 1 - P` in degree `0`, then the identity of `K` is homotopic to `P` placed in
degree `0`, through the homotopy whose component from degree `n + 1` to degree `n` is `h n`
(`CochainComplex.homotopyOfDCompEq_hom_succ`). -/
def homotopyOfDCompEq :
    Homotopy (𝟙 K) (K.ofDegreeZero P (comp_d_zero_eq_zero_of_d_comp_eq hd hd₀)) :=
  Homotopy.equivSubZero.symm <|
    (Homotopy.ofEq (sub_ofDegreeZero_eq_nullHomotopicMap' hd hd₀)).trans (Homotopy.nullHomotopy' _)

/-- The component of `CochainComplex.homotopyOfDCompEq` from degree `n + 1` to degree `n` is
`h n`. -/
@[simp]
theorem homotopyOfDCompEq_hom_succ (n : ℕ) : (homotopyOfDCompEq hd hd₀).hom (n + 1) n = h n := by
  simp [homotopyOfDCompEq, Homotopy.equivSubZero, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.nullHomotopy'_hom, homotopyOfDCompEqHom]

/-- **The explicit primitive of a positive-degree cocycle.** For a cochain complex of modules, if
`d ∘ h + h ∘ d = 1` on `Kⁿ⁺¹`, then a cocycle `φ` of degree `n + 1` is the coboundary of
`h φ`. -/
theorem d_hom_apply_of_d_comp_eq {R : Type*} [Ring R] {K : CochainComplex (ModuleCat R) ℕ}
    {h : ∀ n : ℕ, K.X (n + 1) ⟶ K.X n} {n : ℕ}
    (hd : K.d (n + 1) (n + 2) ≫ h (n + 1) + h n ≫ K.d n (n + 1) = 𝟙 _) {φ : K.X (n + 1)}
    (hφ : (K.d (n + 1) (n + 2)).hom φ = 0) : (K.d n (n + 1)).hom ((h n).hom φ) = φ := by
  simpa [hφ] using congr($(hd).hom φ)

end CochainComplex
