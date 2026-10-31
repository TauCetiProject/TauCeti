/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.OrthogonalSum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeA.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.CosetMinimum
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.CosetMinimum

/-!
# The shortest norm of a glue label

A glue label `a` of a simply-laced Dynkin type `t` names a coset of the root lattice
`Q = t.rootLattice ht` in its dual, through the isometry `t.glueAlphabetIsometry`.  This file
defines the least norm `μ_t(a)` of a dual vector in that coset, uniformly in `t`, by the
Conway--Sloane formulas

| type | label | `μ` |
| --- | --- | --- |
| `Aₙ` | `i ∈ ℤ/(n+1)`, `0 ≤ i ≤ n` | `i (n + 1 - i) / (n + 1)` |
| `Dₙ` | `0`, vector `v`, spinors `s` and `c` | `0`, `1`, `n/4`, `n/4` |
| `E₆` | `0`, `±1` | `0`, `4/3` |
| `E₇` | `0`, `1` | `0`, `3/2` |
| `E₈` | `0` | `0` |

and proves that it is the least norm of the coset, attained by a dual vector
(`TauCeti.DynkinType.isLeast_glueMinimum`).  The minima are the family-specific computations of
`TauCeti.IntegralLattice.isLeast_form_self_typeADiscriminantGroupEquiv`,
`isLeast_form_self_checkerboardVectorClass`, `isLeast_form_self_checkerboardSpinorClass`,
`isLeast_form_self_checkerboardCospinorClass` and their `E₆`, `E₇`, `E₈` analogues, transported to
the uniform root lattice by
`TauCeti.IntegralLattice.Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq`.
For `Dₙ` the labels are those of the glue alphabet: `(1, 0)`, `(0, 1)`, `(1, 1)` in `ℤ/2 × ℤ/2`
for even `n`, and `2`, `1`, `3` in `ℤ/4` for odd `n`, name `v`, `s` and `c`.

Two consequences hold uniformly, read off from attainment: half the shortest norm is the quadratic
value of the label (`quadratic_glueAlphabet_eq_glueMinimum_div_two`), so a label is isotropic
exactly when its shortest norm is an even integer, and only the zero label has shortest norm
zero (`glueMinimum_eq_zero_iff`).

For a glue word `w = (w_i)` of a finite family `t` of components, the coset of the orthogonal sum
`⊥ i, (t i).rootLattice` named by `w` through `TauCeti.DynkinType.glueWordIsometry` has least norm
`μ(w) = ∑ i, μ_(t i)(w_i)`, again attained (`TauCeti.DynkinType.isLeast_sum_glueMinimum`): a
shortest vector of the word's coset is a family of shortest vectors of the label cosets, by
`TauCeti.IntegralLattice.isLeast_form_self_pi`.  The two label-level consequences pass to words:
half of `μ(w)` is the quadratic value of `w`, and `μ(w) = 0` only for the zero word.

## Main declarations

* `TauCeti.DynkinType.glueMinimum`: the shortest norm `μ_t(a)` of the coset labelled `a`.
* `TauCeti.DynkinType.isLeast_glueMinimum`: `μ_t(a)` is the least norm of a dual vector in the
  coset `t.glueAlphabetIsometry hv ht a`, and it is attained.
* `TauCeti.DynkinType.quadratic_glueAlphabet_eq_glueMinimum_div_two`: `q(a) = μ_t(a) / 2 mod ℤ`.
* `TauCeti.DynkinType.glueMinimum_eq_zero_iff`: `μ_t(a) = 0` exactly when `a = 0`.
* `TauCeti.DynkinType.isLeast_sum_glueMinimum`: `μ(w) = ∑ i, μ_(t i)(w_i)` is the least norm of a
  dual vector of the orthogonal sum of root lattices in the coset named by the glue word `w`, and
  it is attained.
* `TauCeti.DynkinType.quadratic_pi_glueAlphabet_eq_sum_glueMinimum_div_two`:
  `q(w) = μ(w) / 2 mod ℤ`.
* `TauCeti.DynkinType.sum_glueMinimum_eq_zero_iff`: `μ(w) = 0` exactly when `w = 0`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  and Chapter 16, §1.
-/

public section

namespace TauCeti.DynkinType

open IntegralLattice

/-- **The shortest norm of a glue label** `a` of a simply-laced Dynkin type `t`: the least norm of
a dual vector in the coset of the root lattice labelled `a`, when `t` is valid
(`isLeast_glueMinimum`).  It is
`i (n + 1 - i) / (n + 1)` for the label `i` of `Aₙ`; `0`, `1`, `n/4`, `n/4` for the zero, vector,
spinor and cospinor labels of `Dₙ`; and `4/3` and `3/2` for the nonzero labels of `E₆` and `E₇`. -/
noncomputable def glueMinimum :
    (t : DynkinType) → (ht : t.IsSimplyLaced) → t.glueAlphabet ht → ℚ
  | A n, _ => fun a : ZMod (n + 1) ↦ (a.val : ℚ) * (n + 1 - a.val) / (n + 1)
  | D n, ht =>
    if hn : Even n then fun a ↦
      let b : ZMod 2 × ZMod 2 :=
        FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn) a
      if b = 0 then 0 else if b = (1, 0) then 1 else (n : ℚ) / 4
    else fun a ↦
      let b : ZMod 4 := FiniteQuadraticModule.Isometry.ofEq
        (glueAlphabet_D_of_odd n ht (Nat.not_even_iff_odd.mp hn)) a
      if b = 0 then 0 else if b = 2 then 1 else (n : ℚ) / 4
  | E6, _ => fun a : ZMod 3 ↦ if a = 0 then 0 else 4 / 3
  | E7, _ => fun a : ZMod 2 ↦ if a = 0 then 0 else 3 / 2
  | E8, _ => fun _ ↦ 0
  | B n, h => absurd h (not_isSimplyLaced_B n)
  | C n, h => absurd h (not_isSimplyLaced_C n)
  | F4, h => absurd h not_isSimplyLaced_F4
  | G2, h => absurd h not_isSimplyLaced_G2

/-- The shortest norm of the label `i` of `Aₙ` is `i (n + 1 - i) / (n + 1)`. -/
@[simp]
theorem glueMinimum_A (n : ℕ) (ht : (A n).IsSimplyLaced) (a : ZMod (n + 1)) :
    (A n).glueMinimum ht a = (a.val : ℚ) * (n + 1 - a.val) / (n + 1) :=
  (rfl)

/-- For even `n`, the labels `0`, `(1, 0)`, `(0, 1)`, `(1, 1)` of `Dₙ` have shortest norms `0`,
`1`, `n/4`, `n/4`. -/
theorem glueMinimum_D_of_even (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Even n)
    (a : (D n).glueAlphabet ht) (b : ZMod 2 × ZMod 2)
    (hb : FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn) a = b) :
    (D n).glueMinimum ht a = if b = 0 then 0 else if b = (1, 0) then 1 else (n : ℚ) / 4 := by
  subst hb
  simp only [glueMinimum, dite_eq_left hn]

/-- For odd `n`, the labels `0`, `2`, `1`, `3` of `Dₙ` have shortest norms `0`, `1`, `n/4`,
`n/4`. -/
theorem glueMinimum_D_of_odd (n : ℕ) (ht : (D n).IsSimplyLaced) (hn : Odd n)
    (a : (D n).glueAlphabet ht) (b : ZMod 4)
    (hb : FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn) a = b) :
    (D n).glueMinimum ht a = if b = 0 then 0 else if b = 2 then 1 else (n : ℚ) / 4 := by
  subst hb
  simp only [glueMinimum, dite_eq_right (Nat.not_even_iff_odd.mpr hn)]

/-- The nonzero labels of `E₆` have shortest norm `4/3`. -/
@[simp]
theorem glueMinimum_E6 (ht : E6.IsSimplyLaced) (a : ZMod 3) :
    E6.glueMinimum ht a = if a = 0 then 0 else 4 / 3 :=
  (rfl)

/-- The nonzero label of `E₇` has shortest norm `3/2`. -/
@[simp]
theorem glueMinimum_E7 (ht : E7.IsSimplyLaced) (a : ZMod 2) :
    E7.glueMinimum ht a = if a = 0 then 0 else 3 / 2 :=
  (rfl)

/-- The only label of `E₈` has shortest norm `0`. -/
@[simp]
theorem glueMinimum_E8 (ht : E8.IsSimplyLaced) (a : E8.glueAlphabet ht) :
    E8.glueMinimum ht a = 0 :=
  (rfl)

/-- **The shortest norm of a glue label is attained and minimal.**  For a valid simply-laced
Dynkin type `t`, `t.glueMinimum ht a` is the least norm of a dual vector of the root lattice in
the coset `t.glueAlphabetIsometry hv ht a` labelled `a`, and some dual vector of that coset has
this norm. -/
theorem isLeast_glueMinimum (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    (a : t.glueAlphabet ht) :
    IsLeast {q : ℚ | ∃ x : (t.rootLattice ht).dualCarrier,
      Submodule.Quotient.mk x = t.glueAlphabetIsometry hv ht a ∧
        (t.rootLattice ht).form x x = q} (t.glueMinimum ht a) := by
  cases t with
  | A n =>
    exact (Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq
      (Isometry.ofEq (rootLattice_A n ht).symm) (glueAlphabetIsometry_A_apply n hv ht a).symm).mpr
        (isLeast_form_self_typeADiscriminantGroupEquiv a)
  | D n =>
    have : NeZero n := ⟨by have := valid_D.mp hv; omega⟩
    rcases Nat.even_or_odd n with hn | hn
    · refine (Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq
        (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm
        (glueAlphabetIsometry_D_apply_of_even n hv ht hn a).symm).mpr ?_
      rw [glueMinimum_D_of_even n ht hn a _ rfl]
      exact isLeast_form_self_zmodTwoProdAddEquivCheckerboardDiscriminantGroup hn _
    · refine (Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq
        (rootLatticeIsometryCheckerboard n (valid_D.mp hv) ht).symm
        (glueAlphabetIsometry_D_apply_of_odd n hv ht hn a).symm).mpr ?_
      rw [glueMinimum_D_of_odd n ht hn a _ rfl]
      exact isLeast_form_self_zmodFourAddEquivCheckerboardDiscriminantGroup hn _
  | E6 =>
    exact (Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq
      (Isometry.ofEq (rootLattice_E6 ht).symm) (glueAlphabetIsometry_E6_apply hv ht a).symm).mpr
        (isLeast_form_self_typeE₆DiscriminantGroupEquiv a)
  | E7 =>
    exact (Isometry.isLeast_form_self_iff_of_discriminantGroupEquiv_eq
      (Isometry.ofEq (rootLattice_E7 ht).symm) (glueAlphabetIsometry_E7_apply hv ht a).symm).mpr
        (isLeast_form_self_typeE₇DiscriminantGroupEquiv a)
  | E8 =>
    rw [Subsingleton.elim a 0, map_zero, glueMinimum_E8]
    exact (isPosDef_rootLattice E8 ht).isPosSemidef.isLeast_form_self_zero
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Shortest norms are nonnegative.** -/
theorem glueMinimum_nonneg (t : DynkinType) (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    0 ≤ t.glueMinimum ht a := by
  cases t with
  | A n =>
    have : (ZMod.val (n := n + 1) a : ℚ) < n + 1 := by exact_mod_cast ZMod.val_lt (n := n + 1) a
    rw [glueMinimum_A n ht a]
    exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  | D n =>
    rcases Nat.even_or_odd n with hn | hn
    · rw [glueMinimum_D_of_even n ht hn a _ rfl]
      split_ifs <;> positivity
    · rw [glueMinimum_D_of_odd n ht hn a _ rfl]
      split_ifs <;> positivity
  | E6 =>
    rw [glueMinimum_E6 ht a]
    split_ifs <;> norm_num
  | E7 =>
    rw [glueMinimum_E7 ht a]
    split_ifs <;> norm_num
  | E8 => rw [glueMinimum_E8]
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Half the shortest norm of a label is its quadratic value**: `q(a) = μ_t(a) / 2 mod ℤ`.  In
particular a label is quadratically isotropic exactly when its shortest norm is an even
integer. -/
theorem quadratic_glueAlphabet_eq_glueMinimum_div_two (t : DynkinType) (hv : t.Valid)
    (ht : t.IsSimplyLaced) (a : t.glueAlphabet ht) :
    (t.glueAlphabet ht).quadratic a = ((t.glueMinimum ht a / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨x, hx, hxa⟩ := (t.isLeast_glueMinimum hv ht a).1
  rw [← (t.glueAlphabetIsometry hv ht).map_app a, ← hx, discriminantQuadraticModule_quadratic,
    discriminantQuadraticMap_mk, hxa]

/-- The zero label has shortest norm `0`. -/
@[simp]
theorem glueMinimum_zero (t : DynkinType) (ht : t.IsSimplyLaced) : t.glueMinimum ht 0 = 0 := by
  cases t with
  | A n => exact (glueMinimum_A n ht 0).trans (by simp)
  | D n =>
    rcases Nat.even_or_odd n with hn | hn
    · exact (glueMinimum_D_of_even n ht hn 0 0 (map_zero _)).trans (by simp)
    · exact (glueMinimum_D_of_odd n ht hn 0 0 (map_zero _)).trans (by simp)
  | E6 => exact (glueMinimum_E6 ht 0).trans (by simp)
  | E7 => exact (glueMinimum_E7 ht 0).trans (by simp)
  | E8 => rfl
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-- **Only the zero label has shortest norm zero**: the root lattice is positive definite, so the
only dual vector of norm zero is `0`, which lies in the zero coset. -/
@[simp]
theorem glueMinimum_eq_zero_iff (t : DynkinType) (hv : t.Valid) (ht : t.IsSimplyLaced)
    {a : t.glueAlphabet ht} : t.glueMinimum ht a = 0 ↔ a = 0 := by
  constructor
  · intro h
    obtain ⟨x, hx, hxa⟩ := (t.isLeast_glueMinimum hv ht a).1
    have hx0 : x = 0 := by
      by_contra hne
      have := ((t.rootLattice ht).isPosDef_iff.mp (t.isPosDef_rootLattice ht)) x
        (by simpa using Subtype.coe_ne_coe.mpr hne)
      linarith
    rw [hx0, Submodule.Quotient.mk_zero] at hx
    exact (map_eq_zero_iff _ (EquivLike.injective _)).mp hx.symm
  · rintro rfl
    exact t.glueMinimum_zero ht

/-! ## Glue words -/

section GlueWord

universe v

variable {ι : Type v} [Fintype ι] (t : ι → DynkinType) (hv : ∀ i, (t i).Valid)
  (ht : ∀ i, (t i).IsSimplyLaced)

/-- **The shortest norm of a glue word is the sum of the shortest norms of its labels.**  For a
finite family `t` of valid simply-laced components and a glue word `w`,
`μ(w) = ∑ i, μ_(t i)(w_i)` is the least norm of a dual vector of the orthogonal sum of the root
lattices in the coset `glueWordIsometry t ht hv w` named by `w`, and some dual vector of that coset
has this norm. -/
theorem isLeast_sum_glueMinimum (w : ∀ i, (t i).glueAlphabet (ht i)) :
    IsLeast {q : ℚ | ∃ x : (pi fun i ↦ (t i).rootLattice (ht i)).dualCarrier,
      Submodule.Quotient.mk x = glueWordIsometry t ht hv w ∧
        (pi fun i ↦ (t i).rootLattice (ht i)).form x x = q}
      (∑ i, (t i).glueMinimum (ht i) (w i)) := by
  have hw : glueWordIsometry t ht hv w = (discriminantGroupPiEquiv _).symm
      fun i ↦ (t i).glueAlphabetIsometry (hv i) (ht i) (w i) :=
    (LinearEquiv.eq_symm_apply _).mpr (funext (discriminantGroupPiEquiv_glueWordIsometry t ht hv w))
  rw [hw]
  exact isLeast_form_self_pi _ fun i ↦ (t i).isLeast_glueMinimum (hv i) (ht i) (w i)

include hv in
/-- **Half the shortest norm of a glue word is its quadratic value**:
`q(w) = μ(w) / 2 mod ℤ`.  In particular a glue word is quadratically isotropic exactly when the
sum of the shortest norms of its labels is an even integer. -/
theorem quadratic_pi_glueAlphabet_eq_sum_glueMinimum_div_two
    (w : ∀ i, (t i).glueAlphabet (ht i)) :
    (FiniteQuadraticModule.pi fun i ↦ (t i).glueAlphabet (ht i)).quadratic w =
      (((∑ i, (t i).glueMinimum (ht i) (w i)) / 2 : ℚ) : AddCircle (1 : ℚ)) := by
  obtain ⟨x, hx, hxw⟩ := (isLeast_sum_glueMinimum t hv ht w).1
  rw [← (glueWordIsometry t ht hv).map_app w, ← hx, discriminantQuadraticModule_quadratic,
    discriminantQuadraticMap_mk, hxw]

include hv in
/-- **Only the zero glue word has shortest norm zero.** -/
@[simp]
theorem sum_glueMinimum_eq_zero_iff {w : ∀ i, (t i).glueAlphabet (ht i)} :
    ∑ i, (t i).glueMinimum (ht i) (w i) = 0 ↔ w = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ (t i).glueMinimum_nonneg (ht i) (w i), funext_iff]
  simp only [Finset.mem_univ, true_imp_iff, glueMinimum_eq_zero_iff _ (hv _), Pi.zero_apply]

end GlueWord

end TauCeti.DynkinType
