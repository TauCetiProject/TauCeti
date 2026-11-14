/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Iwasawa
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Generation

/-!
# The Iwasawa structure of the special unitary group on its isotropic points

Let `σ` be a nontrivial involution of a field `K`, let `Q` be an invertible `ε`-Hermitian matrix
over `K`, and assume that the `ε`-trace `t ↦ t + ε σ(t)` is onto `{s | σ(s) = ε s}` with a nonzero
kernel element and the norm `b ↦ b σ(b)` is onto `K^σ`. To each isotropic point
`p : Matrix.isotropicPoints Q σ` of projective space, `Matrix.unitaryTransvectionSubgroup Q σ p`
attaches the abelian subgroup of unitary transvections along `p`, which is conjugated to
`T(g • p)` by `g` (`Matrix.unitaryTransvectionSubgroup_smul`). When either `K^σ` has at least three
elements or `4 ≤ Fintype.card n`, these subgroups generate `Matrix.specialIsometryGroup Q σ`
(`Matrix.iSup_unitaryTransvectionSubgroup_eq_top`).

This file packages these properties into `Matrix.specialIsometryIwasawaStructure`, an instance of
Mathlib's `MulAction.IwasawaStructure` for the action of `Q.specialIsometryGroup σ` on
`Q.isotropicPoints σ`.

## Main definitions

* `Matrix.specialIsometryIwasawaStructure`: the `MulAction.IwasawaStructure` of
  `Q.specialIsometryGroup σ` on `Q.isotropicPoints σ` given by `Matrix.unitaryTransvectionSubgroup`.
* `Matrix.specialIsometryIwasawaStructure_T`: its subgroup at `p` is
  `Q.unitaryTransvectionSubgroup σ p`.

## References

* K. Iwasawa, *Über die Einfachheit der speziellen projektiven Gruppen*, Proc. Imp. Acad. Tokyo
  **17** (1941), 57--59.
* D. E. Taylor, *The Geometry of the Classical Groups* (1992), Chapters 10 and 11.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K] {Q : Matrix n n K} {σ : K →+* K}
  {ε : K}

/-- **The Iwasawa structure of the special unitary group on its isotropic points**: the groups of
unitary transvections along isotropic points are abelian, permuted by conjugation compatibly with
the action, and generate `Q.specialIsometryGroup σ` when `K^σ` has at least three elements or
`4 ≤ Fintype.card n`. -/
def specialIsometryIwasawaStructure (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n) :
    MulAction.IwasawaStructure (Q.specialIsometryGroup σ) (Q.isotropicPoints σ) where
  T := Q.unitaryTransvectionSubgroup σ
  is_comm _ := inferInstance
  is_conj := unitaryTransvectionSubgroup_smul
  is_generator := iSup_unitaryTransvectionSubgroup_eq_top hσ hQ hdet htr hadm hnorm hσ_ne hgen

/-- The subgroups of `Matrix.specialIsometryIwasawaStructure` are the unitary transvection groups
of isotropic points. -/
@[simp]
theorem specialIsometryIwasawaStructure_T (hσ : Function.Involutive σ)
    (hQ : (Q.map σ)ᵀ = ε • Q) (hdet : Q.det ≠ 0)
    (htr : ∀ s, σ s = ε * s → ∃ t, t + ε * σ t = s)
    (hadm : ∃ d ≠ 0, d + ε * σ d = 0)
    (hnorm : ∀ t, σ t = t → ∃ b, b * σ b = t)
    (hσ_ne : ∃ a : K, σ a ≠ a)
    (hgen : (∃ t : K, t ≠ 0 ∧ t ≠ 1 ∧ σ t = t) ∨ 4 ≤ Fintype.card n)
    (p : Q.isotropicPoints σ) :
    (specialIsometryIwasawaStructure hσ hQ hdet htr hadm hnorm hσ_ne hgen).T p =
      Q.unitaryTransvectionSubgroup σ p :=
  (rfl)

end Matrix
