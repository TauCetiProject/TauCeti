/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- The classification of the conjugacy classes of `GL₂` by trace and determinant is what every
-- normal form below is checked against.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- `TauCeti.diagGL` is the split semisimple normal form and occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- `TauCeti.jordanGL` is the non-semisimple normal form and occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarUnipotent
-- `TauCeti.GL2NonSplitTorusHom` is the elliptic normal form and occurs in the statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NonSplitTorus
-- Non-public: the trace and the norm of a quadratic irrationality, and the existence of one over a
-- finite field, are what pin the elliptic normal form; used in proofs only.
import TauCeti.FieldTheory.Quadratic
-- Non-public: `Matrix.GeneralLinearGroup.center_eq_range_scalar` turns a scalar element of `GL₂`
-- into the scalar matrix of a unit, in a proof only.
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# The four conjugacy normal forms of `GL₂` over a finite field

`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean` classifies the conjugacy
classes of `GL₂(F)` by trace and determinant, with the companion matrix of the characteristic
polynomial as the representative of each non-scalar class. That representative is uniform but
anonymous. This file replaces it, over a finite field, by the four **named** normal forms the
character theory of `GL₂(𝔽_q)` is written against:

* a **central** scalar matrix `a • 1`;
* a **split semisimple** `TauCeti.diagGL ![a, b]` with `a ≠ b`;
* a **non-semisimple** Jordan block `TauCeti.jordanGL a 1`;
* an **elliptic** `TauCeti.GL2NonSplitTorusHom F E hE x`, multiplication by an element of a
  degree-`2` extension `E/F` that does not lie in `F`.

`TauCeti.exists_isConj_normalForm` is the resulting statement that every element of `GL₂(F)` is
conjugate to one of the four. It is what turns the four character values computed at these normal
forms in `TauCeti/RepresentationTheory/CharacterTable/GL2/CharacterValues.lean` into a full row of
the character table of `GL₂(𝔽_q)`: a character is a class function, so a row is determined once the
normal forms exhaust the classes.

The two non-central split forms need no finiteness and no extension. Each is the same check
against `TauCeti.isConj_iff_of_notMem_range_scalar`: the normal form is not scalar, and its trace
and determinant are the prescribed ones. What the roots of `X² - t X + d` are is the only thing
that distinguishes them — two distinct roots give `diagGL`, a repeated root gives `jordanGL` —
and only in the repeated-root case need non-scalarness be assumed: a scalar matrix has a repeated
root, so prescribing two distinct roots, or a root outside `F`, already rules it out.

The elliptic case is the one that needs a quadratic extension, and it is where the finiteness of
`F` enters. Multiplication by `x : E` has trace `Tr_{E/F} x` and determinant `N_{E/F} x`
(`TauCeti.GL2NonSplitTorus.trace_gl2NonSplitTorusHom` and
`TauCeti.GL2NonSplitTorus.val_det_gl2NonSplitTorusHom`), so the normal form is pinned by the
quadratic-extension lemmas of `TauCeti/FieldTheory/Quadratic.lean`:
`TauCeti.Algebra.trace_eq_of_mul_self_eq` and `TauCeti.Algebra.norm_eq_of_mul_self_eq` identify
those with `t` and `d` for an `x` outside `F` satisfying `x² = t x - d`, and
`TauCeti.exists_mul_self_eq_of_finite` supplies such an `x` over a finite field.

Uniqueness — that the four families are pairwise disjoint and that the parameters are determined up
to the evident symmetries `(a, b) ↦ (b, a)` and `x ↦ x^q` — is the second half of the file, and it
runs on the same classification. Being scalar is a conjugacy invariant on its own
(`TauCeti.not_isConj_of_mem_range_scalar`), which separates the central family from the other
three; that is the one separation trace and determinant do not make, a scalar and a Jordan block
with the same eigenvalue having the same characteristic polynomial. Among the three non-central
families the characteristic polynomial does all the work, and what separates them is how it
factors: two distinct roots in `F` for `diagGL`, a repeated root for `jordanGL`, and no root in `F`
for the elliptic form. Reading that off is one equation per pair, and in the elliptic case it needs
the torus parameter `x` to satisfy the quadratic built from its own trace and norm,
`TauCeti.Algebra.mul_self_eq_trace_mul_sub_norm`: an eigenvalue of a split or a Jordan form
lies in `F`, and `x` does not.

None of those statements needs `F` finite, and the split and non-semisimple ones need no extension
at all. What does need finiteness is the symmetry `x ↦ x^q` of the elliptic parameter, which is
`TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff` in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`. Together with the results
here it says that the four families, with their parameters read up to the two symmetries, index the
conjugacy classes of `GL₂(𝔽_q)` without repetition — the description by named data of the indexing
that `TauCeti.conjClassesGLFinTwoEquiv` supplies anonymously.

## Main results

* `TauCeti.isConj_diagGL_of_trace_of_det`, `TauCeti.isConj_jordanGL_one_of_trace_of_det` and
  `TauCeti.isConj_gl2NonSplitTorusHom_of_trace_of_det`: **the three non-central normal forms**, each
  characterized by the roots of its characteristic polynomial, read off the trace and the
  determinant.
* `TauCeti.exists_isConj_normalForm`: **every element of `GL₂(F)`, for `F` finite with a degree-`2`
  extension `E`, is conjugate to one of the four normal forms.**
* `TauCeti.not_isConj_scalar_diagGL`, `TauCeti.not_isConj_scalar_jordanGL_one`,
  `TauCeti.not_isConj_scalar_gl2NonSplitTorusHom`, `TauCeti.not_isConj_diagGL_jordanGL_one`,
  `TauCeti.not_isConj_diagGL_gl2NonSplitTorusHom` and
  `TauCeti.not_isConj_jordanGL_one_gl2NonSplitTorusHom`: **the four families are pairwise
  disjoint.**
* `TauCeti.isConj_diagGL_iff` and `TauCeti.isConj_jordanGL_one_iff`: **the parameters inside a
  family are determined**, the split family up to the transposition of its two eigenvalues and the
  non-semisimple family outright. For the central family this is `TauCeti.isConj_scalar_iff`, which
  needs nothing about `GL₂` and lives with the other scalar invariants in
  `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ConjugacyClasses.lean`.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`* (2011), Chapter 1.
* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F]

/-! ### Shape adapters for the two split normal forms

The normal forms below are written against the pair `![a, b]` and the Jordan parameter `1`, while
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/Diagonal/Basic.lean` and
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/ScalarUnipotent.lean` state non-scalarity, the
trace and the determinant for a general family and a general off-diagonal entry. These six private
lemmas do that adaptation once, so that no proof below recomputes the trace, the determinant or the
non-scalarity of a normal form from its matrix entries. -/

/-- The split normal form attached to a repeated eigenvalue is the central one. This is
`TauCeti.diagGL_const` with the family spelled as the pair the normal forms are written against. It
is what lets the three split statements below whose conclusion survives a repeated eigenvalue carry
no hypothesis on their two parameters. -/
private theorem diagGL_pair_eq_scalar {a b : Fˣ} (hab : a = b) :
    diagGL ![a, b] = Matrix.GeneralLinearGroup.scalar (Fin 2) a := by
  have h : ![a, b] = fun _ : Fin 2 => a := by
    subst hab
    funext i
    fin_cases i <;> rfl
  rw [h, diagGL_const]

/-- `TauCeti.notMem_range_scalar_diagGL` for the pair the normal forms are written against. -/
private theorem notMem_range_scalar_diagGL_pair {a b : Fˣ} (hab : a ≠ b) :
    (diagGL ![a, b] : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) :=
  notMem_range_scalar_diagGL (t := ![a, b]) (by simpa using hab)

/-- `TauCeti.notMem_range_scalar_jordanGL` for the off-diagonal entry `1`. -/
private theorem notMem_range_scalar_jordanGL_one (a : Fˣ) :
    (jordanGL a (1 : F) : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) :=
  notMem_range_scalar_jordanGL (one_ne_zero (α := F))

/-- The trace of the split normal form, read off the general `TauCeti.trace_diagGL`. -/
private theorem trace_diagGL_pair (a b : Fˣ) :
    (diagGL ![a, b] : Matrix (Fin 2) (Fin 2) F).trace = (a : F) + b := by
  rw [trace_diagGL, Fin.sum_univ_two]
  simp

/-- The determinant of the split normal form, read off the unit-level `TauCeti.det_diagGL`. -/
private theorem det_diagGL_pair (a b : Fˣ) :
    (diagGL ![a, b] : Matrix (Fin 2) (Fin 2) F).det = (a : F) * b := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_diagGL, Fin.prod_univ_two]
  simp

/-- The determinant of the Jordan normal form, read off the unit-level `TauCeti.det_jordanGL`. -/
private theorem det_jordanGL_one (a : Fˣ) :
    (jordanGL a (1 : F) : Matrix (Fin 2) (Fin 2) F).det = (a : F) * a := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, det_jordanGL, Units.val_pow_eq_pow_val]
  ring

/-! ### The two split normal forms -/

/-- **The split semisimple normal form.** An element of `GL₂(F)` whose characteristic polynomial
has the two *distinct* roots `a` and `b` is conjugate to `diagGL ![a, b]`. Distinct roots already
force the element to be non-scalar. -/
theorem isConj_diagGL_of_trace_of_det {g : GL (Fin 2) F} {a b : Fˣ} (hab : a ≠ b)
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = (a : F) + b)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = (a : F) * b) :
    IsConj g (diagGL ![a, b]) := by
  -- Distinct roots force non-scalarness: a scalar `c` has trace `c + c` and determinant `c * c`,
  -- so `X² - (a + b) X + a b` would be `(X - c)²`, making `a` and `b` both equal to `c`.
  have hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
    rintro ⟨c, hc⟩
    rw [← hc, Matrix.scalar_apply, Matrix.trace_diagonal, Fin.sum_univ_two] at htrace
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    have hac : (a : F) = c :=
      sub_eq_zero.1 (mul_self_eq_zero.1 (by linear_combination -(a : F) * htrace + hdet))
    exact hab (Units.ext (by linear_combination htrace + 2 * hac))
  refine (isConj_iff_of_notMem_range_scalar hg (notMem_range_scalar_diagGL_pair hab)).2 ⟨?_, ?_⟩
  · rw [htrace, trace_diagGL_pair]
  · rw [hdet, det_diagGL_pair]

/-- **The non-semisimple normal form.** A non-scalar element of `GL₂(F)` whose characteristic
polynomial is `(X - a)²` is conjugate to the Jordan block `jordanGL a 1`. -/
theorem isConj_jordanGL_one_of_trace_of_det {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : Fˣ}
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = 2 * (a : F))
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = (a : F) * a) :
    IsConj g (jordanGL a (1 : F)) := by
  refine (isConj_iff_of_notMem_range_scalar hg (notMem_range_scalar_jordanGL_one a)).2 ⟨?_, ?_⟩
  · rw [htrace, trace_jordanGL]
  · rw [hdet, det_jordanGL_one]

/-! ### The elliptic normal form -/

section Elliptic

variable {E : Type*} [Field E] [Algebra F E]

/-- **The elliptic normal form.** An element of `GL₂(F)` whose characteristic polynomial
`X² - t X + d` is satisfied by an element `x` of a degree-`2` extension `E/F` lying outside `F` is
conjugate to the element `x` of the non-split torus. A root outside `F` already forces the element
to be non-scalar. -/
theorem isConj_gl2NonSplitTorusHom_of_trace_of_det (hE : Module.finrank F E = 2)
    {g : GL (Fin 2) F} {x : Eˣ} (hx : (x : E) ∉ Set.range (algebraMap F E)) {t d : F}
    (hx2 : (x : E) * x = algebraMap F E t * x - algebraMap F E d)
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = t)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = d) :
    IsConj g (GL2NonSplitTorusHom F E hE x) := by
  -- A root outside `F` forces non-scalarness: were `g` the scalar `c`, then `t = c + c` and
  -- `d = c * c`, so `x` would be the double root `algebraMap F E c`.
  have hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2)) := by
    rintro ⟨c, hc⟩
    rw [← hc, Matrix.scalar_apply, Matrix.trace_diagonal, Fin.sum_univ_two] at htrace
    rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
    subst htrace
    subst hdet
    rw [map_add, map_mul] at hx2
    exact hx ⟨c, (sub_eq_zero.1 (mul_self_eq_zero.1 (by linear_combination hx2))).symm⟩
  refine (isConj_iff_of_notMem_range_scalar hg
    (GL2NonSplitTorus.notMem_range_scalar_gl2NonSplitTorusHom hE hx)).2 ⟨?_, ?_⟩
  · rw [htrace, GL2NonSplitTorus.trace_gl2NonSplitTorusHom,
      Algebra.trace_eq_of_mul_self_eq hE hx hx2]
  · rw [hdet, ← Matrix.GeneralLinearGroup.val_det_apply,
      GL2NonSplitTorus.val_det_gl2NonSplitTorusHom, Algebra.norm_eq_of_mul_self_eq hE hx hx2]

end Elliptic

/-! ### The classification -/

/-- **Every element of `GL₂(F)` is conjugate to one of the four normal forms**, for `F` a finite
field with a supplied degree-`2` extension `E`: a central scalar, a split semisimple
`diagGL ![a, b]` with `a ≠ b`, a non-semisimple Jordan block `jordanGL a 1`, or an elliptic
element `GL2NonSplitTorusHom F E hE x` with `x` outside `F`.

This is what turns a computation of a character at these four normal forms into a full row of the
character table of `GL₂(𝔽_q)`. -/
theorem exists_isConj_normalForm [Finite F] (E : Type*) [Field E] [Algebra F E]
    (hE : Module.finrank F E = 2) (g : GL (Fin 2) F) :
    (∃ a : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) a = g) ∨
      (∃ a b : Fˣ, a ≠ b ∧ IsConj g (diagGL ![a, b])) ∨
      (∃ a : Fˣ, IsConj g (jordanGL a (1 : F))) ∨
      (∃ x : Eˣ, (x : E) ∉ Set.range (algebraMap F E) ∧
        IsConj g (GL2NonSplitTorusHom F E hE x)) := by
  classical
  by_cases hg : (g : Matrix (Fin 2) (Fin 2) F) ∈ Set.range (Matrix.scalar (Fin 2))
  · refine Or.inl (MonoidHom.mem_range.1 ?_)
    rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.2 hg
  set t := (g : Matrix (Fin 2) (Fin 2) F).trace with ht
  set d := (g : Matrix (Fin 2) (Fin 2) F).det with hd
  have hd0 : d ≠ 0 := by
    rw [hd, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det g).ne_zero
  by_cases hsplit : ∃ a : F, a * a = t * a - d
  · obtain ⟨a, ha⟩ := hsplit
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hd0 (by linear_combination ha)
    have hb : a * (t - a) = d := by linear_combination -ha
    have hb0 : t - a ≠ 0 := fun h => hd0 (by rw [← hb, h, mul_zero])
    by_cases hab : a = t - a
    · refine Or.inr (Or.inr (Or.inl ⟨Units.mk0 a ha0, ?_⟩))
      refine isConj_jordanGL_one_of_trace_of_det hg ?_ ?_
      · simp only [Units.val_mk0]
        linear_combination -hab
      · simp only [Units.val_mk0]
        linear_combination -hb - a * hab
    · refine Or.inr (Or.inl ⟨Units.mk0 a ha0, Units.mk0 (t - a) hb0, ?_, ?_⟩)
      · simpa [Units.ext_iff] using hab
      · refine isConj_diagGL_of_trace_of_det (by simpa [Units.ext_iff] using hab) ?_ ?_
        · simp only [Units.val_mk0]
          ring
        · simp only [Units.val_mk0]
          linear_combination -hb
  · push Not at hsplit
    obtain ⟨x, hx2⟩ := exists_mul_self_eq_of_finite E hE hsplit
    have hxF : x ∉ Set.range (algebraMap F E) := by
      rintro ⟨a, rfl⟩
      refine hsplit a ?_
      have : algebraMap F E (a * a) = algebraMap F E (t * a - d) := by
        simpa using hx2
      exact (algebraMap F E).injective this
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hxF ⟨0, by simp⟩
    -- The elliptic parameter is the unit `Units.mk0 x hx0`, so both hypotheses on `x` have to be
    -- read back through the coercion `Eˣ → E`, which is `Units.val_mk0`.
    refine Or.inr (Or.inr (Or.inr ⟨Units.mk0 x hx0, ?_, ?_⟩))
    · simpa only [Units.val_mk0] using hxF
    · refine isConj_gl2NonSplitTorusHom_of_trace_of_det hE ?_ ?_ ht.symm hd.symm
      · simpa only [Units.val_mk0] using hxF
      · simpa only [Units.val_mk0] using hx2

/-! ### Uniqueness of the normal form

The four families are pairwise non-conjugate, and inside each family the parameters are determined
up to the evident symmetry.  Only the order shown is proved; the reverse order follows from
`IsConj.symm`. -/

/-- **A scalar is not conjugate to a split semisimple normal form.** The hypothesis `b ≠ c` is
needed: `diagGL ![b, b]` is the scalar `b`. -/
theorem not_isConj_scalar_diagGL (a : Fˣ) {b c : Fˣ} (hbc : b ≠ c) :
    ¬ IsConj (Matrix.GeneralLinearGroup.scalar (Fin 2) a) (diagGL ![b, c]) :=
  not_isConj_of_mem_range_scalar ⟨(a : F), rfl⟩ (notMem_range_scalar_diagGL_pair hbc)

/-- **A scalar is not conjugate to a Jordan block.** The two have the same characteristic
polynomial `(X - a)²` when their eigenvalues agree, so this is exactly where trace and determinant
fail to separate the conjugacy classes of `GL₂(F)`. -/
theorem not_isConj_scalar_jordanGL_one (a b : Fˣ) :
    ¬ IsConj (Matrix.GeneralLinearGroup.scalar (Fin 2) a) (jordanGL b (1 : F)) :=
  not_isConj_of_mem_range_scalar ⟨(a : F), rfl⟩ (notMem_range_scalar_jordanGL_one b)

/-- **A split semisimple normal form is not conjugate to a Jordan block.** For distinct `a` and `b`
equal traces and determinants would force `(a - b)² = 0`; for `a = b` the left-hand side is a
scalar, which is not conjugate to a Jordan block either. -/
theorem not_isConj_diagGL_jordanGL_one (a b c : Fˣ) :
    ¬ IsConj (diagGL ![a, b]) (jordanGL c (1 : F)) := by
  by_cases hab : a = b
  · rw [diagGL_pair_eq_scalar hab]
    exact not_isConj_scalar_jordanGL_one a c
  intro h
  obtain ⟨htrace, hdet⟩ := (isConj_iff_of_notMem_range_scalar
    (notMem_range_scalar_diagGL_pair hab) (notMem_range_scalar_jordanGL_one c)).1 h
  rw [trace_diagGL_pair, trace_jordanGL] at htrace
  rw [det_diagGL_pair, det_jordanGL_one] at hdet
  refine hab (Units.ext (sub_eq_zero.1 (sq_eq_zero_iff.1 ?_)))
  linear_combination ((a : F) + (b : F) + 2 * (c : F)) * htrace - 4 * hdet

/-- **Two split semisimple normal forms are conjugate exactly when their eigenvalue pairs agree up
to order.** The transposition `(a, b) ↦ (b, a)` is the Weyl group of the split torus acting on the
torus by permuting the diagonal entries, and it is the only identification among these normal forms.
No distinctness is asked of either pair: when a pair repeats, its normal form is the corresponding
scalar, and the statement specializes to `TauCeti.isConj_scalar_iff`. -/
theorem isConj_diagGL_iff (a b c d : Fˣ) :
    IsConj (diagGL ![a, b]) (diagGL ![c, d]) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  by_cases hab : a = b
  · by_cases hcd : c = d
    · rw [diagGL_pair_eq_scalar hab, diagGL_pair_eq_scalar hcd, isConj_scalar_iff]
      subst hab
      subst hcd
      simp
    · rw [diagGL_pair_eq_scalar hab]
      subst hab
      exact iff_of_false (not_isConj_scalar_diagGL a hcd)
        (by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hcd rfl)
  · by_cases hcd : c = d
    · rw [diagGL_pair_eq_scalar hcd]
      subst hcd
      exact iff_of_false (fun h => not_isConj_scalar_diagGL c hab h.symm)
        (by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hab rfl)
    · rw [isConj_iff_of_notMem_range_scalar (notMem_range_scalar_diagGL_pair hab)
        (notMem_range_scalar_diagGL_pair hcd)]
      simp only [trace_diagGL_pair, det_diagGL_pair]
      refine ⟨fun ⟨htrace, hdet⟩ => ?_, ?_⟩
      · have key : ((c : F) - (a : F)) * ((c : F) - (b : F)) = 0 := by
          linear_combination (-(c : F)) * htrace + hdet
        rcases mul_eq_zero.1 key with hc | hc
        · exact Or.inl ⟨Units.ext (sub_eq_zero.1 hc).symm,
            Units.ext (by linear_combination htrace + hc)⟩
        · exact Or.inr ⟨Units.ext (by linear_combination htrace + hc),
            Units.ext (sub_eq_zero.1 hc).symm⟩
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact ⟨rfl, rfl⟩
        · exact ⟨add_comm _ _, mul_comm _ _⟩

/-- **Two Jordan blocks are conjugate exactly when their eigenvalues agree**: the non-semisimple
family carries no symmetry at all. -/
theorem isConj_jordanGL_one_iff (a b : Fˣ) :
    IsConj (jordanGL a (1 : F)) (jordanGL b (1 : F)) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ IsConj.refl _⟩
  obtain ⟨htrace, hdet⟩ := (isConj_iff_of_notMem_range_scalar
    (notMem_range_scalar_jordanGL_one a) (notMem_range_scalar_jordanGL_one b)).1 h
  rw [trace_jordanGL, trace_jordanGL] at htrace
  rw [det_jordanGL_one, det_jordanGL_one] at hdet
  exact Units.ext (sub_eq_zero.1 (sq_eq_zero_iff.1 (by
    linear_combination hdet - (b : F) * htrace)))

section EllipticUniqueness

variable {E : Type*} [Field E] [Algebra F E]

/-- **A scalar is not conjugate to an elliptic normal form.** -/
theorem not_isConj_scalar_gl2NonSplitTorusHom (hE : Module.finrank F E = 2) (a : Fˣ) {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    ¬ IsConj (Matrix.GeneralLinearGroup.scalar (Fin 2) a) (GL2NonSplitTorusHom F E hE x) :=
  not_isConj_of_mem_range_scalar ⟨(a : F), rfl⟩
    (GL2NonSplitTorus.notMem_range_scalar_gl2NonSplitTorusHom hE hx)

/-- **A split semisimple normal form is not conjugate to an elliptic one.** Equal traces and
determinants make `x` a root of `(X - a) (X - b)`, so `x` would be `a` or `b`, and both lie in
`F`. -/
theorem not_isConj_diagGL_gl2NonSplitTorusHom (hE : Module.finrank F E = 2) (a b : Fˣ) {x : Eˣ}
    (hx : (x : E) ∉ Set.range (algebraMap F E)) :
    ¬ IsConj (diagGL ![a, b]) (GL2NonSplitTorusHom F E hE x) := by
  by_cases hab : a = b
  · rw [diagGL_pair_eq_scalar hab]
    exact not_isConj_scalar_gl2NonSplitTorusHom hE a hx
  intro h
  obtain ⟨htrace, hdet⟩ := (isConj_iff_of_notMem_range_scalar
    (notMem_range_scalar_diagGL_pair hab)
    (GL2NonSplitTorus.notMem_range_scalar_gl2NonSplitTorusHom hE hx)).1 h
  rw [trace_diagGL_pair, GL2NonSplitTorus.trace_gl2NonSplitTorusHom] at htrace
  rw [det_diagGL_pair, ← Matrix.GeneralLinearGroup.val_det_apply,
    GL2NonSplitTorus.val_det_gl2NonSplitTorusHom] at hdet
  have hx2 := Algebra.mul_self_eq_trace_mul_sub_norm hE (x : E)
  rw [← htrace, ← hdet, map_add, map_mul] at hx2
  have key : ((x : E) - algebraMap F E (a : F)) * ((x : E) - algebraMap F E (b : F)) = 0 := by
    linear_combination hx2
  rcases mul_eq_zero.1 key with hroot | hroot
  · exact hx ⟨(a : F), (sub_eq_zero.1 hroot).symm⟩
  · exact hx ⟨(b : F), (sub_eq_zero.1 hroot).symm⟩

/-- **A Jordan block is not conjugate to an elliptic normal form.** Equal traces and determinants
make `x` a double root of `(X - a)²`, so `x` would be `a`, which lies in `F`. No hypothesis is
needed on `x`: a torus parameter inside `F` gives the corresponding scalar, which is not conjugate
to a Jordan block either. -/
theorem not_isConj_jordanGL_one_gl2NonSplitTorusHom (hE : Module.finrank F E = 2) (a : Fˣ)
    (x : Eˣ) :
    ¬ IsConj (jordanGL a (1 : F)) (GL2NonSplitTorusHom F E hE x) := by
  by_cases hx : (x : E) ∈ Set.range (algebraMap F E)
  · obtain ⟨c, hc⟩ := hx
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact x.ne_zero (by simpa using hc.symm)
    have hxc : x = Units.map (algebraMap F E : F →* E) (Units.mk0 c hc0) :=
      Units.ext (by simpa using hc.symm)
    rw [hxc, GL2NonSplitTorus.gl2NonSplitTorusHom_map_algebraMap]
    exact fun h => not_isConj_scalar_jordanGL_one _ a h.symm
  intro h
  obtain ⟨htrace, hdet⟩ := (isConj_iff_of_notMem_range_scalar
    (notMem_range_scalar_jordanGL_one a)
    (GL2NonSplitTorus.notMem_range_scalar_gl2NonSplitTorusHom hE hx)).1 h
  rw [trace_jordanGL, two_mul, GL2NonSplitTorus.trace_gl2NonSplitTorusHom] at htrace
  rw [det_jordanGL_one, ← Matrix.GeneralLinearGroup.val_det_apply,
    GL2NonSplitTorus.val_det_gl2NonSplitTorusHom] at hdet
  have hx2 := Algebra.mul_self_eq_trace_mul_sub_norm hE (x : E)
  rw [← htrace, ← hdet, map_add, map_mul] at hx2
  refine hx ⟨(a : F), (sub_eq_zero.1 (mul_self_eq_zero.1 ?_)).symm⟩
  linear_combination hx2

end EllipticUniqueness

end TauCeti
