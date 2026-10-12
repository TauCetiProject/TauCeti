/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `ConjClasses`, `GL`, `Matrix.trace`, `Matrix.det` and `Matrix.scalar` occur in the statements
-- below, and `TauCeti.conjClassesGLFinTwoEquiv` indexes the classes counted in the last one.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: the three non-central normal forms and the sizes of their classes are used only in
-- proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.NormalForm
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
-- Non-public: an element of a quadratic extension with a prescribed minimal polynomial, and the
-- quadratic extension of a finite field it lives in, are used only in the elliptic proof.
import TauCeti.FieldTheory.Quadratic
import Mathlib.FieldTheory.Finite.Extension
-- Non-public: the identification of a three-element field with `ZMod 3` is used only in the proof
-- of the class equation.
import Mathlib.Data.ZMod.Basic

/-!
# Sizes of the conjugacy classes of `GL₂(𝔽_q)`

The four named normal forms of `GL₂(F)` over a finite field `F` with `q` elements have classes of
sizes `1` (central), `q (q + 1)` (split semisimple), `q² - 1` (non-semisimple) and `q (q - 1)`
(elliptic): these are `TauCeti.ncard_carrier_mk_scalar`, `TauCeti.ncard_carrier_mk_diagGL`,
`TauCeti.ncard_carrier_mk_jordanGL` and
`TauCeti.GL2NonSplitTorus.ncard_carrier_mk_gl2NonSplitTorusHom`. This file reads the size of the
class of an *arbitrary* non-central element off its characteristic polynomial `X² - t X + d`,
where `t` is the trace and `d` the determinant:

* two distinct roots `a ≠ b` in `F` give a class of `q (q + 1)` elements
  (`TauCeti.ncard_carrier_mk_of_trace_eq_add_of_det_eq_mul`);
* a repeated root, for a non-scalar element, gives `q² - 1` elements
  (`TauCeti.ncard_carrier_mk_of_trace_eq_two_mul_of_det_eq_mul_self`);
* no root in `F` gives `q (q - 1)` elements (`TauCeti.ncard_carrier_mk_of_forall_mul_self_ne`).

Each is the class size of the normal form the element is conjugate to, by the normal-form theorems
of `TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/NormalForm.lean`. Only the elliptic case needs
a quadratic extension `E/F`, to supply the element of the non-split torus; since the class size
does not depend on it, the statement makes no mention of `E`.

These sizes are what is needed to write down the columns of the character table of `GL₂(𝔽_q)` for
a given `q`. The last section does this for the uniform worked case `q = 3`: `GL₂(𝔽₃)` has
`48` elements in eight conjugacy classes, two central classes of size `1`, three elliptic classes of
size `6`, two non-semisimple classes of size `8` and one split semisimple class of size `12`
(`TauCeti.map_ncard_carrier_conjClasses_GL2_of_card_eq_three`). The eight irreducible characters
these classes are paired with, of degrees `1, 1, 2, 2, 2, 3, 3, 4`, are counted in
`TauCeti/RepresentationTheory/CharacterTable/GL2/DegreeCounts.lean`.

## Main results

* `TauCeti.ncard_carrier_mk_of_trace_eq_add_of_det_eq_mul`,
  `TauCeti.ncard_carrier_mk_of_trace_eq_two_mul_of_det_eq_mul_self` and
  `TauCeti.ncard_carrier_mk_of_forall_mul_self_ne`: the size of the conjugacy class of a
  non-central element of `GL₂(𝔽_q)`, according to how its characteristic polynomial factors.
* `TauCeti.map_ncard_carrier_conjClasses_GL2_of_card_eq_three`: the class sizes of `GL₂(𝔽₃)` are
  `1, 1, 6, 6, 6, 8, 8, 12`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
-/

public section

open Matrix

namespace TauCeti

variable {F : Type*} [Field F] [Fintype F]

/-- **The class of a split regular semisimple element of `GL₂(𝔽_q)` has `q (q + 1)` elements**:
an element whose characteristic polynomial has two distinct roots `a ≠ b` in `F` is conjugate to
`diagGL ![a, b]`. -/
theorem ncard_carrier_mk_of_trace_eq_add_of_det_eq_mul {g : GL (Fin 2) F} {a b : F}
    (hab : a ≠ b) (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = a + b)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = a * b) :
    (ConjClasses.mk g).carrier.ncard = Fintype.card F * (Fintype.card F + 1) := by
  -- The roots are nonzero because their product is the determinant of an invertible matrix.
  obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 (hdet ▸ g.det_ne_zero)
  have hab' : Units.mk0 a ha ≠ Units.mk0 b hb := fun h => hab (congrArg Units.val h)
  rw [ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_diagGL_of_trace_of_det hab' htrace hdet)]
  exact ncard_carrier_mk_diagGL (by simpa using hab')

/-- **The class of a non-semisimple element of `GL₂(𝔽_q)` has `q² - 1` elements**: a non-scalar
element whose characteristic polynomial is `(X - a)²` is conjugate to the Jordan block
`jordanGL a 1`. -/
theorem ncard_carrier_mk_of_trace_eq_two_mul_of_det_eq_mul_self {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : F}
    (htrace : (g : Matrix (Fin 2) (Fin 2) F).trace = 2 * a)
    (hdet : (g : Matrix (Fin 2) (Fin 2) F).det = a * a) :
    (ConjClasses.mk g).carrier.ncard = Fintype.card F ^ 2 - 1 := by
  -- The root is nonzero because its square is the determinant of an invertible matrix.
  have ha : a ≠ 0 := (mul_ne_zero_iff.1 (hdet ▸ g.det_ne_zero)).1
  rw [ConjClasses.mk_eq_mk_iff_isConj.2
    (isConj_jordanGL_one_of_trace_of_det hg (a := Units.mk0 a ha) htrace hdet)]
  exact ncard_carrier_mk_jordanGL one_ne_zero

/-- **The class of an elliptic element of `GL₂(𝔽_q)` has `q (q - 1)` elements**: an element whose
characteristic polynomial `X² - t X + d` has no root in `F` is conjugate to an element of the
non-split torus, multiplication by a root of that polynomial in the quadratic extension of `F`. -/
theorem ncard_carrier_mk_of_forall_mul_self_ne {g : GL (Fin 2) F}
    (hroot : ∀ a : F, a * a ≠ (g : Matrix (Fin 2) (Fin 2) F).trace * a -
      (g : Matrix (Fin 2) (Fin 2) F).det) :
    (ConjClasses.mk g).carrier.ncard = Fintype.card F * (Fintype.card F - 1) := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  let E := FiniteField.Extension F (ringChar F) 2
  have : Algebra.IsQuadraticExtension F E := ⟨FiniteField.finrank_extension F (ringChar F) 2⟩
  obtain ⟨x, hx2⟩ := exists_mul_self_eq_of_finite E hroot
  have hxF : x ∉ Set.range (algebraMap F E) := by
    rintro ⟨a, rfl⟩
    exact hroot a ((algebraMap F E).injective (by simpa using hx2))
  have hx0 : x ≠ 0 := fun h => hxF ⟨0, by simp [h]⟩
  rw [ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_gl2NonSplitTorusHom_of_trace_of_det
    (x := Units.mk0 x hx0) hxF hx2 rfl rfl)]
  exact GL2NonSplitTorus.ncard_carrier_mk_gl2NonSplitTorusHom hxF

/-! ### The class equation of `GL₂(𝔽₃)`

Over the field with three elements the classes are indexed, through
`TauCeti.conjClassesGLFinTwoEquiv`, by the two central units and the six pairs `(t, d)` of a trace
and a unit determinant. Reading the field as `ZMod 3`, the six polynomials `X² - t X + d` are
`X² + 1`, `X² - X - 1` and `X² + X - 1`, which have no root; `(X + 1)²` and `(X - 1)²`, which have a
repeated one; and `X² - 1 = (X - 1) (X + 1)`, which splits. -/

/-- **The class equation of `GL₂(𝔽₃)`**: the eight conjugacy classes of `GL₂(F)`, for a field `F`
with three elements, have sizes `1, 1, 6, 6, 6, 8, 8, 12`. The two classes of size `1` are the
central ones, the three of size `q (q - 1) = 6` the elliptic ones, the two of size `q² - 1 = 8` the
non-semisimple ones, and the one of size `q (q + 1) = 12` the split semisimple one; together they
exhaust the `48` elements of `GL₂(𝔽₃)`. -/
theorem map_ncard_carrier_conjClasses_GL2_of_card_eq_three (hF : Fintype.card F = 3)
    [Fintype (ConjClasses (GL (Fin 2) F))] :
    (Finset.univ : Finset (ConjClasses (GL (Fin 2) F))).val.map (fun C => C.carrier.ncard) =
      {1, 1, 6, 6, 6, 8, 8, 12} := by
  -- Transport the indexing `Fˣ ⊕ F × Fˣ` of the classes to `ZMod 3`, where it can be enumerated.
  let e : ZMod 3 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_three hF
  let u : (ZMod 3)ˣ ≃* Fˣ := Units.mapEquiv e.toMulEquiv
  have hu (d : (ZMod 3)ˣ) : ((u d : Fˣ) : F) = e d := (rfl)
  let φ := (Equiv.sumCongr u.toEquiv (e.toEquiv.prodCongr u.toEquiv)).trans
    (conjClassesGLFinTwoEquiv (F := F))
  have hscalar (a : (ZMod 3)ˣ) : (φ (.inl a)).carrier.ncard = 1 := by
    simp [φ]
  have hcomp (t : ZMod 3) (d : (ZMod 3)ˣ) :
      φ (.inr (t, d)) = ConjClasses.mk (companionGL (e t) (u d)) := by
    simp [φ]
  -- The size of a non-central class, according to how `X² - t X + d` factors over `ZMod 3`.
  have hell (t : ZMod 3) (d : (ZMod 3)ˣ) (h : ∀ b : ZMod 3, b * b ≠ t * b - d) :
      (φ (.inr (t, d))).carrier.ncard = 6 := by
    rw [hcomp, ncard_carrier_mk_of_forall_mul_self_ne, hF]
    intro a
    obtain ⟨b, rfl⟩ := e.surjective a
    rw [coe_companionGL, trace_companionFinTwo, det_companionFinTwo, hu, ← map_mul, ← map_mul,
      ← map_sub]
    exact e.injective.ne (h b)
  have hjordan (t : ZMod 3) (d : (ZMod 3)ˣ) (a : ZMod 3) (ht : t = 2 * a)
      (hd : (d : ZMod 3) = a * a) : (φ (.inr (t, d))).carrier.ncard = 8 := by
    rw [hcomp, ncard_carrier_mk_of_trace_eq_two_mul_of_det_eq_mul_self
      (companionGL_notMem_range_scalar _ _) (a := e a), hF]
    · rfl
    · rw [coe_companionGL, trace_companionFinTwo, ht, map_mul, map_ofNat]
    · rw [coe_companionGL, det_companionFinTwo, hu, hd, map_mul]
  have hsplit (t : ZMod 3) (d : (ZMod 3)ˣ) (a b : ZMod 3) (hab : a ≠ b) (ht : t = a + b)
      (hd : (d : ZMod 3) = a * b) : (φ (.inr (t, d))).carrier.ncard = 12 := by
    rw [hcomp, ncard_carrier_mk_of_trace_eq_add_of_det_eq_mul (a := e a) (b := e b)
      (e.injective.ne hab), hF]
    · rw [coe_companionGL, trace_companionFinTwo, ht, map_add]
    · rw [coe_companionGL, det_companionFinTwo, hu, hd, map_mul]
  have huniv : (Finset.univ : Finset ((ZMod 3)ˣ ⊕ ZMod 3 × (ZMod 3)ˣ)).val =
      {.inl 1, .inl (-1), .inr (0, 1), .inr (0, -1), .inr (1, 1), .inr (1, -1), .inr (2, 1),
        .inr (2, -1)} := by
    decide
  rw [← Multiset.map_univ_val_equiv φ, Multiset.map_map, huniv]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Function.comp_apply, hscalar]
  rw [hell 0 1 (by decide), hsplit 0 (-1) 1 (-1) (by decide) (by decide) (by decide),
    hjordan 1 1 (-1) (by decide) (by decide), hell 1 (-1) (by decide),
    hjordan 2 1 1 (by decide) (by decide), hell 2 (-1) (by decide)]
  decide

end TauCeti
