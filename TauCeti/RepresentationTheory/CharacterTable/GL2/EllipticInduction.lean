/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.indClassFun` is the object computed here.
public import TauCeti.RepresentationTheory.Induction.ClassFunction
-- `TauCeti.GL2NonSplitTorus`, `TauCeti.diagGL` and `TauCeti.jordanGL` occur in the statements
-- below, and the centralizer of an elliptic element is what pins the two contributing cosets.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Centralizer
-- Non-public: the conjugacy classification of the non-scalar elements of `GL₂` is used only
-- inside the proofs.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: the `q`-power map on a quadratic extension of a finite field, whose fixed points
-- are the base field, is used only inside the proofs.
import TauCeti.FieldTheory.Finite.FrobeniusFixed
-- Non-public: the explicit trace and norm of a finite field extension, in the proofs only.
import Mathlib.FieldTheory.Finite.Trace
-- Non-public: `TauCeti.smul_quotientGroup_mk_eq_self_iff` is used only inside a proof.
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# The class function of `GL₂(𝔽_q)` induced from the non-split torus

Let `E/F` be a quadratic extension of a finite field with `q` elements and let
`T = TauCeti.GL2NonSplitTorus F E hE` be the resulting elliptic torus of `GL₂(F)`, a copy of `Eˣ`.
This file computes the induced class function `TauCeti.indClassFun T f` on the four families of
conjugacy classes of `GL₂(F)`: at a central scalar `a` it is `[GL₂(F) : T] = q (q - 1)` copies of
`f(a)`, it vanishes on the split semisimple and the non-semisimple families, and at an elliptic
element coming from `u : Eˣ` outside `F` it is `f(u) + f(u^q)`.

Applied to a character `θ` of `Eˣ` this is the character of `Ind_{Eˣ}^{GL₂(F)} θ`, one of the two
induced characters whose difference is the cuspidal (discrete series) character attached to a
character of `Eˣ` in general position; the other is induced from the product of the centre with the
unipotent radical. The vanishing on the two families that meet the Borel subgroup is the reason
that difference has degree `q - 1` rather than `q (q - 1)`.

## The geometry behind the four values

Everything follows from which conjugates of an element land in `T`, and `T` is small: away from the
scalars its elements have no eigenvalue in `F`
(`TauCeti.GL2NonSplitTorus.det_sub_algebraMap_ne_zero`).

* A **scalar** matrix is central, so every conjugate of it lies in `T`, and the sum has one equal
  summand for each of the `[GL₂(F) : T]` cosets.
* A **split semisimple** or **non-semisimple** element is non-scalar with an eigenvalue in `F`, and
  both properties are conjugation invariant, so no conjugate of it meets `T` at all.
* An **elliptic** element `u : Eˣ` outside `F` meets `T` in exactly the two points `u` and `u^q`:
  a conjugate of it inside `T` has the same trace and norm as `u`, and the only elements of `E`
  with those invariants are the two roots `u, u^q` of `X² - Tr(u) X + N(u)`
  (`TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff`). The centralizer of an elliptic
  element being `T` itself, those two points contribute one coset each.

## Main results

* `TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff`: the elements of the elliptic torus
  conjugate to a given elliptic `u` are exactly `u` and `u^q`.
* `TauCeti.GL2NonSplitTorus.conj_notMem_of_det_sub_algebraMap_eq_zero` and
  `TauCeti.GL2NonSplitTorus.indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero`: a non-scalar
  element with an eigenvalue in `F` has no conjugate in the torus, so the induced class function
  vanishes on it.
* `TauCeti.GL2NonSplitTorus.indClassFun_scalar`,
  `TauCeti.GL2NonSplitTorus.indClassFun_diagGL`,
  `TauCeti.GL2NonSplitTorus.indClassFun_jordanGL` and
  `TauCeti.GL2NonSplitTorus.indClassFun_gl2NonSplitTorusHom`: **the four values**, on the central,
  split semisimple, non-semisimple and elliptic normal forms.

That the four normal forms exhaust the conjugacy classes is
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses`; as in
`TauCeti/RepresentationTheory/CharacterTable/GL2/CharacterValues.lean`, the values below are
stated at the normal forms themselves rather than assembled into a single case distinction. None
of the four is a `simp` lemma: they evaluate a class function at a normal form, and neither side
is a normal form for `simp`.

## References

* C. Bonnafé, *Representations of `SL₂(𝔽_q)`*, Springer (2011), Chapter 6.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §5.
-/

public section

open Matrix

namespace TauCeti

namespace GL2NonSplitTorus

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {k : Type*} [Semiring k] (hE : Module.finrank F E = 2)

/-! ### Elements with an eigenvalue in the base field -/

/-- **A non-scalar element with an eigenvalue in `F` has no conjugate in the non-split torus.**
An element of the torus is either scalar or has no eigenvalue in `F`
(`TauCeti.GL2NonSplitTorus.det_sub_algebraMap_ne_zero`), and both conditions are invariant under
conjugation. This is what makes the induced class function vanish on the split semisimple and the
non-semisimple classes. -/
theorem conj_notMem_of_det_sub_algebraMap_eq_zero {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : F}
    (ha : ((g : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det = 0) (x : GL (Fin 2) F) :
    x⁻¹ * g * x ∉ GL2NonSplitTorus F E hE := by
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  intro hmem
  obtain ⟨v, hv⟩ := (mem_iff hE).mp hmem
  -- the conjugated matrix is multiplication by `v`
  have hmat : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Algebra.leftMulMatrix (nonSplitTorusBasis F E hE) (v : E) := by
    rw [← coe_gl2NonSplitTorusHom hE, hv]
  -- conjugation does not change the determinant of `g - a`
  have hdet : (((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det = 0 := by
    have hxx : ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (x : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hcancel : ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        algebraMap F (Matrix (Fin 2) (Fin 2) F) a * (x : Matrix (Fin 2) (Fin 2) F) =
        algebraMap F (Matrix (Fin 2) (Fin 2) F) a := by
      rw [mul_assoc, Algebra.commutes a (x : Matrix (Fin 2) (Fin 2) F), ← mul_assoc, hxx, one_mul]
    have hsplit : ((x⁻¹ * g * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) -
        algebraMap F (Matrix (Fin 2) (Fin 2) F) a =
        ((x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((g : Matrix (Fin 2) (Fin 2) F) -
            algebraMap F (Matrix (Fin 2) (Fin 2) F) a) * (x : Matrix (Fin 2) (Fin 2) F) := by
      rw [mul_sub, sub_mul, hcancel, Units.val_mul, Units.val_mul]
    rw [hsplit, Matrix.det_mul, Matrix.det_mul, ha, mul_zero, zero_mul]
  -- so the norm of `v - a` vanishes, forcing `v` into `F`
  have hnorm : Algebra.norm F ((v : E) - algebraMap F E a) = 0 := by
    rw [Algebra.norm_eq_matrix_det (nonSplitTorusBasis F E hE), map_sub,
      (Algebra.leftMulMatrix (nonSplitTorusBasis F E hE)).commutes, ← hmat, hdet]
  have hvF : (v : E) = algebraMap F E a := sub_eq_zero.mp (Algebra.norm_eq_zero_iff.mp hnorm)
  -- the conjugate is then a central scalar matrix, so `g` is scalar
  have ha0 : a ≠ 0 := fun h => v.ne_zero (by rw [hvF, h, map_zero])
  have hvu : v = Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) := by
    ext
    simpa using hvF
  have hscal : x⁻¹ * g * x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha0) := by
    rw [← hv, hvu, gl2NonSplitTorusHom_map_algebraMap]
  have hgeq : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha0) := by
    have hgx : g = x * (x⁻¹ * g * x) * x⁻¹ := by group
    rw [hgx, hscal, ← Matrix.GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel,
      mul_one]
  exact hg ⟨a, by rw [hgeq, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]⟩

variable [Finite F]

/-- **The induced class function vanishes on a non-scalar element with an eigenvalue in `F`**: no
coset contributes, by `TauCeti.GL2NonSplitTorus.conj_notMem_of_det_sub_algebraMap_eq_zero`. -/
theorem indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero (f : GL2NonSplitTorus F E hE → k)
    {g : GL (Fin 2) F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F) ∉ Set.range (Matrix.scalar (Fin 2))) {a : F}
    (ha : ((g : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) a).det = 0) :
    indClassFun (GL2NonSplitTorus F E hE) f g = 0 := by
  classical
  rw [indClassFun_apply]
  exact Finset.sum_eq_zero fun t _ =>
    dite_eq_right (conj_notMem_of_det_sub_algebraMap_eq_zero hE hg ha _)

/-! ### The four values -/

/-- **The induced class function at a central element**: every conjugate of a scalar matrix is
itself and lies in the torus, so each of the `[GL₂(F) : T]` cosets contributes the same value.
Over a field with `q` elements the index is `q (q - 1)` by
`TauCeti.GL2NonSplitTorus.index_eq`. -/
theorem indClassFun_scalar (f : GL2NonSplitTorus F E hE → k) (a : Fˣ) :
    indClassFun (GL2NonSplitTorus F E hE) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      (GL2NonSplitTorus F E hE).index •
        f ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) a, scalar_mem hE a⟩ := by
  classical
  have hconj : ∀ x : GL (Fin 2) F,
      x⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) a * x =
        Matrix.GeneralLinearGroup.scalar (Fin 2) a := fun x => by
    rw [mul_assoc, Matrix.GeneralLinearGroup.scalar_commute a x, ← mul_assoc, inv_mul_cancel,
      one_mul]
  let _ : Fintype (GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) := Fintype.ofFinite _
  rw [indClassFun_apply, Subgroup.index_eq_card, Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact Finset.sum_eq_card_nsmul fun t _ => by rw [hconj, dite_eq_left (scalar_mem hE a)]

/-- **The induced class function vanishes on the split semisimple classes**: an invertible
diagonal matrix with distinct entries is non-scalar and has its entries as eigenvalues in `F`. -/
theorem indClassFun_diagGL (f : GL2NonSplitTorus F E hE → k) {t : Fin 2 → Fˣ} (ht : t 0 ≠ t 1) :
    indClassFun (GL2NonSplitTorus F E hE) f (diagGL t) = 0 := by
  refine indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero hE f
    (notMem_range_scalar_diagGL ht) (a := (t 0 : F)) ?_
  have hsub : ((diagGL t : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (t 0 : F)) =
      !![0, 0; 0, (t 1 : F) - (t 0 : F)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.algebraMap_matrix_apply, diagGL_coe]
  rw [hsub, Matrix.det_fin_two_of, mul_zero, zero_mul, sub_zero]

/-- **The induced class function vanishes on the non-semisimple classes**: a Jordan block with
`b ≠ 0` is non-scalar and has its repeated diagonal entry as an eigenvalue in `F`. -/
theorem indClassFun_jordanGL (f : GL2NonSplitTorus F E hE → k) (a : Fˣ) {b : F} (hb : b ≠ 0) :
    indClassFun (GL2NonSplitTorus F E hE) f (jordanGL a b) = 0 := by
  refine indClassFun_eq_zero_of_det_sub_algebraMap_eq_zero hE f
    (notMem_range_scalar_jordanGL hb) (a := (a : F)) ?_
  have hsub : ((jordanGL a b : Matrix (Fin 2) (Fin 2) F) -
      algebraMap F (Matrix (Fin 2) (Fin 2) F) (a : F)) = !![0, b; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_jordanGL, Matrix.algebraMap_matrix_apply]
  rw [hsub, Matrix.det_fin_two_of, mul_zero, mul_zero, sub_zero]

/-! ### The elliptic classes -/

section Elliptic

variable {u v : Eˣ}

/-- **The elements of the elliptic torus conjugate to a given elliptic element.** For `u : Eˣ`
outside `F`, the matrix of `v : Eˣ` is conjugate to that of `u` exactly when `v` is `u` or its
Frobenius conjugate `u^q`.

Conjugate matrices have the same trace and determinant, which on the torus are the trace and the
norm of the field element; and `u`, `u^q` are the two roots of `X² - Tr(u) X + N(u)`, so an element
with those invariants is one of them. -/
theorem isConj_gl2NonSplitTorusHom_iff (hu : (u : E) ∉ Set.range (algebraMap F E)) :
    IsConj (GL2NonSplitTorusHom F E hE u) (GL2NonSplitTorusHom F E hE v) ↔
      v = u ∨ v = u ^ Nat.card F := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  have : Finite E := Module.finite_of_finite F
  have hupow : ((u ^ Nat.card F : Eˣ) : E) ∉ Set.range (algebraMap F E) := by
    rw [Units.val_pow_eq_pow_val]
    exact FiniteField.pow_natCard_notMem_range_algebraMap hE hu
  -- the trace and the norm of a quadratic extension of a finite field, written out
  have htr : ∀ w : E, algebraMap F E (Algebra.trace F E w) = w + w ^ Nat.card F := by
    intro w
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hE]
    simp [Finset.sum_range_succ]
  have hnm : ∀ w : E, algebraMap F E (Algebra.norm F w) = w * w ^ Nat.card F := by
    intro w
    rw [FiniteField.algebraMap_norm_eq_prod_pow, hE]
    simp [Finset.prod_range_succ]
  constructor
  · intro hconj
    have htrace : Algebra.trace F E (v : E) = Algebra.trace F E (u : E) := by
      rw [← trace_gl2NonSplitTorusHom hE, ← trace_gl2NonSplitTorusHom hE,
        trace_val_eq_of_isConj hconj]
    have hnorm : Algebra.norm F (v : E) = Algebra.norm F (u : E) := by
      rw [← val_det_gl2NonSplitTorusHom hE, ← val_det_gl2NonSplitTorusHom hE]
      exact congrArg Units.val
        (isConj_iff_eq.1 (Matrix.GeneralLinearGroup.det.map_isConj hconj)).symm
    have h1 : (v : E) + (v : E) ^ Nat.card F = (u : E) + (u : E) ^ Nat.card F := by
      rw [← htr, ← htr, htrace]
    have h2 : (v : E) * (v : E) ^ Nat.card F = (u : E) * (u : E) ^ Nat.card F := by
      rw [← hnm, ← hnm, hnorm]
    have key : ((v : E) - (u : E)) * ((v : E) - (u : E) ^ Nat.card F) = 0 := by
      linear_combination (v : E) * h1 - h2
    rcases mul_eq_zero.mp key with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.mp h))
    · exact Or.inr (Units.ext (by rw [Units.val_pow_eq_pow_val]; exact sub_eq_zero.mp h))
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · refine (isConj_iff_of_notMem_range_scalar
        (notMem_range_scalar_gl2NonSplitTorusHom hE hu)
        (notMem_range_scalar_gl2NonSplitTorusHom hE hupow)).mpr ⟨?_, ?_⟩
      · rw [trace_gl2NonSplitTorusHom, trace_gl2NonSplitTorusHom]
        refine FaithfulSMul.algebraMap_injective F E ?_
        rw [htr, htr, Units.val_pow_eq_pow_val, FiniteField.pow_natCard_pow_natCard hE, add_comm]
      · rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply,
          val_det_gl2NonSplitTorusHom, val_det_gl2NonSplitTorusHom]
        refine FaithfulSMul.algebraMap_injective F E ?_
        rw [hnm, hnm, Units.val_pow_eq_pow_val, FiniteField.pow_natCard_pow_natCard hE, mul_comm]

/-- **The induced class function at an elliptic element.** For `u : Eˣ` outside `F` exactly two
cosets contribute, the trivial one and the one that conjugates `u` to `u^q`, so the value is
`f(u) + f(u^q)`.

The two cosets are pinned by two facts: the elements of the torus conjugate to `u` are `u` and
`u^q` (`TauCeti.GL2NonSplitTorus.isConj_gl2NonSplitTorusHom_iff`), and the centralizer of an
elliptic element is the whole torus
(`TauCeti.GL2NonSplitTorus.centralizer_gl2NonSplitTorusHom`), so each of the two accounts for a
single coset. -/
theorem indClassFun_gl2NonSplitTorusHom (f : GL2NonSplitTorus F E hE → k)
    (hu : (u : E) ∉ Set.range (algebraMap F E)) :
    indClassFun (GL2NonSplitTorus F E hE) f (GL2NonSplitTorusHom F E hE u) =
      f (unitsEquiv hE u) + f (unitsEquiv hE (u ^ Nat.card F)) := by
  classical
  have hupow : ((u ^ Nat.card F : Eˣ) : E) ∉ Set.range (algebraMap F E) := by
    rw [Units.val_pow_eq_pow_val]
    exact FiniteField.pow_natCard_notMem_range_algebraMap hE hu
  have hune : (u ^ Nat.card F : Eˣ) ≠ u := fun h =>
    FiniteField.pow_natCard_ne hu (by rw [← Units.val_pow_eq_pow_val, h])
  have hgmem : GL2NonSplitTorusHom F E hE u ∈ GL2NonSplitTorus F E hE :=
    (mem_iff hE).mpr ⟨u, rfl⟩
  have hgmem' : GL2NonSplitTorusHom F E hE (u ^ Nat.card F) ∈ GL2NonSplitTorus F E hE :=
    (mem_iff hE).mpr ⟨_, rfl⟩
  -- membership in the torus is commuting with an elliptic element
  have hmemT : ∀ y : GL (Fin 2) F, y ∈ GL2NonSplitTorus F E hE ↔
      GL2NonSplitTorusHom F E hE u * y = y * GL2NonSplitTorusHom F E hE u := by
    intro y
    rw [← centralizer_gl2NonSplitTorusHom hE hu, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h _ rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩
  have hmemT' : ∀ y : GL (Fin 2) F, y ∈ GL2NonSplitTorus F E hE ↔
      GL2NonSplitTorusHom F E hE (u ^ Nat.card F) * y =
        y * GL2NonSplitTorusHom F E hE (u ^ Nat.card F) := by
    intro y
    rw [← centralizer_gl2NonSplitTorusHom hE hupow, Subgroup.mem_centralizer_iff]
    exact ⟨fun h => h _ rfl, fun h z hz => by rw [Set.mem_singleton_iff.mp hz]; exact h⟩
  -- an element conjugating `u` to `u^q`
  obtain ⟨c, hc⟩ := isConj_iff.mp
    ((isConj_gl2NonSplitTorusHom_iff hE (v := u ^ Nat.card F) hu).mpr (Or.inr rfl))
  set d : GL (Fin 2) F := c⁻¹ with hd
  have hdg : d⁻¹ * GL2NonSplitTorusHom F E hE u * d =
      GL2NonSplitTorusHom F E hE (u ^ Nat.card F) := by
    rw [hd, inv_inv]; exact hc
  -- `d` normalizes the torus, since it moves one elliptic element to another
  have hdnorm : ∀ y ∈ GL2NonSplitTorus F E hE, d⁻¹ * y * d ∈ GL2NonSplitTorus F E hE := by
    intro y hy
    have hcomm := (hmemT y).mp hy
    refine (hmemT' _).mpr ?_
    rw [← hdg]
    calc d⁻¹ * GL2NonSplitTorusHom F E hE u * d * (d⁻¹ * y * d)
        = d⁻¹ * (GL2NonSplitTorusHom F E hE u * y) * d := by group
      _ = d⁻¹ * (y * GL2NonSplitTorusHom F E hE u) * d := by rw [hcomm]
      _ = d⁻¹ * y * d * (d⁻¹ * GL2NonSplitTorusHom F E hE u * d) := by group
  have hdT : d ∉ GL2NonSplitTorus F E hE := by
    intro hmem
    refine hune (gl2NonSplitTorusHom_injective hE ?_)
    rw [← hdg]
    have hcomm := (hmemT d).mp hmem
    calc d⁻¹ * GL2NonSplitTorusHom F E hE u * d
        = d⁻¹ * (GL2NonSplitTorusHom F E hE u * d) := by group
      _ = d⁻¹ * (d * GL2NonSplitTorusHom F E hE u) := by rw [hcomm]
      _ = GL2NonSplitTorusHom F E hE u := by group
  -- only the coset of `1` and the coset of `d` are fixed
  have hfix : ∀ x : GL (Fin 2) F,
      x⁻¹ * GL2NonSplitTorusHom F E hE u * x ∈ GL2NonSplitTorus F E hE →
      (x : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) = ((1 : GL (Fin 2) F) : _) ∨
        (x : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) = (d : _) := by
    intro x hx
    obtain ⟨w, hw⟩ := (mem_iff hE).mp hx
    have hconj : IsConj (GL2NonSplitTorusHom F E hE u) (GL2NonSplitTorusHom F E hE w) :=
      isConj_iff.mpr ⟨x⁻¹, by rw [inv_inv]; exact hw.symm⟩
    rcases (isConj_gl2NonSplitTorusHom_iff hE hu).mp hconj with h | h
    · refine Or.inl ?_
      rw [QuotientGroup.eq, mul_one]
      refine Subgroup.inv_mem _ ((hmemT x).mpr ?_)
      have hxg : x⁻¹ * GL2NonSplitTorusHom F E hE u * x = GL2NonSplitTorusHom F E hE u := by
        rw [← hw, h]
      calc GL2NonSplitTorusHom F E hE u * x
          = x * (x⁻¹ * GL2NonSplitTorusHom F E hE u * x) := by group
        _ = x * GL2NonSplitTorusHom F E hE u := by rw [hxg]
    · refine Or.inr ?_
      rw [QuotientGroup.eq]
      have hxd : x⁻¹ * GL2NonSplitTorusHom F E hE u * x =
          d⁻¹ * GL2NonSplitTorusHom F E hE u * d := by rw [hdg, ← hw, h]
      have hmem : d * x⁻¹ ∈ GL2NonSplitTorus F E hE := by
        refine (hmemT _).mpr ?_
        calc GL2NonSplitTorusHom F E hE u * (d * x⁻¹)
            = d * (d⁻¹ * GL2NonSplitTorusHom F E hE u * d) * d⁻¹ * (d * x⁻¹) := by group
          _ = d * (x⁻¹ * GL2NonSplitTorusHom F E hE u * x) * d⁻¹ * (d * x⁻¹) := by rw [hxd]
          _ = d * x⁻¹ * GL2NonSplitTorusHom F E hE u := by group
      have hconjmem := hdnorm _ hmem
      have hrw : d⁻¹ * (d * x⁻¹) * d = x⁻¹ * d := by group
      rwa [hrw] at hconjmem
  have hne : ((1 : GL (Fin 2) F) : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) ≠
      (d : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE) := by
    intro h
    rw [QuotientGroup.eq, inv_one, one_mul] at h
    exact hdT h
  -- the torus is abelian, so every function on it is a class function
  have hcomm : ∀ y z : (GL2NonSplitTorus F E hE), z * y * z⁻¹ = y := by
    intro y z
    obtain ⟨p, hp⟩ := (mem_iff hE).mp y.2
    obtain ⟨r, hr⟩ := (mem_iff hE).mp z.2
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hp, ← hr, ← map_inv, ← map_mul,
      ← map_mul, mul_comm r p, mul_assoc, mul_inv_cancel, mul_one]
  have hcf : f ∈ ClassFunction k (GL2NonSplitTorus F E hE) :=
    ClassFunction.mem_iff.mpr fun y z => by rw [hcomm y z]
  rw [indClassFun_eq_sum_of_smul_eq_self_mem f _
    ({((1 : GL (Fin 2) F) : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE),
      (d : GL (Fin 2) F ⧸ GL2NonSplitTorus F E hE)} : Finset _) ?_, Finset.sum_pair hne]
  · congr 1
    · rw [indTerm_eq_of_mk_eq hcf _ _ (1 : GL (Fin 2) F) (QuotientGroup.out_eq' _), indTerm_one,
        dite_eq_left hgmem]
      exact congrArg f (Subtype.ext (coe_unitsEquiv_apply hE u).symm)
    · rw [indTerm_eq_of_mk_eq hcf _ _ d (QuotientGroup.out_eq' _), indTerm_apply, hdg,
        dite_eq_left hgmem']
      exact congrArg f (Subtype.ext (coe_unitsEquiv_apply hE _).symm)
  · intro t ht
    rw [← QuotientGroup.out_eq' t] at ht ⊢
    rcases hfix _ ((smul_quotientGroup_mk_eq_self_iff _ _ _).mp ht) with h | h <;> simp [h]

end Elliptic

end GL2NonSplitTorus

end TauCeti
