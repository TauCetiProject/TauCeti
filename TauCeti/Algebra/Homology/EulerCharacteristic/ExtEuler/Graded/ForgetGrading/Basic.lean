/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Sesquilinear

/-!
# The q-Euler form at `q = 1` against the ungraded Ext-Euler characteristic

Let `C` be a `k`-linear abelian category with a grading-shift autoequivalence `e`, and let `D` be
a `k`-linear abelian category thought of as `C` with its grading forgotten along a functor `U`.
Setting `q = 1` collapses the internal degrees of

```text
χ_q(X, Y) = ∑ n, (-1)ⁿ ∑ j, q⁻ʲ dim_k Ext^n(X, Y{j})
```

into the single alternating sum `∑ n, (-1)ⁿ ∑ j, dim_k Ext^n(X, Y{j})`.  That is the ordinary
Ext-Euler characteristic of the ungraded pair only when the ungraded `Ext` groups assemble the
graded ones, so the identification is not a formal consequence of having a shift: it needs the
comparison isomorphisms

```text
⨁ j, Ext^n(X, Y{j}) ≅ Ext^n(X', Y')
```

as an extra hypothesis, recorded here as `TauCeti.IsGradedExtComparison`.  A pair `(X', Y')` of
objects of `D` is the intended value `(U X, U Y)` of such a functor, but nothing below uses `U`
itself, so the predicate is stated for two objects of `D` directly.  Only the isomorphisms
themselves are asked for: comparing the two Ext long exact sequences would need them to be
compatible with the connecting maps as well, which the numerical identity below does not use.

Under that hypothesis the ungraded pair inherits both halves of Euler-admissibility from the
graded one, and `TauCeti.IsGradedExtComparison.laurentEval_one_gradedExtEuler` identifies the
specialization of the q-Euler characteristic at `q = 1` with the ordinary Ext-Euler
characteristic.  The same identity for the packaged sesquilinear form is
`TauCeti.IsGradedExtComparison.gradedExtEulerSpecialized_one_mk_of_mk_of`.

## Main definitions

* `TauCeti.IsGradedExtComparison`: the bigraded `Ext` groups of a pair in `C` assemble, degree by
  cohomological degree, into the ungraded `Ext` groups of a pair in `D`.

## Main results

* `TauCeti.isGradedExtComparison_of_subsingleton_ne`: a grading concentrated in a single internal
  degree admits the shifted pair `(X, Y{d})` as a comparison inside the same category.
* `TauCeti.IsGradedExtComparison.isEulerAdmissible`: a graded Euler-admissible pair has an
  Euler-admissible comparison pair.
* `TauCeti.IsGradedExtComparison.laurentEval_one_gradedExtEuler`: `χ_q(X, Y)` evaluated at
  `q = 1` is `χ(X', Y')`.
* `TauCeti.IsGradedExtComparison.gradedExtEulerSpecialized_one_mk_of_mk_of`: the same identity
  for the q-Euler form specialized at `q = 1`.

## References

* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", *Journal of
  Combinatorial Theory, Series A* 185 (2022), Sections 1.2 and 2.2, for graded Grothendieck
  groups, the q-Euler form and its specializations.
-/

public section

open scoped DirectSum

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w w' v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (k : Type t) [Field k] [Linear k C] [Linear k D] [HasExt.{w} C] [HasExt.{w'} D] (e : C ≌ C)

/-- The bigraded `Ext` groups of `(X, Y)` **assemble into the ungraded `Ext` groups** of a pair
`(X', Y')`: in every cohomological degree the direct sum over the internal degrees of
`Ext^n(X, Y{j})` is `Ext^n(X', Y')`.

This is the hypothesis under which a q-Euler form specializes at `q = 1` to an ordinary Ext-Euler
characteristic.  A functor forgetting the grading supplies the intended pairs `(U X, U Y)`; the
existence of such a functor, or even of a shift-compatible one, does not by itself supply these
isomorphisms. -/
structure IsGradedExtComparison (X Y : C) (X' Y' : D) : Prop where
  /-- In each cohomological degree the internal degrees add up to the ungraded `Ext` group. -/
  nonempty_linearEquiv (n : ℕ) :
    Nonempty ((⨁ j : ℤ, GradedExt.{w} e X Y n j) ≃ₗ[k] Ext.{w'} X' Y' n)

/-- **A grading concentrated in a single internal degree admits a shifted comparison pair.**  If
the bigraded `Ext` groups of `(X, Y)` vanish in every internal degree other than `d`, then the
surviving degree is the whole direct sum, so `(X, Y{d})` is a comparison pair for `(X, Y)` inside
the same category. -/
theorem isGradedExtComparison_of_subsingleton_ne {X Y : C} (d : ℤ)
    (hd : ∀ (n : ℕ) (j : ℤ), j ≠ d → Subsingleton (GradedExt.{w} e X Y n j)) :
    IsGradedExtComparison.{w, w} k e X Y X ((e ^ d).functor.obj Y) :=
  ⟨fun n => ⟨DirectSum.componentLinearEquiv (GradedExt.{w} e X Y n) d (hd n)⟩⟩

namespace IsGradedExtComparison

variable {k e} {X Y : C} {X' Y' : D}

/-- `Ext`-finiteness of the ungraded pair follows from finiteness of the internal grading: a
direct sum of finitely many finite-dimensional spaces is finite-dimensional. -/
theorem isExtFinite (hc : IsGradedExtComparison.{w, w'} k e X Y X' Y')
    (h : IsGradedExtInternallyFinite.{w} k e X Y) : IsExtFinite.{w'} k X' Y' := by
  refine ⟨fun n => ?_⟩
  obtain ⟨φ⟩ := hc.nonempty_linearEquiv n
  have := (h.finiteLaurentSupport n).finiteDimensional_directSum
  exact Module.Finite.equiv φ

/-- A uniform cohomological vanishing bound for the bigraded `Ext` groups bounds the ungraded
ones. -/
theorem isExtBoundedBy (hc : IsGradedExtComparison.{w, w'} k e X Y X' Y') {N : ℕ}
    (h : IsGradedExtBoundedBy.{w} e X Y N) : IsExtBoundedBy.{w'} X' Y' N := by
  refine ⟨fun n hn => ?_⟩
  obtain ⟨φ⟩ := hc.nonempty_linearEquiv n
  have hj : ∀ j, Subsingleton (GradedExt.{w} e X Y n j) := fun j => h.subsingleton hn j
  have : Subsingleton (⨁ j : ℤ, GradedExt.{w} e X Y n j) := inferInstance
  exact φ.toEquiv.symm.subsingleton

/-- **Euler-admissibility descends to the comparison pair.**  Both halves transfer separately:
finite internal support gives `Ext`-finiteness and the uniform cohomological bound gives eventual
vanishing. -/
theorem isEulerAdmissible (hc : IsGradedExtComparison.{w, w'} k e X Y X' Y')
    (h : IsGradedEulerAdmissible.{w} k e X Y) : IsEulerAdmissible.{w'} k X' Y' :=
  ⟨hc.isExtFinite h.internallyFinite,
    ⟨h.bounded.exists_bound.choose, hc.isExtBoundedBy h.bounded.exists_bound.choose_spec⟩⟩

/-- Every truncation of the q-Euler sum evaluates at `q = 1` to the corresponding truncation of
the ungraded alternating sum. -/
theorem laurentEval_one_truncatedGradedExtEuler
    (hc : IsGradedExtComparison.{w, w'} k e X Y X' Y')
    (h : IsGradedExtInternallyFinite.{w} k e X Y) (N : ℕ) :
    laurentEval (1 : ℤˣ) (truncatedGradedExtEuler k e h N) =
      truncatedExtEuler.{w'} k X' Y' N := by
  induction N with
  | zero => simp
  | succ N ih =>
    obtain ⟨φ⟩ := hc.nonempty_linearEquiv N
    rw [truncatedGradedExtEuler_succ, truncatedExtEuler_succ, map_add, ih, map_zsmul,
      gradedExtDimension_eq_targetShiftGradedDimension,
      laurentEval_one_targetShiftGradedDimension, φ.finrank_eq, zsmul_eq_mul]
    norm_cast

/-- **The q-Euler characteristic at `q = 1` is the ordinary Ext-Euler characteristic** of the
comparison pair.  The comparison isomorphisms are what make this true: a grading shift alone
identifies no graded sum of `Ext` groups with an ungraded one. -/
theorem laurentEval_one_gradedExtEuler (hc : IsGradedExtComparison.{w, w'} k e X Y X' Y')
    (h : IsGradedEulerAdmissible.{w} k e X Y) :
    laurentEval (1 : ℤˣ) (gradedExtEuler k e h) = extEuler.{w'} k (hc.isEulerAdmissible h) := by
  obtain ⟨N, hN⟩ := h.bounded.exists_bound
  rw [gradedExtEuler_eq k e h hN, extEuler_eq k _ (hc.isExtBoundedBy hN),
    hc.laurentEval_one_truncatedGradedExtEuler h.internallyFinite]

end IsGradedExtComparison

/-! ### The specialized q-Euler form -/

variable [e.functor.Additive] [e.functor.Linear k]

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

/-- **The q-Euler form specialized at `q = 1`, evaluated on two object classes, is the ordinary
Ext-Euler characteristic** of any comparison pair for those two objects. -/
theorem IsGradedExtComparison.gradedExtEulerSpecialized_one_mk_of_mk_of
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    (X : P.FullSubcategory) (Y : Q.FullSubcategory) {X' Y' : D}
    (hc : IsGradedExtComparison.{w, w'} k e X.obj Y.obj X' Y') :
    gradedExtEulerSpecialized hP hQ hPshift hQshift h 1
        (LaurentSpecialization.mk 1 (LaurentK0.of _ X))
        (LaurentSpecialization.mk 1 (LaurentK0.of _ Y)) =
      extEuler.{w'} k
        (hc.isEulerAdmissible (h.isGradedEulerAdmissible X.property Y.property)) := by
  rw [gradedExtEulerSpecialized_mk_of_mk_of, hc.laurentEval_one_gradedExtEuler]

end TauCeti
