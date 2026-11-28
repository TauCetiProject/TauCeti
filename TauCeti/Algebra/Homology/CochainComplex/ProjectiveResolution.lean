/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import TauCeti.Algebra.Homology.CochainComplex.Opposite

/-!
# Projective resolutions of bounded above cochain complexes

In an abelian category with enough projectives, every cochain complex `K` which is strictly
bounded above, say `K.IsStrictlyLE n`, receives a quasi-isomorphism from a cochain complex of
projective objects which is again strictly bounded above by `n`
(`CochainComplex.exists_quasiIso_projective`). By Mathlib's
`CochainComplex.isKProjective_of_projective` such a complex is K-projective. Over a ringed site,
resolving the underlying complex of presheaves of modules in this way and sheafifying gives flat
resolutions of bounded above complexes of sheaves of modules.

The statement is dual to Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective` for bounded below complexes
in an abelian category with enough injectives, and it is deduced from it through the equivalence
`CochainComplex.opEquivalence C` between `(CochainComplex C ℤ)ᵒᵖ` and `CochainComplex Cᵒᵖ ℤ`,
which reverses the grading and preserves and reflects quasi-isomorphisms
(`CochainComplex.quasiIso_opEquivalence_map_iff`).

## References

* The Stacks Project, Derived Categories, Section 13.19, Projective resolutions.
* D. Quillen, *Homotopical algebra*, Lecture Notes in Mathematics 43, Springer, 1967, Chapter I,
  Section 1, Example B.
-/

public section

open CategoryTheory Limits Opposite

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- In an abelian category with enough projectives, a cochain complex which is strictly bounded
above by `n` receives a quasi-isomorphism from a cochain complex of projective objects which is
also strictly bounded above by `n`. -/
theorem exists_quasiIso_projective [EnoughProjectives C] (K : CochainComplex C ℤ) (n : ℤ)
    [K.IsStrictlyLE n] :
    ∃ (P : CochainComplex C ℤ) (π : P ⟶ K) (_ : QuasiIso π)
      (_ : ∀ i, Projective (P.X i)), P.IsStrictlyLE n := by
  -- Resolve the bounded below complex corresponding to `K` in the opposite category by
  -- injectives, and read the resolution back in `C`.
  let e := opEquivalence C
  have : (e.functor.obj (op K)).IsStrictlyGE (-n) := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact (K.isZero_of_isStrictlyLE n (-i) (by lia)).op
  obtain ⟨L, ι, _, hL, _⟩ :=
    Plus.modelCategoryQuillen.exists_quasiIso_injective (e.functor.obj (op K)) (-n)
  let P : CochainComplex C ℤ := (e.inverse.obj L).unop
  let φ : e.functor.obj (op P) ≅ L := e.counitIso.app L
  obtain ⟨π, hπ⟩ := e.functor.map_surjective (ι ≫ φ.inv)
  -- The term of `e.functor.obj (op P)` in degree `-i` is `op (P.X (-(-i)))`.
  have hX (i : ℤ) : op (P.X i) ≅ L.X (-i) :=
    (P.XIsoOfEq (neg_neg i)).op ≪≫ (HomologicalComplex.eval _ _ (-i)).mapIso φ
  refine ⟨P, π.unop, ?_, fun i ↦ ?_, ?_⟩
  · rw [← quasiIso_opEquivalence_map_iff, Quiver.Hom.op_unop, hπ]
    infer_instance
  · have : Injective (op (P.X i)) := Injective.of_iso (hX i).symm (hL _)
    infer_instance
  · rw [isStrictlyLE_iff]
    intro i hi
    exact ((L.isZero_of_isStrictlyGE (-n) (-i) (by lia)).of_iso (hX i)).unop

end CochainComplex
