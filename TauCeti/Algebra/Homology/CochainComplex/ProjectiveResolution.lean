/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Factorizations.CM5a

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
which reverses the grading. For this we record that a morphism of cochain complexes is a
quasi-isomorphism exactly when its image under this equivalence is one
(`CochainComplex.quasiIso_opEquivalence_functor_map_iff`), degree `n` corresponding to degree
`-n`.

## References

* The Stacks Project, Derived Categories, Section 13.19, Projective resolutions.
* D. Quillen, *Homotopical algebra*, Lecture Notes in Mathematics 43, Springer, 1967, Chapter I,
  Section 1, Example B.
-/

public section

open CategoryTheory Limits Opposite

namespace CochainComplex

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism of cochain complexes is a quasi-isomorphism in degree `-n` exactly when its image
under `opEquivalence C`, in the opposite category, is a quasi-isomorphism in degree `n`. -/
@[simp]
lemma quasiIsoAt_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ) :
    QuasiIsoAt ((opEquivalence C).functor.map f.op) n ↔ QuasiIsoAt f (-n) := by
  rw [← HomologicalComplex.quasiIsoAt_opFunctor_map_iff f (-n),
    quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp),
    quasiIsoAt_iff' _ (-(n - 1)) (-n) (-(n + 1))
      (ComplexShape.prev_eq' _ (by simp; lia)) (ComplexShape.next_eq' _ (by simp))]
  -- `opEquivalence C` restricts the opposite complex along `n ↦ -n`, so its short complex in
  -- degree `n` is, by definition, that of the opposite complex in degree `-n`.
  rfl

/-- A morphism of cochain complexes is a quasi-isomorphism exactly when its image under
`opEquivalence C`, in the opposite category, is a quasi-isomorphism. -/
@[simp]
lemma quasiIso_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    QuasiIso ((opEquivalence C).functor.map f.op) ↔ QuasiIso f := by
  simp only [quasiIso_iff, quasiIsoAt_opEquivalence_functor_map_iff]
  exact ⟨fun h n ↦ by simpa using h (-n), fun h n ↦ h (-n)⟩

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
  · rw [← quasiIso_opEquivalence_functor_map_iff, Quiver.Hom.op_unop, hπ]
    infer_instance
  · have : Injective (op (P.X i)) := Injective.of_iso (hX i).symm (hL _)
    infer_instance
  · rw [isStrictlyLE_iff]
    intro i hi
    exact ((L.isZero_of_isStrictlyGE (-n) (-i) (by lia)).of_iso (hX i)).unop

end CochainComplex
