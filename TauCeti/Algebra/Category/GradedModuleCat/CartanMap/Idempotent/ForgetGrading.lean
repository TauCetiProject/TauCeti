/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Projective
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Specialization
public import TauCeti.RepresentationTheory.GrothendieckGroup.CartanMatrix

/-!
# Forgetting a nonnegative grading with split or semisimple degree-zero part

Let `A` be a finite-dimensional nonnegatively graded algebra over a field. Suppose that its
degree-zero part is spanned by a complete family of nonzero orthogonal idempotents. Forgetting
the grading identifies graded `G₀` specialized at `q = 1` with ordinary `G₀`.

The heads `Sᵢ = A eᵢ / A₊ eᵢ` provide the comparison: their underlying modules are pairwise
nonisomorphic simples and exhaust the ordinary simples. Their graded classes are already a
Laurent basis, so the forgetful map carries the specialized basis to the ordinary simple-class
basis. The inverse sends an ordinary simple class to the corresponding specialized head class.
No finite-global-dimension assumption is needed, and arbitrary ordinary modules need not admit
a grading.

The same holds over a field that does not split the simple modules. Let the degree-zero part
instead be a semisimple ring, and let the `eᵢ` be a complete family of orthogonal primitive
idempotents of degree zero whose left ideals `A eᵢ` are pairwise nonisomorphic. The heads `Sᵢ`
are again simple, they are pairwise nonisomorphic as ungraded modules, and their graded classes
form a Laurent basis (`TauCeti.gradedIdempotentHeadBasisOfPrimitive`); only the diagonal
idempotent coordinates change, from `1` to `dim_k End_A(Sᵢ)`. Together with the projective
comparison `TauCeti.gradedIdempotentProjectiveForgetK0Equiv`, this identifies the ordinary Cartan
matrix in the projectives `A eᵢ` and the simples `Sᵢ` with the graded Cartan matrix evaluated at
`q = 1`.

## Main definitions

* `TauCeti.gradedIdempotentHeadForgetK0Equiv`: forgetting the grading identifies `G₀^gr` at
  `q = 1` with ordinary `G₀`, for a split degree-zero part.
* `TauCeti.gradedIdempotentHeadForgetK0EquivOfPrimitive`: the same for primitive idempotents
  over a semisimple degree-zero part.

## Main results

* `TauCeti.isExhaustiveSimpleFamily_gradedIdempotentHead` and
  `TauCeti.isExhaustiveSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent`: the
  underlying heads exhaust the ordinary simple modules.
* `TauCeti.cartanMatrix_span_singleton_eq_map_gradedCartanMatrix`: in the primitive idempotent
  bases, the ordinary Cartan matrix is the graded Cartan matrix at `q = 1`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Sections 2.3--2.4, for graded
  simple modules and the passage to underlying modules.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for specialization
  of the graded Grothendieck group at `q = 1`.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Section 1.2, for positively graded rings with semisimple degree-zero part.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] {I : Type uI} [Fintype I] {e : I → A}
  (hneg : ∀ p < 0, 𝒜 p = ⊥) (he : CompleteOrthogonalIdempotents e) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (hspan : 𝒜 0 ≤ Submodule.span k (Set.range e)) (hne : ∀ i, e i ≠ 0)

local notation "S" => (fun i : I ↦
  (ObjectProperty.FullSubcategory.mk (gradedPositiveMulQuotient 𝒜 (he₀ i))
    (gradedFiniteModules_gradedPositiveMulQuotient 𝒜 (he₀ i)) :
      ObjectProperty.FullSubcategory (gradedFiniteModules 𝒜)))

local notation "T" => (fun i : I ↦ FGModuleCat.of A (gradedPositiveMulQuotient 𝒜 (he₀ i)))

include hneg he hspan hne in
/-- The underlying idempotent heads exhaust the ordinary simple modules. Thus every ordinary
simple admits a grading concentrated in degree zero, even though arbitrary modules need not. -/
theorem isExhaustiveSimpleFamily_gradedIdempotentHead : IsExhaustiveSimpleFamily T := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  exact isExhaustiveSimpleFamily_of_isExhaustiveGradedSimpleFamily S T
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan)
    (fun _ ↦ ⟨Iso.refl _⟩)

include hneg he hspan hne in
/-- **Forgetting grading identifies `G₀^gr` at `q = 1` with ordinary `G₀`** for a
finite-dimensional nonnegatively graded algebra whose degree-zero part is spanned by nonzero
complete orthogonal idempotents. -/
def gradedIdempotentHeadForgetK0Equiv :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) ≃ₗ[ℤ]
      ExactK0.{uA} (finiteModulesExactStructure A) := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies S T he.idem he₀
    (fun j i hji ↦ by
      simpa [hji] using smulGradedDimension_gradedIdempotentHead
        hneg he.toOrthogonalIdempotents he₀ hspan j i (hne i))
    (fun i ↦ smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hne i))
    (isExhaustiveGradedSimpleFamily_gradedIdempotentHead (hcomplete := he) hneg he₀ hspan)
    (fun i j hij ↦ isEmpty_linearEquiv_gradedIdempotentHead
      hneg he.toOrthogonalIdempotents he₀ hspan hij (hne i))
    (isExhaustiveSimpleFamily_gradedIdempotentHead hneg he he₀ hspan hne)
    (fun _ ↦ ⟨Iso.refl _⟩)

/-- The comparison equivalence has the actual forgetful map as its forward map. -/
@[simp]
theorem gradedIdempotentHeadForgetK0Equiv_toLinearMap :
    (gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne).toLinearMap =
      gradedFiniteModulesForgetK0 𝒜 := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  unfold gradedIdempotentHeadForgetK0Equiv
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_toLinearMap ..

/-- A specialized graded module class maps to the class of its underlying module. -/
-- Keep this a named rewrite so equivalence inverse laws can match before child normalization.
theorem gradedIdempotentHeadForgetK0Equiv_mk_of (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne
        (LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ M)) =
      ExactK0.of.{uA} ((gradedFiniteModulesForget 𝒜).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedIdempotentHeadForgetK0Equiv_toLinearMap]
  exact gradedFiniteModulesForgetK0_mk_of 𝒜 M

/-- The inverse sends the class of an ordinary idempotent head to its graded class at `q = 1`. -/
-- As above, avoid rewriting inside generic equivalence inverse laws automatically.
theorem gradedIdempotentHeadForgetK0Equiv_symm_head (i : I) :
    (gradedIdempotentHeadForgetK0Equiv hneg he he₀ hspan hne).symm (ExactK0.of.{uA} (T i)) =
      LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ (S i)) := by
  classical
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedIdempotentHead hneg he.toOrthogonalIdempotents he₀ hspan i (hne i)
  unfold gradedIdempotentHeadForgetK0Equiv
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_symm_simple ..

/-! ### Primitive idempotents over a semisimple degree-zero part -/

section Primitive

variable [IsSemisimpleRing (𝒜 0)] (hprim : ∀ i, IsPrimitiveIdempotent (e i))
  (hnoniso : Pairwise fun i j =>
    IsEmpty ((Ideal.span {e i} : Ideal A) ≃ₗ[A] (Ideal.span {e j} : Ideal A)))

include hneg he hprim in
/-- The underlying heads of a complete family of primitive idempotents exhaust the ordinary simple
modules, when the degree-zero part is a semisimple ring. -/
theorem isExhaustiveSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent :
    IsExhaustiveSimpleFamily T := by
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  exact isExhaustiveSimpleFamily_of_isExhaustiveGradedSimpleFamily S T
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)
    (fun _ ↦ ⟨Iso.refl _⟩)

include hneg he hprim hnoniso in
/-- **Forgetting grading identifies `G₀^gr` at `q = 1` with ordinary `G₀`** for a
finite-dimensional nonnegatively graded algebra whose degree-zero part is a semisimple ring,
given a complete family of orthogonal primitive idempotents `eᵢ` of degree zero whose left ideals
`A eᵢ` are pairwise nonisomorphic. The field need not split the simple modules. -/
def gradedIdempotentHeadForgetK0EquivOfPrimitive :
    LaurentSpecialization (1 : ℤˣ)
        (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)) ≃ₗ[ℤ]
      ExactK0.{uA} (finiteModulesExactStructure A) :=
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  gradedFiniteModulesForgetK0EquivOfSimpleFamilies S T he.idem he₀
    (fun _ _ hij ↦ smulGradedDimension_gradedPositiveMulQuotient_eq_zero hneg (hprim _) (he₀ _)
      (hprim _) (hnoniso hij.symm))
    (fun i ↦ smulGradedDimension_gradedPositiveMulQuotient_self_ne_zero hneg (he.idem i) (he₀ i)
      (hprim i).ne_zero)
    (isExhaustiveGradedSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
      hprim)
    (fun i j hij ↦ isEmpty_linearEquiv_gradedPositiveMulQuotient hneg (hprim i) (he₀ i) (hprim j)
      (he₀ j) (hnoniso hij))
    (isExhaustiveSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀ hprim)
    (fun _ ↦ ⟨Iso.refl _⟩)

/-- The comparison equivalence has the actual forgetful map as its forward map. -/
@[simp]
theorem gradedIdempotentHeadForgetK0EquivOfPrimitive_toLinearMap :
    (gradedIdempotentHeadForgetK0EquivOfPrimitive hneg he he₀ hprim hnoniso).toLinearMap =
      gradedFiniteModulesForgetK0 𝒜 := by
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  unfold gradedIdempotentHeadForgetK0EquivOfPrimitive
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_toLinearMap ..

/-- A specialized graded module class maps to the class of its underlying module. -/
-- Keep this a named rewrite so equivalence inverse laws can match before child normalization.
theorem gradedIdempotentHeadForgetK0EquivOfPrimitive_mk_of
    (M : (gradedFiniteModules 𝒜).FullSubcategory) :
    gradedIdempotentHeadForgetK0EquivOfPrimitive hneg he he₀ hprim hnoniso
        (LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ M)) =
      ExactK0.of.{uA} ((gradedFiniteModulesForget 𝒜).obj M) := by
  rw [← LinearEquiv.coe_coe, gradedIdempotentHeadForgetK0EquivOfPrimitive_toLinearMap]
  exact gradedFiniteModulesForgetK0_mk_of 𝒜 M

/-- The inverse sends the class of an ordinary head to its graded class at `q = 1`. -/
-- As above, avoid rewriting inside generic equivalence inverse laws automatically.
theorem gradedIdempotentHeadForgetK0EquivOfPrimitive_symm_head (i : I) :
    (gradedIdempotentHeadForgetK0EquivOfPrimitive hneg he he₀ hprim hnoniso).symm
        (ExactK0.of.{uA} (T i)) =
      LaurentSpecialization.mk 1 (LaurentK0.of.{uA} _ (S i)) := by
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  unfold gradedIdempotentHeadForgetK0EquivOfPrimitive
  exact gradedFiniteModulesForgetK0EquivOfSimpleFamilies_symm_simple ..

include hneg he hprim hnoniso in
/-- **The Cartan matrix is the graded Cartan matrix at `q = 1`** in the bases given by a complete
family of orthogonal primitive idempotents `eᵢ` of degree zero with pairwise nonisomorphic left
ideals, over a semisimple degree-zero part: the ungraded matrix in the projectives `A eᵢ` and the
underlying heads `Sᵢ` is the evaluation at one of the graded matrix in the graded projectives
`A eᵢ` and the graded heads `Sᵢ`. -/
theorem cartanMatrix_span_singleton_eq_map_gradedCartanMatrix :
    letI : IsArtinianRing A := IsArtinianRing.of_finite k A
    letI : ∀ i, IsSimpleModule A (T i) := fun i ↦
      isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
    cartanMatrix (fun i ↦ (⟨ModuleCat.of A (Ideal.span {e i}), finiteProjectiveModules_iff.2
          ⟨inferInstance, (he.idem i).projective_span_singleton⟩⟩ :
            (finiteProjectiveModules A).FullSubcategory)) T
        (fun i ↦ (hprim i).isIndecomposableModule) hnoniso
        (isExhaustiveIndecomposableProjectiveFamily_span_singleton he hprim)
        (fun i j hij ↦ isEmpty_linearEquiv_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
          (hprim j) (he₀ j) (hnoniso hij))
        (isExhaustiveSimpleFamily_gradedPositiveMulQuotient_of_isPrimitiveIdempotent hneg he he₀
          hprim) =
      (gradedCartanMatrix 𝒜
        (gradedIdempotentProjectiveBasisOfPrimitive he he₀
          (fun i ↦ Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, he₀ i⟩) hprim hnoniso)
        (gradedIdempotentHeadBasisOfPrimitive hneg he he₀ hprim hnoniso)).map
        (laurentEval (1 : ℤˣ)) := by
  classical
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  let _ : ∀ i, IsSimpleModule A (T i) := fun i ↦
    isSimpleModule_gradedPositiveMulQuotient hneg (hprim i) (he₀ i)
  refine (cartanMatrix_eq_toMatrix ..).trans <|
    toMatrix_cartanMap_eq_map_gradedCartanMatrix _ _ _ _ _ (fun j ↦ ?_) fun i ↦ ?_
  · -- The underlying module of the graded ideal `GradedModuleCat.ofIdeal` is the ideal itself.
    rw [indecomposableProjectiveClassBasis_apply, LaurentSpecialization.basis_apply,
      gradedIdempotentProjectiveBasisOfPrimitive_apply, gradedFiniteProjectiveModulesForgetK0_mk_of,
      gradedFiniteProjectiveModulesForget_obj]
  · simp only [LaurentSpecialization.basis_apply, gradedIdempotentHeadBasisOfPrimitive_apply,
      gradedFiniteModulesForgetK0_mk_of, gradedFiniteModulesForget_obj]
    exact (simpleClassBasis_apply T _ _ i).symm

end Primitive

end TauCeti
