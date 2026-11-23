/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.WordFiltration.AssociatedGraded

/-!
# Functoriality of word-filtration associated gradeds

Let `f : M →ₗ[R] A` and `f' : N →ₗ[R] B` generate word filtrations of two `R`-algebras. An algebra
homomorphism `g : A →ₐ[R] B` sending every generator `f m` into the first target step
`wordFiltration f' 1` preserves every filtration step (`TauCeti.Algebra.map_mem_wordFiltration`),
and also every preceding step (`TauCeti.Algebra.map_mem_wordFiltrationPrevious`). It therefore
induces linear maps of the successive quotients and an algebra homomorphism of associated gradeds.
This file constructs them and proves that they respect identities, composition and the graded
multiplication.

The hypothesis on `g` is the one of `TauCeti.Algebra.map_wordFiltration_le`. Two instances are an
isometry of quadratic forms acting on Clifford algebras, and a Lie algebra homomorphism acting on
universal enveloping algebras.

The construction generalizes the one first written for universal enveloping algebras in
`TauCeti/Algebra/Lie/UniversalEnveloping/PBW/Functoriality.lean`;
`TauCeti.UniversalEnvelopingAlgebra.mapGradedPiece` and
`TauCeti.UniversalEnvelopingAlgebra.mapAssociatedGraded` are now its specializations.

## Main definitions

* `TauCeti.Algebra.wordFiltration.mapGradedPiece`: the linear map of degree-`k` graded pieces
  induced by a filtered algebra homomorphism.
* `TauCeti.Algebra.wordFiltration.mapAssociatedGraded`: the induced algebra homomorphism of
  associated gradeds.

## Main results

* `TauCeti.Algebra.wordFiltration.mapGradedPiece_mk`: on representatives the induced map is `g`.
* `TauCeti.Algebra.wordFiltration.mapGradedPiece_gradedMul` and
  `TauCeti.Algebra.wordFiltration.mapGradedPiece_gradedOne`: the piece maps respect the graded
  multiplication and unit.
* `TauCeti.Algebra.wordFiltration.mapAssociatedGraded_id` and
  `TauCeti.Algebra.wordFiltration.mapAssociatedGraded_comp`: the construction is functorial.
-/

public section

namespace TauCeti.Algebra

universe u v w

variable {R : Type u} {M N P : Type*} {A : Type v} {B : Type w} {C : Type*}
variable [CommRing R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
variable (f : M →ₗ[R] A) (f' : N →ₗ[R] B) (f'' : P →ₗ[R] C)

namespace wordFiltration

/-- The linear map on degree-`k` graded pieces induced by an algebra homomorphism that sends each
generator into the first target filtration step. -/
noncomputable def mapGradedPiece (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1)
    (k : ℕ) : GradedPiece f k →ₗ[R] GradedPiece f' k :=
  (previousRestricted f k).mapQ (previousRestricted f' k)
    (g.toLinearMap.restrict fun _ hx => by
      simpa only [AlgHom.toLinearMap_apply] using map_mem_wordFiltration f g f' h hx)
    fun _ hx => by
      rw [Submodule.mem_comap, mem_previousRestricted_iff]
      exact map_mem_wordFiltrationPrevious f g f' h hx

/-- On quotient representatives, the induced map on a graded piece is the algebra homomorphism. -/
@[simp]
theorem mapGradedPiece_mk (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1) {k : ℕ}
    (x : wordFiltration f k) :
    mapGradedPiece f f' g h k (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨g x, map_mem_wordFiltration f g f' h x.property⟩ := by
  rw [mapGradedPiece, Submodule.mapQ_apply]
  rfl

/-- The identity algebra homomorphism induces the identity on every graded piece. -/
@[simp]
theorem mapGradedPiece_id (h : ∀ m, AlgHom.id R A (f m) ∈ wordFiltration f 1) (k : ℕ) :
    mapGradedPiece f f (AlgHom.id R A) h k = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- Composition of filtered algebra homomorphisms becomes composition on each graded piece. -/
theorem mapGradedPiece_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] C)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) (h' : ∀ n, g' (f' n) ∈ wordFiltration f'' 1)
    (h'' : ∀ m, g'.comp g (f m) ∈ wordFiltration f'' 1) (k : ℕ) :
    mapGradedPiece f f'' (g'.comp g) h'' k =
      (mapGradedPiece f' f'' g' h' k).comp (mapGradedPiece f f' g h k) := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => simp

/-- The induced map on degree zero preserves the homogeneous unit. -/
@[simp]
theorem mapGradedPiece_gradedOne (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1) :
    mapGradedPiece f f' g h 0 (gradedOne f) = gradedOne f' := by
  rw [gradedOne_def, mapGradedPiece_mk, gradedOne_def]
  exact congrArg Submodule.Quotient.mk (Subtype.ext (map_one g))

/-- The maps on graded pieces preserve homogeneous multiplication. -/
@[simp]
theorem mapGradedPiece_gradedMul (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1)
    (i j : ℕ) (x : GradedPiece f i) (y : GradedPiece f j) :
    mapGradedPiece f f' g h (i + j) (gradedMul f i j x y) =
      gradedMul f' i j (mapGradedPiece f f' g h i x) (mapGradedPiece f f' g h j y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
          rw [gradedMul_apply_mk, mapGradedPiece_mk, mapGradedPiece_mk, mapGradedPiece_mk,
            gradedMul_apply_mk]
          exact congrArg Submodule.Quotient.mk (Subtype.ext (map_mul g (x : A) (y : A)))

/-- The algebra homomorphism of associated gradeds induced by an algebra homomorphism that sends
each generator into the first target filtration step. -/
noncomputable def mapAssociatedGraded (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1) :
    AssociatedGraded f →ₐ[R] AssociatedGraded f' :=
  DirectSum.toAlgebra R (GradedPiece f)
    (fun k => (DirectSum.lof R ℕ (GradedPiece f') k).comp (mapGradedPiece f f' g h k))
    (by
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, gradedGOne_one,
        mapGradedPiece_gradedOne, associatedGraded_of_gradedOne])
    (by
      intro i j x y
      simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, gradedGMul_mul,
        mapGradedPiece_gradedMul, associatedGraded_of_mul_of])

/-- On a homogeneous element, the induced associated-graded map is the map on that graded
piece. -/
@[simp]
theorem mapAssociatedGraded_of (g : A →ₐ[R] B) (h : ∀ m, g (f m) ∈ wordFiltration f' 1) (k : ℕ)
    (x : GradedPiece f k) :
    mapAssociatedGraded f f' g h (DirectSum.of (GradedPiece f) k x) =
      DirectSum.of (GradedPiece f') k (mapGradedPiece f f' g h k x) :=
  -- Mathlib has no `DirectSum.toAlgebra_of`. The underlying function of `DirectSum.toAlgebra` is
  -- definitionally `DirectSum.toModule`, so the linear computation rule applies directly.
  DirectSum.toModule_lof R k x

/-- The identity algebra homomorphism induces the identity on the associated graded. -/
@[simp]
theorem mapAssociatedGraded_id (h : ∀ m, AlgHom.id R A (f m) ∈ wordFiltration f 1) :
    mapAssociatedGraded f f (AlgHom.id R A) h = AlgHom.id R _ := by
  apply DirectSum.algHom_ext
  intro k x
  simp

/-- Composition of filtered algebra homomorphisms becomes composition on associated gradeds. -/
theorem mapAssociatedGraded_comp (g : A →ₐ[R] B) (g' : B →ₐ[R] C)
    (h : ∀ m, g (f m) ∈ wordFiltration f' 1) (h' : ∀ n, g' (f' n) ∈ wordFiltration f'' 1)
    (h'' : ∀ m, g'.comp g (f m) ∈ wordFiltration f'' 1) :
    mapAssociatedGraded f f'' (g'.comp g) h'' =
      (mapAssociatedGraded f' f'' g' h').comp (mapAssociatedGraded f f' g h) := by
  apply DirectSum.algHom_ext
  intro k x
  simp [mapGradedPiece_comp f f' f'' g g' h h' h'']

end wordFiltration

end TauCeti.Algebra
