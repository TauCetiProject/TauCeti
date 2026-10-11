/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Head
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Admissible
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Graded

/-!
# The graded Cartan map of a zigzag algebra

Let `Z` be the zigzag relation quotient of a finite simple graph, graded by path length, and let
`P_j = Z e_j` be its graded vertex projectives. Each `P_j` is a finite graded module with
projective underlying module, so it has a class `[P_j]` in the graded Grothendieck group
`K₀^gr(proj Z)`, and the graded Cartan map `TauCeti.gradedCartanMap` sends it to its class in
`G₀^gr(mod Z)`. This file reads that image through the idempotent coordinates
`TauCeti.gradedIdempotentCoordinate` of the vertex idempotents `e_i`, which send the class of a
finite graded module `M` to `∑ₚ dim_k(e_i • Mₚ) qᵖ`.

Since `e_i • (P_j)ₚ` is the degree-`p` part of the corner `e_i Z e_j`, the `e_i`-coordinate of
the image of `[P_j]` is the entry `C_G(q)_{ij}` of the graded Cartan matrix
`TauCeti.zigzagGradedCartanMatrix`. When the graph has no isolated vertex this entry is `1 + q²`
on the diagonal, `q` on an edge and zero otherwise, so the coordinates of the graded Cartan map
on the vertex projectives form the matrix

```text
C_G(q) = (1 + q²) I + q A_G.
```

The determinant of `C_G(q)` is a nonzero polynomial, as its value at `q = 0` is `1`. Hence the
images of the classes `[P_j]` are linearly independent over `ℤ[q,q⁻¹]` in `G₀^gr(mod Z)`, and so
are the classes `[P_j]` themselves in `K₀^gr(proj Z)`. This holds for every finite graph,
including graphs with isolated vertices, where the corner at an isolated vertex is spanned by its
idempotent.

The path-length grading of `Z` is nonnegative, and its degree-zero piece is spanned by the
complete orthogonal family of vertex idempotents. The graded simple `S_i`, the quotient of `P_i`
by its paths of positive length, is therefore simple, every simple finite graded `Z`-module is a
shift `S_i{d}`, and the classes `[S_i]` form a basis of `G₀^gr(mod Z)` over `ℤ[q,q⁻¹]` whose
coordinates are the idempotent coordinates (`TauCeti.gradedIdempotentHeadBasis`). In this basis
the image of `[P_j]` is the `j`th column of the graded Cartan matrix:

```text
c^gr [P_j] = ∑ᵢ C_G(q)_{ij} [S_i].
```

These statements concern the relation quotient. On a component with an edge it is the ordinary
zigzag algebra; singleton components of the public algebra `TauCeti.zigzagAlgebra` instead use
the dual numbers.

## Main definitions

* `TauCeti.zigzagGradedProjectiveClass`: the class `[P_j]` in `K₀^gr(proj Z)`.
* `TauCeti.zigzagGradedSimple`: the graded vertex simple `S_i`.
* `TauCeti.zigzagGradedSimpleClassBasis`: the basis `[S_i]` of `G₀^gr(mod Z)`.

## Main results

* `TauCeti.map_subtype_smul_zigzagProjectiveGrade`: `e_i • (P_j)ₚ` is the degree-`p` part of
  the corner `e_i Z e_j`.
* `TauCeti.smulGradedDimension_zigzagGradedProjective`: the graded dimension of `e_i • P_j` is
  the graded Cartan entry `C_G(q)_{ij}`.
* `TauCeti.gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent`:
  the `e_i`-coordinate of the image of `[P_j]` under the graded Cartan map is `C_G(q)_{ij}`.
* `TauCeti.gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass`: its value
  `(1 + q²) δᵢⱼ + q A_{ij}` when no vertex is isolated.
* `TauCeti.linearIndependent_gradedCartanMap_zigzagGradedProjectiveClass` and
  `TauCeti.linearIndependent_zigzagGradedProjectiveClass`: the images of the vertex-projective
  classes in `G₀^gr(mod Z)`, and the classes themselves in `K₀^gr(proj Z)`, are linearly
  independent over `ℤ[q,q⁻¹]`.
* `TauCeti.simple_zigzagGradedSimple` and
  `TauCeti.isExhaustiveGradedSimpleFamily_zigzagGradedSimple`: the `S_i` are simple, and every
  simple finite graded module is a shift of one of them.
* `TauCeti.gradedCartanMap_zigzagGradedProjectiveClass_eq_sum`: the image of `[P_j]` is
  `∑ᵢ C_G(q)_{ij} [S_i]`.
* `TauCeti.zigzagGradedSimpleClassBasis_repr_gradedCartanMap_zigzagGradedProjectiveClass`: its
  `[S_i]`-coordinate is `(1 + q²) δᵢⱼ + q A_{ij}` when no vertex is isolated.

## References

* Huerfano--Khovanov, *A category for the adjoint representation*, Section 3, for the quantum
  Cartan matrix of a zigzag algebra.
* Ehrig--Tubbenhauer, *Algebraic properties of zigzag algebras*, Section 2.
* Dancso--Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded Cartan matrix
  as the matrix of the graded Cartan map.
-/

public section

namespace TauCeti

open CategoryTheory LaurentPolynomial
open scoped Pointwise

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]

/-! ### The vertex projectives as finite graded projectives -/

/-- A graded vertex projective is a finite graded module with projective underlying module, so it
has a class in `K₀^gr(proj Z)`. -/
theorem gradedFiniteProjectiveModules_zigzagGradedProjective (j : V) :
    gradedFiniteProjectiveModules (zigzagIntegerGrade k G) (zigzagGradedProjective k G j) := by
  let _ := zigzagIntegerGradedAlgebra k G
  have hI := isHomogeneous_zigzagProjective k G j
  rw [zigzagProjective_def] at hI
  simpa only [zigzagGradedProjective, zigzagProjective_def] using
    gradedFiniteProjectiveModules_ofIdeal_span_singleton
      (isIdempotentElem_zigzagVertexIdempotent k G j) hI

/-- The class `[P_j]` of the graded vertex projective `P_j = Z e_j` in the graded Grothendieck
group `K₀^gr(proj Z)` of finite graded projective modules. -/
noncomputable def zigzagGradedProjectiveClass (j : V) :
    LaurentK0.{max u w} (gradedFiniteProjectiveModulesExactStructure (zigzagIntegerGrade k G)) :=
  LaurentK0.of _ ⟨zigzagGradedProjective k G j,
    gradedFiniteProjectiveModules_zigzagGradedProjective k G j⟩

/-- The class `[P_j]` is the Grothendieck class of the graded vertex projective. -/
theorem zigzagGradedProjectiveClass_def (j : V) :
    zigzagGradedProjectiveClass k G j =
      LaurentK0.of _ ⟨zigzagGradedProjective k G j,
        gradedFiniteProjectiveModules_zigzagGradedProjective k G j⟩ :=
  (rfl)

/-! ### Idempotent pieces of the vertex projectives -/

/-- **The idempotent pieces of a vertex projective are graded corners**: `e_i • (P_j)ₚ`, viewed
inside `Z`, is the degree-`p` part of the corner `e_i Z e_j`. -/
theorem map_subtype_smul_zigzagProjectiveGrade (i j : V) (p : ℤ) :
    (zigzagVertexIdempotent k G i • zigzagProjectiveGrade k G j p).map
        ((zigzagProjective k G j).subtype.restrictScalars k) =
      zigzagIntegerGradedCorner k G i j p := by
  let _ := zigzagIntegerGradedAlgebra k G
  rw [← zigzagGradedProjective_piece]
  have key : ∀ (I : Ideal (nonisolatedZigzagQuotient k G))
      (hI : I.IsHomogeneous (zigzagIntegerGrade k G)),
      I = Ideal.span {zigzagVertexIdempotent k G j} →
      (zigzagVertexIdempotent k G i • (GradedModuleCat.ofIdeal _ I hI).grading.piece p).map
          (I.subtype.restrictScalars k) =
        cornerSubmodule k (zigzagVertexIdempotent k G i)
          (zigzagVertexIdempotent k G j) ⊓ zigzagIntegerGrade k G p := by
    rintro _ hI rfl
    exact GradedModuleCat.map_subtype_smul_ofIdeal_span_singleton_piece
      (isIdempotentElem_zigzagVertexIdempotent k G i)
      (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
      (isIdempotentElem_zigzagVertexIdempotent k G j) hI p
  calc
    _ = cornerSubmodule k (zigzagVertexIdempotent k G i)
        (zigzagVertexIdempotent k G j) ⊓ zigzagIntegerGrade k G p :=
      key _ (isHomogeneous_zigzagProjective k G j) (zigzagProjective_def k G j)
    _ = zigzagIntegerGradedCorner k G i j p := by
      ext x
      rw [Submodule.mem_inf, mem_cornerSubmodule_iff k
        (isIdempotentElem_zigzagVertexIdempotent k G i)
        (isIdempotentElem_zigzagVertexIdempotent k G j),
        mem_zigzagIntegerGradedCorner_iff, mem_zigzagCorner_iff]

/-- The dimension of `e_i • (P_j)ₚ` is the dimension of the degree-`p` corner of `e_i Z e_j`. -/
theorem finrank_smul_zigzagProjectiveGrade (i j : V) (p : ℤ) :
    Module.finrank k ↥(zigzagVertexIdempotent k G i • zigzagProjectiveGrade k G j p) =
      Module.finrank k (zigzagIntegerGradedCorner k G i j p) := by
  rw [← map_subtype_smul_zigzagProjectiveGrade]
  exact (Submodule.equivMapOfInjective _ Subtype.val_injective _).finrank_eq

/-- Graded corners vanish outside degrees `0`, `1` and `2`. -/
private theorem finrank_zigzagIntegerGradedCorner_eq_zero (i j : V) {p : ℤ}
    (hp : p ∉ (Finset.range 3).map Nat.castEmbedding) :
    Module.finrank k (zigzagIntegerGradedCorner k G i j p) = 0 := by
  rcases lt_or_ge p 0 with hneg | hnonneg
  · rw [zigzagIntegerGradedCorner_eq_bot_of_neg k G i j hneg, finrank_bot]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    simp only [Finset.mem_map, Finset.mem_range, Nat.castEmbedding_apply, Nat.cast_inj,
      exists_eq_right, not_lt] at hp
    rw [zigzagIntegerGradedCorner_ofNat]
    exact finrank_zigzagGradedCorner_of_three_le k G i j hp

/-- **The graded dimension of `e_i • P_j` is the graded Cartan entry** `C_G(q)_{ij}`. -/
theorem smulGradedDimension_zigzagGradedProjective (i j : V) :
    (zigzagGradedProjective k G j).smulGradedDimension (zigzagVertexIdempotent k G i) =
      Polynomial.toLaurent (zigzagGradedCartanMatrix k G i j) := by
  have hzero (p : ℤ) (hp : p ∉ (Finset.range 3).map Nat.castEmbedding) :
      Subsingleton (zigzagIntegerGradedCorner k G i j p) := by
    rw [← Module.finrank_zero_iff (R := k),
      finrank_zigzagIntegerGradedCorner_eq_zero k G i j hp]
  have hfin : HasFiniteLaurentSupport k fun p => zigzagIntegerGradedCorner k G i j p :=
    .of_finset (fun _ => inferInstance) _ hzero
  calc
    _ = gradedDimension k (fun p => zigzagIntegerGradedCorner k G i j p) hfin :=
      LaurentPolynomial.ext fun p => by
        rw [GradedModuleCat.coeff_smulGradedDimension, coeff_gradedDimension,
          zigzagGradedProjective_piece, finrank_smul_zigzagProjectiveGrade]
    _ = _ := by
      have hcorner (n : ℕ) :
          Module.finrank k (zigzagIntegerGradedCorner k G i j (Nat.castEmbedding n)) =
            Module.finrank k (zigzagGradedCorner k G i j n) := by
        rw [Nat.castEmbedding_apply, zigzagIntegerGradedCorner_ofNat]
      rw [gradedDimension_eq_sum hfin _ hzero, Finset.sum_map,
        zigzagGradedCartanMatrix_apply_eq_sum]
      simp only [hcorner, Finset.sum_range_succ, Finset.sum_range_zero, Nat.castEmbedding_apply,
        map_add, map_mul, map_natCast, Polynomial.toLaurent_X, Polynomial.toLaurent_X_pow,
        Nat.cast_zero, Nat.cast_one, T_zero, mul_one, zero_add]

/-! ### The graded Cartan map on the vertex projectives -/

/-- **The coordinates of the graded Cartan map are the graded Cartan matrix.** The
`e_i`-coordinate of the image of `[P_j]` in `G₀^gr(mod Z)` is the entry `C_G(q)_{ij}`. -/
theorem gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent
    (i j : V) :
    gradedIdempotentCoordinate (isIdempotentElem_zigzagVertexIdempotent k G i)
        (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
        (gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j)) =
      Polynomial.toLaurent (zigzagGradedCartanMatrix k G i j) := by
  rw [zigzagGradedProjectiveClass_def, gradedCartanMap_of, gradedIdempotentCoordinate_of,
    smulGradedDimension_zigzagGradedProjective]

/-- **The graded Cartan map of a zigzag algebra has matrix `(1 + q²) I + q A_G`** in the
idempotent coordinates on the vertex projectives, for a graph without isolated vertices: the
`e_i`-coordinate of the image of `[P_j]` is `1 + q²` for `i = j`, `q` on an edge and zero
otherwise. -/
theorem gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass
    [DecidableEq V] [DecidableRel G.Adj] (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    gradedIdempotentCoordinate (isIdempotentElem_zigzagVertexIdempotent k G i)
        (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
        (gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j)) =
      (if i = j then 1 + T 2 else 0) + if G.Adj i j then T 1 else 0 := by
  rw [gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent,
    ← zigzagProjectiveQHom_eq_toLaurent k G hns, ← zigzagProjectiveQHomMatrix_apply_eq_qHom,
    zigzagProjectiveQHomMatrix_apply k G hns]

/-- **The images of the vertex-projective classes under the graded Cartan map are linearly
independent** over `ℤ[q,q⁻¹]`: their idempotent coordinates form the graded Cartan matrix, whose
determinant is a nonzero polynomial. -/
theorem linearIndependent_gradedCartanMap_zigzagGradedProjectiveClass :
    LinearIndependent (LaurentPolynomial ℤ)
      (gradedCartanMap (zigzagIntegerGrade k G) ∘ zigzagGradedProjectiveClass k G) := by
  classical
  have := Fintype.ofFinite V
  let coord := LinearMap.pi fun i : V =>
    gradedIdempotentCoordinate (isIdempotentElem_zigzagVertexIdempotent k G i)
      (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
  refine LinearIndependent.of_comp coord ?_
  have hcols : coord ∘ (gradedCartanMap (zigzagIntegerGrade k G) ∘
      zigzagGradedProjectiveClass k G) =
        ((zigzagGradedCartanMatrix k G).map Polynomial.toLaurent).col := by
    ext j i
    simp only [coord, Function.comp_apply, LinearMap.pi_apply, Matrix.col_apply,
      Matrix.map_apply,
      gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent]
  rw [hcols]
  refine Matrix.linearIndependent_cols_of_det_ne_zero ?_
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Polynomial.toLaurent_ne_zero]
  exact det_zigzagGradedCartanMatrix_ne_zero k G

/-- **The vertex-projective classes are linearly independent in `K₀^gr(proj Z)`** over
`ℤ[q,q⁻¹]`, since their images under the graded Cartan map are. -/
theorem linearIndependent_zigzagGradedProjectiveClass :
    LinearIndependent (LaurentPolynomial ℤ) (zigzagGradedProjectiveClass k G) :=
  (linearIndependent_gradedCartanMap_zigzagGradedProjectiveClass k G).of_comp _

/-! ### The graded simples and the simple-class basis -/

/-- The degree-zero piece of the path-length grading is spanned by the vertex idempotents. -/
private theorem zigzagIntegerGrade_zero_le_span :
    zigzagIntegerGrade k G 0 ≤ Submodule.span k (Set.range (zigzagVertexIdempotent k G)) := by
  have h0 : zigzagIntegerGrade k G 0 = zigzagGrade k G 0 := by
    simpa only [Nat.cast_zero] using zigzagIntegerGrade_ofNat k G 0
  rw [h0]
  exact (zigzagGrade_zero_eq_span_range_vertexIdempotent k G).le

/-- **The graded simple module `S_i`** at a vertex: the head of the graded vertex projective
`P_i = Z e_i`, its quotient by the span of the paths of positive length starting at `i`. -/
noncomputable def zigzagGradedSimple (i : V) :
    GradedModuleCat.{max u w} (zigzagIntegerGrade k G) :=
  let _ := zigzagIntegerGradedAlgebra k G
  gradedPositiveMulQuotient (zigzagIntegerGrade k G)
    (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)

/-- A graded vertex simple is the generic graded head of its vertex idempotent. -/
theorem zigzagGradedSimple_def (i : V) :
    zigzagGradedSimple k G i =
      let _ := zigzagIntegerGradedAlgebra k G
      gradedPositiveMulQuotient (zigzagIntegerGrade k G)
        (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i) := by
  rw [zigzagGradedSimple]

/-- The class of a vertex-projective element in its graded simple head. -/
noncomputable def zigzagGradedSimpleMk (i : V) :
    (Ideal.span {zigzagVertexIdempotent k G i} : Ideal (nonisolatedZigzagQuotient k G)) →ₗ[
      nonisolatedZigzagQuotient k G]
      zigzagGradedSimple k G i :=
  let _ := zigzagIntegerGradedAlgebra k G
  (eqToHom (zigzagGradedSimple_def k G i).symm).hom ∘ₗ
    gradedPositiveMulQuotientMk (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)

/-- The head projection is the generic quotient map, transported to the graded vertex simple. -/
theorem zigzagGradedSimpleMk_def (i : V) :
    zigzagGradedSimpleMk k G i =
      let _ := zigzagIntegerGradedAlgebra k G
      (eqToHom (zigzagGradedSimple_def k G i).symm).hom ∘ₗ
        gradedPositiveMulQuotientMk
          (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i) :=
  (rfl)

/-- Every element of the graded simple head has a vertex-projective representative. -/
theorem zigzagGradedSimpleMk_surjective (i : V) :
    Function.Surjective (zigzagGradedSimpleMk k G i) := by
  let _ := zigzagIntegerGradedAlgebra k G
  have hs : Function.Surjective (eqToHom (zigzagGradedSimple_def k G i).symm).hom :=
    (GradedModuleCat.epi_iff_surjective _).1 inferInstance
  exact hs.comp (gradedPositiveMulQuotientMk_surjective _)

/-- A representative vanishes in the graded head exactly when it lies in the
positive-degree ideal of its vertex projective. -/
@[simp]
theorem zigzagGradedSimpleMk_eq_zero_iff (i : V)
    (x : (Ideal.span {zigzagVertexIdempotent k G i} : Ideal (nonisolatedZigzagQuotient k G))) :
    zigzagGradedSimpleMk k G i x = 0 ↔
      (x : nonisolatedZigzagQuotient k G) ∈
        gradedPositiveMulIdeal (zigzagIntegerGrade k G) (zigzagVertexIdempotent k G i) := by
  let _ := zigzagIntegerGradedAlgebra k G
  have hi : Function.Injective (eqToHom (zigzagGradedSimple_def k G i).symm).hom :=
    (GradedModuleCat.mono_iff_injective _).1 inferInstance
  rw [zigzagGradedSimpleMk_def, LinearMap.comp_apply,
    LinearMap.map_eq_zero_iff _ hi, gradedPositiveMulQuotientMk_eq_zero_iff]

/-- A graded vertex simple is a finite graded module. -/
theorem gradedFiniteModules_zigzagGradedSimple (i : V) :
    gradedFiniteModules (zigzagIntegerGrade k G) (zigzagGradedSimple k G i) :=
  let _ := zigzagIntegerGradedAlgebra k G
  gradedFiniteModules_gradedPositiveMulQuotient _ _

/-- **The graded vertex simples are simple graded modules.** -/
theorem simple_zigzagGradedSimple (i : V) : Simple (zigzagGradedSimple k G i) :=
  let _ := zigzagIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  simple_gradedIdempotentHead (fun _ => zigzagIntegerGrade_eq_bot_of_neg k G)
    (completeOrthogonalIdempotents_zigzagVertexIdempotent k G).toOrthogonalIdempotents
    (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G)
    (zigzagIntegerGrade_zero_le_span k G) i (zigzagVertexIdempotent_ne_zero k G i)

/-- **Every simple finite graded `Z`-module is a shift `S_i{d}` of a graded vertex simple.** -/
theorem isExhaustiveGradedSimpleFamily_zigzagGradedSimple :
    IsExhaustiveGradedSimpleFamily fun i : V =>
      (⟨zigzagGradedSimple k G i, gradedFiniteModules_zigzagGradedSimple k G i⟩ :
        (gradedFiniteModules (zigzagIntegerGrade k G)).FullSubcategory) :=
  let _ := zigzagIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  isExhaustiveGradedSimpleFamily_gradedIdempotentHead
    (hcomplete := completeOrthogonalIdempotents_zigzagVertexIdempotent k G)
    (fun _ => zigzagIntegerGrade_eq_bot_of_neg k G)
    (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G)
    (zigzagIntegerGrade_zero_le_span k G)

/-- **The simple-class basis of `G₀^gr(mod Z)`** over `ℤ[q,q⁻¹]`: its vector at `i` is the class
`[S_i]` of the graded vertex simple. -/
noncomputable def zigzagGradedSimpleClassBasis :
    Module.Basis V (LaurentPolynomial ℤ)
      (LaurentK0.{max u w} (gradedFiniteModulesExactStructure (zigzagIntegerGrade k G))) :=
  let _ := zigzagIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  gradedIdempotentHeadBasis (fun _ => zigzagIntegerGrade_eq_bot_of_neg k G)
    (completeOrthogonalIdempotents_zigzagVertexIdempotent k G)
    (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G)
    (zigzagIntegerGrade_zero_le_span k G) (zigzagVertexIdempotent_ne_zero k G)

/-- The basis vector of `TauCeti.zigzagGradedSimpleClassBasis` at `i` is the class `[S_i]`. -/
@[simp]
theorem zigzagGradedSimpleClassBasis_apply (i : V) :
    zigzagGradedSimpleClassBasis k G i =
      LaurentK0.of _ ⟨zigzagGradedSimple k G i, gradedFiniteModules_zigzagGradedSimple k G i⟩ :=
  let _ := zigzagIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  gradedIdempotentHeadBasis_apply _ _ _ _ _ i

/-- The coordinates in the basis `[S_i]` are the idempotent coordinates of the vertex
idempotents: the `i`th coordinate of `[M]` is `∑ₚ dim_k(e_i • Mₚ) qᵖ`. -/
@[simp]
theorem zigzagGradedSimpleClassBasis_repr_apply
    (x : LaurentK0.{max u w} (gradedFiniteModulesExactStructure (zigzagIntegerGrade k G)))
    (i : V) :
    (zigzagGradedSimpleClassBasis k G).repr x i =
      gradedIdempotentCoordinate (isIdempotentElem_zigzagVertexIdempotent k G i)
        (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i) x :=
  let _ := zigzagIntegerGradedAlgebra k G
  let _ := Fintype.ofFinite V
  gradedIdempotentHeadBasis_repr_apply _ _ _ _ _ x i

/-! ### The graded Cartan map in the simple basis -/

/-- **The graded Cartan matrix records the composition factors of the vertex projectives.** The
`[S_i]`-coordinate of the image of `[P_j]` in `G₀^gr(mod Z)` is the graded Cartan entry
`C_G(q)_{ij}`. -/
theorem zigzagGradedSimpleClassBasis_repr_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent
    (i j : V) :
    (zigzagGradedSimpleClassBasis k G).repr
        (gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j)) i =
      Polynomial.toLaurent (zigzagGradedCartanMatrix k G i j) := by
  rw [zigzagGradedSimpleClassBasis_repr_apply,
    gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent]

/-- **The image of `[P_j]` under the graded Cartan map** is `∑ᵢ C_G(q)_{ij} [S_i]` in
`G₀^gr(mod Z)`: the `j`th column of the graded Cartan matrix in the simple basis. -/
theorem gradedCartanMap_zigzagGradedProjectiveClass_eq_sum [Fintype V] (j : V) :
    gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j) =
      ∑ i, Polynomial.toLaurent (zigzagGradedCartanMatrix k G i j) •
        zigzagGradedSimpleClassBasis k G i := by
  conv_lhs => rw [← (zigzagGradedSimpleClassBasis k G).sum_repr
    (gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j))]
  simp only [
    zigzagGradedSimpleClassBasis_repr_gradedCartanMap_zigzagGradedProjectiveClass_eq_toLaurent]

/-- **The graded Cartan matrix `(1 + q²) I + q A_G` in the simple basis**, for a graph without
isolated vertices: the `[S_i]`-coordinate of the image of `[P_j]` is `1 + q²` for `i = j`, `q` on
an edge and zero otherwise. -/
theorem zigzagGradedSimpleClassBasis_repr_gradedCartanMap_zigzagGradedProjectiveClass
    [DecidableEq V] [DecidableRel G.Adj] (hns : ∀ i : V, ∃ j, G.Adj i j) (i j : V) :
    (zigzagGradedSimpleClassBasis k G).repr
        (gradedCartanMap (zigzagIntegerGrade k G) (zigzagGradedProjectiveClass k G j)) i =
      (if i = j then 1 + T 2 else 0) + if G.Adj i j then T 1 else 0 := by
  rw [zigzagGradedSimpleClassBasis_repr_apply,
    gradedIdempotentCoordinate_gradedCartanMap_zigzagGradedProjectiveClass k G hns]

end TauCeti
