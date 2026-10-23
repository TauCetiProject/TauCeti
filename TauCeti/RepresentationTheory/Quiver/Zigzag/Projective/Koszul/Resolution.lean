/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.DirectSum
public import TauCeti.Algebra.Module.GradedModule.Resolution
public import TauCeti.Algebra.Module.GradedModule.Shift
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.CartanMap
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Projective.Koszul.Complex

/-!
# The Koszul resolution of a zigzag simple module

Let `Z` be the zigzag relation quotient `TauCeti.nonisolatedZigzagQuotient` of a finite graph `G`,
graded by path length, and let `Π` be the signless preprojective algebra of the doubled quiver,
the quadratic dual of the quadratic zigzag presentation. The Koszul complex `K` of the simple
`Z`-module at a vertex `v`, with terms `K_n = ⨁_u Hom_k(e_u Π_n e_v, Z e_u)`, is exact in every
positive homological degree when every signless vertex Koszul complex
`0 → e_w Π → ⨁_{j ∼ w} e_j Π` is exact at its left end
(`TauCeti.range_zigzagKoszulDifferential_eq_ker`). This file completes `K` to a linear graded
projective resolution of the graded simple module `S_v` (`TauCeti.zigzagGradedSimple`).

* **Grading.** A map `f ∈ K_n` has degree `p` when its values have degree `p - n`. Evaluation on
  bases of the finite-dimensional corners `e_u Π_n e_v` identifies `K_n` with a finite direct sum
  of vertex projectives `Z e_u`, which makes this an internal grading and `K_n` a projective
  module. The term `K_n` is generated in degree `n`, by the maps with values in the lines of the
  vertex idempotents, and the differential preserves degrees because arrows have degree one.
* **Augmentation.** Since `e_v Π_0 e_v` is the line of `e_v` and `e_u Π_0 e_v = 0` for `u ≠ v`, an
  element `f ∈ K_0` is determined by `f_v(e_v) ∈ Z e_v`, and the augmentation sends `f` to the class
  of `f_v(e_v)` in the head `S_v` of `Z e_v`. Every arrow out of `v`, and the volume class at `v`,
  is the value `(d g)_v(e_v)` of a boundary, because the arrows of `Π` are nonzero; so the
  boundaries account for the whole radical of `Z e_v`, which is the kernel of the augmentation.

Hence `S_v` has a linear resolution whenever the signless Koszul complexes are exact at their left
ends; a non-backtracking choice of neighbours provides this for every connected graph which is
not a tree. For such graphs every vertex simple module `S_v`, concentrated in degree zero, has a
linear resolution, and its grading shifts have the correspondingly shifted resolutions; this is
Koszulity in the sense of Beilinson--Ginzburg--Soergel. Through
`TauCeti.coeff_inv_zigzagGradedCartanMatrix_map_aeval_neg_X_eq`, the multiplicities of these
resolutions are the coefficients of the inverse graded Cartan matrix `C_G(-X)⁻¹`.

## Main definitions

* `TauCeti.zigzagKoszulTermGrading`: the internal grading of `K_n`.
* `TauCeti.zigzagKoszulAugmentation`: the augmentation `K_0 → S_v`.
* `TauCeti.zigzagKoszulResolution`: the graded projective resolution of `S_v` by `K`.

## Main results

* `TauCeti.mem_zigzagKoszulTermGrading_piece_iff`: the homogeneous pieces of `K_n`.
* `TauCeti.isHomogeneous_zigzagKoszulDifferential` and
  `TauCeti.isHomogeneous_zigzagKoszulAugmentation`: the maps preserve internal degree.
* `TauCeti.isGeneratedInDegree_zigzagKoszulTermGrading`: `K_n` is generated in degree `n`.
* `TauCeti.exact_zigzagKoszulDifferential_zigzagKoszulAugmentation`: exactness at `K_0`.
* `TauCeti.isLinear_zigzagKoszulResolution`: the Koszul resolution is linear.
* `TauCeti.exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_isAcyclic`: the
  vertex simple modules, concentrated in degree zero, of the zigzag algebra of a connected graph
  which is not a tree have linear resolutions.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  J. Amer. Math. Soc. 9 (1996), Sections 1.2 and 2, for linear resolutions and the Koszul
  complex.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, J. Algebra 246
  (2001), Section 3, for the zigzag algebra and its quadratic dual.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3, for the vertex Koszul complexes of `Π`.
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra DoubledQuiver
open scoped _root_.DirectSum

universe u w

variable (k : Type w) [Field k] {V : Type u} [Fintype V] (G : SimpleGraph V)
  [DecidableRel G.Adj]

local notation "Z" => nonisolatedZigzagQuotient k G
local notation "Π" => signlessPreprojectiveAlgebra k (DoubledQuiver G)
local notation "σ" => signlessPreprojectiveMk k (DoubledQuiver G)
local notation "C" => signlessPreprojectiveCorner k (DoubledQuiver G)

attribute [local instance] zigzagIntegerGradedAlgebra

/-! ### The terms as direct sums of vertex projectives -/

/-- The summands of `K_n`: one vertex projective `Z e_u` for each vector of a basis of
`e_u Π_n e_v`. -/
private abbrev TermIndex (v : V) (n : ℕ) : Type u :=
  Σ u : V, Fin (Module.finrank k (C n (vertex G v) (vertex G u)))

/-- The chosen basis of the graded corner `e_u Π_n e_v`. -/
private noncomputable abbrev cornerBasis (v : V) (n : ℕ) (u : V) :
    Module.Basis (Fin (Module.finrank k (C n (vertex G v) (vertex G u)))) k
      (C n (vertex G v) (vertex G u)) :=
  Module.finBasis k _

/-- Evaluation on the chosen bases identifies `K_n` with a finite direct sum of vertex
projectives. -/
private noncomputable def termEquiv (v : V) (n : ℕ) :
    ZigzagKoszulTerm k G v n ≃ₗ[Z] ⨁ s : TermIndex k G v n, zigzagProjective k G s.1 :=
  (LinearEquiv.piCongrRight fun u => ((cornerBasis k G v n u).constr Z).symm) ≪≫ₗ
    (LinearEquiv.piCurry Z fun u (_ : Fin _) => zigzagProjective k G u).symm ≪≫ₗ
      (DirectSum.linearEquivFunOnFintype Z _ _).symm

private theorem termEquiv_apply (v : V) (n : ℕ) (f : ZigzagKoszulTerm k G v n)
    (s : TermIndex k G v n) :
    termEquiv k G v n f s = f s.1 (cornerBasis k G v n s.1 s.2) :=
  (rfl)

private theorem restrictScalars_termEquiv_symm_symm_apply (v : V) (n : ℕ)
    (f : ZigzagKoszulTerm k G v n) :
    ((termEquiv k G v n).symm.restrictScalars k).symm f = termEquiv k G v n f :=
  (rfl)

/-! ### The internal grading -/

/-- **The internal grading of the Koszul term** `K_n = ⨁_u Hom_k(e_u Π_n e_v, Z e_u)`: a map has
degree `p` when it takes values in degree `p - n` of the vertex projectives, so that `K_n` is the
direct sum of the shifted projectives `Z e_u{n}` tensored with the dual corners. -/
noncomputable def zigzagKoszulTermGrading (v : V) (n : ℕ) :
    InternalGrading k (ZigzagKoszulTerm k G v n) :=
  (InternalGrading.directSum fun s : TermIndex k G v n =>
    (zigzagGradedProjective k G s.1).grading.shift (-n)).map
    ((termEquiv k G v n).symm.restrictScalars k)

/-- A map in `K_n` has degree `p` exactly when all its values have degree `p - n`. -/
@[simp]
theorem mem_zigzagKoszulTermGrading_piece_iff {v : V} {n : ℕ} {p : ℤ}
    {f : ZigzagKoszulTerm k G v n} :
    f ∈ (zigzagKoszulTermGrading k G v n).piece p ↔
      ∀ (u : V) (y : C n (vertex G v) (vertex G u)),
        f u y ∈ zigzagProjectiveGrade k G u (p - n) := by
  have hpiece (u : V) : ((zigzagGradedProjective k G u).grading.shift (-n)).piece p =
      zigzagProjectiveGrade k G u (p - n) := by
    rw [InternalGrading.shift_piece, zigzagGradedProjective_piece, sub_eq_add_neg]
  rw [zigzagKoszulTermGrading, InternalGrading.mem_map_piece_iff, InternalGrading.directSum_piece,
    InternalGrading.mem_directSumPiece_iff]
  simp only [hpiece, restrictScalars_termEquiv_symm_symm_apply, termEquiv_apply]
  refine ⟨fun h u y => ?_, fun h s => h _ _⟩
  rw [← (cornerBasis k G v n u).sum_repr y, map_sum]
  exact Submodule.sum_mem _ fun i _ => by
    rw [map_smul]
    exact Submodule.smul_mem _ _ (h ⟨u, i⟩)

/-- The scalar action of the zigzag algebra on the Koszul terms, read off from their module
structure. Synthesizing it directly, through the actions on `Pi` types and on linear maps, exceeds
the default instance-search budget. -/
noncomputable local instance (v : V) (n : ℕ) : SMul Z (ZigzagKoszulTerm k G v n) :=
  (inferInstance : Module Z (ZigzagKoszulTerm k G v n)).toSMul

/-- The Koszul terms are graded modules over the path-length graded zigzag algebra. -/
instance (v : V) (n : ℕ) :
    SetLike.GradedSMul (zigzagIntegerGrade k G) (zigzagKoszulTermGrading k G v n).piece where
  smul_mem {i p} a f ha hf := by
    rw [mem_zigzagKoszulTermGrading_piece_iff] at hf ⊢
    intro u y
    have h := mul_mem_zigzagIntegerGrade k G ha ((mem_zigzagProjectiveGrade_iff k G).1 (hf u y))
    rw [vadd_eq_add, add_sub_assoc, mem_zigzagProjectiveGrade_iff, Pi.smul_apply,
      LinearMap.smul_apply, Submodule.coe_smul, smul_eq_mul]
    exact h

/-- The Koszul terms are projective modules over the zigzag algebra. -/
instance (v : V) (n : ℕ) : Module.Projective Z (ZigzagKoszulTerm k G v n) :=
  have := fun u => zigzagProjective_projective k G u
  Module.Projective.of_equiv (termEquiv k G v n).symm

/-- **The Koszul differential preserves internal degree.** -/
theorem isHomogeneous_zigzagKoszulDifferential (v : V) (n : ℕ) :
    LinearMap.IsHomogeneous (zigzagKoszulDifferential k G v n)
      (zigzagKoszulTermGrading k G v (n + 1)).piece (zigzagKoszulTermGrading k G v n).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p f hf
  rw [mem_zigzagKoszulTermGrading_piece_iff] at hf ⊢
  intro w y
  have hdeg : p + 0 - n = p - (n + 1 : ℕ) + 1 := by push_cast; ring
  rw [mem_zigzagProjectiveGrade_iff, coe_zigzagKoszulDifferential_apply, hdeg]
  exact Submodule.sum_mem _ fun j _ => mul_mem_zigzagIntegerGrade k G
    ((mem_zigzagProjectiveGrade_iff k G).1 (hf _ _))
    (zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G ⟨(w, j), (G.mem_neighborSet w j).1 j.2⟩)

/-- **The Koszul term `K_n` is generated in degree `n`**: it is a direct sum of shifted vertex
projectives `Z e_u{n}`, each generated by its vertex idempotent `e_u`. -/
theorem isGeneratedInDegree_zigzagKoszulTermGrading (v : V) (n : ℕ) :
    (zigzagKoszulTermGrading k G v n).IsGeneratedInDegree Z n := by
  rw [zigzagKoszulTermGrading, InternalGrading.isGeneratedInDegree_map_iff]
  refine InternalGrading.isGeneratedInDegree_directSum _ _ fun s => ?_
  rw [InternalGrading.isGeneratedInDegree_shift_iff, add_neg_cancel,
    InternalGrading.isGeneratedInDegree_iff]
  intro x
  -- `smul_spanSingletonGenerator` does not apply directly: `zigzagProjective` is not exposed as
  -- `Ideal.span {e_u}`, so the generator identity is read off from membership in `Z e_u`.
  have hx : (x : Z) • zigzagProjectiveGenerator k G s.1 = x := Subtype.ext (by
    rw [Submodule.coe_smul, coe_zigzagProjectiveGenerator, smul_eq_mul,
      (mem_zigzagProjective_iff k G).1 x.2])
  rw [← hx]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rw [zigzagGradedProjective_piece, SetLike.mem_coe, mem_zigzagProjectiveGrade_iff,
    coe_zigzagProjectiveGenerator]
  exact zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G s.1

/-! ### The augmentation -/

/-- The vertex idempotent `e_v`, as an element of the graded corner `e_v Π_0 e_v`. -/
private noncomputable def cornerVertex (v : V) : C 0 (vertex G v) (vertex G v) :=
  ⟨σ (vertexIdempotent k (vertex G v)),
    signlessPreprojectiveMk_vertexIdempotent_mem_signlessPreprojectiveCorner_zero k _⟩

/-- An element of `K_0` is determined by its value at the vertex idempotent `e_v`, since
`e_v Π_0 e_v` is the line of `e_v` and `e_u Π_0 e_v` vanishes for `u ≠ v`. -/
private theorem zigzagKoszulTerm_zero_ext {v : V} {f g : ZigzagKoszulTerm k G v 0}
    (h : f v (cornerVertex k G v) = g v (cornerVertex k G v)) : f = g := by
  funext u
  refine LinearMap.ext fun y => ?_
  rcases eq_or_ne v u with rfl | hvu
  · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
      ((signlessPreprojectiveCorner_zero_self_eq_span k (vertex G v)).le y.2)
    have hy : y = c • cornerVertex k G v := Subtype.ext hc.symm
    rw [hy, map_smul, map_smul, h]
  · have hy :=
      (signlessPreprojectiveCorner_zero_eq_bot_of_ne k ((vertex_injective G).ne hvu)).le y.2
    rw [Submodule.mem_bot] at hy
    have hy0 : y = 0 := Subtype.ext hy
    rw [hy0, map_zero, map_zero]

/-- **The augmentation** `K_0 → S_v` of the Koszul complex onto the graded simple module at `v`:
the class in the head of `Z e_v` of the value at the vertex idempotent `e_v ∈ e_v Π_0 e_v`. -/
noncomputable def zigzagKoszulAugmentation (v : V) :
    ZigzagKoszulTerm k G v 0 →ₗ[Z] zigzagGradedSimple k G v :=
  zigzagGradedSimpleMk k G v ∘ₗ (LinearEquiv.ofEq _ _ (zigzagProjective_def k G v)).toLinearMap ∘ₗ
    LinearMap.applyₗ' Z (cornerVertex k G v) ∘ₗ LinearMap.proj v

/-- The augmentation sends `f` to the class of `f_v (e_v)`. -/
theorem zigzagKoszulAugmentation_apply (v : V) (f : ZigzagKoszulTerm k G v 0) :
    zigzagKoszulAugmentation k G v f = zigzagGradedSimpleMk k G v
      ⟨(f v ⟨σ (vertexIdempotent k (vertex G v)),
          signlessPreprojectiveMk_vertexIdempotent_mem_signlessPreprojectiveCorner_zero k _⟩ : Z),
        by rw [← zigzagProjective_def]; exact SetLike.coe_mem _⟩ :=
  (rfl)

private theorem zigzagKoszulAugmentation_apply' (v : V) (f : ZigzagKoszulTerm k G v 0) :
    zigzagKoszulAugmentation k G v f = zigzagGradedSimpleMk k G v
      ⟨(f v (cornerVertex k G v) : Z), by rw [← zigzagProjective_def]; exact SetLike.coe_mem _⟩ :=
  (rfl)

/-- The value at `e_v` of the boundary of an element of `K_1`. -/
private noncomputable def boundaryValue (v : V) :
    ZigzagKoszulTerm k G v 1 →ₗ[Z] zigzagProjective k G v :=
  LinearMap.applyₗ' Z (cornerVertex k G v) ∘ₗ LinearMap.proj v ∘ₗ zigzagKoszulDifferential k G v 0

private theorem boundaryValue_apply (v : V) (g : ZigzagKoszulTerm k G v 1) :
    boundaryValue k G v g = zigzagKoszulDifferential k G v 0 g v (cornerVertex k G v) :=
  (rfl)

/-- **The augmentation preserves internal degree.** -/
theorem isHomogeneous_zigzagKoszulAugmentation (v : V) :
    LinearMap.IsHomogeneous (zigzagKoszulAugmentation k G v)
      (zigzagKoszulTermGrading k G v 0).piece (zigzagGradedSimple k G v).grading.piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p f hf
  rw [mem_zigzagKoszulTermGrading_piece_iff] at hf
  rw [zigzagKoszulAugmentation_apply, add_zero]
  refine zigzagGradedSimpleMk_mem_piece k G v _ ?_
  simpa using hf v _

/-- The value at `e_v` of a boundary `d g ∈ K_0` lies in `A₊ e_v`: it is a sum of right multiples
`z a_{vj}` of the arrows out of `v`. -/
private theorem coe_zigzagKoszulDifferential_cornerVertex_mem (v : V)
    (g : ZigzagKoszulTerm k G v 1) :
    (zigzagKoszulDifferential k G v 0 g v (cornerVertex k G v) : Z) ∈
      gradedPositiveMulIdeal (zigzagIntegerGrade k G) (zigzagVertexIdempotent k G v) := by
  rw [coe_zigzagKoszulDifferential_apply]
  refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ ?_
  rw [← zigzagMk_ofArrow_mul_vertexIdempotent k G ⟨(v, j), (G.mem_neighborSet v j).1 j.2⟩]
  exact mul_mem_gradedPositiveMulIdeal _ one_pos
    (zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _)

/-- **The augmentation kills the boundaries**: `K_1 → K_0 → S_v` composes to zero. -/
@[simp]
theorem zigzagKoszulAugmentation_comp_zigzagKoszulDifferential (v : V) :
    zigzagKoszulAugmentation k G v ∘ₗ zigzagKoszulDifferential k G v 0 = 0 := by
  refine LinearMap.ext fun g => ?_
  rw [LinearMap.comp_apply, zigzagKoszulAugmentation_apply, LinearMap.zero_apply,
    zigzagGradedSimpleMk_eq_zero_iff]
  exact coe_zigzagKoszulDifferential_cornerVertex_mem k G v g

/-- Every right multiple `z a_{vj}` of an arrow out of `v` is the value at `e_v` of a boundary. -/
private theorem exists_zigzagKoszulDifferential_eq_mul (v : V)
    (j : G.neighborSet v) (z : zigzagProjective k G j) :
    ∃ g : ZigzagKoszulTerm k G v 1,
      (zigzagKoszulDifferential k G v 0 g v (cornerVertex k G v) : Z) =
        (z : Z) * zigzagMk k G (ofArrow (arrow G ((G.mem_neighborSet v j).1 j.2))) := by
  classical
  let t : C 1 (vertex G v) (vertex G j) :=
    ⟨σ (ofArrow (arrow G ((G.mem_neighborSet v j).1 j.2))) * (cornerVertex k G v : Π),
      signlessPreprojectiveMk_ofArrow_mul_mem_signlessPreprojectiveCorner _ (cornerVertex k G v).2⟩
  have ht : t ≠ 0 := fun h => signlessPreprojectiveMk_ofArrow_ne_zero k
    (arrow G ((G.mem_neighborSet v j).1 j.2)) (by
      have h' : σ (ofArrow (arrow G ((G.mem_neighborSet v j).1 j.2))) *
          σ (vertexIdempotent k (vertex G v)) = 0 := congrArg Subtype.val h
      rwa [← map_mul, ofArrow_mul_vertexIdempotent] at h')
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k ht
  refine ⟨Pi.single (j : V) (φ.smulRight z), ?_⟩
  rw [coe_zigzagKoszulDifferential_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, LinearMap.smulRight_apply, hφ, one_smul]
  · intro l _ hl
    rw [Pi.single_eq_of_ne (Subtype.coe_injective.ne hl), LinearMap.zero_apply,
      ZeroMemClass.coe_zero, zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-- The values at `e_v` of the boundaries in `K_0`, together with the line of `e_v`, exhaust the
vertex projective `Z e_v`: the arrows out of `v` and the volume class at `v` are such values. -/
private theorem mem_sup_span_zigzagProjectiveGenerator (v : V) (x : zigzagProjective k G v) :
    x ∈ (LinearMap.range (boundaryValue k G v)).restrictScalars k ⊔
      k ∙ zigzagProjectiveGenerator k G v := by
  have hx : x ∈ Submodule.span k (Set.range (zigzagProjectiveBasisFun k G v)) := by
    rw [span_range_zigzagProjectiveBasisFun_eq_top]
    trivial
  refine Submodule.span_le.2 ?_ hx
  rintro _ ⟨b, rfl⟩
  rcases b with ⟨⟩ | ⟨⟨⟨a, j⟩, h⟩, rfl⟩ | e
  · refine Submodule.mem_sup_right (Submodule.mem_span_singleton.2 ⟨1, Subtype.ext ?_⟩)
    rw [one_smul, coe_zigzagProjectiveGenerator, coe_zigzagProjectiveBasisFun_inl]
  · obtain ⟨g, hg⟩ := exists_zigzagKoszulDifferential_eq_mul k G a ⟨j, (G.mem_neighborSet a j).2 h⟩
      (zigzagProjectiveGenerator k G j)
    refine Submodule.mem_sup_left ⟨g, Subtype.ext ?_⟩
    rw [boundaryValue_apply, hg, coe_zigzagProjectiveBasisFun_inr_inl,
      coe_zigzagProjectiveGenerator]
    exact zigzagMk_vertexIdempotent_mul_ofArrow k G ⟨(a, j), h⟩
  · rcases em (∃ j, G.Adj v j) with ⟨j, hj⟩ | hv
    swap
    · -- At an isolated vertex the volume class vanishes.
      have h0 : zigzagProjectiveBasisFun k G v (.inr (.inr e)) = 0 := Subtype.ext (by
        rw [coe_zigzagProjectiveBasisFun_inr_inr, ZeroMemClass.coe_zero,
          zigzagVolume_eq_zero_of_isIsolated k G fun j hj => hv ⟨j, hj⟩])
      rw [h0]
      exact Submodule.zero_mem _
    obtain ⟨g, hg⟩ := exists_zigzagKoszulDifferential_eq_mul k G v ⟨j, (G.mem_neighborSet v j).2 hj⟩
      ⟨zigzagMk k G (ofArrow (arrow G hj.symm)), (mem_zigzagProjective_iff k G).2
        (zigzagMk_ofArrow_mul_vertexIdempotent k G ⟨(j, v), hj.symm⟩)⟩
    refine Submodule.mem_sup_left ⟨g, Subtype.ext ?_⟩
    rw [boundaryValue_apply, hg, coe_zigzagProjectiveBasisFun_inr_inr]
    exact zigzagMk_ofArrow_mul_ofArrow_symm k G ⟨(j, v), hj.symm⟩

/-- **Exactness of the Koszul complex at `K_0`**: the kernel of the augmentation is the image of the
first differential. -/
theorem exact_zigzagKoszulDifferential_zigzagKoszulAugmentation (v : V) :
    Function.Exact (zigzagKoszulDifferential k G v 0) (zigzagKoszulAugmentation k G v) := by
  intro f
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨y, ⟨g, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1
      (mem_sup_span_zigzagProjectiveGenerator k G v (f v (cornerVertex k G v)))
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    -- The vertex coefficient `c` of `f_v (e_v)` vanishes: `c e_v` lies in `A₊ e_v`, which has no
    -- component in degree zero.
    have hmem : c • zigzagVertexIdempotent k G v ∈
        gradedPositiveMulIdeal (zigzagIntegerGrade k G) (zigzagVertexIdempotent k G v) := by
      have h1 := (zigzagGradedSimpleMk_eq_zero_iff k G v _).1
        ((zigzagKoszulAugmentation_apply' k G v f).symm.trans hf)
      have h2 := coe_zigzagKoszulDifferential_cornerVertex_mem k G v g
      have h3 := Ideal.sub_mem _ h1 h2
      rwa [← hyz, boundaryValue_apply, Submodule.coe_add, add_sub_cancel_left,
        Submodule.coe_smul_of_tower, coe_zigzagProjectiveGenerator] at h3
    have he := zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G v
    have h0 := decompose_eq_zero_of_mem_gradedPositiveMulIdeal
      (fun p hp => zigzagIntegerGrade_eq_bot_of_neg k G hp) he hmem le_rfl
    rw [DirectSum.decompose_of_mem_same _ (Submodule.smul_mem _ c he)] at h0
    have hc : c = 0 := (smul_eq_zero.1 h0).resolve_right (zigzagVertexIdempotent_ne_zero k G v)
    refine ⟨g, zigzagKoszulTerm_zero_ext k G ?_⟩
    rw [← hyz, hc, zero_smul, add_zero, boundaryValue_apply]
  · rintro ⟨g, rfl⟩
    exact LinearMap.congr_fun (zigzagKoszulAugmentation_comp_zigzagKoszulDifferential k G v) g

/-- **The augmentation is onto the graded simple module.** -/
theorem zigzagKoszulAugmentation_surjective (v : V) :
    Function.Surjective (zigzagKoszulAugmentation k G v) := by
  classical
  intro s
  obtain ⟨x, rfl⟩ := zigzagGradedSimpleMk_surjective k G v s
  have hne : cornerVertex k G v ≠ 0 := fun h =>
    signlessPreprojectiveMk_vertexIdempotent_ne_zero k (vertex G v) (congrArg Subtype.val h)
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one k hne
  let x' : zigzagProjective k G v := ⟨x, by rw [zigzagProjective_def]; exact x.2⟩
  have hx :
      (Pi.single v (ψ.smulRight x') : ZigzagKoszulTerm k G v 0) v (cornerVertex k G v) = x' := by
    rw [Pi.single_eq_same, LinearMap.smulRight_apply, hψ, one_smul]
  refine ⟨Pi.single v (ψ.smulRight x'), ?_⟩
  simp only [zigzagKoszulAugmentation_apply', hx, x']

/-! ### The linear Koszul resolution -/

section Resolution

variable (hinj : ∀ (w : V) (y : signlessPreprojectiveAlgebra k (DoubledQuiver G)),
  signlessPreprojectiveMk k _ (vertexIdempotent k (vertex G w)) * y = y →
    (∀ (i : DoubledQuiver G) (b : i ⟶ vertex G w),
      signlessPreprojectiveMk k _ (ofArrow (reverse b)) * y = 0) → y = 0)

include hinj in
/-- **The Koszul resolution of a graded simple zigzag module.** Let `G` be a finite graph such
that the Koszul complex `0 → e_w Π → ⨁_{j ∼ w} e_j Π` of the signless preprojective algebra `Π` is
exact at its left end at every vertex `w`. Then the Koszul complex `K` of the graded simple module
`S_v` of the zigzag algebra, with its augmentation `K_0 → S_v`, is a graded projective resolution
of `S_v`.

This is an abbreviation so that the types and module instances of its terms are those of
`TauCeti.ZigzagKoszulTerm`; its data are computed by the `[simp]` lemmas below. -/
noncomputable abbrev zigzagKoszulResolution (v : V) :
    GradedProjectiveResolution (zigzagIntegerGrade k G) (zigzagGradedSimple k G v).grading where
  X := ZigzagKoszulTerm k G v
  grading := zigzagKoszulTermGrading k G v
  projective _ := inferInstance
  d := zigzagKoszulDifferential k G v
  π := zigzagKoszulAugmentation k G v
  isHomogeneous_d := isHomogeneous_zigzagKoszulDifferential k G v
  isHomogeneous_π := isHomogeneous_zigzagKoszulAugmentation k G v
  surjective_π := zigzagKoszulAugmentation_surjective k G v
  exact_d_π := exact_zigzagKoszulDifferential_zigzagKoszulAugmentation k G v
  exact_d_d n := LinearMap.exact_iff.2 (range_zigzagKoszulDifferential_eq_ker k G hinj v n).symm

/-- The terms of the Koszul resolution are the Koszul terms. -/
@[simp]
theorem zigzagKoszulResolution_X (v : V) (n : ℕ) :
    (zigzagKoszulResolution k G hinj v).X n = ZigzagKoszulTerm k G v n :=
  (rfl)

/-- The terms of the Koszul resolution carry the gradings `TauCeti.zigzagKoszulTermGrading`. -/
@[simp]
theorem zigzagKoszulResolution_grading (v : V) (n : ℕ) :
    (zigzagKoszulResolution k G hinj v).grading n = zigzagKoszulTermGrading k G v n :=
  (rfl)

/-- The differentials of the Koszul resolution are the Koszul differentials. -/
@[simp]
theorem zigzagKoszulResolution_d (v : V) (n : ℕ) :
    (zigzagKoszulResolution k G hinj v).d n = zigzagKoszulDifferential k G v n :=
  (rfl)

/-- The augmentation of the Koszul resolution is `TauCeti.zigzagKoszulAugmentation`. -/
@[simp]
theorem zigzagKoszulResolution_π (v : V) :
    (zigzagKoszulResolution k G hinj v).π = zigzagKoszulAugmentation k G v :=
  (rfl)

/-- **The Koszul resolution is linear**: its term in homological degree `n` is generated in
internal degree `n`. -/
theorem isLinear_zigzagKoszulResolution (v : V) : (zigzagKoszulResolution k G hinj v).IsLinear :=
  GradedProjectiveResolution.isLinear_iff.2 (isGeneratedInDegree_zigzagKoszulTermGrading k G v)

end Resolution

omit [Fintype V] [DecidableRel G.Adj] in
variable {G} in
/-- **The vertex simple modules of the zigzag algebra of a connected graph which is not a tree have
linear resolutions**: the simple module `S_v`, concentrated in degree zero, has the linear
resolution `TauCeti.zigzagKoszulResolution`, since a non-backtracking choice of neighbours makes the
signless Koszul complexes exact at their left ends. Its grading shifts have the correspondingly
shifted resolutions. Such a graph is never a finite ADE Dynkin diagram. -/
theorem exists_isLinear_gradedProjectiveResolution_zigzagGradedSimple_of_not_isAcyclic [Finite V]
    (hG : G.Preconnected) (hc : ¬G.IsAcyclic) (v : V) :
    ∃ r : GradedProjectiveResolution.{w, max u w, max u w, max u w} (zigzagIntegerGrade k G)
      (zigzagGradedSimple k G v).grading, r.IsLinear := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨f, hf⟩ := hG.exists_forall_adj_and_apply_apply_ne_of_not_isAcyclic hc
  have hinj (w : V) (y : Π) (hy : σ (vertexIdempotent k (vertex G w)) * y = y)
      (h : ∀ (i : DoubledQuiver G) (b : i ⟶ vertex G w), σ (ofArrow (reverse b)) * y = 0) :
      y = 0 :=
    (forall_signlessPreprojectiveMk_ofArrow_reverse_mul_eq_zero_iff_of_adj k
      (fun u => (hf u).1) (fun u => (hf u).2) w hy).1 h
  exact ⟨zigzagKoszulResolution k G hinj v, isLinear_zigzagKoszulResolution k G hinj v⟩

end TauCeti
