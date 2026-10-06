/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Projective

/-!
# Graded free modules and projective presentations

A free graded module with basis degrees `d : I → ℤ` is the direct sum of copies of the regular
module using the internal grading shift `-d i`, equivalently the categorical shift
`shiftObj (d i)`, so basis vector `i` has degree `d i`.
Its degree-`p` elements have coordinate `i` in `𝒜 (p - d i)`.
Maps out of it are uniquely determined by the images of its homogeneous basis vectors.

Every graded module is a quotient of such a free graded module: use all homogeneous elements as
generators. If the underlying module is finitely generated, finitely many homogeneous elements
suffice, so the free source can be chosen finitely generated. These presentations provide the
projective terms needed to construct graded resolutions; they do not assert minimality.
Over a left Noetherian algebra, the kernel is again finitely generated, giving a two-term
presentation by finite graded free modules.

No positivity, semisimplicity, or finite-dimensionality assumption on the graded algebra is needed.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3,
  for graded free modules and projective presentations.

The construction uses `InternalGrading.directSum` and Mathlib's direct-sum universal property.
The free object is an abbreviation with a concrete carrier. Its computation lemmas normalize
projections with `dsimp% only` so that they still match after the simplifier reduces that carrier.
-/

public section

noncomputable section

open CategoryTheory
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v uI

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
  {I : Type uI} (d : I → ℤ)

/-- The free graded module with basis indexed by `I` and basis vector `i` in degree `d i`.
The abbreviation retains the concrete direct-sum carrier for computations with generators. -/
abbrev free : GradedModuleCat.{max uA uI} 𝒜 :=
  directSumObj fun i => (regular (𝒜 := 𝒜)).shiftObj (d i)

/-- `x` lies in the degree-`p` piece exactly when its `i`-th coordinate lies in `𝒜 (p - d i)`.
This is not a simp lemma: the direct-sum and shift simp lemmas already simplify its left side. -/
theorem mem_free_piece_iff (p : ℤ) (x : free 𝒜 d) :
    dsimp% only (x ∈ (free 𝒜 d).grading.piece p) ↔ ∀ i, x i ∈ 𝒜 (p - d i) := by
  simp only [InternalGrading.directSum_piece, InternalGrading.mem_directSumPiece_iff,
    InternalGrading.shift_piece, InternalGrading.ofDecomposition_piece, sub_eq_add_neg]

variable {𝒜 d}

/-- The homogeneous basis vector indexed by `i`. -/
def freeGenerator (i : I) : free 𝒜 d := by
  classical
  exact DirectSum.of (fun _ : I => A) i 1

/-- The coordinates of a homogeneous basis vector. -/
@[simp]
theorem freeGenerator_apply [DecidableEq I] (i j : I) :
    freeGenerator (𝒜 := 𝒜) (d := d) i j = if i = j then 1 else 0 := by
  classical
  simp [freeGenerator, DirectSum.of_apply]

/-- The homogeneous basis vector is the canonical inclusion of `1` from its summand. -/
theorem freeGenerator_eq_lof [DecidableEq I] (i : I) :
    freeGenerator (𝒜 := 𝒜) (d := d) i = DirectSum.lof A I (fun _ => A) i 1 := by
  classical
  ext j
  simp [freeGenerator, DirectSum.lof_eq_of, DirectSum.of_apply]

/-- The basis vector indexed by `i` has internal degree `d i`. -/
theorem freeGenerator_mem_free_piece (i : I) : freeGenerator (𝒜 := 𝒜) (d := d) i ∈
    (free 𝒜 d).grading.piece (d i) := by
  classical
  rw [freeGenerator_eq_lof, InternalGrading.directSum_piece]
  exact InternalGrading.lof_mem_directSumPiece _ (d i) i
    ⟨1, by simpa using SetLike.one_mem_graded 𝒜⟩

/-- Extend a family of homogeneous elements to a morphism out of the graded free module. -/
def freeLift {M : GradedModuleCat.{max uA uI} 𝒜} (x : ∀ i, M.grading.piece (d i)) :
    free 𝒜 d ⟶ M := by
  classical
  let f := DirectSum.toModule A I M fun i => LinearMap.toSpanSingleton A M (x i : M)
  refine ofHom f (LinearMap.isHomogeneous_def.mpr fun p y hy => ?_)
  have hy' := (mem_free_piece_iff 𝒜 d p y).mp hy
  rw [← DFinsupp.sum_single (f := y), DFinsupp.sum] at ⊢
  rw [map_sum]
  refine (M.grading.piece (p + 0)).sum_mem fun i _ => ?_
  dsimp only [f]
  rw [DirectSum.single_eq_lof A, DirectSum.toModule_lof, LinearMap.toSpanSingleton_apply]
  simpa using SetLike.GradedSMul.smul_mem (hy' i) (x i).property

/-- The underlying linear map of extension is the direct-sum universal map. -/
@[simp]
theorem hom_freeLift {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) [hI : DecidableEq I] :
    (freeLift x).hom =
      DirectSum.toModule A I M (fun i => LinearMap.toSpanSingleton A M (x i : M)) := by
  cases Subsingleton.elim hI (Classical.decEq I)
  rfl

/-- Extension on a summand is scalar multiplication by its prescribed basis image. -/
theorem freeLift_lof {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) [hI : DecidableEq I] (i : I) (a : A) :
    (freeLift x).hom (DirectSum.lof A I (fun _ => A) i a) = a • (x i : M) := by
  rw [hom_freeLift (hI := hI), DirectSum.toModule_lof, LinearMap.toSpanSingleton_apply]

/-- The extension evaluates to the prescribed image on each basis vector. -/
@[simp]
theorem freeLift_generator {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) (i : I) :
    dsimp% only ((freeLift x).hom (freeGenerator (𝒜 := 𝒜) i)) = (x i : M) := by
  classical
  rw [freeGenerator_eq_lof, freeLift_lof, one_smul]

/-- Morphisms out of a free graded module agree if they agree on its homogeneous basis. -/
@[ext]
theorem free_hom_ext {M : GradedModuleCat.{max uA uI} 𝒜} {f g : free 𝒜 d ⟶ M}
    (h : ∀ i, f.hom (freeGenerator i) = g.hom (freeGenerator i)) : f = g := by
  classical
  apply hom_ext
  apply DirectSum.linearMap_ext
  intro i
  exact LinearMap.ext_ring (by simpa only [freeGenerator_eq_lof, LinearMap.comp_apply] using h i)

/-- Postcomposing extension extends the postcomposed homogeneous basis images. -/
@[simp]
theorem freeLift_comp {M N : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) (g : M ⟶ N) :
    freeLift x ≫ g = freeLift (fun i => ⟨g.hom (x i), map_mem g (x i).2⟩) := by
  apply free_hom_ext
  intro i
  simp only [hom_comp, LinearMap.comp_apply, freeLift_generator]

/-- The linear universal property: maps from a graded free module are families of elements in its
specified basis degrees. -/
def freeHomEquiv (M : GradedModuleCat.{max uA uI} 𝒜) :
    (free 𝒜 d ⟶ M) ≃ₗ[k] (∀ i, M.grading.piece (d i)) where
  toFun f i := ⟨f.hom (freeGenerator i), map_mem f (freeGenerator_mem_free_piece i)⟩
  invFun := freeLift
  left_inv _ := free_hom_ext fun i => freeLift_generator _ i
  right_inv x := funext fun i => Subtype.ext (freeLift_generator x i)
  map_add' f g := funext fun i => Subtype.ext (by simp)
  map_smul' a f := funext fun i => Subtype.ext (by simp)

/-- The free-module universal property reads off the basis images. -/
@[simp]
theorem freeHomEquiv_apply_coe (M : GradedModuleCat.{max uA uI} 𝒜) (f : free 𝒜 d ⟶ M) (i : I) :
    (freeHomEquiv M f i : M) = f.hom (freeGenerator i) :=
  (rfl)

/-- The inverse universal-property map is extension from the basis images. -/
@[simp]
theorem freeHomEquiv_symm_apply (M : GradedModuleCat.{max uA uI} 𝒜)
    (x : ∀ i, M.grading.piece (d i)) : (freeHomEquiv M).symm x = freeLift x :=
  (rfl)

/-! ### Presentations -/

/-- A graded free map is surjective exactly when its homogeneous basis images generate. -/
theorem freeLift_surjective_iff {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) :
    Function.Surjective (freeLift x).hom ↔
      Submodule.span A (Set.range fun i => (x i : M)) = ⊤ := by
  classical
  have hcomp : (freeLift x).hom.comp (finsuppLequivDFinsupp A).toLinearMap =
      Finsupp.linearCombination A (fun i => (x i : M)) := by
    apply Finsupp.lhom_ext
    intro i a
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
      finsuppLequivDFinsupp_apply_apply, Function.comp_apply,
      Finsupp.toDFinsupp_single, Finsupp.linearCombination_single,
      DirectSum.single_eq_lof A]
    exact freeLift_lof x i a
  rw [← LinearMap.range_eq_top, ← (finsuppLequivDFinsupp A).range_comp, hcomp,
    Finsupp.range_linearCombination]

/-- Every graded module admits a projective presentation by a graded free module. -/
instance enoughProjectives : EnoughProjectives (GradedModuleCat.{max uA v} 𝒜) where
  presentation M := by
    let I := Σ p : ℤ, M.grading.piece p
    let d : I → ℤ := Sigma.fst
    let x : ∀ i : I, M.grading.piece (d i) := Sigma.snd
    have hrange : (Set.range fun i : I => (x i : M)) =
        {y : M | ∃ p, y ∈ M.grading.piece p} := by
      ext y
      simp [I, d, x]
    have hspan : Submodule.span A (Set.range fun i : I => (x i : M)) = ⊤ := by
      rw [hrange, M.grading.span_setOf_exists_mem_piece_eq_top A]
    have hepi : Epi (freeLift x) := (epi_iff_surjective _).mpr
      ((freeLift_surjective_iff x).mpr hspan)
    exact ⟨{ p := free 𝒜 d, f := freeLift x }⟩

/-- A finitely generated graded module admits a surjection from a finitely generated graded
free module. The homogeneous generating set, and hence the free presentation, need not be
minimal. -/
theorem exists_finite_free_surjection (M : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A M] :
    ∃ (I : Type (max uA v)) (_ : Finite I) (d : I → ℤ) (f : free 𝒜 d ⟶ M),
      Function.Surjective f.hom := by
  let S : Set M := {x | ∃ p, x ∈ M.grading.piece p}
  have hspan : Submodule.span A S = ⊤ := M.grading.span_setOf_exists_mem_piece_eq_top A
  obtain ⟨s, hs, h⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).mp
    (hspan.symm ▸ Module.Finite.fg_top)
  have hdeg : ∀ i : s, ∃ p, (i : M) ∈ M.grading.piece p := fun i => hs i.property
  choose d hd using hdeg
  let x : ∀ i : s, M.grading.piece (d i) := fun i => ⟨i, hd i⟩
  refine ⟨s, inferInstance, d, freeLift x, (freeLift_surjective_iff x).mpr ?_⟩
  have hrange : (Set.range fun i : s => (x i : M)) = (s : Set M) := by
    ext y
    simp [x]
  rw [hrange, ← h, hspan]

/-- Over a left Noetherian algebra, a finitely generated graded module admits a two-term
presentation by finite graded free modules. Both maps preserve the internal grading. -/
theorem exists_finite_free_presentation [IsNoetherianRing A]
    (M : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A M] :
    ∃ (I J : Type (max uA v)) (_ : Finite I) (_ : Finite J)
      (d : I → ℤ) (e : J → ℤ) (g : free 𝒜 e ⟶ free 𝒜 d) (f : free 𝒜 d ⟶ M),
      Function.Exact g.hom f.hom ∧ Function.Surjective f.hom := by
  obtain ⟨I, hI, d, f, hf⟩ := exists_finite_free_surjection M
  let : Finite I := hI
  have : Module.Finite A (kernelObj f) :=
    inferInstanceAs (Module.Finite A (LinearMap.ker f.hom))
  obtain ⟨J, hJ, e, g, hg⟩ := exists_finite_free_surjection (kernelObj f)
  refine ⟨I, J, hI, hJ, d, e, g ≫ kernelι f, f, ?_, hf⟩
  rw [hom_comp, hom_kernelι]
  exact hg.comp_exact_iff_exact.mpr (LinearMap.exact_subtype_ker_map f.hom)

end TauCeti.GradedModuleCat
