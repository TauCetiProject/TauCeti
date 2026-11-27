/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.Projective
public import TauCeti.Algebra.Module.GradedModule.Generated

/-!
# Graded free modules and projective presentations

A free graded module with basis degrees `d : I → ℤ` is the direct sum of copies of the regular
module using the internal grading shift `-d i`, equivalently the categorical shift
`shiftObj (d i)`, so basis vector `i` has degree `d i`.
Its degree-`p` elements have coordinate `i` in `𝒜 (p - d i)`.
Maps out of it are uniquely determined by the images of its homogeneous basis vectors. In rank
one, maps out of the shifted regular module `A{n}` are the degree-`n` elements of the target, and
`A{n}` is generated in degree `n`, and over a nonnegatively graded algebra in no other degree.

Every graded module is a quotient of such a free graded module: use all homogeneous elements as
generators. If the underlying module is finitely generated, finitely many homogeneous elements
suffice, so the free source can be chosen finitely generated. These presentations provide the
projective terms needed to construct graded resolutions; they do not assert minimality.
Over a left Noetherian algebra, the kernel is again finitely generated, giving a two-term
presentation by finite graded free modules.

Homogeneous `A`-bases of a graded `A`-module `M` correspond to isomorphisms `free 𝒜 d ≅ M` in
`GradedModuleCat 𝒜` (`Module.Basis.isoGradedFree` and `CategoryTheory.Iso.homogeneousBasis`).
Over a nonnegatively graded algebra (`∀ i < 0, 𝒜 i = ⊥`), any finitely generated shifted free
graded module is bounded below (`TauCeti.GradedModuleCat.exists_piece_eq_bot_of_lt_free`).

No positivity, semisimplicity, or finite-dimensionality assumption on the graded algebra is needed
for the universal property, homogeneous-basis correspondence, or projective presentations; only
`exists_piece_eq_bot_of_lt_free` assumes nonnegativity (`∀ i < 0, 𝒜 i = ⊥`).

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

universe uk uA v uI

namespace TauCeti.GradedModuleCat

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

/-- Every element of `free 𝒜 d` is the sum over its support of its coordinates times the
corresponding free generators. -/
theorem eq_sum_support_smul_freeGenerator [DecidableEq I] [DecidableEq A] (x : free 𝒜 d) :
    x = ∑ j ∈ x.support, x j • freeGenerator (𝒜 := 𝒜) (d := d) j := by
  conv_lhs => rw [← DirectSum.sum_support_of x]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [freeGenerator_eq_lof, ← LinearMap.map_smul, smul_eq_mul, mul_one, DirectSum.lof_eq_of]

/-- The basis vector indexed by `i` has internal degree `d i`. -/
theorem freeGenerator_mem_free_piece (i : I) : freeGenerator (𝒜 := 𝒜) (d := d) i ∈
    (free 𝒜 d).grading.piece (d i) := by
  classical
  rw [freeGenerator_eq_lof, InternalGrading.directSum_piece]
  exact InternalGrading.lof_mem_directSumPiece _ (d i) i
    ⟨1, by simpa using SetLike.one_mem_graded 𝒜⟩

/-- The basis vector indexed by `i` has internal degree `q` whenever `d i = q`. -/
theorem freeGenerator_mem_free_piece_of_eq {q : ℤ} {i : I} (h : d i = q) :
    freeGenerator (𝒜 := 𝒜) (d := d) i ∈ (free 𝒜 d).grading.piece q :=
  h ▸ freeGenerator_mem_free_piece i

/-- Extend a family of homogeneous elements to a morphism out of the graded free module. -/
def freeLift {M : GradedModuleCat.{max uA uI} 𝒜} (x : ∀ i, M.grading.piece (d i)) :
    free 𝒜 d ⟶ M := by
  classical
  refine ofHom (DirectSum.toModule A I M fun i => LinearMap.toSpanSingleton A M (x i : M))
    (LinearMap.isHomogeneous_def.mpr fun p y hy => ?_)
  refine InternalGrading.toModule_mem_of_mem_directSumPiece _ M.grading.piece _
    (fun i z hz => ?_) (by simpa only [InternalGrading.directSum_piece] using hy)
  have hz' : z ∈ 𝒜 (p - d i) := by simpa [sub_eq_add_neg] using hz
  rw [LinearMap.toSpanSingleton_apply]
  simpa using SetLike.GradedSMul.smul_mem hz' (x i).property

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
    freeLift x ≫ g = freeLift (fun i => ⟨g.hom (x i), map_mem g (x i).property⟩) := by
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

/-- The rank-one universal property: maps from the shifted regular module `A{n}` are the elements
of degree `n` of the target, by evaluation at `1`. -/
def regularShiftHomEquiv (M : GradedModuleCat.{uA} 𝒜) (n : ℤ) :
    ((regular (𝒜 := 𝒜)).shiftObj n ⟶ M) ≃ₗ[k] M.grading.piece n where
  toFun f := ⟨f.hom 1, map_mem f (by simpa using SetLike.one_mem_graded 𝒜)⟩
  invFun m := ofHom (LinearMap.toSpanSingleton A M m) <|
    LinearMap.isHomogeneous_def.2 fun p x hx => by
      have hx' : x ∈ 𝒜 (p - n) := by simpa [sub_eq_add_neg] using hx
      simpa using SetLike.GradedSMul.smul_mem hx' m.property
  left_inv f := hom_ext (LinearMap.ext_ring (by simp))
  right_inv m := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)
  map_smul' c f := Subtype.ext (by simp)

/-- The rank-one universal property evaluates a map at `1`. -/
@[simp]
theorem regularShiftHomEquiv_apply_coe (M : GradedModuleCat.{uA} 𝒜) (n : ℤ)
    (f : (regular (𝒜 := 𝒜)).shiftObj n ⟶ M) :
    (regularShiftHomEquiv M n f : M) = f.hom 1 :=
  (rfl)

/-- The inverse rank-one universal property sends `m` to the map `a ↦ a • m`. -/
@[simp]
theorem hom_regularShiftHomEquiv_symm_apply (M : GradedModuleCat.{uA} 𝒜) (n : ℤ)
    (m : M.grading.piece n) :
    ((regularShiftHomEquiv M n).symm m).hom = LinearMap.toSpanSingleton A M m :=
  (rfl)

/-- The element `1` of the shifted regular module `A{n}` has degree `n`. -/
theorem one_mem_regular_shiftObj_piece (n : ℤ) :
    (1 : A) ∈ ((regular (𝒜 := 𝒜)).shiftObj n).grading.piece n := by
  simpa using SetLike.one_mem_graded 𝒜

/-- The shifted regular module `A{n}` is generated in degree `n`, by the element `1`. -/
theorem isGeneratedInDegree_regular_shiftObj (n : ℤ) :
    ((regular (𝒜 := 𝒜)).shiftObj n).grading.IsGeneratedInDegree A n := by
  refine (InternalGrading.isGeneratedInDegree_iff _ _).2 fun x ↦ ?_
  simpa using Submodule.smul_mem _ x
    (Submodule.subset_span (one_mem_regular_shiftObj_piece (𝒜 := 𝒜) n))

/-- **Over a nonnegatively graded nontrivial algebra, `A{n}` is generated in degree `d` exactly
when `d = n`**: below `n` its pieces vanish, and above `n` they miss the generator `1`. -/
theorem isGeneratedInDegree_regular_shiftObj_iff [Nontrivial A] (h𝒜 : ∀ i < 0, 𝒜 i = ⊥)
    (n d : ℤ) :
    ((regular (𝒜 := 𝒜)).shiftObj n).grading.IsGeneratedInDegree A d ↔ d = n := by
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; exact isGeneratedInDegree_regular_shiftObj d⟩
  have h1 := one_mem_regular_shiftObj_piece (𝒜 := 𝒜) n
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- the degree-`d` piece is `𝒜 (d - n) = 0`, which generates nothing
    have hbot : ((regular (𝒜 := 𝒜)).shiftObj n).grading.piece d = ⊥ := by
      simpa [sub_eq_add_neg] using h𝒜 (d - n) (by omega)
    have h1' := (InternalGrading.isGeneratedInDegree_iff _ _).1 h 1
    rw [hbot, Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h1'
    exact one_ne_zero h1'
  · -- generation in degree `d > n` kills the degree-`n` piece, which contains `1`
    -- `piece_eq_bot_of_lt` needs the `GradedSMul` instance of `A{n}` for its scalar action
    have := ((regular (𝒜 := 𝒜)).shiftObj n).gradedSMul
    rw [h.piece_eq_bot_of_lt 𝒜 h𝒜 hgt, Submodule.mem_bot] at h1
    exact one_ne_zero h1

/-! ### Presentations -/

/-- Under `finsuppLequivDFinsupp`, `freeLift x` is
`Finsupp.linearCombination A (fun i => (x i : M))`. -/
private theorem hom_freeLift_comp_finsuppLequivDFinsupp [DecidableEq I]
    [∀ m : A, Decidable (m ≠ 0)] {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) :
    (freeLift x).hom.comp (finsuppLequivDFinsupp A).toLinearMap =
      Finsupp.linearCombination A (fun i => (x i : M)) := by
  apply Finsupp.lhom_ext
  intro i a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe,
    finsuppLequivDFinsupp_apply_apply, Function.comp_apply,
    Finsupp.toDFinsupp_single, Finsupp.linearCombination_single,
    DirectSum.single_eq_lof A]
  exact freeLift_lof x i a

/-- A graded free map is surjective exactly when its homogeneous basis images generate. -/
theorem freeLift_surjective_iff {M : GradedModuleCat.{max uA uI} 𝒜}
    (x : ∀ i, M.grading.piece (d i)) :
    Function.Surjective (freeLift x).hom ↔
      Submodule.span A (Set.range fun i => (x i : M)) = ⊤ := by
  classical
  rw [← LinearMap.range_eq_top, ← (finsuppLequivDFinsupp A).range_comp,
    hom_freeLift_comp_finsuppLequivDFinsupp x, Finsupp.range_linearCombination]

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
  obtain ⟨s, hs, hspan⟩ := M.grading.exists_finset_span_eq_top A
  choose d hd using fun i : s => hs i i.property
  let x : ∀ i : s, M.grading.piece (d i) := fun i => ⟨i, hd i⟩
  refine ⟨s, inferInstance, d, freeLift x, (freeLift_surjective_iff x).mpr ?_⟩
  have hrange : (Set.range fun i : s => (x i : M)) = (s : Set M) := by
    ext y
    simp [x]
  rw [hrange, hspan]

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

/-! ### Boundedness below -/

/-- Over a nonnegatively graded algebra, a finitely generated shifted free graded module is
bounded below. -/
theorem exists_piece_eq_bot_of_lt_free {I : Type uI} [Finite I] (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (s : I → ℤ) : ∃ b : ℤ, ∀ p < b, (free 𝒜 s).grading.piece p = ⊥ := by
  cases nonempty_fintype I
  obtain ⟨b, hb⟩ := (Finset.univ.image s).bddBelow
  refine ⟨b, fun p hp ↦ (Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_⟩
  ext j
  have hsb : b ≤ s j := hb (Finset.mem_image_of_mem s (Finset.mem_univ j))
  have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
  rw [hneg (p - s j) (by omega), Submodule.mem_bot] at hxj
  simpa using hxj

end TauCeti.GradedModuleCat

/-! ### Correspondence with homogeneous bases -/

namespace Module.Basis

open TauCeti TauCeti.GradedModuleCat

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

private theorem isIso_freeLift_of_basis {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (b : Module.Basis I A M)
    (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    IsIso (freeLift (fun i ↦ (⟨b i, hb i⟩ : M.grading.piece (d i)))) := by
  classical
  let x : ∀ i, M.grading.piece (d i) := fun i ↦ ⟨b i, hb i⟩
  have hfun : ((freeLift x).hom ∘ ⇑(finsuppLequivDFinsupp A)) = ⇑b.repr.symm := funext fun v ↦
    (LinearMap.congr_fun (hom_freeLift_comp_finsuppLequivDFinsupp x) v).trans
      (b.repr_symm_apply v).symm
  have hbij : Function.Bijective (freeLift x).hom := by
    rw [← (finsuppLequivDFinsupp A).bijective.of_comp_iff, hfun]
    exact b.repr.symm.bijective
  exact (isIso_iff_bijective (freeLift x)).mpr hbij

/-- An `A`-basis of `M` consisting of homogeneous elements of degrees `d` induces an isomorphism
`free 𝒜 d ≅ M` in `GradedModuleCat 𝒜`. -/
def isoGradedFree {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) : free 𝒜 d ≅ M :=
  haveI := isIso_freeLift_of_basis b hb
  asIso (freeLift (fun i ↦ (⟨b i, hb i⟩ : M.grading.piece (d i))))

/-- The forward morphism of `b.isoGradedFree hb` is `freeLift`. -/
theorem hom_isoGradedFree {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (b : Module.Basis I A M) (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    (b.isoGradedFree hb).hom = freeLift (fun i ↦ (⟨b i, hb i⟩ : M.grading.piece (d i))) := by
  rw [isoGradedFree]
  rfl

/-- `b.isoGradedFree hb` sends the `i`th free generator to `b i`. -/
@[simp]
theorem isoGradedFree_hom_freeGenerator {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (b : Module.Basis I A M)
    (hb : ∀ i, b i ∈ M.grading.piece (d i)) (i : I) :
    (b.isoGradedFree hb).hom.hom (freeGenerator i) = b i := by
  rw [hom_isoGradedFree, freeLift_generator]

end Module.Basis

namespace CategoryTheory.Iso

open TauCeti TauCeti.GradedModuleCat

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Conversely, an isomorphism `free 𝒜 d ≅ M` in `GradedModuleCat 𝒜` equips `M` with an `A`-basis
whose `i`th vector is the image of `freeGenerator i` in degree `d i`. -/
def homogeneousBasis {I : Type uI} {d : I → ℤ} {M : GradedModuleCat.{max uA uI} 𝒜}
    (Φ : free 𝒜 d ≅ M) : Module.Basis I A M := by
  classical
  exact (Finsupp.basisSingleOne (ι := I) (R := A)).map
    ((finsuppLequivDFinsupp A).trans (toModuleCat.mapIso Φ).toLinearEquiv)

/-- The `i`th basis vector of `Φ.homogeneousBasis` is `Φ.hom.hom (freeGenerator i)`. -/
@[simp]
theorem homogeneousBasis_apply {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (Φ : free 𝒜 d ≅ M) (i : I) :
    Φ.homogeneousBasis i = Φ.hom.hom (freeGenerator i) := by
  classical
  rw [homogeneousBasis, Module.Basis.map_apply, Finsupp.coe_basisSingleOne]
  dsimp only
  -- `(toModuleCat.mapIso Φ).toLinearEquiv` is typed over `↑(toModuleCat.obj (free 𝒜 d))` rather
  -- than `Π₀ _ : I, A`, so `change` aligns those representations to unfold `LinearEquiv.trans`.
  change (toModuleCat.mapIso Φ).toLinearEquiv
    (finsuppLequivDFinsupp A (Finsupp.single i 1)) = Φ.hom.hom (freeGenerator i)
  rw [finsuppLequivDFinsupp_apply_apply, Finsupp.toDFinsupp_single, DirectSum.single_eq_lof A,
    ← freeGenerator_eq_lof (𝒜 := 𝒜) (d := d)]
  rfl

/-- The `i`th vector of `Φ.homogeneousBasis` is homogeneous of degree `d i`. -/
theorem homogeneousBasis_mem_piece {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (Φ : free 𝒜 d ≅ M) (i : I) :
    Φ.homogeneousBasis i ∈ M.grading.piece (d i) := by
  rw [homogeneousBasis_apply]
  exact map_mem Φ.hom (freeGenerator_mem_free_piece i)

/-- Converting a homogeneous `A`-basis to an isomorphism and back recovers the original basis. -/
@[simp]
theorem homogeneousBasis_isoGradedFree {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (b : Module.Basis I A M)
    (hb : ∀ i, b i ∈ M.grading.piece (d i)) :
    (b.isoGradedFree hb).homogeneousBasis = b := by
  ext i
  rw [homogeneousBasis_apply, Module.Basis.isoGradedFree_hom_freeGenerator]

/-- Converting an isomorphism `free 𝒜 d ≅ M` to its homogeneous basis and back recovers the
original isomorphism. -/
@[simp]
theorem _root_.Module.Basis.isoGradedFree_homogeneousBasis {I : Type uI} {d : I → ℤ}
    {M : GradedModuleCat.{max uA uI} 𝒜} (Φ : free 𝒜 d ≅ M) :
    Φ.homogeneousBasis.isoGradedFree Φ.homogeneousBasis_mem_piece = Φ := by
  ext i
  rw [Module.Basis.isoGradedFree_hom_freeGenerator, homogeneousBasis_apply]

end CategoryTheory.Iso
