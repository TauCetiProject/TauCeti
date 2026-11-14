/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
public import TauCeti.Algebra.Category.GradedModuleCat.DegreeQuotient
public import TauCeti.Algebra.Category.GradedModuleCat.Free
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Homogeneous bases of projective graded modules and graded idempotent retracts

Let `A` be a nonnegatively `ℤ`-graded algebra (`𝒜 i = ⊥` for `i < 0`). Reducing a graded `A`-module
`M` to its universal degree-`p` quotient `M.degreeQuotient p` kills all pieces outside degree `p`,
and in degree `p` kills `A₊ M`. For a graded free module `⨁ᵢ A{dᵢ}`, this quotient is the free
`𝒜 0`-module on the basis indices of degree `p`.

When `P` is projective in `GradedModuleCat 𝒜`, graded Nakayama upgrades degreewise invertibility on
degree quotients to a graded isomorphism:

* if all degree quotients of a projective graded module `P` below degree `b` vanish, then `P`
  itself vanishes below degree `b`;
* any graded map `Q ⟶ P` into a bounded-below target inducing surjections on all degree quotients
  is surjective;
* if `Q` is bounded below and `Q ⟶ P` induces bijections on all degree quotients, then `P` is
  automatically bounded below, the projective splitting kills the kernel via graded Nakayama, and
  `Q ⟶ P` is a graded isomorphism;
* lifting `𝒜 0`-bases of every `P.degreeQuotient p` for a bounded-below projective `P` therefore
  gives a graded isomorphism `free 𝒜 Sigma.fst ≅ P`.

When `𝒜 0` is a principal left ideal domain (`[IsDomain (𝒜 0)] [IsPrincipalIdealRing (𝒜 0)]`, for
example `ℤ` or a field, without requiring `A` or `𝒜 0` to be commutative), every finitely generated
projective graded `A`-module `P` is isomorphic to a finite graded free module `free 𝒜 d`
(`d : Fin n → ℤ`), and hence admits a finite homogeneous `A`-basis. Specialising to the graded
image `rangeObj e` of a degree-zero idempotent endomorphism `e : M ⟶ M` splits `e` through a finite
graded free module and equips `LinearMap.range e.hom` with a homogeneous `A`-basis.

## Main definitions

* `TauCeti.GradedModuleCat.freeBasis`: the canonical homogeneous `A`-basis of `free 𝒜 d`.
* `TauCeti.GradedModuleCat.freeReindex`: reindexing a graded free module along an equivalence of
  index types.
* `TauCeti.GradedModuleCat.freeIsoBiproduct`: canonical isomorphism between a finite graded free
  module and the categorical biproduct of shifted regular modules.
* `TauCeti.GradedModuleCat.freeDegreeQuotientEquiv`,
  `TauCeti.GradedModuleCat.freeDegreeQuotientBasis`: `(free 𝒜 d).degreeQuotient p` as the free
  `SetLike.GradeZero.subalgebra 𝒜`-module on `{i // d i = p}`.
* `TauCeti.GradedModuleCat.isoFreeOfDegreeQuotientBasis`: a bounded-below projective graded module
  whose degree quotients have `𝒜 0`-bases is graded free.
* `TauCeti.GradedModuleCat.rangeObj`, `TauCeti.GradedModuleCat.rangeι`,
  `TauCeti.GradedModuleCat.rangeπ`: the graded image of a morphism and its canonical factorisation.

## Main results

* `TauCeti.GradedModuleCat.piece_eq_bot_of_lt_of_projective`,
  `TauCeti.GradedModuleCat.surjective_of_surjective_degreeQuotientMap`, and
  `TauCeti.GradedModuleCat.isIso_of_bijective_degreeQuotientMap`: graded Nakayama lower-bound,
  surjectivity, and invertibility criteria on degree quotients.
* `TauCeti.GradedModuleCat.exists_finite_free_iso_of_projective`: every finitely generated
  projective graded module over a nonnegatively graded algebra with principal-left-ideal-domain
  degree-zero piece is isomorphic to a finite graded free module.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_projective`: underlying finite homogeneous
  `A`-basis of such a projective graded module.
* `TauCeti.GradedModuleCat.exists_free_retract_of_idempotent`: splitting a degree-zero idempotent
  endomorphism of a finite projective graded module through `free 𝒜 d`, with a homogeneous basis
  of its range.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Springer Monographs in Mathematics, 2006,
  Chapter II, Section 4, for freeness of graded projectives via reduction modulo `A₊`.
* L.-H. Robert and E. Wagner, *Symmetric Khovanov--Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), Section 3.3, Lemma 3.31, for homogeneous bases of integral graded retracts.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory _root_.DirectSum

universe uk uA v uI

section FreeBasis

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] {I : Type uI} (d : I → ℤ)

/-- The canonical underlying `A`-basis of the graded free module `free 𝒜 d`, consisting of the
homogeneous generators `freeGenerator i` in degrees `d i`. -/
def freeBasis : Module.Basis I A (free 𝒜 d) := by
  classical
  exact Module.Basis.ofRepr (finsuppLequivDFinsupp A).symm

@[simp]
theorem freeBasis_apply (i : I) :
    freeBasis 𝒜 d i = freeGenerator (𝒜 := 𝒜) (d := d) i := by
  classical
  simp only [freeBasis, Module.Basis.coe_ofRepr, LinearEquiv.symm_symm]
  change (Finsupp.single i (1 : A)).toDFinsupp = freeGenerator i
  rw [Finsupp.toDFinsupp_single, DirectSum.single_eq_lof A, freeGenerator_eq_lof]

instance instModuleFreeFree : Module.Free A (free 𝒜 d) :=
  Module.Free.of_basis (freeBasis 𝒜 d)

variable {𝒜 d}

/-- Transporting the canonical basis of `free 𝒜 d` along a graded isomorphism produces a
homogeneous `A`-basis of the target. -/
def basisOfIsoFree {M : GradedModuleCat.{max uA uI} 𝒜} (e : free 𝒜 d ≅ M) :
    Module.Basis I A M :=
  (freeBasis 𝒜 d).map
    (LinearEquiv.ofBijective e.hom.hom ((isIso_iff_bijective e.hom).mp inferInstance))

@[simp]
theorem basisOfIsoFree_apply {M : GradedModuleCat.{max uA uI} 𝒜} (e : free 𝒜 d ≅ M) (i : I) :
    basisOfIsoFree e i = e.hom.hom (freeGenerator i) := by
  rw [basisOfIsoFree, Module.Basis.map_apply, freeBasis_apply]
  rfl

theorem basisOfIsoFree_mem_piece {M : GradedModuleCat.{max uA uI} 𝒜} (e : free 𝒜 d ≅ M) (i : I) :
    basisOfIsoFree e i ∈ M.grading.piece (d i) := by
  rw [basisOfIsoFree_apply]
  exact map_mem e.hom (freeGenerator_mem_free_piece i)

/-- Reindexing the basis set of a graded free module gives a canonical graded isomorphism. -/
@[expose]
def freeReindex {J : Type uI} (e : I ≃ J) (d : J → ℤ) :
    free 𝒜 (d ∘ e) ≅ free 𝒜 d where
  hom := freeLift fun i ↦ ⟨freeGenerator (e i), freeGenerator_mem_free_piece (e i)⟩
  inv := freeLift fun j ↦
    ⟨freeGenerator (e.symm j), by
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
        freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := d ∘ e) (e.symm j)⟩
  hom_inv_id := by
    apply free_hom_ext
    intro i
    rw [hom_comp, LinearMap.comp_apply, freeLift_generator, freeLift_generator]
    simp
  inv_hom_id := by
    apply free_hom_ext
    intro j
    rw [hom_comp, LinearMap.comp_apply, freeLift_generator, freeLift_generator]
    simp

@[simp]
theorem freeReindex_hom_generator {J : Type uI} (e : I ≃ J) (d : J → ℤ) (i : I) :
    (freeReindex (𝒜 := 𝒜) e d).hom.hom (freeGenerator i) = freeGenerator (e i) :=
  freeLift_generator _ i

@[simp]
theorem freeReindex_inv_generator {J : Type uI} (e : I ≃ J) (d : J → ℤ) (j : J) :
    (freeReindex (𝒜 := 𝒜) e d).inv.hom (freeGenerator j) = freeGenerator (e.symm j) :=
  freeLift_generator _ j

omit [GradedAlgebra 𝒜] in
instance instHasFiniteBiproducts : Limits.HasFiniteBiproducts (GradedModuleCat.{v} 𝒜) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- A finite graded free module `free 𝒜 e` is canonically isomorphic in `GradedModuleCat 𝒜` to the
categorical biproduct of the shifted regular modules `(regular (𝒜 := 𝒜)).shiftObj (e j)`. -/
def freeIsoBiproduct {J : Type} [Finite J] (e : J → ℤ) :
    free 𝒜 e ≅ Limits.biproduct (fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (e j)) :=
  Limits.IsLimit.conePointUniqueUpToIso
    (productFanIsLimit (fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (e j)))
    (Limits.biproduct.isLimit (fun j ↦ (regular (𝒜 := 𝒜)).shiftObj (e j)))

/-- Over a nonnegatively graded algebra, a graded free module vanishes below any common lower bound
for its generator degrees. -/
theorem free_piece_eq_bot_of_lt (hneg : ∀ i < 0, 𝒜 i = ⊥) {b : ℤ} (hd : ∀ i, b ≤ d i)
    {p : ℤ} (hp : p < b) : (free 𝒜 d).grading.piece p = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  ext i
  have hxi : x i ∈ 𝒜 (p - d i) := (mem_free_piece_iff 𝒜 d p x).mp hx i
  have hlt : p - d i < 0 := by have := hd i; omega
  simpa only [hneg _ hlt, Submodule.mem_bot, DirectSum.zero_apply] using hxi

/-- Over a nonnegatively graded algebra, every finitely generated graded module vanishes below some
degree. -/
theorem exists_piece_eq_bot_of_lt_of_finite (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (M : GradedModuleCat.{max uA v} 𝒜) [Module.Finite A M] :
    ∃ b : ℤ, ∀ p < b, M.grading.piece p = ⊥ := by
  obtain ⟨J, hJ, e, f, hf⟩ := exists_finite_free_surjection M
  let _ : Fintype J := Fintype.ofFinite J
  refine ⟨-(∑ j : J, |e j|), fun p hp ↦ piece_eq_bot_of_surjective f hf p ?_⟩
  refine free_piece_eq_bot_of_lt hneg (fun j ↦ ?_) hp
  have hle : |e j| ≤ ∑ t : J, |e t| :=
    Finset.single_le_sum (fun t _ ↦ abs_nonneg (e t)) (Finset.mem_univ j)
  have hneg_abs : -|e j| ≤ e j := neg_abs_le (e j)
  omega

end FreeBasis

section FreeDegreeQuotient

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Degree-zero projection `A → 𝒜 0` as a linear map over `SetLike.GradeZero.subalgebra 𝒜`. -/
private def gradeZeroProj (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜] :
    A →ₗ[SetLike.GradeZero.subalgebra 𝒜] SetLike.GradeZero.subalgebra 𝒜 where
  toFun a := ⟨(decompose 𝒜 a 0 : A), (decompose 𝒜 a 0).property⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' r a := Subtype.ext (DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 r.property)

/-- Reading off the degree-zero parts of the degree-`p` coordinates of `free 𝒜 d`. -/
private def freeDegreeCoord (𝒜 : ℤ → Submodule k A) [GradedAlgebra 𝒜]
    {I : Type uI} (d : I → ℤ) (p : ℤ) :
    free 𝒜 d →ₗ[SetLike.GradeZero.subalgebra 𝒜]
      ({i : I // d i = p} →₀ SetLike.GradeZero.subalgebra 𝒜) := by
  classical
  exact (Finsupp.lsubtypeDomain {i : I | d i = p}).comp <|
    (Finsupp.mapRange.linearMap (gradeZeroProj 𝒜)).comp <|
      (finsuppLequivDFinsupp A).symm.toLinearMap.restrictScalars
        (SetLike.GradeZero.subalgebra 𝒜)

private theorem coe_freeDegreeCoord_apply {I : Type uI} (d : I → ℤ) (p : ℤ)
    (u : free 𝒜 d) (j : {i : I // d i = p}) :
    (freeDegreeCoord 𝒜 d p u j : A) = decompose 𝒜 (u j.1) 0 := by
  classical
  simp only [freeDegreeCoord, gradeZeroProj, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lsubtypeDomain_apply, Finsupp.mapRange.linearMap_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]
  rfl

private theorem freeDegreeCoord_eq_zero_of_mem_offDegreeSpan (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {I : Type uI} (d : I → ℤ) (p : ℤ) {u : free 𝒜 d} (hu : u ∈ (free 𝒜 d).offDegreeSpan p) :
    freeDegreeCoord 𝒜 d p u = 0 := by
  let K : Submodule A (free 𝒜 d) :=
    { carrier := {w | ∀ c : A, freeDegreeCoord 𝒜 d p (c • w) = 0}
      add_mem' := fun ha hb c ↦ by rw [smul_add, map_add, ha c, hb c, add_zero]
      zero_mem' := fun c ↦ by rw [smul_zero, map_zero]
      smul_mem' := fun a _ hx c ↦ by rw [smul_smul]; exact hx (c * a) }
  have hle : (free 𝒜 d).offDegreeSpan p ≤ K :=
    ((free 𝒜 d).offDegreeSpan_le_iff p K).mpr fun q hq y hy c ↦
      Finsupp.ext fun j ↦ Subtype.ext <| by
        rw [Finsupp.zero_apply, ZeroMemClass.coe_zero, coe_freeDegreeCoord_apply]
        have hyj : y j.1 ∈ 𝒜 (q - p) := by
          simpa only [j.2] using (mem_free_piece_iff 𝒜 d q y).mp hy j.1
        have hmul : (decompose 𝒜 ((c • y) j.1) 0 : A) =
            (decompose 𝒜 c (p - q) : A) * y j.1 := by
          have h := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := p - q) (a := c) hyj
          rw [show p - q + (q - p) = 0 by omega] at h
          simpa only [DirectSum.smul_apply, smul_eq_mul] using h
        rw [hmul]
        rcases lt_or_gt_of_ne hq with hlt | hgt
        · have hz : y j.1 = 0 := by
            simpa only [hneg _ (by omega : q - p < 0), Submodule.mem_bot] using hyj
          simp [hz]
        · have hz : (decompose 𝒜 c (p - q) : A) = 0 := by
            simpa only [hneg _ (by omega : p - q < 0), Submodule.mem_bot] using
              (decompose 𝒜 c (p - q)).property
          simp [hz]
  simpa only [one_smul] using hle hu 1

private theorem degreeQuotientπ_lof_eq_gradeZero {I : Type uI} [DecidableEq I] (d : I → ℤ)
    (p : ℤ) (i : I) (a : A) :
    ((free 𝒜 d).degreeQuotientπ p).hom (DirectSum.lof A I (fun _ ↦ A) i a) =
      if d i = p then
        (⟨(decompose 𝒜 a 0 : A), (decompose 𝒜 a 0).property⟩ :
          SetLike.GradeZero.subalgebra 𝒜) •
          ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator i)
      else 0 := by
  rw [show DirectSum.lof A I (fun _ ↦ A) i a = a • freeGenerator (𝒜 := 𝒜) (d := d) i by
    rw [freeGenerator_eq_lof, ← map_smul, smul_eq_mul, mul_one]]
  split_ifs with h
  · induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero =>
      have h0 : (⟨(decompose 𝒜 (0 : A) 0 : A), (decompose 𝒜 (0 : A) 0).property⟩ :
          SetLike.GradeZero.subalgebra 𝒜) = 0 := Subtype.ext (by simp)
      rw [zero_smul, map_zero, h0, zero_smul]
    | add x y hx hy =>
      simp only [add_smul, map_add, decompose_add, DirectSum.add_apply, Submodule.coe_add]
      rw [hx, hy, ← add_smul]
      rfl
    | @homogeneous m x =>
      rcases eq_or_ne m 0 with rfl | hm
      · rw [decompose_coe, DirectSum.of_eq_same, map_smul]
        rfl
      · have hmem : (x : A) • freeGenerator (𝒜 := 𝒜) (d := d) i ∈
            (free 𝒜 d).grading.piece (m + d i) :=
          (free 𝒜 d).gradedSMul.smul_mem x.property (freeGenerator_mem_free_piece i)
        have hkill : ((free 𝒜 d).degreeQuotientπ p).hom ((x : A) • freeGenerator i) = 0 :=
          ((free 𝒜 d).degreeQuotientπ_eq_zero_iff p _).mpr
            ((free 𝒜 d).piece_le_offDegreeSpan (by omega) hmem)
        rw [hkill, decompose_coe, DirectSum.of_eq_of_ne _ _ _ hm.symm]
        exact (zero_smul (SetLike.GradeZero.subalgebra 𝒜)
          (((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator i))).symm
  · have hkill : ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator i) = 0 :=
      ((free 𝒜 d).degreeQuotientπ_eq_zero_iff p _).mpr
        ((free 𝒜 d).piece_le_offDegreeSpan h (freeGenerator_mem_free_piece i))
    rw [map_smul, hkill, smul_zero]

private theorem freeDegreeQuotient_rightInv {I : Type uI} (d : I → ℤ) (p : ℤ) (u : free 𝒜 d) :
    Finsupp.linearCombination (SetLike.GradeZero.subalgebra 𝒜)
      (fun j : {i : I // d i = p} ↦ ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1))
      (freeDegreeCoord 𝒜 d p u) =
      ((free 𝒜 d).degreeQuotientπ p).hom u := by
  classical
  induction u using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | of i a =>
    rw [← DirectSum.lof_eq_of A, degreeQuotientπ_lof_eq_gradeZero d p i a]
    split_ifs with h
    · have hcoord : freeDegreeCoord 𝒜 d p (DirectSum.lof A I (fun _ ↦ A) i a) =
          Finsupp.single ⟨i, h⟩ ⟨(decompose 𝒜 a 0 : A), (decompose 𝒜 a 0).property⟩ := by
        refine Finsupp.ext fun j ↦ Subtype.ext ?_
        rw [coe_freeDegreeCoord_apply, DirectSum.lof_eq_of, DirectSum.of_apply]
        by_cases hij : i = j.1
        · have hjeq : (⟨i, h⟩ : {t : I // d t = p}) = j := Subtype.ext hij
          subst hjeq
          simp
        · have hne : (⟨i, h⟩ : {t : I // d t = p}) ≠ j :=
            fun heq ↦ hij (congrArg Subtype.val heq)
          simp [hij, hne.symm]
      rw [hcoord, Finsupp.linearCombination_single]
    · have hcoord : freeDegreeCoord 𝒜 d p (DirectSum.lof A I (fun _ ↦ A) i a) = 0 := by
        refine Finsupp.ext fun j ↦ Subtype.ext ?_
        have hij : i ≠ j.1 := fun hij ↦ h (hij ▸ j.2)
        rw [Finsupp.zero_apply, ZeroMemClass.coe_zero, coe_freeDegreeCoord_apply,
          DirectSum.lof_eq_of, DirectSum.of_apply]
        simp [hij]
      rw [hcoord, map_zero]

/-- Over a nonnegatively graded algebra, the degree-`p` quotient of `free 𝒜 d` is linearly
equivalent over `SetLike.GradeZero.subalgebra 𝒜` to the finitely supported functions on the basis
indices of degree `p`. -/
def freeDegreeQuotientEquiv (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} (d : I → ℤ) (p : ℤ) :
    (free 𝒜 d).degreeQuotient p ≃ₗ[SetLike.GradeZero.subalgebra 𝒜]
      ({i : I // d i = p} →₀ SetLike.GradeZero.subalgebra 𝒜) := by
  let R₀ := SetLike.GradeZero.subalgebra 𝒜
  let U : Submodule R₀ (free 𝒜 d) :=
    (LinearMap.range ((free 𝒜 d).offDegreeι p).hom).restrictScalars R₀
  have hker : U ≤ LinearMap.ker (freeDegreeCoord 𝒜 d p) := by
    intro u hu
    rw [Submodule.restrictScalars_mem, hom_offDegreeι, Submodule.range_subtype] at hu
    exact freeDegreeCoord_eq_zero_of_mem_offDegreeSpan hneg d p hu
  let fwd : (free 𝒜 d).degreeQuotient p →ₗ[R₀] ({i : I // d i = p} →₀ R₀) :=
    Submodule.liftQ U (freeDegreeCoord 𝒜 d p) hker
  let bwd : ({i : I // d i = p} →₀ R₀) →ₗ[R₀] (free 𝒜 d).degreeQuotient p :=
    Finsupp.linearCombination R₀ fun j : {i : I // d i = p} ↦
      ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1)
  have hfwd : ∀ u : free 𝒜 d,
      fwd (((free 𝒜 d).degreeQuotientπ p).hom u) = freeDegreeCoord 𝒜 d p u := fun u ↦ by
    rw [hom_degreeQuotientπ]
    exact Submodule.liftQ_apply U (freeDegreeCoord 𝒜 d p) u
  refine LinearEquiv.ofLinearMap fwd bwd
    (Finsupp.lhom_ext' fun j ↦ LinearMap.ext fun r ↦ ?_)
    (LinearMap.ext fun y ↦ ?_)
  · classical
    refine Finsupp.ext fun j' ↦ Subtype.ext ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply,
      LinearMap.id_coe, id_eq, bwd, Finsupp.linearCombination_single]
    have hr : r • ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1) =
        ((free 𝒜 d).degreeQuotientπ p).hom ((r : A) • freeGenerator j.1) :=
      (((free 𝒜 d).degreeQuotientπ p).hom.map_smul (r : A) (freeGenerator j.1)).symm
    rw [hr, hfwd, coe_freeDegreeCoord_apply, DirectSum.smul_apply, smul_eq_mul,
      freeGenerator_apply]
    by_cases hjj : j.1 = j'.1
    · have hjeq : j = j' := Subtype.ext hjj
      subst hjeq
      simp [DirectSum.decompose_of_mem_same 𝒜 r.property]
    · have hne : j ≠ j' := fun h ↦ hjj (congrArg Subtype.val h)
      simp [hjj, hne]
  · obtain ⟨u, rfl⟩ := (free 𝒜 d).degreeQuotientπ_surjective p y
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, hfwd]
    exact freeDegreeQuotient_rightInv d p u

@[simp]
theorem freeDegreeQuotientEquiv_symm_single (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI}
    (d : I → ℤ) (p : ℤ) (j : {i : I // d i = p}) (r : SetLike.GradeZero.subalgebra 𝒜) :
    (freeDegreeQuotientEquiv hneg d p).symm (Finsupp.single j r) =
      r • ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1) := by
  exact Finsupp.linearCombination_single _ _ _

/-- The degree-`p` quotient of `free 𝒜 d` has a canonical `SetLike.GradeZero.subalgebra 𝒜`-basis
indexed by `{i // d i = p}`. -/
def freeDegreeQuotientBasis (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} (d : I → ℤ) (p : ℤ) :
    Module.Basis {i : I // d i = p} (SetLike.GradeZero.subalgebra 𝒜)
      ((free 𝒜 d).degreeQuotient p) :=
  Module.Basis.ofRepr (freeDegreeQuotientEquiv hneg d p)

@[simp]
theorem freeDegreeQuotientBasis_apply (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} (d : I → ℤ)
    (p : ℤ) (j : {i : I // d i = p}) :
    freeDegreeQuotientBasis hneg d p j =
      ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1) := by
  simp only [freeDegreeQuotientBasis, Module.Basis.coe_ofRepr]
  rw [freeDegreeQuotientEquiv_symm_single, one_smul]

end FreeDegreeQuotient

section Range

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A}

/-- The graded image of a morphism `f : M ⟶ N` in `GradedModuleCat 𝒜`, carrying the submodule
grading restricted from `N`. -/
abbrev rangeObj {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) : GradedModuleCat.{v} 𝒜 where
  carrier := LinearMap.range f.hom
  isAddCommGroup := Submodule.addCommGroup _
  isModule := Submodule.module _
  isModuleBase := Submodule.module' _
  grading := N.grading.submodule (LinearMap.range f.hom) f.isHomogeneous.isHomogeneous_range
  gradedSMul := ⟨fun {_ _} _ _ ha hy ↦ by
    rw [InternalGrading.mem_submodule_piece] at hy ⊢
    exact SetLike.GradedSMul.smul_mem (B := N.grading.piece) ha hy⟩

/-- An element of `rangeObj f` has degree `p` precisely when it has degree `p` in `N`. -/
theorem mem_rangeObj_piece_iff {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) (p : ℤ)
    (y : rangeObj f) :
    y ∈ (rangeObj f).grading.piece p ↔ (y : N) ∈ N.grading.piece p :=
  InternalGrading.mem_submodule_piece ..

/-- The graded inclusion of `rangeObj f` into `N`. -/
def rangeι {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) : rangeObj f ⟶ N :=
  ofHom (LinearMap.range f.hom).subtype
    (N.grading.isHomogeneous_subtype (LinearMap.range f.hom) f.isHomogeneous.isHomogeneous_range)

@[simp]
theorem hom_rangeι {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    (rangeι f).hom = (LinearMap.range f.hom).subtype := by
  rfl

/-- The graded corestriction of `f` onto `rangeObj f`. -/
def rangeπ {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) : M ⟶ rangeObj f :=
  ofHom f.hom.rangeRestrict (N.grading.isHomogeneous_rangeRestrict f.isHomogeneous)

@[simp]
theorem hom_rangeπ {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    (rangeπ f).hom = f.hom.rangeRestrict := by
  rfl

@[reassoc (attr := simp)]
theorem rangeπ_comp_rangeι {M N : GradedModuleCat.{v} 𝒜} (f : M ⟶ N) :
    rangeπ f ≫ rangeι f = f := by
  ext x
  simp

/-- When `e : M ⟶ M` is idempotent, `rangeObj e` is a categorical retract of `M` via `rangeι e` and
`rangeπ e`. -/
@[reassoc]
theorem rangeι_comp_rangeπ_of_idempotent {M : GradedModuleCat.{v} 𝒜} {e : M ⟶ M}
    (he : e ≫ e = e) : rangeι e ≫ rangeπ e = 𝟙 (rangeObj e) := by
  ext ⟨_, x, rfl⟩
  have hx := LinearMap.congr_fun (congrArg Hom.hom he) x
  simpa using hx

/-- The graded image of an idempotent endomorphism of a projective graded module is projective. -/
theorem projective_rangeObj_of_idempotent {M : GradedModuleCat.{v} 𝒜} [Projective M]
    {e : M ⟶ M} (he : e ≫ e = e) : Projective (rangeObj e) :=
  Retract.projective ⟨rangeι e, rangeπ e, rangeι_comp_rangeπ_of_idempotent he⟩

end Range

section NakayamaIso

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- **Graded Nakayama for morphisms.** Over a nonnegatively graded algebra, a graded morphism into
a bounded-below target is surjective whenever it induces surjections on all universal degree
quotients. -/
theorem surjective_of_surjective_degreeQuotientMap (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {Q P : GradedModuleCat.{v} 𝒜} (bP : ℤ) (hbP : ∀ p < bP, P.grading.piece p = ⊥)
    (f : Q ⟶ P) (hf : ∀ p : ℤ, Function.Surjective (degreeQuotientMap p f).hom) :
    Function.Surjective f.hom := by
  rw [← LinearMap.range_eq_top]
  refine InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜
    (LinearMap.range f.hom) f.isHomogeneous.isHomogeneous_range bP hbP fun p y hy ↦ ?_
  obtain ⟨z, hz⟩ := hf p ((P.degreeQuotientπ p).hom y)
  have hz_mem : z ∈ (Q.degreeQuotient p).grading.piece p := by
    rw [piece_eq_top_of_concentrated (fun _ ↦ Q.degreeQuotient_piece_eq_bot)]
    exact Submodule.mem_top
  obtain ⟨u, hu, rfl⟩ := (Q.mem_degreeQuotient_piece_iff p p z).mp hz_mem
  rw [degreeQuotientMap_apply] at hz
  have hsub_mem : y - f.hom u ∈ P.grading.piece p :=
    sub_mem hy (map_mem f hu)
  have hsub_pos : y - f.hom u ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P) := by
    refine (P.degreeQuotientπ_eq_zero_iff_of_mem_piece hneg hsub_mem).mp ?_
    rw [map_sub, hz, sub_self]
  rw [← add_sub_cancel (f.hom u) y]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self f.hom u) hsub_pos

/-- When `f : Q ⟶ P` is split by `s : P ⟶ Q` and induces injections on all universal degree
quotients, `f` is injective whenever `Q` is bounded below. -/
private theorem injective_of_split_of_injective_degreeQuotientMap (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {Q P : GradedModuleCat.{v} 𝒜} (bQ : ℤ) (hbQ : ∀ p < bQ, Q.grading.piece p = ⊥)
    (f : Q ⟶ P) (s : P ⟶ Q) (hs : s ≫ f = 𝟙 P)
    (hf : ∀ p : ℤ, Function.Injective (degreeQuotientMap p f).hom) :
    Function.Injective f.hom := by
  let e : Q ⟶ Q := 𝟙 Q - f ≫ s
  have hef : e ≫ f = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self]
  have he : e ≫ e = e := by
    rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hef, Limits.zero_comp, sub_zero]
  have hbK : ∀ p < bQ, (rangeObj e).grading.piece p = ⊥ := fun p hp ↦
    (Submodule.eq_bot_iff _).mpr fun z hz ↦ Subtype.ext <| by
      simpa only [hbQ p hp, Submodule.mem_bot, ZeroMemClass.coe_zero] using
        (mem_rangeObj_piece_iff e p z).mp hz
  have hsurj0 : Function.Surjective (0 : rangeObj e ⟶ rangeObj e).hom := by
    refine surjective_of_surjective_degreeQuotientMap hneg bQ hbK 0 fun p y ↦ ⟨0, ?_⟩
    obtain ⟨z, rfl⟩ := (rangeObj e).degreeQuotientπ_surjective p y
    obtain ⟨w, hw⟩ := z.property
    have hew : (Q.degreeQuotientπ p).hom (e.hom w) = 0 :=
      (hf p) <| by
        have hfw : f.hom (e.hom w) = 0 := LinearMap.congr_fun (congrArg Hom.hom hef) w
        rw [degreeQuotientMap_apply, hfw, map_zero, map_zero]
    have hzw : (rangeπ e).hom (e.hom w) = z := Subtype.ext <| by
      simpa [hw] using LinearMap.congr_fun (congrArg Hom.hom he) w
    rw [map_zero, ← hzw, ← degreeQuotientMap_apply, hew, map_zero]
  refine LinearMap.ker_eq_bot.mp ((Submodule.eq_bot_iff _).mpr fun x hx ↦ ?_)
  have hex : e.hom x = x := by
    change x - s.hom (f.hom x) = x
    rw [LinearMap.mem_ker.mp hx, map_zero, sub_zero]
  obtain ⟨_, h0⟩ := hsurj0 ⟨x, x, hex⟩
  exact congrArg Subtype.val h0.symm

private theorem map_free_eq_zero_of_subsingleton_degreeQuotient (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {P : GradedModuleCat.{max uA uI} 𝒜} {I : Type uI} {d : I → ℤ} (s : P ⟶ free 𝒜 d)
    {b : ℤ} (hsub : ∀ q < b, Subsingleton (P.degreeQuotient q))
    {p : ℤ} (hp : p < b) {x : P} (hx : x ∈ P.grading.piece p) :
    s.hom x = 0 := by
  have aux (j : I) : ∀ (m : ℕ) {q : ℤ}, q < b → q - d j < m → ∀ {y : P},
      y ∈ P.grading.piece q → s.hom y j = 0 := by
    intro m
    induction m with
    | zero =>
      intro q _ hqm y hy
      have hyj : s.hom y j ∈ 𝒜 (q - d j) :=
        (mem_free_piece_iff 𝒜 d q (s.hom y)).mp (map_mem s hy) j
      simpa only [hneg _ (by omega : q - d j < 0), Submodule.mem_bot] using hyj
    | succ m ih =>
      intro q hqb hqm y hy
      by_cases hlt : q - d j < 0
      · have hyj : s.hom y j ∈ 𝒜 (q - d j) :=
          (mem_free_piece_iff 𝒜 d q (s.hom y)).mp (map_mem s hy) j
        simpa only [hneg _ hlt, Submodule.mem_bot] using hyj
      · have _ : Subsingleton (P.degreeQuotient q) := hsub q hqb
        have hpos : y ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k P) :=
          (P.degreeQuotientπ_eq_zero_iff_of_mem_piece hneg hy).mp (Subsingleton.elim _ _)
        let proj : P →ₗ[k] A :=
          ((DirectSum.component A I (fun _ ↦ A) j).restrictScalars k).comp
            (s.hom.restrictScalars k)
        change y ∈ LinearMap.ker proj
        rw [← decompose_of_mem_same P.grading.piece hy]
        refine (Submodule.span_le (p := LinearMap.ker proj)).mpr ?_
          (InternalGrading.decompose_mem_span_of_mem_positive_smul_top 𝒜 hpos q)
        rintro _ ⟨i, hi, a, -, z, hz, rfl⟩
        have hz0 : s.hom z j = 0 := ih (by omega) (by omega) hz
        change (s.hom (a • z)) j = 0
        rw [s.hom.map_smul, DirectSum.smul_apply, hz0, smul_zero]
  exact DFinsupp.ext fun j ↦ aux j ((p - d j).toNat + 1) hp (by omega) hx

/-- Over a nonnegatively graded algebra, a projective graded module vanishes in every degree below
`b` whenever all of its universal degree quotients below `b` are subsingletons. -/
theorem piece_eq_bot_of_lt_of_projective (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (P : GradedModuleCat.{max uA v} 𝒜) [Projective P]
    {b : ℤ} (hsub : ∀ q < b, Subsingleton (P.degreeQuotient q))
    {p : ℤ} (hp : p < b) : P.grading.piece p = ⊥ := by
  let π : free 𝒜 (Sigma.fst : (Σ q : ℤ, P.grading.piece q) → ℤ) ⟶ P := freeLift Sigma.snd
  have hrange : (Set.range fun i : Σ q : ℤ, P.grading.piece q ↦ (i.2 : P)) =
      {y | ∃ q, y ∈ P.grading.piece q} := by ext y; simp
  have _ : Epi π := (epi_iff_surjective π).mpr <|
    (freeLift_surjective_iff _).mpr (by rw [hrange, P.grading.span_setOf_exists_mem_piece_eq_top A])
  let s := Projective.factorThru (𝟙 P) π
  have hs : s ≫ π = 𝟙 P := Projective.factorThru_comp (𝟙 P) π
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hsx : s.hom x = 0 := map_free_eq_zero_of_subsingleton_degreeQuotient hneg s hsub hp hx
  calc
    x = π.hom (s.hom x) := (LinearMap.congr_fun (congrArg Hom.hom hs) x).symm
    _ = 0 := by rw [hsx, map_zero]

/-- **Graded Nakayama invertibility criterion.** Over a nonnegatively graded algebra, a graded
morphism out of a bounded-below module into a projective target is an isomorphism whenever it
induces bijections on all universal degree quotients. -/
theorem isIso_of_bijective_degreeQuotientMap (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {Q P : GradedModuleCat.{max uA v} 𝒜} [Projective P]
    (bQ : ℤ) (hbQ : ∀ p < bQ, Q.grading.piece p = ⊥)
    (f : Q ⟶ P) (hf : ∀ p : ℤ, Function.Bijective (degreeQuotientMap p f).hom) :
    IsIso f := by
  have hbP : ∀ p < bQ, P.grading.piece p = ⊥ := fun _ hp ↦
    piece_eq_bot_of_lt_of_projective hneg P (fun q hq ↦ by
      have _ : Subsingleton (Q.degreeQuotient q) :=
        Q.subsingleton_degreeQuotient_of_piece_eq_bot (hbQ q hq)
      exact Function.Surjective.subsingleton (hf q).surjective) hp
  have hsurj : Function.Surjective f.hom :=
    surjective_of_surjective_degreeQuotientMap hneg bQ hbP f fun p ↦ (hf p).surjective
  have _ : Epi f := (epi_iff_surjective f).mpr hsurj
  have hinj : Function.Injective f.hom :=
    injective_of_split_of_injective_degreeQuotientMap hneg bQ hbQ f
      (Projective.factorThru (𝟙 P) f) (Projective.factorThru_comp (𝟙 P) f) fun p ↦ (hf p).injective
  exact (isIso_iff_bijective f).mpr ⟨hinj, hsurj⟩

private theorem bijective_degreeQuotientMap_freeLift
    {P : GradedModuleCat.{max uA uI} 𝒜} {I : ℤ → Type uI}
    (b : ∀ p : ℤ, Module.Basis (I p) (SetLike.GradeZero.subalgebra 𝒜) (P.degreeQuotient p))
    (x : ∀ j : Σ p : ℤ, I p, P.grading.piece j.1)
    (hx : ∀ (p : ℤ) (i : I p), (P.degreeQuotientπ p).hom (x ⟨p, i⟩ : P) = b p i) (p : ℤ) :
    Function.Bijective (degreeQuotientMap p (freeLift x)).hom := by
  let R₀ := SetLike.GradeZero.subalgebra 𝒜
  let d : (Σ q : ℤ, I q) → ℤ := Sigma.fst
  let σ : I p ≃ {j : Σ q : ℤ, I q // d j = p} :=
    { toFun := fun i ↦ ⟨⟨p, i⟩, rfl⟩
      invFun := fun j ↦ j.2 ▸ j.1.2
      left_inv := fun _ ↦ rfl
      right_inv := fun ⟨⟨_, _⟩, h⟩ ↦ by subst h; rfl }
  let domEquiv : (I p →₀ R₀) ≃ₗ[R₀] ({j : Σ q : ℤ, I q // d j = p} →₀ R₀) := Finsupp.domLCongr σ
  let bwd : (I p →₀ R₀) →ₗ[R₀] (free 𝒜 d).degreeQuotient p :=
    (Finsupp.linearCombination R₀ fun j : {j : Σ q : ℤ, I q // d j = p} ↦
      ((free 𝒜 d).degreeQuotientπ p).hom (freeGenerator j.1)).comp
      domEquiv.toLinearMap
  have hbwd_surj : Function.Surjective bwd := fun y ↦ by
    obtain ⟨u, rfl⟩ := (free 𝒜 d).degreeQuotientπ_surjective p y
    refine ⟨domEquiv.symm (freeDegreeCoord 𝒜 d p u), ?_⟩
    dsimp only [bwd]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, domEquiv.apply_symm_apply]
    exact freeDegreeQuotient_rightInv d p u
  have hcomp : ((degreeQuotientMap p (freeLift x)).hom.restrictScalars R₀).comp bwd =
      (b p).repr.symm.toLinearMap := by
    refine Finsupp.lhom_ext' fun i ↦ LinearMap.ext fun r ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, LinearEquiv.coe_coe,
      bwd, domEquiv, Finsupp.domLCongr_single, Finsupp.linearCombination_single]
    rw [(((degreeQuotientMap p (freeLift x)).hom).restrictScalars R₀).map_smul,
      LinearMap.restrictScalars_apply, degreeQuotientMap_apply, freeLift_generator,
      show (σ i).1 = ⟨p, i⟩ from rfl, hx p i, Module.Basis.repr_symm_apply,
      Finsupp.linearCombination_single]
  have hcomp_bij : Function.Bijective (⇑(degreeQuotientMap p (freeLift x)).hom ∘ ⇑bwd) := by
    have : ⇑(degreeQuotientMap p (freeLift x)).hom ∘ ⇑bwd = ⇑(b p).repr.symm :=
      funext fun v ↦ DFunLike.congr_fun hcomp v
    exact this ▸ (b p).repr.symm.bijective
  exact ⟨fun u v h ↦ by
      obtain ⟨u', rfl⟩ := hbwd_surj u
      obtain ⟨v', rfl⟩ := hbwd_surj v
      exact congrArg bwd (hcomp_bij.1 h),
    hcomp_bij.2.of_comp⟩

/-- Lifting `SetLike.GradeZero.subalgebra 𝒜`-bases of every universal degree quotient of a
bounded-below projective graded module `P` produces a graded isomorphism from `free 𝒜 Sigma.fst`
onto `P`. -/
def isoFreeOfDegreeQuotientBasis (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {P : GradedModuleCat.{max uA uI} 𝒜} [Projective P]
    (bP : ℤ) (hbP : ∀ p < bP, P.grading.piece p = ⊥)
    {I : ℤ → Type uI}
    (b : ∀ p : ℤ, Module.Basis (I p) (SetLike.GradeZero.subalgebra 𝒜) (P.degreeQuotient p))
    (x : ∀ j : Σ p : ℤ, I p, P.grading.piece j.1)
    (hx : ∀ (p : ℤ) (i : I p), (P.degreeQuotientπ p).hom (x ⟨p, i⟩ : P) = b p i) :
    free 𝒜 (Sigma.fst : (Σ p : ℤ, I p) → ℤ) ≅ P := by
  have hiso : IsIso (freeLift x) := by
    by_cases hA : Subsingleton A
    · have _ : Subsingleton (free 𝒜 (Sigma.fst : (Σ p : ℤ, I p) → ℤ)) :=
        Module.subsingleton A _
      have _ : Subsingleton P := Module.subsingleton A _
      exact (isIso_iff_bijective (freeLift x)).mpr
        ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩
    · have _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
      have _ : Nontrivial (SetLike.GradeZero.subalgebra 𝒜) :=
        ⟨⟨1, 0, fun h ↦ one_ne_zero (congrArg Subtype.val h)⟩⟩
      have hbQ : ∀ p < bP, (free 𝒜 (Sigma.fst : (Σ q : ℤ, I q) → ℤ)).grading.piece p = ⊥ := by
        intro p hp
        refine free_piece_eq_bot_of_lt hneg (fun j ↦ ?_) hp
        by_contra! hlt
        have _ : Subsingleton (P.degreeQuotient j.1) :=
          P.subsingleton_degreeQuotient_of_piece_eq_bot (hbP j.1 hlt)
        exact (b j.1).ne_zero j.2 (Subsingleton.elim _ _)
      exact isIso_of_bijective_degreeQuotientMap hneg bP hbQ (freeLift x)
        (bijective_degreeQuotientMap_freeLift b x hx)
  exact asIso (freeLift x)

@[simp]
theorem isoFreeOfDegreeQuotientBasis_hom (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {P : GradedModuleCat.{max uA uI} 𝒜} [Projective P]
    (bP : ℤ) (hbP : ∀ p < bP, P.grading.piece p = ⊥)
    {I : ℤ → Type uI}
    (b : ∀ p : ℤ, Module.Basis (I p) (SetLike.GradeZero.subalgebra 𝒜) (P.degreeQuotient p))
    (x : ∀ j : Σ p : ℤ, I p, P.grading.piece j.1)
    (hx : ∀ (p : ℤ) (i : I p), (P.degreeQuotientπ p).hom (x ⟨p, i⟩ : P) = b p i) :
    (isoFreeOfDegreeQuotientBasis hneg bP hbP b x hx).hom = freeLift x := by
  simp [isoFreeOfDegreeQuotientBasis]

end NakayamaIso

section PID

private def consZeroLinearMap {S : Type*} [Semiring S] (m : ℕ) :
    (Fin m → S) →ₗ[S] (Fin (m + 1) → S) where
  toFun w := Fin.cons (0 : S) w
  map_add' u v := funext fun j ↦ by refine Fin.cases (by simp) (fun i ↦ by simp) j
  map_smul' r u := funext fun j ↦ by refine Fin.cases (by simp) (fun i ↦ by simp) j

@[simp]
private theorem consZeroLinearMap_apply {S : Type*} [Semiring S] (m : ℕ) (w : Fin m → S) :
    consZeroLinearMap m w = Fin.cons (0 : S) w :=
  rfl

private def prodConsZeroEquiv {S : Type*} [Ring S] [IsDomain S]
    {m : ℕ} {N : Submodule S (Fin (m + 1) → S)}
    {a : S} (ha : a ≠ 0) (haI : N.map (LinearMap.proj 0) = Submodule.span S {a})
    {y : Fin (m + 1) → S} (hyN : y ∈ N) (hy0 : y 0 = a) :
    (S × N.comap (consZeroLinearMap m)) ≃ₗ[S] N :=
  let K := N.comap (consZeroLinearMap m)
  let fwd : (S × K) →ₗ[S] N :=
    { toFun := fun cw ↦ ⟨cw.1 • y + consZeroLinearMap m cw.2.1,
        N.add_mem (N.smul_mem cw.1 hyN) cw.2.2⟩
      map_add' := fun _ _ ↦ Subtype.ext <| by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul, map_add]
        abel
      map_smul' := fun _ _ ↦ Subtype.ext <| by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, mul_smul,
          map_smul, RingHom.id_apply, smul_add] }
  LinearEquiv.ofBijective fwd
    ⟨fun ⟨c₁, w₁⟩ ⟨c₂, w₂⟩ h ↦ by
        have hval := congrArg Subtype.val h
        have hc : c₁ = c₂ := mul_right_cancel₀ ha (by simpa [fwd, hy0] using congrFun hval 0)
        subst hc
        have hw : consZeroLinearMap m w₁.1 = consZeroLinearMap m w₂.1 := by simpa [fwd] using hval
        exact Prod.ext rfl (Subtype.ext <| funext fun i ↦ by simpa using congrFun hw i.succ),
      fun ⟨v, hvN⟩ ↦ by
        have hv0 : v 0 ∈ Submodule.span S {a} :=
          haI ▸ Submodule.mem_map_of_mem (f := LinearMap.proj 0) hvN
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv0
        let u : Fin (m + 1) → S := v - c • y
        have huN : u ∈ N := N.sub_mem hvN (N.smul_mem c hyN)
        have hu0 : u 0 = 0 := by simp only [u, Pi.sub_apply, Pi.smul_apply, hy0]; rw [hc, sub_self]
        have hcons : Fin.cons (0 : S) (Fin.tail u) = u := by rw [← hu0, Fin.cons_self_tail]
        have huK : Fin.tail u ∈ K := by change Fin.cons (0 : S) (Fin.tail u) ∈ N; rwa [hcons]
        exact ⟨(c, ⟨Fin.tail u, huK⟩), Subtype.ext (by simp [fwd, hcons, u])⟩⟩

/-- Every left submodule of a finite free module `Fin m → S` over a principal left ideal domain
`S` admits a finite `S`-basis, without requiring `S` to be commutative. -/
private theorem exists_basis_submodule_pi {S : Type*} [Ring S] [IsDomain S]
    [IsPrincipalIdealRing S] :
    ∀ (m : ℕ) (N : Submodule S (Fin m → S)), ∃ n : ℕ, Nonempty (Module.Basis (Fin n) S N)
  | 0, N => ⟨0, ⟨Module.Basis.empty N⟩⟩
  | m + 1, N => by
      obtain ⟨n', ⟨bK⟩⟩ := exists_basis_submodule_pi m (N.comap (consZeroLinearMap m))
      let I : Ideal S := N.map (LinearMap.proj 0)
      obtain ⟨a, haI⟩ := (IsPrincipalIdealRing.principal I).principal
      by_cases ha : a = 0
      · have hI : I = ⊥ := by rw [haI, ha, Submodule.span_zero_singleton]
        let fwd0 : N.comap (consZeroLinearMap m) →ₗ[S] N :=
          { toFun := fun w ↦ ⟨consZeroLinearMap m w.1, w.2⟩
            map_add' := fun _ _ ↦ Subtype.ext (by simp [map_add])
            map_smul' := fun _ _ ↦ Subtype.ext (by simp [map_smul]) }
        let eKN : N.comap (consZeroLinearMap m) ≃ₗ[S] N :=
          LinearEquiv.ofBijective fwd0
            ⟨fun w₁ w₂ h ↦ Subtype.ext <| funext fun i ↦ by
                simpa [fwd0] using congrFun (congrArg Subtype.val h) i.succ,
              fun ⟨v, hvN⟩ ↦ by
                have hv0 : v 0 = 0 := by
                  have : v 0 ∈ I := Submodule.mem_map_of_mem (f := LinearMap.proj 0) hvN
                  simpa [hI] using this
                have hcons : Fin.cons (0 : S) (Fin.tail v) = v := by rw [← hv0, Fin.cons_self_tail]
                have hvK : Fin.tail v ∈ N.comap (consZeroLinearMap m) := by
                  change Fin.cons (0 : S) (Fin.tail v) ∈ N
                  rwa [hcons]
                exact ⟨⟨Fin.tail v, hvK⟩, Subtype.ext (by simp [fwd0, hcons])⟩⟩
        exact ⟨n', ⟨bK.map eKN⟩⟩
      · have ha_mem : a ∈ I := haI ▸ Submodule.mem_span_singleton_self a
        obtain ⟨y, hyN, hy0⟩ := Submodule.mem_map.mp ha_mem
        let bProd : Module.Basis (Fin 1 ⊕ Fin n') S (S × N.comap (consZeroLinearMap m)) :=
          (Module.Basis.singleton (Fin 1) S).prod bK
        exact ⟨1 + n',
          ⟨(bProd.reindex finSumFinEquiv).map (prodConsZeroEquiv ha haI hyN hy0)⟩⟩

private theorem exists_basis_of_injective_finsupp {S : Type*} [Ring S] [IsDomain S]
    [IsPrincipalIdealRing S] {M : Type*} [AddCommGroup M] [Module S M]
    {J : Type*} [Finite J] (ι : M →ₗ[S] (J →₀ S)) (hι : Function.Injective ι) :
    ∃ n : ℕ, Nonempty (Module.Basis (Fin n) S M) := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let eJ : (J →₀ S) ≃ₗ[S] (Fin (Fintype.card J) → S) :=
    (Finsupp.domLCongr (Fintype.equivFin J)).trans
      (Finsupp.linearEquivFunOnFinite S S (Fin (Fintype.card J)))
  let ι' : M →ₗ[S] (Fin (Fintype.card J) → S) := eJ.toLinearMap.comp ι
  have hι' : Function.Injective ι' := eJ.injective.comp hι
  obtain ⟨n, ⟨bN⟩⟩ := exists_basis_submodule_pi (Fintype.card J) (LinearMap.range ι')
  exact ⟨n, ⟨bN.map (LinearEquiv.ofInjective ι' hι').symm⟩⟩

private theorem finite_sigma_of_injective_degreeQuotient
    {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]
    [Nontrivial (SetLike.GradeZero.subalgebra 𝒜)]
    {P : GradedModuleCat.{max uA uI} 𝒜} {J : Type uI} [Finite J] {e : J → ℤ}
    (s : P ⟶ free 𝒜 e) (hs_inj : ∀ p : ℤ, Function.Injective (degreeQuotientMap p s).hom)
    (rk : ℤ → ℕ)
    (b : ∀ p : ℤ, Module.Basis (Fin (rk p)) (SetLike.GradeZero.subalgebra 𝒜)
      (P.degreeQuotient p)) :
    Finite (Σ p : ℤ, Fin (rk p)) := by
  have hrange : ∀ j : Σ p : ℤ, Fin (rk p), j.1 ∈ Set.range e := fun ⟨p, i⟩ ↦ by
    by_contra hp
    have : IsEmpty {t : J // e t = p} := ⟨fun ⟨t, ht⟩ ↦ hp ⟨t, ht⟩⟩
    have _ : Subsingleton ((free 𝒜 e).degreeQuotient p) :=
      subsingleton_of_forall_eq 0 fun y ↦ by
        obtain ⟨u, rfl⟩ := (free 𝒜 e).degreeQuotientπ_surjective p y
        rw [← freeDegreeQuotient_rightInv e p u, Subsingleton.elim (freeDegreeCoord 𝒜 e p u) 0,
          map_zero]
    exact (b p).ne_zero i (hs_inj p (Subsingleton.elim _ _))
  let _ : Finite (Set.range e) := Set.finite_range e
  exact Finite.of_injective (fun j : Σ p : ℤ, Fin (rk p) ↦
    (⟨⟨j.1, hrange j⟩, j.2⟩ : Σ q : Set.range e, Fin (rk q.1)))
    fun ⟨_, _⟩ ⟨_, _⟩ h ↦ by
      obtain ⟨hp, hi⟩ := Sigma.mk.inj_iff.mp h
      cases Subtype.ext_iff.mp hp
      exact Sigma.ext rfl hi

/-- **Graded freeness over a principal-left-ideal-domain degree-zero piece.** Over any
nonnegatively `ℤ`-graded algebra whose degree-zero piece `𝒜 0` is a principal left ideal domain,
every finitely generated projective graded module is isomorphic in `GradedModuleCat 𝒜` to a finite
graded free module `free 𝒜 d`. -/
theorem exists_finite_free_iso_of_projective
    {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsDomain (𝒜 0)] [IsPrincipalIdealRing (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Projective P] :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 d ≅ P) := by
  let e₀ : SetLike.GradeZero.subalgebra 𝒜 ≃+* 𝒜 0 :=
    { toFun := id, invFun := id, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl,
      map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }
  have _ : IsDomain (SetLike.GradeZero.subalgebra 𝒜) := e₀.toMulEquiv.isDomain (𝒜 0)
  have _ : IsPrincipalIdealRing (SetLike.GradeZero.subalgebra 𝒜) :=
    IsPrincipalIdealRing.of_surjective e₀.symm.toRingHom e₀.symm.surjective
  obtain ⟨J, hJ, e, π, hπ⟩ := exists_finite_free_surjection.{uk, uA, 0} P
  let _ : Finite J := hJ
  obtain ⟨bP, hbP⟩ := exists_piece_eq_bot_of_lt_of_finite.{uk, uA, 0} hneg P
  have _ : Epi π := (epi_iff_surjective π).mpr hπ
  let s : P ⟶ free 𝒜 e := Projective.factorThru (𝟙 P) π
  have hs : s ≫ π = 𝟙 P := Projective.factorThru_comp (𝟙 P) π
  have hs_inj : ∀ p : ℤ, Function.Injective (degreeQuotientMap p s).hom := fun p y₁ y₂ hy ↦ by
    have h : (degreeQuotientMap p s ≫ degreeQuotientMap p π).hom y₁ =
        (degreeQuotientMap p s ≫ degreeQuotientMap p π).hom y₂ :=
      congrArg (degreeQuotientMap p π).hom hy
    rwa [← degreeQuotientMap_comp, hs, degreeQuotientMap_id, hom_id, LinearMap.id_apply,
      LinearMap.id_apply] at h
  have hex_basis : ∀ p : ℤ, ∃ n : ℕ,
      Nonempty (Module.Basis (Fin n) (SetLike.GradeZero.subalgebra 𝒜) (P.degreeQuotient p)) :=
    fun p ↦ exists_basis_of_injective_finsupp
      ((freeDegreeQuotientEquiv hneg e p).toLinearMap.comp
        ((degreeQuotientMap p s).hom.restrictScalars (SetLike.GradeZero.subalgebra 𝒜)))
      ((freeDegreeQuotientEquiv hneg e p).injective.comp (hs_inj p))
  choose rk hrk using hex_basis
  let b := fun p : ℤ ↦ (hrk p).some
  have hlift : ∀ j : Σ p : ℤ, Fin (rk p),
      ∃ x ∈ P.grading.piece j.1, (P.degreeQuotientπ j.1).hom x = b j.1 j.2 := fun ⟨p, i⟩ ↦
    (P.mem_degreeQuotient_piece_iff p p (b p i)).mp <| by
      rw [piece_eq_top_of_concentrated (fun _ ↦ P.degreeQuotient_piece_eq_bot)]
      exact Submodule.mem_top
  choose x hx_mem hx_eq using hlift
  let isoSigma : free 𝒜 (Sigma.fst : (Σ p : ℤ, Fin (rk p)) → ℤ) ≅ P :=
    isoFreeOfDegreeQuotientBasis hneg bP hbP b (fun j ↦ ⟨x j, hx_mem j⟩) fun p i ↦ hx_eq ⟨p, i⟩
  have _ : Finite (Σ p : ℤ, Fin (rk p)) :=
    finite_sigma_of_injective_degreeQuotient s hs_inj rk b
  let _ : Fintype (Σ p : ℤ, Fin (rk p)) := Fintype.ofFinite _
  let eFin := (Fintype.equivFin (Σ p : ℤ, Fin (rk p))).symm
  exact ⟨_, Sigma.fst ∘ eFin, ⟨(freeReindex eFin Sigma.fst).trans isoSigma⟩⟩

/-- Every finitely generated projective graded module over a nonnegatively `ℤ`-graded algebra with
principal-left-ideal-domain degree-zero piece admits a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_of_projective
    {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsDomain (𝒜 0)] [IsPrincipalIdealRing (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    (P : GradedModuleCat.{uA} 𝒜) [Module.Finite A P] [Projective P] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A P) (d : Fin n → ℤ),
      ∀ i, b i ∈ P.grading.piece (d i) := by
  obtain ⟨n, d, ⟨e⟩⟩ := exists_finite_free_iso_of_projective hneg P
  exact ⟨n, basisOfIsoFree e, d, basisOfIsoFree_mem_piece e⟩

/-- **Graded free splitting of an idempotent endomorphism.** Over a nonnegatively `ℤ`-graded
algebra with principal-left-ideal-domain degree-zero piece, every idempotent morphism `e : M ⟶ M`
on a finitely generated projective graded `A`-module splits through a finite graded free module
`free 𝒜 d` via `ι : free 𝒜 d ⟶ M` and `π : M ⟶ free 𝒜 d` with `π ≫ ι = e` and
`ι ≫ π = 𝟙 (free 𝒜 d)`, giving `LinearMap.range e.hom` a finite homogeneous `A`-basis. -/
theorem exists_free_retract_of_idempotent
    {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
    {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜] [IsDomain (𝒜 0)] [IsPrincipalIdealRing (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥)
    {M : GradedModuleCat.{uA} 𝒜} [Module.Finite A M] [Projective M]
    (e : M ⟶ M) (he : e ≫ e = e) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : free 𝒜 d ⟶ M) (π : M ⟶ free 𝒜 d)
      (b : Module.Basis (Fin n) A (LinearMap.range e.hom)),
      π ≫ ι = e ∧ ι ≫ π = 𝟙 (free 𝒜 d) ∧
        ∀ i, (b i : M) = ι.hom (freeGenerator i) ∧ (b i : M) ∈ M.grading.piece (d i) := by
  have _ : Projective (rangeObj e) := projective_rangeObj_of_idempotent he
  have _ : Module.Finite A (rangeObj e) :=
    Module.Finite.of_surjective (rangeπ e).hom e.hom.surjective_rangeRestrict
  obtain ⟨n, d, ⟨iso⟩⟩ := exists_finite_free_iso_of_projective hneg (rangeObj e)
  refine ⟨n, d, iso.hom ≫ rangeι e, rangeπ e ≫ iso.inv, basisOfIsoFree iso, ?_, ?_, fun i ↦ ?_⟩
  · rw [Category.assoc, ← Category.assoc iso.inv, iso.inv_hom_id, Category.id_comp,
      rangeπ_comp_rangeι]
  · rw [Category.assoc, ← Category.assoc (rangeι e), rangeι_comp_rangeπ_of_idempotent he,
      Category.id_comp, iso.hom_inv_id]
  · refine ⟨?_, (mem_rangeObj_piece_iff e (d i) (basisOfIsoFree iso i)).mp
        (basisOfIsoFree_mem_piece iso i)⟩
    rw [hom_comp, LinearMap.comp_apply, hom_rangeι, Submodule.subtype_apply]
    exact congrArg Subtype.val (basisOfIsoFree_apply iso i)

end PID

end TauCeti.GradedModuleCat
