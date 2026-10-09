/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
import TauCeti.Algebra.Category.GradedModuleCat.Abelian
import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.GradedDimension
import TauCeti.CategoryTheory.ObjectProperty.Retract
import TauCeti.CategoryTheory.Preadditive.Indecomposable
import TauCeti.CategoryTheory.Preadditive.Radical.Multiplicity

/-!
# The indecomposable graded projective basis of `K₀^gr(proj A)`

Over a finite-dimensional algebra, every finite graded projective is a finite direct sum of
indecomposable graded projectives. If a family meets all such indecomposables up to internal
shift, its classes span `K₀^gr(proj A)` over `ℤ[q,q⁻¹]`: shifting a summand by `d` multiplies its
class by `qᵈ`. No uniqueness of decomposition or splitting-field hypothesis is needed for this.

Conversely, when `𝒜` is a decomposition of `A`, the classes of indecomposable finite graded
projectives that are pairwise non-isomorphic up to shift are linearly independent over
`ℤ[q,q⁻¹]`. The coordinates detecting them are Krull–Schmidt multiplicities read through the
radical of the category: for an indecomposable `Y`, the dimension of `(X ⟶ Y) / rad(X, Y)` is
additive in `X` on the split conflations of graded projectives, vanishes on indecomposables not
isomorphic to `Y`, and is positive on `Y`. Together the two halves give a `ℤ[q,q⁻¹]`-basis of
`K₀^gr(proj A)` indexed by the indecomposable graded projectives up to shift, the projective-side
basis in which the graded Cartan map becomes a matrix. Indecomposability is taken in the full
category of finite graded projectives.

## Main definitions

* `TauCeti.IsExhaustiveGradedIndecomposableProjectiveFamily`: a family of finite graded
  projectives meeting every indecomposable one up to shift.
* `TauCeti.gradedIndecomposableProjectiveClassBasis`: the `ℤ[q,q⁻¹]`-basis of `K₀^gr(proj A)`
  given by an exhaustive family of indecomposables, pairwise non-isomorphic up to shift.

## Main results

* `TauCeti.span_range_laurentK0_projective_of_eq_top`: a family exhaustive among indecomposable
  graded projectives up to shift spans the Laurent Grothendieck group.
* `TauCeti.linearIndependent_laurentK0_projective`: indecomposable graded projectives which are
  pairwise non-isomorphic up to shift have linearly independent classes over `ℤ[q,q⁻¹]`.
* `TauCeti.indecomposable_shiftObj`: an internal shift of an indecomposable finite graded
  projective is indecomposable.
* The instance `Module.Finite k (X ⟶ Y)`: over a finite-dimensional algebra, graded maps between
  finite graded projectives form a finite-dimensional space.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3.
* C. A. Weibel, *The K-book*, Chapter II, Sections 5 and 7.
* H. Krause, "Krull–Schmidt categories and projective covers", *Expositiones Mathematicae* **33**
  (2015), 535–549, for Krull–Schmidt categories and their radical.
* `TauCeti.RepresentationTheory.GrothendieckGroup.ProjectiveBasis`: the ungraded
  indecomposable-projective basis of `K₀(proj A)`, of which this file is the graded analogue.
* `TauCeti.Algebra.Category.GradedModuleCat.CartanMap.SimpleBasis`: the graded simple-class basis.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe uk uA uI

section Exhaustive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- A family of finite graded projectives is exhaustive up to shift if every indecomposable
object of their full subcategory is isomorphic to an internal shift of a member of the family. -/
def IsExhaustiveGradedIndecomposableProjectiveFamily
    (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) : Prop :=
  ∀ M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory, Indecomposable M →
    ∃ i d, Nonempty (M ≅
      ⟨(P i).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P i).property d⟩)

/-- Characterization of exhaustiveness up to shift without unfolding the definition. -/
theorem isExhaustiveGradedIndecomposableProjectiveFamily_iff
    (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    IsExhaustiveGradedIndecomposableProjectiveFamily P ↔
      ∀ M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory, Indecomposable M →
        ∃ i d, Nonempty (M ≅
          ⟨(P i).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P i).property d⟩) :=
  Iff.rfl

end Exhaustive

section Span

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A] [Module.Finite k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}
  (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)

private theorem finrank_pos_of_not_isZero
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (hM : ¬IsZero M) :
    0 < Module.finrank k M.obj := by
  have : Module.Finite k M.obj := Module.Finite.trans A M.obj
  by_contra h
  have : Subsingleton M.obj := (Module.finrank_zero_iff (R := k)).mp (by omega)
  exact hM <| (IsZero.iff_id_eq_zero M).2 <| ObjectProperty.hom_ext _ <|
    GradedModuleCat.hom_ext (LinearMap.ext fun _ => Subsingleton.elim _ _)

private theorem finrank_eq_add_of_iso_biprod
    (M Y Z : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) (e : M ≅ Y ⊞ Z) :
    Module.finrank k M.obj = Module.finrank k Y.obj + Module.finrank k Z.obj := by
  have : Module.Finite k Y.obj := Module.Finite.trans A Y.obj
  have : Module.Finite k Z.obj := Module.Finite.trans A Z.obj
  -- Forgetting the grading sends this biproduct decomposition to a product of modules.
  let F := (gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.toModuleCat
  let : PreservesBinaryBiproduct Y Z F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  let e' : ModuleCat.of A M.obj ≅ ModuleCat.of A (Y.obj × Z.obj) :=
    F.mapIso e ≪≫ F.mapBiprod Y Z ≪≫
    ModuleCat.biprodIsoProd (F.obj Y) (F.obj Z)
  exact (e'.toLinearEquiv.restrictScalars k).finrank_eq.trans Module.finrank_prod

private theorem laurentK0_projective_of_mem_span
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P)
    (M : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M ∈
      Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i =>
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i)) := by
  classical
  set G := Submodule.span (LaurentPolynomial ℤ)
    (Set.range fun i =>
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i))
  induction hn : Module.finrank k M.obj using Nat.strong_induction_on generalizing M with
  | _ n ih =>
    by_cases hM : IsZero M
    · rw [← LaurentK0.ofExactK0_exactK0_of.{uA}, ExactK0.of_eq_zero_of_isZero.{uA} hM,
        map_zero]
      exact G.zero_mem
    by_cases hind : Indecomposable M
    · obtain ⟨i, d, ⟨e⟩⟩ := hP M hind
      rw [LaurentK0.of_congr.{uA} _ e, laurentK0_projective_of_shiftObj]
      exact G.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    -- A nonzero decomposable object has two nonzero projective summands.
    obtain ⟨Y, Z, e, hY, hZ⟩ :
        ∃ Y Z, ∃ e : M ≅ Y ⊞ Z, ¬IsZero Y ∧ ¬IsZero Z := by
      simpa only [Indecomposable, hM, not_false_eq_true, true_and, not_forall,
        not_or, exists_prop] using hind
    have hdim := finrank_eq_add_of_iso_biprod M Y Z e
    have hYpos := finrank_pos_of_not_isZero Y hY
    have hZpos := finrank_pos_of_not_isZero Z hZ
    have hclass : LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) M =
        LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Y +
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) Z := by
      exact (LaurentK0.of_congr.{uA} _ e).trans <| LaurentK0.of_conflation.{uA} _
        (ExactStructure.conflation_biprodShortComplex
          (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure Y Z)
    rw [hclass]
    exact G.add_mem (ih _ (by omega) Y rfl) (ih _ (by omega) Z rfl)

/-- **The classes of a family exhaustive among indecomposable graded projectives up to shift span
`K₀^gr(proj A)` over `ℤ[q,q⁻¹]`.** Every finite graded projective splits into finitely many
indecomposable summands, and the class of a shifted summand is a Laurent monomial times the class
of a member of the family. No independence or uniqueness of decomposition is assumed. -/
theorem span_range_laurentK0_projective_of_eq_top
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P) :
    Submodule.span (LaurentPolynomial ℤ)
        (Set.range fun i =>
          LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i)) = ⊤ := by
  refine top_unique fun x _ => ?_
  clear ‹x ∈ ⊤›
  obtain ⟨x, rfl⟩ :=
    (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).surjective x
  induction x using ExactK0.induction_on with
  | zero => simp
  | of M => simpa using laurentK0_projective_of_mem_span P hP M
  | add x y hx hy => simpa using Submodule.add_mem _ hx hy
  | neg x hx => simpa using Submodule.neg_mem _ hx

end Span

/-! ### Linear independence -/

section Independence

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- **A shift of an indecomposable finite graded projective is indecomposable**: graded
endomorphisms of `X` and of `X{d}` are the same `A`-linear maps. -/
theorem indecomposable_shiftObj {X : (gradedFiniteProjectiveModules 𝒜).FullSubcategory}
    (hX : Indecomposable X) (d : ℤ) :
    Indecomposable (⟨X.obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj X.property d⟩ :
      (gradedFiniteProjectiveModules 𝒜).FullSubcategory) := by
  let F := (gradedFiniteProjectiveModules 𝒜).lift
    ((gradedFiniteProjectiveModules 𝒜).ι ⋙ GradedModuleCat.shiftFunctor d)
    fun X ↦ gradedFiniteProjectiveModules_shiftObj X.property d
  -- The shift leaves underlying linear maps unchanged (`GradedModuleCat.hom_shiftFunctor_map`),
  -- so `F.map f` and `f` have the same underlying map, and comparing those is `rfl`.
  refine F.indecomposable_obj_of_map_bijective hX ⟨fun f g h ↦ ?_, fun g ↦ ?_⟩
  · exact ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext (congrArg (fun φ ↦ φ.hom.hom) h))
  · -- A degree-zero map of `X{d}` is a degree-zero map of `X`.
    refine ⟨ObjectProperty.homMk (GradedModuleCat.ofHom g.hom.hom <|
      LinearMap.isHomogeneous_def.2 fun p x hx ↦ ?_),
      ObjectProperty.hom_ext _ (GradedModuleCat.hom_ext rfl)⟩
    have hx' : x ∈ (X.obj.shiftObj d).grading.piece (p + d) := by
      rw [GradedModuleCat.mem_shiftObj_piece_iff, add_sub_cancel_right]
      exact hx
    have := GradedModuleCat.map_mem (M := X.obj.shiftObj d) (N := X.obj.shiftObj d) g.hom hx'
    rwa [GradedModuleCat.mem_shiftObj_piece_iff, add_sub_cancel_right, ← add_zero p] at this

variable [Module.Finite k A]

/-- **Graded maps between finite graded projectives over a finite-dimensional algebra form a
finite-dimensional space**, as graded maps between finite-dimensional graded modules. -/
instance (X Y : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    Module.Finite k (X ⟶ Y) := by
  have : Module.Finite k X.obj := Module.Finite.trans A X.obj
  have : Module.Finite k Y.obj := Module.Finite.trans A Y.obj
  exact Module.Finite.equiv InducedCategory.homLinearEquiv.symm

/-- An indecomposable finite graded projective has a local endomorphism ring. -/
private theorem isLocalRing_end {X : (gradedFiniteProjectiveModules 𝒜).FullSubcategory}
    (hX : Indecomposable X) : IsLocalRing (End X) :=
  isLocalRing_end_of_indecomposable (k := k) hX

/-- A nonzero finite graded projective is not isomorphic to a nontrivial shift of itself
(`TauCeti.GradedModuleCat.eq_zero_of_iso_shiftObj`). -/
private theorem isEmpty_iso_shiftObj (X : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (hX : ¬IsZero X) {d : ℤ} (hd : d ≠ 0) :
    IsEmpty (X ≅ ⟨X.obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj X.property d⟩) := by
  refine ⟨fun e ↦ hd ?_⟩
  have : Module.Finite k X.obj := Module.Finite.trans A X.obj
  have : Nontrivial X.obj := not_subsingleton_iff_nontrivial.1 fun _ ↦ hX <|
    (IsZero.iff_id_eq_zero X).2 <| ObjectProperty.hom_ext _ <|
      GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ Subsingleton.elim _ _)
  exact X.obj.eq_zero_of_iso_shiftObj (k := k) ((gradedFiniteProjectiveModules 𝒜).ι.mapIso e)

variable [DirectSum.Decomposition 𝒜]

/-- For a fixed finite graded projective `Y`, the dimension of `(X ⟶ Y) / rad(X, Y)` as an
invariant of `X`; it is additive on conflations, which split. -/
private noncomputable def radicalInvariant (Y : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    ExactK0.AdditiveInvariant (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure ℤ
    where
  obj X := Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y)
  map_conflation S hS := by
    rw [gradedFiniteProjectiveModulesExactStructure_eq_split, ExactStructure.split_conflation]
      at hS
    obtain ⟨σ⟩ := hS
    rw [finrank_quotient_jacobsonRadicalSubmodule_congr k σ.isoBinaryBiproduct (Iso.refl Y),
      finrank_quotient_jacobsonRadicalSubmodule_biprod, Nat.cast_add]

/-- The coordinate on `K₀^gr(proj A)` attached to `Y` by `radicalInvariant`. -/
private noncomputable def radicalCoordinate
    (Y : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →+ ℤ :=
  (ExactK0.lift (radicalInvariant (k := k) Y) :
      ExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜).toExactStructure →+ ℤ).comp
    (LaurentK0.ofExactK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)).symm.toAddMonoidHom

private theorem radicalCoordinate_of (Y X : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    radicalCoordinate (k := k) Y (LaurentK0.of.{uA} _ X) =
      Module.finrank k ((X ⟶ Y) ⧸ jacobsonRadicalSubmodule k X Y) := by
  rw [radicalCoordinate, AddMonoidHom.comp_apply, ← LaurentK0.ofExactK0_exactK0_of,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply, ExactK0.lift_of]
  rfl

variable (P : I → (gradedFiniteProjectiveModules 𝒜).FullSubcategory)

/-- On a Laurent multiple `c • [P j]`, the coordinate attached to `P i` is the constant
coefficient of `c` times `dim (P i ⟶ P i) / rad` when `j = i`, and zero otherwise. -/
private theorem radicalCoordinate_smul_of [DecidableEq I] (hind : ∀ i, Indecomposable (P i))
    (hnoniso : Pairwise fun i j ↦ ∀ d, IsEmpty (P i ≅
      ⟨(P j).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P j).property d⟩))
    (i j : I) (c : LaurentPolynomial ℤ) :
    radicalCoordinate (k := k) (P i) (c • LaurentK0.of.{uA} _ (P j)) =
      if j = i then c.coeff 0 *
        Module.finrank k ((P i ⟶ P i) ⧸ jacobsonRadicalSubmodule k (P i) (P i)) else 0 := by
  induction c using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_smul, map_add, hp, hq]
    split_ifs <;> simp [add_mul]
  | C_mul_T n a =>
    have := isLocalRing_end (k := k) (hind i)
    have := isLocalRing_end (k := k) (indecomposable_shiftObj (hind j) n)
    rw [mul_smul, ← laurentK0_projective_of_shiftObj, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, LaurentPolynomial.C_eq_algebraMap,
      algebraMap_smul, map_zsmul, radicalCoordinate_of, smul_eq_mul]
    by_cases hji : j = i
    · subst hji
      by_cases hn : n = 0
      · subst hn
        rw [finrank_quotient_jacobsonRadicalSubmodule_congr k
          (ObjectProperty.isoMk _ ((GradedModuleCat.shiftFunctorZeroIso 𝒜).app (P j).obj))
          (Iso.refl _)]
        simp
      · rw [finrank_quotient_jacobsonRadicalSubmodule_eq_zero k
          ⟨fun e ↦ (isEmpty_iso_shiftObj (P j) (hind j).1 hn).false e.symm⟩]
        simp [hn]
    · rw [finrank_quotient_jacobsonRadicalSubmodule_eq_zero k
        ⟨fun e ↦ (hnoniso (Ne.symm hji) n).false e.symm⟩]
      simp [hji]

/-- **Indecomposable graded projectives which are pairwise non-isomorphic up to shift have
`ℤ[q,q⁻¹]`-linearly independent classes in `K₀^gr(proj A)`.** The hypothesis only compares
distinct indices: a nonzero finite graded projective is never isomorphic to a nontrivial shift of
itself. -/
theorem linearIndependent_laurentK0_projective (hind : ∀ i, Indecomposable (P i))
    (hnoniso : Pairwise fun i j ↦ ∀ d, IsEmpty (P i ≅
      ⟨(P j).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P j).property d⟩)) :
    LinearIndependent (LaurentPolynomial ℤ)
      fun i ↦ LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i) := by
  classical
  refine linearIndependent_iff'.2 fun s g hg i hi ↦ AddMonoidAlgebra.ext (Finsupp.ext fun e ↦ ?_)
  -- Multiply the relation by `q⁻ᵉ` and read off the coordinate attached to `P i`.
  have h := congrArg (fun x ↦ radicalCoordinate (k := k) (P i)
    ((LaurentPolynomial.T (-e) : LaurentPolynomial ℤ) • x)) hg
  simp only [Finset.smul_sum, smul_smul, map_sum, smul_zero, map_zero,
    radicalCoordinate_smul_of (k := k) P hind hnoniso, Finset.sum_ite_eq', hi, ite_true] at h
  have := isLocalRing_end (k := k) (hind i)
  have hpos := finrank_quotient_jacobsonRadicalSubmodule_self_pos k (P i)
  rw [LaurentPolynomial.T, AddMonoidAlgebra.coeff_single_mul_eq_mul_coeff e fun _ _ ↦ by omega,
    one_mul] at h
  simpa [hpos.ne'] using h

/-- **The indecomposable graded projective basis of `K₀^gr(proj A)`.** A family of indecomposable
finite graded projectives which is pairwise non-isomorphic up to shift and meets every
indecomposable finite graded projective up to shift gives a `ℤ[q,q⁻¹]`-basis of the Laurent
Grothendieck group, whose basis vector at `i` is the class `[P i]`. -/
noncomputable def gradedIndecomposableProjectiveClassBasis (hind : ∀ i, Indecomposable (P i))
    (hnoniso : Pairwise fun i j ↦ ∀ d, IsEmpty (P i ≅
      ⟨(P j).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P j).property d⟩))
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P) :
    Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :=
  Module.Basis.mk (linearIndependent_laurentK0_projective P hind hnoniso)
    (span_range_laurentK0_projective_of_eq_top P hP).ge

/-- The basis vector of `TauCeti.gradedIndecomposableProjectiveClassBasis` at `i` is `[P i]`. -/
@[simp]
theorem gradedIndecomposableProjectiveClassBasis_apply (hind : ∀ i, Indecomposable (P i))
    (hnoniso : Pairwise fun i j ↦ ∀ d, IsEmpty (P i ≅
      ⟨(P j).obj.shiftObj d, gradedFiniteProjectiveModules_shiftObj (P j).property d⟩))
    (hP : IsExhaustiveGradedIndecomposableProjectiveFamily P) (i : I) :
    gradedIndecomposableProjectiveClassBasis P hind hnoniso hP i =
      LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) (P i) :=
  Module.Basis.mk_apply _ _ i

end Independence

end TauCeti
