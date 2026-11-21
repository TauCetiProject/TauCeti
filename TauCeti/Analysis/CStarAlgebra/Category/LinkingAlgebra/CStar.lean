/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.Analysis.CStarAlgebra.Category.LinkingAlgebra.Basic
public import TauCeti.Analysis.StarAlgebra.GNS.Bounded

import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import TauCeti.Analysis.CStarAlgebra.State.Spectrum
import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# C*-algebra structure and matrix positivity on finite linking algebras

For a C*-category `C` and a finite family of objects `X : ι → C`, every positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ` pulls back to a `StarPositiveFunctional`
`LinkingAlgebra.cornerFunctional X k φ` on `TauCeti.LinkingAlgebra X`. Every matrix unit acts
boundedly on its GNS space (by `CStarCategory.comp_self_comp_dagger_le`), so
`TauCeti.StarPositiveFunctional.boundedRepresentation` yields a unital star-representation
`LinkingAlgebra.gnsRep X k φ`. Taking the supremum of operator norms over all `(k, φ)` equips
`LinkingAlgebra X` with a `CStarAlgebra` structure whose norm satisfies
`‖A.entry i j‖ ≤ ‖A‖ ≤ ∑ i, ∑ j, ‖A.entry i j‖` and `‖single X i j f‖ = ‖f‖`.

From this we obtain isometric corner identifications
`cornerSubmodule X ℂ i j ≃ₗᵢ[ℂ] (X j ⟶ X i)`, isometric order-embedding diagonal
maps `diagHom X ℂ i : End (X i) →⋆ₙₐ[ℂ] LinkingAlgebra X`, the matrix positivity criterion
`LinkingAlgebra.nonneg_iff`, and recovery of the Hom norm and endomorphism positivity from
two-object corners `LinkingAlgebra ![X, Y]`.

## References

* P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*, Pacific J. Math. 120 (1985), 79–109,
  Section 1.
-/

public section

open CategoryTheory
open scoped ComplexOrder InnerProductSpace

universe v u

namespace TauCeti

namespace LinkingAlgebra

/-! ### Corner positive functionals, GNS representations, and C*-algebra structure -/

section CStar

open scoped _root_.CStarAlgebra

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {ι : Type} [Fintype ι]

variable (X : ι → C)

section GNS

variable (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ)

/-- The `StarPositiveFunctional` on `LinkingAlgebra X` obtained by composing a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ` with extraction of the `(k, k)` diagonal corner. -/
def cornerFunctional : StarPositiveFunctional (LinkingAlgebra X) where
  toLinearMap :=
    { toFun A := φ (End.of (A.entry k k))
      map_add' A B := by simp only [add_entry, End.of_add, map_add]
      map_smul' c A := by simp only [smul_entry, End.of_smul, map_smul, RingHom.id_apply] }
  square_nonneg A := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_entry, star_entry, End.of_sum, map_sum]
    exact Finset.sum_nonneg fun j _ =>
      φ.map_nonneg (End.self_comp_dagger_nonneg (A.entry j k))

@[simp] theorem cornerFunctional_apply (A : LinkingAlgebra X) :
    cornerFunctional X k φ A = φ (End.of (A.entry k k)) := (rfl)

private theorem cornerFunctional_single_bound [DecidableEq ι]
    (i j : ι) (f : X j ⟶ X i) (B : LinkingAlgebra X) :
    cornerFunctional X k φ (star B * star (single X i j f) * single X i j f * B) ≤
      (‖f‖ : ℂ) ^ 2 * cornerFunctional X k φ (star B * B) := by
  have hprod_entry (m : ι) :
      (single X i j f * B).entry m k =
        if hm : m = i then B.entry j k ≫ f ≫ eqToHom (congrArg X hm.symm) else 0 := by
    simp only [mul_entry]
    by_cases hm : m = i
    · subst hm
      rw [dite_eq_left rfl, Fintype.sum_eq_single j]
      · simp
      · intro l hl; simp [single_entry_of_ne_right X hl]
    · rw [dite_eq_right hm]
      exact Finset.sum_eq_zero fun l _ => by simp [single_entry_of_ne_left X hm]
  have hlhs :
      End.of ((star B * star (single X i j f) * single X i j f * B).entry k k) =
        End.of ((B.entry j k ≫ f) ≫ dagger (B.entry j k ≫ f)) := by
    have hassoc : star B * star (single X i j f) * single X i j f * B =
        star (single X i j f * B) * (single X i j f * B) := by
      simp only [star_mul, mul_assoc]
    rw [hassoc, mul_entry]
    simp only [star_entry]
    rw [Fintype.sum_eq_single i]
    · have hi := hprod_entry i
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id] at hi
      rw [hi]
    · intro m hm; rw [hprod_entry m, dite_eq_right hm]; simp
  have hle_end :
      End.of ((star B * star (single X i j f) * single X i j f * B).entry k k) ≤
        (‖f‖ ^ 2 : ℝ) • End.of ((star B * B).entry k k) := by
    rw [hlhs]
    simp only [mul_entry, star_entry, End.of_sum]
    refine (CStarCategory.comp_self_comp_dagger_le (B.entry j k) f).trans ?_
    refine smul_le_smul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum
      (fun m _ => End.self_comp_dagger_nonneg (B.entry m k)) (Finset.mem_univ j)
  have hφ := OrderHomClass.mono φ hle_end
  rw [LinearMapClass.map_smul_of_tower, Complex.real_smul, Complex.ofReal_pow] at hφ
  exact hφ

private theorem continuous_leftMul_single [DecidableEq ι] (i j : ι) (f : X j ⟶ X i) :
    Continuous ((cornerFunctional X k φ).leftMul (single X i j f)) :=
  ((cornerFunctional X k φ).continuous_leftMul_iff _).mpr
    ⟨‖f‖, CStarCategory.norm_nonneg f, cornerFunctional_single_bound X k φ i j f⟩

/-- Every element of `LinkingAlgebra X` acts continuously on the algebraic GNS space of
`cornerFunctional X k φ`. -/
theorem continuous_leftMul_cornerFunctional (A : LinkingAlgebra X) :
    Continuous ((cornerFunctional X k φ).leftMul A) := by
  classical
  rw [← (cornerFunctional X k φ).mem_boundedSubalgebra, eq_sum_single X A]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [(cornerFunctional X k φ).mem_boundedSubalgebra]
  exact continuous_leftMul_single X k φ i j (A.entry i j)

/-- The completed GNS Hilbert space of `LinkingAlgebra X` associated to a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`. Defined as `def` rather than `abbrev` because
operator-norm rewrites and `NegPart` synthesis on `(cornerFunctional X k φ).HilbertGNS →L[ℂ] ...`
time out unfolding `UniformSpace.Completion (SeparationQuotient PreGNS)`. -/
def GNS : Type v :=
  (cornerFunctional X k φ).HilbertGNS

noncomputable instance instGNSNormedAddCommGroup : NormedAddCommGroup (GNS X k φ) :=
  inferInstanceAs (NormedAddCommGroup (cornerFunctional X k φ).HilbertGNS)

noncomputable instance instGNSInnerProductSpace : InnerProductSpace ℂ (GNS X k φ) :=
  inferInstanceAs (InnerProductSpace ℂ (cornerFunctional X k φ).HilbertGNS)

instance instGNSCompleteSpace : CompleteSpace (GNS X k φ) :=
  inferInstanceAs (CompleteSpace (cornerFunctional X k φ).HilbertGNS)

/-- The canonical linear isometry equivalence identifying `GNS X k φ` with
`(cornerFunctional X k φ).HilbertGNS`. -/
noncomputable def gnsEquiv : GNS X k φ ≃ₗᵢ[ℂ] (cornerFunctional X k φ).HilbertGNS where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- The canonical linear map sending an element of `LinkingAlgebra X` to its class in
`GNS X k φ`. -/
noncomputable def gnsClassMap : LinkingAlgebra X →ₗ[ℂ] GNS X k φ :=
  (gnsEquiv X k φ).symm.toLinearMap.comp (cornerFunctional X k φ).hilbertClassMap

/-- The canonical cyclic vector represented by `1` in `GNS X k φ`. -/
noncomputable def gnsCyclicVector : GNS X k φ :=
  (gnsEquiv X k φ).symm (cornerFunctional X k φ).hilbertCyclicVector

@[simp] theorem gnsEquiv_gnsClassMap (A : LinkingAlgebra X) :
    gnsEquiv X k φ (gnsClassMap X k φ A) = (cornerFunctional X k φ).hilbertClassMap A := (rfl)

@[simp] theorem gnsEquiv_gnsCyclicVector :
    gnsEquiv X k φ (gnsCyclicVector X k φ) = (cornerFunctional X k φ).hilbertCyclicVector := (rfl)

@[simp] theorem inner_gnsClassMap (A B : LinkingAlgebra X) :
    ⟪gnsClassMap X k φ A, gnsClassMap X k φ B⟫_ℂ = cornerFunctional X k φ (star A * B) :=
  (cornerFunctional X k φ).inner_hilbertClassMap A B

theorem norm_gnsClassMap_sq (A : LinkingAlgebra X) :
    ‖gnsClassMap X k φ A‖ ^ 2 = (cornerFunctional X k φ (star A * A)).re :=
  (cornerFunctional X k φ).norm_hilbertClassMap_sq A

theorem norm_gnsCyclicVector (hφ : φ 1 = 1) : ‖gnsCyclicVector X k φ‖ = 1 :=
  (cornerFunctional X k φ).norm_hilbertCyclicVector (by simpa using hφ)

/-- Algebra classes are dense in `GNS X k φ`. -/
theorem denseRange_gnsClassMap : DenseRange (gnsClassMap X k φ) :=
  (gnsEquiv X k φ).symm.surjective.denseRange.comp
    (cornerFunctional X k φ).denseRange_hilbertClassMap (gnsEquiv X k φ).symm.continuous

/-- The canonical unital GNS star-representation of `LinkingAlgebra X` induced by a positive linear
functional `φ : End (X k) →ₚ[ℂ] ℂ`, built via
`TauCeti.StarPositiveFunctional.boundedRepresentation`. -/
noncomputable def gnsRep : LinkingAlgebra X →⋆ₐ[ℂ] (GNS X k φ →L[ℂ] GNS X k φ) :=
  (cornerFunctional X k φ).boundedRepresentation (continuous_leftMul_cornerFunctional X k φ)

/-- Transporting `gnsRep X k φ A` along `gnsEquiv X k φ` recovers the Hilbert GNS
left-multiplication operator of `cornerFunctional X k φ`. -/
theorem gnsEquiv_gnsRep_apply (A : LinkingAlgebra X) (x : GNS X k φ) :
    gnsEquiv X k φ (gnsRep X k φ A x) =
      (cornerFunctional X k φ).hilbertLeftMul (continuous_leftMul_cornerFunctional X k φ A)
        (gnsEquiv X k φ x) :=
  congrArg (fun T => T (gnsEquiv X k φ x))
    ((cornerFunctional X k φ).boundedRepresentation_apply _ A)

/-- Action of `gnsRep X k φ` on `gnsClassMap X k φ`. -/
@[simp] theorem gnsRep_gnsClassMap (A B : LinkingAlgebra X) :
    gnsRep X k φ A (gnsClassMap X k φ B) = gnsClassMap X k φ (A * B) :=
  (cornerFunctional X k φ).boundedRepresentation_hilbertClassMap _ A B

/-- Action of `gnsRep X k φ` on `gnsCyclicVector X k φ`. -/
@[simp] theorem gnsRep_gnsCyclicVector (A : LinkingAlgebra X) :
    gnsRep X k φ A (gnsCyclicVector X k φ) = gnsClassMap X k φ A :=
  (cornerFunctional X k φ).boundedRepresentation_hilbertCyclicVector _ A

/-- Operator-norm bound for `gnsRep X k φ A` in terms of the quadratic form of
`cornerFunctional X k φ`. -/
theorem norm_gnsRep_le_iff (A : LinkingAlgebra X) {R : ℝ} (hR : 0 ≤ R) :
    ‖gnsRep X k φ A‖ ≤ R ↔
      ∀ B : LinkingAlgebra X,
        cornerFunctional X k φ (star B * star A * A * B) ≤
          (R : ℂ) ^ 2 * cornerFunctional X k φ (star B * B) := by
  rw [← (cornerFunctional X k φ).norm_hilbertLeftMul_le_iff
    (continuous_leftMul_cornerFunctional X k φ A) hR,
    ContinuousLinearMap.opNorm_le_iff hR, ContinuousLinearMap.opNorm_le_iff hR]
  refine ⟨fun h y => ?_, fun h x => ?_⟩
  · have hy := h ((gnsEquiv X k φ).symm y)
    rw [← (gnsEquiv X k φ).norm_map, gnsEquiv_gnsRep_apply,
      (gnsEquiv X k φ).apply_symm_apply, (gnsEquiv X k φ).symm.norm_map] at hy
    exact hy
  · simpa only [← gnsEquiv_gnsRep_apply, LinearIsometryEquiv.norm_map] using
      h (gnsEquiv X k φ x)

private theorem norm_gnsRep_single_le [DecidableEq ι] (i j : ι) (f : X j ⟶ X i) :
    ‖gnsRep X k φ (single X i j f)‖ ≤ ‖f‖ :=
  (norm_gnsRep_le_iff X k φ (single X i j f) (CStarCategory.norm_nonneg f)).mpr
    (cornerFunctional_single_bound X k φ i j f)

private theorem norm_gnsRep_le_sum (A : LinkingAlgebra X) :
    ‖gnsRep X k φ A‖ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ := by
  classical
  calc ‖gnsRep X k φ A‖
      = ‖∑ i : ι, ∑ j : ι, gnsRep X k φ (single X i j (A.entry i j))‖ := by
          conv_lhs => rw [eq_sum_single X A]
          simp only [map_sum]
    _ ≤ ∑ i : ι, ‖∑ j : ι, gnsRep X k φ (single X i j (A.entry i j))‖ := norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖gnsRep X k φ (single X i j (A.entry i j))‖ :=
          Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
            norm_gnsRep_single_le X k φ i j (A.entry i j)

end GNS

/-- The C*-norm on `LinkingAlgebra X`, defined as the supremum of operator norms over all GNS
representations induced by positive linear functionals on `End (X k)`. -/
noncomputable instance instNorm : Norm (LinkingAlgebra X) where
  norm A := ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖

variable {X}

/-- Definitional formula for the C*-norm on `LinkingAlgebra X`. -/
theorem norm_def (A : LinkingAlgebra X) :
    ‖A‖ = ⨆ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖ := (rfl)

private theorem bddAbove_gnsRep_inner (k : ι) (A : LinkingAlgebra X) :
    BddAbove (Set.range fun φ : End (X k) →ₚ[ℂ] ℂ => ‖gnsRep X k φ A‖) :=
  ⟨∑ i : ι, ∑ j : ι, ‖A.entry i j‖, by rintro _ ⟨φ, rfl⟩; exact norm_gnsRep_le_sum X k φ A⟩

private theorem bddAbove_gnsRep_outer (A : LinkingAlgebra X) :
    BddAbove (Set.range fun k : ι => ⨆ φ : End (X k) →ₚ[ℂ] ℂ, ‖gnsRep X k φ A‖) :=
  ⟨∑ i : ι, ∑ j : ι, ‖A.entry i j‖, by
    rintro _ ⟨k, rfl⟩
    exact Real.iSup_le (fun φ => norm_gnsRep_le_sum X k φ A)
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => CStarCategory.norm_nonneg _)⟩

/-- The norm of `A` in `LinkingAlgebra X` dominates every GNS operator norm `‖gnsRep X k φ A‖`. -/
theorem norm_gnsRep_le (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) (A : LinkingAlgebra X) :
    ‖gnsRep X k φ A‖ ≤ ‖A‖ :=
  (le_ciSup (bddAbove_gnsRep_inner k A) φ).trans (le_ciSup (bddAbove_gnsRep_outer A) k)

/-- Upper bound for the C*-norm on `LinkingAlgebra X` from a uniform bound on all GNS
representations. -/
theorem norm_le_of_forall_gnsRep {A : LinkingAlgebra X} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), ‖gnsRep X k φ A‖ ≤ M) : ‖A‖ ≤ M :=
  Real.iSup_le (fun k => Real.iSup_le (fun φ => h k φ) hM) hM

/-- The C*-norm on `LinkingAlgebra X` is bounded above by the entrywise `ℓ¹` norm. -/
theorem norm_le_sum_norm_entry (A : LinkingAlgebra X) :
    ‖A‖ ≤ ∑ i : ι, ∑ j : ι, ‖A.entry i j‖ :=
  norm_le_of_forall_gnsRep
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => CStarCategory.norm_nonneg _)
    (fun k φ => norm_gnsRep_le_sum X k φ A)

/-- Every matrix entry has norm bounded by the C*-norm of the linking-algebra element. -/
theorem norm_entry_le (A : LinkingAlgebra X) (i j : ι) : ‖A.entry i j‖ ≤ ‖A‖ := by
  have hA_nn : 0 ≤ ‖A‖ := (norm_nonneg (gnsRep X j 0 A)).trans (norm_gnsRep_le j 0 A)
  by_cases h0 : A.entry i j = 0
  · rw [h0, CStarCategory.norm_zero]; exact hA_nn
  · let a : End (X j) := End.of (A.entry i j ≫ dagger (A.entry i j))
    have ha_nn : 0 ≤ a := End.self_comp_dagger_nonneg (A.entry i j)
    have ha_ne : a ≠ 0 := fun h =>
      h0 ((CStarCategory.self_comp_dagger_eq_zero (A.entry i j)).mp (congrArg End.asHom h))
    have : Nontrivial (End (X j)) := nontrivial_of_ne a 0 ha_ne
    obtain ⟨φ₀, hφ1, -, hφa⟩ :=
      TauCeti.CStarAlgebra.exists_positiveContinuousLinearMap_apply_eq_norm ha_nn
    let φ : End (X j) →ₚ[ℂ] ℂ := φ₀.toPositiveLinearMap
    have hcyc : ‖gnsCyclicVector X j φ‖ = 1 := norm_gnsCyclicVector X j φ hφ1
    have hge : ‖A.entry i j‖ ^ 2 ≤ ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖ ^ 2 := by
      rw [gnsRep_gnsCyclicVector, norm_gnsClassMap_sq]
      simp only [cornerFunctional_apply, mul_entry, star_entry, End.of_sum, map_sum, Complex.re_sum]
      have hterm : ‖A.entry i j‖ ^ 2 = (φ (End.of (A.entry i j ≫ dagger (A.entry i j)))).re := by
        simpa only [a, φ, PositiveContinuousLinearMap.coe_toPositiveLinearMap, End.norm_of,
          CStarCategory.norm_self_comp_dagger, Complex.ofReal_re] using
          (congrArg Complex.re hφa).symm
      rw [hterm]
      exact Finset.single_le_sum (fun m _ =>
        (RCLike.nonneg_iff.mp (φ.map_nonneg
          (End.self_comp_dagger_nonneg (A.entry m j)))).1) (Finset.mem_univ i)
    have hle : ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖ ≤ ‖A‖ :=
      calc ‖gnsRep X j φ A (gnsCyclicVector X j φ)‖
          ≤ ‖gnsRep X j φ A‖ * ‖gnsCyclicVector X j φ‖ := (gnsRep X j φ A).le_opNorm _
        _ = ‖gnsRep X j φ A‖ := by rw [hcyc, mul_one]
        _ ≤ ‖A‖ := norm_gnsRep_le j φ A
    exact (sq_le_sq₀ (CStarCategory.norm_nonneg _) hA_nn).mp
      (hge.trans (pow_le_pow_left₀ (norm_nonneg _) hle 2))

private theorem norm_nonneg_aux (A : LinkingAlgebra X) : 0 ≤ ‖A‖ := by
  rw [norm_def]; exact Real.iSup_nonneg fun k => Real.iSup_nonneg fun φ => norm_nonneg _

private theorem norm_neg_le_aux (A : LinkingAlgebra X) : ‖-A‖ ≤ ‖A‖ := by
  refine norm_le_of_forall_gnsRep (norm_nonneg_aux A) fun k φ => ?_
  rw [map_neg, norm_neg]; exact norm_gnsRep_le k φ A

private theorem norm_neg_aux (A : LinkingAlgebra X) : ‖-A‖ = ‖A‖ :=
  le_antisymm (norm_neg_le_aux A) (by simpa only [neg_neg] using norm_neg_le_aux (-A))

private theorem norm_add_le_aux (A B : LinkingAlgebra X) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := by
  refine norm_le_of_forall_gnsRep (add_nonneg (norm_nonneg_aux A) (norm_nonneg_aux B)) fun k φ => ?_
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add (norm_gnsRep_le k φ A) (norm_gnsRep_le k φ B))

/-- The normed ring structure on `LinkingAlgebra X`, reusing the native `Ring` instance. -/
noncomputable instance instNormedRing : NormedRing (LinkingAlgebra X) where
  toNorm := instNorm X
  toRing := instRing
  dist A B := ‖A - B‖
  dist_self A := by
    rw [sub_self]
    exact le_antisymm (by simpa using norm_le_sum_norm_entry (0 : LinkingAlgebra X))
      (norm_nonneg_aux 0)
  dist_comm A B := by rw [← neg_sub, norm_neg_aux]
  dist_triangle A B D := by
    simpa only [sub_add_sub_cancel] using norm_add_le_aux (A - B) (B - D)
  eq_of_dist_eq_zero {A B} h := by
    apply sub_eq_zero.mp; ext i j; rw [zero_entry]
    exact CStarCategory.norm_eq_zero.mp
      (le_antisymm ((norm_entry_le (A - B) i j).trans_eq h) (CStarCategory.norm_nonneg _))
  dist_eq A B := by rw [neg_add_eq_sub, ← neg_sub, norm_neg_aux]
  norm_mul_le A B := by
    refine norm_le_of_forall_gnsRep (mul_nonneg (norm_nonneg_aux A) (norm_nonneg_aux B))
      fun k φ => ?_
    rw [map_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (norm_gnsRep_le k φ A) (norm_gnsRep_le k φ B)
      (norm_nonneg _) (norm_nonneg_aux A))

/-- The normed `ℂ`-algebra structure on `LinkingAlgebra X`, reusing the native `Algebra ℂ`
instance. -/
noncomputable instance instNormedAlgebra : NormedAlgebra ℂ (LinkingAlgebra X) where
  toAlgebra := instAlgebra
  norm_smul_le c A := by
    refine norm_le_of_forall_gnsRep (mul_nonneg (norm_nonneg c) (norm_nonneg A)) fun k φ => ?_
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_gnsRep_le k φ A) (norm_nonneg c)

/-- Finite linking algebras of a C*-category are complete. -/
instance instCompleteSpace : CompleteSpace (LinkingAlgebra X) :=
  Metric.complete_of_cauchySeq_tendsto fun u hu => by
    have hcoord (i j : ι) :
        letI := CStarCategory.normedAddCommGroup (X j) (X i)
        CauchySeq fun n => (u n).entry i j := by
      let := CStarCategory.normedAddCommGroup (X j) (X i)
      rw [Metric.cauchySeq_iff] at hu ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hu ε hε
      refine ⟨N, fun m hm n hn => ?_⟩
      rw [dist_eq_norm, ← sub_entry]
      exact (norm_entry_le (u m - u n) i j).trans_lt
        (by simpa only [dist_eq_norm] using hN m hm n hn)
    have hconv (i j : ι) : ∃ l : X j ⟶ X i,
        Filter.Tendsto (fun n => ‖(u n).entry i j - l‖) Filter.atTop (nhds 0) := by
      let := CStarCategory.normedAddCommGroup (X j) (X i)
      have : CompleteSpace (X j ⟶ X i) := CStarCategory.completeSpace (X j) (X i)
      obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (hcoord i j)
      exact ⟨l, tendsto_iff_norm_sub_tendsto_zero.mp hl⟩
    choose L hL using hconv
    refine ⟨ofEntry L, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
    have hsum : Filter.Tendsto (fun n => ∑ i : ι, ∑ j : ι, ‖(u n).entry i j - L i j‖)
        Filter.atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using
        tendsto_finsetSum Finset.univ fun i _ =>
          tendsto_finsetSum Finset.univ fun j _ => hL i j
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hsum) ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h0 := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => CStarCategory.norm_nonneg _)] at h0
    exact (norm_le_sum_norm_entry (u n - ofEntry L)).trans_lt
      (by simpa only [sub_entry, ofEntry_entry] using h0)

/-- The C*-identity holds on `LinkingAlgebra X`. -/
instance instCStarRing : CStarRing (LinkingAlgebra X) where
  norm_mul_self_le A := by
    have hsqrt : ‖A‖ ≤ √‖star A * A‖ := by
      refine norm_le_of_forall_gnsRep (Real.sqrt_nonneg _) fun k φ => ?_
      refine Real.le_sqrt_of_sq_le ?_
      rw [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
      exact norm_gnsRep_le k φ (star A * A)
    calc ‖A‖ * ‖A‖ = ‖A‖ ^ 2 := (sq ‖A‖).symm
      _ ≤ (√‖star A * A‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsqrt 2
      _ = ‖star A * A‖ := Real.sq_sqrt (norm_nonneg _)

/-- Finite linking algebras of a C*-category are unital C*-algebras. -/
noncomputable instance instCStarAlgebra : CStarAlgebra (LinkingAlgebra X) where

/-- The spectral partial order on `LinkingAlgebra X`. -/
noncomputable instance instPartialOrder : PartialOrder (LinkingAlgebra X) :=
  CStarAlgebra.spectralOrder _

/-- Finite linking algebras of a C*-category are star-ordered rings under the spectral order. -/
instance instStarOrderedRing : StarOrderedRing (LinkingAlgebra X) :=
  CStarAlgebra.spectralOrderedRing _

/-! ### Corner identifications -/

section CornerIdentifications

variable [DecidableEq ι] (X)

/-- The matrix unit `single X i j f` has the same norm as its entry `f`. -/
@[simp] theorem norm_single (i j : ι) (f : X j ⟶ X i) : ‖single X i j f‖ = ‖f‖ :=
  le_antisymm
    (norm_le_of_forall_gnsRep (CStarCategory.norm_nonneg f) fun k φ =>
      norm_gnsRep_single_le X k φ i j f)
    (by simpa only [single_entry_self] using norm_entry_le (single X i j f) i j)

/-- The `(i, j)` matrix-unit embedding as a linear isometry
`(X j ⟶ X i) →ₗᵢ[ℂ] LinkingAlgebra X`. -/
def singleLinearIsometry (i j : ι) :
    letI := CStarCategory.normedAddCommGroup (X j) (X i)
    (X j ⟶ X i) →ₗᵢ[ℂ] LinkingAlgebra X :=
  letI := CStarCategory.normedAddCommGroup (X j) (X i)
  { toFun := single X i j
    map_add' := single_add X i j
    map_smul' := single_smul X i j
    norm_map' := norm_single X i j }

@[simp] theorem singleLinearIsometry_apply (i j : ι) (f : X j ⟶ X i) :
    singleLinearIsometry X i j f = single X i j f := (rfl)

/-- The `(i, j)` corner `cornerSubmodule X ℂ i j` is linearly isometrically equivalent to the Hom
space `X j ⟶ X i`. -/
def cornerLinearIsometryEquiv (i j : ι) :
    letI := CStarCategory.normedAddCommGroup (X j) (X i)
    cornerSubmodule X ℂ i j ≃ₗᵢ[ℂ] (X j ⟶ X i) :=
  letI := CStarCategory.normedAddCommGroup (X j) (X i)
  { toFun A := A.1.entry i j
    invFun f := ⟨single X i j f, by simp⟩
    left_inv A := by
      apply Subtype.ext
      simpa only [mem_cornerSubmodule, proj_mul_mul_proj] using A.2
    right_inv f := single_entry_self X i j f
    map_add' A B := add_entry A.1 B.1 i j
    map_smul' c A := smul_entry c A.1 i j
    norm_map' A := by
      have hA : A.1 = single X i j (A.1.entry i j) :=
        ((mem_cornerSubmodule X i j A.1).mp A.2).symm.trans (proj_mul_mul_proj X A.1 i j)
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      conv_rhs => rw [← Submodule.norm_coe, hA]
      exact (norm_single X i j (A.1.entry i j)).symm }

@[simp] theorem cornerLinearIsometryEquiv_apply (i j : ι) (A : cornerSubmodule X ℂ i j) :
    cornerLinearIsometryEquiv X i j A = A.1.entry i j := (rfl)

@[simp] theorem cornerLinearIsometryEquiv_symm_apply (i j : ι) (f : X j ⟶ X i) :
    letI := CStarCategory.normedAddCommGroup (X j) (X i)
    ((cornerLinearIsometryEquiv X i j).symm f).1 = single X i j f := (rfl)

/-- The diagonal embedding `diagHom X ℂ i : End (X i) →⋆ₙₐ[ℂ] LinkingAlgebra X` preserves norms. -/
theorem norm_diagHom (i : ι) (a : End (X i)) : ‖diagHom X ℂ i a‖ = ‖a‖ := by
  rw [diagHom_apply, norm_single, End.norm_def]

/-- The diagonal embedding `diagHom X ℂ i` is an isometry. -/
theorem isometry_diagHom (i : ι) : Isometry (diagHom X ℂ i) :=
  NonUnitalStarAlgHom.isometry (φ := diagHom X ℂ i) (diagHom_injective X i)

/-- The diagonal embedding `diagHom X ℂ i` preserves and reflects the spectral order. -/
theorem diagHom_le_iff (i : ι) {a b : End (X i)} :
    diagHom X ℂ i a ≤ diagHom X ℂ i b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (f := diagHom X ℂ i) (diagHom_injective X i)

/-- An endomorphism `a : End (X i)` is positive if and only if its image under `diagHom X ℂ i` is
positive in `LinkingAlgebra X`. -/
theorem diagHom_nonneg_iff (i : ι) {a : End (X i)} :
    0 ≤ diagHom X ℂ i a ↔ 0 ≤ a := by
  simpa only [map_zero] using diagHom_le_iff X i (a := 0) (b := a)

end CornerIdentifications

/-! ### Matrix positivity characterization -/

/-- A positive element `A` of `LinkingAlgebra X` defines a positive quadratic form
`v ↦ ∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` in `End Z` for every object `Z : C` and every
column `v : (j : ι) → (Z ⟶ X j)`. -/
theorem sum_comp_entry_comp_dagger_nonneg {A : LinkingAlgebra X} (hA : 0 ≤ A) {Z : C}
    (v : (j : ι) → (Z ⟶ X j)) :
    0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have hsum : ∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i) =
      ∑ m : ι, (∑ j : ι, v j ≫ B.entry m j) ≫ dagger (∑ i : ι, v i ≫ B.entry m i) := by
    have hentry (i j : ι) : A.entry i j = ∑ m : ι, B.entry m j ≫ dagger (B.entry m i) := by
      simpa only [mul_entry, star_entry] using
        congrArg (fun M : LinkingAlgebra X => M.entry i j) hB
    simp only [hentry, dagger_sum, dagger_comp, Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hsum, End.of_sum]
  exact Finset.sum_nonneg fun m _ => End.self_comp_dagger_nonneg _

/-- The family of GNS representations `gnsRep X k φ` is jointly faithful: an element that vanishes
under every `gnsRep X k φ` is zero. -/
theorem eq_zero_of_forall_gnsRep {A : LinkingAlgebra X}
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), gnsRep X k φ A = 0) : A = 0 := by
  rw [← norm_eq_zero]
  refine le_antisymm (norm_le_of_forall_gnsRep le_rfl fun k φ => ?_) (norm_nonneg _)
  rw [h k φ, norm_zero]

/-- An element of `LinkingAlgebra X` is positive in the spectral order if its image under every GNS
representation `gnsRep X k φ` is positive. -/
theorem nonneg_of_forall_gnsRep {A : LinkingAlgebra X}
    (h : ∀ (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ), 0 ≤ gnsRep X k φ A) : 0 ≤ A := by
  -- First show `A` is self-adjoint, then show its negative part `A⁻` vanishes in every GNS rep.
  have hsa : IsSelfAdjoint A := by
    rw [IsSelfAdjoint, ← sub_eq_zero]
    refine eq_zero_of_forall_gnsRep fun k φ => ?_
    simp only [map_sub, map_star, (h k φ).isSelfAdjoint.star_eq, sub_self]
  have hneg : A⁻ = 0 := by
    refine eq_zero_of_forall_gnsRep fun k φ => ?_
    have hmap : gnsRep X k φ (A⁻) = (gnsRep X k φ A)⁻ := by
      rw [CFC.negPart_def, CFC.negPart_def]
      exact NonUnitalStarAlgHomClass.map_cfcₙ (gnsRep X k φ) (·⁻ : ℝ → ℝ) A
    rw [hmap, (CFC.negPart_eq_zero_iff (gnsRep X k φ A)).mpr (h k φ)]
  exact (CFC.negPart_eq_zero_iff A hsa).mp hneg

private theorem gnsRep_nonneg_of_forall_sum_nonneg {A : LinkingAlgebra X}
    (hquad : ∀ (k : ι) (v : (j : ι) → (X k ⟶ X j)),
      0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)))
    (k : ι) (φ : End (X k) →ₚ[ℂ] ℂ) : 0 ≤ gnsRep X k φ A := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  have hnn : 0 ≤ ⟪gnsRep X k φ A x, x⟫_ℂ := by
    refine (denseRange_gnsClassMap X k φ).induction_on x
      (isClosed_le continuous_const (by fun_prop)) fun B => ?_
    have h0 : 0 ≤ ⟪gnsClassMap X k φ B, gnsRep X k φ A (gnsClassMap X k φ B)⟫_ℂ := by
      simp only [gnsRep_gnsClassMap, inner_gnsClassMap, cornerFunctional_apply,
        mul_entry, star_entry, Preadditive.sum_comp, Category.assoc]
      exact φ.map_nonneg (hquad k fun j => B.entry j k)
    rw [← inner_conj_symm, ← Complex.star_def, h0.isSelfAdjoint.star_eq]
    exact h0
  obtain ⟨hre, him⟩ := Complex.le_def.mp hnn
  exact ⟨Complex.ext rfl (by simpa using him), hre⟩

/-- Matrix positivity in a C*-category: an element `A : LinkingAlgebra X` is positive in the
spectral order if and only if every quadratic form
`∑ i, ∑ j, v j ≫ A.entry i j ≫ dagger (v i)` is positive in `End (X k)` for all `k : ι` and
`v : (j : ι) → (X k ⟶ X j)`. -/
theorem nonneg_iff {A : LinkingAlgebra X} :
    0 ≤ A ↔ ∀ (k : ι) (v : (j : ι) → (X k ⟶ X j)),
      0 ≤ End.of (∑ i : ι, ∑ j : ι, v j ≫ A.entry i j ≫ dagger (v i)) :=
  -- Forward: factor `A = star B * B`. Backward: positivity of quadratic forms makes every GNS
  -- representation `gnsRep X k φ A` positive, which forces `0 ≤ A` via `nonneg_of_forall_gnsRep`.
  ⟨fun hA _ v => sum_comp_entry_comp_dagger_nonneg hA v,
   fun hquad => nonneg_of_forall_gnsRep (gnsRep_nonneg_of_forall_sum_nonneg hquad)⟩

/-! ### Recovery of Hom norm and endomorphism positivity from two-object corners -/

/-- The Hom norm of `f : X ⟶ Y` is recovered as the C*-norm of the off-diagonal corner element
`single ![X, Y] 1 0 f` in the two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem norm_single_pair {X Y : C} (f : X ⟶ Y) :
    ‖single ![X, Y] (1 : Fin 2) 0 f‖ = ‖f‖ :=
  norm_single ![X, Y] 1 0 f

/-- Positivity in `End X` is recovered from positivity of its `(0, 0)` corner image in the
two-object linking algebra `LinkingAlgebra ![X, Y]`. -/
theorem end_nonneg_iff_diagHom_pair (X Y : C) (a : End X) :
    0 ≤ a ↔ 0 ≤ diagHom ![X, Y] ℂ 0 a :=
  (diagHom_nonneg_iff ![X, Y] 0).symm

end CStar

end LinkingAlgebra

end TauCeti
