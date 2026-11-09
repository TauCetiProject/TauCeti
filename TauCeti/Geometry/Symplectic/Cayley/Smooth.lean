/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cayley.Basic
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth compatible Cayley interpolation

The algebraic Cayley chart identifies tame complex structures with a convex ball of antilinear
endomorphisms, and compatible structures with its self-adjoint part. Here the inverse charts
are shown to preserve smooth parameter families, using the operator-norm topology on continuous
linear maps. This is needed when
extending prescribed almost complex structures across collars: convex interpolation must be
smooth as well as pointwise compatible.

`SymplecticForm.Compatible.cayleyPath` joins a compatible structure to any other compatible
structure, is constant for parameters at most zero and at least one, and is smooth on the
whole real line. Thus its endpoint jets of every positive order vanish. Smoothness is also
proved jointly with external parameters for families expressed in Cayley coordinates. In
operator-norm coordinates the path is the rational expression `TauCeti.cayleyPathFormula` in
its two endpoints, which commutes with algebra isomorphisms and is smooth jointly in the
parameter and both endpoints wherever its denominators are invertible.
Over a manifold of parameters, `SymplecticForm.Compatible.contMDiffAt_cayleyEquiv_symm` shows
that the inverse chart preserves smoothness, and conversely
`SymplecticForm.Tames.contMDiffAt_cayley` shows that the forward chart sends a smooth family of
tame structures to a smooth family of Cayley coordinates. These are linear, fixed-form
statements; no extension theorem for sections of a tangent bundle is asserted here.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart on compatible complex structures).
-/

public noncomputable section

open Set Real Manifold

namespace TauCeti

/-! ### The Cayley path as a rational expression -/

section Formula

variable {R : Type*} [Ring R] [Algebra ℝ R]

/-- The point at parameter `b` of the Cayley segment from `A` to `B`, that is
`A (1 + b C)(1 - b C)⁻¹` for the Cayley coordinate `C` of `B` relative to `A`. -/
def cayleyPathFormula (b : ℝ) (A B : R) : R :=
  A * (1 + b • cayleyFormula A B) * Ring.inverse (1 - b • cayleyFormula A B)

/-- The defining formula of the Cayley path expression. -/
lemma cayleyPathFormula_def (b : ℝ) (A B : R) :
    cayleyPathFormula b A B =
      A * (1 + b • cayleyFormula A B) * Ring.inverse (1 - b • cayleyFormula A B) := (rfl)

/-- Algebra isomorphisms commute with the Cayley path expression. -/
theorem map_cayleyPathFormula {S F : Type*} [Ring S] [Algebra ℝ S] [EquivLike F R S]
    [AlgEquivClass F ℝ R S] (f : F) (b : ℝ) (A B : R) :
    f (cayleyPathFormula b A B) = cayleyPathFormula b (f A) (f B) := by
  simp only [cayleyPathFormula_def, map_mul, map_add, map_one, map_smul, map_sub, map_ringInverse,
    map_cayleyFormula]

/-- The Cayley path expression is smooth in its parameter and both endpoints at any point where
its two denominators are invertible. -/
theorem contDiffAt_cayleyPathFormula {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    [CompleteSpace R] {n : WithTop ℕ∞} {b : ℝ} {A B : R} (h₁ : IsUnit (1 - A * B))
    (h₂ : IsUnit (1 - b • cayleyFormula A B)) :
    ContDiffAt ℝ n (fun q : ℝ × R × R ↦ cayleyPathFormula q.1 q.2.1 q.2.2) (b, A, B) := by
  have hA : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ q.2.1) (b, A, B) :=
    contDiffAt_fst.comp _ contDiffAt_snd
  have hB : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ q.2.2) (b, A, B) :=
    contDiffAt_snd.comp _ contDiffAt_snd
  have hAB := hA.mul hB
  have hC : ContDiffAt ℝ n (fun q : ℝ × R × R ↦ cayleyFormula q.2.1 q.2.2) (b, A, B) := by
    simp only [cayleyFormula_def]
    exact ((contDiffAt_const.add hAB).mul ((contDiffAt_const.sub hAB).inverse h₁)).neg
  have hbC := contDiffAt_fst.smul hC
  exact (hA.mul (contDiffAt_const.add hbC)).mul ((contDiffAt_const.sub hbC).inverse h₂)

end Formula

end TauCeti

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SymplecticForm V} {J₀ J₁ : AlmostComplexStructure V}

/-- The inverse-chart denominator is invertible also in the continuous-endomorphism ring. -/
lemma isUnit_one_sub_of_toLinearMap_mem_cayleyBall {C : V →L[ℝ] V}
    (hC : C.toLinearMap ∈ ω.cayleyBall J₀) : IsUnit (1 - C) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  exact isUnit_one_sub_of_mem_cayleyBall hC

/-- In operator-norm coordinates, the inverse tame Cayley chart is the same rational
formula as its algebraic version. -/
theorem Compatible.cayleyEquiv_symm_apply_toContinuousLinearMap
    (h₀ : ω.Compatible J₀) (C : V →L[ℝ] V)
    (hC : C.toLinearMap ∈ ω.cayleyBall J₀) :
    LinearMap.toContinuousLinearMap
        (h₀.cayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  apply ContinuousLinearMap.coe_injective
  rw [LinearMap.coe_toContinuousLinearMap, Compatible.cayleyEquiv_symm_apply_toLinearMap]
  have hinv := (isUnit_one_sub_of_toLinearMap_mem_cayleyBall hC).map_ringInverse
    (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ))
  simpa only [ContinuousLinearMap.toLinearMap_mul, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_one, LinearMap.coe_toContinuousLinearMap,
    ContinuousLinearMap.toLinearMapRingHom_apply, map_sub, map_one] using
    congrArg (fun A => J₀.toLinearMap * (1 + C.toLinearMap) * A) hinv.symm

/-- In operator-norm coordinates, the inverse compatible Cayley chart is the same rational
formula as its algebraic version. -/
theorem Compatible.compatibleCayleyEquiv_symm_apply_toContinuousLinearMap
    (h₀ : ω.Compatible J₀) (C : V →L[ℝ] V)
    (hC : C.toLinearMap ∈ ω.compatibleCayleyBall J₀) :
    LinearMap.toContinuousLinearMap
        (h₀.compatibleCayleyEquiv.symm ⟨C.toLinearMap, hC⟩).val.toLinearMap =
      LinearMap.toContinuousLinearMap J₀.toLinearMap * (1 + C) * Ring.inverse (1 - C) := by
  simpa only [Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap,
    Compatible.cayleyEquiv_symm_apply_toLinearMap] using
    h₀.cayleyEquiv_symm_apply_toContinuousLinearMap C (compatibleCayleyBall_subset_cayleyBall hC)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A smooth family in the tame Cayley ball gives a smooth family of tame structures.
Smoothness is in the continuous-endomorphism carrier, including all external parameters. -/
theorem Compatible.contDiffAt_cayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.cayleyBall J₀)
    {n : WithTop ℕ∞} {p : P} (hCs : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (fun q => LinearMap.toContinuousLinearMap
      (h₀.cayleyEquiv.symm ⟨(C q).toLinearMap, hC q⟩).val.toLinearMap) p := by
  simp_rw [h₀.cayleyEquiv_symm_apply_toContinuousLinearMap]
  have hu := isUnit_one_sub_of_toLinearMap_mem_cayleyBall (hC p)
  exact (contDiffAt_const.mul (contDiffAt_const.add hCs)).mul
    ((contDiffAt_const.sub hCs).inverse hu)

/-- The inverse tame Cayley chart preserves globally smooth parameter families. -/
theorem Compatible.contDiff_cayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.cayleyBall J₀)
    {n : WithTop ℕ∞} (hCs : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => LinearMap.toContinuousLinearMap
      (h₀.cayleyEquiv.symm ⟨(C p).toLinearMap, hC p⟩).val.toLinearMap) :=
  contDiff_iff_contDiffAt.2 fun _ => h₀.contDiffAt_cayleyEquiv_symm hC hCs.contDiffAt

/-- A smooth family in the compatible Cayley ball gives a smooth family of compatible
structures. Smoothness is in the continuous-endomorphism carrier, so it includes all external
parameters of the family. -/
theorem Compatible.contDiffAt_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} {p : P} (hCs : ContDiffAt ℝ n C p) :
    ContDiffAt ℝ n (fun q => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C q).toLinearMap, hC q⟩).val.toLinearMap) p := by
  simpa only [Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap,
    Compatible.cayleyEquiv_symm_apply_toLinearMap] using
    h₀.contDiffAt_cayleyEquiv_symm (fun q => compatibleCayleyBall_subset_cayleyBall (hC q)) hCs

/-- The inverse compatible Cayley chart preserves globally smooth parameter families. -/
theorem Compatible.contDiff_compatibleCayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : P → V →L[ℝ] V} (hC : ∀ p, (C p).toLinearMap ∈ ω.compatibleCayleyBall J₀)
    {n : WithTop ℕ∞} (hCs : ContDiff ℝ n C) :
    ContDiff ℝ n (fun p => LinearMap.toContinuousLinearMap
      (h₀.compatibleCayleyEquiv.symm ⟨(C p).toLinearMap, hC p⟩).val.toLinearMap) :=
  contDiff_iff_contDiffAt.2 fun _ => h₀.contDiffAt_compatibleCayleyEquiv_symm hC hCs.contDiffAt

section Manifold

variable {E G N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace N] [ChartedSpace G N]

omit [FiniteDimensional ℝ V] in
/-- The Cayley formula `-(1 + A B)(1 - A B)⁻¹` of two families of endomorphisms on a manifold
which are `C^n` at a point `p` is `C^n` at `p` when `1 - A p * B p` is a unit. -/
theorem contMDiffAt_cayleyFormula_of_isUnit [CompleteSpace V] {A B : N → V →L[ℝ] V}
    {n : WithTop ℕ∞} {p : N}
    (hA : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n A p) (hB : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n B p)
    (hu : IsUnit (1 - A p * B p)) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n (fun y => cayleyFormula (A y) (B y)) p := by
  obtain ⟨u, hu⟩ := hu
  have hinv := contDiffAt_ringInverse (n := n) ℝ u
  rw [hu] at hinv
  have hi := hinv.comp_contMDiffAt (f := fun y => 1 - A y * B y)
    (contMDiffAt_const.sub (hA.clm_comp hB))
  simp only [cayleyFormula_def]
  exact (((contMDiffAt_const.add (hA.clm_comp hB)).clm_comp hi).neg)

omit [FiniteDimensional ℝ V] in
/-- The inverse Cayley expression `A (1 + C)(1 - C)⁻¹` of two families of endomorphisms on a
manifold which are `C^n` at a point `p` is `C^n` at `p` when `1 - C p` is a unit. -/
theorem contMDiffAt_mul_one_add_ringInverse [CompleteSpace V] {A C : N → V →L[ℝ] V}
    {n : WithTop ℕ∞} {p : N}
    (hA : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n A p) (hC : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n C p)
    (hu : IsUnit (1 - C p)) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n (fun y => A y * (1 + C y) * Ring.inverse (1 - C y)) p := by
  obtain ⟨u, hu⟩ := hu
  have hinv := contDiffAt_ringInverse (n := n) ℝ u
  rw [hu] at hinv
  have hi := hinv.comp_contMDiffAt (f := fun y => 1 - C y)
    (contMDiffAt_const.sub hC)
  exact (hA.clm_comp ((contMDiffAt_const (c := (1 : V →L[ℝ] V))).add hC)).clm_comp hi

/-- The forward Cayley chart `J ↦ -(1 + J₀ J)(1 - J₀ J)⁻¹` relative to an `ω`-tame `J₀` sends a
family of structures on a manifold which is `C^n` at a point `p`, where it is `ω`-tame, to a
family of Cayley coordinates which is `C^n` at `p`: the denominator `1 - J₀ J p` is invertible. -/
theorem Tames.contMDiffAt_cayley (h₀ : ω.Tames J₀) {J : N → AlmostComplexStructure V}
    {n : WithTop ℕ∞} {p : N} (hJp : ω.Tames (J p))
    (hJs : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap) p) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J₀.cayley (J y))) p := by
  -- Pass to the algebra equivalence `Module.End.toContinuousLinearMap`, which is
  -- `LinearMap.toContinuousLinearMap` as a function, to move products and inverses across.
  set e := Module.End.toContinuousLinearMap (𝕜 := ℝ) V
  set j : N → V →L[ℝ] V := fun y => e (J y).toLinearMap
  have hC : (fun y => LinearMap.toContinuousLinearMap (J₀.cayley (J y))) =
      fun y => -(1 + e J₀.toLinearMap * j y) * Ring.inverse (1 - e J₀.toLinearMap * j y) := by
    funext y
    change e (J₀.cayley (J y)) = _
    rw [AlmostComplexStructure.cayley_def, map_neg, map_mul, map_ringInverse, map_add, map_sub,
      map_one, map_mul, neg_mul]
  have hu : IsUnit (1 - e J₀.toLinearMap * j p) := by
    have := (h₀.isUnit_one_sub_mul hJp).map e
    rwa [map_sub, map_one, map_mul] at this
  rw [hC]
  exact ((contDiffAt_const.add (contDiffAt_const.mul contDiffAt_id)).neg.mul
    ((contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inverse hu)).comp_contMDiffAt
    (f := j) hJs

/-- The inverse Cayley chart relative to an `ω`-compatible `J₀` sends a family in the tame Cayley
ball, parameterized by a manifold and `C^n` at a point `p`, to a family of tame structures which is
`C^n` at `p`. -/
theorem Compatible.contMDiffAt_cayleyEquiv_symm (h₀ : ω.Compatible J₀)
    {C : N → V →L[ℝ] V} (hC : ∀ y, (C y).toLinearMap ∈ ω.cayleyBall J₀)
    {n : WithTop ℕ∞} {p : N} (hCs : ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n C p) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] V) n (fun y => LinearMap.toContinuousLinearMap
      (h₀.cayleyEquiv.symm ⟨(C y).toLinearMap, hC y⟩).val.toLinearMap) p := by
  simp_rw [h₀.cayleyEquiv_symm_apply_toContinuousLinearMap]
  have hu := isUnit_one_sub_of_toLinearMap_mem_cayleyBall (hC p)
  exact ((contDiffAt_const.mul (contDiffAt_const.add contDiffAt_id)).mul
    ((contDiffAt_const.sub contDiffAt_id).inverse hu)).comp_contMDiffAt hCs

/-- The forward Cayley chart relative to an `ω`-tame `J₀` sends a `C^n` family of `ω`-tame
structures on a manifold to a `C^n` family of Cayley coordinates. -/
theorem Tames.contMDiff_cayley (h₀ : ω.Tames J₀) {J : N → AlmostComplexStructure V}
    {n : WithTop ℕ∞} (hJ : ∀ y, ω.Tames (J y))
    (hJs : ContMDiff I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J y).toLinearMap)) :
    ContMDiff I 𝓘(ℝ, V →L[ℝ] V) n
      (fun y => LinearMap.toContinuousLinearMap (J₀.cayley (J y))) :=
  fun p => h₀.contMDiffAt_cayley (hJ p) (hJs p)

end Manifold

/-- A smooth, collar-constant path from `J₀` to `J₁` through compatible structures, obtained by
multiplying the Cayley coordinate of `J₁` by `smoothTransition t`. -/
def Compatible.cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    AlmostComplexStructure V :=
  (h₀.compatibleCayleyEquiv.symm
    ⟨smoothTransition t • J₀.cayley J₁,
      h₀.smul_cayley_mem_compatibleCayleyBall h₁
        (smoothTransition.abs_le_one t)⟩).val

/-- The path is the inverse compatible Cayley chart at the cutoff-scaled endpoint coordinate. -/
theorem Compatible.cayleyPath_eq_compatibleCayleyEquiv_symm
    (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    h₀.cayleyPath h₁ t =
      (h₀.compatibleCayleyEquiv.symm
        ⟨smoothTransition t • J₀.cayley J₁,
          h₀.smul_cayley_mem_compatibleCayleyBall h₁
            (smoothTransition.abs_le_one t)⟩).val := by
  rfl

/-- The cutoff-scaled Cayley coordinate of `J₁`, as a continuous endomorphism, lies in the
compatible Cayley ball. -/
theorem Compatible.smoothTransition_smul_cayley_mem_compatibleCayleyBall
    (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    (smoothTransition t • LinearMap.toContinuousLinearMap (J₀.cayley J₁)).toLinearMap ∈
      ω.compatibleCayleyBall J₀ := by
  simpa only [ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap] using
    h₀.smul_cayley_mem_compatibleCayleyBall h₁
      (smoothTransition.abs_le_one t)

/-- The interpolated structure is compatible at every parameter, not only at its endpoints. -/
theorem Compatible.compatible_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    ω.Compatible (h₀.cayleyPath h₁ t) :=
  (h₀.compatibleCayleyEquiv.symm _).property

/-- The Cayley coordinate of the path is the cutoff-scaled coordinate of its endpoint. -/
@[simp]
theorem Compatible.cayley_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁) (t : ℝ) :
    J₀.cayley (h₀.cayleyPath h₁ t) = smoothTransition t • J₀.cayley J₁ := by
  rw [h₀.cayleyPath_eq_compatibleCayleyEquiv_symm h₁ t]
  simpa only [Compatible.compatibleCayleyEquiv_apply_coe] using
    congrArg Subtype.val (h₀.compatibleCayleyEquiv.apply_symm_apply _)

/-- Interpolating a structure with itself leaves it fixed at every parameter. -/
@[simp]
theorem Compatible.cayleyPath_self (h₀ : ω.Compatible J₀) (t : ℝ) :
    h₀.cayleyPath h₀ t = J₀ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₀ t).tames h₀.tames (by simp)

/-- The path agrees with its initial structure on the entire incoming collar. -/
@[simp]
theorem Compatible.cayleyPath_of_nonpos (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : t ≤ 0) : h₀.cayleyPath h₁ t = J₀ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₁ t).tames h₀.tames
    (by simp [smoothTransition.zero_of_nonpos ht])

/-- The path agrees with its final structure on the entire outgoing collar. -/
@[simp]
theorem Compatible.cayleyPath_of_one_le (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    {t : ℝ} (ht : 1 ≤ t) : h₀.cayleyPath h₁ t = J₁ := by
  exact h₀.eq_of_cayley_eq (h₀.compatible_cayleyPath h₁ t).tames h₁.tames
    (by simp [smoothTransition.one_of_one_le ht])

/-- The path is smooth on the whole real line, including both transition endpoints. -/
theorem Compatible.contDiff_cayleyPath (h₀ : ω.Compatible J₀) (h₁ : ω.Compatible J₁)
    (n : ℕ∞) :
    ContDiff ℝ n (fun t => LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap) := by
  let C : ℝ → V →L[ℝ] V := fun t =>
    smoothTransition t • LinearMap.toContinuousLinearMap (J₀.cayley J₁)
  have hC (t : ℝ) : (C t).toLinearMap ∈ ω.compatibleCayleyBall J₀ :=
    h₀.smoothTransition_smul_cayley_mem_compatibleCayleyBall h₁ t
  convert h₀.contDiff_compatibleCayleyEquiv_symm (n := n) hC
    (smoothTransition.contDiff.smul contDiff_const) using 1
  funext t
  rw [h₀.cayleyPath_eq_compatibleCayleyEquiv_symm h₁ t]
  simp only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]

/-! ### The linear Cayley path in operator-norm coordinates -/

section Coordinates

variable {A B : V →L[ℝ] V}

/-- For two tame structures, `1 - J₀ J₁` is invertible among continuous endomorphisms. -/
theorem Tames.isUnit_one_sub_mul_of_toLinearMap (h₀ : ω.Tames J₀) (h₁ : ω.Tames J₁)
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    IsUnit (1 - A * B) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap]
  simpa [hA, hB] using h₀.isUnit_one_sub_mul h₁

/-- In operator-norm coordinates, the Cayley transform is the rational expression
`-(1 + J₀ J₁)(1 - J₀ J₁)⁻¹` of the continuous endomorphisms `J₀` and `J₁`. -/
theorem Tames.toContinuousLinearMap_cayley (h₀ : ω.Tames J₀) (h₁ : ω.Tames J₁)
    (hA : A.toLinearMap = J₀.toLinearMap) (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (J₀.cayley J₁) = cayleyFormula A B := by
  apply ContinuousLinearMap.coe_injective
  have hinv := (h₀.isUnit_one_sub_mul_of_toLinearMap h₁ hA hB).map_ringInverse
    (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℝ))
  simp only [ContinuousLinearMap.toLinearMapRingHom_apply, map_sub, map_one, map_mul] at hinv
  rw [AlmostComplexStructure.cayley_eq_cayleyFormula, LinearMap.coe_toContinuousLinearMap,
    cayleyFormula_def, cayleyFormula_def, ContinuousLinearMap.toLinearMap_neg,
    ContinuousLinearMap.toLinearMap_mul, hinv]
  simp [hA, hB]

/-- In operator-norm coordinates, the tame structure whose Cayley coordinate at `J₀` is `b` times
that of a tame `J₁`, for `|b| ≤ 1`, is `J₀ (1 + b C)(1 - b C)⁻¹`, where `C` is the Cayley
coordinate of `J₁`. -/
theorem Compatible.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley (h₀ : ω.Compatible J₀)
    (h₁ : ω.Tames J₁) {b : ℝ} (hb : |b| ≤ 1) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap
        (h₀.cayleyEquiv.symm
          ⟨b • J₀.cayley J₁, h₀.smul_cayley_mem_cayleyBall h₁ hb⟩).val.toLinearMap =
      cayleyPathFormula b A B := by
  set C : V →L[ℝ] V := b • LinearMap.toContinuousLinearMap (J₀.cayley J₁) with hCdef
  have hC : C.toLinearMap ∈ ω.cayleyBall J₀ := by
    simpa only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]
      using h₀.smul_cayley_mem_cayleyBall h₁ hb
  have hsymm : h₀.cayleyEquiv.symm ⟨b • J₀.cayley J₁, h₀.smul_cayley_mem_cayleyBall h₁ hb⟩ =
      h₀.cayleyEquiv.symm ⟨C.toLinearMap, hC⟩ := by
    simp only [C, ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]
  have hA' : LinearMap.toContinuousLinearMap J₀.toLinearMap = A :=
    ContinuousLinearMap.coe_injective (by rw [LinearMap.coe_toContinuousLinearMap, hA])
  rw [hsymm, h₀.cayleyEquiv_symm_apply_toContinuousLinearMap _ hC, cayleyPathFormula_def, hCdef,
    h₀.tames.toContinuousLinearMap_cayley h₁ hA hB, hA']

/-- In operator-norm coordinates, the compatible Cayley path from `J₀` to `J₁` at time `t` is
`J₀ (1 + β C)(1 - β C)⁻¹`, where `C` is the Cayley coordinate of `J₁` and
`β = smoothTransition t`. -/
theorem Compatible.toContinuousLinearMap_cayleyPath (h₀ : ω.Compatible J₀)
    (h₁ : ω.Compatible J₁) (t : ℝ) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J₁.toLinearMap) :
    LinearMap.toContinuousLinearMap (h₀.cayleyPath h₁ t).toLinearMap =
      cayleyPathFormula (smoothTransition t) A B := by
  rw [← h₀.toContinuousLinearMap_cayleyEquiv_symm_smul_cayley h₁.tames
    (smoothTransition.abs_le_one t) hA hB,
    h₀.cayleyPath_eq_compatibleCayleyEquiv_symm,
    Compatible.compatibleCayleyEquiv_symm_apply_toLinearMap,
    Compatible.cayleyEquiv_symm_apply_toLinearMap]

/-- For `|b| ≤ 1` and a tame `J₁`, the denominator `1 - b C` of the Cayley path expression is
invertible, where `C` is the Cayley coordinate of `J₁`. -/
theorem Compatible.isUnit_one_sub_smul_cayleyFormula (h₀ : ω.Compatible J₀)
    (h₁ : ω.Tames J₁) {b : ℝ} (hb : |b| ≤ 1) (hA : A.toLinearMap = J₀.toLinearMap)
    (hB : B.toLinearMap = J₁.toLinearMap) :
    IsUnit (1 - b • cayleyFormula A B) := by
  rw [← h₀.tames.toContinuousLinearMap_cayley h₁ hA hB]
  refine isUnit_one_sub_of_toLinearMap_mem_cayleyBall (ω := ω) (J₀ := J₀) ?_
  simpa only [ContinuousLinearMap.toLinearMap_smul, LinearMap.coe_toContinuousLinearMap]
    using h₀.smul_cayley_mem_cayleyBall h₁ hb

/-- For a compact set `𝒦` of tame structures, the Cayley path expressions
`J₀ (1 + b C)(1 - b C)⁻¹`, where `|b| ≤ 1` and `C` is the Cayley coordinate of a member of `𝒦`,
form a compact set of operators. The expression is continuous there, since its denominators are
invertible. -/
theorem Compatible.isCompact_image_cayleyPathFormula (h₀ : ω.Compatible J₀)
    (hA : A.toLinearMap = J₀.toLinearMap) {𝒦 : Set (AlmostComplexStructure V)}
    (h𝒦 : IsCompact 𝒦) (h𝒦t : ∀ J ∈ 𝒦, ω.Tames J) :
    IsCompact ((fun p : ℝ × (V →L[ℝ] V) ↦ cayleyPathFormula p.1 A p.2) ''
      (Icc (-1) 1 ×ˢ
        ((fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap) ''
          𝒦))) := by
  refine (isCompact_Icc.prod (h𝒦.image
    AlmostComplexStructure.isEmbedding_toContinuousLinearMap.continuous)).image_of_continuousOn ?_
  rintro ⟨b, _⟩ ⟨hb, J, hJ, rfl⟩
  have hB := LinearMap.coe_toContinuousLinearMap J.toLinearMap
  exact ((contDiffAt_cayleyPathFormula (n := 0)
    (h₀.tames.isUnit_one_sub_mul_of_toLinearMap (h𝒦t J hJ) hA hB)
    (h₀.isUnit_one_sub_smul_cayleyFormula (h𝒦t J hJ) (abs_le.2 hb) hA hB)).continuousAt.comp
      (f := fun p : ℝ × (V →L[ℝ] V) ↦ (p.1, A, p.2)) (by fun_prop)).continuousWithinAt

end Coordinates

end TauCeti.SymplecticForm
