/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Cayley.Path

/-!
# Cayley segments between two tame almost complex structures

Let `σ` be a smooth two-form on a finite-dimensional manifold `M` and `J₀` a smooth almost complex
structure compatible with `σ`. At each point `x`, the Cayley chart based at `J₀ x` identifies the
`σ_x`-tame complex structures on `T_x M` with a convex ball containing `0`, and the
`σ_x`-compatible ones with a convex subset of it. So any two smooth `σ`-tame structures `J₁` and
`J₂` are joined by the segment between their Cayley coordinates. This file assembles these
pointwise segments into the family of smooth almost complex structures

`TauCeti.SmoothTwoForm.Compatible.cayleySegment h₀ h₁ h₂ t`,

for `h₀ : σ.Compatible J₀`, `h₁ : σ.Tames J₁` and `h₂ : σ.Tames J₂`, whose Cayley coordinate
relative to `J₀` is `(1 - β t) • cayley J₁ + β t • cayley J₂` at every point, where `β` is the
smooth transition function. It is `J₁` for `t ≤ 0` and `J₂` for `t ≥ 1`. The Cayley path
`TauCeti.SmoothTwoForm.Compatible.cayleyPath h₀ h₂` is the segment starting at `J₀`
(`TauCeti.SmoothTwoForm.Compatible.cayleySegment_eq_cayleyPath`), and the continuation homotopy
`TauCeti.SmoothTwoForm.Compatible.continuationAlmostComplex` between two families of structures is
defined as the segment between their members. The endpoints of the segments may vary with a
parameter, and the segments then vary smoothly with it
(`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_cayleySegment`).

Such segments switch a domain-dependent structure on or off over a family of domains, keeping it
tame throughout: a family of Floer data whose Hamiltonian perturbation is scaled by `β t` uses the
segment from the structure without the term to the structure with it.

## Main results

* `TauCeti.SmoothTwoForm.Compatible.cayley_almostComplexStructureAt_cayleySegment`: the Cayley
  coordinate of the segment at every point, which characterizes it
  (`TauCeti.SmoothTwoForm.Compatible.eq_cayleySegment_of_cayley_eq`).
* `TauCeti.SmoothTwoForm.Compatible.tames_cayleySegment` and
  `TauCeti.SmoothTwoForm.Compatible.compatible_cayleySegment`: every structure on the segment is
  tame, and compatible when both endpoints are.
* `TauCeti.SmoothTwoForm.Compatible.cayleySegment_of_nonpos`,
  `TauCeti.SmoothTwoForm.Compatible.cayleySegment_of_one_le`: the endpoints.
* `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_cayleySegment`: for endpoints and times depending
  smoothly on a parameter, the segments depend smoothly on the parameter and the point.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford
  University Press, 2017, Proposition 2.5.13 (the Cayley chart on tame and compatible complex
  structures, and the contractibility of the spaces of tame and of compatible structures).
-/

public section

open Bundle Real
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J₀ J₁ J₂ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀) (h₁ : σ.Tames J₁) (h₂ : σ.Tames J₂)

include h₁ h₂ in
/-- At each point, the segment between the Cayley coordinates of two tame structures lies in the
Cayley ball. -/
private theorem segment_mem_cayleyBall (t : ℝ) (x : M) :
    (1 - smoothTransition t) •
          (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) +
        smoothTransition t •
          (J₀.almostComplexStructureAt x).cayley (J₂.almostComplexStructureAt x) ∈
      (h₀.isNondegenerate.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x) :=
  (h₀.compatibleAt x).tames.convex_cayleyBall
    ((h₀.compatibleAt x).cayley_mem_cayleyBall (h₀.isNondegenerate.tames_iff.mp h₁ x))
    ((h₀.compatibleAt x).cayley_mem_cayleyBall (h₀.isNondegenerate.tames_iff.mp h₂ x))
    (sub_nonneg.2 (smoothTransition.le_one t)) (smoothTransition.nonneg t) (sub_add_cancel 1 _)

/-- The pointwise segment at `x`: the tame structure on `T_x M` with the segment's Cayley
coordinate. -/
private def cayleySegmentAt (t : ℝ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  ((h₀.compatibleAt x).cayleyEquiv.symm ⟨_, segment_mem_cayleyBall h₀ h₁ h₂ t x⟩).val

private theorem tames_cayleySegmentAt (t : ℝ) (x : M) :
    (h₀.isNondegenerate.symplecticFormAt x).Tames (cayleySegmentAt h₀ h₁ h₂ t x) :=
  ((h₀.compatibleAt x).cayleyEquiv.symm _).property

private theorem cayley_cayleySegmentAt (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (cayleySegmentAt h₀ h₁ h₂ t x) =
      (1 - smoothTransition t) •
          (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) +
        smoothTransition t •
          (J₀.almostComplexStructureAt x).cayley (J₂.almostComplexStructureAt x) := by
  rw [cayleySegmentAt, ← (h₀.compatibleAt x).cayleyEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The pointwise segment is smooth in the point: its Cayley coordinate is a constant-weight
combination of those of the two smooth endpoints. -/
private theorem contMDiffAt_cayleySegmentAt (t : ℝ) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y (LinearMap.toContinuousLinearMap (cayleySegmentAt h₀ h₁ h₂ t y).toLinearMap)) x :=
  h₀.contMDiffAt_of_cayley_eq_sum (b := id) (L := fun i (_ : M) => ![J₁, J₂] i)
    (a := fun i (_ : M) => ![1 - smoothTransition t, smoothTransition t] i)
    (fun y => tames_cayleySegmentAt h₀ h₁ h₂ t y)
    (fun i _ => by fin_cases i <;> assumption)
    (fun y => by simp [cayley_cayleySegmentAt, Fin.sum_univ_two]) contMDiffAt_id
    (fun _ => contMDiffAt_const)
    (fun i => by fin_cases i <;> exact SmoothAlmostComplexStructure.toEndomorphism _ |>.contMDiff x)

/-- **The Cayley segment from `J₁` to `J₂`.** For a `σ`-compatible base structure `J₀` and
`σ`-tame structures `J₁` and `J₂`, the smooth almost complex structure whose Cayley coordinate
relative to `J₀` is `(1 - β t) • cayley J₁ + β t • cayley J₂` at every point, where `β` is the
smooth transition function. It is `J₁` for `t ≤ 0` and `J₂` for `1 ≤ t`. -/
def cayleySegment (t : ℝ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x => LinearMap.toContinuousLinearMap (cayleySegmentAt h₀ h₁ h₂ t x).toLinearMap,
      contMDiffAt_cayleySegmentAt h₀ h₁ h₂ t⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the pointwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of the segment at `x` is the pointwise structure, read as a continuous
endomorphism. -/
private theorem cayleySegment_toEndomorphism (t : ℝ) (x : M) :
    (h₀.cayleySegment h₁ h₂ t).toEndomorphism x =
      LinearMap.toContinuousLinearMap (cayleySegmentAt h₀ h₁ h₂ t x).toLinearMap :=
  (rfl)

private theorem almostComplexStructureAt_cayleySegment (t : ℝ) (x : M) :
    (h₀.cayleySegment h₁ h₂ t).almostComplexStructureAt x = cayleySegmentAt h₀ h₁ h₂ t x := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    cayleySegment_toEndomorphism, LinearMap.coe_toContinuousLinearMap]

/-- At every point, the Cayley coordinate of the segment relative to `J₀` is
`(1 - β t) • cayley J₁ + β t • cayley J₂`. Since tame structures are determined by their Cayley
coordinate relative to a compatible structure, this characterizes the segment. -/
@[simp]
theorem cayley_almostComplexStructureAt_cayleySegment (t : ℝ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.cayleySegment h₁ h₂ t).almostComplexStructureAt x) =
      (1 - smoothTransition t) •
          (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) +
        smoothTransition t •
          (J₀.almostComplexStructureAt x).cayley (J₂.almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_cayleySegment, cayley_cayleySegmentAt]

/-- Every structure on the segment is tamed by `σ`. -/
theorem tames_cayleySegment (t : ℝ) : σ.Tames (h₀.cayleySegment h₁ h₂ t) :=
  h₀.isNondegenerate.tames_iff.2 fun x => by
    rw [almostComplexStructureAt_cayleySegment]
    exact tames_cayleySegmentAt h₀ h₁ h₂ t x

/-- A tame smooth almost complex structure with the prescribed Cayley coordinate at every point
is the segment at time `t`. -/
theorem eq_cayleySegment_of_cayley_eq {t : ℝ} {J : SmoothAlmostComplexStructure I M}
    (hJ : σ.Tames J)
    (h : ∀ x, (J₀.almostComplexStructureAt x).cayley (J.almostComplexStructureAt x) =
      (1 - smoothTransition t) •
          (J₀.almostComplexStructureAt x).cayley (J₁.almostComplexStructureAt x) +
        smoothTransition t •
          (J₀.almostComplexStructureAt x).cayley (J₂.almostComplexStructureAt x)) :
    J = h₀.cayleySegment h₁ h₂ t :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x =>
    (h₀.compatibleAt x).eq_of_cayley_eq (h₀.isNondegenerate.tames_iff.mp hJ x)
      (h₀.isNondegenerate.tames_iff.mp (h₀.tames_cayleySegment h₁ h₂ t) x)
      ((h x).trans (cayley_almostComplexStructureAt_cayleySegment h₀ h₁ h₂ t x).symm)

/-- For compatible endpoints, every structure on the segment is compatible with `σ`. -/
theorem compatible_cayleySegment (h₁ : σ.Compatible J₁) (h₂ : σ.Compatible J₂) (t : ℝ) :
    σ.Compatible (h₀.cayleySegment h₁.tames h₂.tames t) := by
  refine h₀.isNondegenerate.compatible_iff.2 fun x => ?_
  have hc (J : SmoothAlmostComplexStructure I M) (hJ : σ.Compatible J) :=
    ((h₀.compatibleAt x).cayley_mem_compatibleCayleyBall_iff
      (h₀.isNondegenerate.tames_iff.mp hJ.tames x)).mpr (hJ.compatibleAt x)
  refine ((h₀.compatibleAt x).cayley_mem_compatibleCayleyBall_iff
    (h₀.isNondegenerate.tames_iff.mp (h₀.tames_cayleySegment _ _ t) x)).mp ?_
  rw [cayley_almostComplexStructureAt_cayleySegment]
  exact (h₀.compatibleAt x).tames.convex_compatibleCayleyBall (hc J₁ h₁) (hc J₂ h₂)
    (sub_nonneg.2 (smoothTransition.le_one t)) (smoothTransition.nonneg t) (sub_add_cancel 1 _)

/-- The segment starts at `J₁`: it is `J₁` for `t ≤ 0`. -/
@[simp]
theorem cayleySegment_of_nonpos {t : ℝ} (ht : t ≤ 0) : h₀.cayleySegment h₁ h₂ t = J₁ :=
  (h₀.eq_cayleySegment_of_cayley_eq h₁ h₂ h₁ fun x => by
    rw [smoothTransition.zero_of_nonpos ht, sub_zero, one_smul, zero_smul, add_zero]).symm

/-- The segment ends at `J₂`: it is `J₂` for `1 ≤ t`. -/
@[simp]
theorem cayleySegment_of_one_le {t : ℝ} (ht : 1 ≤ t) : h₀.cayleySegment h₁ h₂ t = J₂ :=
  (h₀.eq_cayleySegment_of_cayley_eq h₁ h₂ h₂ fun x => by
    rw [smoothTransition.one_of_one_le ht, sub_self, zero_smul, one_smul, zero_add]).symm

/-- The segment from a structure to itself is constant. -/
@[simp]
theorem cayleySegment_self (t : ℝ) : h₀.cayleySegment h₁ h₁ t = J₁ :=
  (h₀.eq_cayleySegment_of_cayley_eq h₁ h₁ h₁ fun x => by
    rw [← add_smul, sub_add_cancel, one_smul]).symm

/-- The segment depends only on its endpoints, not on the proofs of their tameness. -/
theorem cayleySegment_congr {J₁' J₂' : SmoothAlmostComplexStructure I M} (h₁' : σ.Tames J₁')
    (h₂' : σ.Tames J₂') (e₁ : J₁ = J₁') (e₂ : J₂ = J₂') (t : ℝ) :
    h₀.cayleySegment h₁ h₂ t = h₀.cayleySegment h₁' h₂' t := by
  subst e₁ e₂
  rfl

/-- The segment starting at the base structure `J₀` is the Cayley path from `J₀`. -/
theorem cayleySegment_eq_cayleyPath (t : ℝ) :
    h₀.cayleySegment h₀.tames h₂ t = h₀.cayleyPath h₂ t :=
  h₀.eq_cayleyPath_of_cayley_eq h₂ (h₀.tames_cayleySegment _ _ t) fun x => by
    rw [cayley_almostComplexStructureAt_cayleySegment, AlmostComplexStructure.cayley_self,
      smul_zero, zero_add]

/-- **Smooth families of segments.** Let `A y` and `B y` be smooth `σ`-tame structures and `t y` a
time, for `y` in a manifold `N`, and let `b y` be points of `M`. If `t`, `b` and the sections
`y ↦ A y (b y)` and `y ↦ B y (b y)` are `C^n` at `y₀`, then so is the section
`y ↦ cayleySegment (A y) (B y) (t y) (b y)` of the tangent endomorphism bundle along `b`. -/
theorem contMDiffAt_cayleySegment {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : WithTop ℕ∞} [ENat.LEInfty n] {A B : N → SmoothAlmostComplexStructure I M}
    (hA : ∀ y, σ.Tames (A y)) (hB : ∀ y, σ.Tames (B y)) {t : N → ℝ} {b : N → M} {y₀ : N}
    (ht : ContMDiffAt I' 𝓘(ℝ) n t y₀) (hb : ContMDiffAt I' I n b y₀)
    (hAs : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((A y).toEndomorphism (b y))) y₀)
    (hBs : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((B y).toEndomorphism (b y))) y₀) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.cayleySegment (hA y) (hB y) (t y)).toEndomorphism (b y))) y₀ := by
  have hβ : ContMDiffAt I' 𝓘(ℝ) n (fun y => smoothTransition (t y)) y₀ :=
    ((smoothTransition.contDiff (n := ⊤)).of_le ENat.LEInfty.out).contMDiff.contMDiffAt.comp y₀ ht
  simp only [cayleySegment_toEndomorphism]
  refine h₀.contMDiffAt_of_cayley_eq_sum (b := b) (L := fun i y => ![A y, B y] i)
    (a := fun i y => ![1 - smoothTransition (t y), smoothTransition (t y)] i)
    (fun y => tames_cayleySegmentAt h₀ (hA y) (hB y) (t y) (b y))
    (fun i y => by fin_cases i <;> simp [hA, hB])
    (fun y => by simp [cayley_cayleySegmentAt, Fin.sum_univ_two]) hb ?_ ?_
  · intro i
    fin_cases i
    · simpa using contMDiffAt_const.sub hβ
    · simpa using hβ
  · intro i
    fin_cases i
    · simpa using hAs
    · simpa using hBs

end TauCeti.SmoothTwoForm.Compatible
