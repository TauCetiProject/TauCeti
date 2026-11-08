/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Basic

/-!
# Almost complex structures on the capped pair of pants in a manifold

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, giving a sphere with
three poles `0`, `1` and `∞`. The almost complex structures of this comparison family are
constructed in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped` on a fixed
symplectic vector space. This file constructs them on the actual tangent bundle of a manifold `M`
with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth base structure `J₀` and three smooth period-one families `J_q(t)` of
`σ`-tame smooth structures on the ends. For the cutoff parameter `r`, the neck length `L` and a
point `w ∈ ℂ`, the structure
`TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex h₀ J hJ hJp hJs r L w` is, on each tangent
space `T_x M`, the linear capped structure `TauCeti.Floer.cappedAlmostComplex` of the structures
at `x` (`SmoothTwoForm.Compatible.almostComplexStructureAt_cappedAlmostComplex`): the inverse
Cayley transform, relative to `J₀(x)`, of

`β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J_q(t_q)(x))`,

where `(s_q, t_q)` are the coordinates of the end `q`, `σ_q = ±s_q` and `β` is the smooth
transition function. It is tame, and compatible when the end structures are. It is `J₀` for
`r ≤ 0` and outside the truncation `S_{L + 3}`, hence near the three poles. For `r ≥ 1` it is the
end structure `J_q(t)` along the neck `2 ≤ σ_q ≤ L + 2` and, up to the necks, the manifold
pair-of-pants structure `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex`. Beyond the
neck it does not depend on the neck length up to translation.

The structure is smooth jointly in `r`, `L`, the domain point `w ∈ ℂ`, including the poles `0` and
`1`, and the target point, as a section of the tangent endomorphism bundle
(`SmoothTwoForm.Compatible.contMDiff_cappedAlmostComplex`). Away from the poles this follows, as for
the pair-of-pants structure, from the smoothness of inverse Cayley transforms of weighted sums of
Cayley coordinates, `SmoothTwoForm.Compatible.contMDiffAt_mul_one_add_cayleySum`. Near the poles
`0` and `1` the structure is the base structure `J₀`.

The comparison family `TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex` uses the
cutoff parameter `3R - 1` and the neck length `TauCeti.Floer.comparisonNeckLength R`, as its
vector-space counterpart `TauCeti.Floer.cappedComparisonAlmostComplex`. It starts at the
domain-independent `J₀` for `R ≤ 1/3`, has no necks on the collar `2/3 ≤ R ≤ 3/2`, has necks of
length `R - 1` for `R ≥ 2`, and is smooth in `R`.

Neither closedness of the two-form nor compactness of the target is used.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures, and Section 12.1, on the PSS isomorphism.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart).
-/

public noncomputable section

open Bundle Set Real Filter Manifold Topology
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJ : ∀ q t, σ.Tames (J q t))

/-- The linear capped structure on the tangent space at `x`. -/
private def cappedFiber (r L : ℝ) (w : ℂ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  Floer.cappedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
    (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
    (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) r L w ()

/-- The fiberwise construction, read as a continuous tangent endomorphism. -/
private def cappedEnd (r L : ℝ) (w : ℂ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap (cappedFiber h₀ J hJ r L w x).toLinearMap

/-- The weights of the end structures in the Cayley coordinate of the fiberwise construction. -/
private def cappedWeight (r L : ℝ) (w : ℂ) (q : Puncture) : ℝ :=
  smoothTransition r * (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
    smoothTransition (L + 3 - q.endSign * (q.endCoord w).re))

private theorem cappedCayley_toLinearMap (r L : ℝ) (w : ℂ) (x : M) :
    (J₀.cayleySum (cappedWeight r L w) (fun q => J q (q.endCoord w).im) x).toLinearMap =
      (J₀.almostComplexStructureAt x).cayley (cappedFiber h₀ J hJ r L w x) := by
  rw [h₀.cayleySum_toLinearMap _ (K := fun q => J q (q.endCoord w).im) (fun q => hJ q _),
    cappedFiber, Floer.cayley_cappedAlmostComplex, Finset.smul_sum]
  simp only [cappedWeight, smul_smul]

private theorem cappedEnd_eq (r L : ℝ) (w : ℂ) (x : M) :
    cappedEnd h₀ J hJ r L w x = J₀.toEndomorphism x *
      (1 + J₀.cayleySum (cappedWeight r L w) (fun q => J q (q.endCoord w).im) x) *
      Ring.inverse (1 - J₀.cayleySum (cappedWeight r L w) (fun q => J q (q.endCoord w).im) x) :=
  h₀.toContinuousLinearMap_eq_of_cayley_eq (Floer.tames_cappedAlmostComplex _ r L w ())
    (cappedCayley_toLinearMap h₀ J hJ r L w x)

/-- Outside the truncation `S_{L + 3}` the fiberwise construction is the base structure. -/
private theorem cappedEnd_eq_of_notMem_truncation (r : ℝ) {L : ℝ} {w : ℂ}
    (hw : w ∉ truncation (L + 3)) (x : M) :
    cappedEnd h₀ J hJ r L w x = J₀.toEndomorphism x := by
  rw [cappedEnd, cappedFiber, Floer.cappedAlmostComplex_eq_base_of_notMem_truncation _ r hw]
  exact J₀.toContinuousLinearMap_almostComplexStructureAt x

variable (hJp : ∀ q, Function.Periodic (J q) 1)
  (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((J q p.1).toEndomorphism p.2)))

include hJp hJs in
/-- Away from the poles, the fiberwise construction is smooth jointly in the cutoff parameter, the
neck length, the domain point and the target point. -/
private theorem contMDiffAt_cappedEnd_of_ne (r L : ℝ) {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ × ℂ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × ℂ) × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (cappedEnd h₀ J hJ p.1.1 p.1.2.1 p.1.2.2 p.2)) ((r, L, w), x) := by
  have hS := ne_endCenter hw
  refine (h₀.contMDiffAt_mul_one_add_cayleySum
    (c := fun q (p : ℝ × ℝ × ℂ) => cappedWeight p.1 p.2.1 p.2.2 q)
    (K := fun q (p : ℝ × ℝ × ℂ) => J q (q.endCoord p.2.2).im) (fun q => hJ q _) (fun q => ?_)
    (fun q => ?_) ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  · -- The cutoff parameter and the weights of the ends are smooth functions of `(r, L, w)`.
    have hσ : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ × ℂ => q.endSign * (q.endCoord p.2.2).re)
        (r, L, w) :=
      contDiffAt_const.mul (ContDiffAt.comp (g := fun w : ℂ => (q.endCoord w).re)
        (f := fun p : ℝ × ℝ × ℂ => p.2.2) (r, L, w) (q.contDiffAt_re_endCoord (hS q))
        (contDiff_snd.comp contDiff_snd).contDiffAt)
    exact ((smoothTransition.contDiff.comp contDiff_fst).contDiffAt.mul
      ((smoothTransition.contDiff.contDiffAt.comp _ (hσ.sub contDiffAt_const)).mul
        (smoothTransition.contDiff.contDiffAt.comp _
          (((contDiff_fst.comp contDiff_snd).contDiffAt.add contDiffAt_const).sub
            hσ)))).contMDiffAt
  · -- Each end family, read at the angular coordinate of its end, is smooth off the end center.
    have hp : Function.Periodic (fun t y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y ((J q t).toEndomorphism y)) 1 := fun t => by simp only [hJp q t]
    have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ × ℂ).prod I) (𝓘(ℝ, ℂ).prod I) (⊤ : ℕ∞)
        (fun p : (ℝ × ℝ × ℂ) × M => (p.1.2.2, p.2)) ((r, L, w), x) :=
      ((contDiff_snd.comp contDiff_snd).contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
        contMDiffAt_snd
    exact (q.contMDiffAt_comp_im_endCoord hp (hJs q) (hS q) x).comp ((r, L, w), x) hφ
  · exact h₀.isUnit_one_sub_of_toLinearMap_eq_cayley (Floer.tames_cappedAlmostComplex _ r L w ())
      (cappedCayley_toLinearMap h₀ J hJ r L w x)
  · dsimp only
    rw [cappedEnd_eq h₀ J hJ]

/-- Near the poles `0` and `1`, the fiberwise construction is the base structure, so it is smooth
there. -/
private theorem contMDiffAt_cappedEnd_of_pole (r L : ℝ) {w : ℂ} (hw : w = 0 ∨ w = 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ × ℂ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × ℂ) × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (cappedEnd h₀ J hJ p.1.1 p.1.2.1 p.1.2.2 p.2)) ((r, L, w), x) := by
  refine ((J₀.toEndomorphism.contMDiff x).comp ((r, L, w), x)
    contMDiffAt_snd).congr_of_eventuallyEq ?_
  have hproj : Tendsto (fun p : (ℝ × ℝ × ℂ) × M => (p.1.2.2, p.1.2.1 + 3))
      (𝓝 ((r, L, w), x)) (𝓝 (w, L + 3)) :=
    ((continuous_snd.comp (continuous_snd.comp continuous_fst)).prodMk
      ((continuous_fst.comp (continuous_snd.comp continuous_fst)).add
        continuous_const)).tendsto ((r, L, w), x)
  filter_upwards [hproj.eventually (eventually_notMem_truncation hw (L + 3))] with p hp
  simp only [Function.comp_apply, cappedEnd_eq_of_notMem_truncation h₀ J hJ _ hp]

include hJp hJs in
private theorem contMDiffAt_cappedEnd (r L : ℝ) (w : ℂ) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ × ℂ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × ℂ) × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (cappedEnd h₀ J hJ p.1.1 p.1.2.1 p.1.2.2 p.2)) ((r, L, w), x) := by
  by_cases hw : w = 0 ∨ w = 1
  · exact contMDiffAt_cappedEnd_of_pole h₀ J hJ r L hw x
  · rw [not_or] at hw
    exact contMDiffAt_cappedEnd_of_ne h₀ J hJ hJp hJs r L hw x

/-- The domain-dependent almost complex structure on the pair of pants capped by three PSS planes
along necks of length `L`, moved along the segment from `J₀` by the cutoff `β(r)`, on the tangent
bundle of `M`. On each tangent space it is the linear capped structure
`TauCeti.Floer.cappedAlmostComplex` of `J₀` and the end structures `J_q(t)` at that point. -/
def cappedAlmostComplex (r L : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨cappedEnd h₀ J hJ r L w, fun x =>
    (contMDiffAt_cappedEnd h₀ J hJ hJp hJs r L w x).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the linear fiberwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism section of the capped structure is the fiberwise construction. -/
private theorem toEndomorphism_cappedAlmostComplex (r L : ℝ) (w : ℂ) (x : M) :
    (h₀.cappedAlmostComplex J hJ hJp hJs r L w).toEndomorphism x = cappedEnd h₀ J hJ r L w x :=
  rfl

/-- The value on a tangent fiber is precisely the linear capped construction there. -/
theorem almostComplexStructureAt_cappedAlmostComplex (r L : ℝ) (w : ℂ) (x : M) :
    (h₀.cappedAlmostComplex J hJ hJp hJs r L w).almostComplexStructureAt x =
      Floer.cappedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) r L w () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    toEndomorphism_cappedAlmostComplex]
  simp only [cappedEnd, cappedFiber, LinearMap.coe_toContinuousLinearMap]

/-- The capped structure is tamed by the given two-form. -/
theorem tames_cappedAlmostComplex (r L : ℝ) (w : ℂ) :
    σ.Tames (h₀.cappedAlmostComplex J hJ hJp hJs r L w) := by
  apply h₀.isNondegenerate.tames_iff.mpr
  intro x
  rw [almostComplexStructureAt_cappedAlmostComplex]
  exact Floer.tames_cappedAlmostComplex _ r L w ()

/-- Compatible end families give compatible capped structures. -/
theorem compatible_cappedAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (r L : ℝ) (w : ℂ) :
    σ.Compatible (h₀.cappedAlmostComplex J hJ hJp hJs r L w) := by
  apply h₀.isNondegenerate.compatible_iff.mpr
  intro x
  rw [almostComplexStructureAt_cappedAlmostComplex]
  exact Floer.compatible_cappedAlmostComplex _
    (fun q t _ => h₀.isNondegenerate.compatible_iff.mp (hJc q t) x) r L w ()

/-- The Cayley coordinate, relative to `J₀`, characterizes the capped structure on every tangent
fiber: it is `β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J_q(t_q))`. -/
@[simp]
theorem cayley_cappedAlmostComplex (r L : ℝ) (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.cappedAlmostComplex J hJ hJp hJs r L w).almostComplexStructureAt x) =
      smoothTransition r • ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
        smoothTransition (L + 3 - q.endSign * (q.endCoord w).re)) •
        (J₀.almostComplexStructureAt x).cayley
          ((J q (q.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_cappedAlmostComplex, Floer.cayley_cappedAlmostComplex]

/-- For `r ≤ 0` the capped structure is the domain-independent base structure `J₀`. -/
theorem cappedAlmostComplex_of_nonpos {r : ℝ} (hr : r ≤ 0) (L : ℝ) (w : ℂ) :
    h₀.cappedAlmostComplex J hJ hJp hJs r L w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex,
      Floer.cappedAlmostComplex_of_nonpos _ hr]

/-- The capped structure does not depend on `r ≥ 1`. -/
theorem cappedAlmostComplex_of_one_le {r : ℝ} (hr : 1 ≤ r) (L : ℝ) :
    h₀.cappedAlmostComplex J hJ hJp hJs r L = h₀.cappedAlmostComplex J hJ hJp hJs 1 L := by
  funext w
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_cappedAlmostComplex, almostComplexStructureAt_cappedAlmostComplex,
    Floer.cappedAlmostComplex_of_one_le _ hr]

/-- **The structure is `J₀` near the poles.** Outside the compact truncation `S_{L + 3}` of the
pair of pants, the capped structure is the base structure `J₀`. -/
theorem cappedAlmostComplex_eq_base_of_notMem_truncation (r : ℝ) {L : ℝ} {w : ℂ}
    (hw : w ∉ truncation (L + 3)) : h₀.cappedAlmostComplex J hJ hJp hJs r L w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex,
      Floer.cappedAlmostComplex_eq_base_of_notMem_truncation _ r hw]

/-- **The structure is `J₀` near the poles `0` and `1`.** -/
theorem eventually_cappedAlmostComplex_eq_base_of_eq_zero_or_eq_one (r L : ℝ) {c : ℂ}
    (hc : c = 0 ∨ c = 1) : ∀ᶠ w in 𝓝 c, h₀.cappedAlmostComplex J hJ hJp hJs r L w = J₀ := by
  filter_upwards [(isCompact_truncation (L + 3)).isClosed.isOpen_compl.mem_nhds
    (notMem_truncation_of_eq_zero_or_eq_one hc _)] with w hw
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ J hJ hJp hJs r hw

/-- **The structure is `J₀` near the pole `∞`.** -/
theorem eventually_cocompact_cappedAlmostComplex_eq_base (r L : ℝ) :
    ∀ᶠ w in cocompact ℂ, h₀.cappedAlmostComplex J hJ hJp hJs r L w = J₀ := by
  filter_upwards [(isCompact_truncation (L + 3)).compl_mem_cocompact] with w hw
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ J hJ hJp hJs r hw

/-- **The neck.** For `r ≥ 1`, on the part `2 ≤ ±s ≤ L + 2` of the end `q`, the capped structure
at the point with end coordinates `z = s + i t` is the end structure `J_q(t)`. -/
theorem cappedAlmostComplex_cylindricalEndLift_of_mem_Icc {r L : ℝ} (hr : 1 ≤ r) {q : Puncture}
    {z : ℂ} (hz : q.endSign * z.re ∈ Icc 2 (L + 2)) :
    h₀.cappedAlmostComplex J hJ hJp hJs r L (q.cylindricalEndLift z) = J q z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    have hp : Function.Periodic
        (fun t (_ : Unit) => (J q t).almostComplexStructureAt x) 1 := fun t => by
      simp only [hJp q t]
    rw [almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_cylindricalEndLift_of_mem_Icc _ hp hr hz ()

/-- **The PSS plane pieces do not depend on the neck length.** Beyond the neck of length `L ≥ 0`,
the capped structure on the end `q` is the structure with `L = 0` translated by `L` along the
end. -/
theorem cappedAlmostComplex_cylindricalEndLift_add_endSign_mul (r : ℝ) {L : ℝ} (hL : 0 ≤ L)
    {q : Puncture} {z : ℂ} (hz : 2 ≤ q.endSign * z.re) :
    h₀.cappedAlmostComplex J hJ hJp hJs r L (q.cylindricalEndLift (z + ↑(q.endSign * L))) =
      h₀.cappedAlmostComplex J hJ hJp hJs r 0 (q.cylindricalEndLift z) :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    have hp : Function.Periodic
        (fun t (_ : Unit) => (J q t).almostComplexStructureAt x) 1 := fun t => by
      simp only [hJp q t]
    rw [almostComplexStructureAt_cappedAlmostComplex, almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_cylindricalEndLift_add_endSign_mul _ hp r hL hz ()

/-- **The structure is the pair-of-pants structure up to the necks.** For `r ≥ 1`, at points of the
pair of pants where the signed longitudinal coordinate of every end is at most `L + 2`, such as the
points of the truncation `S_{L + 2}`, the capped structure is the pair-of-pants structure. -/
theorem cappedAlmostComplex_eq_pairOfPantsAlmostComplex {r L : ℝ} (hr : 1 ≤ r)
    (w : ThricePuncturedSphere) (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L + 2) :
    h₀.cappedAlmostComplex J hJ hJp hJs r L w = h₀.pairOfPantsAlmostComplex J hJ hJp hJs w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex]
    exact Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex _ hr hw ()

/-- **The structure is smooth.** The capped structures are jointly `C^n` along any `C^n` family of
cutoff parameters, neck lengths, domain points and target points. The domain points may pass
through the poles `0` and `1`. This formulation also allows independent external manifold
parameters. -/
theorem contMDiff_cappedAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] {r L : N → ℝ} {f : N → ℂ} {b : N → M}
    (hr : ContMDiff I' 𝓘(ℝ) n r) (hL : ContMDiff I' 𝓘(ℝ) n L) (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f)
    (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.cappedAlmostComplex J hJ hJp hJs (r p) (L p) (f p)).toEndomorphism (b p))) := by
  intro p
  have hrLf : ContMDiffAt I' 𝓘(ℝ, ℝ × ℝ × ℂ) n (fun p => (r p, L p, f p)) p :=
    (hr p).prodMk_space ((hL p).prodMk_space (hf p))
  simp only [toEndomorphism_cappedAlmostComplex]
  exact ((contMDiffAt_cappedEnd h₀ J hJ hJp hJs (r p) (L p) (f p) (b p)).of_le
    ENat.LEInfty.out).comp p (hrLf.prodMk hb.contMDiffAt)

/-! ### The comparison family -/

/-- The comparison family of almost complex structures on the three-pole sphere in `M`: the capped
structure with cutoff parameter `3R - 1` and the neck length
`L = TauCeti.Floer.comparisonNeckLength R`. It is the domain-independent `J₀` for `R ≤ 1/3`, is
switched on for `1/3 ≤ R ≤ 2/3`, and its necks grow without bound as `R → ∞`. -/
def cappedComparisonAlmostComplex (R : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  h₀.cappedAlmostComplex J hJ hJp hJs (3 * R - 1) (Floer.comparisonNeckLength R) w

theorem cappedComparisonAlmostComplex_def (R : ℝ) :
    h₀.cappedComparisonAlmostComplex J hJ hJp hJs R =
      h₀.cappedAlmostComplex J hJ hJp hJs (3 * R - 1) (Floer.comparisonNeckLength R) :=
  (rfl)

/-- For `R ≤ 1/3`, in particular at the start `R = 0` of the family, the structure is the
domain-independent base structure `J₀`. -/
theorem cappedComparisonAlmostComplex_of_le {R : ℝ} (hR : R ≤ 1 / 3) (w : ℂ) :
    h₀.cappedComparisonAlmostComplex J hJ hJp hJs R w = J₀ :=
  cappedAlmostComplex_of_nonpos h₀ J hJ hJp hJs (by linarith) _ w

/-- The family is constant on the collar `2/3 ≤ R ≤ 3/2`, where the structure is fully switched
on and has no necks. -/
theorem cappedComparisonAlmostComplex_of_mem_Icc {R : ℝ} (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    h₀.cappedComparisonAlmostComplex J hJ hJp hJs R = h₀.cappedAlmostComplex J hJ hJp hJs 1 0 := by
  rw [cappedComparisonAlmostComplex_def, Floer.comparisonNeckLength_of_le hR.2,
    cappedAlmostComplex_of_one_le h₀ J hJ hJp hJs (by linarith [hR.1])]

/-- For `R ≥ 2` the structure is fully switched on and has necks of length `R - 1`. -/
theorem cappedComparisonAlmostComplex_of_two_le {R : ℝ} (hR : 2 ≤ R) :
    h₀.cappedComparisonAlmostComplex J hJ hJp hJs R =
      h₀.cappedAlmostComplex J hJ hJp hJs 1 (R - 1) := by
  rw [cappedComparisonAlmostComplex_def, Floer.comparisonNeckLength_of_ge hR,
    cappedAlmostComplex_of_one_le h₀ J hJ hJp hJs (by linarith)]

/-- **The comparison family is smooth** jointly along any `C^n` family of family parameters `R`,
domain points and target points. -/
theorem contMDiff_cappedComparisonAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] {R : N → ℝ} {f : N → ℂ} {b : N → M}
    (hR : ContMDiff I' 𝓘(ℝ) n R) (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.cappedComparisonAlmostComplex J hJ hJp hJs (R p) (f p)).toEndomorphism
          (b p))) :=
  contMDiff_cappedAlmostComplex h₀ J hJ hJp hJs
    ((contDiff_const.mul contDiff_id |>.sub contDiff_const).contMDiff.comp hR)
    (((Floer.contDiff_comparisonNeckLength (n := ⊤)).contMDiff.of_le ENat.LEInfty.out).comp hR)
    hf hb

end TauCeti.SmoothTwoForm.Compatible
