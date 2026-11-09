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

The comparison between the pair-of-pants product and the quantum product attaches a
Piunikhin–Salamon–Schwarz (PSS) plane to each of the three ends of a pair of pants, which gives a
sphere with three poles `0`, `1` and `∞`. `TauCeti.Floer.cappedAlmostComplex` constructs the
domain-dependent almost complex structures of the resulting one-parameter family on a fixed
symplectic vector space. This file constructs them on the tangent bundle of a manifold `M` with a
nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀` and smooth `σ`-tame structures
`J q t` for the ends `q` and times `t`. For a cutoff parameter `r`, a neck length `L` and a point
`w ∈ ℂ`, the smooth almost complex structure
`TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex h₀ J hJ r L w` is, on the tangent space at
every point `x`, the linear capped structure of `J₀ x` and the end structures `J q t x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cappedAlmostComplex`). Its Cayley
coordinate relative to `J₀` is `β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J q t_q)`, where
`(s_q, t_q)` are the end coordinates, `σ_q = ±s_q` and `β` is the smooth transition function.

* It is tame, and compatible when the end structures are.
* It is `J₀` for `r ≤ 0`, it does not depend on `r ≥ 1`, and it is `J₀` outside the truncation
  `S_{L + 3}`, in particular near the three poles.
* For `r ≥ 1` and period-one end structures, it is `J q t` along the neck `2 ≤ σ_q ≤ L + 2`, it
  is the structure for `L = 0` translated by `L` beyond the neck, and it is the pair-of-pants
  structure `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex` wherever every
  `σ_q ≤ L + 2`.
* For period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly `C^n` along
  `C^n` families of cutoff parameters, neck lengths, points of `ℂ`, including the poles `0` and
  `1`, and points of `M`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedAlmostComplex`).

The comparison family `TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex` takes the
cutoff parameter `3R - 1` and the neck length `TauCeti.Floer.comparisonNeckLength R`. It starts at
the domain-independent `J₀`, has no necks on the collar `2/3 ≤ R ≤ 3/2`, has necks of length
`R - 1` for `R ≥ 2`, and is smooth in `R`.

The structure is the end-weighted structure
`TauCeti.SmoothTwoForm.Compatible.endWeightedAlmostComplex` with the weights above, so tameness
and compatibility come from it, and every other property except smoothness holds fiberwise and
follows from the linear construction. Smoothness away from the poles follows from
`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_endWeightedAlmostComplex`; near the poles `0` and
`1` the structure is `J₀`, locally uniformly in the neck length.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures, and Section 12.1, on the PSS isomorphism.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Filter
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

/-- The weight of the end `q` in the Cayley coordinate of the capped structure. -/
private def cappedWeight (r L : ℝ) (q : Puncture) (w : ℂ) : ℝ :=
  smoothTransition r * (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
    smoothTransition (L + 3 - q.endSign * (q.endCoord w).re))

/-- The weights lie in `[0, 1]`. -/
private theorem cappedWeight_mem_Icc (r L : ℝ) (q : Puncture) (w : ℂ) :
    cappedWeight r L q w ∈ Icc 0 1 :=
  unitInterval.mul_mem ⟨smoothTransition.nonneg r, smoothTransition.le_one r⟩
    (unitInterval.mul_mem ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
      ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩)

/-- The weight of the end `q` vanishes off the part `±s > 1` of that end. -/
private theorem endSign_mul_re_endCoord_pos_of_cappedWeight_ne_zero {r L : ℝ} {q : Puncture}
    {w : ℂ} (h : cappedWeight r L q w ≠ 0) : 0 < q.endSign * (q.endCoord w).re := by
  by_contra! h'
  refine h ?_
  rw [cappedWeight, smoothTransition.zero_of_nonpos (x := q.endSign * (q.endCoord w).re - 1)
    (by linarith), zero_mul, mul_zero]

/-- The almost complex structure on `M` of the pair of pants capped by three PSS planes along
necks of length `L`, moved along the segment from `J₀` by the cutoff `β(r)`, at the point
`w ∈ ℂ`. It is the end-weighted structure
`TauCeti.SmoothTwoForm.Compatible.endWeightedAlmostComplex` with the weights
`β(r) β(σ_q - 1) β(L + 3 - σ_q)`, so on each tangent space it is the linear capped structure
`TauCeti.Floer.cappedAlmostComplex` of `J₀` and the end structures `J q t`. -/
def cappedAlmostComplex (r L : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  h₀.endWeightedAlmostComplex J hJ (cappedWeight r L) (cappedWeight_mem_Icc r L)
    (fun _ _ => endSign_mul_re_endCoord_pos_of_cappedWeight_ne_zero) w

/-- The capped structure is tamed by `σ`. -/
theorem tames_cappedAlmostComplex (r L : ℝ) (w : ℂ) :
    σ.Tames (h₀.cappedAlmostComplex J hJ r L w) :=
  tames_endWeightedAlmostComplex h₀ J hJ _ _ _ w

/-- The value on a tangent fiber is precisely the linear capped structure there. -/
theorem almostComplexStructureAt_cappedAlmostComplex (r L : ℝ) (w : ℂ) (x : M) :
    (h₀.cappedAlmostComplex J hJ r L w).almostComplexStructureAt x =
      Floer.cappedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun q t _ => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) r L w () := by
  -- Both structures are tame and have the same Cayley coordinate relative to `J₀`.
  refine (h₀.compatibleAt x).eq_of_cayley_eq
    (h₀.isNondegenerate.tames_iff.mp (tames_cappedAlmostComplex h₀ J hJ r L w) x)
    (Floer.tames_cappedAlmostComplex (h₀.compatibleAt x) r L w ()) ?_
  rw [cappedAlmostComplex, cayley_endWeightedAlmostComplex, Floer.cayley_cappedAlmostComplex,
    Finset.smul_sum]
  simp only [smul_smul, cappedWeight]

/-- The capped structure is `σ`-compatible when the structures on the ends are. -/
theorem compatible_cappedAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (r L : ℝ) (w : ℂ) :
    σ.Compatible (h₀.cappedAlmostComplex J hJ r L w) :=
  compatible_endWeightedAlmostComplex h₀ J hJ _ _ _ hJc w

/-- On every tangent fiber, the Cayley coordinate of the capped structure relative to `J₀` is
`β(r) • ∑ q, β(σ_q - 1) β(L + 3 - σ_q) • cayley (J q t_q)`. This characterizes the structure,
since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_cappedAlmostComplex (r L : ℝ) (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.cappedAlmostComplex J hJ r L w).almostComplexStructureAt x) =
      smoothTransition r • ∑ q, (smoothTransition (q.endSign * (q.endCoord w).re - 1) *
        smoothTransition (L + 3 - q.endSign * (q.endCoord w).re)) •
        (J₀.almostComplexStructureAt x).cayley
          ((J q (q.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_cappedAlmostComplex, Floer.cayley_cappedAlmostComplex]

variable {r L : ℝ}

/-- For `r ≤ 0` the capped structure is the base structure `J₀`. -/
theorem cappedAlmostComplex_of_nonpos (hr : r ≤ 0) (L : ℝ) (w : ℂ) :
    h₀.cappedAlmostComplex J hJ r L w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_of_nonpos (h₀.compatibleAt x) hr L w ()

/-- The capped structure does not depend on `r ≥ 1`. -/
theorem cappedAlmostComplex_of_one_le (hr : 1 ≤ r) (L : ℝ) :
    h₀.cappedAlmostComplex J hJ r L = h₀.cappedAlmostComplex J hJ 1 L := by
  funext w
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  rw [almostComplexStructureAt_cappedAlmostComplex, almostComplexStructureAt_cappedAlmostComplex,
    Floer.cappedAlmostComplex_of_one_le (h₀.compatibleAt x) hr L]

/-- **The structure is `J₀` near the poles.** Outside the compact truncation `S_{L + 3}` of the
pair of pants, the capped structure is the base structure `J₀`. -/
theorem cappedAlmostComplex_eq_base_of_notMem_truncation (r : ℝ) {w : ℂ}
    (hw : w ∉ truncation (L + 3)) : h₀.cappedAlmostComplex J hJ r L w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_eq_base_of_notMem_truncation (h₀.compatibleAt x) r hw ()

/-- **The structure is `J₀` near the poles `0` and `1`**, locally uniformly in the neck length. -/
theorem eventually_cappedAlmostComplex_eq_base_of_eq_zero_or_eq_one {c : ℂ} (hc : c = 0 ∨ c = 1)
    (L₀ : ℝ) :
    ∀ᶠ p : ℂ × ℝ in 𝓝 (c, L₀), ∀ r, h₀.cappedAlmostComplex J hJ r p.2 p.1 = J₀ := by
  have hT : c ∉ truncation (L₀ + 4) := fun h => by
    obtain ⟨h₀, h₁, -⟩ := mem_truncation.1 h
    rcases hc with rfl | rfl
    exacts [h₀ rfl, h₁ rfl]
  have hw : ∀ᶠ p : ℂ × ℝ in 𝓝 (c, L₀), p.1 ∉ truncation (L₀ + 4) :=
    continuous_fst.continuousAt.eventually
      ((isCompact_truncation _).isClosed.isOpen_compl.mem_nhds hT)
  have hL : ∀ᶠ p : ℂ × ℝ in 𝓝 (c, L₀), p.2 < L₀ + 1 :=
    continuous_snd.continuousAt.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hw, hL] with p hpw hpL r
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ J hJ r
    fun h => hpw (truncation_mono (by linarith) h)

/-- **The structure is `J₀` near the pole `∞`.** -/
theorem eventually_cocompact_cappedAlmostComplex_eq_base (r : ℝ) :
    ∀ᶠ w in cocompact ℂ, h₀.cappedAlmostComplex J hJ r L w = J₀ := by
  filter_upwards [(isCompact_truncation (L + 3)).compl_mem_cocompact] with w hw
  exact cappedAlmostComplex_eq_base_of_notMem_truncation h₀ J hJ r hw

variable {q : Puncture}

/-- **The neck.** If `J q` has period one in `t` and `r ≥ 1`, then on the part
`2 ≤ ±s ≤ L + 2` of the end `q`, the capped structure at the point with end coordinates
`z = s + i t` is `J q t`. -/
theorem cappedAlmostComplex_cylindricalEndLift_of_mem_Icc (hJp : Function.Periodic (J q) 1)
    (hr : 1 ≤ r) {z : ℂ} (hz : q.endSign * z.re ∈ Icc 2 (L + 2)) :
    h₀.cappedAlmostComplex J hJ r L (q.cylindricalEndLift z) = J q z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_cylindricalEndLift_of_mem_Icc (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) hr hz ()

/-- **The PSS plane pieces do not depend on the neck length.** If `J q` has period one in `t`,
then beyond the neck of length `L ≥ 0` the capped structure on the end `q` is the structure with
`L = 0` translated by `L` along the end. -/
theorem cappedAlmostComplex_cylindricalEndLift_add_endSign_mul (hJp : Function.Periodic (J q) 1)
    (r : ℝ) (hL : 0 ≤ L) {z : ℂ} (hz : 2 ≤ q.endSign * z.re) :
    h₀.cappedAlmostComplex J hJ r L (q.cylindricalEndLift (z + ↑(q.endSign * L))) =
      h₀.cappedAlmostComplex J hJ r 0 (q.cylindricalEndLift z) :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex, almostComplexStructureAt_cappedAlmostComplex]
    exact Floer.cappedAlmostComplex_cylindricalEndLift_add_endSign_mul (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) r hL hz ()

/-- **The structure is the pair-of-pants structure up to the necks.** For `r ≥ 1`, at points of
the pair of pants where the signed longitudinal coordinate of every end is at most `L + 2`, the
capped structure is the pair-of-pants structure. -/
theorem cappedAlmostComplex_eq_pairOfPantsAlmostComplex (hr : 1 ≤ r) {w : ThricePuncturedSphere}
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ L + 2) :
    h₀.cappedAlmostComplex J hJ r L w = h₀.pairOfPantsAlmostComplex J hJ w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_cappedAlmostComplex,
      almostComplexStructureAt_pairOfPantsAlmostComplex]
    exact Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex (h₀.compatibleAt x) hr hw ()

/-! ### Smoothness -/

section Smooth

variable {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [ENat.LEInfty n]

/-- The weight of the end `q` is `C^n` along a `C^n` family that stays away from the center of
the end. -/
private theorem contMDiffAt_cappedWeight {r L : N → ℝ} {f : N → ℂ} {y₀ : N}
    (hr : ContMDiffAt I' 𝓘(ℝ) n r y₀) (hL : ContMDiffAt I' 𝓘(ℝ) n L y₀)
    (hf : ContMDiffAt I' 𝓘(ℝ, ℂ) n f y₀) (q : Puncture) (hq : f y₀ ≠ q.endCenter) :
    ContMDiffAt I' 𝓘(ℝ) n (fun y => cappedWeight (r y) (L y) q (f y)) y₀ := by
  have hβ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n smoothTransition :=
    ((smoothTransition.contDiff (n := ⊤)).of_le ENat.LEInfty.out).contMDiff
  have hσ : ContMDiffAt I' 𝓘(ℝ) n (fun y => q.endSign * (q.endCoord (f y)).re) y₀ :=
    (contDiffAt_const.mul (q.contDiffAt_re_endCoord hq)).contMDiffAt.comp y₀ hf
  -- Products of real functions are scalar products.
  exact (hβ.contMDiffAt.comp y₀ hr).smul ((hβ.contMDiffAt.comp y₀ (hσ.sub contMDiffAt_const)).smul
    (hβ.contMDiffAt.comp y₀ ((hL.add contMDiffAt_const).sub hσ)))

/-- **The structure is smooth.** For end structures which have period one in `t` and are `C^n`
on `ℝ × M`, the capped structures are `C^n` along every `C^n` family of cutoff parameters `r`,
neck lengths `L`, points `f` of `ℂ`, including the poles `0` and `1`, and points `b` of `M`. -/
theorem contMDiff_cappedAlmostComplex (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    {r L : N → ℝ} {f : N → ℂ} {b : N → M} (hr : ContMDiff I' 𝓘(ℝ) n r)
    (hL : ContMDiff I' 𝓘(ℝ) n L) (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.cappedAlmostComplex J hJ (r y) (L y) (f y)).toEndomorphism (b y))) := by
  intro y₀
  by_cases hS : f y₀ = 0 ∨ f y₀ = 1
  · -- Near the poles `0` and `1`, the structure is `J₀`.
    have hp : Tendsto (fun y => (f y, L y)) (𝓝 y₀) (𝓝 (f y₀, L y₀)) :=
      (hf.continuous.prodMk hL.continuous).tendsto y₀
    exact SmoothAlmostComplexStructure.contMDiffAt_toEndomorphism_of_eventuallyEq (hb y₀)
      ((hp.eventually (eventually_cappedAlmostComplex_eq_base_of_eq_zero_or_eq_one h₀ J hJ hS
        (L y₀))).mono fun y hy => hy (r y))
  -- Away from the poles, the Cayley coordinate is a sum of the end structures read at the
  -- angular coordinates, with weights that are smooth there.
  have hq (q : Puncture) : f y₀ ≠ q.endCenter := ne_endCenter (not_or.mp hS) q
  simp only [cappedAlmostComplex]
  exact contMDiffAt_endWeightedAlmostComplex h₀ J hJ (c := fun y => cappedWeight (r y) (L y))
    (hb y₀) (fun q => contMDiffAt_cappedWeight (hr y₀) (hL y₀) (hf y₀) q (hq q))
    fun q => q.contMDiffAt_toEndomorphism_comp_im_endCoord (hJp q) (hJs q) (hf y₀) (hb y₀) (hq q)

end Smooth

/-! ### The comparison family -/

/-- The comparison family of almost complex structures on `M` over the three-pole sphere: the
capped structure with cutoff parameter `3R - 1` and the neck length
`L = TauCeti.Floer.comparisonNeckLength R`. It is the domain-independent `J₀` for `R ≤ 1/3`, is
switched on for `1/3 ≤ R ≤ 2/3`, and its necks grow without bound as `R → ∞`. -/
def cappedComparisonAlmostComplex (R : ℝ) : ℂ → SmoothAlmostComplexStructure I M :=
  h₀.cappedAlmostComplex J hJ (3 * R - 1) (Floer.comparisonNeckLength R)

variable {R : ℝ}

theorem cappedComparisonAlmostComplex_def (R : ℝ) :
    h₀.cappedComparisonAlmostComplex J hJ R =
      h₀.cappedAlmostComplex J hJ (3 * R - 1) (Floer.comparisonNeckLength R) :=
  (rfl)

/-- For `R ≤ 1/3`, in particular at the start `R = 0` of the family, the structure is the
domain-independent base structure `J₀`. -/
theorem cappedComparisonAlmostComplex_of_le (hR : R ≤ 1 / 3) (w : ℂ) :
    h₀.cappedComparisonAlmostComplex J hJ R w = J₀ :=
  cappedAlmostComplex_of_nonpos h₀ J hJ (by linarith) _ w

/-- The family is constant on the collar `2/3 ≤ R ≤ 3/2`, where the structure is fully switched
on and has no necks. -/
theorem cappedComparisonAlmostComplex_of_mem_Icc (hR : R ∈ Icc (2 / 3 : ℝ) (3 / 2)) :
    h₀.cappedComparisonAlmostComplex J hJ R = h₀.cappedAlmostComplex J hJ 1 0 := by
  rw [cappedComparisonAlmostComplex_def, Floer.comparisonNeckLength_of_le hR.2,
    cappedAlmostComplex_of_one_le h₀ J hJ (by linarith [hR.1])]

/-- For `R ≥ 2` the structure is fully switched on and has necks of length `R - 1`. -/
theorem cappedComparisonAlmostComplex_of_two_le (hR : 2 ≤ R) :
    h₀.cappedComparisonAlmostComplex J hJ R = h₀.cappedAlmostComplex J hJ 1 (R - 1) := by
  rw [cappedComparisonAlmostComplex_def, Floer.comparisonNeckLength_of_ge hR,
    cappedAlmostComplex_of_one_le h₀ J hJ (by linarith)]

/-- **The comparison family is smooth** along every `C^n` family of family parameters `R`, points
`f` of `ℂ` and points `b` of `M`. -/
theorem contMDiff_cappedComparisonAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    {R : N → ℝ} {f : N → ℂ} {b : N → M} (hR : ContMDiff I' 𝓘(ℝ) n R)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.cappedComparisonAlmostComplex J hJ (R y) (f y)).toEndomorphism (b y))) :=
  contMDiff_cappedAlmostComplex h₀ J hJ hJp hJs
    (((contDiff_const.mul contDiff_id).sub contDiff_const :
      ContDiff ℝ n fun R : ℝ => 3 * R - 1).contMDiff.comp hR)
    ((Floer.contDiff_comparisonNeckLength (n := ⊤).of_le ENat.LEInfty.out).contMDiff.comp hR)
    hf hb

end TauCeti.SmoothTwoForm.Compatible
