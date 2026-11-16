/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capping

/-!
# Almost complex structures along the input-exchange family in a manifold

Graded commutativity of the pair-of-pants product compares the pair of pants `S = ℂ ∖ {0, 1}` with
its inputs exchanged by the holomorphic involution `w ↦ 1 - w`. The comparison is the
input-exchange family of Floer data `(K_c, J_c)`, `0 ≤ c ≤ 1`, whose output end is the end at `∞`
recentred at `c`. Its perturbations `TauCeti.Floer.exchangePerturbation H c` are defined for any
target, and `TauCeti.Floer.exchangeAlmostComplex` constructs its almost complex structures on a
fixed symplectic vector space. This file constructs them on the tangent bundle of a manifold `M`
with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀` and smooth `σ`-tame structures `J q t`
for the ends `q` and times `t`. For `c ∈ ℝ` and `w ∈ ℂ`, the smooth almost complex structure
`TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex h₀ J hJ c w` is the pair-of-pants
structure of the input structures `J 0`, `J 1` (with output structure `J₀`) on the disc
`‖w - c‖ ≤ 2 exp (2π)`, and the negative plane structure
`TauCeti.SmoothTwoForm.Compatible.negativePlaneAlmostComplex` of `J ∞` translated by `c` off it. On
the tangent space at every point `x` it is the linear input-exchange structure of `J₀ x` and the
end structures `J q t x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_exchangeAlmostComplex`), so its
properties follow fiberwise from the linear construction:

* it is tame, and compatible when the end structures are;
* for `-1 ≤ c ≤ 2` its Cayley coordinate relative to `J₀` is
  `∑_{q ∈ {0, 1}} β(s_q - 1) • cayley (J q t_q) + β(-s_∞ - 1) • cayley (J ∞ t_∞)`, where
  `(s_q, t_q)` are the end coordinates of `w` for the inputs, `(s_∞, t_∞)` those of `w - c` for the
  output and `β` is the smooth transition function
  (`TauCeti.SmoothTwoForm.Compatible.cayley_exchangeAlmostComplex`);
* at `c = 0` it is the pair-of-pants structure
  `TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex`
  (`TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex_zero`), and at `c = 1`, if `J ∞` has
  period one, its value at `1 - w` is the pair-of-pants structure of the exchanged end structures
  `TauCeti.Floer.exchangeEndData J` at `w`
  (`TauCeti.SmoothTwoForm.Compatible.exchangeAlmostComplex_one`);
* for `0 ≤ c ≤ 1` and period-one end structures, it is `J q t` far out on each input end in the
  end lift `φ_q`, and `J ∞ t` far out on the output end in the end lift `c + φ_∞`, the end
  coordinates in which the perturbations of the family are `H_q(t) dt`;
* for period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly `C^n` along
  `C^n` families of parameters `-1 < c < 2`, points of `S` and points of `M`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_exchangeAlmostComplex`).

Finally, the member `c = 1` of the family of Floer data is the pullback of the pair-of-pants data
with exchanged inputs along `w ↦ 1 - w`: if `u` solves the Floer equation in `M` at `1 - w` for the
exchanged pair-of-pants data, then `u (1 - ·)` solves it at `w` for `(K_1, J_1)`
(`TauCeti.SmoothTwoForm.Compatible.isComplexLinearMap_perturbedMFDeriv_exchange_one`). This uses
the naturality of the intrinsic perturbed derivative under holomorphic changes of domain
coordinates (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_perturbationPullback`).

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data on punctured surfaces whose ends are related by automorphisms.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Bundle Set Real Manifold Topology Function
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : Puncture → ℝ → SmoothAlmostComplexStructure I M) (hJ : ∀ q t, σ.Tames (J q t))

omit [FiniteDimensional ℝ E] in
include h₀ hJ in
/-- The input structures of `J`, with the output structure replaced by `J₀`, are tame. -/
private theorem tames_update_inf (q : Puncture) (t : ℝ) :
    σ.Tames (update J inf (fun _ => J₀) q t) := by
  rcases eq_or_ne q inf with rfl | hq
  · simpa using h₀.tames
  · simpa [update_of_ne hq] using hJ q t

/-- The input part of the family at `w ∈ ℂ`: the pair-of-pants structure of the input structures
of `J`, with output structure `J₀`, written as an end-weighted structure so that it is defined at
every point of `ℂ`. -/
private def inputAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M :=
  h₀.endWeightedAlmostComplex (update J inf fun _ => J₀) (tames_update_inf h₀ J hJ)
    (fun q w => smoothTransition (q.endSign * (q.endCoord w).re - 1))
    (fun _ _ => mem_Icc.2 ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩)
    (fun _ _ hq => zero_lt_one.trans (Floer.one_lt_endSign_mul_re_endCoord hq).1) w

/-- On a tangent fiber, the input part is the linear pair-of-pants structure of the input
structures there. -/
private theorem almostComplexStructureAt_inputAlmostComplex (w : ℂ) (x : M) :
    (inputAlmostComplex h₀ J hJ w).almostComplexStructureAt x =
      Floer.pairOfPantsAlmostComplex (h₀.compatibleAt x)
        (update (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x) inf
          fun _ _ => J₀.almostComplexStructureAt x)
        (Floer.tames_update_inf_base (h₀.compatibleAt x).tames
          fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w () := by
  refine (h₀.compatibleAt x).eq_of_cayley_eq
    (h₀.isNondegenerate.tames_iff.mp (tames_endWeightedAlmostComplex h₀ _ _ _ _ _ w) x)
    (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ()) ?_
  rw [inputAlmostComplex, cayley_endWeightedAlmostComplex, Floer.cayley_pairOfPantsAlmostComplex]
  refine Finset.sum_congr rfl fun q _ => ?_
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · simp [update_of_ne hq]

/-- Far from both inputs, the input part is the base structure `J₀`. -/
private theorem inputAlmostComplex_eq_base {w : ℂ} (hw₀ : 1 / 2 ≤ ‖w‖) (hw₁ : 1 / 2 ≤ ‖w - 1‖) :
    inputAlmostComplex h₀ J hJ w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_inputAlmostComplex]
    exact Floer.pairOfPantsAlmostComplex_update_inf_base_eq
      (hJb := fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) (h₀.compatibleAt x)
      hw₀ hw₁ ()

omit [FiniteDimensional ℝ E] in
/-- The input structures of `J`, with the output structure replaced by `J₀`, inherit periodicity
and joint `C^n` regularity on `ℝ × M` from `J`. -/
private theorem periodic_and_contMDiff_update_inf {n : ℕ∞ω} [ENat.LEInfty n]
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2))) (q : Puncture) :
    Periodic (update J inf (fun _ => J₀) q) 1 ∧
      ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          p.2 ((update J inf (fun _ => J₀) q p.1).toEndomorphism p.2)) :=
  (forall_update_iff J fun _ g => Periodic g 1 ∧
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((g p.1).toEndomorphism p.2))).2
    ⟨⟨fun _ => rfl, (J₀.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp contMDiff_snd⟩,
      fun q _ => ⟨hJp q, hJs q⟩⟩ q

/-- The input part is `C^n` along `C^n` families of domain points of `S` and target points, for
period-one end structures which are jointly `C^n` on `ℝ × M`. -/
private theorem contMDiffAt_inputAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    {f : N → ℂ} {b : N → M} {y₀ : N} (hf : ContMDiffAt I' 𝓘(ℝ, ℂ) n f y₀)
    (hb : ContMDiffAt I' I n b y₀) (hS : f y₀ ≠ 0 ∧ f y₀ ≠ 1) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((inputAlmostComplex h₀ J hJ (f y)).toEndomorphism (b y))) y₀ :=
  have h := periodic_and_contMDiff_update_inf (J₀ := J₀) J hJp hJs
  contMDiffAt_endWeightedAlmostComplex h₀ _ _ (hb := hb)
    (fun q => Floer.contMDiffAt_smoothTransition_endCoord_comp q 1 hf (ne_endCenter hS q))
    fun q => q.contMDiffAt_toEndomorphism_comp_im_endCoord (h q).1 (h q).2 hf hb
      (ne_endCenter hS q)

/-- **The input-exchange family of almost complex structures on a manifold.** For `c ∈ ℝ`,
relative to a `σ`-compatible base structure `J₀`, this is the pair-of-pants structure of the input
structures of `J` (with output structure `J₀`) on the disc `‖w - c‖ ≤ 2 exp (2π)`, and the negative
plane structure of the output structures `J ∞` translated by `c` off that disc. Its output end is
the end at `∞` recentred at `c`, as for the perturbations `TauCeti.Floer.exchangePerturbation`. -/
def exchangeAlmostComplex (c : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if ‖w - c‖ ≤ 2 * Real.exp (2 * π) then inputAlmostComplex h₀ J hJ w
  else h₀.negativePlaneAlmostComplex (J inf) (hJ inf) (w - c)

variable {c : ℝ} {w : ℂ}

/-- Off the disc `‖w - c‖ ≤ 2 exp (2π)` the member `c` of the family is the negative plane
structure of the output structures, translated by `c`. -/
theorem exchangeAlmostComplex_of_lt_norm (hw : 2 * Real.exp (2 * π) < ‖w - c‖) :
    h₀.exchangeAlmostComplex J hJ c w = h₀.negativePlaneAlmostComplex (J inf) (hJ inf) (w - c) := by
  simp only [exchangeAlmostComplex, hw.not_ge, ↓reduceIte]

/-- **The fiberwise description.** On the tangent space at `x`, the member `c` of the family at
`w` is the linear input-exchange structure `TauCeti.Floer.exchangeAlmostComplex` of `J₀ x` and the
end structures `J q t x`. -/
theorem almostComplexStructureAt_exchangeAlmostComplex (c : ℝ) (w : ℂ) (x : M) :
    (h₀.exchangeAlmostComplex J hJ c w).almostComplexStructureAt x =
      Floer.exchangeAlmostComplex (h₀.compatibleAt x)
        (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) c w () := by
  rcases le_or_gt ‖w - c‖ (2 * Real.exp (2 * π)) with hw | hw
  · rw [Floer.exchangeAlmostComplex_of_norm_le _ hw,
      ← almostComplexStructureAt_inputAlmostComplex h₀ J hJ]
    simp only [exchangeAlmostComplex, hw, ↓reduceIte]
  · rw [Floer.exchangeAlmostComplex_of_lt_norm _ hw, exchangeAlmostComplex_of_lt_norm h₀ J hJ hw,
      almostComplexStructureAt_negativePlaneAlmostComplex]

/-- Every member of the family is tamed by `σ`. -/
theorem tames_exchangeAlmostComplex (c : ℝ) (w : ℂ) :
    σ.Tames (h₀.exchangeAlmostComplex J hJ c w) := by
  unfold exchangeAlmostComplex
  split_ifs
  exacts [tames_endWeightedAlmostComplex h₀ _ _ _ _ _ w,
    tames_negativePlaneAlmostComplex h₀ _ _ _]

/-- Every member of the family is `σ`-compatible when the end structures are. -/
theorem compatible_exchangeAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (c : ℝ) (w : ℂ) :
    σ.Compatible (h₀.exchangeAlmostComplex J hJ c w) := by
  unfold exchangeAlmostComplex
  split_ifs
  · refine compatible_endWeightedAlmostComplex h₀ _ _ _ _ _ (fun q t => ?_) w
    rcases eq_or_ne q inf with rfl | hq
    · simpa using h₀
    · simpa [update_of_ne hq] using hJc q t
  · exact compatible_negativePlaneAlmostComplex h₀ _ _ (hJc inf) _

/-- **The Cayley coordinate of the family.** For `-1 ≤ c ≤ 2`, on every tangent fiber, the Cayley
coordinate relative to `J₀` of the member `c` at `w` is the sum of the cutoff-weighted Cayley
coordinates of the input structures, in the end coordinates of `w`, and of the output structure,
in the end coordinates of `w - c`. This characterizes the structure, since the Cayley transform is
injective on tame structures. -/
theorem cayley_exchangeAlmostComplex (hc : c ∈ Icc (-1) 2) (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.exchangeAlmostComplex J hJ c w).almostComplexStructureAt x) =
      smoothTransition ((zero.endCoord w).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((J zero (zero.endCoord w).im).almostComplexStructureAt x) +
        smoothTransition ((one.endCoord w).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((J one (one.endCoord w).im).almostComplexStructureAt x) +
        smoothTransition (-(inf.endCoord (w - c)).re - 1) •
          (J₀.almostComplexStructureAt x).cayley
            ((J inf (inf.endCoord (w - c)).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_exchangeAlmostComplex, Floer.cayley_exchangeAlmostComplex _ hc,
    Floer.cayley_pairOfPantsAlmostComplex, Floer.cayley_negativePlaneAlmostComplex,
    Puncture.sum_univ]
  simp [AlmostComplexStructure.cayley_self]

/-- **The start of the family is the pair-of-pants structure.** -/
@[simp]
theorem exchangeAlmostComplex_zero (w : ThricePuncturedSphere) :
    h₀.exchangeAlmostComplex J hJ 0 w = h₀.pairOfPantsAlmostComplex J hJ w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_exchangeAlmostComplex, Floer.exchangeAlmostComplex_zero,
      almostComplexStructureAt_pairOfPantsAlmostComplex]

/-- **The end of the family is the exchanged pair-of-pants structure.** If the output structures
`J ∞` have period one in `t`, the member `c = 1` of the family at `1 - w` is the pair-of-pants
structure with exchanged end structures (`TauCeti.Floer.exchangeEndData`: `J 1` at `0`, `J 0` at
`1` and `t ↦ J ∞ (t + 1/2)` at `∞`) at `w`. -/
theorem exchangeAlmostComplex_one (hJp : Periodic (J inf) 1)
    (hJ' : ∀ q t, σ.Tames (Floer.exchangeEndData J q t)) (w : ThricePuncturedSphere) :
    h₀.exchangeAlmostComplex J hJ 1 (1 - w) =
      h₀.pairOfPantsAlmostComplex (Floer.exchangeEndData J) hJ' w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    have hJx : ∀ q t (y : Unit), (h₀.isNondegenerate.symplecticFormAt x).Tames
        (Floer.exchangeEndData (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x) q t
          y) := by
      intro q t _
      cases q
      · simpa using h₀.isNondegenerate.tames_iff.mp (hJ' zero t) x
      · simpa using h₀.isNondegenerate.tames_iff.mp (hJ' one t) x
      · simpa using h₀.isNondegenerate.tames_iff.mp (hJ' inf t) x
    rw [almostComplexStructureAt_exchangeAlmostComplex,
      Floer.exchangeAlmostComplex_one (h₀.compatibleAt x) (fun t => by simp only [hJp t]) hJx,
      sub_sub_cancel, almostComplexStructureAt_pairOfPantsAlmostComplex]
    -- Both sides are the linear pair-of-pants structure of the same exchanged end structures.
    refine (h₀.compatibleAt x).eq_of_cayley_eq
      (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) _ ())
      (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) _ ()) ?_
    rw [Floer.cayley_pairOfPantsAlmostComplex, Floer.cayley_pairOfPantsAlmostComplex]
    refine Finset.sum_congr rfl fun q _ => ?_
    cases q <;> simp

/-- **The family is `J q t` far out on an input end.** For `0 ≤ c ≤ 1`, if `J q` has period one
in `t`, then on the part `s ≥ 2` of the input end `q` the member `c` of the family at the point
with end coordinates `z = s + i t` is `J q t`. -/
theorem exchangeAlmostComplex_cylindricalEndLift {q : Puncture} (hq : q ≠ inf)
    (hJp : Periodic (J q) 1) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) :
    h₀.exchangeAlmostComplex J hJ c (q.cylindricalEndLift z) = J q z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_exchangeAlmostComplex]
    exact Floer.exchangeAlmostComplex_cylindricalEndLift (h₀.compatibleAt x) hq
      (fun t => by simp only [hJp t]) hc₀ hc₁ hz ()

/-- **The family is `J ∞ t` far out on the output end.** If `J ∞` has period one in `t`, then on
the part `s ≤ -2` of the output end recentred at `c`, the member `c` of the family at the point
`c + φ_∞(z)` with end coordinates `z = s + i t` is `J ∞ t`. -/
theorem exchangeAlmostComplex_add_cylindricalEndLift_inf (hJp : Periodic (J inf) 1) (c : ℝ)
    {z : ℂ} (hz : z.re ≤ -2) :
    h₀.exchangeAlmostComplex J hJ c (c + inf.cylindricalEndLift z) = J inf z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_exchangeAlmostComplex]
    exact Floer.exchangeAlmostComplex_add_cylindricalEndLift_inf (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) c hz ()

/-! ### Smoothness -/

/-- **The family is smooth.** For end structures which have period one in `t` and are `C^n` on
`ℝ × M`, the input-exchange family is `C^n` at `y₀` as a section of the tangent endomorphism
bundle along `b`, read along families of parameters `c`, domain points `f` and target points `b`
that are `C^n` at `y₀`, provided `-1 < c y₀ < 2` and `f y₀` is a point of `S = ℂ ∖ {0, 1}`.
Near the disc `‖w - c‖ < 2 exp (2π)` it is the pair-of-pants structure of the input structures,
and near the complement of the disc `‖w - c‖ ≤ 3` it is the translated negative plane
structure. -/
theorem contMDiffAt_exchangeAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    {c : N → ℝ} {f : N → ℂ} {b : N → M} {y₀ : N} (hc : ContMDiffAt I' 𝓘(ℝ) n c y₀)
    (hf : ContMDiffAt I' 𝓘(ℝ, ℂ) n f y₀) (hb : ContMDiffAt I' I n b y₀)
    (hcy : c y₀ ∈ Ioo (-1) 2) (hS : f y₀ ≠ 0 ∧ f y₀ ≠ 1) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.exchangeAlmostComplex J hJ (c y) (f y)).toEndomorphism (b y))) y₀ := by
  have hfc : ContMDiffAt I' 𝓘(ℝ, ℂ) n (fun y => f y - (c y : ℂ)) y₀ :=
    hf.sub (Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y₀ hc)
  have hdist : ContinuousAt (fun y => ‖f y - (c y : ℂ)‖) y₀ := hfc.continuousAt.norm
  rcases lt_or_ge ‖f y₀ - c y₀‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- Near the disc the family is the pair-of-pants structure of the input structures.
    have hin := contMDiffAt_inputAlmostComplex h₀ J hJ hJp hJs hf hb hS
    refine hin.congr_of_eventuallyEq ?_
    filter_upwards [hdist.eventually (gt_mem_nhds hlt)] with y hy
    simp only [exchangeAlmostComplex, hy.le, ↓reduceIte]
  · -- Away from the disc `‖w - c‖ ≤ 3` the family is the translated plane structure.
    have hpl : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
        (fun y => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          (b y) ((h₀.negativePlaneAlmostComplex (J inf) (hJ inf) (f y - c y)).toEndomorphism
            (b y))) y₀ :=
      (contMDiff_negativePlaneAlmostComplex h₀ (J inf) (hJ inf) (hJp inf) (hJs inf)
        contMDiff_fst contMDiff_snd ((f y₀ - c y₀ : ℂ), b y₀)).comp
          (f := fun y => ((f y - c y : ℂ), b y)) y₀ (hfc.prodMk hb)
    refine hpl.congr_of_eventuallyEq ?_
    have h3 : 3 < ‖f y₀ - c y₀‖ :=
      lt_of_lt_of_le (by nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]) hge
    filter_upwards [hdist.eventually (lt_mem_nhds h3),
      hc.continuousAt.eventually (isOpen_Ioo.mem_nhds hcy)] with y hy hcy'
    rcases le_or_gt ‖f y - c y‖ (2 * Real.exp (2 * π)) with hle | hgt
    · -- In the annulus `3 < ‖w - c‖ ≤ 2 exp (2π)` both parts are the base structure.
      obtain ⟨hw₀, hw₁⟩ := half_le_norm_of_le_norm_sub (r := 2) (w := f y)
        (abs_le.2 ⟨by linarith [hcy'.1], hcy'.2.le⟩)
        (abs_le.2 ⟨by linarith [hcy'.1], by linarith [hcy'.2]⟩) (by linarith)
      simp only [exchangeAlmostComplex, hle, ↓reduceIte, inputAlmostComplex_eq_base h₀ J hJ hw₀ hw₁,
        negativePlaneAlmostComplex_eq_of_norm_le h₀ (J inf) (hJ inf) hle]
    · simp only [exchangeAlmostComplex_of_lt_norm h₀ J hJ hgt]

/-! ### Solutions at the end of the family -/

/-- **Solutions at the end of the family.** Let `σ'(z) = (1, 0) - z` be the exchange `w ↦ 1 - w`
in the real coordinates `ℝ × ℝ ≃ ℂ`, let the Hamiltonians `H_q` on `M` have period one and be
`C¹`, and let the output structures `J ∞` have period one. If `u` is differentiable at the point
`σ'(z)` of `S` and solves the Floer equation there for the pair-of-pants data with exchanged
inputs, then `u ∘ σ'` solves the Floer equation at `z` for the member `c = 1` of the
input-exchange family: the perturbation `TauCeti.Floer.exchangePerturbation H 1` with the almost
complex structure `exchangeAlmostComplex h₀ J hJ 1`. -/
theorem isComplexLinearMap_perturbedMFDeriv_exchange_one {H : Puncture → ℝ → M → ℝ}
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hJp : Periodic (J inf) 1) (hJ' : ∀ q t, σ.Tames (Floer.exchangeEndData J q t))
    {u : ℝ × ℝ → M} {z : ℝ × ℝ} (hz : Complex.equivRealProdCLM.symm ((1, 0) - z) ≠ 0 ∧
      Complex.equivRealProdCLM.symm ((1, 0) - z) ≠ 1)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u ((1, 0) - z))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.pairOfPantsAlmostComplex (Floer.exchangeEndData J) hJ' ⟨_, hz⟩).almostComplexStructureAt
        (u ((1, 0) - z)))
      (σ.perturbedMFDeriv
        (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H)
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ((1, 0) - z)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.exchangeAlmostComplex J hJ 1 (Complex.equivRealProdCLM.symm z)).almostComplexStructureAt
        (u ((1, 0) - z)))
      (σ.perturbedMFDeriv
        (fun z x ↦ Floer.exchangePerturbation H 1 (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ Floer.exchangePerturbation H 1 (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ fun z ↦ (1, 0) - z) z).toLinearMap := by
  set e := Complex.equivRealProdCLM.symm
  have hσ : 1 - e ((1, 0) - z) = e z := by
    apply Complex.ext <;> simp [e]
  -- The structure at `z` is the exchanged pair-of-pants structure at `σ'(z)`.
  have hJz := exchangeAlmostComplex_one h₀ J hJ hJp hJ' ⟨_, hz⟩
  simp only [hσ] at hJz
  rw [hJz]
  -- The perturbation is the pullback along `σ'` of the exchanged pair-of-pants perturbation.
  have hpull (v : ℝ × ℝ) : (fun z x ↦ Floer.exchangePerturbation H 1 (e z) x (e v)) =
      Floer.perturbationPullback (fun z ↦ (1, 0) - z)
        (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x 1)
        (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x Complex.I)
        v := by
    funext z' x
    rw [Floer.perturbationPullback_pairOfPantsPerturbation_exchangeEndData (hH inf)]
  have hD : σ.perturbedMFDeriv (fun z x ↦ Floer.exchangePerturbation H 1 (e z) x 1)
      (fun z x ↦ Floer.exchangePerturbation H 1 (e z) x Complex.I) (u ∘ fun z ↦ (1, 0) - z) z =
      σ.perturbedMFDeriv
        (Floer.perturbationPullback (fun z ↦ (1, 0) - z)
          (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x 1)
          (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x Complex.I)
          stdComplexLineReal)
        (Floer.perturbationPullback (fun z ↦ (1, 0) - z)
          (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x 1)
          (fun z x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e z) x Complex.I)
          stdComplexLineImag)
        (u ∘ fun z ↦ (1, 0) - z) z := by
    conv_lhs => rw [← equivRealProdCLM_symm_stdComplexLineReal,
      ← equivRealProdCLM_symm_stdComplexLineImag, hpull, hpull]
  rw [hD]
  -- The exchanged pair-of-pants perturbation is differentiable in the target point at `σ'(z)`.
  have hK (v : ℂ) : MDifferentiableAt I 𝓘(ℝ)
      (fun x ↦ Floer.pairOfPantsPerturbation (Floer.exchangeEndData H) (e ((1, 0) - z)) x v)
      (u ((1, 0) - z)) := by
    have hd := Floer.contMDiffAt_pairOfPantsPerturbation (Floer.periodic_exchangeEndData hH)
      (Floer.contMDiff_uncurry_exchangeEndData hHs) ⟨_, hz⟩ (u ((1, 0) - z))
    exact ((hd.comp _ (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
      contMDiffAt_const).mdifferentiableAt one_ne_zero
  -- The exchange is holomorphic: its derivative is `-1`.
  have hφ : DifferentiableAt ℝ (fun z : ℝ × ℝ ↦ (1, 0) - z) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (fun z : ℝ × ℝ ↦ (1, 0) - z) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [fderiv_const_sub, fderiv_fun_id]
    simp
  exact σ.isComplexLinearMap_perturbedMFDeriv_perturbationPullback hφ hu (hK 1) (hK Complex.I)
    hφJ h

end TauCeti.SmoothTwoForm.Compatible
