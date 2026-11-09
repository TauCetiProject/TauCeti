/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath

/-!
# Pair-of-pants almost complex data on a manifold

Given a compatible base structure and three smooth period-one families of tame structures on
an actual tangent bundle, construct a smooth domain-dependent tame structure on the
thrice-punctured sphere. Compatible end data give compatible structures. On each sufficiently
far cylindrical tail the structure is exactly the prescribed end structure; off the cutoff
regions it is the base structure.

More generally, `TauCeti.SmoothTwoForm.Compatible.endWeightedAlmostComplex` applies the linear
end-weighted construction `TauCeti.Floer.endWeightedAlmostComplex` in each tangent fiber, for any
weights in `[0, 1]` that vanish off the parts `±s > 0` of their ends; the pair-of-pants structure
is the case of the cutoffs `β(±s_q - 1)`. The Cayley coordinate is a weighted sum of the Cayley
coordinates of the end structures, so smoothness follows from
`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_of_cayley_eq_sum`, which works in tangent
trivializations. Thus no global trivialization or constant target two-form is assumed.
Neither closedness of the two-form nor compactness of the target is needed. The resulting
family is jointly smooth in the domain and target variables as a section of the tangent
endomorphism bundle along the target projection. This is extension of coefficient data, not
regularity of a curve operator.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1.
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart).
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9.
-/

public noncomputable section

open Bundle Set Real Manifold Topology
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.ThricePuncturedSphere.Puncture

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

/-- A period-one family `J t` of smooth almost complex structures which is jointly `C^n` on
`ℝ × M`, read at the angular coordinate of the end `q` along a `C^n` family of domain points
avoiding the center of the end, is `C^n` along every `C^n` family of target points. -/
theorem contMDiffAt_toEndomorphism_comp_im_endCoord (q : Puncture) {n : ℕ∞ω}
    {J : ℝ → SmoothAlmostComplexStructure I M} (hJp : Function.Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J p.1).toEndomorphism p.2)))
    {f : N → ℂ} {b : N → M} {y₀ : N} (hf : ContMDiffAt I' 𝓘(ℝ, ℂ) n f y₀)
    (hb : ContMDiffAt I' I n b y₀) (hq : f y₀ ≠ q.endCenter) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((J (q.endCoord (f y)).im).toEndomorphism (b y))) y₀ := by
  have hp : Function.Periodic (fun t (x : M) => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      x ((J t).toEndomorphism x)) 1 := fun t => by simp only [hJp t]
  exact (q.contMDiffAt_comp_im_endCoord hp hJs hq (b y₀)).comp y₀ (hf.prodMk hb)

end TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJ : ∀ q t, σ.Tames (J q t))

/-! ### End-weighted structures -/

section EndWeighted

variable (c : Puncture → ℂ → ℝ) (hc : ∀ q w, c q w ∈ Icc 0 1)
  (hc₀ : ∀ q w, c q w ≠ 0 → 0 < q.endSign * (q.endCoord w).re)

/-- The linear end-weighted structure on the tangent space at `x`. -/
private def endWeightedAt (w : ℂ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  Floer.endWeightedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
    (fun q t _ => (J q t).almostComplexStructureAt x)
    (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) c hc hc₀ w ()

private theorem cayley_endWeightedAt (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (endWeightedAt h₀ J hJ c hc hc₀ w x) =
      ∑ q, c q w • (J₀.almostComplexStructureAt x).cayley
        ((J q (q.endCoord w).im).almostComplexStructureAt x) :=
  Floer.cayley_endWeightedAlmostComplex _ w ()

/-- The end-weighted structure is smooth on `M` for a fixed domain point. -/
private theorem contMDiffAt_endWeightedAt (w : ℂ) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y (LinearMap.toContinuousLinearMap (endWeightedAt h₀ J hJ c hc hc₀ w y).toLinearMap)) x :=
  h₀.contMDiffAt_of_cayley_eq_sum (b := id) (L := fun q _ => J q (q.endCoord w).im)
    (a := fun q _ => c q w)
    (fun y => Floer.tames_endWeightedAlmostComplex (h₀.compatibleAt y) w ())
    (fun q _ => hJ q _) (cayley_endWeightedAt h₀ J hJ c hc hc₀ w) contMDiffAt_id
    (fun _ => contMDiffAt_const) (fun q => (J q _).toEndomorphism.contMDiff x)

/-- The domain-dependent almost complex structure on the tangent bundle over the pair of pants
given by smooth tame structures `J q t` on its three ends, relative to a compatible base structure
`J₀`, and by weights `c q w ∈ [0, 1]` that vanish off the parts `±s > 0` of their ends. On each
tangent space it is the linear end-weighted structure `TauCeti.Floer.endWeightedAlmostComplex`. -/
def endWeightedAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x => LinearMap.toContinuousLinearMap (endWeightedAt h₀ J hJ c hc hc₀ w x).toLinearMap,
      contMDiffAt_endWeightedAt h₀ J hJ c hc hc₀ w⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the linear fiberwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of the end-weighted structure at `x` is the linear end-weighted structure
there, read as a continuous endomorphism. -/
private theorem endWeightedAlmostComplex_toEndomorphism (w : ℂ) (x : M) :
    (h₀.endWeightedAlmostComplex J hJ c hc hc₀ w).toEndomorphism x =
      LinearMap.toContinuousLinearMap (endWeightedAt h₀ J hJ c hc hc₀ w x).toLinearMap :=
  (rfl)

/-- The value on a tangent fiber is precisely the linear end-weighted structure there. -/
theorem almostComplexStructureAt_endWeightedAlmostComplex (w : ℂ) (x : M) :
    (h₀.endWeightedAlmostComplex J hJ c hc hc₀ w).almostComplexStructureAt x =
      Floer.endWeightedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun q t _ => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) c hc hc₀ w () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    endWeightedAlmostComplex_toEndomorphism, LinearMap.coe_toContinuousLinearMap, endWeightedAt]

/-- The end-weighted structure is tamed by `σ`. -/
theorem tames_endWeightedAlmostComplex (w : ℂ) :
    σ.Tames (h₀.endWeightedAlmostComplex J hJ c hc hc₀ w) := by
  refine h₀.isNondegenerate.tames_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_endWeightedAlmostComplex]
  exact Floer.tames_endWeightedAlmostComplex (h₀.compatibleAt x) w ()

/-- The end-weighted structure is `σ`-compatible when the end structures are. -/
theorem compatible_endWeightedAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t)) (w : ℂ) :
    σ.Compatible (h₀.endWeightedAlmostComplex J hJ c hc hc₀ w) := by
  refine h₀.isNondegenerate.compatible_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_endWeightedAlmostComplex]
  exact Floer.compatible_endWeightedAlmostComplex (h₀.compatibleAt x)
    (fun q t _ => h₀.isNondegenerate.compatible_iff.mp (hJc q t) x) w ()

/-- On every tangent fiber, the Cayley coordinate of the end-weighted structure relative to `J₀`
is the weighted sum `∑ q, c q w • cayley (J q (t_q(w)))`. This characterizes the structure, since
the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_endWeightedAlmostComplex (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.endWeightedAlmostComplex J hJ c hc hc₀ w).almostComplexStructureAt x) =
      ∑ q, c q w • (J₀.almostComplexStructureAt x).cayley
        ((J q (q.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_endWeightedAlmostComplex, Floer.cayley_endWeightedAlmostComplex]

end EndWeighted

/-- **The end-weighted structures are jointly smooth.** Along families of weights, domain points
`f` and target points `b`, the end-weighted structures are `C^n` at `y₀` as sections of the
tangent endomorphism bundle along `b`, provided `b` and the weights read at `f` are `C^n` at `y₀`
and so are the end structures read at the angular coordinates of `f` along `b`. -/
theorem contMDiffAt_endWeightedAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] {c : N → Puncture → ℂ → ℝ} {hc : ∀ y q w, c y q w ∈ Icc 0 1}
    {hc₀ : ∀ y q w, c y q w ≠ 0 → 0 < q.endSign * (q.endCoord w).re}
    {f : N → ℂ} {b : N → M} {y₀ : N} (hb : ContMDiffAt I' I n b y₀)
    (hcs : ∀ q, ContMDiffAt I' 𝓘(ℝ) n (fun y => c y q (f y)) y₀)
    (hJs : ∀ q, ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((J q (q.endCoord (f y)).im).toEndomorphism (b y))) y₀) :
    ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.endWeightedAlmostComplex J hJ (c y) (hc y) (hc₀ y) (f y)).toEndomorphism
          (b y))) y₀ := by
  simp only [endWeightedAlmostComplex_toEndomorphism]
  exact h₀.contMDiffAt_of_cayley_eq_sum
    (K := fun y => endWeightedAt h₀ J hJ (c y) (hc y) (hc₀ y) (f y) (b y))
    (L := fun q y => J q (q.endCoord (f y)).im) (a := fun q y => c y q (f y))
    (fun y => Floer.tames_endWeightedAlmostComplex (h₀.compatibleAt (b y)) _ ())
    (fun q _ => hJ q _) (fun y => cayley_endWeightedAt h₀ J hJ _ _ _ _ _) hb hcs hJs

/-! ### The pair-of-pants structure -/

/-- Extend three smooth tame end families to the tangent bundle over the pair of pants, relative
to a compatible base structure: the end-weighted structure with the cutoffs `β(±s_q - 1)`. -/
def pairOfPantsAlmostComplex (w : ThricePuncturedSphere) : SmoothAlmostComplexStructure I M :=
  h₀.endWeightedAlmostComplex J hJ
    (fun q w => smoothTransition (q.endSign * (q.endCoord w).re - 1))
    (fun _ _ => mem_Icc.2 ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩)
    (fun _ _ hq => zero_lt_one.trans (Floer.one_lt_endSign_mul_re_endCoord hq).1) w

/-- The value on a tangent fiber is precisely the linear pair-of-pants construction there. -/
theorem almostComplexStructureAt_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) (x : M) :
    (h₀.pairOfPantsAlmostComplex J hJ w).almostComplexStructureAt x =
      Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (h₀.compatibleAt x)
        (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w () := by
  rw [pairOfPantsAlmostComplex, almostComplexStructureAt_endWeightedAlmostComplex]
  -- Both linear structures have the same Cayley coordinate relative to `J₀`.
  refine (h₀.compatibleAt x).eq_of_cayley_eq
    (Floer.tames_endWeightedAlmostComplex (h₀.compatibleAt x) _ ())
    (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) _ ()) ?_
  rw [Floer.cayley_endWeightedAlmostComplex, Floer.cayley_pairOfPantsAlmostComplex]

/-- The extension is tamed by the given two-form. -/
theorem tames_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) :
    σ.Tames (h₀.pairOfPantsAlmostComplex J hJ w) :=
  tames_endWeightedAlmostComplex h₀ J hJ _ _ _ w

/-- Compatible end families extend through compatible structures. -/
theorem compatible_pairOfPantsAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t))
    (w : ThricePuncturedSphere) :
    σ.Compatible (h₀.pairOfPantsAlmostComplex J hJ w) :=
  compatible_endWeightedAlmostComplex h₀ J hJ _ _ _ hJc w

/-- The Cayley coordinate characterizes the extension on every tangent fiber. -/
@[simp]
theorem cayley_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.pairOfPantsAlmostComplex J hJ w).almostComplexStructureAt x) =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((J q (q.endCoord w).im).almostComplexStructureAt x) :=
  cayley_endWeightedAlmostComplex h₀ J hJ _ _ _ w x

/-- Far out on a cylindrical end, the extension is the prescribed end structure. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift (w : ThricePuncturedSphere)
    {q : Puncture} (hJp : Function.Periodic (J q) 1) {z : ℂ}
    (hw : (w : ℂ) = q.cylindricalEndLift z) (hz : 2 ≤ q.endSign * z.re) :
    h₀.pairOfPantsAlmostComplex J hJ w = J q z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsAlmostComplex, hw]
    exact Floer.pairOfPantsAlmostComplex_cylindricalEndLift (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) hz ()

/-- Where all the end cutoffs vanish, the extension is the base structure. -/
theorem pairOfPantsAlmostComplex_eq_base_of_forall_le_one (w : ThricePuncturedSphere)
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) :
    h₀.pairOfPantsAlmostComplex J hJ w = J₀ := by
  have hc (q : Puncture) : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (sub_nonpos.mpr (hw q))
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  apply (h₀.compatibleAt x).eq_of_cayley_eq
    (h₀.isNondegenerate.tames_iff.mp (tames_pairOfPantsAlmostComplex h₀ J hJ w) x)
    (h₀.compatibleAt x).tames
  rw [cayley_pairOfPantsAlmostComplex, AlmostComplexStructure.cayley_self]
  simp only [hc, zero_smul, Finset.sum_const_zero]

/-- The domain-dependent structures are jointly `C^n` along any `C^n` family of domain and
target points, for period-one end families which are jointly `C^n` on `ℝ × M`. The domain family
must avoid the two deleted points. This formulation also allows independent external manifold
parameters. -/
theorem contMDiff_pairOfPantsAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hJp : ∀ q, Function.Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    {f : N → ℂ} {b : N → M} (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f)
    (hb : ContMDiff I' I n b) (hS : ∀ p, f p ≠ 0 ∧ f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.pairOfPantsAlmostComplex J hJ ⟨f p, hS p⟩).toEndomorphism (b p))) := by
  intro y₀
  have hq (q : Puncture) : f y₀ ≠ q.endCenter := ne_endCenter (hS y₀) q
  have hβ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n smoothTransition :=
    ((smoothTransition.contDiff (n := ⊤)).of_le ENat.LEInfty.out).contMDiff
  simp only [pairOfPantsAlmostComplex]
  exact contMDiffAt_endWeightedAlmostComplex h₀ J hJ (hb y₀)
    (fun q => hβ.contMDiffAt.comp y₀ (((contDiffAt_const.mul
      (q.contDiffAt_re_endCoord (hq q))).sub contDiffAt_const).contMDiffAt.comp y₀ (hf y₀)))
    fun q => q.contMDiffAt_toEndomorphism_comp_im_endCoord (hJp q) (hJs q) (hf y₀) (hb y₀) (hq q)

end TauCeti.SmoothTwoForm.Compatible
