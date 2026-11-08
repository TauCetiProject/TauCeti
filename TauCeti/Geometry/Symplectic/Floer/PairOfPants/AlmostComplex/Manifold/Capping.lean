/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleyPath

/-!
# Almost complex structures on the negative PSS plane in a manifold

The unit of the pair-of-pants product is the count of negative planes: maps from `ℂ` with a
Morse incidence at the pole `0` and a negative cylindrical end at `∞`.
`TauCeti.Floer.negativePlaneAlmostComplex` constructs their domain-dependent almost complex
structures on a fixed symplectic vector space. This file constructs them on the tangent bundle of a
manifold `M` with a nondegenerate two-form `σ`, such as a closed symplectic manifold.

Fix a `σ`-compatible smooth almost complex structure `J₀` and smooth `σ`-tame structures `J t`.
For `w ∈ ℂ`, the smooth almost complex structure
`TauCeti.SmoothTwoForm.Compatible.negativePlaneAlmostComplex h₀ J hJ w` is, on the tangent space at
every point `x`, the linear negative plane structure of `J₀ x` and the end structures `J t x`
(`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_negativePlaneAlmostComplex`). Its Cayley
coordinate relative to `J₀` is `β(-s - 1) • cayley (J t)`, where `(s, t)` are the coordinates of
the end at `∞` and `β` is the smooth transition function.

* It is tame, and compatible when the end structures are.
* It is `J₀` on the pole disc `‖w‖ ≤ 2 exp (2π)`.
* For period-one end structures, it is `J t` on the part `s ≤ -2` of the end.
* For smooth period-one end structures, it is jointly `C^n` along `C^n` families of points of
  `ℂ`, including the pole, and points of `M`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_negativePlaneAlmostComplex`).

Smoothness off the pole disc follows from
`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_of_cayley_eq_sum`.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps and the unit of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  domain-dependent almost complex structures agreeing with given ones on the cylindrical ends.
-/

public noncomputable section

open Bundle Set Real Manifold Topology
open scoped ContDiff
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : ℝ → SmoothAlmostComplexStructure I M) (hJ : ∀ t, σ.Tames (J t))

/-- The linear negative plane structure on the tangent space at `x`. -/
private def negativePlaneAt (w : ℂ) (x : M) : AlmostComplexStructure (TangentSpace I x) :=
  Floer.negativePlaneAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
    (fun t _ => (J t).almostComplexStructureAt x)
    (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x) w ()

/-- The Cayley coordinate of the negative plane structure, as a sum over the single end. -/
private theorem cayley_negativePlaneAt (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley (negativePlaneAt h₀ J hJ w x) =
      ∑ _ : Unit, smoothTransition (-(inf.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((J (inf.endCoord w).im).almostComplexStructureAt x) := by
  rw [Fintype.sum_unique, negativePlaneAt, Floer.cayley_negativePlaneAlmostComplex]

/-- The negative plane structure is smooth on `M` for a fixed domain point. -/
private theorem contMDiffAt_negativePlaneAt (w : ℂ) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y (LinearMap.toContinuousLinearMap (negativePlaneAt h₀ J hJ w y).toLinearMap)) x :=
  h₀.contMDiffAt_of_cayley_eq_sum (b := id) (L := fun _ _ => J (inf.endCoord w).im)
    (a := fun _ _ => smoothTransition (-(inf.endCoord w).re - 1))
    (fun y => Floer.tames_negativePlaneAlmostComplex (h₀.compatibleAt y) w ())
    (fun _ _ => hJ _) (cayley_negativePlaneAt h₀ J hJ w) contMDiffAt_id
    (fun _ => contMDiffAt_const) (fun _ => (J _).toEndomorphism.contMDiff x)

/-- The almost complex structure on `M` of the negative PSS plane with end structures `J t`, at
the point `w ∈ ℂ`. On each tangent space it is the linear negative plane structure
`TauCeti.Floer.negativePlaneAlmostComplex` of `J₀` and the end structures. -/
def negativePlaneAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M where
  toEndomorphism :=
    ⟨fun x => LinearMap.toContinuousLinearMap (negativePlaneAt h₀ J hJ w x).toLinearMap,
      contMDiffAt_negativePlaneAt h₀ J hJ w⟩
  square_neg x := by
    ext v
    exact AlmostComplexStructure.apply_apply _ v

/-- The endomorphism of the negative plane structure at `x` is the linear negative plane structure
there, read as a continuous endomorphism. -/
private theorem negativePlaneAlmostComplex_toEndomorphism (w : ℂ) (x : M) :
    (h₀.negativePlaneAlmostComplex J hJ w).toEndomorphism x =
      LinearMap.toContinuousLinearMap (negativePlaneAt h₀ J hJ w x).toLinearMap :=
  (rfl)

/-- The value on a tangent fiber is precisely the linear negative plane structure there. -/
theorem almostComplexStructureAt_negativePlaneAlmostComplex (w : ℂ) (x : M) :
    (h₀.negativePlaneAlmostComplex J hJ w).almostComplexStructureAt x =
      Floer.negativePlaneAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun t _ => (J t).almostComplexStructureAt x)
        (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x) w () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap,
    negativePlaneAlmostComplex_toEndomorphism, LinearMap.coe_toContinuousLinearMap,
    negativePlaneAt]

/-- The negative plane structure is tamed by `σ`. -/
theorem tames_negativePlaneAlmostComplex (w : ℂ) :
    σ.Tames (h₀.negativePlaneAlmostComplex J hJ w) := by
  refine h₀.isNondegenerate.tames_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_negativePlaneAlmostComplex]
  exact Floer.tames_negativePlaneAlmostComplex (h₀.compatibleAt x) w ()

/-- The negative plane structure is `σ`-compatible when the end structures are. -/
theorem compatible_negativePlaneAlmostComplex (hJc : ∀ t, σ.Compatible (J t)) (w : ℂ) :
    σ.Compatible (h₀.negativePlaneAlmostComplex J hJ w) := by
  refine h₀.isNondegenerate.compatible_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_negativePlaneAlmostComplex]
  exact Floer.compatible_negativePlaneAlmostComplex (h₀.compatibleAt x)
    (fun t _ => h₀.isNondegenerate.compatible_iff.mp (hJc t) x) w ()

/-- On every tangent fiber, the Cayley coordinate of the negative plane structure relative to `J₀`
is `β(-s(w) - 1) • cayley (J (t(w)))`, where `(s, t)` are the coordinates of the end at `∞`. This
characterizes the structure, since the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_negativePlaneAlmostComplex (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.negativePlaneAlmostComplex J hJ w).almostComplexStructureAt x) =
      smoothTransition (-(inf.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((J (inf.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.cayley_negativePlaneAlmostComplex]

/-- **The pole disc.** The negative plane structure is the base structure `J₀` on the disc
`‖w‖ ≤ 2 exp (2π)` about the pole. -/
theorem negativePlaneAlmostComplex_eq_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) :
    h₀.negativePlaneAlmostComplex J hJ w = J₀ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.negativePlaneAlmostComplex_eq_of_norm_le (h₀.compatibleAt x) hw,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- **The structure is `J t` far out on the end.** If `J` has period one in `t`, then on the part
`s ≤ -2` of the end, the negative plane structure at the point with end coordinates `z = s + i t`
is `J t`. -/
theorem negativePlaneAlmostComplex_cylindricalEndLift (hJp : Function.Periodic J 1) {z : ℂ}
    (hz : z.re ≤ -2) : h₀.negativePlaneAlmostComplex J hJ (inf.cylindricalEndLift z) = J z.im := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.negativePlaneAlmostComplex_cylindricalEndLift (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) hz,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- **The plane structure is smooth.** For end structures which have period one in `t` and are
smooth on `ℝ × M`, the negative plane structures are `C^n` along every `C^n` family of points `f`
of `ℂ`, including the pole, and points `b` of `M`. -/
theorem contMDiff_negativePlaneAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : Function.Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J p.1).toEndomorphism p.2)))
    {f : N → ℂ} {b : N → M} (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b y) ((h₀.negativePlaneAlmostComplex J hJ (f y)).toEndomorphism (b y))) := by
  intro y₀
  rcases lt_or_ge ‖f y₀‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- On the open pole disc, the structure is `J₀`.
    have hJ₀ : ContMDiffAt I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
        (fun y => TotalSpace.mk' (E →L[ℝ] E)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
          (b y) (J₀.toEndomorphism (b y))) y₀ :=
      ((J₀.toEndomorphism.contMDiff (b y₀)).of_le ENat.LEInfty.out).comp y₀ (hb y₀)
    refine hJ₀.congr_of_eventuallyEq ?_
    filter_upwards [hf.continuous.norm.continuousAt.eventually (gt_mem_nhds hlt)] with y hy
    rw [negativePlaneAlmostComplex_eq_of_norm_le h₀ J hJ hy.le]
  -- Off it, the point is not the center `0` of the end, where the end coordinates are smooth.
  have hw : f y₀ ≠ inf.endCenter := by
    rintro h
    rw [h, endCenter_inf, norm_zero] at hge
    linarith [Real.exp_pos (2 * π)]
  have hβ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n smoothTransition :=
    ((smoothTransition.contDiff (n := ⊤)).of_le ENat.LEInfty.out).contMDiff
  have hp : Function.Periodic (fun t (x : M) => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      x ((J t).toEndomorphism x)) 1 := fun t => by simp only [hJp t]
  exact h₀.contMDiffAt_of_cayley_eq_sum
    (K := fun y => negativePlaneAt h₀ J hJ (f y) (b y))
    (L := fun _ y => J (inf.endCoord (f y)).im)
    (a := fun _ y => smoothTransition (-(inf.endCoord (f y)).re - 1))
    (fun y => Floer.tames_negativePlaneAlmostComplex (h₀.compatibleAt (b y)) _ ())
    (fun _ _ => hJ _) (fun y => cayley_negativePlaneAt h₀ J hJ _ _) (hb y₀)
    (fun _ => hβ.contMDiffAt.comp y₀
      (((inf.contDiffAt_re_endCoord hw).neg.sub contDiffAt_const).contMDiffAt.comp y₀ (hf y₀)))
    fun _ => ((inf.contMDiffAt_comp_im_endCoord hp hJs hw (b y₀)).of_le
      ENat.LEInfty.out).comp y₀ ((hf y₀).prodMk (hb y₀))

end TauCeti.SmoothTwoForm.Compatible
