/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Basic

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
* For period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly `C^n` along
  `C^n` families of points of `ℂ`, including the pole, and points of `M`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_negativePlaneAlmostComplex`).

The structure is the end-weighted structure
`TauCeti.SmoothTwoForm.Compatible.endWeightedAlmostComplex` whose only nonzero weight is that of
the end `∞`, so tameness and compatibility come from it, and smoothness off the pole disc follows
from `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_endWeightedAlmostComplex`.

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

/-- The weights of the negative plane: the cutoff `β(-s - 1)` on the end `∞` and `0` on the
inputs. -/
private def negativePlaneWeight (q : Puncture) (w : ℂ) : ℝ :=
  if q = inf then smoothTransition (-(inf.endCoord w).re - 1) else 0

/-- The weights lie in `[0, 1]`. -/
private theorem negativePlaneWeight_mem_Icc (q : Puncture) (w : ℂ) :
    negativePlaneWeight q w ∈ Icc 0 1 := by
  unfold negativePlaneWeight
  split_ifs
  exacts [⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩, ⟨le_rfl, zero_le_one⟩]

/-- The weights vanish off the part `s < 0` of the end `∞` and on the inputs. -/
private theorem endSign_mul_re_endCoord_pos_of_negativePlaneWeight_ne_zero {q : Puncture}
    {w : ℂ} (h : negativePlaneWeight q w ≠ 0) : 0 < q.endSign * (q.endCoord w).re := by
  unfold negativePlaneWeight at h
  split_ifs at h with hq
  · subst hq
    rw [endSign_inf, neg_one_mul]
    by_contra! h'
    exact h (smoothTransition.zero_of_nonpos (by linarith))
  · exact absurd rfl h

/-- The almost complex structure on `M` of the negative PSS plane with end structures `J t`, at
the point `w ∈ ℂ`. It is the end-weighted structure
`TauCeti.SmoothTwoForm.Compatible.endWeightedAlmostComplex` with the end structures `J t` and the
weights `β(-s - 1)` on the end `∞` and `0` on the inputs, so on each tangent space it is the linear
negative plane structure `TauCeti.Floer.negativePlaneAlmostComplex` of `J₀` and the end
structures. -/
def negativePlaneAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M :=
  h₀.endWeightedAlmostComplex (fun _ => J) (fun _ => hJ) negativePlaneWeight
    negativePlaneWeight_mem_Icc
    (fun _ _ => endSign_mul_re_endCoord_pos_of_negativePlaneWeight_ne_zero) w

/-- The negative plane structure is tamed by `σ`. -/
theorem tames_negativePlaneAlmostComplex (w : ℂ) :
    σ.Tames (h₀.negativePlaneAlmostComplex J hJ w) :=
  tames_endWeightedAlmostComplex h₀ _ _ _ _ _ w

/-- The value on a tangent fiber is precisely the linear negative plane structure there. -/
theorem almostComplexStructureAt_negativePlaneAlmostComplex (w : ℂ) (x : M) :
    (h₀.negativePlaneAlmostComplex J hJ w).almostComplexStructureAt x =
      Floer.negativePlaneAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun t _ => (J t).almostComplexStructureAt x)
        (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x) w () := by
  -- Both structures are tame and have the same Cayley coordinate relative to `J₀`.
  refine (h₀.compatibleAt x).eq_of_cayley_eq
    (h₀.isNondegenerate.tames_iff.mp (tames_negativePlaneAlmostComplex h₀ J hJ w) x)
    (Floer.tames_negativePlaneAlmostComplex (h₀.compatibleAt x) w ()) ?_
  rw [negativePlaneAlmostComplex, cayley_endWeightedAlmostComplex,
    Floer.cayley_negativePlaneAlmostComplex,
    Fintype.sum_eq_single inf fun q hq => by simp [negativePlaneWeight, hq]]
  simp [negativePlaneWeight]

/-- The negative plane structure is `σ`-compatible when the end structures are. -/
theorem compatible_negativePlaneAlmostComplex (hJc : ∀ t, σ.Compatible (J t)) (w : ℂ) :
    σ.Compatible (h₀.negativePlaneAlmostComplex J hJ w) :=
  compatible_endWeightedAlmostComplex h₀ _ _ _ _ _ (fun _ => hJc) w

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
    h₀.negativePlaneAlmostComplex J hJ w = J₀ :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_negativePlaneAlmostComplex]
    exact Floer.negativePlaneAlmostComplex_eq_of_norm_le (h₀.compatibleAt x) hw ()

/-- **The structure is `J t` far out on the end.** If `J` has period one in `t`, then on the part
`s ≤ -2` of the end, the negative plane structure at the point with end coordinates `z = s + i t`
is `J t`. -/
theorem negativePlaneAlmostComplex_cylindricalEndLift (hJp : Function.Periodic J 1) {z : ℂ}
    (hz : z.re ≤ -2) : h₀.negativePlaneAlmostComplex J hJ (inf.cylindricalEndLift z) = J z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_negativePlaneAlmostComplex]
    exact Floer.negativePlaneAlmostComplex_cylindricalEndLift (h₀.compatibleAt x)
      (fun t => by simp only [hJp t]) hz ()

/-- **The plane structure is smooth.** For end structures which have period one in `t` and are
`C^n` on `ℝ × M`, the negative plane structures are `C^n` along every `C^n` family of points `f`
of `ℂ`, including the pole, and points `b` of `M`. -/
theorem contMDiff_negativePlaneAlmostComplex {F G N : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace G] {I' : ModelWithCorners ℝ F G} [TopologicalSpace N]
    [ChartedSpace G N] {n : ℕ∞ω} [ENat.LEInfty n] (hJp : Function.Periodic J 1)
    (hJs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
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
    exact SmoothAlmostComplexStructure.contMDiffAt_toEndomorphism_of_eventuallyEq (hb y₀)
      ((hf.continuous.norm.continuousAt.eventually (gt_mem_nhds hlt)).mono fun y hy =>
        negativePlaneAlmostComplex_eq_of_norm_le h₀ J hJ hy.le)
  -- Off it, the point is not a puncture, where the end coordinates are smooth.
  have h₁ : 1 < ‖f y₀‖ :=
    lt_of_lt_of_le (by linarith [Real.one_le_exp (by positivity : 0 ≤ 2 * π)]) hge
  have hS : f y₀ ≠ 0 ∧ f y₀ ≠ 1 :=
    ⟨fun h => by norm_num [h] at h₁, fun h => by norm_num [h] at h₁⟩
  simp only [negativePlaneAlmostComplex]
  refine contMDiffAt_endWeightedAlmostComplex h₀ _ _ (c := fun _ => negativePlaneWeight) (hb y₀)
    (fun q => ?_)
    fun q => q.contMDiffAt_toEndomorphism_comp_im_endCoord hJp hJs (hf y₀) (hb y₀)
      (ne_endCenter hS q)
  -- Only the weight of the end `∞` is nonzero, and it is smooth off the center of that end.
  by_cases hq : q = inf
  · simp only [negativePlaneWeight, hq, ↓reduceIte]
    simpa only [endSign_inf, neg_one_mul] using
      Floer.contMDiffAt_smoothTransition_endCoord_comp inf 1 (hf y₀) (ne_endCenter hS inf)
  · simp only [negativePlaneWeight, hq, ↓reduceIte]
    exact contMDiffAt_const

end TauCeti.SmoothTwoForm.Compatible
