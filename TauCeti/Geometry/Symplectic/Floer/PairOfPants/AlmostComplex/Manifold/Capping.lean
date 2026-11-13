/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Plumbing

/-!
# The negative PSS plane and the capping families in a manifold

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
On `ℂ ∖ {0, 1}` it is the pair-of-pants structure whose input families are the constant family
`J₀` and whose output family is `J`
(`TauCeti.SmoothTwoForm.Compatible.pairOfPantsAlmostComplex_update_inf`).

The unit property of the pair-of-pants product is proved with the *capping families*, which glue a
negative plane into an input `q ∈ {0, 1}` of the pair of pants along a neck of length `L`. For
such an input of a pair of pants with end families `Jb`, the capping structure
`TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex` plumbs the negative plane with end family
`Jb q` into the end `q`. It is the manifold plumbed structure
`TauCeti.SmoothTwoForm.Compatible.plumbedAlmostComplex` whose inserted pair of pants has the input
families `J₀`, on the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, and `J₀` at the three missing
points (`TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex_of_not`).

* On every tangent fiber of the four-punctured sphere it is the linear plumbed structure
  (`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cappingAlmostComplex`).
* It is tame, and compatible when the end structures are.
* For `L > 2` it is `J₀` on the disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture
  `c_q`, the image of the pole disc of the plane, which contains `c_q` and `ψ(1)`.
* Off the collar `Re z > L - 2` of the end `q` it is the structure of the receiving pair of pants,
  and deep in the end `q` it is the negative plane structure in the plumbing coordinate
  `w ↦ (w - c_q) / ψ'`.
* For `L > 4` and period-one end structures which are jointly `C^n` on `ℝ × M`, it is jointly
  `C^n` in the neck length, the domain point and the target point on the capped cylinder
  `ℂ ∖ {c_q'}`, where `q'` is the other input
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappingAlmostComplex`).

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  perturbed planes of the PSS maps and the unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
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

/-! ### The plane as a pair of pants with base inputs -/

section UpdateInf

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane, `K` at `∞` and a tame base structure `J₀` at the
inputs, are tame when `K` is. -/
theorem _root_.TauCeti.SmoothTwoForm.tames_update_inf (h₀ : σ.Tames J₀)
    {K : ℝ → SmoothAlmostComplexStructure I M} (hK : ∀ t, σ.Tames (K t)) (q : Puncture) (t : ℝ) :
    σ.Tames (update (fun _ _ => J₀) inf K q t) :=
  (forall_update_iff (fun _ _ => J₀) fun _ f => ∀ t, σ.Tames (f t)).2 ⟨hK, fun _ _ _ => h₀⟩ q t

omit [FiniteDimensional ℝ E] in
/-- Dually, the end families of the input part of a pair of pants, `K` at the inputs and a tame base
structure `J₀` at `∞`, are tame when `K` is. -/
theorem _root_.TauCeti.SmoothTwoForm.tames_update_inf_base (hJ₀ : σ.Tames J₀)
    {K : Puncture → ℝ → SmoothAlmostComplexStructure I M} (hK : ∀ q t, σ.Tames (K q t))
    (q : Puncture) (t : ℝ) : σ.Tames (update K inf (fun _ => J₀) q t) :=
  (forall_update_iff K fun _ f => ∀ t, σ.Tames (f t)).2 ⟨fun _ => hJ₀, fun q _ => hK q⟩ q t

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane, `K` at `∞` and the constant family `J₀` at the inputs,
have period one when `K` does. -/
theorem _root_.TauCeti.SmoothAlmostComplexStructure.periodic_update_inf
    {K : ℝ → SmoothAlmostComplexStructure I M} (hK : Periodic K 1) (q : Puncture) :
    Periodic (update (fun _ _ => J₀) inf K q) 1 :=
  (forall_update_iff (fun _ _ => J₀) fun _ f => Periodic f 1).2 ⟨hK, fun _ _ _ => rfl⟩ q

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane, `K` at `∞` and the constant family `J₀` at the inputs,
are `C^n` on `ℝ × M` when `K` is. -/
theorem _root_.TauCeti.SmoothAlmostComplexStructure.contMDiff_update_inf {n : ℕ∞ω}
    [ENat.LEInfty n] {K : ℝ → SmoothAlmostComplexStructure I M}
    (hK : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((K p.1).toEndomorphism p.2)))
    (q : Puncture) :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((update (fun _ _ => J₀) inf K q p.1).toEndomorphism p.2)) :=
  (forall_update_iff (fun _ _ => J₀) fun _ f => ContMDiff (𝓘(ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E)) n (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((f p.1).toEndomorphism p.2))).2
    ⟨hK, fun _ _ => (J₀.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp contMDiff_snd⟩ q

omit [FiniteDimensional ℝ E] in
/-- On a tangent fiber, the end families of the plane are the linear end families of the plane. -/
private theorem almostComplexStructureAt_update_inf (K : ℝ → SmoothAlmostComplexStructure I M)
    (x : M) :
    (fun q t (_ : Unit) => (update (fun _ _ => J₀) inf K q t).almostComplexStructureAt x) =
      update (fun _ _ _ => J₀.almostComplexStructureAt x) inf
        (fun t (_ : Unit) => (K t).almostComplexStructureAt x) := by
  funext q t u
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · simp [update_of_ne hq]

/-- **The plane is a pair of pants with base inputs.** On `ℂ ∖ {0, 1}`, the pair-of-pants
structure whose input families are the constant family `J₀` and whose output family is `J` is the
negative plane structure of `J`. -/
theorem pairOfPantsAlmostComplex_update_inf
    (hJ' : ∀ q t, σ.Tames (update (fun _ _ => J₀) inf J q t)) (w : ThricePuncturedSphere) :
    h₀.pairOfPantsAlmostComplex (update (fun _ _ => J₀) inf J) hJ' w =
      h₀.negativePlaneAlmostComplex J hJ w :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    rw [almostComplexStructureAt_pairOfPantsAlmostComplex,
      almostComplexStructureAt_negativePlaneAlmostComplex,
      ← Floer.pairOfPantsAlmostComplex_update_inf (h₀.compatibleAt x)
        (Floer.tames_update_inf (h₀.compatibleAt x).tames
          (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x))]
    congr 1
    exact almostComplexStructureAt_update_inf J x

end UpdateInf

/-! ### Capping an input of the pair of pants -/

section Capping

variable (Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M) (hJb : ∀ r t, σ.Tames (Jb r t))
  {q : Puncture} {L : ℝ}

/-- The almost complex structure on the tangent bundle over the pair of pants with end families
`Jb` whose input `q` is capped by the negative plane with end family `Jb q`, plumbed along a neck
of length `L`, relative to a compatible base structure `J₀` on both pieces. On the four-punctured
sphere `ℂ ∖ {0, 1, ψ(1)}` it is the plumbed structure whose inserted pair of pants has the input
families `J₀`, and it is `J₀` at the three missing points. -/
def cappingAlmostComplex (q : Puncture) (L : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1 then
    h₀.plumbedAlmostComplex h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
      (tames_update_inf h₀.tames (hJb q)) hJb q L w hw
  else J₀

/-- On the four-punctured sphere the capping structure is the plumbed structure whose inserted
pair of pants has the input families `J₀`. -/
theorem cappingAlmostComplex_eq_plumbedAlmostComplex {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    h₀.cappingAlmostComplex Jb hJb q L w =
      h₀.plumbedAlmostComplex h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
        (tames_update_inf h₀.tames (hJb q)) hJb q L w hw :=
  dite_eq_left hw

/-- At the points `0`, `1` and `ψ(1)` missing from the four-punctured sphere, the capping
structure is `J₀`. -/
theorem cappingAlmostComplex_of_not {w : ℂ} (hw : ¬((w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)) :
    h₀.cappingAlmostComplex Jb hJb q L w = J₀ :=
  dite_eq_right hw

/-- At the puncture `0` the capping structure is `J₀`. -/
@[simp]
theorem cappingAlmostComplex_zero : h₀.cappingAlmostComplex Jb hJb q L 0 = J₀ :=
  cappingAlmostComplex_of_not h₀ Jb hJb fun h => h.1.1 rfl

/-- At the puncture `1` the capping structure is `J₀`. -/
@[simp]
theorem cappingAlmostComplex_one : h₀.cappingAlmostComplex Jb hJb q L 1 = J₀ :=
  cappingAlmostComplex_of_not h₀ Jb hJb fun h => h.1.2 rfl

/-- At the image `ψ(1)` of the input `1` of the inserted pair of pants, the capping structure is
`J₀`. -/
@[simp]
theorem cappingAlmostComplex_plumbingMap_one :
    h₀.cappingAlmostComplex Jb hJb q L (q.plumbingMap L 1) = J₀ :=
  cappingAlmostComplex_of_not h₀ Jb hJb fun h => h.2 rfl

/-- On every tangent fiber of the four-punctured sphere, the capping structure is the linear
plumbed structure of the fiberwise end families, with base inputs on the inserted piece. -/
theorem almostComplexStructureAt_cappingAlmostComplex {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    (h₀.cappingAlmostComplex Jb hJb q L w).almostComplexStructureAt x =
      Floer.plumbedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (h₀.compatibleAt x)
        (update (fun _ _ _ => J₀.almostComplexStructureAt x) inf
          (fun t _ => (Jb q t).almostComplexStructureAt x))
        (fun r t _ => (Jb r t).almostComplexStructureAt x)
        (Floer.tames_update_inf (h₀.compatibleAt x).tames
          (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJb q t) x))
        (fun r t _ => h₀.isNondegenerate.tames_iff.mp (hJb r t) x) q L w () := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hw,
    almostComplexStructureAt_plumbedAlmostComplex]
  congr 1
  exact almostComplexStructureAt_update_inf (Jb q) x

/-- The capping structure is tamed by the two-form, regardless of the neck length. -/
theorem tames_cappingAlmostComplex (w : ℂ) : σ.Tames (h₀.cappingAlmostComplex Jb hJb q L w) := by
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hw]
    exact tames_plumbedAlmostComplex h₀ h₀ _ _ _ _ w hw
  · rw [cappingAlmostComplex_of_not h₀ Jb hJb hw]
    exact h₀.tames

/-- The capping structure is compatible with the two-form when the end structures are. -/
theorem compatible_cappingAlmostComplex (hJbc : ∀ r t, σ.Compatible (Jb r t)) (w : ℂ) :
    σ.Compatible (h₀.cappingAlmostComplex Jb hJb q L w) := by
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hw]
    exact compatible_plumbedAlmostComplex h₀ h₀ _ _ _ _
      ((forall_update_iff (fun _ _ => J₀) fun _ f => ∀ t, σ.Compatible (f t)).2
        ⟨hJbc q, fun _ _ _ => h₀⟩) hJbc w hw
  · rw [cappingAlmostComplex_of_not h₀ Jb hJb hw]
    exact h₀

/-- **The capped disc.** For a neck length `L > 2`, the capping structure is `J₀` on the disc of
radius `exp (-2π(L - 1)) / 2` about the capped puncture `c_q`, the image under the plumbing map of
the pole disc of the plane. -/
theorem cappingAlmostComplex_eq_of_norm_sub_endCenter_le (hq : q ≠ inf) (hL : 2 < L) {w : ℂ}
    (hw : ‖w - q.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) :
    h₀.cappingAlmostComplex Jb hJb q L w = J₀ := by
  by_cases hw' : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
    rw [almostComplexStructureAt_cappingAlmostComplex h₀ Jb hJb hw']
    exact Floer.plumbedAlmostComplex_update_inf_eq
      (Jb := fun r t _ => (Jb r t).almostComplexStructureAt x) (h₀.compatibleAt x) hq hL hw ()
  · exact cappingAlmostComplex_of_not h₀ Jb hJb hw'

/-- Off the width-two collar `Re z > L - 2` of the end `q`, the capping structure is the structure
of the receiving pair of pants. -/
theorem cappingAlmostComplex_of_re_endCoord_le (hq : q ≠ inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (hle : (q.endCoord w).re ≤ L - 2) :
    h₀.cappingAlmostComplex Jb hJb q L w = h₀.pairOfPantsAlmostComplex Jb hJb ⟨w, hw.1⟩ := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hw]
  exact plumbedAlmostComplex_of_re_endCoord_le _ _ _ _ _ _ hq
    (update_self inf (Jb q) fun _ _ => J₀).symm hw hle

/-- **The plane in the plumbing coordinate.** Deep in the end `q`, the capping structure is the
negative plane structure with end family `Jb q` at the point `(w - c_q) / ψ'` of the plane. This
holds on the part `2 < Re z` of the end `q`, off the punctures `0`, `1` and `ψ(1)`. -/
theorem cappingAlmostComplex_eq_negativePlaneAlmostComplex (hq : q ≠ inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (h2 : 2 < (q.endCoord w).re) :
    h₀.cappingAlmostComplex Jb hJb q L w =
      h₀.negativePlaneAlmostComplex (Jb q) (hJb q) ((w - q.endCenter) / q.plumbingFactor L) := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hw,
    plumbedAlmostComplex_eq_inserted _ _ _ _ _ _ hq
      (update_self inf (Jb q) fun _ _ => J₀).symm hw h2,
    pairOfPantsAlmostComplex_update_inf h₀ (Jb q) (hJb q)]

/-- **The capping structure is smooth.** For end structures which have period one in `t` and are
`C^n` on `ℝ × M`, and neck lengths `L > 4`, the capping structure is `C^n` jointly in the neck
length, the domain point and the target point, along any `C^n` family of these whose domain points
lie in the capped cylinder `ℂ ∖ {c_q'}`, where `q'` is the other input: each domain point is the
capped puncture `c_q` or a point of `ℂ ∖ {0, 1}`. The family may depend on further manifold
parameters. -/
theorem contMDiff_cappingAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hJbp : ∀ r, Periodic (Jb r) 1)
    (hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((Jb r p.1).toEndomorphism p.2)))
    (hq : q ≠ inf) {ℓ : N → ℝ} {f : N → ℂ} {b : N → M} (hℓ : ContMDiff I' 𝓘(ℝ) n ℓ)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hL : ∀ p, 4 < ℓ p)
    (hS : ∀ p, f p = q.endCenter ∨ f p ≠ 0 ∧ f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b p)
        ((h₀.cappingAlmostComplex Jb hJb q (ℓ p) (f p)).toEndomorphism (b p))) := by
  intro p
  set ρ : ℝ → ℝ := fun l => Real.exp (-(2 * π * (l - 1))) / 2
  have hρ : Continuous fun y => ρ (ℓ y) := by
    have : Continuous ρ := by fun_prop
    exact this.comp hℓ.continuous
  rcases lt_or_ge ‖f p - q.endCenter‖ (ρ (ℓ p)) with hlt | hge
  · -- Near a point of the open capped disc, for nearby neck lengths, the structure is `J₀`.
    exact SmoothAlmostComplexStructure.contMDiffAt_toEndomorphism_of_eventuallyEq (hb p)
      (((hf.continuous.sub continuous_const).norm.continuousAt.eventually_lt
        hρ.continuousAt hlt).mono fun p' hp' =>
          cappingAlmostComplex_eq_of_norm_sub_endCenter_le h₀ Jb hJb hq (by linarith [hL p'])
            hp'.le)
  -- Off it, the point lies in the plumbed four-punctured sphere. Restrict the family to the open
  -- set of parameters whose domain point lies there.
  have hψ : Continuous fun y => q.plumbingMap (ℓ y) 1 := by
    simp only [plumbingMap_apply]
    exact continuous_const.add
      ((q.contDiff_plumbingFactor (n := 0)).continuous.comp hℓ.continuous |>.mul continuous_const)
  let U : TopologicalSpace.Opens N :=
    ⟨{y | (f y ≠ 0 ∧ f y ≠ 1) ∧ f y ≠ q.plumbingMap (ℓ y) 1},
      ((isOpen_ne_fun hf.continuous continuous_const).inter
        (isOpen_ne_fun hf.continuous continuous_const)).inter (isOpen_ne_fun hf.continuous hψ)⟩
  have hU := contMDiff_plumbedAlmostComplex h₀ h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
    (tames_update_inf h₀.tames (hJb q)) hJb
    (SmoothAlmostComplexStructure.periodic_update_inf (hJbp q))
    (SmoothAlmostComplexStructure.contMDiff_update_inf (hJbs q)) hJbp hJbs hq
    (update_self inf (Jb q) fun _ _ => J₀).symm (hℓ.comp contMDiff_subtype_val)
    (hf.comp contMDiff_subtype_val) (hb.comp contMDiff_subtype_val) (fun y : U => hL y)
    (fun y : U => y.2)
  refine contMDiffAt_subtype_iff (U := U)
    (x := ⟨p, mem_plumbedSphere_of_le_norm_sub_endCenter (hS p) hge⟩).mp ?_
  refine (hU _).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [comp_apply, cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb y.2]

end Capping

end TauCeti.SmoothTwoForm.Compatible
