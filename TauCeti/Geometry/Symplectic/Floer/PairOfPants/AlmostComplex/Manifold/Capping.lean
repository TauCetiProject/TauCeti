/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Plumbing

/-!
# The negative PSS plane and the capping families on a manifold

The unit of the pair-of-pants product counts *negative planes*: maps from `ℂ` with an incidence
condition at the pole `0` and a negative (output) cylindrical end at `∞`. Its unit property is
proved with the *capping families*, which glue a negative plane into an input `q ∈ {0, 1}` of the
pair of pants along a neck of length `L`. This file constructs the domain-dependent almost complex
structures of these domains on the tangent bundle of a manifold `M` with a nondegenerate two-form
`σ`, such as a closed symplectic manifold. The linear constructions on a fixed symplectic vector
space are `TauCeti.Floer.negativePlaneAlmostComplex` and the plumbed structure with base inputs of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capping`.

Fix a `σ`-compatible base structure `J₀` and a jointly smooth period-one family `J t` of `σ`-tame
structures. The negative plane structure
`TauCeti.SmoothTwoForm.Compatible.negativePlaneAlmostComplex` is the manifold pair-of-pants
structure whose two input families are the constant family `J₀` and whose output family is `J`,
on `ℂ ∖ {0, 1}`, and `J₀` at the two points `0` and `1`.

* On every tangent fiber it is the linear negative plane structure
  (`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_negativePlaneAlmostComplex`).
* It is `σ`-tame, and `σ`-compatible when every `J t` is.
* It is `J₀` on the pole disc `‖w‖ ≤ 2 exp (2π)`, which contains `0` and `1`, and it is `J t` on
  the part `s ≤ -2` of the end at `∞`.
* It is smooth jointly in the domain point `w ∈ ℂ` and the target point, including at `0` and `1`
  (`TauCeti.SmoothTwoForm.Compatible.contMDiff_negativePlaneAlmostComplex`). The pair-of-pants
  structure is only smooth on `ℂ ∖ {0, 1}`; the plane structure extends smoothly across these
  points because it is `J₀` near them.

For an input `q ≠ ∞` of a pair of pants with end families `Jb`, the capping structure
`TauCeti.SmoothTwoForm.Compatible.cappingAlmostComplex` plumbs the negative plane with end family
`Jb q` into the end `q` along a neck of length `L`. It is the manifold plumbed structure whose
inserted pair of pants has the input families `J₀`, on the four-punctured sphere
`ℂ ∖ {0, 1, ψ(1)}`, and `J₀` at the three missing points.

* On every tangent fiber of the four-punctured sphere it is the linear plumbed structure
  (`TauCeti.SmoothTwoForm.Compatible.almostComplexStructureAt_cappingAlmostComplex`).
* For `L > 2` it is `J₀` on the disc of radius `exp (-2π(L - 1)) / 2` about the capped puncture
  `c_q`, the image of the pole disc of the plane, which contains `c_q` and `ψ(1)`.
* Off the collar `Re z > L - 2` of the end `q` it is the structure of the receiving pair of pants,
  and deep in the end `q` it is the negative plane structure in the plumbing coordinate
  `w ↦ (w - c_q) / ψ'`.
* For `L > 4` it is smooth jointly in the neck length, the domain point and the target point on the
  capped cylinder `ℂ ∖ {c_q'}`, where `q'` is the other input
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

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

/-! ### The end data of the negative plane -/

section EndData

variable {J : ℝ → SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] in
/-- Families indexed by the ends that are `J` at `∞` and the constant family `J₀` at the inputs
inherit any property shared by `J` and the constant family. -/
private theorem SmoothAlmostComplexStructure.forall_update_inf
    {P : (ℝ → SmoothAlmostComplexStructure I M) → Prop} (h₀ : P fun _ => J₀) (hJ : P J)
    (q : Puncture) : P (update (fun _ _ => J₀) inf J q) := by
  rcases eq_or_ne q inf with rfl | hq
  · simpa using hJ
  · simpa [update_of_ne hq] using h₀

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane, `J` at `∞` and `J₀` at the inputs, are tame when `J₀`
and `J` are. -/
theorem SmoothTwoForm.tames_update_inf (h₀ : σ.Tames J₀) (hJ : ∀ t, σ.Tames (J t))
    (q : Puncture) (t : ℝ) :
    σ.Tames (update (fun _ _ => J₀) inf J q t) :=
  SmoothAlmostComplexStructure.forall_update_inf (P := fun f => ∀ t, σ.Tames (f t)) (fun _ => h₀)
    hJ q t

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane have period one when `J` has. -/
theorem SmoothAlmostComplexStructure.periodic_update_inf (hJp : Periodic J 1) (q : Puncture) :
    Periodic (update (fun _ _ => J₀) inf J q) 1 :=
  forall_update_inf (P := fun f => Periodic f 1) (fun _ => rfl) hJp q

omit [FiniteDimensional ℝ E] in
/-- The end families of the negative plane are jointly smooth when `J` is. -/
theorem SmoothAlmostComplexStructure.contMDiff_update_inf
    (hJs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J p.1).toEndomorphism p.2)))
    (q : Puncture) :
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((update (fun _ _ => J₀) inf J q p.1).toEndomorphism p.2)) :=
  forall_update_inf (P := fun f => ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((f p.1).toEndomorphism p.2)))
    (J₀.toEndomorphism.contMDiff.comp contMDiff_snd) hJs q

omit [FiniteDimensional ℝ E] in
/-- On a tangent fiber, the end families of the plane are the linear end families of the plane. -/
private theorem SmoothAlmostComplexStructure.almostComplexStructureAt_update_inf (x : M) :
    (fun q t (_ : Unit) => (update (fun _ _ => J₀) inf J q t).almostComplexStructureAt x) =
      update (fun _ _ _ => J₀.almostComplexStructureAt x) inf
        (fun t (_ : Unit) => (J t).almostComplexStructureAt x) := by
  funext q t u
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · simp [update_of_ne hq]

end EndData

namespace SmoothTwoForm.Compatible

open SmoothAlmostComplexStructure

/-- The points `0` and `1` lie in the open pole disc `‖w‖ < 2 exp (2π)` of the negative plane. -/
private theorem norm_lt_of_not_ne_zero_and_ne_one {w : ℂ} (hw : ¬(w ≠ 0 ∧ w ≠ 1)) :
    ‖w‖ < 2 * Real.exp (2 * π) := by
  have h1 : 1 ≤ Real.exp (2 * π) := Real.one_le_exp (by positivity)
  rcases eq_or_ne w 0 with rfl | h0
  · rw [norm_zero]
    positivity
  · rw [show w = 1 by tauto, norm_one]
    linarith

/-! ### The negative plane -/

section NegativePlane

variable (h₀ : σ.Compatible J₀) (J : ℝ → SmoothAlmostComplexStructure I M)
  (hJ : ∀ t, σ.Tames (J t)) (hJp : Periodic J 1)
  (hJs : ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((J p.1).toEndomorphism p.2)))

/-- The almost complex structure on the tangent bundle over the negative PSS plane with end family
`J`, relative to a compatible base structure `J₀`. On `ℂ ∖ {0, 1}` it is the pair-of-pants
structure with input families `J₀` and output family `J`, and it is `J₀` at `0` and `1`. -/
def negativePlaneAlmostComplex (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if hw : w ≠ 0 ∧ w ≠ 1 then
    h₀.pairOfPantsAlmostComplex (update (fun _ _ => J₀) inf J)
      (tames_update_inf h₀.tames hJ) (periodic_update_inf hJp) (contMDiff_update_inf hJs)
      ⟨w, hw⟩
  else J₀

/-- On `ℂ ∖ {0, 1}` the negative plane structure is the pair-of-pants structure with input
families `J₀` and output family `J`. -/
theorem negativePlaneAlmostComplex_eq_pairOfPantsAlmostComplex {w : ℂ} (hw : w ≠ 0 ∧ w ≠ 1) :
    h₀.negativePlaneAlmostComplex J hJ hJp hJs w =
      h₀.pairOfPantsAlmostComplex (update (fun _ _ => J₀) inf J)
        (tames_update_inf h₀.tames hJ) (periodic_update_inf hJp) (contMDiff_update_inf hJs)
        ⟨w, hw⟩ :=
  dite_eq_left hw

/-- On every tangent fiber, the negative plane structure is the linear negative plane structure
of the fiberwise end family. -/
theorem almostComplexStructureAt_negativePlaneAlmostComplex (w : ℂ) (x : M) :
    (h₀.negativePlaneAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x =
      Floer.negativePlaneAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (fun t _ => (J t).almostComplexStructureAt x)
        (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x) w () := by
  by_cases hw : w ≠ 0 ∧ w ≠ 1
  · rw [negativePlaneAlmostComplex_eq_pairOfPantsAlmostComplex h₀ J hJ hJp hJs hw,
      almostComplexStructureAt_pairOfPantsAlmostComplex,
      ← Floer.pairOfPantsAlmostComplex_update_inf (h₀.compatibleAt x)
        (Floer.tames_update_inf (h₀.compatibleAt x).tames
          (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJ t) x))]
    congr 1
    exact almostComplexStructureAt_update_inf x
  · rw [negativePlaneAlmostComplex, dite_eq_right hw,
      Floer.negativePlaneAlmostComplex_eq_of_norm_le _ (norm_lt_of_not_ne_zero_and_ne_one hw).le]

/-- The negative plane structure is tamed by the two-form. -/
theorem tames_negativePlaneAlmostComplex (w : ℂ) :
    σ.Tames (h₀.negativePlaneAlmostComplex J hJ hJp hJs w) := by
  refine h₀.isNondegenerate.tames_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_negativePlaneAlmostComplex]
  exact Floer.tames_negativePlaneAlmostComplex (h₀.compatibleAt x) w ()

/-- The negative plane structure is compatible with the two-form when the end structures are. -/
theorem compatible_negativePlaneAlmostComplex (hJc : ∀ t, σ.Compatible (J t)) (w : ℂ) :
    σ.Compatible (h₀.negativePlaneAlmostComplex J hJ hJp hJs w) := by
  refine h₀.isNondegenerate.compatible_iff.mpr fun x => ?_
  rw [almostComplexStructureAt_negativePlaneAlmostComplex]
  exact Floer.compatible_negativePlaneAlmostComplex (h₀.compatibleAt x)
    (fun t _ => h₀.isNondegenerate.compatible_iff.mp (hJc t) x) w ()

/-- The Cayley transform of the negative plane structure, relative to `J₀`, is
`β(-s(w) - 1) • cayley (J (t(w)))` on every tangent fiber. This characterizes the structure, since
the Cayley transform is injective on tame structures. -/
@[simp]
theorem cayley_negativePlaneAlmostComplex (w : ℂ) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.negativePlaneAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x) =
      smoothTransition (-(inf.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((J (inf.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.cayley_negativePlaneAlmostComplex]

/-- **The pole disc.** The negative plane structure is the base structure `J₀` on the disc
`‖w‖ ≤ 2 exp (2π)` about the pole. -/
theorem negativePlaneAlmostComplex_eq_of_norm_le {w : ℂ} (hw : ‖w‖ ≤ 2 * Real.exp (2 * π)) :
    h₀.negativePlaneAlmostComplex J hJ hJp hJs w = J₀ := by
  ext x v
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.negativePlaneAlmostComplex_eq_of_norm_le _ hw,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- **The structure is `J t` far out on the end.** On the part `s ≤ -2` of the end at `∞`, the
negative plane structure at the point with end coordinates `z = s + i t` is `J t`. -/
theorem negativePlaneAlmostComplex_cylindricalEndLift {z : ℂ} (hz : z.re ≤ -2) :
    h₀.negativePlaneAlmostComplex J hJ hJp hJs (inf.cylindricalEndLift z) = J z.im := by
  ext x v
  have hp : Periodic (fun t (_ : Unit) => (J t).almostComplexStructureAt x) 1 := fun t => by
    simp only [hJp t]
  rw [← SmoothAlmostComplexStructure.almostComplexStructureAt_apply,
    almostComplexStructureAt_negativePlaneAlmostComplex,
    Floer.negativePlaneAlmostComplex_cylindricalEndLift _ hp hz,
    SmoothAlmostComplexStructure.almostComplexStructureAt_apply]

/-- **The plane structure is smooth.** The negative plane structure is `C^n` jointly in the domain
point and the target point, along any `C^n` family of these, as a section of the tangent
endomorphism bundle. Unlike the pair-of-pants structure, the domain points may be `0` and `1`. The
family may depend on further manifold parameters. -/
theorem contMDiff_negativePlaneAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] {f : N → ℂ} {b : N → M} (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f)
    (hb : ContMDiff I' I n b) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.negativePlaneAlmostComplex J hJ hJp hJs (f p)).toEndomorphism (b p))) := by
  intro p
  rcases lt_or_ge ‖f p‖ (2 * Real.exp (2 * π)) with hlt | hge
  · -- Near a point of the open pole disc, the structure is `J₀`.
    refine (((J₀.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp hb) p).congr_of_eventuallyEq
      ?_
    filter_upwards [hf.continuous.norm.continuousAt.eventually (gt_mem_nhds hlt)] with p' hp'
    rw [negativePlaneAlmostComplex_eq_of_norm_le h₀ J hJ hJp hJs hp'.le]
    rfl
  · -- Off it, the point lies in the pair of pants with base inputs. Restrict the family to the
    -- open set of parameters whose domain point avoids `0` and `1`.
    have hS : f p ≠ 0 ∧ f p ≠ 1 := by
      by_contra h
      exact (norm_lt_of_not_ne_zero_and_ne_one h).not_ge hge
    let U : TopologicalSpace.Opens N :=
      ⟨{y | f y ≠ 0 ∧ f y ≠ 1}, (isOpen_ne_fun hf.continuous continuous_const).inter
        (isOpen_ne_fun hf.continuous continuous_const)⟩
    have hU := h₀.contMDiff_pairOfPantsAlmostComplex (update (fun _ _ => J₀) inf J)
      (tames_update_inf h₀.tames hJ) (periodic_update_inf hJp) (contMDiff_update_inf hJs)
      (hf.comp contMDiff_subtype_val) (hb.comp contMDiff_subtype_val) (fun y : U => y.2)
    refine contMDiffAt_subtype_iff (U := U) (x := ⟨p, hS⟩).mp ?_
    refine (hU ⟨p, hS⟩).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [comp_apply,
      negativePlaneAlmostComplex_eq_pairOfPantsAlmostComplex h₀ J hJ hJp hJs y.2]

end NegativePlane

/-! ### Capping an input of the pair of pants -/

section Capping

variable (h₀ : σ.Compatible J₀) (Jb : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJb : ∀ r t, σ.Tames (Jb r t)) (hJbp : ∀ r, Periodic (Jb r) 1)
  (hJbs : ∀ r, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((Jb r p.1).toEndomorphism p.2)))
  {q : Puncture} {L : ℝ}

/-- The almost complex structure on the tangent bundle over the pair of pants with end families
`Jb` whose input `q` is capped by the negative plane with end family `Jb q`, plumbed along a neck
of length `L`, relative to a compatible base structure `J₀` on both pieces. On the four-punctured
sphere `ℂ ∖ {0, 1, ψ(1)}` it is the plumbed structure whose inserted pair of pants has the input
families `J₀`, and it is `J₀` at the three missing points. -/
def cappingAlmostComplex (q : Puncture) (L : ℝ) (w : ℂ) : SmoothAlmostComplexStructure I M :=
  if hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1 then
    h₀.plumbedAlmostComplex h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
      (tames_update_inf h₀.tames (hJb q)) hJb (periodic_update_inf (hJbp q))
      (contMDiff_update_inf (hJbs q)) hJbp hJbs q L w hw
  else J₀

/-- On the four-punctured sphere the capping structure is the plumbed structure whose inserted
pair of pants has the input families `J₀`. -/
theorem cappingAlmostComplex_eq_plumbedAlmostComplex {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) :
    h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w =
      h₀.plumbedAlmostComplex h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
        (tames_update_inf h₀.tames (hJb q)) hJb (periodic_update_inf (hJbp q))
        (contMDiff_update_inf (hJbs q)) hJbp hJbs q L w hw :=
  dite_eq_left hw

/-- On every tangent fiber of the four-punctured sphere, the capping structure is the linear
plumbed structure of the fiberwise end families, with base inputs on the inserted piece. -/
theorem almostComplexStructureAt_cappingAlmostComplex {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    (h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w).almostComplexStructureAt x =
      Floer.plumbedAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
        (h₀.compatibleAt x)
        (update (fun _ _ _ => J₀.almostComplexStructureAt x) inf
          (fun t _ => (Jb q t).almostComplexStructureAt x))
        (fun r t _ => (Jb r t).almostComplexStructureAt x)
        (Floer.tames_update_inf (h₀.compatibleAt x).tames
          (fun t _ => h₀.isNondegenerate.tames_iff.mp (hJb q t) x))
        (fun r t _ => h₀.isNondegenerate.tames_iff.mp (hJb r t) x) q L w () := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs hw,
    almostComplexStructureAt_plumbedAlmostComplex]
  congr 1
  exact almostComplexStructureAt_update_inf x

/-- The capping structure is tamed by the two-form, regardless of the neck length. -/
theorem tames_cappingAlmostComplex (w : ℂ) :
    σ.Tames (h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w) := by
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs hw]
    exact tames_plumbedAlmostComplex h₀ h₀ _ _ _ _ _ _ _ _ w hw
  · rw [cappingAlmostComplex, dite_eq_right hw]
    exact h₀.tames

/-- The capping structure is compatible with the two-form when the end structures are. -/
theorem compatible_cappingAlmostComplex (hJbc : ∀ r t, σ.Compatible (Jb r t)) (w : ℂ) :
    σ.Compatible (h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w) := by
  by_cases hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs hw]
    exact compatible_plumbedAlmostComplex h₀ h₀ _ _ _ _ _ _ _ _
      (forall_update_inf (P := fun f => ∀ t, σ.Compatible (f t)) (fun _ => h₀) (hJbc q)) hJbc w hw
  · rw [cappingAlmostComplex, dite_eq_right hw]
    exact h₀

/-- **The capped disc.** For a neck length `L > 2`, the capping structure is `J₀` on the disc of
radius `exp (-2π(L - 1)) / 2` about the capped puncture `c_q`, the image under the plumbing map of
the pole disc of the plane. -/
theorem cappingAlmostComplex_eq_of_norm_sub_endCenter_le (hq : q ≠ inf) (hL : 2 < L) {w : ℂ}
    (hw : ‖w - q.endCenter‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) :
    h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w = J₀ := by
  by_cases hw' : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1
  · ext x v
    have h : (h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w).almostComplexStructureAt x =
        J₀.almostComplexStructureAt x := by
      rw [almostComplexStructureAt_cappingAlmostComplex h₀ Jb hJb hJbp hJbs hw']
      exact Floer.plumbedAlmostComplex_update_inf_eq
        (Jb := fun r t _ => (Jb r t).almostComplexStructureAt x) _ hq hL hw ()
    simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
      congrArg (fun A : AlmostComplexStructure (TangentSpace I x) => A v) h
  · rw [cappingAlmostComplex, dite_eq_right hw']

/-- Off the width-two collar `Re z > L - 2` of the end `q`, the capping structure is the structure
of the receiving pair of pants. -/
theorem cappingAlmostComplex_of_re_endCoord_le (hq : q ≠ inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (hle : (q.endCoord w).re ≤ L - 2) :
    h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w =
      h₀.pairOfPantsAlmostComplex Jb hJb hJbp hJbs ⟨w, hw.1⟩ := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs hw]
  exact plumbedAlmostComplex_of_re_endCoord_le _ _ _ _ _ _ _ _ _ _ hq
    (update_self inf (Jb q) fun _ _ => J₀).symm hw hle

/-- **The plane in the plumbing coordinate.** Deep in the end `q`, the capping structure is the
negative plane structure with end family `Jb q` at the point `(w - c_q) / ψ'` of the plane. This
holds on an open set independent of the neck length. -/
theorem cappingAlmostComplex_eq_negativePlaneAlmostComplex (hq : q ≠ inf) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (h2 : 2 < (q.endCoord w).re) :
    h₀.cappingAlmostComplex Jb hJb hJbp hJbs q L w =
      h₀.negativePlaneAlmostComplex (Jb q) (hJb q) (hJbp q) (hJbs q)
        ((w - q.endCenter) / q.plumbingFactor L) := by
  rw [cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs hw,
    plumbedAlmostComplex_eq_inserted _ _ _ _ _ _ _ _ _ _ hq
      (update_self inf (Jb q) fun _ _ => J₀).symm hw h2,
    negativePlaneAlmostComplex_eq_pairOfPantsAlmostComplex h₀ _ _ _ _
      (q.sub_endCenter_div_plumbingFactor_ne_zero_and_ne_one L hw)]

/-- **The capping structure is smooth.** For neck lengths `L > 4`, the capping structure is `C^n`
jointly in the neck length, the domain point and the target point, along any `C^n` family of these
whose domain points lie in the capped cylinder `ℂ ∖ {c_q'}`, where `q'` is the other input: each
domain point is the capped puncture `c_q` or a point of `ℂ ∖ {0, 1}`. The family may depend on
further manifold parameters. -/
theorem contMDiff_cappingAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n] (hq : q ≠ inf)
    {ℓ : N → ℝ} {f : N → ℂ} {b : N → M} (hℓ : ContMDiff I' 𝓘(ℝ) n ℓ)
    (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f) (hb : ContMDiff I' I n b) (hL : ∀ p, 4 < ℓ p)
    (hS : ∀ p, f p = q.endCenter ∨ f p ≠ 0 ∧ f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) (b p)
        ((h₀.cappingAlmostComplex Jb hJb hJbp hJbs q (ℓ p) (f p)).toEndomorphism (b p))) := by
  intro p
  set ρ : ℝ → ℝ := fun l => Real.exp (-(2 * π * (l - 1))) / 2
  have hρ : Continuous fun y => ρ (ℓ y) := by
    have : Continuous ρ := by fun_prop
    exact this.comp hℓ.continuous
  rcases lt_or_ge ‖f p - q.endCenter‖ (ρ (ℓ p)) with hlt | hge
  · -- Near a point of the open capped disc, for nearby neck lengths, the structure is `J₀`.
    refine (((J₀.toEndomorphism.contMDiff.of_le ENat.LEInfty.out).comp hb) p).congr_of_eventuallyEq
      ?_
    filter_upwards [(hf.continuous.sub continuous_const).norm.continuousAt.eventually_lt
      hρ.continuousAt hlt] with p' hp'
    rw [cappingAlmostComplex_eq_of_norm_sub_endCenter_le h₀ Jb hJb hJbp hJbs hq
      (by linarith [hL p']) hp'.le]
    rfl
  · -- Off it, the point lies in the plumbed four-punctured sphere. Restrict the family to the
    -- open set of parameters whose domain point lies there.
    have hc : f p ≠ q.endCenter := fun h => by
      rw [h, sub_self, norm_zero] at hge
      exact (by positivity : 0 < ρ (ℓ p)).not_ge hge
    have h₁ : f p ≠ q.plumbingMap (ℓ p) 1 := fun h =>
      (h ▸ norm_plumbingMap_one_sub_endCenter_lt hq (ℓ p)).not_ge hge
    have hψ : Continuous fun y => q.plumbingMap (ℓ y) 1 := by
      simp only [plumbingMap_apply]
      exact continuous_const.add
        ((q.contDiff_plumbingFactor (n := 0)).continuous.comp hℓ.continuous |>.mul continuous_const)
    let U : TopologicalSpace.Opens N :=
      ⟨{y | (f y ≠ 0 ∧ f y ≠ 1) ∧ f y ≠ q.plumbingMap (ℓ y) 1},
        ((isOpen_ne_fun hf.continuous continuous_const).inter
          (isOpen_ne_fun hf.continuous continuous_const)).inter (isOpen_ne_fun hf.continuous hψ)⟩
    have hU := h₀.contMDiff_plumbedAlmostComplex h₀ (update (fun _ _ => J₀) inf (Jb q)) Jb
      (tames_update_inf h₀.tames (hJb q)) hJb (periodic_update_inf (hJbp q))
      (contMDiff_update_inf (hJbs q)) hJbp hJbs hq (update_self inf (Jb q) fun _ _ => J₀).symm
      (hℓ.comp contMDiff_subtype_val) (hf.comp contMDiff_subtype_val)
      (hb.comp contMDiff_subtype_val) (fun y : U => hL y) (fun y : U => y.2)
    refine contMDiffAt_subtype_iff (U := U) (x := ⟨p, ⟨(hS p).resolve_left hc, h₁⟩⟩).mp ?_
    refine (hU _).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp only [comp_apply, cappingAlmostComplex_eq_plumbedAlmostComplex h₀ Jb hJb hJbp hJbs y.2]

end Capping

end SmoothTwoForm.Compatible

end TauCeti
