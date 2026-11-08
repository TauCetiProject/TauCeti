/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.CayleySum

/-!
# Pair-of-pants almost complex data on a manifold

Given a compatible base structure and three smooth period-one families of tame structures on
an actual tangent bundle, construct a smooth domain-dependent tame structure on the
thrice-punctured sphere. Compatible end data give compatible structures. On each sufficiently
far cylindrical tail the structure is exactly the prescribed end structure; off the cutoff
regions it is the base structure.

The construction applies the linear pair-of-pants construction in each tangent fiber. Its Cayley
coordinate is a weighted sum of the Cayley coordinates of the end structures, so smoothness follows
from `TauCeti.SmoothTwoForm.Compatible.contMDiffAt_mul_one_add_cayleySum`, which is checked in
tangent trivializations. Thus no global trivialization or constant target two-form is assumed.
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

namespace TauCeti.SmoothTwoForm.Compatible

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}
  (h₀ : σ.Compatible J₀)
  (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
  (hJ : ∀ q t, σ.Tames (J q t))

/-- The fiberwise construction, read as a continuous tangent endomorphism. -/
private def pantsEnd (w : ℂ) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (M := Unit) (h₀.compatibleAt x)
      (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
      (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w ()).toLinearMap

/-- The weights of the end structures in the Cayley coordinate of the fiberwise construction. -/
private def pantsWeight (w : ℂ) (q : Puncture) : ℝ :=
  smoothTransition (q.endSign * (q.endCoord w).re - 1)

private theorem pantsCayley_toLinearMap (w : ℂ) (x : M) :
    (J₀.cayleySum (pantsWeight w) (fun q => J q (q.endCoord w).im) x).toLinearMap =
      (J₀.almostComplexStructureAt x).cayley
        (Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (h₀.compatibleAt x)
          (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
          (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w ()) := by
  rw [h₀.cayleySum_toLinearMap _ (K := fun q => J q (q.endCoord w).im) (fun q => hJ q _),
    Floer.cayley_pairOfPantsAlmostComplex]
  rfl

private theorem pantsEnd_eq (w : ℂ) (x : M) :
    pantsEnd h₀ J hJ w x = J₀.toEndomorphism x *
      (1 + J₀.cayleySum (pantsWeight w) (fun q => J q (q.endCoord w).im) x) *
      Ring.inverse (1 - J₀.cayleySum (pantsWeight w) (fun q => J q (q.endCoord w).im) x) :=
  h₀.toContinuousLinearMap_eq_of_cayley_eq
    (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ())
    (pantsCayley_toLinearMap h₀ J hJ w x)

variable (hJp : ∀ q, Function.Periodic (J q) 1)
  (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
    (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
      p.2 ((J q p.1).toEndomorphism p.2)))

include hJp hJs in
private theorem contMDiffAt_pantsEnd (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : ℂ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (pantsEnd h₀ J hJ p.1 p.2)) ((w : ℂ), x) := by
  have hS := ne_endCenter w.2
  refine (h₀.contMDiffAt_mul_one_add_cayleySum (c := fun q (w : ℂ) => pantsWeight w q)
    (K := fun q (w : ℂ) => J q (q.endCoord w).im) (fun q => hJ q _) (fun q => ?_) (fun q => ?_)
    ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun p => ?_)
  · exact (smoothTransition.contDiff.contDiffAt.comp _
      ((contDiffAt_const.mul (q.contDiffAt_re_endCoord (hS q))).sub contDiffAt_const)).contMDiffAt
  · -- Each end family, read at the angular coordinate of its end, is smooth off the end center.
    exact q.contMDiffAt_comp_im_endCoord
      (f := fun t y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x) y ((J q t).toEndomorphism y))
      (fun t => by simp only [hJp q t]) (hJs q) (hS q) x
  · exact h₀.isUnit_one_sub_of_toLinearMap_eq_cayley
      (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ())
      (pantsCayley_toLinearMap h₀ J hJ w x)
  · dsimp only
    rw [pantsEnd_eq h₀ J hJ]

/-- Extend three jointly smooth period-one tame end families to the tangent bundle over the
pair of pants, relative to a compatible base structure. -/
def pairOfPantsAlmostComplex (w : ThricePuncturedSphere) : SmoothAlmostComplexStructure I M where
  toEndomorphism := ⟨pantsEnd h₀ J hJ w, fun x =>
    (contMDiffAt_pantsEnd h₀ J hJ hJp hJs w x).comp x
      (contMDiffAt_const.prodMk contMDiffAt_id)⟩
  square_neg x := by
    ext v
    -- The endomorphism is the continuous version of the linear fiberwise complex structure.
    exact AlmostComplexStructure.apply_apply _ v

/-- The value on a tangent fiber is precisely the linear pair-of-pants construction there. -/
theorem almostComplexStructureAt_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) (x : M) :
    (h₀.pairOfPantsAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x =
      Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (h₀.compatibleAt x)
        (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
        (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w () := by
  apply AlmostComplexStructure.toLinearMap_injective
  rw [SmoothAlmostComplexStructure.almostComplexStructureAt_toLinearMap]
  unfold pairOfPantsAlmostComplex
  -- The section coercion is its underlying function, evaluated at `x`.
  erw [ContMDiffSection.coeFn_mk]
  simp only [pantsEnd, LinearMap.coe_toContinuousLinearMap]

/-- The extension is tamed by the given two-form. -/
theorem tames_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) :
    σ.Tames (h₀.pairOfPantsAlmostComplex J hJ hJp hJs w) := by
  apply h₀.isNondegenerate.tames_iff.mpr
  intro x
  rw [almostComplexStructureAt_pairOfPantsAlmostComplex]
  exact Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ()

/-- Compatible end families extend through compatible structures. -/
theorem compatible_pairOfPantsAlmostComplex (hJc : ∀ q t, σ.Compatible (J q t))
    (w : ThricePuncturedSphere) :
    σ.Compatible (h₀.pairOfPantsAlmostComplex J hJ hJp hJs w) := by
  apply h₀.isNondegenerate.compatible_iff.mpr
  intro x
  rw [almostComplexStructureAt_pairOfPantsAlmostComplex]
  exact Floer.compatible_pairOfPantsAlmostComplex (h₀.compatibleAt x)
    (fun q t _ => h₀.isNondegenerate.compatible_iff.mp (hJc q t) x) w ()

/-- The Cayley coordinate characterizes the extension on every tangent fiber. -/
@[simp]
theorem cayley_pairOfPantsAlmostComplex (w : ThricePuncturedSphere) (x : M) :
    (J₀.almostComplexStructureAt x).cayley
        ((h₀.pairOfPantsAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x) =
      ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
        (J₀.almostComplexStructureAt x).cayley
          ((J q (q.endCoord w).im).almostComplexStructureAt x) := by
  rw [almostComplexStructureAt_pairOfPantsAlmostComplex,
    Floer.cayley_pairOfPantsAlmostComplex]

/-- Far out on a cylindrical end, the extension is the prescribed end structure. -/
theorem pairOfPantsAlmostComplex_cylindricalEndLift (w : ThricePuncturedSphere)
    {q : Puncture} {z : ℂ} (hw : (w : ℂ) = q.cylindricalEndLift z)
    (hz : 2 ≤ q.endSign * z.re) :
    h₀.pairOfPantsAlmostComplex J hJ hJp hJs w = J q z.im :=
  SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => by
    have hp : Function.Periodic
        (fun t (_ : Unit) => (J q t).almostComplexStructureAt x) 1 := fun t => by
      simp only [hJp q t]
    rw [almostComplexStructureAt_pairOfPantsAlmostComplex, hw]
    exact Floer.pairOfPantsAlmostComplex_cylindricalEndLift (h₀.compatibleAt x) hp hz ()

/-- Where all the end cutoffs vanish, the extension is the base structure. -/
theorem pairOfPantsAlmostComplex_eq_base_of_forall_le_one (w : ThricePuncturedSphere)
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) :
    h₀.pairOfPantsAlmostComplex J hJ hJp hJs w = J₀ := by
  have hc (q : Puncture) : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (sub_nonpos.mpr (hw q))
  refine SmoothAlmostComplexStructure.ext_almostComplexStructureAt fun x => ?_
  apply (h₀.compatibleAt x).eq_of_cayley_eq
    (h₀.isNondegenerate.tames_iff.mp (tames_pairOfPantsAlmostComplex h₀ J hJ hJp hJs w) x)
    (h₀.compatibleAt x).tames
  rw [cayley_pairOfPantsAlmostComplex, AlmostComplexStructure.cayley_self]
  simp only [hc, zero_smul, Finset.sum_const_zero]

/-- The domain-dependent structures are jointly `C^n` along any `C^n` family of domain and
target points. The domain family must avoid the two deleted points. This formulation also
allows independent external manifold parameters. -/
theorem contMDiff_pairOfPantsAlmostComplex
    {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {I' : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
    {n : ℕ∞ω} [ENat.LEInfty n]
    {f : N → ℂ} {b : N → M} (hf : ContMDiff I' 𝓘(ℝ, ℂ) n f)
    (hb : ContMDiff I' I n b) (hS : ∀ p, f p ≠ 0 ∧ f p ≠ 1) :
    ContMDiff I' (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun p => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        (b p) ((h₀.pairOfPantsAlmostComplex J hJ hJp hJs ⟨f p, hS p⟩).toEndomorphism (b p))) := by
  intro p
  have hs := ((contMDiffAt_pantsEnd h₀ J hJ hJp hJs ⟨f p, hS p⟩ (b p)).of_le
    ENat.LEInfty.out).comp p
    (hf.contMDiffAt.prodMk hb.contMDiffAt)
  -- The bundled structure has the same underlying endomorphism section as the fiberwise
  -- construction used in the joint smoothness proof.
  convert hs using 1
  funext y
  unfold pairOfPantsAlmostComplex
  erw [ContMDiffSection.coeFn_mk]
  rfl

end TauCeti.SmoothTwoForm.Compatible
