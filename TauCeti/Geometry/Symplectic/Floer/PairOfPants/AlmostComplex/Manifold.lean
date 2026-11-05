/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Basic
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Pair-of-pants almost complex data on a manifold

Given a compatible base structure and three smooth period-one families of tame structures on
an actual tangent bundle, construct a smooth domain-dependent tame structure on the
thrice-punctured sphere. Compatible end data give compatible structures. On each sufficiently
far cylindrical tail the structure is exactly the prescribed end structure; off the cutoff
regions it is the base structure.

The construction applies the linear pair-of-pants construction in each tangent fiber.
Smoothness is checked in tangent trivializations, where conjugation preserves the Cayley
formula and its inverse, using the same conjugation method as
`TauCeti.SmoothTwoForm.Compatible.cayleyPath`. Thus no global trivialization or constant
target two-form is assumed.
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

/-- The continuous Cayley coordinate of the fiberwise construction. -/
private def pantsCayley (J₀ : SmoothAlmostComplexStructure I M) (w : ℂ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  ∑ q, smoothTransition (q.endSign * (q.endCoord w).re - 1) •
    cayleyFormula (J₀.toEndomorphism x) ((J q (q.endCoord w).im).toEndomorphism x)

private theorem pantsCayley_toLinearMap (w : ℂ) (x : M) :
    (pantsCayley J J₀ w x).toLinearMap =
      (J₀.almostComplexStructureAt x).cayley
        (Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (h₀.compatibleAt x)
          (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
          (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w ()) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  rw [Floer.cayley_pairOfPantsAlmostComplex, pantsCayley]
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul]
  congr 1
  funext q
  congr 1
  have h := (h₀.compatibleAt x).tames.toContinuousLinearMap_cayley
    (h₀.isNondegenerate.tames_iff.mp (hJ q (q.endCoord w).im) x)
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    ((J q (q.endCoord w).im).almostComplexStructureAt_toLinearMap x).symm
  exact (congrArg ContinuousLinearMap.toLinearMap h).symm

include hJ in
private theorem pantsCayley_mem (w : ℂ) (x : M) :
    (pantsCayley J J₀ w x).toLinearMap ∈
      (h₀.isNondegenerate.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x) := by
  rw [pantsCayley_toLinearMap h₀ J hJ]
  exact (h₀.compatibleAt x).cayley_mem_cayleyBall
    (Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ())

include h₀ hJ in
private theorem isUnit_one_sub_pantsCayley (w : ℂ) (x : M) :
    IsUnit (1 - pantsCayley J J₀ w x) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  exact SymplecticForm.isUnit_one_sub_of_toLinearMap_mem_cayleyBall
    (pantsCayley_mem h₀ J hJ w x)

private theorem pantsEnd_eq (w : ℂ) (x : M) :
    pantsEnd h₀ J hJ w x = J₀.toEndomorphism x * (1 + pantsCayley J J₀ w x) *
      Ring.inverse (1 - pantsCayley J J₀ w x) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  have hc := pantsCayley_mem h₀ J hJ w x
  have h := (h₀.compatibleAt x).cayleyEquiv_symm_apply_toContinuousLinearMap
    (V := TangentSpace I x) (pantsCayley J J₀ w x) hc
  let P := Floer.pairOfPantsAlmostComplex (V := TangentSpace I x) (h₀.compatibleAt x)
    (fun q t (_ : Unit) => (J q t).almostComplexStructureAt x)
    (fun q t _ => h₀.isNondegenerate.tames_iff.mp (hJ q t) x) w ()
  have hp : (h₀.isNondegenerate.symplecticFormAt x).Tames P :=
    Floer.tames_pairOfPantsAlmostComplex (h₀.compatibleAt x) w ()
  have heq : (h₀.compatibleAt x).cayleyEquiv.symm ⟨_, hc⟩ = ⟨P, hp⟩ := by
    apply ((h₀.compatibleAt x).cayleyEquiv.symm_apply_eq).mpr
    apply Subtype.ext
    rw [SymplecticForm.Compatible.cayleyEquiv_apply_coe]
    exact pantsCayley_toLinearMap h₀ J hJ w x
  rw [heq] at h
  have hbase : LinearMap.toContinuousLinearMap (J₀.almostComplexStructureAt x).toLinearMap =
      J₀.toEndomorphism x :=
    ContinuousLinearMap.coe_injective (J₀.almostComplexStructureAt_toLinearMap x)
  exact h.trans (congrArg
    (fun A : TangentSpace I x →L[ℝ] TangentSpace I x =>
      A * (1 + pantsCayley J J₀ w x) * Ring.inverse (1 - pantsCayley J J₀ w x)) hbase)

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
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_snd, ?_⟩
  let e := trivializationAt E (TangentSpace I) x
  let coord := fun (y : M) (A : TangentSpace I y →L[ℝ] TangentSpace I y) =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I) x y x y A
  have hconj {y : M} (hy : y ∈ e.baseSet) (A : TangentSpace I y →L[ℝ] TangentSpace I y) :
      coord y A = (e.continuousLinearEquivAt ℝ y hy).conjContinuousAlgEquiv A := by
    simp only [coord, e, ContinuousLinearMap.inCoordinates_eq hy hy,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply]
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  let A := fun p : ℂ × M => coord p.2 (J₀.toEndomorphism p.2)
  let B := fun q (p : ℂ × M) => coord p.2 ((J q (q.endCoord p.1).im).toEndomorphism p.2)
  have hJ₀ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞)
      (fun y => coord y (J₀.toEndomorphism y)) x :=
    ((contMDiffAt_hom_bundle _).mp (J₀.toEndomorphism.contMDiff x)).2
  have hA : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞) A ((w : ℂ), x) :=
    hJ₀.comp (f := Prod.snd) ((w : ℂ), x) contMDiffAt_snd
  have hB (q : Puncture) : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, E →L[ℝ] E)
      (⊤ : ℕ∞) (B q) ((w : ℂ), x) := by
    have hp : Function.Periodic (fun t y => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        y ((J q t).toEndomorphism y)) 1 := fun t => by simp only [hJp q t]
    exact ((contMDiffAt_hom_bundle _).mp
      (q.contMDiffAt_comp_im_endCoord hp (hJs q) (ne_endCenter w.2 q) x)).2
  let C := fun p : ℂ × M => ∑ q, smoothTransition (q.endSign * (q.endCoord p.1).re - 1) •
    cayleyFormula (A p) (B q p)
  -- In a fixed tangent trivialization, both Cayley denominators are units at the base point.
  have hC : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞) C ((w : ℂ), x) := by
    refine contMDiffAt_finsetSum fun q _ => ?_
    have hu : IsUnit (1 - A ((w : ℂ), x) * B q ((w : ℂ), x)) := by
      dsimp only [A, B]
      rw [hconj hx, hconj hx, ← map_mul,
        ← map_one (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv, ← map_sub]
      exact ((h₀.compatibleAt x).tames.isUnit_one_sub_mul_of_toLinearMap
        (h₀.isNondegenerate.tames_iff.mp (hJ q _) x)
        (J₀.almostComplexStructureAt_toLinearMap x).symm
        ((J q _).almostComplexStructureAt_toLinearMap x).symm).map _
    obtain ⟨u, hu⟩ := hu
    have hinv := contDiffAt_ringInverse (n := (⊤ : ℕ∞)) ℝ u
    rw [hu] at hinv
    have hi := hinv.comp_contMDiffAt (f := fun p => 1 - A p * B q p)
      (contMDiffAt_const.sub (hA.clm_comp (hB q)))
    have hformula : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞)
        (fun p => cayleyFormula (A p) (B q p)) ((w : ℂ), x) := by
      simp only [cayleyFormula_def]
      exact (((contMDiffAt_const.add (hA.clm_comp (hB q))).clm_comp hi).neg)
    exact (Floer.contMDiffAt_smoothTransition_endCoord q (ne_endCenter w.2 q) x).smul hformula
  have hcoordC {p : ℂ × M} (hp : p.2 ∈ e.baseSet) :
      coord p.2 (pantsCayley J J₀ p.1 p.2) = C p := by
    simp only [pantsCayley, hconj hp, map_sum, map_smul, map_cayleyFormula, C, A, B]
  have hu : IsUnit (1 - C ((w : ℂ), x)) := by
    rw [← hcoordC hx, hconj hx,
      ← map_one (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv, ← map_sub]
    exact (isUnit_one_sub_pantsCayley h₀ J hJ w x).map _
  obtain ⟨u, hu⟩ := hu
  have hinv := contDiffAt_ringInverse (n := (⊤ : ℕ∞)) ℝ u
  rw [hu] at hinv
  have hi := hinv.comp_contMDiffAt (f := fun p => 1 - C p) (contMDiffAt_const.sub hC)
  have hresult : ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞)
      (fun p => A p * (1 + C p) * Ring.inverse (1 - C p)) ((w : ℂ), x) :=
    (hA.clm_comp ((contMDiffAt_const (c := (1 : E →L[ℝ] E))).add hC)).clm_comp hi
  -- Conjugation commutes with the inverse Cayley expression on a neighborhood of `x`.
  refine hresult.congr_of_eventuallyEq ?_
  filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds hx] with p hp
  -- The hom-bundle smoothness criterion reads this fiber value in the fixed trivialization.
  change coord p.2 (pantsEnd h₀ J hJ p.1 p.2) = _
  rw [pantsEnd_eq h₀ J hJ, hconj hp, map_mul, map_mul, map_add, map_one,
    map_ringInverse, map_sub, map_one]
  simp only [← hconj hp, hcoordC hp, A]

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
    h₀.pairOfPantsAlmostComplex J hJ hJp hJs w = J q z.im := by
  ext x v
  have hp : Function.Periodic
      (fun t (_ : Unit) => (J q t).almostComplexStructureAt x) 1 := fun t => by
    simp only [hJp q t]
  have heq : (h₀.pairOfPantsAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x =
      (J q z.im).almostComplexStructureAt x := by
    rw [almostComplexStructureAt_pairOfPantsAlmostComplex, hw]
    exact Floer.pairOfPantsAlmostComplex_cylindricalEndLift (h₀.compatibleAt x) hp hz ()
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
    congrArg (fun A : AlmostComplexStructure (TangentSpace I x) => A v) heq

/-- Where all the end cutoffs vanish, the extension is the base structure. -/
theorem pairOfPantsAlmostComplex_eq_base_of_forall_le_one (w : ThricePuncturedSphere)
    (hw : ∀ q : Puncture, q.endSign * (q.endCoord w).re ≤ 1) :
    h₀.pairOfPantsAlmostComplex J hJ hJp hJs w = J₀ := by
  have hc (q : Puncture) : smoothTransition (q.endSign * (q.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (sub_nonpos.mpr (hw q))
  ext x v
  have heq : (h₀.pairOfPantsAlmostComplex J hJ hJp hJs w).almostComplexStructureAt x =
      J₀.almostComplexStructureAt x := by
    apply (h₀.compatibleAt x).eq_of_cayley_eq
      (h₀.isNondegenerate.tames_iff.mp (tames_pairOfPantsAlmostComplex h₀ J hJ hJp hJs w) x)
      (h₀.compatibleAt x).tames
    rw [cayley_pairOfPantsAlmostComplex, AlmostComplexStructure.cayley_self]
    simp only [hc, zero_smul, Finset.sum_const_zero]
  simpa only [SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using
    congrArg (fun A : AlmostComplexStructure (TangentSpace I x) => A v) heq

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
