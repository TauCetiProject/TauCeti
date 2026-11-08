/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Symplectic.Cayley.Smooth
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# Weighted sums of Cayley coordinates on a manifold

Let `σ` be a smooth two-form on a finite-dimensional manifold `M`, nondegenerate with a compatible
smooth almost complex structure `J₀`. For finitely many smooth structures `K i` and real weights
`c i`, `TauCeti.SmoothAlmostComplexStructure.cayleySum J₀ c K x` is the weighted sum
`∑ i, c i • cayley (K i x)` of the Cayley coordinates relative to `J₀ x`, as a continuous
endomorphism of `T_x M`. For `σ`-tame `K i` its underlying linear map is the weighted sum of the
linear Cayley coordinates (`TauCeti.SmoothTwoForm.Compatible.cayleySum_toLinearMap`).

When such a sum is the Cayley coordinate of a tame structure `A` on `T_x M`, the structure `A` is
the inverse Cayley expression `J₀ (1 + C) (1 - C)⁻¹`
(`TauCeti.SmoothTwoForm.Compatible.toContinuousLinearMap_eq_of_cayley_eq`). For weights and
structures depending smoothly on parameters, this expression is smooth jointly in the parameters
and the point of `M`, as a section of the tangent endomorphism bundle
(`TauCeti.SmoothTwoForm.Compatible.contMDiffAt_mul_one_add_cayleySum`). Smoothness is checked in
tangent trivializations, where conjugation preserves the Cayley formula and its inverse, as for
`TauCeti.SmoothTwoForm.Compatible.cayleyPath`. Thus no global trivialization or constant two-form
is assumed.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition,
  Section 2.5 (the Cayley chart).
-/

public noncomputable section

open Bundle Manifold Topology
open scoped ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {ι : Type*} [Fintype ι]

/-- The weighted sum `∑ i, c i • cayley (K i x)` of the Cayley coordinates of the structures `K i`
relative to `J₀`, on the tangent space at `x`, as a continuous endomorphism. -/
def SmoothAlmostComplexStructure.cayleySum (J₀ : SmoothAlmostComplexStructure I M) (c : ι → ℝ)
    (K : ι → SmoothAlmostComplexStructure I M) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  ∑ i, c i • cayleyFormula (J₀.toEndomorphism x) ((K i).toEndomorphism x)

namespace SmoothTwoForm.Compatible

variable {σ : SmoothTwoForm I M} {J₀ : SmoothAlmostComplexStructure I M}

/-- For tame structures, the weighted sum of continuous Cayley coordinates is the weighted sum of
the linear Cayley coordinates. -/
theorem cayleySum_toLinearMap (h₀ : σ.Compatible J₀) (c : ι → ℝ)
    {K : ι → SmoothAlmostComplexStructure I M} (hK : ∀ i, σ.Tames (K i)) (x : M) :
    (J₀.cayleySum c K x).toLinearMap =
      ∑ i, c i • (J₀.almostComplexStructureAt x).cayley ((K i).almostComplexStructureAt x) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  simp only [SmoothAlmostComplexStructure.cayleySum, ContinuousLinearMap.toLinearMap_sum,
    ContinuousLinearMap.toLinearMap_smul]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  have h := (h₀.compatibleAt x).tames.toContinuousLinearMap_cayley
    (h₀.isNondegenerate.tames_iff.mp (hK i) x)
    (J₀.almostComplexStructureAt_toLinearMap x).symm
    ((K i).almostComplexStructureAt_toLinearMap x).symm
  exact (congrArg ContinuousLinearMap.toLinearMap h).symm

/-- A continuous endomorphism of `T_x M` which is the Cayley coordinate of a tame structure has an
invertible Cayley denominator `1 - C`. -/
theorem isUnit_one_sub_of_toLinearMap_eq_cayley (h₀ : σ.Compatible J₀) {x : M}
    {A : AlmostComplexStructure (TangentSpace I x)}
    (hA : (h₀.isNondegenerate.symplecticFormAt x).Tames A)
    {C : TangentSpace I x →L[ℝ] TangentSpace I x}
    (hC : C.toLinearMap = (J₀.almostComplexStructureAt x).cayley A) :
    IsUnit (1 - C) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  exact SymplecticForm.isUnit_one_sub_of_toLinearMap_mem_cayleyBall
    (hC ▸ (h₀.compatibleAt x).cayley_mem_cayleyBall hA)

/-- A tame structure on `T_x M` whose Cayley coordinate relative to `J₀` is `C` is the inverse
Cayley expression `J₀ (1 + C) (1 - C)⁻¹`. -/
theorem toContinuousLinearMap_eq_of_cayley_eq (h₀ : σ.Compatible J₀) {x : M}
    {A : AlmostComplexStructure (TangentSpace I x)}
    (hA : (h₀.isNondegenerate.symplecticFormAt x).Tames A)
    {C : TangentSpace I x →L[ℝ] TangentSpace I x}
    (hC : C.toLinearMap = (J₀.almostComplexStructureAt x).cayley A) :
    LinearMap.toContinuousLinearMap A.toLinearMap =
      J₀.toEndomorphism x * (1 + C) * Ring.inverse (1 - C) := by
  let : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
  have hc : C.toLinearMap ∈
      (h₀.isNondegenerate.symplecticFormAt x).cayleyBall (J₀.almostComplexStructureAt x) :=
    hC ▸ (h₀.compatibleAt x).cayley_mem_cayleyBall hA
  have h := (h₀.compatibleAt x).cayleyEquiv_symm_apply_toContinuousLinearMap
    (V := TangentSpace I x) C hc
  have heq : (h₀.compatibleAt x).cayleyEquiv.symm ⟨_, hc⟩ = ⟨A, hA⟩ := by
    apply ((h₀.compatibleAt x).cayleyEquiv.symm_apply_eq).mpr
    apply Subtype.ext
    rw [SymplecticForm.Compatible.cayleyEquiv_apply_coe]
    exact hC
  rw [heq] at h
  exact h.trans (congrArg
    (fun B : TangentSpace I x →L[ℝ] TangentSpace I x => B * (1 + C) * Ring.inverse (1 - C))
    (J₀.toContinuousLinearMap_almostComplexStructureAt x))

/-- **Smoothness of the inverse Cayley expression.** Let the weights `c i` and the tame structures
`K i` depend smoothly on a parameter `p`. At a parameter `p₀` and a point `x` where `1 - C` is
invertible, the inverse Cayley expression `J₀ (1 + C) (1 - C)⁻¹` of the weighted sum
`C = J₀.cayleySum (c · p) (K · p)` is smooth jointly in the parameter and the point of `M`, as a
section of the tangent endomorphism bundle. -/
theorem contMDiffAt_mul_one_add_cayleySum (h₀ : σ.Compatible J₀)
    {F G P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
    {IP : ModelWithCorners ℝ F G} [TopologicalSpace P] [ChartedSpace G P]
    {c : ι → P → ℝ} {K : ι → P → SmoothAlmostComplexStructure I M} {p₀ : P} {x : M}
    (hK : ∀ i, σ.Tames (K i p₀)) (hc : ∀ i, ContMDiffAt IP 𝓘(ℝ) (⊤ : ℕ∞) (c i) p₀)
    (hKs : ∀ i, ContMDiffAt (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : P × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((K i p.1).toEndomorphism p.2)) (p₀, x))
    (hu : IsUnit (1 - J₀.cayleySum (c · p₀) (K · p₀) x)) :
    ContMDiffAt (IP.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (⊤ : ℕ∞)
      (fun p : P × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 (J₀.toEndomorphism p.2 * (1 + J₀.cayleySum (c · p.1) (K · p.1) p.2) *
          Ring.inverse (1 - J₀.cayleySum (c · p.1) (K · p.1) p.2))) (p₀, x) := by
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
  let A := fun p : P × M => coord p.2 (J₀.toEndomorphism p.2)
  let B := fun i (p : P × M) => coord p.2 ((K i p.1).toEndomorphism p.2)
  have hA : ContMDiffAt (IP.prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞) A (p₀, x) :=
    ((contMDiffAt_hom_bundle _).mp (J₀.toEndomorphism.contMDiff x)).2.comp (f := Prod.snd)
      (p₀, x) contMDiffAt_snd
  let C := fun p : P × M => ∑ i, c i p.1 • cayleyFormula (A p) (B i p)
  -- In a fixed tangent trivialization, every Cayley denominator is a unit at the base point.
  have hC : ContMDiffAt (IP.prod I) 𝓘(ℝ, E →L[ℝ] E) (⊤ : ℕ∞) C (p₀, x) := by
    refine contMDiffAt_finsetSum fun i _ => ?_
    have hu : IsUnit (1 - A (p₀, x) * B i (p₀, x)) := by
      dsimp only [A, B]
      rw [hconj hx, hconj hx, ← map_mul,
        ← map_one (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv, ← map_sub]
      exact ((h₀.compatibleAt x).tames.isUnit_one_sub_mul_of_toLinearMap
        (h₀.isNondegenerate.tames_iff.mp (hK i) x)
        (J₀.almostComplexStructureAt_toLinearMap x).symm
        ((K i p₀).almostComplexStructureAt_toLinearMap x).symm).map _
    exact ((hc i).comp (p₀, x) contMDiffAt_fst).smul
      (SymplecticForm.contMDiffAt_cayleyFormula_of_isUnit hA
        ((contMDiffAt_hom_bundle _).mp (hKs i)).2 hu)
  have hcoordC {p : P × M} (hp : p.2 ∈ e.baseSet) :
      coord p.2 (J₀.cayleySum (c · p.1) (K · p.1) p.2) = C p := by
    simp only [SmoothAlmostComplexStructure.cayleySum, hconj hp, map_sum, map_smul,
      map_cayleyFormula, C, A, B]
  have hu' : IsUnit (1 - C (p₀, x)) := by
    rw [← hcoordC hx, hconj hx,
      ← map_one (e.continuousLinearEquivAt ℝ x hx).conjContinuousAlgEquiv, ← map_sub]
    exact hu.map _
  have hresult := SymplecticForm.contMDiffAt_mul_one_add_ringInverse hA hC hu'
  -- Conjugation commutes with the inverse Cayley expression on a neighborhood of `x`.
  refine hresult.congr_of_eventuallyEq ?_
  filter_upwards [(e.open_baseSet.preimage continuous_snd).mem_nhds hx] with p hp
  -- The hom-bundle smoothness criterion reads this fiber value in the fixed trivialization.
  change coord p.2 (J₀.toEndomorphism p.2 * (1 + J₀.cayleySum (c · p.1) (K · p.1) p.2) *
    Ring.inverse (1 - J₀.cayleySum (c · p.1) (K · p.1) p.2)) = _
  rw [hconj hp, map_mul, map_mul, map_add, map_one, map_ringInverse, map_sub, map_one]
  simp only [← hconj hp, hcoordC hp, A]

end SmoothTwoForm.Compatible

end TauCeti
