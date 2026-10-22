/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Measure.FiniteProjection
public import TauCeti.NumberTheory.Padics.CongruenceQuotients
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.ContinuousMap.LocallyConstant
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Extend
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Integral measures from finite coordinates on the p-adic units

A compatible family of integral coefficients on the finite groups `(ℤ/p^nℤ)ˣ` defines
integration on locally constant tests by finite summation. Refinement independence makes this
well-defined, and its norm bound allows extension to all continuous tests. The resulting measure
has exactly the prescribed coordinates and is unique. This gives a finite-coordinate construction
of measures without using compactness of a space of measures.

The descent and density of cylinder functions are supplied by
`TauCeti.NumberTheory.Padics.CongruenceQuotients`. Finite coefficients form `Finsupp`-valued
coordinate families; reconstructed measures use Mathlib's `AbstractMeasure` carrier and the
existing `AbstractMeasure.finiteProjection`.

The reconstruction API is in `TauCeti`. In particular,
`TauCeti.finiteProjection_unitsToZModPow_ext μ ν h` proves uniqueness,
`TauCeti.mapDomain_finiteProjection_unitsToZModPow μ` supplies compatibility, and
`TauCeti.ofUnitCoordinates_finiteProjection μ` reconstructs a measure.
Use these qualified calls: measure field notation searches Mathlib's root `AbstractMeasure`
namespace and does not find these lemmas in `TauCeti`.

## References

J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
Definitions 3.7–3.8, Remarks 3.11–3.12 and Proposition 3.16 with its inverse construction.
-/

public noncomputable section

open ContinuousMap _root_.AbstractMeasure IsUltrametricDist
open scoped AbstractMeasure

namespace TauCeti

variable {p : ℕ} [Fact p.Prime]

/-- Measures on the p-adic units are determined by their finite unit coordinates. -/
theorem finiteProjection_unitsToZModPow_ext {R : Type*} [NormedCommRing R]
    (μ ν : D(ℤ_[p]ˣ, R))
    (h : ∀ n, finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n) :
      C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) μ =
      finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n) :
        C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) ν) : μ = ν := by
  apply _root_.AbstractMeasure.ext
  have heq : Set.EqOn μ ν {f : C(ℤ_[p]ˣ, R) |
      ∃ n, ∃ g : (ZMod (p ^ n))ˣ → R, g ∘ PadicInt.unitsToZModPow n = f} := by
    rintro f ⟨n, g, hg⟩
    have hf : f = (ContinuousMap.equivFnOfDiscrete.symm g).comp
        (↑(PadicInt.unitsToZModPow (p := p) n)) := by
      ext u
      exact congrFun hg u |>.symm
    rw [hf, apply_comp_eq_sum_finiteProjection, apply_comp_eq_sum_finiteProjection, h n]
  exact fun f ↦ congrFun (Continuous.ext_on (dense_setOf_comp_unitsToZModPow R)
    μ.continuous ν.continuous heq) f

variable (c : ∀ n : ℕ, (ZMod (p ^ n))ˣ →₀ ℤ_[p])
  (hc : ∀ (m n : ℕ) (h : m ≤ n),
    (c n).mapDomain (ZMod.unitsMap (pow_dvd_pow p h)) = c m)

include hc in
private theorem pairing_refinement {m n : ℕ} (h : m ≤ n)
    (g : (ZMod (p ^ m))ˣ → ℤ_[p]) :
    ∑ a, g a * c m a = ∑ b, g (ZMod.unitsMap (pow_dvd_pow p h) b) * c n b := by
  classical
  rw [← hc m n h, ← Finsupp.sum_fintype _ _ (fun _ ↦ mul_zero _),
    Finsupp.sum_mapDomain_index (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _),
    Finsupp.sum_fintype _ _ (fun _ ↦ mul_zero _)]

include hc in
private theorem pairing_eq {m n : ℕ}
    (g : (ZMod (p ^ m))ˣ → ℤ_[p]) (h : (ZMod (p ^ n))ˣ → ℤ_[p])
    (heq : g ∘ PadicInt.unitsToZModPow m = h ∘ PadicInt.unitsToZModPow n) :
    ∑ a, g a * c m a = ∑ b, h b * c n b := by
  rw [pairing_refinement c hc (Nat.le_max_left m n),
    pairing_refinement c hc (Nat.le_max_right m n)]
  apply Finset.sum_congr rfl
  intro a _
  obtain ⟨u, rfl⟩ := PadicInt.unitsToZModPow_surjective (max m n) a
  simp only [PadicInt.unitsMap_unitsToZModPow]
  exact congrArg (fun z ↦ z * c (max m n)
    (PadicInt.unitsToZModPow (max m n) u)) (congrFun heq u)

private def coordinateIntegralFun (f : LocallyConstant ℤ_[p]ˣ ℤ_[p]) : ℤ_[p] :=
  let n := f.isLocallyConstant.exists_comp_unitsToZModPow_eq.choose
  let g := f.isLocallyConstant.exists_comp_unitsToZModPow_eq.choose_spec.choose
  ∑ a, g a * c n a

include hc in
private theorem coordinateIntegralFun_eq_sum (f : LocallyConstant ℤ_[p]ˣ ℤ_[p])
    (n : ℕ) (g : (ZMod (p ^ n))ˣ → ℤ_[p])
    (hg : g ∘ PadicInt.unitsToZModPow n = f) :
    coordinateIntegralFun c f = ∑ a, g a * c n a := by
  apply pairing_eq c hc
  exact f.isLocallyConstant.exists_comp_unitsToZModPow_eq.choose_spec.choose_spec.trans hg.symm

/-- Integration of locally constant unit tests against compatible integral finite coefficients. -/
def unitCoordinateIntegral : LocallyConstant ℤ_[p]ˣ ℤ_[p] →ₗ[ℤ_[p]] ℤ_[p] where
  toFun := coordinateIntegralFun c
  map_add' f g := by
    obtain ⟨m, a, ha⟩ := f.isLocallyConstant.exists_comp_unitsToZModPow_eq
    obtain ⟨n, b, hb⟩ := g.isLocallyConstant.exists_comp_unitsToZModPow_eq
    obtain ⟨a', ha'⟩ := exists_comp_unitsToZModPow_eq_of_le (Nat.le_max_left m n) ⟨a, ha⟩
    obtain ⟨b', hb'⟩ := exists_comp_unitsToZModPow_eq_of_le (Nat.le_max_right m n) ⟨b, hb⟩
    rw [coordinateIntegralFun_eq_sum c hc f _ a' ha',
      coordinateIntegralFun_eq_sum c hc g _ b' hb',
      coordinateIntegralFun_eq_sum c hc (f + g) (max m n) (a' + b') (by
        exact funext fun u ↦ congrArg₂ (· + ·) (congrFun ha' u) (congrFun hb' u))]
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r f := by
    obtain ⟨n, g, hg⟩ := f.isLocallyConstant.exists_comp_unitsToZModPow_eq
    rw [coordinateIntegralFun_eq_sum c hc f n g hg,
      coordinateIntegralFun_eq_sum c hc (r • f) n (r • g) (by
        exact funext fun u ↦ congrArg (r • ·) (congrFun hg u))]
    simp [Finset.mul_sum, mul_assoc]

/-- Integration sends the zero locally constant test to zero. -/
theorem unitCoordinateIntegral_zero : unitCoordinateIntegral c hc 0 = 0 :=
  map_zero _

/-- Integration preserves addition of locally constant tests. -/
theorem unitCoordinateIntegral_add (f g : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    unitCoordinateIntegral c hc (f + g) =
      unitCoordinateIntegral c hc f + unitCoordinateIntegral c hc g :=
  map_add _ _ _

/-- Integration preserves scalar multiplication of locally constant tests. -/
theorem unitCoordinateIntegral_smul (a : ℤ_[p]) (f : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    unitCoordinateIntegral c hc (a • f) = a • unitCoordinateIntegral c hc f :=
  map_smul _ _ _

/-- Every finite-level presentation gives the same integral. -/
theorem unitCoordinateIntegral_eq_sum (f : LocallyConstant ℤ_[p]ˣ ℤ_[p])
    (n : ℕ) (g : (ZMod (p ^ n))ˣ → ℤ_[p])
    (hg : g ∘ PadicInt.unitsToZModPow n = f) :
    unitCoordinateIntegral c hc f = ∑ a, g a * c n a :=
  coordinateIntegralFun_eq_sum c hc f n g hg

/-- Integral coordinates make integration a contraction for the supremum norm on tests. -/
theorem unitCoordinateIntegral_norm_le (f : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    ‖unitCoordinateIntegral c hc f‖ ≤ ‖f.toContinuousMap‖ := by
  obtain ⟨n, g, hg⟩ := f.isLocallyConstant.exists_comp_unitsToZModPow_eq
  rw [unitCoordinateIntegral_eq_sum c hc f n g hg]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun a _ ↦ ?_
  obtain ⟨u, rfl⟩ := PadicInt.unitsToZModPow_surjective n a
  calc
    ‖g (PadicInt.unitsToZModPow n u) * c n (PadicInt.unitsToZModPow n u)‖ ≤
        ‖g (PadicInt.unitsToZModPow n u)‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one _)
    _ ≤ ‖f.toContinuousMap‖ := by
      have hgu : g (PadicInt.unitsToZModPow n u) = f u := congrFun hg u
      rw [hgu]
      exact f.toContinuousMap.norm_coe_le_norm u

private abbrev unitTests := (LocallyConstant.toContinuousMapLinearMap ℤ_[p]
  (X := ℤ_[p]ˣ) (Y := ℤ_[p])).range

private theorem dense_unitTests :
    DenseRange ((unitTests (p := p)).subtype : unitTests →ₗ[ℤ_[p]] C(ℤ_[p]ˣ, ℤ_[p])) := by
  apply denseRange_subtype_val.mpr
  apply (dense_setOf_comp_unitsToZModPow ℤ_[p]).mono
  rintro f ⟨n, g, hg⟩
  have hloc : IsLocallyConstant (f : ℤ_[p]ˣ → ℤ_[p]) := by
    rw [← hg]
    exact (IsLocallyConstant.of_discrete g).comp_continuous
      (PadicInt.unitsToZModPow n).continuous
  exact ⟨⟨f, hloc⟩, rfl⟩

private def integralOnUnitTests : unitTests (p := p) →L[ℤ_[p]] ℤ_[p] :=
  let e := LinearEquiv.ofInjective (LocallyConstant.toContinuousMapLinearMap ℤ_[p]
    (X := ℤ_[p]ˣ) (Y := ℤ_[p])) LocallyConstant.toContinuousMap_injective
  ((unitCoordinateIntegral c hc).comp e.symm.toLinearMap).mkContinuous 1 (by
    intro f
    -- Use the inverse equivalence's public evaluation lemma at the range-subtype boundary.
    have he : (e.symm f).toContinuousMap = f.val := by
      simpa only [LocallyConstant.toContinuousMapLinearMap_apply] using
        LinearEquiv.ofInjective_symm_apply (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) f
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, one_mul, he,
      Submodule.norm_coe] using unitCoordinateIntegral_norm_le c hc (e.symm f))

private theorem integralOnUnitTests_apply (f : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    integralOnUnitTests c hc ⟨f.toContinuousMap, ⟨f, rfl⟩⟩ = unitCoordinateIntegral c hc f := by
  let e := LinearEquiv.ofInjective (LocallyConstant.toContinuousMapLinearMap ℤ_[p]
    (X := ℤ_[p]ˣ) (Y := ℤ_[p])) LocallyConstant.toContinuousMap_injective
  -- Compare the underlying continuous maps using the public evaluation lemma;
  -- subtype extensionality discards the choice of range-membership witness.
  have he : (⟨f.toContinuousMap, ⟨f, rfl⟩⟩ : unitTests (p := p)) = e f := by
    apply Subtype.ext
    exact (LinearEquiv.ofInjective_apply (LocallyConstant.toContinuousMapLinearMap ℤ_[p]) f).symm
  simp only [integralOnUnitTests, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap]
  exact congrArg (unitCoordinateIntegral c hc) (he ▸ e.symm_apply_apply f)

/-- The unique measure with a given compatible family of integral unit coordinates.
It is the continuous extension of finite summation on locally constant tests. -/
def ofUnitCoordinates : D(ℤ_[p]ˣ, ℤ_[p]) :=
  toCLMEquiv.symm ((integralOnUnitTests c hc).extend (unitTests (p := p)).subtypeL)

/-- Reconstruction extends integration of locally constant tests. -/
@[simp]
theorem ofUnitCoordinates_apply_locallyConstant (f : LocallyConstant ℤ_[p]ˣ ℤ_[p]) :
    ofUnitCoordinates c hc f.toContinuousMap = unitCoordinateIntegral c hc f := by
  have he := (integralOnUnitTests c hc).extend_eq
    (e := (unitTests (p := p)).subtypeL) dense_unitTests
    isUniformEmbedding_subtype_val.isUniformInducing
    ⟨f.toContinuousMap, ⟨f, rfl⟩⟩
  rw [ofUnitCoordinates, coe_symm_toCLMEquiv]
  exact he.trans (integralOnUnitTests_apply c hc f)

/-- The reconstructed measure contracts the supremum norm of every continuous test. -/
theorem ofUnitCoordinates_norm_le (f : C(ℤ_[p]ˣ, ℤ_[p])) :
    ‖ofUnitCoordinates c hc f‖ ≤ ‖f‖ := by
  refine dense_unitTests.induction_on (p := fun f ↦ ‖ofUnitCoordinates c hc f‖ ≤ ‖f‖) f ?_ ?_
  · exact isClosed_le ((ofUnitCoordinates c hc).continuous.norm) continuous_norm
  · rintro ⟨f, g, rfl⟩
    simpa using unitCoordinateIntegral_norm_le c hc g

/-- Reconstruction recovers every prescribed finite coordinate. -/
@[simp]
theorem finiteProjection_ofUnitCoordinates (n : ℕ) :
    finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n) :
      C(ℤ_[p]ˣ, (ZMod (p ^ n))ˣ)) (ofUnitCoordinates c hc) = c n := by
  classical
  apply Finsupp.ext
  intro a
  let g : (ZMod (p ^ n))ˣ → ℤ_[p] := Pi.single a 1
  let f : LocallyConstant ℤ_[p]ˣ ℤ_[p] :=
    ⟨g ∘ PadicInt.unitsToZModPow n, (IsLocallyConstant.of_discrete g).comp_continuous
      (PadicInt.unitsToZModPow n).continuous⟩
  have hf : fiberIndicator (↑(PadicInt.unitsToZModPow (p := p) n)) a = f.toContinuousMap := by
    ext u
    simp [fiberIndicator_apply, f, g, Pi.single_apply]
  rw [finiteProjection_apply, hf, ofUnitCoordinates_apply_locallyConstant,
    unitCoordinateIntegral_eq_sum c hc f n g rfl]
  simp [g, Pi.single_apply]

include hc in
/-- Every compatible integral family is the family of coordinates of exactly one measure. -/
theorem existsUnique_finiteProjection_unitsToZModPow_eq :
    ∃! μ : D(ℤ_[p]ˣ, ℤ_[p]),
      ∀ n, finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)) μ = c n := by
  refine ⟨ofUnitCoordinates c hc, finiteProjection_ofUnitCoordinates c hc, fun μ hμ ↦ ?_⟩
  exact finiteProjection_unitsToZModPow_ext μ _ fun n ↦ (hμ n).trans
    (finiteProjection_ofUnitCoordinates c hc n).symm

/-- The total mass is the sole coefficient at depth zero. -/
@[simp]
theorem ofUnitCoordinates_apply_one : ofUnitCoordinates c hc 1 = c 0 1 := by
  have : Subsingleton (ZMod (p ^ 0)) := by
    simpa only [pow_zero] using (inferInstance : Subsingleton (ZMod 1))
  have h := sum_finiteProjection (↑(PadicInt.unitsToZModPow (p := p) 0) :
    C(ℤ_[p]ˣ, (ZMod (p ^ 0))ˣ))
    (ofUnitCoordinates c hc)
  rw [finiteProjection_ofUnitCoordinates] at h
  rw [Finsupp.sum_fintype _ _ (fun _ ↦ rfl)] at h
  simpa only [Fintype.sum_subsingleton _ (1 : (ZMod (p ^ 0))ˣ)] using h.symm

/-- The finite unit coordinates of a measure satisfy the transition compatibility. -/
theorem mapDomain_finiteProjection_unitsToZModPow {R : Type*} [TopologicalSpace R] [CommRing R]
    [IsTopologicalRing R] (μ : D(ℤ_[p]ˣ, R)) (m n : ℕ) (h : m ≤ n) :
    (finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)) μ).mapDomain
      (ZMod.unitsMap (pow_dvd_pow p h)) =
        finiteProjection (↑(PadicInt.unitsToZModPow (p := p) m)) μ := by
  let t : C((ZMod (p ^ n))ˣ, (ZMod (p ^ m))ˣ) :=
    ContinuousMap.equivFnOfDiscrete.symm (ZMod.unitsMap (pow_dvd_pow p h))
  have ht : t.comp (↑(PadicInt.unitsToZModPow (p := p) n)) =
      (↑(PadicInt.unitsToZModPow (p := p) m) : C(ℤ_[p]ˣ, (ZMod (p ^ m))ˣ)) := by
    apply ContinuousMap.ext
    intro u
    simp [t]
  simpa only [ht, t, ContinuousMap.equivFnOfDiscrete_symm_apply] using
    (finiteProjection_comp (↑(PadicInt.unitsToZModPow (p := p) n)) t μ).symm

/-- Reconstructing a measure from its own coordinates returns that measure. -/
@[simp]
theorem ofUnitCoordinates_finiteProjection (μ : D(ℤ_[p]ˣ, ℤ_[p])) :
    ofUnitCoordinates (fun n ↦ finiteProjection (↑(PadicInt.unitsToZModPow (p := p) n)) μ)
      (mapDomain_finiteProjection_unitsToZModPow μ) = μ := by
  apply finiteProjection_unitsToZModPow_ext
  intro n
  exact finiteProjection_ofUnitCoordinates _ _ n

/-- The zero coordinate family reconstructs the zero measure. -/
@[simp]
theorem ofUnitCoordinates_zero :
    ofUnitCoordinates (p := p) (fun _ ↦ 0) (by intros; simp) = 0 := by
  apply finiteProjection_unitsToZModPow_ext
  intro n
  simp

/-- Reconstruction preserves addition of compatible coordinate families. -/
@[simp]
theorem ofUnitCoordinates_add (d : ∀ n : ℕ, (ZMod (p ^ n))ˣ →₀ ℤ_[p])
    (hd : ∀ (m n : ℕ) (h : m ≤ n),
      (d n).mapDomain (ZMod.unitsMap (pow_dvd_pow p h)) = d m) :
    ofUnitCoordinates (fun n ↦ c n + d n) (by
      intro m n h; simp [Finsupp.mapDomain_add, hc m n h, hd m n h]) =
        ofUnitCoordinates c hc + ofUnitCoordinates d hd := by
  apply finiteProjection_unitsToZModPow_ext
  intro n
  simp

/-- A compatible family of atoms reconstructs the corresponding scalar Dirac measure. -/
@[simp]
theorem ofUnitCoordinates_single (u : ℤ_[p]ˣ) (a : ℤ_[p]) :
    ofUnitCoordinates (fun n ↦ Finsupp.single (PadicInt.unitsToZModPow n u) a)
      (by intros; simp) = a • dirac ℤ_[p] u := by
  apply finiteProjection_unitsToZModPow_ext
  intro n
  simp

example (u v : ℤ_[3]ˣ) :
    ofUnitCoordinates
      (fun n ↦ Finsupp.single (PadicInt.unitsToZModPow n u) 2 +
        Finsupp.single (PadicInt.unitsToZModPow n v) 3)
      (by intros; simp [Finsupp.mapDomain_add]) 1 = 5 := by
  rw [ofUnitCoordinates_apply_one]
  rw [PadicInt.unitsToZModPow_zero_apply, PadicInt.unitsToZModPow_zero_apply]
  norm_num

example (u : ℤ_[2]ˣ) :
    ofUnitCoordinates (fun n ↦ Finsupp.single (PadicInt.unitsToZModPow n u) 1)
      (by intros; simp) = dirac ℤ_[2] u := by
  simp

end TauCeti
