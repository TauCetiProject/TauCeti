/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.MeasureTheory.Function.PreciseRepresentative
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.WeakDeriv.Local
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding for local Sobolev maps on planar domains

Let `Ω ⊆ ℂ` be open, let `F` be a finite-dimensional real normed space and let `2 < p ≤ ∞`.
This file proves that a map `u ∈ W^{1,p}_loc(Ω, F)`, in the sense of `TauCeti.MemWkpLoc p Ω 1`,
has a representative that is continuous on `Ω` and Hölder continuous with exponent
`α = 1 - 2 / p` on compact subsets of `Ω`, with the local Morrey inequality

`‖u*(x) - u*(y)‖ ≤ C ‖Du‖_{Lᵖ(B(x, 2|x - y|))} |x - y|^α` whenever `closedBall x (2|x - y|) ⊆ Ω`.

The representative is the precise representative `u*` of `u`, the limit of its averages over
shrinking balls; it agrees with `u` almost everywhere on `Ω`. The constant `C` depends only on `p`
and `F`. At the endpoint `p = ∞` the exponent is `1` and `u*` is Lipschitz on compact subsets.

The order-one comparison with the library's `TauCeti.W1p` comes first: a real function lies in
`MemWkpLoc p Ω 1` exactly when its restriction to every relatively compact open `W` with closure in
`Ω` is represented by an element of `W1p volume W p`, and then the weak gradient of that element
is dual, through `InnerProductSpace.toDual`, to the weak derivative of the function. The scalar
Morrey inequality is the interior Morrey inequality
`TauCeti.W1p.exists_dist_preciseRepresentative_le` applied on such a `W`; the vector-valued
statement follows coordinatewise in a basis of `F`.

## Main declarations

* `TauCeti.W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn`: an `Lᵖ` function with an `Lᵖ`
  weak derivative is represented by an element of `W1p`.
* `TauCeti.MemWkpLoc.exists_w1p` and `TauCeti.memWkpLoc_one_iff_forall_w1p`: the order-one
  comparison with `W1p` for real functions.
* `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`: the precise representative is continuous
  on `Ω`.
* `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`: the local Morrey inequality.
* `TauCeti.MemWkpLoc.exists_holderOnWith_preciseRepresentative_of_isCompact`: Hölder continuity
  with exponent `1 - 2 / p` on compact subsets of `Ω`.
* `TauCeti.MemWkpLoc.exists_lipschitzOnWith_preciseRepresentative_of_isCompact`: the endpoint
  `p = ∞`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 (Morrey's embedding for local Sobolev spaces).
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

section W1p

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [OpensMeasurableSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **An `Lᵖ` function with an `Lᵖ` weak derivative is a Sobolev function.** If `u` and a weak
derivative `D` of `u` on `Ω` both lie in `Lᵖ(Ω)`, then `u` is represented by an element of
`W^{1,p}(Ω)` whose weak gradient is the field of vectors dual to `D`. -/
theorem W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn {u : E → ℝ} {D : E → E →L[ℝ] ℝ}
    (hu : MemLp u p (mu.restrict Omega)) (hD : MemLp D p (mu.restrict Omega))
    (h : HasWeakFDerivOn mu Omega u D) :
    ∃ v : W1p mu Omega p, W1p.value v =ᵐ[mu.restrict Omega] u ∧
      W1p.gradient v =ᵐ[mu.restrict Omega]
        fun x => (InnerProductSpace.toDual ℝ E).symm (D x) := by
  have hg : MemLp (fun x => (InnerProductSpace.toDual ℝ E).symm (D x)) p (mu.restrict Omega) :=
    hD.of_le ((InnerProductSpace.toDual ℝ E).symm.continuous.comp_aestronglyMeasurable
      hD.aestronglyMeasurable) (ae_of_all _ fun x => by simp)
  refine ⟨W1p.mk (hu.toLp u) (hg.toLp _)
    ((h.congr_ae hu.coeFn_toLp.symm).congr_ae_deriv ?_), ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp] with x hx
    ext w
    rw [hx, innerSL_apply_apply, InnerProductSpace.toDual_symm_apply]
  · rw [W1p.value_mk]
    exact hu.coeFn_toLp
  · rw [W1p.gradient_mk]
    exact hg.coeFn_toLp

end W1p

section Planar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {u : ℂ → F}

/-- Every weak derivative of a member of `MemWkpLoc p Ω 1` is locally `Lᵖ` on `Ω`, not only the
one supplied by the definition: weak derivatives are unique almost everywhere. -/
theorem MemWkpLoc.memLpLoc_of_hasWeakFDerivOn (hu : MemWkpLoc p Ω 1 u)
    {D : ℂ → ℂ →L[ℝ] F} (hD : HasWeakFDerivOn volume Ω u D) : MemLpLoc p Ω D := by
  obtain ⟨D', hD', hD'p⟩ := hu.exists_weakFDeriv_of_isOpen
  exact (memWkpLoc_zero_iff.1 hD'p).congr_ae (hD'.ae_eq hD)

/-- **Local Sobolev functions are Sobolev on relatively compact subdomains.** Let
`u ∈ MemWkpLoc p Ω 1` be real-valued, with weak derivative `D` on `Ω`. On every open `W` whose
closure is compact and contained in `Ω`, `u` is represented by an element of `W1p volume W p`
whose weak gradient is dual to `D`. -/
theorem MemWkpLoc.exists_w1p [Fact (1 ≤ p)] {u : ℂ → ℝ} (hu : MemWkpLoc p Ω 1 u)
    {D : ℂ → ℂ →L[ℝ] ℝ} (hD : HasWeakFDerivOn volume Ω u D) {W : Opens ℂ}
    (hWc : IsCompact (closure (W : Set ℂ))) (hWΩ : closure (W : Set ℂ) ⊆ Ω) :
    ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u ∧
      W1p.gradient v =ᵐ[volume.restrict W]
        fun z => (InnerProductSpace.toDual ℝ ℂ).symm (D z) := by
  have hmono : volume.restrict (W : Set ℂ) ≤ volume.restrict (closure (W : Set ℂ)) :=
    Measure.restrict_mono subset_closure le_rfl
  exact W1p.exists_value_gradient_ae_eq_of_hasWeakFDerivOn
    ((memLpLoc_iff.1 hu.memLpLoc _ hWΩ hWc).mono_measure hmono)
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hWΩ hWc).mono_measure hmono)
    (hD.mono (SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ)))

/-- Every compact subset of an open planar set lies in an open set whose closure is compact and
contained in the open set. -/
private theorem exists_opens_isCompact_closure {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ W : Opens ℂ, K ⊆ W ∧ IsCompact (closure (W : Set ℂ)) ∧ closure (W : Set ℂ) ⊆ Ω := by
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  exact ⟨⟨V, hVo⟩, hKV, hVc, hVΩ⟩

/-- **Comparison with `W1p` at order one.** A real function lies in `MemWkpLoc p Ω 1` exactly when
its restriction to every open `W` with compact closure contained in `Ω` is represented by an element
of `W1p volume W p`. The weak gradients then correspond to the weak derivative of `u` on `Ω`
through `InnerProductSpace.toDual`, by `TauCeti.MemWkpLoc.exists_w1p`. -/
theorem memWkpLoc_one_iff_forall_w1p [Fact (1 ≤ p)] {u : ℂ → ℝ} :
    MemWkpLoc p Ω 1 u ↔ ∀ W : Opens ℂ, IsCompact (closure (W : Set ℂ)) →
      closure (W : Set ℂ) ⊆ Ω → ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
  constructor
  · intro hu W hWc hWΩ
    obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
    obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
    exact ⟨v, hv⟩
  · intro h
    have hcover : ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∃ W : Opens ℂ, K ⊆ W ∧ W ≤ Ω ∧
        ∃ v : W1p volume W p, W1p.value v =ᵐ[volume.restrict W] u := by
      intro K hK hKΩ
      obtain ⟨W, hKW, hWc, hWΩ⟩ := exists_opens_isCompact_closure hK hKΩ
      exact ⟨W, hKW, SetLike.coe_subset_coe.1 (subset_closure.trans hWΩ), h W hWc hWΩ⟩
    obtain ⟨D, hD⟩ : ∃ D : ℂ → ℂ →L[ℝ] ℝ, HasWeakFDerivOn volume Ω u D := by
      refine exists_hasWeakFDerivOn_iff_locally.2 fun x hx => ?_
      obtain ⟨W, hxW, -, v, hv⟩ := hcover {x} isCompact_singleton (singleton_subset_iff.2 hx)
      exact ⟨W, hxW rfl, _, (W1p.hasWeakFDerivOn v).congr_ae hv⟩
    refine memWkpLoc_succ_iff_of_isOpen.2 ⟨memLpLoc_iff.2 fun K hKΩ hK => ?_, D, hD,
      memWkpLoc_zero_iff.2 (memLpLoc_iff.2 fun K hKΩ hK => ?_)⟩
    · obtain ⟨W, hKW, -, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set ℂ) :=
        Measure.restrict_mono hKW le_rfl
      exact ((Lp.memLp (W1p.value v)).mono_measure hmono).ae_eq (ae_mono hmono hv)
    · obtain ⟨W, hKW, hWΩ, v, hv⟩ := hcover K hK hKΩ
      have hmono : volume.restrict K ≤ volume.restrict (W : Set ℂ) :=
        Measure.restrict_mono hKW le_rfl
      have hae : (fun z => innerSL ℝ (W1p.gradient v z)) =ᵐ[volume.restrict W] D :=
        ((W1p.hasWeakFDerivOn v).congr_ae hv).ae_eq (hD.mono hWΩ)
      exact (((innerSL ℝ).comp_memLp' (Lp.memLp (W1p.gradient v))).mono_measure hmono).ae_eq
        (ae_mono hmono hae)

/-- A locally `Lᵖ` function with `1 ≤ p` agrees almost everywhere on `Ω` with its precise
representative. -/
theorem MemLpLoc.ae_eq_preciseRepresentative [CompleteSpace F] (hp : 1 ≤ p)
    (hu : MemLpLoc p Ω u) : u =ᵐ[volume.restrict Ω] preciseRepresentative volume u :=
  ae_eq_restrict_preciseRepresentative Ω.isOpen
    (hu.locallyIntegrableOn hp Ω.isOpen.isLocallyClosed)

/-- The dimension of `ℂ` over `ℝ`, as an extended real exponent, is `2`. -/
private theorem finrank_real_complex_lt (hp : 2 < p) : (finrank ℝ ℂ : ℝ≥0∞) < p := by
  rwa [Complex.finrank_real_complex, Nat.cast_ofNat]

/-- The real-valued case of `TauCeti.MemWkpLoc.continuousOn_preciseRepresentative`. -/
private theorem continuousOn_preciseRepresentative_real (hp : 2 < p) {u : ℂ → ℝ}
    (hu : MemWkpLoc p Ω 1 u) : ContinuousOn (preciseRepresentative volume u) Ω := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
  intro x hx
  obtain ⟨W, hxW, hWc, hWΩ⟩ :=
    exists_opens_isCompact_closure isCompact_singleton (singleton_subset_iff.2 hx)
  obtain ⟨v, hv, -⟩ := hu.exists_w1p hD hWc hWΩ
  have heq : EqOn (preciseRepresentative volume u) (preciseRepresentative volume (W1p.value v))
      W := fun z hz => (preciseRepresentative_congr_ae_nhds (W.isOpen.mem_nhds hz) hv).symm
  exact (((W1p.continuousOn_preciseRepresentative (finrank_real_complex_lt hp) v).congr
    heq).continuousAt (W.isOpen.mem_nhds (hxW rfl))).continuousWithinAt

/-- The real-valued case of `TauCeti.MemWkpLoc.exists_dist_preciseRepresentative_le`. -/
private theorem exists_dist_preciseRepresentative_le_real (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u : ℂ → ℝ} {D : ℂ → ℂ →L[ℝ] ℝ}, MemWkpLoc p Ω 1 u →
      HasWeakFDerivOn volume Ω u D → ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (preciseRepresentative volume u x) (preciseRepresentative volume u y) ≤
          C * (eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  have : Fact (1 ≤ p) := ⟨one_le_two.trans hp.le⟩
  obtain ⟨C, hC, hdist⟩ :=
    W1p.exists_dist_preciseRepresentative_le (mu := (volume : Measure ℂ))
      (finrank_real_complex_lt hp)
  refine ⟨C, hC, fun {Ω u D} hu hD x y hxy => ?_⟩
  obtain ⟨W, hBW, hWc, hWΩ⟩ := exists_opens_isCompact_closure (isCompact_closedBall _ _) hxy
  obtain ⟨v, hv, hgrad⟩ := hu.exists_w1p hD hWc hWΩ
  have hW : ∀ z ∈ closedBall x (2 * dist x y),
      preciseRepresentative volume (W1p.value v) z = preciseRepresentative volume u z :=
    fun z hz => preciseRepresentative_congr_ae_nhds (W.isOpen.mem_nhds (hBW hz)) hv
  have hy : y ∈ closedBall x (2 * dist x y) := by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)]
  have hnorm : eLpNorm (W1p.gradient v : ℂ → ℂ) p (volume.restrict (ball x (2 * dist x y))) =
      eLpNorm D p (volume.restrict (ball x (2 * dist x y))) := by
    have hBW' : volume.restrict (ball x (2 * dist x y)) ≤ volume.restrict (W : Set ℂ) :=
      Measure.restrict_mono (ball_subset_closedBall.trans hBW) le_rfl
    refine eLpNorm_congr_norm_ae ((Lp.aestronglyMeasurable _).mono_measure hBW')
      ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hxy
        (isCompact_closedBall _ _)).mono_measure
          (Measure.restrict_mono ball_subset_closedBall le_rfl)).aestronglyMeasurable ?_
    filter_upwards [ae_mono (Measure.restrict_mono (ball_subset_closedBall.trans hBW) le_rfl)
      hgrad] with z hz
    rw [hz, LinearIsometryEquiv.norm_map]
  have h := hdist v hBW
  rwa [hW x (mem_closedBall_self (by positivity)), hW y hy, hnorm, Complex.finrank_real_complex,
    Nat.cast_ofNat] at h

variable [FiniteDimensional ℝ F]

/-- In the basis `Module.finBasis ℝ F`, the precise representative of `u ∈ MemWkpLoc p Ω 1` is,
on `Ω`, the sum of the precise representatives of the coordinates of `u` times the basis vectors.
In particular it is continuous on `Ω`. -/
private theorem eqOn_preciseRepresentative_coord (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) :
    EqOn (preciseRepresentative volume u)
      (fun z => ∑ i, preciseRepresentative volume
        (fun w => ((Module.finBasis ℝ F).coord i).toContinuousLinearMap (u w)) z •
          Module.finBasis ℝ F i) Ω ∧
    ContinuousOn (fun z => ∑ i, preciseRepresentative volume
        (fun w => ((Module.finBasis ℝ F).coord i).toContinuousLinearMap (u w)) z •
          Module.finBasis ℝ F i) Ω := by
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hcont : ContinuousOn
      (fun z => ∑ i, preciseRepresentative volume (fun w => ℓ i (u w)) z • b i) Ω :=
    continuousOn_finsetSum _ fun i _ =>
      (continuousOn_preciseRepresentative_real hp (hu.clm_comp (ℓ i))).smul continuousOn_const
  refine ⟨eqOn_preciseRepresentative_of_continuousOn Ω.isOpen
    (hu.memLpLoc.locallyIntegrableOn hp1 Ω.isOpen.isLocallyClosed) ?_ hcont, hcont⟩
  have hcoord : ∀ i, (fun w => ℓ i (u w)) =ᵐ[volume.restrict Ω]
      preciseRepresentative volume (fun w => ℓ i (u w)) := fun i =>
    (hu.clm_comp (ℓ i)).memLpLoc.ae_eq_preciseRepresentative hp1
  filter_upwards [ae_all_iff.2 hcoord] with z hz
  conv_lhs => rw [← b.sum_repr (u z)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hz i]
  simp [ℓ]

/-- **Continuity of `W^{1,p}_loc` maps for `p > 2`.** The precise representative of
`u ∈ MemWkpLoc p Ω 1`, which agrees with `u` almost everywhere on `Ω`
(`TauCeti.MemLpLoc.ae_eq_preciseRepresentative`), is continuous on `Ω`. -/
theorem MemWkpLoc.continuousOn_preciseRepresentative (hp : 2 < p) (hu : MemWkpLoc p Ω 1 u) :
    ContinuousOn (preciseRepresentative volume u) Ω :=
  let h := eqOn_preciseRepresentative_coord hp hu
  h.2.congr h.1

/-- **The local Morrey inequality for `W^{1,p}_loc` maps.** Let `2 < p ≤ ∞` and `α = 1 - 2 / p`.
There is a constant `C > 0`, depending only on `p` and `F`, such that the following holds. Let
`u ∈ MemWkpLoc p Ω 1` with weak derivative `D` on `Ω`, and let `x, y` be points with
`closedBall x (2 |x - y|) ⊆ Ω`. Then the precise representative `u*` of `u` satisfies

`‖u*(x) - u*(y)‖ ≤ C ‖D‖_{Lᵖ(B(x, 2 |x - y|))} |x - y|^α`. -/
theorem MemWkpLoc.exists_dist_preciseRepresentative_le (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Opens ℂ} {u : ℂ → F} {D : ℂ → ℂ →L[ℝ] F}, MemWkpLoc p Ω 1 u →
      HasWeakFDerivOn volume Ω u D → ∀ {x y : ℂ}, closedBall x (2 * dist x y) ⊆ Ω →
        dist (preciseRepresentative volume u x) (preciseRepresentative volume u y) ≤
          C * (eLpNorm D p (volume.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ) := by
  obtain ⟨C₀, hC₀, h₀⟩ := exists_dist_preciseRepresentative_le_real hp
  set b := Module.finBasis ℝ F
  set ℓ : Fin (finrank ℝ F) → F →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  refine ⟨C₀ * (1 + ∑ i, ‖ℓ i‖ * ‖b i‖), by positivity, fun {Ω u D} hu hD x y hxy => ?_⟩
  set B := ball x (2 * dist x y)
  set N := (eLpNorm D p (volume.restrict B)).toReal
  set a : ℝ := dist x y ^ (((1 : ℝ≥0∞) - 2 / p).toNNReal : ℝ)
  have hBK : volume.restrict B ≤ volume.restrict (closedBall x (2 * dist x y)) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hDfin : eLpNorm D p (volume.restrict B) ≠ ∞ :=
    ((memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hxy
      (isCompact_closedBall _ _)).mono_measure hBK).eLpNorm_ne_top
  have hcoord : ∀ i, dist (preciseRepresentative volume (fun w => ℓ i (u w)) x)
      (preciseRepresentative volume (fun w => ℓ i (u w)) y) ≤ C₀ * (‖ℓ i‖ * N) * a := by
    intro i
    refine (h₀ (hu.clm_comp (ℓ i)) (hD.clm_comp (ℓ i)) hxy).trans ?_
    gcongr
    have hmeas : AEStronglyMeasurable (fun z => (ℓ i).comp (D z)) (volume.restrict B) :=
      ((memLpLoc_iff.1 ((hu.clm_comp (ℓ i)).memLpLoc_of_hasWeakFDerivOn (hD.clm_comp (ℓ i))) _ hxy
        (isCompact_closedBall _ _)).mono_measure hBK).aestronglyMeasurable
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas
      (ae_of_all _ fun z => (ℓ i).opNorm_comp_le (D z)) p
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDfin) hle).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hx : x ∈ (Ω : Set ℂ) := hxy (mem_closedBall_self (by positivity))
  have hy : y ∈ (Ω : Set ℂ) := hxy (by
    rw [mem_closedBall, dist_comm]
    linarith [dist_nonneg (x := x) (y := y)])
  have heq := (eqOn_preciseRepresentative_coord hp hu).1
  rw [heq hx, heq hy, dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ i, (preciseRepresentative volume (fun w => ℓ i (u w)) x • b i -
          preciseRepresentative volume (fun w => ℓ i (u w)) y • b i)‖
      ≤ ∑ i, ‖preciseRepresentative volume (fun w => ℓ i (u w)) x • b i -
          preciseRepresentative volume (fun w => ℓ i (u w)) y • b i‖ := norm_sum_le _ _
    _ = ∑ i, dist (preciseRepresentative volume (fun w => ℓ i (u w)) x)
          (preciseRepresentative volume (fun w => ℓ i (u w)) y) * ‖b i‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, norm_smul, Real.norm_eq_abs, Real.dist_eq]
    _ ≤ ∑ i, C₀ * (‖ℓ i‖ * N) * a * ‖b i‖ := by
        gcongr with i
        exact hcoord i
    _ = C₀ * (∑ i, ‖ℓ i‖ * ‖b i‖) * N * a := by
        rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ C₀ * (1 + ∑ i, ‖ℓ i‖ * ‖b i‖) * N * a := by
        gcongr
        linarith

/-- **Morrey's embedding for `W^{1,p}_loc` maps on compact sets.** If `2 < p ≤ ∞`, the precise
representative of `u ∈ MemWkpLoc p Ω 1` is Hölder continuous with exponent `1 - 2 / p` on every
compact subset of `Ω`. -/
theorem MemWkpLoc.exists_holderOnWith_preciseRepresentative_of_isCompact (hp : 2 < p)
    (hu : MemWkpLoc p Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - 2 / p).toNNReal
      (preciseRepresentative volume u) K := by
  set α := ((1 : ℝ≥0∞) - 2 / p).toNNReal
  set f := preciseRepresentative volume u
  obtain ⟨C, hC, hdist⟩ := MemWkpLoc.exists_dist_preciseRepresentative_le (F := F) hp
  obtain ⟨D, hD, -⟩ := hu.exists_weakFDeriv_of_isOpen
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hu.continuousOn_preciseRepresentative hp).mono hKΩ)
  have hRc : IsCompact (cthickening R K) := hK.cthickening
  have hDfin : eLpNorm D p (volume.restrict (cthickening R K)) ≠ ∞ :=
    (memLpLoc_iff.1 (hu.memLpLoc_of_hasWeakFDerivOn hD) _ hRK hRc).eLpNorm_ne_top
  set N := (eLpNorm D p (volume.restrict (cthickening R K))).toReal
  set L := max (C * N) (2 * M * (2 / R) ^ (α : ℝ))
  refine ⟨L.toNNReal, HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ ((mul_nonneg hC.le ENNReal.toReal_nonneg).trans (le_max_left _ _))]
  rcases le_or_gt (dist x y) (R / 2) with hd | hd
  · -- Nearby points: the local Morrey inequality on `closedBall x (2 |x - y|) ⊆ Ω`.
    have hsub : closedBall x (2 * dist x y) ⊆ cthickening R K :=
      (closedBall_subset_cthickening hx _).trans (cthickening_mono (by linarith) K)
    refine (hdist hu hD (hsub.trans hRK)).trans ?_
    gcongr
    refine le_trans ?_ (le_max_left _ _)
    exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hDfin (eLpNorm_mono_measure _
      (Measure.restrict_mono (ball_subset_closedBall.trans hsub) le_rfl))) hC.le
  · -- Distant points: `‖f x - f y‖ ≤ 2M ≤ 2M (2 |x - y| / R)^α`.
    have hone : 1 ≤ (2 / R * dist x y) ^ (α : ℝ) :=
      Real.one_le_rpow (by rw [div_mul_eq_mul_div, le_div_iff₀ hR]; linarith) α.coe_nonneg
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M * 1 := by linarith [hM x hx, hM y hy]
      _ ≤ 2 * M * (2 / R * dist x y) ^ (α : ℝ) := by
          gcongr
          linarith [(norm_nonneg (f x)).trans (hM x hx)]
      _ = 2 * M * (2 / R) ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
          rw [Real.mul_rpow (by positivity) dist_nonneg]
          ring
      _ ≤ L * dist x y ^ (α : ℝ) := by gcongr; exact le_max_right _ _

/-- **`W^{1,∞}_loc` maps are locally Lipschitz.** At the endpoint `p = ∞` the Morrey exponent
`1 - 2 / p` is `1`: the precise representative of `u ∈ MemWkpLoc ∞ Ω 1` is Lipschitz on every
compact subset of `Ω`. -/
theorem MemWkpLoc.exists_lipschitzOnWith_preciseRepresentative_of_isCompact
    (hu : MemWkpLoc ∞ Ω 1 u) {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ C : ℝ≥0, LipschitzOnWith C (preciseRepresentative volume u) K := by
  obtain ⟨C, hC⟩ :=
    hu.exists_holderOnWith_preciseRepresentative_of_isCompact ENNReal.ofNat_lt_top hK hKΩ
  simp only [ENNReal.div_top, tsub_zero, ENNReal.toNNReal_one] at hC
  exact ⟨C, holderOnWith_one.1 hC⟩

end Planar

end TauCeti
