/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.RealInterpolation
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Besov
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Density.Lp

/-!
# Real interpolation of the Bessel-potential spaces of a vector bundle

Let `A` be a square chart partition of a smooth real vector bundle `V → M`
(`TauCeti.SquareChartPartition`): finitely many charts `cᵢ` with frames `tᵢ` over their sources and
cutoffs `χᵢ` with `∑ᵢ χᵢ² = 1`. A real functional `T` on the bundle tests of `V`, for instance a
distributional section of a bundle whose dual density bundle is `V`, has localizations `χᵢ Tᵢⱼ`
(`TauCeti.SquareChartPartition.localization`), tempered distributions on the model space `E`. The
Bessel-potential space `H^{s,p}` of `A` (`TauCeti.SquareChartPartition.besselPotentialSpace`) and
its Besov space `B^s_{p,q}` (`TauCeti.SquareChartPartition.besovSpace`) consist of the tuples of
localizations lying in `H^{s,p}(E, ℂ)`, respectively `B^s_{p,q}(E, ℂ)`.

For real orders `s₀`, `s₁` and `1 ≤ p ≤ ∞`, the spaces `H^{s₀,p}` and `H^{s₁,p}` of `A` form a
compatible couple of real Banach spaces (`TauCeti.SquareChartPartition.besselPotentialCouple`),
both embedded in the tuples of tempered distributions on `E` by their localizations. This file
computes its real interpolation spaces, for `1 < p < ∞`, `1 ≤ q ≤ ∞`, `s₀ ≠ s₁` and `0 < θ < 1`:

`(H^{s₀,p}, H^{s₁,p})_{θ,q} = B^{s_θ}_{p,q}`, `s_θ = (1 - θ) s₀ + θ s₁`,

with equivalent norms (`TauCeti.SquareChartPartition.besselPotentialCoupleKMethodEquiv`). In
membership form: an element of `H^{s₀,p} + H^{s₁,p}` lies in `(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly
when the functional it represents is `B^{s_θ}_{p,q}` with respect to `A`
(`TauCeti.SquareChartPartition.mem_kMethod_besselPotentialCouple_iff`). For `p = 2` and `q = 2`
the Besov space `B^{s_θ}_{2,2}` of `A` is its Sobolev space `H^{s_θ}`
(`TauCeti.SquareChartPartition.besovSpaceEquivSobolevSpace`).

## The argument

This is the Euclidean identity
`TauCeti.CompatibleCouple.besselPotentialSpaceKMethodEquiv` (Bergh–Löfström, Theorem 6.4.5(4))
transported along the localizations, as in Triebel's construction of function spaces on manifolds.
Taking the `k`-th localization is a morphism from the bundle couple to the Euclidean couple
`(H^{s₀,p}(E, ℂ), H^{s₁,p}(E, ℂ))`, so the localizations of an element of the interpolation space
lie in the Euclidean interpolation space `B^{s_θ}_{p,q}(E, ℂ)`. Conversely, for `1 < p < ∞` the
reconstruction of an arbitrary tuple of `H^{s,p}(E, ℂ)` distributions is `H^{s,p}` with respect to
`A` (`TauCeti.SquareChartPartition.besselPotentialReconstruction`). Reconstructing the `k`-th
localization alone, then localizing again, is therefore a morphism of couples in the other
direction, and an element of the sum space is the sum over `k` of these reconstructions of its
localizations, since a functional is the reconstruction of its localizations. The real method is
an exact interpolation functor for such additive morphisms between couples over `ℝ` and over `ℂ`
(`TauCeti.CompatibleCouple.kMethodENorm_map_le`), which gives both inclusions.

## Main declarations

* `TauCeti.SquareChartPartition.besselPotentialCouple`: the couple `(H^{s₀,p}, H^{s₁,p})` of `A`.
* `TauCeti.SquareChartPartition.localization_reconstruction_sumSpaceEmbed_besselPotentialCouple`:
  the elements of its sum space are tuples of localizations of functionals on bundle tests.
* `TauCeti.SquareChartPartition.mem_kMethod_besselPotentialCouple_iff`: membership in
  `(H^{s₀,p}, H^{s₁,p})_{θ,q}` is `B^{s_θ}_{p,q}` regularity with respect to `A`.
* `TauCeti.SquareChartPartition.besselPotentialCoupleKMethodEquiv`: the isomorphism
  `(H^{s₀,p}, H^{s₁,p})_{θ,q} ≃L[ℝ] B^{s_θ}_{p,q}`, which does not change the represented
  functional (`TauCeti.SquareChartPartition.besovToDistribution_besselPotentialCoupleKMethodEquiv`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223, Springer,
  1976, Theorem 6.4.2 (interpolation of retracts) and Theorem 6.4.5(4).
* H. Triebel, *Theory of Function Spaces II*, Birkhäuser, 1992, Chapter 7 (function spaces on
  manifolds, defined through localization in charts, and their interpolation).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex TemperedDistribution
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM ENNReal
  BesselPotentialSpace

namespace TauCeti

namespace SquareChartPartition

attribute [local instance] ContMDiffSection.ChartTestData.memTrivializationAtlas

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]

variable (A : SquareChartPartition ι I F V)

/-! ### The couple `(H^{s₀,p}, H^{s₁,p})` -/

section Couple

variable (s₀ s₁ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The embedding of the Bessel-potential space `H^{s,p}` of `A` in the tuples of tempered
distributions on the model space, by the localizations of the represented functional. -/
private def besselPotentialEmbed (s : ℝ) :
    A.besselPotentialSpace s p →L[ℝ] (ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) :=
  (ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
      BesselPotentialSpace.toDistrCLM E ℂ s p ∘L
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ H^{s, p}(E, ℂ)) k).restrictScalars ℝ ∘L
    (A.besselPotentialSpace s p).subtypeL

private theorem besselPotentialEmbed_apply (s : ℝ) (u : A.besselPotentialSpace s p)
    (k : ι × Fin (Module.finrank ℝ F)) :
    A.besselPotentialEmbed p s u k = (u.val k).toDistr :=
  BesselPotentialSpace.toDistrCLM_apply _

private theorem besselPotentialEmbed_injective (s : ℝ) :
    Function.Injective (A.besselPotentialEmbed p s) := fun u u' h ↦
  Subtype.ext <| funext fun k ↦ BesselPotentialSpace.ext <| by
    simpa [besselPotentialEmbed_apply] using congrFun h k

/-- The **compatible couple `(H^{s₀,p}, H^{s₁,p})`** of the Bessel-potential spaces of the square
chart partition `A`, as real Banach spaces, both embedded in the tuples of tempered distributions
on the model space: an element is sent to its components, the localizations of the functional it
represents (`TauCeti.SquareChartPartition.besselPotentialCouple_embed₀_apply`). -/
def besselPotentialCouple :
    CompatibleCouple ℝ (A.besselPotentialSpace s₀ p) (A.besselPotentialSpace s₁ p)
      (ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) where
  embed₀ := A.besselPotentialEmbed p s₀
  embed₁ := A.besselPotentialEmbed p s₁
  embed₀_injective := A.besselPotentialEmbed_injective p s₀
  embed₁_injective := A.besselPotentialEmbed_injective p s₁

variable {s₀ s₁ p}

@[simp]
theorem besselPotentialCouple_embed₀_apply (u : A.besselPotentialSpace s₀ p)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialCouple s₀ s₁ p).embed₀ u k = (u.val k).toDistr :=
  A.besselPotentialEmbed_apply p s₀ u k

@[simp]
theorem besselPotentialCouple_embed₁_apply (u : A.besselPotentialSpace s₁ p)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialCouple s₀ s₁ p).embed₁ u k = (u.val k).toDistr :=
  A.besselPotentialEmbed_apply p s₁ u k

/-- The elements of the sum space `H^{s₀,p} + H^{s₁,p}` of `A` are tuples of localizations: the
tuple of tempered distributions of `u` is the tuple of localizations of its reconstruction. -/
theorem localization_reconstruction_sumSpaceEmbed_besselPotentialCouple
    (u : (A.besselPotentialCouple s₀ s₁ p).SumSpace) (k : ι × Fin (Module.finrank ℝ F)) :
    A.localization k.1 k.2 (A.reconstruction ((A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u)) =
      (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u k := by
  obtain ⟨x₀, x₁, rfl⟩ := (A.besselPotentialCouple s₀ s₁ p).exists_fstToSum_add_sndToSum_eq u
  have h₀ : (A.besselPotentialCouple s₀ s₁ p).embed₀ x₀ = fun l ↦ (x₀.val l).toDistr :=
    funext (A.besselPotentialCouple_embed₀_apply x₀)
  have h₁ : (A.besselPotentialCouple s₀ s₁ p).embed₁ x₁ = fun l ↦ (x₁.val l).toDistr :=
    funext (A.besselPotentialCouple_embed₁_apply x₁)
  simp only [map_add, CompatibleCouple.sumSpaceEmbed_fstToSum,
    CompatibleCouple.sumSpaceEmbed_sndToSum, Pi.add_apply, h₀, h₁]
  rw [(A.mem_besselPotentialSpace).1 x₀.property k, (A.mem_besselPotentialSpace).1 x₁.property k]

end Couple

/-! ### Localizations and reconstructions of single components -/

section Morphisms

variable {s₀ s₁ : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "𝓗" => CompatibleCouple.besselPotentialSpace E ℂ s₀ p s₁ p

/-- The `k`-th localization, from the sum space of the couple `(H^{s₀,p}, H^{s₁,p})` of `A` to the
sum space of the Euclidean couple `(H^{s₀,p}(E, ℂ), H^{s₁,p}(E, ℂ))`. -/
private def sumLocalization (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialCouple s₀ s₁ p).SumSpace →L[ℝ] (𝓗).SumSpace :=
  (A.besselPotentialCouple s₀ s₁ p).sumLift
    ((𝓗).fstToSum.restrictScalars ℝ ∘L
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ H^{s₀, p}(E, ℂ)) k ∘L
        (A.besselPotentialSpace s₀ p).subtypeL))
    ((𝓗).sndToSum.restrictScalars ℝ ∘L
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ H^{s₁, p}(E, ℂ)) k ∘L
        (A.besselPotentialSpace s₁ p).subtypeL))
    fun x ↦ (𝓗).sumSpace_ext <| by
      simpa using congrFun ((A.besselPotentialCouple s₀ s₁ p).embed₀_interFst x) k

private theorem sumLocalization_fstToSum (k : ι × Fin (Module.finrank ℝ F))
    (x : A.besselPotentialSpace s₀ p) :
    A.sumLocalization k ((A.besselPotentialCouple s₀ s₁ p).fstToSum x) = (𝓗).fstToSum (x.val k) :=
  CompatibleCouple.sumLift_fstToSum _ _ _ _ x

private theorem sumLocalization_sndToSum (k : ι × Fin (Module.finrank ℝ F))
    (x : A.besselPotentialSpace s₁ p) :
    A.sumLocalization k ((A.besselPotentialCouple s₀ s₁ p).sndToSum x) = (𝓗).sndToSum (x.val k) :=
  CompatibleCouple.sumLift_sndToSum _ _ _ _ x

private theorem sumSpaceEmbed_sumLocalization (k : ι × Fin (Module.finrank ℝ F))
    (u : (A.besselPotentialCouple s₀ s₁ p).SumSpace) :
    (𝓗).sumSpaceEmbed (A.sumLocalization k u) =
      (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u k := by
  obtain ⟨x₀, x₁, rfl⟩ := (A.besselPotentialCouple s₀ s₁ p).exists_fstToSum_add_sndToSum_eq u
  simp [sumLocalization_fstToSum, sumLocalization_sndToSum]

/-- The `k`-th localization does not increase the `K`-method norm. -/
private theorem kMethodENorm_sumLocalization_le (θ : ℝ) (q : ℝ≥0∞)
    (k : ι × Fin (Module.finrank ℝ F)) (u : (A.besselPotentialCouple s₀ s₁ p).SumSpace) :
    (𝓗).kMethodENorm θ q (A.sumLocalization k u) ≤
      (A.besselPotentialCouple s₀ s₁ p).kMethodENorm θ q u := by
  simpa using CompatibleCouple.kMethodENorm_map_le (A.sumLocalization k).toLinearMap.toAddMonoidHom
    (T₀ := fun x : A.besselPotentialSpace s₀ p ↦ x.val k)
    (T₁ := fun x : A.besselPotentialSpace s₁ p ↦ x.val k)
    (A.sumLocalization_fstToSum k) (A.sumLocalization_sndToSum k) one_pos one_pos
    (fun x ↦ by simpa using A.norm_besselPotentialSpace_val_apply_le x k)
    (fun x ↦ by simpa using A.norm_besselPotentialSpace_val_apply_le x k) (θ := θ) (q := q) u

variable (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))

/-- The tuple of localizations of the functional reconstructed from a single tempered distribution
`w` in the slot `k`. -/
private def singleReconstruction [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F)) :
    𝓢'(E, ℂ) →ₗ[ℝ] (ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) :=
  (LinearMap.pi fun l : ι × Fin (Module.finrank ℝ F) ↦ A.localization l.1 l.2) ∘ₗ
    A.reconstruction ∘ₗ LinearMap.single ℝ (fun _ ↦ 𝓢'(E, ℂ)) k

omit [MeasurableSpace E] [BorelSpace E] in
private theorem singleReconstruction_apply [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F))
    (w : 𝓢'(E, ℂ)) (l : ι × Fin (Module.finrank ℝ F)) :
    A.singleReconstruction k w l = A.localization l.1 l.2 (A.reconstruction (Pi.single k w)) :=
  (rfl)

include hp hp_top in
/-- The components of the element of `H^{s,p}` of `A` reconstructed from a single component
`x ∈ H^{s,p}(E, ℂ)` in the slot `k` are the localizations of the functional reconstructed from
`x` in that slot. -/
private theorem embed_besselPotentialReconstruction_single [DecidableEq ι] (s : ℝ)
    (k : ι × Fin (Module.finrank ℝ F)) (x : H^{s, p}(E, ℂ)) :
    A.besselPotentialEmbed p s (A.besselPotentialReconstruction s hp hp_top (Pi.single k x)) =
      A.singleReconstruction k x.toDistr := by
  ext1 l
  rw [besselPotentialEmbed_apply, singleReconstruction_apply,
    ← localization_besselPotentialToDistribution,
    besselPotentialToDistribution_besselPotentialReconstruction]
  congr 2
  ext1 m
  rcases eq_or_ne m k with rfl | hm
  · simp
  · simp [hm]

include hp hp_top in
/-- Every element `w` of the Euclidean sum space `H^{s₀,p}(E, ℂ) + H^{s₁,p}(E, ℂ)` has a
reconstruction in the sum space of `A` from the slot `k`, of norm at most `c ‖w‖`. -/
private theorem exists_sumSpaceEmbed_eq_singleReconstruction [DecidableEq ι]
    (k : ι × Fin (Module.finrank ℝ F)) (w : (𝓗).SumSpace) :
    ∃ u, (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u =
        A.singleReconstruction k ((𝓗).sumSpaceEmbed w) ∧
      ‖u‖ ≤ 2 * (‖A.besselPotentialReconstruction s₀ hp hp_top‖ +
        ‖A.besselPotentialReconstruction s₁ hp hp_top‖) * ‖w‖ := by
  set P₀ := A.besselPotentialReconstruction s₀ hp hp_top
  set P₁ := A.besselPotentialReconstruction s₁ hp hp_top
  rcases eq_or_ne w 0 with rfl | hw
  · exact ⟨(A.besselPotentialCouple s₀ s₁ p).fstToSum 0, by simp,
      ((A.besselPotentialCouple s₀ s₁ p).norm_fstToSum_le 0).trans (by simp)⟩
  obtain ⟨a, b, rfl, hab⟩ := (𝓗).norm_sumSpace_lt_iff.1
    (lt_two_mul_self (norm_pos_iff.2 hw) : ‖w‖ < 2 * ‖w‖)
  refine ⟨(A.besselPotentialCouple s₀ s₁ p).fstToSum (P₀ (Pi.single k a)) +
    (A.besselPotentialCouple s₀ s₁ p).sndToSum (P₁ (Pi.single k b)), ?_, ?_⟩
  · simp only [map_add, CompatibleCouple.sumSpaceEmbed_fstToSum,
      CompatibleCouple.sumSpaceEmbed_sndToSum, CompatibleCouple.besselPotentialSpace_embed₀_apply,
      CompatibleCouple.besselPotentialSpace_embed₁_apply]
    exact congrArg₂ (· + ·) (A.embed_besselPotentialReconstruction_single hp hp_top s₀ k a)
      (A.embed_besselPotentialReconstruction_single hp hp_top s₁ k b)
  · calc _ ≤ ‖P₀ (Pi.single k a)‖ + ‖P₁ (Pi.single k b)‖ :=
          (CompatibleCouple.norm_fstToSum_add_sndToSum_le _ _ _)
      _ ≤ ‖P₀‖ * ‖a‖ + ‖P₁‖ * ‖b‖ := by
          gcongr
          · exact (P₀.le_opNorm _).trans_eq (by rw [Pi.norm_single])
          · exact (P₁.le_opNorm _).trans_eq (by rw [Pi.norm_single])
      _ ≤ (‖P₀‖ + ‖P₁‖) * (‖a‖ + ‖b‖) := by
          have := norm_nonneg P₀
          have := norm_nonneg P₁
          have := norm_nonneg a
          have := norm_nonneg b
          nlinarith
      _ ≤ (‖P₀‖ + ‖P₁‖) * (2 * ‖(𝓗).fstToSum a + (𝓗).sndToSum b‖) := by gcongr
      _ = _ := by ring

/-- The reconstruction from the slot `k`, from the Euclidean sum space
`H^{s₀,p}(E, ℂ) + H^{s₁,p}(E, ℂ)` to the sum space of `A`: localizing the functional reconstructed
from a single tempered distribution in the slot `k`. -/
private def sumReconstruction [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F)) :
    (𝓗).SumSpace →L[ℝ] (A.besselPotentialCouple s₀ s₁ p).SumSpace :=
  (A.besselPotentialCouple s₀ s₁ p).toSum
    (A.singleReconstruction k ∘ₗ ((𝓗).sumSpaceEmbed.restrictScalars ℝ).toLinearMap) _
    (A.exists_sumSpaceEmbed_eq_singleReconstruction hp hp_top k)

private theorem sumSpaceEmbed_sumReconstruction [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F))
    (w : (𝓗).SumSpace) :
    (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed (A.sumReconstruction hp hp_top k w) =
      A.singleReconstruction k ((𝓗).sumSpaceEmbed w) :=
  CompatibleCouple.sumSpaceEmbed_toSum _ _ _ _ w

private theorem sumReconstruction_fstToSum [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F))
    (x : H^{s₀, p}(E, ℂ)) :
    A.sumReconstruction hp hp_top k ((𝓗).fstToSum x) =
      (A.besselPotentialCouple s₀ s₁ p).fstToSum
        (A.besselPotentialReconstruction s₀ hp hp_top (Pi.single k x)) :=
  (A.besselPotentialCouple s₀ s₁ p).sumSpace_ext <| by
    rw [sumSpaceEmbed_sumReconstruction, CompatibleCouple.sumSpaceEmbed_fstToSum,
      CompatibleCouple.sumSpaceEmbed_fstToSum, CompatibleCouple.besselPotentialSpace_embed₀_apply]
    exact (A.embed_besselPotentialReconstruction_single hp hp_top s₀ k x).symm

private theorem sumReconstruction_sndToSum [DecidableEq ι] (k : ι × Fin (Module.finrank ℝ F))
    (x : H^{s₁, p}(E, ℂ)) :
    A.sumReconstruction hp hp_top k ((𝓗).sndToSum x) =
      (A.besselPotentialCouple s₀ s₁ p).sndToSum
        (A.besselPotentialReconstruction s₁ hp hp_top (Pi.single k x)) :=
  (A.besselPotentialCouple s₀ s₁ p).sumSpace_ext <| by
    rw [sumSpaceEmbed_sumReconstruction, CompatibleCouple.sumSpaceEmbed_sndToSum,
      CompatibleCouple.sumSpaceEmbed_sndToSum, CompatibleCouple.besselPotentialSpace_embed₁_apply]
    exact (A.embed_besselPotentialReconstruction_single hp hp_top s₁ k x).symm

/-- The reconstruction from the slot `k` multiplies the `K`-method norm by a bounded factor. -/
private theorem exists_kMethodENorm_sumReconstruction_le [DecidableEq ι] (θ : ℝ) (q : ℝ≥0∞)
    (k : ι × Fin (Module.finrank ℝ F)) :
    ∃ c : ℝ, ∀ w, (A.besselPotentialCouple s₀ s₁ p).kMethodENorm θ q
      (A.sumReconstruction hp hp_top k w) ≤ ENNReal.ofReal c * (𝓗).kMethodENorm θ q w := by
  set P₀ := A.besselPotentialReconstruction s₀ hp hp_top
  set P₁ := A.besselPotentialReconstruction s₁ hp hp_top
  refine ⟨(‖P₀‖ + 1) ^ (1 - θ) * (‖P₁‖ + 1) ^ θ, fun w ↦ ?_⟩
  refine CompatibleCouple.kMethodENorm_map_le
    (A.sumReconstruction hp hp_top k).toLinearMap.toAddMonoidHom
    (T₀ := fun x ↦ P₀ (Pi.single k x)) (T₁ := fun x ↦ P₁ (Pi.single k x))
    (A.sumReconstruction_fstToSum hp hp_top k) (A.sumReconstruction_sndToSum hp hp_top k)
    (by positivity) (by positivity) (fun x ↦ ?_) (fun x ↦ ?_) w
  · exact (P₀.le_opNorm _).trans (by rw [Pi.norm_single]; gcongr; linarith)
  · exact (P₁.le_opNorm _).trans (by rw [Pi.norm_single]; gcongr; linarith)

/-- The sum over `k` of the reconstructions from the slots `k` of a tuple `w` of elements of the
Euclidean sum space is the tuple of localizations of the functional reconstructed from `w`. -/
private theorem sumSpaceEmbed_sum_sumReconstruction [DecidableEq ι]
    (w : ι × Fin (Module.finrank ℝ F) → (𝓗).SumSpace) :
    (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed (∑ k, A.sumReconstruction hp hp_top k (w k)) =
      fun l ↦ A.localization l.1 l.2 (A.reconstruction fun k ↦ (𝓗).sumSpaceEmbed (w k)) := by
  ext1 l
  simp only [map_sum, sumSpaceEmbed_sumReconstruction, Finset.sum_apply, singleReconstruction_apply]
  rw [← map_sum, ← map_sum, Finset.univ_sum_single]

/-- An element of the sum space of `A` is the sum of the reconstructions of its localizations. -/
private theorem sum_sumReconstruction_sumLocalization [DecidableEq ι]
    (u : (A.besselPotentialCouple s₀ s₁ p).SumSpace) :
    ∑ k, A.sumReconstruction hp hp_top k (A.sumLocalization k u) = u :=
  (A.besselPotentialCouple s₀ s₁ p).sumSpace_ext <| by
    simp only [sumSpaceEmbed_sum_sumReconstruction, sumSpaceEmbed_sumLocalization]
    exact funext (A.localization_reconstruction_sumSpaceEmbed_besselPotentialCouple u)

end Morphisms

/-! ### Real interpolation -/

section Interpolation

variable (φ : ContDiffBump (0 : E)) {s₀ s₁ θ : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Real interpolation of the Bessel-potential spaces of a vector bundle**, membership form.
Let `1 < p < ∞`, `1 ≤ q ≤ ∞`, `s₀ ≠ s₁` and `0 < θ < 1`. An element `u` of the sum space
`H^{s₀,p} + H^{s₁,p}` of the square chart partition `A` lies in the real interpolation space
`(H^{s₀,p}, H^{s₁,p})_{θ,q}` exactly when the functional it represents is `B^{s_θ}_{p,q}` with
respect to `A`, where `s_θ = (1 - θ) s₀ + θ s₁`. -/
theorem mem_kMethod_besselPotentialCouple_iff (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (hq : 1 ≤ q)
    {u : (A.besselPotentialCouple s₀ s₁ p).SumSpace} :
    u ∈ (A.besselPotentialCouple s₀ s₁ p).kMethod θ q ↔
      A.MemBesov φ ((1 - θ) * s₀ + θ * s₁) p q
        (A.reconstruction ((A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u)) := by
  classical
  have hloc (k : ι × Fin (Module.finrank ℝ F)) :
      A.sumLocalization k u ∈ (CompatibleCouple.besselPotentialSpace E ℂ s₀ p s₁ p).kMethod θ q ↔
        (A.localization k.1 k.2 (A.reconstruction
          ((A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u))).MemBesov φ
          ((1 - θ) * s₀ + θ * s₁) p q := by
    rw [CompatibleCouple.mem_kMethod_besselPotentialSpace_iff φ hs hθ hq,
      sumSpaceEmbed_sumLocalization,
      localization_reconstruction_sumSpaceEmbed_besselPotentialCouple]
  refine ⟨fun hu ↦ A.memBesov_iff.2 fun i j ↦ (hloc (i, j)).1 ?_, fun hu ↦ ?_⟩
  · exact CompatibleCouple.mem_kMethod_iff.2 <|
      (A.kMethodENorm_sumLocalization_le θ q (i, j) u).trans_lt
        (CompatibleCouple.mem_kMethod_iff.1 hu)
  · rw [← A.sum_sumReconstruction_sumLocalization hp hp_top u]
    refine Submodule.sum_mem _ fun k _ ↦ CompatibleCouple.mem_kMethod_iff.2 ?_
    obtain ⟨c, hc⟩ := A.exists_kMethodENorm_sumReconstruction_le hp hp_top θ q k
    exact (hc _).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (CompatibleCouple.mem_kMethod_iff.1 ((hloc k).2 (A.memBesov_iff.1 hu k.1 k.2))))

variable [Fact (1 ≤ q)]

/-- The `k`-th localization of the real interpolation space `(H^{s₀,p}, H^{s₁,p})_{θ,q}` of `A`,
with values in the Euclidean real interpolation space, as a contraction. -/
private def kMethodLocalization (k : ι × Fin (Module.finrank ℝ F)) :
    (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q →L[ℝ]
      (CompatibleCouple.besselPotentialSpace E ℂ s₀ p s₁ p).KMethodSpace θ q :=
  LinearMap.mkContinuous
    { toFun u := CompatibleCouple.KMethodSpace.mk (A.sumLocalization k
          (CompatibleCouple.KMethodSpace.toSumₗ u))
        (CompatibleCouple.mem_kMethod_iff.2 <| (A.kMethodENorm_sumLocalization_le θ q k _).trans_lt
          (CompatibleCouple.mem_kMethod_iff.1 (CompatibleCouple.KMethodSpace.toSumₗ_mem u)))
      map_add' u v := by ext1; simp
      map_smul' a u := by ext1; simp }
    1 fun u ↦ by
      rw [LinearMap.coe_mk, AddHom.coe_mk, one_mul, CompatibleCouple.KMethodSpace.norm_mk,
        CompatibleCouple.KMethodSpace.norm_def]
      exact ENNReal.toReal_mono
        (CompatibleCouple.mem_kMethod_iff.1 (CompatibleCouple.KMethodSpace.toSumₗ_mem u)).ne
        (A.kMethodENorm_sumLocalization_le θ q k _)

private theorem toDistr_besselPotentialSpaceKMethodEquiv_kMethodLocalization (hs : s₀ ≠ s₁)
    (hθ : θ ∈ Ioo 0 1) (k : ι × Fin (Module.finrank ℝ F))
    (u : (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q) :
    (CompatibleCouple.besselPotentialSpaceKMethodEquiv φ hs hθ
        (A.kMethodLocalization k u)).toDistr =
      (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed
        (CompatibleCouple.KMethodSpace.toSumₗ u) k := by
  simp [kMethodLocalization, sumSpaceEmbed_sumLocalization]

/-- The localizations of an element of `(H^{s₀,p}, H^{s₁,p})_{θ,q}`, as an element of the Besov
space `B^{s_θ}_{p,q}` of `A`. -/
private def kMethodToBesovSpace (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q →L[ℝ]
      A.besovSpace φ ((1 - θ) * s₀ + θ * s₁) p q :=
  (ContinuousLinearMap.pi fun k : ι × Fin (Module.finrank ℝ F) ↦
      ((CompatibleCouple.besselPotentialSpaceKMethodEquiv (E := E) (F := ℂ) (p := p) (q := q) φ hs
          hθ).toContinuousLinearMap.restrictScalars ℝ) ∘L
        A.kMethodLocalization k).codRestrict _ fun u ↦ (A.mem_besovSpace φ).2 fun k ↦ by
    simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_restrictScalars', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe,
      A.toDistr_besselPotentialSpaceKMethodEquiv_kMethodLocalization φ hs hθ]
    exact A.localization_reconstruction_sumSpaceEmbed_besselPotentialCouple _ k

private theorem toDistr_kMethodToBesovSpace_apply (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (u : (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q) (k : ι × Fin (Module.finrank ℝ F)) :
    ((A.kMethodToBesovSpace φ hs hθ u).val k).toDistr =
      (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed
        (CompatibleCouple.KMethodSpace.toSumₗ u) k := by
  simp [kMethodToBesovSpace, A.toDistr_besselPotentialSpaceKMethodEquiv_kMethodLocalization φ hs hθ]

private theorem kMethodToBesovSpace_injective (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    Function.Injective (A.kMethodToBesovSpace (p := p) (q := q) φ hs hθ) := fun u v h ↦
  CompatibleCouple.KMethodSpace.ext <| (A.besselPotentialCouple s₀ s₁ p).sumSpace_ext <|
    funext fun k ↦ by
      rw [← A.toDistr_kMethodToBesovSpace_apply φ hs hθ u k,
        ← A.toDistr_kMethodToBesovSpace_apply φ hs hθ v k, h]

private theorem kMethodToBesovSpace_surjective (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    Function.Surjective (A.kMethodToBesovSpace (p := p) (q := q) φ hs hθ) := by
  classical
  intro v
  choose w hw using fun k : ι × Fin (Module.finrank ℝ F) ↦
    CompatibleCouple.mem_range_sumSpaceEmbed_besselPotentialSpace (E := E) (F := ℂ) hs hθ
      (BesovSpace.memBesov_toDistr (v.val k))
  set u := ∑ k, A.sumReconstruction hp hp_top k (w k) with hu_def
  have hu : (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed u = fun k ↦ (v.val k).toDistr := by
    simp only [hu_def, sumSpaceEmbed_sum_sumReconstruction, hw]
    exact funext ((A.mem_besovSpace φ).1 v.property)
  have hmem : u ∈ (A.besselPotentialCouple s₀ s₁ p).kMethod θ q :=
    (A.mem_kMethod_besselPotentialCouple_iff φ hp hp_top hs hθ Fact.out).2 <| by
      rw [hu, ← besovToDistribution_apply]
      exact A.memBesov_besovToDistribution φ v
  refine ⟨CompatibleCouple.KMethodSpace.mk u hmem, Subtype.ext <| funext fun k ↦
    BesovSpace.ext ?_⟩
  rw [toDistr_kMethodToBesovSpace_apply, CompatibleCouple.KMethodSpace.toSumₗ_mk, hu]

/-- **Real interpolation of the Bessel-potential spaces of a vector bundle.** Let `1 < p < ∞`,
`1 ≤ q ≤ ∞`, `s₀ ≠ s₁` and `0 < θ < 1`. The real interpolation space `(H^{s₀,p}, H^{s₁,p})_{θ,q}`
of the Bessel-potential spaces of the square chart partition `A` is its Besov space
`B^{s_θ}_{p,q}`, `s_θ = (1 - θ) s₀ + θ s₁`, with equivalent norms. The isomorphism does not change
the represented functional
(`TauCeti.SquareChartPartition.besovToDistribution_besselPotentialCoupleKMethodEquiv`). -/
def besselPotentialCoupleKMethodEquiv (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) :
    (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q ≃L[ℝ]
      A.besovSpace φ ((1 - θ) * s₀ + θ * s₁) p q :=
  ContinuousLinearEquiv.ofBijective (A.kMethodToBesovSpace φ hs hθ)
    (LinearMap.ker_eq_bot.2 (A.kMethodToBesovSpace_injective φ hs hθ))
    (LinearMap.range_eq_top.2 (A.kMethodToBesovSpace_surjective φ hp hp_top hs hθ))

/-- The components of the image of `u` under `besselPotentialCoupleKMethodEquiv` are the
components of `u` in the tuples of tempered distributions. -/
@[simp]
theorem toDistr_besselPotentialCoupleKMethodEquiv_apply (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (u : (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q)
    (k : ι × Fin (Module.finrank ℝ F)) :
    ((A.besselPotentialCoupleKMethodEquiv φ hp hp_top hs hθ u).val k).toDistr =
      (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed
        (CompatibleCouple.KMethodSpace.toSumₗ u) k := by
  rw [besselPotentialCoupleKMethodEquiv, ContinuousLinearEquiv.coeFn_ofBijective]
  exact A.toDistr_kMethodToBesovSpace_apply φ hs hθ u k

/-- The element of `(H^{s₀,p}, H^{s₁,p})_{θ,q}` corresponding to `v ∈ B^{s_θ}_{p,q}` under
`besselPotentialCoupleKMethodEquiv` has the components of `v` in the tuples of tempered
distributions. -/
@[simp]
theorem sumSpaceEmbed_toSumₗ_besselPotentialCoupleKMethodEquiv_symm_apply (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1)
    (v : A.besovSpace φ ((1 - θ) * s₀ + θ * s₁) p q) :
    (A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed
        (CompatibleCouple.KMethodSpace.toSumₗ
          ((A.besselPotentialCoupleKMethodEquiv φ hp hp_top hs hθ).symm v)) =
      fun k ↦ (v.val k).toDistr := by
  ext1 k
  rw [← A.toDistr_besselPotentialCoupleKMethodEquiv_apply φ hp hp_top hs hθ,
    ContinuousLinearEquiv.apply_symm_apply]

/-- The isomorphism `besselPotentialCoupleKMethodEquiv` does not change the represented
functional. -/
@[simp]
theorem besovToDistribution_besselPotentialCoupleKMethodEquiv (hp : 1 < p) (hp_top : p ≠ (∞ : ℝ≥0∞))
    (hs : s₀ ≠ s₁) (hθ : θ ∈ Ioo 0 1) (u : (A.besselPotentialCouple s₀ s₁ p).KMethodSpace θ q) :
    A.besovToDistribution φ _ p q (A.besselPotentialCoupleKMethodEquiv φ hp hp_top hs hθ u) =
      A.reconstruction
        ((A.besselPotentialCouple s₀ s₁ p).sumSpaceEmbed
          (CompatibleCouple.KMethodSpace.toSumₗ u)) := by
  rw [besovToDistribution_apply]
  congr 1
  ext1 k
  exact A.toDistr_besselPotentialCoupleKMethodEquiv_apply φ hp hp_top hs hθ u k

end Interpolation

end SquareChartPartition

end TauCeti
