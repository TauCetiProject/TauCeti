/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import TauCeti.Analysis.Normed.Interpolation.CompatibleCouple
import TauCeti.MeasureTheory.Function.AEEqFun
public import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The space `L¹ + L^∞`

Every `Lᵖ(μ; E)`, `1 ≤ p ≤ ∞`, consists of functions that are the sum of an integrable function and
an essentially bounded one: split `f` where `‖f‖` exceeds `‖f‖_p` and where it does not
(`MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le`). The space `L¹ + L^∞` of such sums is therefore a
common home for all the Lebesgue spaces of one measure space, and is where interpolation theory
places them (Bergh–Löfström, §2.3 and Chapter 5), so that `L^{p₀}` and `L^{p₁}` form a compatible
couple (`TauCeti.CompatibleCouple.lebesgue`).

It is realised as the sum space of the compatible couple `(L¹, L^∞)`
(`TauCeti.CompatibleCouple.l1Linfty`), whose ambient space is `α →ₘ[μ] E` with the indiscrete
topology (`TauCeti.L1AddLinfty.Ambient`): the quotient of the `ℓ¹` product `L¹ × L^∞` by the pairs
`(g, h)` with `g + h = 0` almost everywhere. That subspace is closed, because convergence in `L¹`
and in `L^∞` both imply convergence in measure, whose limits are unique almost everywhere
(`TauCeti.CompatibleCouple.isClosed_sumKer_l1Linfty`). The quotient is thus a normed space, with
norm `‖u‖ = inf {‖g‖₁ + ‖h‖_∞ | u = g + h}`, and a Banach space when `E` is complete; the general
`TauCeti.CompatibleCouple.SumSpace` API applies to it.

## Main declarations

* `TauCeti.CompatibleCouple.l1Linfty 𝕜 E μ`: the couple `(L¹, L^∞)` in `α →ₘ[μ] E`.
* `TauCeti.L1AddLinfty 𝕜 E μ`: the space `L¹ + L^∞`, the sum space of that couple.
* `TauCeti.L1AddLinfty.ofLp`: the continuous injective inclusion `Lᵖ → L¹ + L^∞`, of norm at most
  `2` (`TauCeti.L1AddLinfty.norm_ofLp_le`), equal to the inclusions of the couple for `p = 1` and
  `p = ∞` (`TauCeti.L1AddLinfty.ofLp_eq_fstToSum`, `TauCeti.L1AddLinfty.ofLp_eq_sndToSum`).
* `TauCeti.L1AddLinfty.toAEEqFun`: the almost-everywhere class of an element of `L¹ + L^∞`, in
  terms of which the decompositions `u = g + h` are characterised
  (`TauCeti.L1AddLinfty.fstToSum_add_sndToSum_eq_iff`), as are the functions representing an
  element of `L¹ + L^∞` (`TauCeti.L1AddLinfty.exists_toAEEqFun_ae_eq_iff`).

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.3 and §5.1.
-/

public noncomputable section

open MeasureTheory Filter Topology WithLp
open scoped ENNReal

namespace TauCeti

variable (𝕜 E : Type*) {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace L1AddLinfty

/-- The space `α →ₘ[μ] E` of almost-everywhere equivalence classes of strongly measurable
functions, with the indiscrete topology. It is the ambient space of the couple `(L¹, L^∞)`
(`TauCeti.CompatibleCouple.l1Linfty`): every linear map into it is continuous, and the closedness
of the kernel of addition, which this topology does not give, is proved directly
(`TauCeti.CompatibleCouple.isClosed_sumKer_l1Linfty`). -/
def Ambient : Type _ :=
  α →ₘ[μ] E

instance : AddCommGroup (Ambient E μ) :=
  inferInstanceAs (AddCommGroup (α →ₘ[μ] E))

instance : Module 𝕜 (Ambient E μ) :=
  inferInstanceAs (Module 𝕜 (α →ₘ[μ] E))

instance : TopologicalSpace (Ambient E μ) :=
  ⊤

instance : ContinuousAdd (Ambient E μ) :=
  ⟨continuous_top⟩

variable {E μ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The class of a function of `Lᵖ` in `TauCeti.L1AddLinfty.Ambient`. -/
def lpToAmbient : Lp E p μ →L[𝕜] Ambient E μ where
  toFun f := (f : α →ₘ[μ] E)
  map_add' _ _ := rfl
  -- The scalar action on `Lp E p μ` is the restriction of that on `α →ₘ[μ] E`.
  map_smul' _ _ := rfl
  cont := continuous_top

theorem lpToAmbient_eq_lpToAmbient_iff {f : Lp E p μ} {g : Lp E q μ} :
    lpToAmbient 𝕜 f = lpToAmbient 𝕜 g ↔ ⇑f =ᵐ[μ] ⇑g :=
  AEEqFun.ext_iff

theorem lpToAmbient_injective : Function.Injective (lpToAmbient 𝕜 : Lp E p μ → Ambient E μ) :=
  fun _ _ h => Lp.ext ((lpToAmbient_eq_lpToAmbient_iff 𝕜).1 h)

variable {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]

/-- The sum of the classes of `f` and `g` is the class of `h` exactly when `f + g = h` almost
everywhere. -/
theorem lpToAmbient_add_lpToAmbient_eq_iff {f : Lp E p μ} {g : Lp E q μ} {h : Lp E r μ} :
    lpToAmbient 𝕜 f + lpToAmbient 𝕜 g = lpToAmbient 𝕜 h ↔ ⇑f + ⇑g =ᵐ[μ] ⇑h :=
  AEEqFun.ext_iff.trans (AEEqFun.coeFn_add (f : α →ₘ[μ] E) g).congr_left

/-- Two sums of classes of `Lᵖ` functions agree exactly when the sums of the functions agree almost
everywhere. -/
theorem lpToAmbient_add_lpToAmbient_eq_add_iff {f₀ : Lp E p μ} {f₁ : Lp E q μ} {g₀ : Lp E r μ}
    {g₁ : Lp E s μ} :
    lpToAmbient 𝕜 f₀ + lpToAmbient 𝕜 f₁ = lpToAmbient 𝕜 g₀ + lpToAmbient 𝕜 g₁ ↔
      ⇑f₀ + ⇑f₁ =ᵐ[μ] ⇑g₀ + ⇑g₁ :=
  AEEqFun.add_eq_add_iff_ae_eq

end L1AddLinfty

namespace CompatibleCouple

/-- The couple `(L¹, L^∞)`, with both spaces embedded in the space of almost-everywhere
equivalence classes `TauCeti.L1AddLinfty.Ambient E μ`. Its sum is `L¹ + L^∞`
(`TauCeti.L1AddLinfty`). -/
def l1Linfty : CompatibleCouple 𝕜 (Lp E 1 μ) (Lp E ∞ μ) (L1AddLinfty.Ambient E μ) where
  embed₀ := L1AddLinfty.lpToAmbient 𝕜
  embed₁ := L1AddLinfty.lpToAmbient 𝕜
  embed₀_injective := L1AddLinfty.lpToAmbient_injective 𝕜
  embed₁_injective := L1AddLinfty.lpToAmbient_injective 𝕜

variable {𝕜 E μ}

@[simp]
theorem l1Linfty_embed₀ : (l1Linfty 𝕜 E μ).embed₀ = L1AddLinfty.lpToAmbient 𝕜 :=
  (rfl)

@[simp]
theorem l1Linfty_embed₁ : (l1Linfty 𝕜 E μ).embed₁ = L1AddLinfty.lpToAmbient 𝕜 :=
  (rfl)

variable (𝕜 E μ)

/-- The pairs `(g, h)` in `L¹ × L^∞` with `g + h = 0` almost everywhere form a closed subspace.
Convergence in `L¹` and in `L^∞` both imply convergence in measure, whose limits are unique. -/
instance isClosed_sumKer_l1Linfty :
    IsClosed ((l1Linfty 𝕜 E μ).sumKer : Set (WithLp 1 (Lp E 1 μ × Lp E ∞ μ))) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 hx
  have h₀ : TendstoInMeasure μ (fun n => ⇑(u n).fst) atTop x.fst :=
    tendstoInMeasure_of_tendsto_Lp (((fstL 1 𝕜 _ _).continuous.tendsto x).comp hux)
  have h₁ : TendstoInMeasure μ (fun n => ⇑(-(u n).snd)) atTop ⇑(-x.snd) :=
    tendstoInMeasure_of_tendsto_Lp
      ((((sndL 1 𝕜 _ _).continuous.tendsto x).comp hux).neg)
  have hu' (n : ℕ) : ⇑(-(u n).snd) =ᵐ[μ] ⇑(u n).fst := by
    have := hu n
    simp only [SetLike.mem_coe, mem_sumKer_iff, l1Linfty_embed₀, l1Linfty_embed₁] at this
    rw [← L1AddLinfty.lpToAmbient_eq_lpToAmbient_iff 𝕜, map_neg,
      ← eq_neg_of_add_eq_zero_left this]
  have hx' : ⇑x.fst =ᵐ[μ] ⇑(-x.snd) :=
    tendstoInMeasure_ae_unique h₀ (h₁.congr_left hu')
  simp only [SetLike.mem_coe, mem_sumKer_iff, l1Linfty_embed₀, l1Linfty_embed₁]
  rw [(L1AddLinfty.lpToAmbient_eq_lpToAmbient_iff 𝕜).2 hx', map_neg, neg_add_cancel]

end CompatibleCouple

/-- The space `L¹ + L^∞` of functions `g + h` with `g ∈ L¹` and `h ∈ L^∞`: the sum space of the
couple `(L¹, L^∞)` (`TauCeti.CompatibleCouple.l1Linfty`), normed by
`‖u‖ = inf {‖g‖₁ + ‖h‖_∞ | u = g + h}`, a Banach space when `E` is complete. Every `Lᵖ`,
`1 ≤ p ≤ ∞`, embeds continuously into it by `TauCeti.L1AddLinfty.ofLp`. -/
abbrev L1AddLinfty : Type _ :=
  (CompatibleCouple.l1Linfty 𝕜 E μ).SumSpace

namespace L1AddLinfty

open CompatibleCouple

variable {𝕜 E μ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The inclusion `Lᵖ → L¹ + L^∞` for `1 ≤ p ≤ ∞`: `f` is sent to `g + h` for any decomposition
`f = g + h` with `g ∈ L¹` and `h ∈ L^∞`. It is injective (`TauCeti.L1AddLinfty.ofLp_injective`)
of norm at most `2` (`TauCeti.L1AddLinfty.norm_ofLp_le`). -/
def ofLp : Lp E p μ →L[𝕜] L1AddLinfty 𝕜 E μ :=
  (l1Linfty 𝕜 E μ).toSum (lpToAmbient 𝕜 : Lp E p μ →L[𝕜] Ambient E μ) 2 fun f => by
    -- Split `f` where `‖f‖` exceeds `‖f‖_p` and where it does not.
    obtain ⟨g, h, hgh, hg, hh⟩ := Lp.exists_add_ae_eq_of_le_of_le f (Fact.out : 1 ≤ p) le_top
    refine ⟨(l1Linfty 𝕜 E μ).fstToSum g + (l1Linfty 𝕜 E μ).sndToSum h, ?_,
      (norm_fstToSum_add_sndToSum_le _ _ _).trans (by linarith)⟩
    simpa only [map_add, sumSpaceEmbed_fstToSum, sumSpaceEmbed_sndToSum, l1Linfty_embed₀,
      l1Linfty_embed₁, ContinuousLinearMap.coe_coe] using
      (lpToAmbient_add_lpToAmbient_eq_iff 𝕜).2 hgh

@[simp]
theorem sumSpaceEmbed_ofLp (f : Lp E p μ) :
    (l1Linfty 𝕜 E μ).sumSpaceEmbed (ofLp f) = lpToAmbient 𝕜 f :=
  sumSpaceEmbed_toSum _ _ _ _ f

theorem norm_ofLp_le (f : Lp E p μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ 2 * ‖f‖ :=
  norm_toSum_le _ _ _ _ f

theorem ofLp_eq_ofLp_iff {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp E p μ} {g : Lp E q μ} :
    (ofLp f : L1AddLinfty 𝕜 E μ) = ofLp g ↔ ⇑f =ᵐ[μ] ⇑g := by
  rw [← (l1Linfty 𝕜 E μ).sumSpaceEmbed_injective.eq_iff, sumSpaceEmbed_ofLp, sumSpaceEmbed_ofLp,
    lpToAmbient_eq_lpToAmbient_iff]

theorem ofLp_injective : Function.Injective (ofLp : Lp E p μ → L1AddLinfty 𝕜 E μ) :=
  toSum_injective _ _ _ _ (lpToAmbient_injective 𝕜)

/-- On `L¹`, the inclusion into `L¹ + L^∞` is the inclusion of the first space of the couple. -/
theorem ofLp_eq_fstToSum (f : Lp E 1 μ) :
    (ofLp f : L1AddLinfty 𝕜 E μ) = (l1Linfty 𝕜 E μ).fstToSum f :=
  sumSpace_ext _ (by simp)

/-- On `L^∞`, the inclusion into `L¹ + L^∞` is the inclusion of the second space of the couple. -/
theorem ofLp_eq_sndToSum (f : Lp E ∞ μ) :
    (ofLp f : L1AddLinfty 𝕜 E μ) = (l1Linfty 𝕜 E μ).sndToSum f :=
  sumSpace_ext _ (by simp)

theorem norm_ofLp_one_le (f : Lp E 1 μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ ‖f‖ := by
  rw [ofLp_eq_fstToSum]
  exact norm_fstToSum_le _ f

theorem norm_ofLp_top_le (f : Lp E ∞ μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ ‖f‖ := by
  rw [ofLp_eq_sndToSum]
  exact norm_sndToSum_le _ f

variable (𝕜) in
/-- The almost-everywhere class of a function of `L¹ + L^∞`: the embedding of the sum space into
the ambient space `α →ₘ[μ] E` of the couple `(L¹, L^∞)`. It is injective
(`TauCeti.L1AddLinfty.toAEEqFun_injective`) and sends `f ∈ Lᵖ` to its class
(`TauCeti.L1AddLinfty.toAEEqFun_ofLp`). -/
def toAEEqFun : L1AddLinfty 𝕜 E μ →ₗ[𝕜] α →ₘ[μ] E where
  -- `Ambient E μ` is by definition `α →ₘ[μ] E`, with the same additive group and module
  -- structures (only the topology differs), so the embedding is read in `α →ₘ[μ] E` as it is.
  toFun u := ((l1Linfty 𝕜 E μ).sumSpaceEmbed u : Ambient E μ)
  map_add' := map_add _
  map_smul' := map_smul _

theorem toAEEqFun_injective : Function.Injective (toAEEqFun 𝕜 : L1AddLinfty 𝕜 E μ → α →ₘ[μ] E) :=
  (l1Linfty 𝕜 E μ).sumSpaceEmbed_injective

@[simp]
theorem toAEEqFun_ofLp (f : Lp E p μ) : toAEEqFun 𝕜 (ofLp f : L1AddLinfty 𝕜 E μ) = f :=
  -- As in `toAEEqFun`, an element of `Ambient E μ` is read in `α →ₘ[μ] E` by definition.
  congrArg (fun v : Ambient E μ => (v : α →ₘ[μ] E)) (sumSpaceEmbed_ofLp f)

@[simp]
theorem toAEEqFun_fstToSum (g : Lp E 1 μ) : toAEEqFun 𝕜 ((l1Linfty 𝕜 E μ).fstToSum g) = g := by
  rw [← ofLp_eq_fstToSum, toAEEqFun_ofLp]

@[simp]
theorem toAEEqFun_sndToSum (h : Lp E ∞ μ) : toAEEqFun 𝕜 ((l1Linfty 𝕜 E μ).sndToSum h) = h := by
  rw [← ofLp_eq_sndToSum, toAEEqFun_ofLp]

/-- A pair `(g, h)` in `L¹ × L^∞` decomposes an element `u` of `L¹ + L^∞` exactly when `g + h` is
almost everywhere equal to `u`. -/
theorem fstToSum_add_sndToSum_eq_iff {g : Lp E 1 μ} {h : Lp E ∞ μ} {u : L1AddLinfty 𝕜 E μ} :
    (l1Linfty 𝕜 E μ).fstToSum g + (l1Linfty 𝕜 E μ).sndToSum h = u ↔
      ⇑g + ⇑h =ᵐ[μ] ⇑(toAEEqFun 𝕜 u) := by
  rw [← ofLp_eq_fstToSum, ← ofLp_eq_sndToSum, ← toAEEqFun_injective.eq_iff, map_add,
    toAEEqFun_ofLp, toAEEqFun_ofLp]
  exact AEEqFun.ext_iff.trans (AEEqFun.coeFn_add (g : α →ₘ[μ] E) h).congr_left

/-- A function represents an element of `L¹ + L^∞` exactly when it is almost everywhere the sum of
a function of `L¹` and a function of `L^∞`. -/
theorem exists_toAEEqFun_ae_eq_iff {f : α → E} :
    (∃ u : L1AddLinfty 𝕜 E μ, ⇑(toAEEqFun 𝕜 u) =ᵐ[μ] f) ↔
      ∃ (g : Lp E 1 μ) (h : Lp E ∞ μ), ⇑g + ⇑h =ᵐ[μ] f := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨g, h, hgh⟩ := (l1Linfty 𝕜 E μ).exists_fstToSum_add_sndToSum_eq u
    exact ⟨g, h, (fstToSum_add_sndToSum_eq_iff.1 hgh).trans hu⟩
  · rintro ⟨g, h, hgh⟩
    exact ⟨_, (fstToSum_add_sndToSum_eq_iff.1 rfl).symm.trans hgh⟩

end L1AddLinfty

end TauCeti
