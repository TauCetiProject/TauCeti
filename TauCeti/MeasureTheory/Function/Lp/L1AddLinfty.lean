/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The space `L¹ + L^∞`

Every `Lᵖ(μ; E)`, `1 ≤ p ≤ ∞`, consists of functions that are the sum of an integrable function and
an essentially bounded one: split `f` where `‖f‖` exceeds `‖f‖_p` and where it does not
(`MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le`). The space `L¹ + L^∞` of such sums is therefore a
common home for all the Lebesgue spaces of one measure space, and is where interpolation theory
places them (Bergh–Löfström, §2.3 and Chapter 5), so that `L^{p₀}` and `L^{p₁}` form a compatible
couple (`TauCeti.CompatibleCouple.lebesgue`).

It is realised as the quotient of the `ℓ¹` product `L¹ × L^∞` by the pairs `(g, h)` with
`g + h = 0` almost everywhere. That subspace is closed, because convergence in `L¹` and in `L^∞`
both imply convergence in measure, whose limits are unique almost everywhere
(`TauCeti.isClosed_ker_l1AddLinftyMap`). The quotient is thus a normed space, with norm
`‖u‖ = inf {‖g‖₁ + ‖h‖_∞ | u = g + h}`, and a Banach space when `E` is complete.

## Main declarations

* `TauCeti.L1AddLinfty 𝕜 E μ`: the space `L¹ + L^∞`.
* `TauCeti.L1AddLinfty.mk`: the element `g + h` for `g ∈ L¹`, `h ∈ L^∞`, with
  `TauCeti.L1AddLinfty.mk_eq_mk_iff` and `TauCeti.L1AddLinfty.norm_lt_iff`.
* `TauCeti.L1AddLinfty.toAEEqFun`: the injective linear map to `α →ₘ[μ] E`, `g + h ↦ g + h`.
* `TauCeti.L1AddLinfty.ofLp`: the continuous injective inclusion `Lᵖ → L¹ + L^∞`, of norm at most
  `2` (`TauCeti.L1AddLinfty.norm_ofLp_le`) and at most `1` for `p = 1` and `p = ∞`.

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

/-- The addition map `(g, h) ↦ g + h` from the `ℓ¹` product `L¹ × L^∞` to the space
`α →ₘ[μ] E` of almost-everywhere equivalence classes of strongly measurable functions. -/
def l1AddLinftyMap : WithLp 1 (Lp E 1 μ × Lp E ∞ μ) →ₗ[𝕜] α →ₘ[μ] E where
  toFun x := (x.fst : α →ₘ[μ] E) + (x.snd : α →ₘ[μ] E)
  map_add' x y := by simp only [add_fst, add_snd, AddSubgroup.coe_add]; abel
  -- The scalar action on `Lp E p μ` is the restriction of that on `α →ₘ[μ] E`.
  map_smul' c x := by simp only [smul_fst, smul_snd, RingHom.id_apply, smul_add]; rfl

@[simp]
theorem l1AddLinftyMap_apply (x : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)) :
    l1AddLinftyMap 𝕜 E μ x = (x.fst : α →ₘ[μ] E) + (x.snd : α →ₘ[μ] E) :=
  (rfl)

/-- The pairs `(g, h)` in `L¹ × L^∞` with `g + h = 0` almost everywhere form a closed subspace.
Convergence in `L¹` and in `L^∞` both imply convergence in measure, whose limits are unique. -/
instance isClosed_ker_l1AddLinftyMap :
    IsClosed (LinearMap.ker (l1AddLinftyMap 𝕜 E μ) : Set (WithLp 1 (Lp E 1 μ × Lp E ∞ μ))) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 hx
  have h₀ : TendstoInMeasure μ (fun n => ⇑(u n).fst) atTop x.fst :=
    tendstoInMeasure_of_tendsto_Lp (((fstL 1 𝕜 _ _).continuous.tendsto x).comp hux)
  have h₁ : TendstoInMeasure μ (fun n => ⇑(-(u n).snd)) atTop ⇑(-x.snd) :=
    tendstoInMeasure_of_tendsto_Lp
      ((((sndL 1 𝕜 _ _).continuous.tendsto x).comp hux).neg)
  have hu' (n : ℕ) : ((u n).fst : α →ₘ[μ] E) = ((-(u n).snd : Lp E ∞ μ) : α →ₘ[μ] E) := by
    have := hu n
    simp only [SetLike.mem_coe, LinearMap.mem_ker, l1AddLinftyMap_apply] at this
    rw [AddSubgroup.coe_neg, eq_neg_iff_add_eq_zero, this]
  have hx' : ⇑x.fst =ᵐ[μ] ⇑(-x.snd) :=
    tendstoInMeasure_ae_unique h₀ (h₁.congr_left fun n => by rw [hu' n])
  simp only [SetLike.mem_coe, LinearMap.mem_ker, l1AddLinftyMap_apply]
  rw [AEEqFun.ext hx', AddSubgroup.coe_neg, neg_add_cancel]

/-- The space `L¹ + L^∞` of functions `g + h` with `g ∈ L¹` and `h ∈ L^∞`, normed by
`‖u‖ = inf {‖g‖₁ + ‖h‖_∞ | u = g + h}`. It is the quotient of the `ℓ¹` product `L¹ × L^∞` by the
closed subspace of pairs adding to zero almost everywhere, a Banach space when `E` is complete.
It embeds injectively into `α →ₘ[μ] E` by `TauCeti.L1AddLinfty.toAEEqFun`, and every `Lᵖ`,
`1 ≤ p ≤ ∞`, embeds continuously into it by `TauCeti.L1AddLinfty.ofLp`. -/
abbrev L1AddLinfty : Type _ :=
  WithLp 1 (Lp E 1 μ × Lp E ∞ μ) ⧸ LinearMap.ker (l1AddLinftyMap 𝕜 E μ)

namespace L1AddLinfty

variable {𝕜 E μ}

/-- The element `g + h` of `L¹ + L^∞`, for `g ∈ L¹` and `h ∈ L^∞`. -/
def mk : WithLp 1 (Lp E 1 μ × Lp E ∞ μ) →L[𝕜] L1AddLinfty 𝕜 E μ :=
  (LinearMap.ker (l1AddLinftyMap 𝕜 E μ)).mkQL

theorem mk_surjective : Function.Surjective (mk : _ → L1AddLinfty 𝕜 E μ) :=
  Submodule.mkQ_surjective _

theorem norm_mk_le (x : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)) :
    ‖(mk x : L1AddLinfty 𝕜 E μ)‖ ≤ ‖x.fst‖ + ‖x.snd‖ :=
  (Submodule.Quotient.norm_mk_le _ x).trans_eq (prod_norm_eq_of_L1 x)

/-- The injective map from `L¹ + L^∞` to almost-everywhere equivalence classes, `g + h ↦ g + h`. -/
def toAEEqFun : L1AddLinfty 𝕜 E μ →ₗ[𝕜] α →ₘ[μ] E :=
  (LinearMap.ker (l1AddLinftyMap 𝕜 E μ)).liftQ (l1AddLinftyMap 𝕜 E μ) le_rfl

@[simp]
theorem toAEEqFun_mk (x : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)) :
    toAEEqFun (mk x : L1AddLinfty 𝕜 E μ) = (x.fst : α →ₘ[μ] E) + (x.snd : α →ₘ[μ] E) :=
  (rfl)

theorem toAEEqFun_injective : Function.Injective (toAEEqFun : L1AddLinfty 𝕜 E μ → _) :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

@[ext]
theorem ext {u v : L1AddLinfty 𝕜 E μ} (h : toAEEqFun u = toAEEqFun v) : u = v :=
  toAEEqFun_injective h

theorem mk_eq_mk_iff {x y : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)} :
    (mk x : L1AddLinfty 𝕜 E μ) = mk y ↔ ⇑x.fst + ⇑x.snd =ᵐ[μ] ⇑y.fst + ⇑y.snd := by
  rw [← toAEEqFun_injective.eq_iff, toAEEqFun_mk, toAEEqFun_mk, AEEqFun.ext_iff]
  exact ⟨fun h => (AEEqFun.coeFn_add _ _).symm.trans (h.trans (AEEqFun.coeFn_add _ _)),
    fun h => (AEEqFun.coeFn_add _ _).trans (h.trans (AEEqFun.coeFn_add _ _).symm)⟩

theorem mk_eq_zero_iff {x : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)} :
    (mk x : L1AddLinfty 𝕜 E μ) = 0 ↔ ⇑x.fst + ⇑x.snd =ᵐ[μ] 0 := by
  have h0 : ⇑(0 : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)).fst +
      ⇑(0 : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)).snd =ᵐ[μ] 0 := by
    simp only [zero_fst, zero_snd]
    filter_upwards [Lp.coeFn_zero E 1 μ, Lp.coeFn_zero E ∞ μ] with a h₁ h₂
    rw [Pi.add_apply, h₁, h₂, Pi.zero_apply, add_zero]
  rw [← map_zero mk, mk_eq_mk_iff]
  exact ⟨fun h => h.trans h0, fun h => h.trans h0.symm⟩

/-- The norm of `L¹ + L^∞` is the infimum of `‖g‖₁ + ‖h‖_∞` over the decompositions `u = g + h`:
strict upper bounds. -/
theorem norm_lt_iff {u : L1AddLinfty 𝕜 E μ} {r : ℝ} :
    ‖u‖ < r ↔ ∃ x, mk x = u ∧ ‖x.fst‖ + ‖x.snd‖ < r := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, hx, hxr⟩ := QuotientAddGroup.norm_lt_iff.1 h
    exact ⟨x, hx, (prod_norm_eq_of_L1 x).symm.trans_lt hxr⟩
  · rintro ⟨x, rfl, h⟩
    exact (norm_mk_le x).trans_lt h

/-- The norm of `L¹ + L^∞` is the infimum of `‖g‖₁ + ‖h‖_∞` over the decompositions `u = g + h`:
lower bounds. -/
theorem le_norm_iff {u : L1AddLinfty 𝕜 E μ} {r : ℝ} :
    r ≤ ‖u‖ ↔ ∀ x, mk x = u → r ≤ ‖x.fst‖ + ‖x.snd‖ := by
  simp only [← not_lt, norm_lt_iff, not_exists, not_and]

section ofLp

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every `f ∈ Lᵖ` is the image of an element of `L¹ + L^∞` of norm at most `2 ‖f‖_p`. -/
private theorem exists_toAEEqFun_eq_and_norm_le (f : Lp E p μ) :
    ∃ u : L1AddLinfty 𝕜 E μ, toAEEqFun u = (f : α →ₘ[μ] E) ∧ ‖u‖ ≤ 2 * ‖f‖ := by
  obtain ⟨g, h, hgh, hg, hh⟩ := Lp.exists_add_ae_eq_of_le_of_le f (Fact.out : 1 ≤ p) le_top
  refine ⟨mk (toLp 1 (g, h)), ?_, (norm_mk_le _).trans ?_⟩
  · rw [toAEEqFun_mk, toLp_fst, toLp_snd]
    exact AEEqFun.ext ((AEEqFun.coeFn_add _ _).trans hgh)
  · rw [toLp_fst, toLp_snd]
    linarith

/-- The inclusion `Lᵖ → L¹ + L^∞` for `1 ≤ p ≤ ∞`: `f` is sent to `g + h` for any decomposition
`f = g + h` with `g ∈ L¹` and `h ∈ L^∞`. It is injective (`TauCeti.L1AddLinfty.ofLp_injective`)
of norm at most `2` (`TauCeti.L1AddLinfty.norm_ofLp_le`). -/
def ofLp : Lp E p μ →L[𝕜] L1AddLinfty 𝕜 E μ :=
  LinearMap.mkContinuous
    { toFun f := (exists_toAEEqFun_eq_and_norm_le f).choose
      map_add' f g := toAEEqFun_injective <| by
        rw [map_add, (exists_toAEEqFun_eq_and_norm_le (f + g)).choose_spec.1,
          (exists_toAEEqFun_eq_and_norm_le f).choose_spec.1,
          (exists_toAEEqFun_eq_and_norm_le g).choose_spec.1, AddSubgroup.coe_add]
      map_smul' c f := toAEEqFun_injective <| by
        rw [map_smul, (exists_toAEEqFun_eq_and_norm_le (c • f)).choose_spec.1,
          (exists_toAEEqFun_eq_and_norm_le f).choose_spec.1]
        -- The scalar action on `Lp E p μ` is the restriction of that on `α →ₘ[μ] E`.
        rfl }
    2 fun f => (exists_toAEEqFun_eq_and_norm_le f).choose_spec.2

@[simp]
theorem toAEEqFun_ofLp (f : Lp E p μ) :
    toAEEqFun (ofLp f : L1AddLinfty 𝕜 E μ) = (f : α →ₘ[μ] E) :=
  (exists_toAEEqFun_eq_and_norm_le f).choose_spec.1

theorem norm_ofLp_le (f : Lp E p μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ 2 * ‖f‖ :=
  (exists_toAEEqFun_eq_and_norm_le f).choose_spec.2

theorem ofLp_eq_ofLp_iff {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Lp E p μ} {g : Lp E q μ} :
    (ofLp f : L1AddLinfty 𝕜 E μ) = ofLp g ↔ ⇑f =ᵐ[μ] ⇑g := by
  rw [← toAEEqFun_injective.eq_iff, toAEEqFun_ofLp, toAEEqFun_ofLp, AEEqFun.ext_iff]

theorem ofLp_injective : Function.Injective (ofLp : Lp E p μ → L1AddLinfty 𝕜 E μ) :=
  fun _ _ h => Lp.ext (ofLp_eq_ofLp_iff.1 h)

/-- An element `g + h` of `L¹ + L^∞` is the sum of the images of `g` and `h`. -/
theorem mk_eq_ofLp_add_ofLp (x : WithLp 1 (Lp E 1 μ × Lp E ∞ μ)) :
    (mk x : L1AddLinfty 𝕜 E μ) = ofLp x.fst + ofLp x.snd :=
  toAEEqFun_injective <| by simp

theorem norm_ofLp_one_le (f : Lp E 1 μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ ‖f‖ := by
  simpa [mk_eq_ofLp_add_ofLp] using norm_mk_le (𝕜 := 𝕜) (toLp 1 (f, (0 : Lp E ∞ μ)))

theorem norm_ofLp_top_le (f : Lp E ∞ μ) : ‖(ofLp f : L1AddLinfty 𝕜 E μ)‖ ≤ ‖f‖ := by
  simpa [mk_eq_ofLp_add_ofLp] using norm_mk_le (𝕜 := 𝕜) (toLp 1 ((0 : Lp E 1 μ), f))

end ofLp

end L1AddLinfty

end TauCeti
