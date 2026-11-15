/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# Compatible couples of normed spaces

A *compatible couple* is a pair of normed spaces `X₀`, `X₁` together with continuous injective
linear maps into a common Hausdorff topological vector space `V`. It is the basic object of
interpolation theory: the intersection `X₀ ∩ X₁` and the sum `X₀ + X₁` are normed spaces, Banach
when `X₀` and `X₁` are, and the interpolation functors (the complex method and the real
`K`-method) produce spaces between them.

We realise both spaces without choosing a norm on `V`:

* the intersection `CompatibleCouple.inter` is the closed submodule of `X₀ × X₁` of pairs with
  equal images in `V`, normed by `max ‖x₀‖ ‖x₁‖`;
* the sum `CompatibleCouple.SumSpace` is the quotient of the `ℓ¹` product `WithLp 1 (X₀ × X₁)`
  by the closed kernel of `(x₀, x₁) ↦ x₀ + x₁`, so its norm is
  `‖u‖ = inf {‖x₀‖ + ‖x₁‖ | u = x₀ + x₁}`. It embeds injectively into `V` by
  `CompatibleCouple.sumSpaceEmbed`, with range `range embed₀ ⊔ range embed₁`.

## Main declarations

* `TauCeti.CompatibleCouple`: two continuous injective linear maps into a common space.
* `TauCeti.CompatibleCouple.inter`: the intersection, with its two norm-nonincreasing
  inclusions `interFst`, `interSnd`.
* `TauCeti.CompatibleCouple.SumSpace`: the sum, with its norm-nonincreasing inclusions
  `fstToSum`, `sndToSum` and the injective map `sumSpaceEmbed` into `V`.
* `TauCeti.CompatibleCouple.toSum`: the factorisation through the sum space of a linear map into
  `V` whose values have bounded preimages in the sum.
* `TauCeti.CompatibleCouple.sumLift`: the extension to the sum of continuous linear maps on `X₀`
  and `X₁` that agree on the intersection.
* `TauCeti.CompatibleCouple.norm_sumSpace_lt_iff`, `TauCeti.CompatibleCouple.le_norm_sumSpace_iff`:
  the infimum description of the sum norm.
* `TauCeti.CompatibleCouple.refl`: the couple `(X, X)`, for which both norms are the norm of `X`.
* `TauCeti.CompatibleCouple.swap`, `TauCeti.CompatibleCouple.sumSwap`: reversal of the endpoints
  and the canonical isometric identification of their sum spaces.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §2.3 (Lemma 2.3.1).
-/

public noncomputable section

open WithLp

namespace TauCeti

/-- A compatible couple: two topological modules `X₀`, `X₁` with continuous injective linear maps
into a common topological module `V`. In interpolation theory `X₀`, `X₁` are normed (usually
Banach) spaces and `V` is a Hausdorff topological vector space; these hypotheses are imposed by
the constructions below rather than by the structure. -/
@[ext]
structure CompatibleCouple (𝕜 : Type*) [Semiring 𝕜] (X₀ X₁ V : Type*)
    [AddCommMonoid X₀] [Module 𝕜 X₀] [TopologicalSpace X₀]
    [AddCommMonoid X₁] [Module 𝕜 X₁] [TopologicalSpace X₁]
    [AddCommMonoid V] [Module 𝕜 V] [TopologicalSpace V] where
  /-- The embedding of the first space into the ambient space. -/
  embed₀ : X₀ →L[𝕜] V
  /-- The embedding of the second space into the ambient space. -/
  embed₁ : X₁ →L[𝕜] V
  embed₀_injective : Function.Injective embed₀
  embed₁_injective : Function.Injective embed₁

namespace CompatibleCouple

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V]
  (C : CompatibleCouple 𝕜 X₀ X₁ V)

/-! ### The intersection -/

section Inter

/-- The intersection `X₀ ∩ X₁` of a compatible couple, realised as the submodule of `X₀ × X₁` of
pairs with the same image in the ambient space. With the product norm its norm is
`max ‖x₀‖ ‖x₁‖`. -/
def inter : Submodule 𝕜 (X₀ × X₁) :=
  LinearMap.eqLocus (C.embed₀.toLinearMap ∘ₗ LinearMap.fst 𝕜 X₀ X₁)
    (C.embed₁.toLinearMap ∘ₗ LinearMap.snd 𝕜 X₀ X₁)

@[simp]
theorem mem_inter_iff {x : X₀ × X₁} : x ∈ C.inter ↔ C.embed₀ x.1 = C.embed₁ x.2 :=
  Iff.rfl

/-- The norm of an element of the intersection is the larger of the norms of its two
components. -/
theorem norm_inter (x : C.inter) : ‖x‖ = max ‖(x : X₀ × X₁).1‖ ‖(x : X₀ × X₁).2‖ :=
  Prod.norm_def _

instance [T2Space V] : IsClosed (C.inter : Set (X₀ × X₁)) :=
  isClosed_eq (C.embed₀.continuous.comp continuous_fst) (C.embed₁.continuous.comp continuous_snd)

instance [T2Space V] [CompleteSpace X₀] [CompleteSpace X₁] : CompleteSpace C.inter :=
  IsClosed.completeSpace_coe

/-- The inclusion of the intersection into the first space. -/
def interFst : C.inter →L[𝕜] X₀ :=
  (ContinuousLinearMap.fst 𝕜 X₀ X₁).comp C.inter.subtypeL

/-- The inclusion of the intersection into the second space. -/
def interSnd : C.inter →L[𝕜] X₁ :=
  (ContinuousLinearMap.snd 𝕜 X₀ X₁).comp C.inter.subtypeL

@[simp]
theorem interFst_apply (x : C.inter) : C.interFst x = (x : X₀ × X₁).1 :=
  (rfl)

@[simp]
theorem interSnd_apply (x : C.inter) : C.interSnd x = (x : X₀ × X₁).2 :=
  (rfl)

theorem embed₀_interFst (x : C.inter) : C.embed₀ (C.interFst x) = C.embed₁ (C.interSnd x) :=
  C.mem_inter_iff.1 x.2

theorem interFst_injective : Function.Injective C.interFst := by
  rintro ⟨⟨a₀, a₁⟩, ha⟩ ⟨⟨b₀, b₁⟩, hb⟩ h
  simp only [interFst_apply] at h
  subst h
  simp only [mem_inter_iff] at ha hb
  have : a₁ = b₁ := C.embed₁_injective (ha.symm.trans hb)
  subst this
  rfl

theorem interSnd_injective : Function.Injective C.interSnd := by
  rintro ⟨⟨a₀, a₁⟩, ha⟩ ⟨⟨b₀, b₁⟩, hb⟩ h
  simp only [interSnd_apply] at h
  subst h
  simp only [mem_inter_iff] at ha hb
  have : a₀ = b₀ := C.embed₀_injective (ha.trans hb.symm)
  subst this
  rfl

theorem norm_interFst_le (x : C.inter) : ‖C.interFst x‖ ≤ ‖x‖ :=
  norm_fst_le (x : X₀ × X₁)

theorem norm_interSnd_le (x : C.inter) : ‖C.interSnd x‖ ≤ ‖x‖ :=
  norm_snd_le (x : X₀ × X₁)

/-- The intersection is the common part of the two ranges in the ambient space. -/
theorem range_embed₀_comp_interFst :
    (C.embed₀.comp C.interFst).range = C.embed₀.range ⊓ C.embed₁.range := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, (C.embed₀_interFst x).symm⟩⟩
  · rintro ⟨⟨x₀, rfl⟩, ⟨x₁, hx⟩⟩
    exact ⟨⟨(x₀, x₁), hx.symm⟩, rfl⟩

end Inter

/-! ### The sum -/

section Sum

variable [ContinuousAdd V]

/-- The addition map `(x₀, x₁) ↦ x₀ + x₁` from the `ℓ¹` product to the ambient space. -/
def sumMap : WithLp 1 (X₀ × X₁) →L[𝕜] V :=
  C.embed₀.comp (WithLp.fstL 1 𝕜 X₀ X₁) + C.embed₁.comp (WithLp.sndL 1 𝕜 X₀ X₁)

@[simp]
theorem sumMap_apply (x : WithLp 1 (X₀ × X₁)) : C.sumMap x = C.embed₀ x.fst + C.embed₁ x.snd :=
  (rfl)

/-- The pairs `(x₀, x₁)` with `x₀ + x₁ = 0` in the ambient space. -/
def sumKer : Submodule 𝕜 (WithLp 1 (X₀ × X₁)) :=
  C.sumMap.ker

@[simp]
theorem mem_sumKer_iff {x : WithLp 1 (X₀ × X₁)} :
    x ∈ C.sumKer ↔ C.embed₀ x.fst + C.embed₁ x.snd = 0 :=
  Iff.rfl

instance [T1Space V] : IsClosed (C.sumKer : Set (WithLp 1 (X₀ × X₁))) :=
  C.sumMap.isClosed_ker

/-- The sum `X₀ + X₁` of a compatible couple: the quotient of the `ℓ¹` product of `X₀` and `X₁`
by the pairs adding to zero. Its norm is `‖u‖ = inf {‖x₀‖ + ‖x₁‖ | u = x₀ + x₁}`
(`norm_sumSpace_lt_iff`, `le_norm_sumSpace_iff`). It is a normed space when `V` is `T₁` (for
instance Hausdorff), and complete when `X₀` and `X₁` are. -/
abbrev SumSpace : Type _ :=
  WithLp 1 (X₀ × X₁) ⧸ C.sumKer

/-- The element `x₀ + x₁` of the sum space. -/
def sumMk : WithLp 1 (X₀ × X₁) →L[𝕜] C.SumSpace :=
  C.sumKer.mkQL

theorem sumMk_surjective : Function.Surjective C.sumMk :=
  C.sumKer.mkQ_surjective

theorem norm_sumMk_le (x : WithLp 1 (X₀ × X₁)) : ‖C.sumMk x‖ ≤ ‖x.fst‖ + ‖x.snd‖ :=
  (Submodule.Quotient.norm_mk_le _ x).trans_eq (prod_norm_eq_of_L1 x)

/-- The inclusion of the first space into the sum. -/
def fstToSum : X₀ →L[𝕜] C.SumSpace :=
  C.sumMk.comp ((WithLp.prodContinuousLinearEquiv 1 𝕜 X₀ X₁).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl 𝕜 X₀ X₁))

/-- The inclusion of the second space into the sum. -/
def sndToSum : X₁ →L[𝕜] C.SumSpace :=
  C.sumMk.comp ((WithLp.prodContinuousLinearEquiv 1 𝕜 X₀ X₁).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr 𝕜 X₀ X₁))

theorem fstToSum_add_sndToSum (x₀ : X₀) (x₁ : X₁) :
    C.fstToSum x₀ + C.sndToSum x₁ = C.sumMk (toLp 1 (x₀, x₁)) := by
  simp [fstToSum, sndToSum, ← map_add, ← toLp_add]

theorem sumMk_apply (x : WithLp 1 (X₀ × X₁)) :
    C.sumMk x = C.fstToSum x.fst + C.sndToSum x.snd := by
  rcases x with ⟨x₀, x₁⟩
  rw [toLp_fst, toLp_snd, fstToSum_add_sndToSum]

/-- Every element of the sum space is a sum `x₀ + x₁`. -/
theorem exists_fstToSum_add_sndToSum_eq (u : C.SumSpace) :
    ∃ x₀ x₁, C.fstToSum x₀ + C.sndToSum x₁ = u := by
  obtain ⟨x, rfl⟩ := C.sumMk_surjective u
  exact ⟨x.fst, x.snd, (C.sumMk_apply x).symm⟩

theorem norm_fstToSum_add_sndToSum_le (x₀ : X₀) (x₁ : X₁) :
    ‖C.fstToSum x₀ + C.sndToSum x₁‖ ≤ ‖x₀‖ + ‖x₁‖ := by
  simpa [fstToSum_add_sndToSum] using C.norm_sumMk_le (toLp 1 (x₀, x₁))

theorem norm_fstToSum_le (x : X₀) : ‖C.fstToSum x‖ ≤ ‖x‖ := by
  simpa using C.norm_fstToSum_add_sndToSum_le x 0

theorem norm_sndToSum_le (x : X₁) : ‖C.sndToSum x‖ ≤ ‖x‖ := by
  simpa using C.norm_fstToSum_add_sndToSum_le 0 x

/-- The sum norm is the infimum of `‖x₀‖ + ‖x₁‖` over the decompositions `u = x₀ + x₁`:
strict upper bounds. -/
theorem norm_sumSpace_lt_iff {u : C.SumSpace} {r : ℝ} :
    ‖u‖ < r ↔ ∃ x₀ x₁, C.fstToSum x₀ + C.sndToSum x₁ = u ∧ ‖x₀‖ + ‖x₁‖ < r := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨x, hx, hxr⟩ := QuotientAddGroup.norm_lt_iff.1 h
    refine ⟨x.fst, x.snd, ?_, (prod_norm_eq_of_L1 x).symm.trans_lt hxr⟩
    rw [← C.sumMk_apply]
    exact hx
  · rintro ⟨x₀, x₁, rfl, h⟩
    exact (C.norm_fstToSum_add_sndToSum_le x₀ x₁).trans_lt h

/-- The sum norm is the infimum of `‖x₀‖ + ‖x₁‖` over the decompositions `u = x₀ + x₁`:
lower bounds. -/
theorem le_norm_sumSpace_iff {u : C.SumSpace} {r : ℝ} :
    r ≤ ‖u‖ ↔ ∀ x₀ x₁, C.fstToSum x₀ + C.sndToSum x₁ = u → r ≤ ‖x₀‖ + ‖x₁‖ := by
  simp only [← not_lt, norm_sumSpace_lt_iff, not_exists, not_and]

/-- The injective map from the sum space to the ambient space, `x₀ + x₁ ↦ x₀ + x₁`. -/
def sumSpaceEmbed : C.SumSpace →L[𝕜] V :=
  C.sumKer.liftQL C.sumMap le_rfl

@[simp]
theorem sumSpaceEmbed_sumMk (x : WithLp 1 (X₀ × X₁)) :
    C.sumSpaceEmbed (C.sumMk x) = C.sumMap x :=
  (rfl)

@[simp]
theorem sumSpaceEmbed_fstToSum (x : X₀) : C.sumSpaceEmbed (C.fstToSum x) = C.embed₀ x := by
  simp [fstToSum]

@[simp]
theorem sumSpaceEmbed_sndToSum (x : X₁) : C.sumSpaceEmbed (C.sndToSum x) = C.embed₁ x := by
  simp [sndToSum]

theorem sumSpaceEmbed_injective : Function.Injective C.sumSpaceEmbed :=
  LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- Two elements of the sum space agree as soon as their images in the ambient space do. -/
theorem sumSpace_ext {u v : C.SumSpace} (h : C.sumSpaceEmbed u = C.sumSpaceEmbed v) : u = v :=
  C.sumSpaceEmbed_injective h

/-- The image of the sum space in the ambient space is the sum of the two ranges. -/
theorem range_sumSpaceEmbed :
    C.sumSpaceEmbed.range = C.embed₀.range ⊔ C.embed₁.range := by
  ext v
  simp only [Submodule.mem_sup, LinearMap.mem_range]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
    exact ⟨_, ⟨x₀, rfl⟩, _, ⟨x₁, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x₀, rfl⟩, _, ⟨x₁, rfl⟩, rfl⟩
    exact ⟨C.fstToSum x₀ + C.sndToSum x₁, by simp⟩

theorem fstToSum_injective : Function.Injective C.fstToSum := fun x y h =>
  C.embed₀_injective <| by simpa using congrArg C.sumSpaceEmbed h

theorem sndToSum_injective : Function.Injective C.sndToSum := fun x y h =>
  C.embed₁_injective <| by simpa using congrArg C.sumSpaceEmbed h

/-- The two routes from the intersection to the sum agree. -/
theorem fstToSum_interFst (x : C.inter) : C.fstToSum (C.interFst x) = C.sndToSum (C.interSnd x) :=
  C.sumSpace_ext <| by simpa using C.embed₀_interFst x

section ToSum

variable {X : Type*} [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- A linear map `T : X → V` whose values `T x` are images of elements of the sum space of norm at
most `c ‖x‖` factors through the sum space: this is the continuous linear map `X → X₀ + X₁` sending
`x` to the unique `u` with `sumSpaceEmbed u = T x` (`sumSpaceEmbed_toSum`), of norm at most `c`
(`norm_toSum_le`). -/
def toSum (T : X →ₗ[𝕜] V) (c : ℝ) (hT : ∀ x, ∃ u, C.sumSpaceEmbed u = T x ∧ ‖u‖ ≤ c * ‖x‖) :
    X →L[𝕜] C.SumSpace :=
  LinearMap.mkContinuous
    { toFun x := (hT x).choose
      map_add' x y := C.sumSpace_ext <| (hT (x + y)).choose_spec.1.trans <| by
        simp only [map_add, (hT x).choose_spec.1, (hT y).choose_spec.1]
      map_smul' a x := C.sumSpace_ext <| (hT (a • x)).choose_spec.1.trans <| by
        simp only [RingHom.id_apply, map_smul, (hT x).choose_spec.1] }
    c fun x => (hT x).choose_spec.2

variable (T : X →ₗ[𝕜] V) (c : ℝ) (hT : ∀ x, ∃ u, C.sumSpaceEmbed u = T x ∧ ‖u‖ ≤ c * ‖x‖)

@[simp]
theorem sumSpaceEmbed_toSum (x : X) : C.sumSpaceEmbed (C.toSum T c hT x) = T x :=
  (hT x).choose_spec.1

theorem norm_toSum_le (x : X) : ‖C.toSum T c hT x‖ ≤ c * ‖x‖ :=
  (hT x).choose_spec.2

theorem toSum_injective (hTi : Function.Injective T) : Function.Injective (C.toSum T c hT) :=
  fun x y h => hTi <| by rw [← sumSpaceEmbed_toSum C T c hT, h, sumSpaceEmbed_toSum]

end ToSum

section Lift

variable {W : Type*} [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]

/-- A continuous linear map out of the sum space is determined by its restrictions to `X₀` and
`X₁`. -/
@[ext]
theorem sumSpace_hom_ext {f g : C.SumSpace →L[𝕜] W} (h₀ : f.comp C.fstToSum = g.comp C.fstToSum)
    (h₁ : f.comp C.sndToSum = g.comp C.sndToSum) : f = g := by
  ext u
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  rw [map_add, map_add]
  exact congr_arg₂ (· + ·) (DFunLike.congr_fun h₀ x₀) (DFunLike.congr_fun h₁ x₁)

variable [ContinuousAdd W]

/-- The extension to the sum space of continuous linear maps `T₀ : X₀ →L W`, `T₁ : X₁ →L W` that
agree on the intersection: `x₀ + x₁ ↦ T₀ x₀ + T₁ x₁`. This is the universal property of the sum
(`sumLift_fstToSum`, `sumLift_sndToSum`, `sumLift_unique`). -/
def sumLift (T₀ : X₀ →L[𝕜] W) (T₁ : X₁ →L[𝕜] W)
    (h : ∀ x : C.inter, T₀ (C.interFst x) = T₁ (C.interSnd x)) : C.SumSpace →L[𝕜] W :=
  C.sumKer.liftQL (T₀.comp (WithLp.fstL 1 𝕜 X₀ X₁) + T₁.comp (WithLp.sndL 1 𝕜 X₀ X₁))
    fun x hx => by
      have hx' : C.embed₀ x.fst = C.embed₁ (-x.snd) := by
        rw [map_neg, eq_neg_iff_add_eq_zero]
        exact hx
      have := h ⟨(x.fst, -x.snd), hx'⟩
      simp only [interFst_apply, interSnd_apply, map_neg] at this
      simp [this]

variable (T₀ : X₀ →L[𝕜] W) (T₁ : X₁ →L[𝕜] W)
  (h : ∀ x : C.inter, T₀ (C.interFst x) = T₁ (C.interSnd x))

@[simp]
theorem sumLift_sumMk (x : WithLp 1 (X₀ × X₁)) :
    C.sumLift T₀ T₁ h (C.sumMk x) = T₀ x.fst + T₁ x.snd :=
  (rfl)

@[simp]
theorem sumLift_fstToSum (x : X₀) : C.sumLift T₀ T₁ h (C.fstToSum x) = T₀ x := by
  simp [fstToSum]

@[simp]
theorem sumLift_sndToSum (x : X₁) : C.sumLift T₀ T₁ h (C.sndToSum x) = T₁ x := by
  simp [sndToSum]

@[simp]
theorem sumLift_comp_fstToSum : (C.sumLift T₀ T₁ h).comp C.fstToSum = T₀ :=
  ContinuousLinearMap.ext <| C.sumLift_fstToSum T₀ T₁ h

@[simp]
theorem sumLift_comp_sndToSum : (C.sumLift T₀ T₁ h).comp C.sndToSum = T₁ :=
  ContinuousLinearMap.ext <| C.sumLift_sndToSum T₀ T₁ h

/-- `sumLift T₀ T₁ h` is the only continuous linear map out of the sum space restricting to `T₀`
on `X₀` and to `T₁` on `X₁`. -/
theorem sumLift_unique {f : C.SumSpace →L[𝕜] W} (h₀ : f.comp C.fstToSum = T₀)
    (h₁ : f.comp C.sndToSum = T₁) : f = C.sumLift T₀ T₁ h :=
  C.sumSpace_hom_ext (by rw [h₀, sumLift_comp_fstToSum]) (by rw [h₁, sumLift_comp_sndToSum])

end Lift

section Morphism

variable {C} {Y₀ Y₁ W : Type*} [NormedAddCommGroup Y₀] [NormedSpace 𝕜 Y₀] [NormedAddCommGroup Y₁]
  [NormedSpace 𝕜 Y₁] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [ContinuousAdd W]
  {D : CompatibleCouple 𝕜 Y₀ Y₁ W}

/-- A linear map `P` of sum spaces is a left inverse of another one `I` as soon as their
restrictions to the endpoints are left inverses of each other. -/
theorem leftInverse_of_leftInverse {I : C.SumSpace →ₗ[𝕜] D.SumSpace}
    {P : D.SumSpace →ₗ[𝕜] C.SumSpace} {I₀ : X₀ → Y₀} {I₁ : X₁ → Y₁} {P₀ : Y₀ → X₀}
    {P₁ : Y₁ → X₁} (hI₀ : ∀ x, I (C.fstToSum x) = D.fstToSum (I₀ x))
    (hI₁ : ∀ x, I (C.sndToSum x) = D.sndToSum (I₁ x))
    (hP₀ : ∀ y, P (D.fstToSum y) = C.fstToSum (P₀ y))
    (hP₁ : ∀ y, P (D.sndToSum y) = C.sndToSum (P₁ y)) (h₀ : Function.LeftInverse P₀ I₀)
    (h₁ : Function.LeftInverse P₁ I₁) : Function.LeftInverse P I := by
  intro u
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  rw [map_add, map_add, hI₀, hI₁, hP₀, hP₁, h₀, h₁]

/-- If `P₀`, `P₁` are left inverses of `I₀`, `I₁`, the map of sum spaces induced by `P₀`, `P₁`
is a left inverse of the one induced by `I₀`, `I₁`. -/
theorem leftInverse_sumLift (I₀ : X₀ →L[𝕜] Y₀) (I₁ : X₁ →L[𝕜] Y₁)
    (hI : ∀ x : C.inter, D.fstToSum (I₀ (C.interFst x)) = D.sndToSum (I₁ (C.interSnd x)))
    (P₀ : Y₀ →L[𝕜] X₀) (P₁ : Y₁ →L[𝕜] X₁)
    (hP : ∀ y : D.inter, C.fstToSum (P₀ (D.interFst y)) = C.sndToSum (P₁ (D.interSnd y)))
    (hPI₀ : Function.LeftInverse P₀ I₀) (hPI₁ : Function.LeftInverse P₁ I₁) :
    Function.LeftInverse (D.sumLift (C.fstToSum.comp P₀) (C.sndToSum.comp P₁) hP)
      (C.sumLift (D.fstToSum.comp I₀) (D.sndToSum.comp I₁) hI) :=
  leftInverse_of_leftInverse (I := (C.sumLift _ _ hI).toLinearMap)
    (P := (D.sumLift _ _ hP).toLinearMap) (fun x => C.sumLift_fstToSum _ _ hI x)
    (fun x => C.sumLift_sndToSum _ _ hI x) (fun y => D.sumLift_fstToSum _ _ hP y)
    (fun y => D.sumLift_sndToSum _ _ hP y) hPI₀ hPI₁

variable {e : C.SumSpace ≃ₗ[𝕜] D.SumSpace} {e₀ : X₀ ≃L[𝕜] Y₀} {e₁ : X₁ ≃L[𝕜] Y₁}

/-- If a linear equivalence of sum spaces restricts to an isomorphism `e₀` of the first
endpoints, its inverse restricts to `e₀.symm`. -/
theorem symm_apply_fstToSum (he₀ : ∀ x, e (C.fstToSum x) = D.fstToSum (e₀ x)) (y : Y₀) :
    e.symm (D.fstToSum y) = C.fstToSum (e₀.symm y) :=
  e.symm_apply_eq.2 (by rw [he₀, ContinuousLinearEquiv.apply_symm_apply])

/-- If a linear equivalence of sum spaces restricts to an isomorphism `e₁` of the second
endpoints, its inverse restricts to `e₁.symm`. -/
theorem symm_apply_sndToSum (he₁ : ∀ x, e (C.sndToSum x) = D.sndToSum (e₁ x)) (y : Y₁) :
    e.symm (D.sndToSum y) = C.sndToSum (e₁.symm y) :=
  e.symm_apply_eq.2 (by rw [he₁, ContinuousLinearEquiv.apply_symm_apply])

end Morphism

end Sum

/-! ### Reversing the endpoints -/

/-- The compatible couple with the two endpoints exchanged. -/
-- Reducibility makes double reversal preserve the types of the associated sum spaces.
abbrev swap : CompatibleCouple 𝕜 X₁ X₀ V where
  embed₀ := C.embed₁
  embed₁ := C.embed₀
  embed₀_injective := C.embed₁_injective
  embed₁_injective := C.embed₀_injective

@[simp]
theorem swap_embed₀ : C.swap.embed₀ = C.embed₁ := (rfl)

@[simp]
theorem swap_embed₁ : C.swap.embed₁ = C.embed₀ := (rfl)

@[simp]
theorem swap_swap : C.swap.swap = C := (rfl)

section SwapSum

variable [ContinuousAdd V] [T1Space V]

omit [T1Space V] in
private theorem sumSwap_compat (x : C.inter) :
    C.swap.sndToSum (C.interFst x) = C.swap.fstToSum (C.interSnd x) :=
  C.swap.sumSpace_ext (by simpa using C.embed₀_interFst x)

private def sumSwapMap : C.SumSpace →L[𝕜] C.swap.SumSpace :=
  C.sumLift C.swap.sndToSum C.swap.fstToSum C.sumSwap_compat

private theorem sumSwapMap_norm_le (u : C.SumSpace) : ‖C.sumSwapMap u‖ ≤ ‖u‖ := by
  refine le_of_forall_gt fun r hr => ?_
  obtain ⟨x₀, x₁, rfl, hx⟩ := C.norm_sumSpace_lt_iff.1 hr
  simpa [sumSwapMap, add_comm] using
    (C.swap.norm_fstToSum_add_sndToSum_le x₁ x₀).trans_lt (by simpa [add_comm] using hx)

omit [T1Space V] in
private theorem sumSwapMap_sumSwapMap (u : C.SumSpace) :
    C.swap.sumSwapMap (C.sumSwapMap u) = u := by
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  simp [sumSwapMap]

/-- Exchanging the endpoints preserves the sum norm and the element in the ambient space. -/
def sumSwap : C.SumSpace ≃ₗᵢ[𝕜] C.swap.SumSpace :=
  LinearIsometryEquiv.ofBounds
    { toFun := C.sumSwapMap
      invFun := C.swap.sumSwapMap
      left_inv := C.sumSwapMap_sumSwapMap
      right_inv := C.swap.sumSwapMap_sumSwapMap
      map_add' := map_add C.sumSwapMap
      map_smul' := map_smul C.sumSwapMap }
    C.sumSwapMap_norm_le C.swap.sumSwapMap_norm_le

@[simp]
theorem sumSwap_fstToSum (x : X₀) : C.sumSwap (C.fstToSum x) = C.swap.sndToSum x :=
  C.sumLift_fstToSum _ _ C.sumSwap_compat x

@[simp]
theorem sumSwap_sndToSum (x : X₁) : C.sumSwap (C.sndToSum x) = C.swap.fstToSum x :=
  C.sumLift_sndToSum _ _ C.sumSwap_compat x

@[simp]
theorem sumSwap_symm : C.sumSwap.symm = C.swap.sumSwap := (rfl)

@[simp]
theorem sumSpaceEmbed_sumSwap (u : C.SumSpace) :
    C.swap.sumSpaceEmbed (C.sumSwap u) = C.sumSpaceEmbed u := by
  obtain ⟨x₀, x₁, rfl⟩ := C.exists_fstToSum_add_sndToSum_eq u
  simp

end SwapSum

/-! ### The diagonal couple -/

section Refl

variable (𝕜 X : Type*) [NormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The couple `(X, X)` with both embeddings the identity of `X`. -/
def refl : CompatibleCouple 𝕜 X X X where
  embed₀ := ContinuousLinearMap.id 𝕜 X
  embed₁ := ContinuousLinearMap.id 𝕜 X
  embed₀_injective := Function.injective_id
  embed₁_injective := Function.injective_id

@[simp]
theorem refl_embed₀ : (refl 𝕜 X).embed₀ = ContinuousLinearMap.id 𝕜 X :=
  (rfl)

@[simp]
theorem refl_embed₁ : (refl 𝕜 X).embed₁ = ContinuousLinearMap.id 𝕜 X :=
  (rfl)

variable {𝕜 X}

/-- For the couple `(X, X)`, the inclusion of the first space into the sum inverts
`sumSpaceEmbed`. -/
@[simp]
theorem refl_fstToSum_sumSpaceEmbed (u : (refl 𝕜 X).SumSpace) :
    (refl 𝕜 X).fstToSum ((refl 𝕜 X).sumSpaceEmbed u) = u :=
  (refl 𝕜 X).sumSpace_ext (by simp)

/-- For the couple `(X, X)`, the inclusion of the second space into the sum inverts
`sumSpaceEmbed`. -/
@[simp]
theorem refl_sndToSum_sumSpaceEmbed (u : (refl 𝕜 X).SumSpace) :
    (refl 𝕜 X).sndToSum ((refl 𝕜 X).sumSpaceEmbed u) = u :=
  (refl 𝕜 X).sumSpace_ext (by simp)

/-- For the couple `(X, X)` the intersection norm is the norm of `X`. -/
theorem norm_refl_inter (x : (refl 𝕜 X).inter) : ‖x‖ = ‖(refl 𝕜 X).interFst x‖ := by
  have h := (refl 𝕜 X).mem_inter_iff.1 x.2
  simp only [refl_embed₀, refl_embed₁, ContinuousLinearMap.id_apply] at h
  rw [norm_inter, interFst_apply, h, max_self]

/-- For the couple `(X, X)` the sum norm is the norm of `X`: the map to the ambient space `X` is
an isometry. -/
theorem norm_refl_sumSpaceEmbed (u : (refl 𝕜 X).SumSpace) :
    ‖(refl 𝕜 X).sumSpaceEmbed u‖ = ‖u‖ := by
  apply le_antisymm
  · refine le_of_forall_gt fun r hr => ?_
    obtain ⟨x₀, x₁, rfl, h⟩ := (refl 𝕜 X).norm_sumSpace_lt_iff.1 hr
    simpa using (norm_add_le x₀ x₁).trans_lt h
  · simpa using (refl 𝕜 X).norm_fstToSum_le ((refl 𝕜 X).sumSpaceEmbed u)

end Refl

end CompatibleCouple

end TauCeti
