/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transition
public import TauCeti.Geometry.Manifold.Morse.Boundary.DigonHomotopy

/-!
# Digon trajectories through the transition maps of the slab

Let `f₀` and `f₁` be Morse functions on a compact boundaryless manifold `M`, with pseudo-gradients
`X₀` and `X₁` adapted to them. The mod-two digon homotopy of a family `V λ` of fields on `M × ℝ`
(`TauCeti.morseDigonHomotopy`) counts the *digon trajectories*: the pairs of a parameter
`λ ∈ [0, 1]` and a trajectory of `V λ` from `(p, 0)` to `(q, 1)`, recorded by `λ` and the point of
the trajectory on the middle level `t = 1 / 2` (`TauCeti.morseDigonSlice`). This file describes
these trajectories through the transition maps of the slab, as was done for a single continuation
field in `TauCeti.Geometry.Manifold.Morse.Boundary.Continuation.Transition`.

**Families of continuation fields.** A family `V` is a *family of continuation fields* from `X₀`
to `X₁` at rate `C` (`TauCeti.IsContinuationFamily`) when, for every parameter `λ ∈ [0, 1]`, the
time component of `V λ` in the open slab is `C t (1 - t²)`, and its space component is `X₀` near
`t = 0` and `X₁` near `t = 1`, on neighbourhoods of the two ends that do not depend on `λ`. Each
`V λ` is then a continuation field (`TauCeti.IsContinuationFamily.isContinuationField`). The
constant family at a continuation field is a family of continuation fields
(`TauCeti.isContinuationFamily_const_iff`), and two continuation fields `V₀` and `V₁` with the same
ends and the same rate are joined by the family `(1 - λ) • V₀ + λ • V₁`
(`TauCeti.IsContinuationField.isContinuationFamily_one_sub_smul_add_smul`), the digon with edges
`V₀` and `V₁`.

**Digon trajectories through the transition maps.** Write `φ^λ_{s, t}` for the time-dependent flow
of the space component of `V λ` along the base trajectory `β = TauCeti.intervalBaseOrbit C`
(`TauCeti.continuationSpaceField`), and `σ` for the time with `β σ = 1 / 2`. Since the windows near
the ends of the slab are uniform in `λ`, the description of continuation trajectories by the
transition maps (`TauCeti.IsContinuationField.morseContinuationSlice_eq_preimage`) applies with
the same times `a` and `b` to all parameters at once: for every sufficiently negative `a` and every
sufficiently positive `b`, the digon slice from `p` to `q` consists of the pairs `(λ, x)` with
`λ ∈ [0, 1]`, `φ^λ_{σ, a} x ∈ W^u_{X₀}(p)` and `φ^λ_{σ, b} x ∈ W^s_{X₁}(q)`
(`TauCeti.IsContinuationFamily.eventually_morseDigonSlice_eq`). So the map
`(λ, x) ↦ (λ, φ^λ_{σ, a} x)` is a bijection from the digon slice onto the set
`TauCeti.morseDigonTransitionSlice` of pairs `(λ, y)` with `λ ∈ [0, 1]` and
`y ∈ W^u_{X₀}(p) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(q))`
(`TauCeti.IsContinuationFamily.eventually_bijOn_morseDigonSlice`): the digon trajectories are the
points of the intersections of the unstable manifolds of `X₀` with the preimages of the stable
manifolds of `X₁` under the one-parameter family of transition diffeomorphisms `φ^λ_{a, b}` of `M`.

**The digon identity.** Consequently the mod-two digon homotopy of `V` is the degree-one map of
these intersections
(`TauCeti.IsContinuationFamily.eventually_morseDegreeOneMap_morseDigonSlice_eq`), and the digon
identity `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹` of
`TauCeti.morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff` holds exactly when,
between critical points `p` of `f₀` and `q` of `f₁` of the same index, the configurations of these
intersections broken at the source and at the target, together with the points of
`W^u_{X₀}(p) ∩ (φ^0_{a, b})⁻¹ (W^s_{X₁}(q))` and of `W^u_{X₀}(p) ∩ (φ^1_{a, b})⁻¹ (W^s_{X₁}(q))` on
the two edges, are evenly many in total
(`IsContinuationFamily.eventually_morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff`).
This criterion is a statement about a one-parameter family of diffeomorphisms of `M` and the stable
and unstable manifolds of two pseudo-gradients, in which the trajectory spaces of the slab no
longer appear.

## Main declarations

* `TauCeti.IsContinuationFamily`: families of continuation fields with uniform end windows.
* `TauCeti.IsContinuationField.isContinuationFamily_one_sub_smul_add_smul`: the family joining two
  continuation fields.
* `TauCeti.morseDigonTransitionSlice`: the parametrized intersections
  `W^u_{X₀}(p) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(q))`, `λ ∈ [0, 1]`.
* `TauCeti.IsContinuationFamily.eventually_bijOn_morseDigonSlice`: the digon trajectories
  correspond to the points of these intersections.
* `eventually_morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff`, in the namespace
  `TauCeti.IsContinuationFamily`: the digon identity in terms of these intersections.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §4.2 (homotopic continuations give chain homotopic
  continuation maps, through the trajectories of a one-parameter family of time-dependent
  pseudo-gradients).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 6 (invariance of Morse homology by continuation).
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x} {C : ℝ}

/-! ### Families of continuation fields -/

/-- A **family of continuation fields** from `X₀` to `X₁` at rate `C`: a family `V λ` of vector
fields on `M × ℝ` such that, for every parameter `λ ∈ [0, 1]`, the time component of `V λ` in the
open slab `0 < t < 1` is `C t (1 - t²)`, and its space component is `X₀` near `t = 0` and `X₁`
near `t = 1`, on neighbourhoods of the two ends of the slab that do not depend on `λ`. Each field
`V λ` with `λ ∈ [0, 1]` is a continuation field
(`TauCeti.IsContinuationFamily.isContinuationField`); only these parameters are read. -/
structure IsContinuationFamily (X₀ X₁ : (x : M) → TangentSpace 𝓘(ℝ, E) x) (C : ℝ)
    (V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z) : Prop where
  /-- In the open slab, the time component of every field of the family is `C t (1 - t²)`. -/
  snd_eq : ∀ l ∈ Icc (0 : ℝ) 1, ∀ z : M × ℝ, z.2 ∈ Ioo 0 1 →
    (V l z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2)
  /-- Near `t = 0`, uniformly in the parameter, the space component is `X₀`. -/
  eventually_fst_eq_left : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ l ∈ Icc (0 : ℝ) 1, ∀ x,
    (V l (x, t) : E × ℝ).1 = X₀ x
  /-- Near `t = 1`, uniformly in the parameter, the space component is `X₁`. -/
  eventually_fst_eq_right : ∀ᶠ t in 𝓝[<] (1 : ℝ), ∀ l ∈ Icc (0 : ℝ) 1, ∀ x,
    (V l (x, t) : E × ℝ).1 = X₁ x

/-- **The fields of a family of continuation fields are continuation fields**, for the parameters
in `[0, 1]`. -/
theorem IsContinuationFamily.isContinuationField
    {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
    (hV : IsContinuationFamily X₀ X₁ C V) {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    IsContinuationField X₀ X₁ C (V l) where
  snd_eq := hV.snd_eq l hl
  eventually_fst_eq_left := hV.eventually_fst_eq_left.mono fun _ h ↦ h l hl
  eventually_fst_eq_right := hV.eventually_fst_eq_right.mono fun _ h ↦ h l hl

/-- **The constant family.** The constant family at a field `V` is a family of continuation
fields from `X₀` to `X₁` exactly when `V` is a continuation field from `X₀` to `X₁`. -/
@[simp]
theorem isContinuationFamily_const_iff {V : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z} :
    IsContinuationFamily X₀ X₁ C (fun _ ↦ V) ↔ IsContinuationField X₀ X₁ C V :=
  ⟨fun h ↦ h.isContinuationField (left_mem_Icc.2 zero_le_one), fun h ↦
    { snd_eq := fun _ _ ↦ h.snd_eq
      eventually_fst_eq_left := h.eventually_fst_eq_left.mono fun _ h _ _ ↦ h
      eventually_fst_eq_right := h.eventually_fst_eq_right.mono fun _ h _ _ ↦ h }⟩

/-- **The family joining two continuations.** Two continuation fields `V₀` and `V₁` from `X₀` to
`X₁` at the same rate `C` are joined by the family `(1 - λ) • V₀ + λ • V₁` of continuation
fields, with `V₀` at `λ = 0` and `V₁` at `λ = 1`. -/
theorem IsContinuationField.isContinuationFamily_one_sub_smul_add_smul
    {V₀ V₁ : (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
    (h₀ : IsContinuationField X₀ X₁ C V₀) (h₁ : IsContinuationField X₀ X₁ C V₁) :
    IsContinuationFamily X₀ X₁ C fun l z ↦ (1 - l) • V₀ z + l • V₁ z where
  snd_eq l _ z hz := by
    have h₀' : (V₀ z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) := h₀.snd_eq z hz
    have h₁' : (V₁ z : E × ℝ).2 = C * z.2 * (1 - z.2 ^ 2) := h₁.snd_eq z hz
    -- The operations of the tangent space are those of `E × ℝ`.
    calc ((1 - l) • V₀ z + l • V₁ z : E × ℝ).2 =
          (1 - l) * (V₀ z : E × ℝ).2 + l * (V₁ z : E × ℝ).2 := rfl
      _ = C * z.2 * (1 - z.2 ^ 2) := by rw [h₀', h₁']; ring
  eventually_fst_eq_left := by
    filter_upwards [h₀.eventually_fst_eq_left, h₁.eventually_fst_eq_left] with t ht₀ ht₁ l _ x
    -- The operations of the tangent space are those of `E × ℝ`.
    have hsum : ((1 - l) • V₀ (x, t) + l • V₁ (x, t) : E × ℝ).1 =
        (1 - l) • (V₀ (x, t) : E × ℝ).1 + l • (V₁ (x, t) : E × ℝ).1 := rfl
    have hcomb (v : E) : (1 - l) • v + l • v = v := by rw [← add_smul, sub_add_cancel, one_smul]
    exact hsum.trans (by rw [ht₀ x, ht₁ x]; exact hcomb _)
  eventually_fst_eq_right := by
    filter_upwards [h₀.eventually_fst_eq_right, h₁.eventually_fst_eq_right] with t ht₀ ht₁ l _ x
    -- The operations of the tangent space are those of `E × ℝ`.
    have hsum : ((1 - l) • V₀ (x, t) + l • V₁ (x, t) : E × ℝ).1 =
        (1 - l) • (V₀ (x, t) : E × ℝ).1 + l • (V₁ (x, t) : E × ℝ).1 := rfl
    have hcomb (v : E) : (1 - l) • v + l • v = v := by rw [← add_smul, sub_add_cancel, one_smul]
    exact hsum.trans (by rw [ht₀ x, ht₁ x]; exact hcomb _)

namespace IsContinuationFamily

variable {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}
  (hV : IsContinuationFamily X₀ X₁ C V) (hC : 0 < C)

include hV hC

/-- For `C > 0`, the space components of a family of continuation fields along the base trajectory
are all `X₀` before a common time. -/
theorem exists_forall_lt_continuationSpaceField_eq :
    ∃ a₀, ∀ s < a₀, ∀ l ∈ Icc (0 : ℝ) 1, continuationSpaceField C (V l) s = X₀ := by
  have hq : Tendsto (intervalBaseOrbit C) atBot (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_intervalBaseOrbit_atBot hC, .of_forall fun s ↦ (intervalBaseOrbit_mem_Ioo C s).1⟩
  obtain ⟨a₀, ha₀⟩ := eventually_atBot.1 (hq.eventually hV.eventually_fst_eq_left)
  exact ⟨a₀, fun s hs l hl ↦ funext fun x ↦ by
    rw [continuationSpaceField_apply]
    exact ha₀ s hs.le l hl x⟩

/-- For `C > 0`, the space components of a family of continuation fields along the base trajectory
are all `X₁` after a common time. -/
theorem exists_forall_gt_continuationSpaceField_eq :
    ∃ b₀, ∀ s > b₀, ∀ l ∈ Icc (0 : ℝ) 1, continuationSpaceField C (V l) s = X₁ := by
  have hq : Tendsto (intervalBaseOrbit C) atTop (𝓝[<] 1) :=
    tendsto_nhdsWithin_iff.2
      ⟨tendsto_intervalBaseOrbit_atTop hC, .of_forall fun s ↦ (intervalBaseOrbit_mem_Ioo C s).2⟩
  obtain ⟨b₀, hb₀⟩ := eventually_atTop.1 (hq.eventually hV.eventually_fst_eq_right)
  exact ⟨b₀, fun s hs l hl ↦ funext fun x ↦ by
    rw [continuationSpaceField_apply]
    exact hb₀ s hs.le l hl x⟩

end IsContinuationFamily

/-! ### Digon trajectories through the transition maps -/

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]
  {f₀ f₁ : M → ℝ} {V : ℝ → (z : M × ℝ) → TangentSpace (𝓘(ℝ, E).prod 𝓘(ℝ)) z}

variable (C V) in
/-- **The digon trajectories through the transition maps** from time `a` to time `b`, between `p`
and `q`: the pairs `(λ, y)` with `λ ∈ [0, 1]`, `y` in the unstable manifold of `p` for `X₀`, and
`φ^λ_{a, b} y` in the stable manifold of `q` for `X₁`, where `φ^λ` is the time-dependent flow of
the space component of `V λ` along the base trajectory (`TauCeti.continuationSpaceField`). For a
family of continuation fields, a very negative `a` and a very positive `b`, they correspond to the
digon trajectories from `p` to `q`
(`TauCeti.IsContinuationFamily.eventually_bijOn_morseDigonSlice`). -/
def morseDigonTransitionSlice (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
    (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (a b : ℝ) (p q : M) : Set (ℝ × M) :=
  {y | y.1 ∈ Icc 0 1 ∧ y.2 ∈ hX₀.flow.unstableSet p ∧
    timeDependentFlowOf (continuationSpaceField C (V y.1)) a b y.2 ∈ hX₁.flow.stableSet q}

/-- Membership in the digon trajectories through the transition maps. -/
@[simp]
theorem mem_morseDigonTransitionSlice {hX₀ : IsAdaptedPseudoGradient f₀ X₀}
    {hX₁ : IsAdaptedPseudoGradient f₁ X₁} {a b : ℝ} {p q : M} {y : ℝ × M} :
    y ∈ morseDigonTransitionSlice C V hX₀ hX₁ a b p q ↔
      y.1 ∈ Icc 0 1 ∧ y.2 ∈ hX₀.flow.unstableSet p ∧
        timeDependentFlowOf (continuationSpaceField C (V y.1)) a b y.2 ∈ hX₁.flow.stableSet q :=
  Iff.rfl

namespace IsContinuationFamily

variable (hV : IsContinuationFamily X₀ X₁ C V) (hX₀ : IsAdaptedPseudoGradient f₀ X₀)
  (hX₁ : IsAdaptedPseudoGradient f₁ X₁) (hC : 0 < C)
  (hVs : ∀ l ∈ Icc (0 : ℝ) 1, ContMDiff (𝓘(ℝ, E).prod 𝓘(ℝ)) (𝓘(ℝ, E).prod 𝓘(ℝ)).tangent 1
    fun z ↦ (⟨z, V l z⟩ : TangentBundle (𝓘(ℝ, E).prod 𝓘(ℝ)) (M × ℝ)))

include hVs in
/-- For the parameters in `[0, 1]`, the time-dependent flows of the space components compose. -/
private theorem flow_trans {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) (r s t : ℝ) (x : M) :
    timeDependentFlowOf (continuationSpaceField C (V l)) s t
        (timeDependentFlowOf (continuationSpaceField C (V l)) r s x) =
      timeDependentFlowOf (continuationSpaceField C (V l)) r t x :=
  TauCeti.timeDependentFlowOf_trans
    (isCompleteVectorField_timeDependentSuspensionField_of_compactSpace
      (contMDiff_continuationSpaceField (C := C) (hVs l hl)))
    (contMDiff_continuationSpaceField (C := C) (hVs l hl)) r s t x

include hV hX₀ hX₁ hC hVs in
/-- **The digon slices through the transition maps of the slab.** Let `V` be a family of `C¹`
continuation fields from `X₀` to `X₁` at rate `C > 0`, let `φ^λ` be the time-dependent flow of the
space component of `V λ` along the base trajectory `β`, and let `σ` be the time at which
`β σ = 1 / 2`. Then for every sufficiently negative time `a` and every sufficiently positive time
`b`, the digon slice from `p` to `q` consists of the pairs `(λ, x)` with `λ ∈ [0, 1]`,
`φ^λ_{σ, a} x` in the unstable manifold of `p` for `X₀` and `φ^λ_{σ, b} x` in the stable manifold
of `q` for `X₁`, for all `p` and `q` at once. -/
theorem eventually_morseDigonSlice_eq {σ : ℝ} (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M, morseDigonSlice V p q =
      {y | y.1 ∈ Icc 0 1 ∧
        timeDependentFlowOf (continuationSpaceField C (V y.1)) σ a y.2 ∈
          hX₀.flow.unstableSet p ∧
        timeDependentFlowOf (continuationSpaceField C (V y.1)) σ b y.2 ∈
          hX₁.flow.stableSet q} := by
  obtain ⟨a₀, ha₀⟩ := hV.exists_forall_lt_continuationSpaceField_eq hC
  obtain ⟨b₀, hb₀⟩ := hV.exists_forall_gt_continuationSpaceField_eq hC
  filter_upwards [eventually_lt_atBot a₀] with a ha
  filter_upwards [eventually_gt_atTop b₀] with b hb
  intro p q
  ext y
  rw [mem_morseDigonSlice, Set.mem_ofPred_eq]
  refine and_congr_right fun hl ↦ ?_
  rw [(hV.isContinuationField hl).morseContinuationSlice_eq_preimage hX₀ hX₁ hC (hVs _ hl) hσ
    (fun s hs ↦ ha₀ s hs _ hl) (fun s hs ↦ hb₀ s hs _ hl) ha hb]
  rfl

include hV hX₀ hX₁ hC hVs in
/-- **The digon trajectories are the points of the intersections through the transition maps.**
Let `V` be a family of `C¹` continuation fields from `X₀` to `X₁` at rate `C > 0`, let `φ^λ` be
the time-dependent flow of the space component of `V λ` along the base trajectory `β`, and let `σ`
be the time at which `β σ = 1 / 2`. Then for every sufficiently negative time `a` and every
sufficiently positive time `b`, the map `(λ, x) ↦ (λ, φ^λ_{σ, a} x)` is a bijection from the digon
slice from `p` to `q` onto the pairs `(λ, y)` with `λ ∈ [0, 1]` and
`y ∈ W^u_{X₀}(p) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(q))`, for all `p` and `q` at once. -/
theorem eventually_bijOn_morseDigonSlice {σ : ℝ} (hσ : intervalBaseOrbit C σ = 1 / 2) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M,
      BijOn (fun y : ℝ × M ↦
          (y.1, timeDependentFlowOf (continuationSpaceField C (V y.1)) σ a y.2))
        (morseDigonSlice V p q) (morseDigonTransitionSlice C V hX₀ hX₁ a b p q) := by
  filter_upwards [hV.eventually_morseDigonSlice_eq hX₀ hX₁ hC hVs hσ] with a ha
  filter_upwards [ha] with b hb p q
  rw [hb p q]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨l, x⟩ ⟨hl, hp, hq⟩
    exact ⟨hl, hp, by rwa [flow_trans hVs hl]⟩
  · rintro ⟨l, x⟩ ⟨hl, -⟩ ⟨l', x'⟩ - h
    obtain ⟨rfl, h⟩ := Prod.mk.inj h
    -- Flowing back from `a` to `σ` recovers the point on the middle level.
    have h' := congrArg (timeDependentFlowOf (continuationSpaceField C (V l)) a σ) h
    simp only [flow_trans hVs hl, timeDependentFlowOf_self] at h'
    rw [h']
  · rintro ⟨l, y⟩ ⟨hl, hp, hq⟩
    refine ⟨(l, timeDependentFlowOf (continuationSpaceField C (V l)) a σ y), ⟨hl, ?_, ?_⟩, ?_⟩
    · rwa [flow_trans hVs hl, timeDependentFlowOf_self]
    · rwa [flow_trans hVs hl]
    · simp [flow_trans hVs hl, timeDependentFlowOf_self]

include hV hX₀ hX₁ hC hVs in
/-- **The continuation trajectories of a field of the family through the transition maps.** Let `V`
be a family of `C¹` continuation fields from `X₀` to `X₁` at rate `C > 0`, and let `φ^λ` be the
time-dependent flow of the space component of `V λ` along the base trajectory. For every
`λ ∈ [0, 1]`, every sufficiently negative time `a` and every sufficiently positive time `b`, the
continuation trajectories of `V λ` from `(p, 0)` to `(q, 1)` are as many as the points of
`W^u_{X₀}(p) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(q))`, for all `p` and `q` at once. -/
theorem eventually_ncard_morseContinuationSlice_eq {l : ℝ} (hl : l ∈ Icc (0 : ℝ) 1) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, ∀ p q : M, (morseContinuationSlice (V l) p q).ncard =
      (hX₀.flow.unstableSet p ∩ timeDependentFlowOf (continuationSpaceField C (V l)) a b ⁻¹'
        hX₁.flow.stableSet q).ncard := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_morseDigonSlice_eq hX₀ hX₁ hC hVs hσ] with a ha
  filter_upwards [ha] with b hb p q
  have hY := contMDiff_continuationSpaceField (C := C) (hVs l hl)
  have hcomp := isCompleteVectorField_timeDependentSuspensionField_of_compactSpace hY
  -- The slice of `V λ` is the preimage of the intersection under the diffeomorphism `φ^λ_{σ, a}`.
  have hslice : morseContinuationSlice (V l) p q =
      timeDependentFlowOf (continuationSpaceField C (V l)) σ a ⁻¹' (hX₀.flow.unstableSet p ∩
        timeDependentFlowOf (continuationSpaceField C (V l)) a b ⁻¹' hX₁.flow.stableSet q) := by
    ext x
    have hx := congrArg ((l, x) ∈ ·) (hb p q)
    simp only [mem_morseDigonSlice, hl, true_and, eq_iff_iff, Set.mem_ofPred_eq] at hx
    rw [hx]
    simp [flow_trans hVs hl]
  set Φ := (timeDependentFlowDiffeomorph hcomp le_rfl hY σ a).toEquiv
  have hΦ : ⇑Φ = timeDependentFlowOf (continuationSpaceField C (V l)) σ a :=
    funext (timeDependentFlowDiffeomorph_apply hcomp le_rfl hY σ a)
  rw [hslice, ← hΦ, Set.ncard_preimage_of_injective_subset_range Φ.injective
    fun y _ ↦ Φ.surjective y]

include hV hX₀ hX₁ hC hVs in
/-- **The digon homotopy through the transition maps.** Let `V` be a family of `C¹` continuation
fields from `X₀` to `X₁` at rate `C > 0`, between pseudo-gradients adapted to Morse functions `f₀`
and `f₁`. For every sufficiently negative time `a` and every sufficiently positive time `b`, the
mod-two digon homotopy of `V` is the degree-one map of the intersections
`W^u_{X₀}(p) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(q))`, `λ ∈ [0, 1]`. -/
theorem eventually_morseDegreeOneMap_morseDigonSlice_eq (hf₁ : IsMorse 𝓘(ℝ, E) f₁) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop, morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) =
      morseDegreeOneMap f₀ hf₁ (morseDigonTransitionSlice C V hX₀ hX₁ a b) := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_bijOn_morseDigonSlice hX₀ hX₁ hC hVs hσ] with a ha
  filter_upwards [ha] with b hb
  exact morseDegreeOneMap_congr_ncard hf₁ fun p q _ ↦ by
    rw [← (hb p q).image_eq, (hb p q).injOn.ncard_image]

variable {hX₀ hX₁} (h₀ : hX₀.IsMorseSmale) (hf₀ : IsMorse 𝓘(ℝ, E) f₀)
  (h₁ : hX₁.IsMorseSmale) (hf₁ : IsMorse 𝓘(ℝ, E) f₁)

include hV hC hVs h₀ hf₀ h₁ in
/-- **The digon identity through the transition maps.** Let `V` be a family of `C¹` continuation
fields from `X₀` to `X₁` at rate `C > 0`, between Morse–Smale pseudo-gradients adapted to Morse
functions `f₀` and `f₁`, whose digon slices between critical points with indices differing by one
are finite. For every sufficiently negative time `a` and every sufficiently positive time `b`, the
mod-two digon homotopy `K` of `V` satisfies `∂₁ ∘ K + K ∘ ∂₀ = F⁰ + F¹`, for the continuation maps
`F⁰` and `F¹` along `V 0` and `V 1`, exactly when, between any critical point `p` of `f₀` and any
critical point `q` of `f₁` of the same index, the configurations of the intersections
`W^u_{X₀}(·) ∩ (φ^λ_{a, b})⁻¹ (W^s_{X₁}(·))` broken at the source and at the target, together with
the points of `W^u_{X₀}(p) ∩ (φ^0_{a, b})⁻¹ (W^s_{X₁}(q))` and of
`W^u_{X₀}(p) ∩ (φ^1_{a, b})⁻¹ (W^s_{X₁}(q))`, are evenly many in total. -/
theorem eventually_morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff
    (hfin : ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
      manifoldMorseIndex 𝓘(ℝ, E) f₁ q = manifoldMorseIndex 𝓘(ℝ, E) f₀ p + 1 →
        (morseDigonSlice V p q).Finite) :
    ∀ᶠ a in atBot, ∀ᶠ b in atTop,
      (h₁.morseBoundary hf₁ ∘ₗ morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) +
          morseDegreeOneMap f₀ hf₁ (morseDigonSlice V) ∘ₗ h₀.morseBoundary hf₀ =
        morseContinuationMap f₀ hf₁ (V 0) + morseContinuationMap f₀ hf₁ (V 1) ↔
      ∀ (p : criticalPoints 𝓘(ℝ, E) f₀) (q : criticalPoints 𝓘(ℝ, E) f₁),
        manifoldMorseIndex 𝓘(ℝ, E) f₀ p = manifoldMorseIndex 𝓘(ℝ, E) f₁ q →
          Even ((morseSourceBrokenDegreeOneSet f₁
              (morseDigonTransitionSlice C V hX₀ hX₁ a b) hX₀ p q).ncard +
            (morseTargetBrokenDegreeOneSet f₀
              (morseDigonTransitionSlice C V hX₀ hX₁ a b) hX₁ p q).ncard +
            (hX₀.flow.unstableSet p ∩ timeDependentFlowOf (continuationSpaceField C (V 0)) a b ⁻¹'
              hX₁.flow.stableSet q).ncard +
            (hX₀.flow.unstableSet p ∩ timeDependentFlowOf (continuationSpaceField C (V 1)) a b ⁻¹'
              hX₁.flow.stableSet q).ncard)) := by
  obtain ⟨σ, hσ⟩ := exists_intervalBaseOrbit_eq hC.ne' (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  filter_upwards [hV.eventually_bijOn_morseDigonSlice hX₀ hX₁ hC hVs hσ,
    hV.eventually_ncard_morseContinuationSlice_eq hX₀ hX₁ hC hVs (left_mem_Icc.2 zero_le_one),
    hV.eventually_ncard_morseContinuationSlice_eq hX₀ hX₁ hC hVs (right_mem_Icc.2 zero_le_one)]
    with a hg h₀' h₁'
  filter_upwards [hg, h₀', h₁'] with b hg h₀' h₁'
  rw [morseBoundary_comp_morseDegreeOneMap_morseDigonSlice_add_eq_iff h₀ hf₀ h₁ hf₁ hfin]
  simp only [← ncard_morseSourceBrokenDegreeOneSet_congr hX₀ hg,
    ← ncard_morseTargetBrokenDegreeOneSet_congr hX₁ hg, h₀', h₁']

end IsContinuationFamily

end TauCeti
