/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Pushforward
public import TauCeti.Geometry.Manifold.VectorBundle.Section.FrameCover

/-!
# Pushforward of bundle-valued distribution densities along smooth maps

Let `f : X → Y` be a smooth map of manifolds modelled on finite-dimensional spaces and `V → Y` a
smooth real vector bundle. A test `s` of `V`, a compactly supported smooth section, pulls back to
the smooth section `x ↦ s (f x)` of the pullback bundle `f*V` over `X`, whose fibre over `x` is
`V (f x)` (`ContMDiffSection.pullback`). It is not compactly supported in general; cut off by a
smooth compactly supported function `χ` it is the test `χ f^*s` of `f*V`, and this is a continuous
linear map of the test spaces (`TauCeti.BundleTest.Pullback.cutoffCompCLM`). Its transpose is the
pushforward of functionals on the tests of `f*V`, cut off by `χ`,
`T ↦ (s ↦ T (χ f^*s))` (`TauCeti.BundleTest.Pullback.cutoffPushforwardCLM`).

When `V = B*` is the dual of a vector bundle `B → Y`, with no density factor, the continuous
linear functionals on the tests of `V` are the distribution densities on `Y` with values in `B`,
just as in the scalar case the distribution densities are the functionals on plain test
functions. Since `f*V = (f*B)*` fibrewise, `(f*B*)_x = B*_(f x)`, the functionals on the tests of
`f*V` over `X` are the distribution densities with values in `f*B`, and the pushforward sends
these to distribution densities on `Y` with values in `B`. This generalizes the scalar pushforward
of `TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Pushforward`, which treats the
trivial bundles `X × G` and `Y × G`. (For `V = B* ⊗ |Λ|` the functionals on the tests of `V` are
instead the distributional sections of `B`, `TauCeti.BundleDistribution`; these are not what this
file pushes forward, since the tests of `f*V` then carry the density factor `f*|Λ_Y|` rather than
`|Λ_X|`.)

As in the scalar case, the pushforward cut off by `χ` does not depend on `χ` near the support of
`T` (`TauCeti.BundleTest.Pullback.cutoffPushforwardCLM_congr`), is supported in
`f (supp χ ∩ supp T)` (`TauCeti.BundleTest.Pullback.dsupport_cutoffPushforwardCLM_subset`), obeys
the projection formula (`TauCeti.BundleTest.Pullback.smulLeftDualCLM_cutoffPushforwardCLM`) and
sends `δ_x ℓ`, for a functional `ℓ` on `V (f x)`, to `χ(x) δ_(f x) ℓ`. When `f` is proper on the
support of `T` (`TauCeti.BundleTest.IsProperOnSupport`), `T` has a **pushforward**
`f_* T` (`TauCeti.BundleTest.Pullback.pushforward`), the functional `s ↦ T (χ f^*s)` with `χ` equal
to one near `supp T ∩ f⁻¹(supp s)`; it does not depend on the cutoffs, is linear in `T`, is
supported in `f (supp T)` and sends `δ_x ℓ` to `δ_(f x) ℓ`. The cutoff pullbacks form a family of
cutoff pullbacks along `f` (`TauCeti.BundleTest.Pullback.isCutoffPullback_cutoffCompCLM`), so
the pushforward, its cutoff independence, support bounds and linearity specialize the generic
results for `TauCeti.BundleTest.IsCutoffPullback`, shared with the scalar pushforward.

## Main declarations

* `TauCeti.BundleTest.Pullback.cutoffCompCLM`: the cutoff pullback `s ↦ χ f^*s` of tests.
* `TauCeti.BundleTest.Pullback.cutoffPushforwardCLM`: its transpose, the pushforward of
  functionals cut off by `χ`.
* `TauCeti.BundleTest.Pullback.pushforward`: the pushforward `f_* T` along a map proper on the
  support of `T`, with `TauCeti.BundleTest.Pullback.pushforward_apply_of_eventuallyEq`,
  `TauCeti.BundleTest.Pullback.pushforward_apply_eq_cutoffCompCLM` and
  `TauCeti.BundleTest.Pullback.pushforward_eq_cutoffPushforwardCLM`.
* `TauCeti.BundleTest.Pullback.dsupport_pushforward_subset`: `supp (f_* T) ⊆ f (supp T)`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions and densities on manifolds, with values in vector bundles)
  and §8.2 (the pushforward of a distribution along a map proper on its support).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set*, Studia Math. 232 (2016), arXiv:1409.7662v2, §3
  (pushforward along maps proper on the support).
-/

public noncomputable section

open Bundle Set Filter Function TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti.BundleTest.Pullback

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  {E' H' Y : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace Y] [ChartedSpace H' Y]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : Y → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℝ (V y)]
  [∀ y, TopologicalSpace (V y)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]

variable [LocallyCompactSpace E] [IsManifold I ∞ X] [LocallyCompactSpace E'] [IsManifold J ∞ Y]
  [ContMDiffVectorBundle ∞ F V J]

/-! ### Pulling tests back along a smooth map -/

section CutoffComp

/-- The linear map underlying `TauCeti.BundleTest.Pullback.cutoffCompCLM`. -/
private def cutoffCompLinearMap (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) : BundleTest J F V →ₗ[ℝ] BundleTest I F ((f : C(X, Y)) *ᵖ V) where
  toFun s := ofCompactlySupported I F _
    ⟨χ • ((ofCompactlySupported J F V).symm s).val.pullback f,
      smul_function_mem_compactlySupported_of_hasCompactSupport χ hχ _⟩
  map_add' s t := by
    ext x
    simp only [ContinuousMap.coe_mk, map_add, Submodule.coe_add, pullback_add,
      LinearEquiv.symm_apply_apply, ContMDiffSection.smul_apply, coe_add, Pi.add_apply,
      pullback_apply, AddMemClass.mk_add_mk]
    -- The fibre of `f*V` at `x` is `V (f x)`.
    exact smul_add (χ x) (s (f x)) (t (f x))
  map_smul' a s := by
    ext x
    simp only [ContinuousMap.coe_mk, map_smul, SetLike.val_smul, pullback_smul,
      LinearEquiv.symm_apply_apply, ContMDiffSection.smul_apply, coe_smul, Pi.smul_apply,
      pullback_apply, RingHom.id_apply, SetLike.mk_smul_mk]
    -- The fibre of `f*V` at `x` is `V (f x)`.
    exact smul_comm (χ x) a (s (f x))

/-- The **pullback of tests along a smooth map `f : X → Y`, cut off by `χ`**: a test `s` of a
vector bundle `V` over `Y` is sent to the test `x ↦ χ x • s (f x)` of the pullback bundle `f*V`
over `X`, for a smooth compactly supported function `χ` on `X`. It is a continuous linear map for
the test topologies. Its transpose is the pushforward of a functional cut off by `χ`
(`TauCeti.BundleTest.Pullback.cutoffPushforwardCLM`). -/
def cutoffCompCLM (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯) :
    BundleTest J F V →L[ℝ] BundleTest I F ((f : C(X, Y)) *ᵖ V) where
  toLinearMap := cutoffCompLinearMap χ hχ f
  cont := by
    -- The frames of `f*V` pulled back from the preferred frames of `V`, over the preimages of
    -- their base sets, cover `X`, so they give the frame topology of the preferred frames of `f*V`.
    let e : Y → Trivialization F (π F V) := fun y ↦ trivializationAt F V y
    let U : Y → Opens Y := fun y ↦ ⟨_, (e y).open_baseSet⟩
    let eX := fun y ↦ (e y).pullback (f : C(X, Y))
    let UX := fun y ↦ Opens.comap (f : C(X, Y)) (U y)
    have hUX : ∀ y, (UX y : Set X) ⊆ (eX y).baseSet := fun _ _ hx ↦ hx
    have hframe : frameTopology (I := I) (n := ∞) eX UX hUX =
        frameTopology (I := I) (n := ∞)
          (fun x : X ↦ trivializationAt F ((f : C(X, Y)) *ᵖ V) x)
          (fun x ↦ ⟨_, (trivializationAt F ((f : C(X, Y)) *ᵖ V) x).open_baseSet⟩)
          fun _ ↦ subset_rfl :=
      frameTopology_eq_of_covers _ _ _ (fun x ↦ ⟨f x, mem_baseSet_trivializationAt F V (f x)⟩)
        _ _ _ fun x ↦ ⟨x, mem_baseSet_trivializationAt _ _ x⟩
    -- On sections, the map is `s ↦ χ • f^*s`, continuous for the frame topologies.
    have hP : @Continuous _ _ (frameTopology (I := J) (n := ∞) e U fun _ ↦ subset_rfl)
        (frameTopology (I := I) (n := ∞) eX UX hUX) fun s : Cₛ^∞⟮J; F, V⟯ ↦ χ • s.pullback f := by
      let := frameTopology (I := J) (n := ∞) e U fun _ ↦ subset_rfl
      let := frameTopology (I := I) (n := ∞) eX UX hUX
      exact (continuous_smul_function_frameTopology eX UX hUX χ).comp
        (continuous_pullback_frameTopology e U (fun _ ↦ subset_rfl) f)
    rw [hframe] at hP
    let := frameTopology (I := J) (n := ∞) e U fun _ ↦ subset_rfl
    let := frameTopology (I := I) (n := ∞)
      (fun x : X ↦ trivializationAt F ((f : C(X, Y)) *ᵖ V) x)
      (fun x ↦ ⟨_, (trivializationAt F ((f : C(X, Y)) *ᵖ V) x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp _).2 fun K ↦ ?_
    -- It sends the stage of tests supported in `K` into the stage of sections supported in
    -- `tsupport χ`.
    refine ((continuous_ofSupportedIn (F := F) ⟨tsupport χ, hχ⟩).comp
      ((hP.comp continuous_subtypeVal).subtype_mk fun s ↦
        mem_supportedIn.2 ((tsupport_smul_function_subset _ _).trans inter_subset_left))).congr
      fun s ↦ ?_
    ext x
    simp only [ContinuousMap.coe_mk, comp_apply, LinearEquiv.symm_apply_apply,
      ofSupportedIn_apply, ContMDiffSection.smul_apply, pullback_apply, cutoffCompLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk]

-- Normalize the continuous-map coercion in the implicit pullback-bundle type.
@[simp]
theorem cutoffCompCLM_apply (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (s : BundleTest J F V) (x : X) :
    dsimp% only [ContinuousMap.coe_mk] (cutoffCompCLM χ hχ f s x = χ x • s (f x)) := by
  simp only [ContinuousMap.coe_mk, cutoffCompCLM, cutoffCompLinearMap,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.symm_apply_apply,
    ContMDiffSection.smul_apply, pullback_apply]
  -- The fibre of `f*V` at `x` is `V (f x)`.
  rfl

/-- The cutoff pullback of a test `s` agrees with `s ∘ f` near every point of a set `S`, when the
cutoff is one near the points of `S` mapped into the support of `s`. -/
theorem cutoffCompCLM_eventuallyEq {χ : C^∞⟮I, X; ℝ⟯} (hχc : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (s : BundleTest J F V) {S : Set X}
    (hχ : ∀ᶠ x in 𝓝ˢ (S ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1) {x : X} (hx : x ∈ S) :
    ∀ᶠ z in 𝓝 x, cutoffCompCLM χ hχc f s z = s (f z) := by
  by_cases hfx : f x ∈ closure {y | s y ≠ 0}
  · filter_upwards [hχ.filter_mono (nhds_le_nhdsSet
      (show x ∈ S ∩ f ⁻¹' closure {y | s y ≠ 0} from ⟨hx, hfx⟩))] with z hz
    exact (cutoffCompCLM_apply χ hχc f s z).trans (by rw [hz, one_smul])
  · -- Near `x`, `f` takes values off the support of `s`, where `s` vanishes.
    filter_upwards [BundleTest.eventually_apply_comp_eq_zero f.contMDiff.continuous s hfx] with z hz
    exact (cutoffCompCLM_apply χ hχc f s z).trans (by rw [hz, smul_zero])

/-- The cutoff pullback of `s` is supported in the part of the support of `χ` that `f` maps into
the support of `s`. -/
theorem closure_cutoffCompCLM_ne_zero_subset (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (s : BundleTest J F V) :
    closure {x | cutoffCompCLM χ hχ f s x ≠ 0} ⊆
      _root_.tsupport χ ∩ f ⁻¹' closure {y | s y ≠ 0} :=
  closure_minimal (fun x hx ↦ by
      -- The fibre of `f*V` at `x` is `V (f x)`.
      have hx' : χ x • s (f x) ≠ 0 := by
        simp only [ContinuousMap.coe_mk, mem_ofPred_eq, cutoffCompCLM_apply] at hx
        exact hx
      rw [smul_ne_zero_iff] at hx'
      exact ⟨subset_tsupport _ hx'.1, subset_closure hx'.2⟩)
    ((_root_.isClosed_tsupport _).inter (isClosed_closure.preimage f.contMDiff.continuous))

/-- Cutoff pullbacks with two cutoffs differ by a test supported where the cutoffs differ. -/
theorem closure_cutoffCompCLM_sub_ne_zero_subset {χ χ' : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (hχ' : HasCompactSupport χ') (f : C^∞⟮I, X; J, Y⟯)
    (s : BundleTest J F V) :
    closure {x | (cutoffCompCLM χ hχ f s - cutoffCompCLM χ' hχ' f s) x ≠ 0} ⊆
      closure {x | χ x ≠ χ' x} :=
  closure_mono fun x hx ↦ by
    -- The fibre of `f*V` at `x` is `V (f x)`.
    have hx' : χ x • s (f x) - χ' x • s (f x) ≠ 0 := by
      simp only [ContinuousMap.coe_mk, mem_ofPred_eq, sub_apply, cutoffCompCLM_apply] at hx
      exact hx
    rw [← sub_smul, smul_ne_zero_iff] at hx'
    exact sub_ne_zero.1 hx'.1

variable (f) in
/-- The cutoff pullbacks `s ↦ χ f^*s` form a family of cutoff pullbacks along `f`, so the generic
pushforward theory of `TauCeti.BundleTest.IsCutoffPullback` applies to them. -/
theorem isCutoffPullback_cutoffCompCLM (f : C^∞⟮I, X; J, Y⟯) :
    IsCutoffPullback (I := I) (J := J) (F := F) (V := V) (F' := F)
      (V' := (f : C(X, Y)) *ᵖ V) f fun χ hχ ↦ cutoffCompCLM χ hχ f where
  closure_ne_zero_subset χ hχ := closure_cutoffCompCLM_ne_zero_subset χ hχ f
  closure_sub_ne_zero_subset hχ hχ' := closure_cutoffCompCLM_sub_ne_zero_subset hχ hχ' f

/-- Multiplying a cutoff pullback by a smooth function `ψ` on `X` multiplies the cutoff by `ψ`. -/
theorem smulLeftCLM_cutoffCompCLM (ψ : C^∞⟮I, X; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (s : BundleTest J F V) :
    smulLeftCLM ψ (cutoffCompCLM χ hχ f s) = cutoffCompCLM (ψ * χ) hχ.mul_left f s := by
  ext x
  simp only [ContinuousMap.coe_mk, smulLeftCLM_apply, cutoffCompCLM_apply, ContMDiffMap.coe_mul,
    Pi.mul_apply]
  exact smul_smul (ψ x) (χ x) (s (f x))

/-- The cutoff pullback of `g s`, for a smooth function `g` on `Y`, is the cutoff pullback of `s`
with the cutoff `χ · (g ∘ f)`. -/
theorem cutoffCompCLM_smulLeftCLM (g : C^∞⟮J, Y; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (s : BundleTest J F V) :
    cutoffCompCLM χ hχ f (smulLeftCLM g s) = cutoffCompCLM (χ * g.comp f) hχ.mul_right f s := by
  ext x
  simp only [ContinuousMap.coe_mk, cutoffCompCLM_apply, smulLeftCLM_apply, ContMDiffMap.coe_mul,
    Pi.mul_apply,
    ContMDiffMap.comp_apply, mul_smul]
  -- The fibre of `f*V` at `x` is `V (f x)`.
  rfl

end CutoffComp

/-! ### Pushforward of functionals with a cutoff -/

section Dual

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul ℝ W]

/-- The **pushforward of a functional cut off by `χ`**: the transpose `T ↦ T ∘ (χ f^*)` of the
cutoff pullback of tests (`TauCeti.BundleTest.Pullback.cutoffCompCLM`), from the functionals on the
tests of the pullback bundle `f*V` over `X` to the functionals on the tests of `V` over `Y`. It is
a continuous linear map for the topologies of uniform convergence on compact sets of tests. For
`T` compactly supported and `χ` equal to one near its support, it is the pushforward `f_* T`
(`TauCeti.BundleTest.Pullback.pushforward_eq_cutoffPushforwardCLM`). -/
def cutoffPushforwardCLM (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯) :
    (BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W) →L[ℝ] BundleTest J F V →L_c[ℝ] W :=
  (cutoffCompCLM χ hχ f).precompCompactConvergenceCLM W

-- As for `cutoffCompCLM_apply`, normalize the implicit pullback-bundle type.
@[simp]
theorem cutoffPushforwardCLM_apply (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W)
    (s : BundleTest J F V) :
    dsimp% only [ContinuousMap.coe_mk]
      (cutoffPushforwardCLM χ hχ f T s = T (cutoffCompCLM χ hχ f s)) :=
  (rfl)

/-- **Independence of the cutoff.** If `T` vanishes on the tests supported in a set `O`, then
cutoffs `χ` and `χ'` that agree off a closed subset of `O` give the same pushforward of `T`. In
particular all cutoffs equal to `1` near the support of `T` give the same pushforward. -/
theorem cutoffPushforwardCLM_congr {χ χ' : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ)
    (hχ' : HasCompactSupport χ') (f : C^∞⟮I, X; J, Y⟯)
    {T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I F ((f : C(X, Y)) *ᵖ V), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    (hχχ' : closure {x | χ x ≠ χ' x} ⊆ O) :
    cutoffPushforwardCLM χ hχ f T = cutoffPushforwardCLM χ' hχ' f T := by
  ext s
  exact (isCutoffPullback_cutoffCompCLM f).map_congr hχ hχ' hT hχχ' s

/-- **The support of a pushforward.** If `T` vanishes on the tests supported in `O`, then
`f_* (χ T)` vanishes on the tests whose support avoids the image under `f` of the part of the
support of `χ` outside `O`. With `O` the complement of the support of `T`, this says that the
support of `f_* (χ T)` lies in `f (supp χ ∩ supp T)`. -/
theorem cutoffPushforwardCLM_apply_eq_zero_of_disjoint {χ : C^∞⟮I, X; ℝ⟯}
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    {T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W} {O : Set X}
    (hT : ∀ s : BundleTest I F ((f : C(X, Y)) *ᵖ V), closure {x | s x ≠ 0} ⊆ O → T s = 0)
    {s : BundleTest J F V}
    (hs : Disjoint (closure {y | s y ≠ 0}) (f '' (_root_.tsupport χ \ O))) :
    cutoffPushforwardCLM χ hχ f T s = 0 :=
  (isCutoffPullback_cutoffCompCLM f).map_eq_zero_of_disjoint hχ hT hs

/-- Multiplying `T` by a smooth function `ψ` before pushing it forward with the cutoff `χ` is
pushing `T` forward with the cutoff `ψ χ`. -/
theorem cutoffPushforwardCLM_smulLeftDualCLM (ψ : C^∞⟮I, X; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W) :
    cutoffPushforwardCLM χ hχ f (smulLeftDualCLM ψ T) =
      cutoffPushforwardCLM (ψ * χ) hχ.mul_left f T := by
  ext s
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply, smulLeftDualCLM_apply,
    smulLeftCLM_cutoffCompCLM]

/-- **The projection formula**: multiplying the pushforward `f_* (χ T)` by a smooth function `g`
on `Y` is pushing `T` forward with the cutoff `χ · (g ∘ f)`. -/
theorem smulLeftDualCLM_cutoffPushforwardCLM (g : C^∞⟮J, Y; ℝ⟯) (χ : C^∞⟮I, X; ℝ⟯)
    (hχ : HasCompactSupport χ) (f : C^∞⟮I, X; J, Y⟯)
    (T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W) :
    smulLeftDualCLM g (cutoffPushforwardCLM χ hχ f T) =
      cutoffPushforwardCLM (χ * g.comp f) hχ.mul_right f T := by
  ext s
  rw [smulLeftDualCLM_apply, cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply,
    cutoffCompCLM_smulLeftCLM]

/-- The pushforward of a point mass is a point mass at the image point:
`f_* (χ δ_x ℓ) = χ(x) δ_(f x) ℓ`, for a continuous linear map `ℓ` on the fibre
`(f*V)_x = V (f x)`. -/
@[simp]
theorem cutoffPushforwardCLM_delta (χ : C^∞⟮I, X; ℝ⟯) (hχ : HasCompactSupport χ)
    (f : C^∞⟮I, X; J, Y⟯) (x : X) (ℓ : V (f x) →L[ℝ] W) :
    dsimp% only [ContinuousMap.coe_mk]
      (cutoffPushforwardCLM χ hχ f (delta (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ) =
        χ x • delta (I := J) (F := F) (V := V) (f x) ℓ) := by
  -- Work with the statement before `ContinuousMap.coe_mk` normalizes the pullback-bundle type.
  change cutoffPushforwardCLM χ hχ f (delta (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ) =
    χ x • delta (I := J) (F := F) (V := V) (f x) ℓ
  ext s
  rw [cutoffPushforwardCLM_apply]
  -- The fibre of `f*V` at `x` is `V (f x)`, on which `ℓ` acts.
  refine (delta_apply (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ _).trans ?_
  refine ((congrArg ℓ (cutoffCompCLM_apply χ hχ f s x)).trans (ℓ.map_smul (χ x) (s (f x)))).trans ?_
  rw [_root_.smul_apply, delta_apply]

end Dual

variable [FiniteDimensional ℝ E]

/-! ### The pushforward -/

section Pushforward

variable [T2Space X] {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
  {f : C^∞⟮I, X; J, Y⟯} {T : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W}

variable (T) in
/-- The **pushforward** `f_* T` of a continuous linear functional `T` on the tests of the pullback
bundle `f*V` over `X`, along a smooth map `f : X → Y` proper on the support of `T`: the functional
on the tests of `V` over `Y` pairing a test `s` with `T` through `T (χ f^*s)`, where `χ` is a smooth
compactly supported function on `X` equal to one near `supp T ∩ f⁻¹(supp s)`. Its value does not
depend on `χ` (`TauCeti.BundleTest.Pullback.pushforward_apply_of_eventuallyEq`). It is the
pushforward through the family of cutoff pullbacks `TauCeti.BundleTest.Pullback.cutoffCompCLM`
(`TauCeti.BundleTest.IsCutoffPullback.pushforward`). For `V = B*` the dual of a vector bundle
`B → Y`, the functionals on the tests of `f*V` are the distribution densities with values in
`f*B`, and `f_* T` is their pushforward, a distribution density with values in `B`. -/
def pushforward (hT : IsProperOnSupport ⇑T f) : BundleTest J F V →L_c[ℝ] W :=
  (isCutoffPullback_cutoffCompCLM f).pushforward T hT

/-- **Values of the pushforward with a cutoff.** `(f_* T) s = T (χ f^*s)` for every smooth
compactly supported `χ` equal to one near `supp T ∩ f⁻¹(supp s)`. -/
theorem pushforward_apply_eq_cutoffCompCLM (hT : IsProperOnSupport ⇑T f) (s : BundleTest J F V)
    {χ : C^∞⟮I, X; ℝ⟯} (hχc : HasCompactSupport χ)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport ⇑T ∩ f ⁻¹' closure {y | s y ≠ 0}), χ x = 1) :
    pushforward T hT s = T (cutoffCompCLM χ hχc f s) :=
  (isCutoffPullback_cutoffCompCLM f).pushforward_apply_eq hT s hχc hχ

/-- **Values of the pushforward.** `(f_* T) s = T t` for every test `t` of `f*V` which agrees with
`f^*s` near each point of the support of `T`. -/
theorem pushforward_apply_of_eventuallyEq (hT : IsProperOnSupport ⇑T f) (s : BundleTest J F V)
    {t : BundleTest I F ((f : C(X, Y)) *ᵖ V)}
    (ht : ∀ x ∈ dsupport ⇑T, ∀ᶠ z in 𝓝 x, t z = s (f z)) : pushforward T hT s = T t := by
  obtain ⟨χ, hχc, hχ⟩ := hT.exists_eventually_eq_one s.isCompact_tsupport
  rw [pushforward_apply_eq_cutoffCompCLM hT s hχc hχ]
  exact map_eq_map_of_eventuallyEq T <| eventually_nhdsSet_iff_forall.2 fun x hx ↦
    ((cutoffCompCLM_eventuallyEq hχc f s hχ hx).and (ht x hx)).mono fun _ h ↦ h.1.trans h.2.symm

/-- **The pushforward of a compactly supported functional** is its pushforward cut off by any
smooth compactly supported function equal to one near its support. -/
theorem pushforward_eq_cutoffPushforwardCLM (hT : IsProperOnSupport ⇑T f) {χ : C^∞⟮I, X; ℝ⟯}
    (hχc : HasCompactSupport χ) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport ⇑T), χ x = 1) :
    pushforward T hT = cutoffPushforwardCLM χ hχc f T := by
  ext s
  exact pushforward_apply_eq_cutoffCompCLM hT s hχc (hχ.filter_mono (nhdsSet_mono
    inter_subset_left))

/-! ### The support of the pushforward -/

omit [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] in
/-- **The support of a pushforward with a cutoff** lies in the image of the part of the support of
`T` in the support of the cutoff: `supp f_* (χ T) ⊆ f (supp χ ∩ supp T)`. -/
theorem dsupport_cutoffPushforwardCLM_subset [T2Space Y] [ContinuousConstSMul ℝ W]
    {χ : C^∞⟮I, X; ℝ⟯} (hχ : HasCompactSupport χ) :
    dsupport ⇑(cutoffPushforwardCLM χ hχ f T) ⊆ f '' (_root_.tsupport χ ∩ dsupport ⇑T) :=
  (isCutoffPullback_cutoffCompCLM f).dsupport_comp_subset f.contMDiff.continuous hχ

/-- **The support of the pushforward** lies in the image of the support:
`supp (f_* T) ⊆ f (supp T)`. -/
theorem dsupport_pushforward_subset [T2Space Y] (hT : IsProperOnSupport ⇑T f) :
    dsupport ⇑(pushforward T hT) ⊆ f '' dsupport ⇑T :=
  (isCutoffPullback_cutoffCompCLM f).dsupport_pushforward_subset f.contMDiff.continuous hT

/-- If `f` is proper on the support of `T` and `g ∘ f` is too, then `g` is proper on the support of
the pushforward `f_* T`. -/
theorem isProperOnSupport_pushforward [T2Space Y] {Z : Type*} [TopologicalSpace Z] {g : Y → Z}
    (hT : IsProperOnSupport ⇑T f) (hgfT : IsProperOnSupport ⇑T (g ∘ f)) :
    IsProperOnSupport ⇑(pushforward T hT) g :=
  (isCutoffPullback_cutoffCompCLM f).isProperOnSupport_pushforward f.contMDiff.continuous hT hgfT

/-! ### Linearity -/

/-- The pushforward of the zero functional is zero. -/
@[simp]
theorem pushforward_zero
    (h0 : IsProperOnSupport ⇑(0 : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W) f) :
    pushforward 0 h0 = 0 :=
  (isCutoffPullback_cutoffCompCLM f).pushforward_zero h0

/-- The pushforward is additive. -/
theorem pushforward_add {S : BundleTest I F ((f : C(X, Y)) *ᵖ V) →L_c[ℝ] W}
    (hS : IsProperOnSupport ⇑S f) (hT : IsProperOnSupport ⇑T f)
    (hST : IsProperOnSupport ⇑(S + T) f := hS.add hT) :
    pushforward (S + T) hST = pushforward S hS + pushforward T hT :=
  (isCutoffPullback_cutoffCompCLM f).pushforward_add hS hT hST

/-- The pushforward commutes with scalar multiplication. -/
theorem pushforward_smul {R : Type*} [Monoid R] [DistribMulAction R W] [SMulCommClass ℝ R W]
    [ContinuousConstSMul R W] (hT : IsProperOnSupport ⇑T f) (c : R)
    (hcT : IsProperOnSupport ⇑(c • T) f := hT.smul c) :
    pushforward (c • T) hcT = c • pushforward T hT :=
  (isCutoffPullback_cutoffCompCLM f).pushforward_smul hT c hcT

/-! ### Point masses -/

/-- **The pushforward of a point mass** is the point mass at the image point:
`f_* δ_x ℓ = δ_(f x) ℓ`, for a continuous linear map `ℓ` on the fibre `(f*V)_x = V (f x)`. -/
@[simp]
theorem pushforward_delta (x : X) (ℓ : V (f x) →L[ℝ] W)
    (h : IsProperOnSupport ⇑(delta (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ) f) :
    pushforward (delta (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ) h =
      delta (I := J) (F := F) (V := V) (f x) ℓ := by
  ext s
  obtain ⟨χ, hχc, hχ⟩ :=
    (isCompact_singleton (x := x)).exists_contMDiffMap_one_nhds_hasCompactSupport I
  rw [pushforward_apply_eq_cutoffCompCLM h s hχc (hχ.filter_mono (nhdsSet_mono
    (inter_subset_left.trans
      (dsupport_delta_subset (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ))))]
  -- The fibre of `f*V` at `x` is `V (f x)`, on which `ℓ` acts.
  refine (delta_apply (I := I) (F := F) (V := (f : C(X, Y)) *ᵖ V) x ℓ _).trans ?_
  refine (congrArg ℓ (cutoffCompCLM_apply χ hχc f s x)).trans ?_
  rw [hχ.self_of_nhdsSet x (mem_singleton x), one_smul, delta_apply]

end Pushforward

end TauCeti.BundleTest.Pullback
