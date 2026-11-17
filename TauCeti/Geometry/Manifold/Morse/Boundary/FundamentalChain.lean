/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Augmentation
public import TauCeti.Geometry.Manifold.Morse.Boundary.Integral
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import TauCeti.Geometry.Manifold.Orientation.Family
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The fundamental chain of the integral Morse complex

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, `X` a
Morse–Smale pseudo-gradient adapted to `f`, `𝔬` orientation data for the integral Morse boundary
(`TauCeti.MorseOrientation`), and `oM` an orientation of `M`. At a critical point `p` of index
`n` the unstable manifold `W^u(p)` is an open subset of `M`, which `𝔬` orients through the unstable
frame at `p`. The **fundamental sign** of `p`
(`TauCeti.IsAdaptedPseudoGradient.fundamentalSign`) is `1` if this is the orientation `oM`, `-1`
if it is the opposite one, and `0` at the critical points of index less than `n`. The
**fundamental chain** (`TauCeti.IsAdaptedPseudoGradient.signedMorseFundamentalChain`) is the sum
of the critical points of index `n`, weighted by their fundamental signs.

The main theorem is that the fundamental chain is a cycle of the integral Morse complex,
`∂ [M] = 0`, with coefficients in any ring. With coefficients in `ZMod 2` it is the mod-two
fundamental chain `TauCeti.morseFundamentalChain`, whatever the orientations. It is dual to the
vanishing of the augmentation on boundaries, `ε ∘ ∂ = 0`
(`TauCeti.Geometry.Manifold.Morse.Boundary.SignedAugmentation`), with the trajectories reaching a
critical point of index `n - 1` in place of those leaving a critical point of index `1`; unlike the
augmentation, it needs the orientation of `M`.

The proof has two steps.

* **The orientation of `M` along `W^u(p)`.** The flow preserves every orientation of `M`
  (`TauCeti.IsAdaptedPseudoGradient.isOrientationPreservingAt_flow`), and in a Morse chart at `p`
  the unstable frames at a point `y` of `W^u(p)` flowed back close to `p` and at `p` itself are the
  same map up to a positive factor. So the unstable frame compares `𝔬` with `oM` in the same way at
  every point of `W^u(p)`
  (`TauCeti.IsAdaptedPseudoGradient.map_unstableFrame_eq_orientationAt_iff`). Along a trajectory
  from `p` to a critical point `q`, the sign of the trajectory times the fundamental sign of `p`
  therefore compares `oM` with the map `v ↦ (df v, N_q v)` formed by the differential of `f` and
  the normal coordinates of `W^s(q)`.
* **The two sides of a critical point of index `n - 1`.** The stable manifold of such a `q` is `q`
  together with two trajectories, coming from critical points of index `n`. In a Morse chart at
  `q`, close to `q`, they have a single nonzero coordinate, of positive weight, and its signs on
  the two trajectories are opposite. There `df` is that coordinate times the coordinate function,
  while `oM` is constant in the chart, so the two maps `v ↦ (df v, N_q v)` carry `oM` to opposite
  orientations, and the two trajectories cancel in the boundary of the fundamental chain.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `fundamentalSign`: the sign comparing the orientation of the unstable manifold of a critical
  point of top index with the orientation of `M`, and `0` at the other critical points.
* `signedMorseFundamentalChain`: the sum of the critical points of top index, weighted by their
  fundamental signs, with coefficients in a ring `R`.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `isOrientationPreservingAt_flow`: the flow preserves every orientation of `M`.
* `map_unstableFrame_eq_orientationAt_iff`: the unstable frame of a critical point of top index
  compares orientations in the same way at every point of its unstable manifold.
* `IsMorseSmale.finsum_fundamentalSign_mul_signedMorseBoundaryCoeff`: the boundary coefficients of
  a critical point, weighted by the fundamental signs of their sources, add up to zero.
* `IsMorseSmale.signedMorseBoundary_signedMorseFundamentalChain`: `∂ [M] = 0`.
* `signedMorseFundamentalChain_eq_morseFundamentalChain`: modulo two, the fundamental chain is the
  mod-two fundamental chain.
* `signedMorseFundamentalChain_neg`, `signedMorseFundamentalChain_reverse`: reversing the
  orientation of `M`, or of unstable manifolds, changes the signs accordingly.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex with integer coefficients).
-/

public section

open Function Module Set Filter Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- Comparing an orientation with the opposite of a reference orientation reverses the sign of the
comparison. -/
private theorem ite_eq_neg_ite {V ι : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [Fintype ι] {o τ : Orientation ℝ V ι} {d₁ : Decidable (o = -τ)} {d₂ : Decidable (o = τ)}
    (h : Fintype.card ι = finrank ℝ V) :
    (if o = -τ then (1 : ℤ) else -1) = -(if o = τ then 1 else -1) := by
  rcases o.eq_or_eq_neg τ h with rfl | rfl
  · rw [ite_eq_right (Module.Ray.ne_neg_self o), ite_eq_left rfl]
  · rw [ite_eq_left rfl, ite_eq_right (Module.Ray.ne_neg_self τ).symm, neg_neg]

/-- Reversing an orientation reverses the sign of its comparison with a reference orientation. -/
private theorem ite_neg_eq_neg_ite {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Fintype ι] {o τ : Orientation ℝ V ι} {d₁ : Decidable (-o = τ)}
    {d₂ : Decidable (o = τ)} (h : Fintype.card ι = finrank ℝ V) :
    (if -o = τ then (1 : ℤ) else -1) = -(if o = τ then 1 else -1) := by
  rcases o.eq_or_eq_neg τ h with rfl | rfl
  · rw [ite_eq_right (Module.Ray.ne_neg_self o).symm, ite_eq_left rfl]
  · rw [ite_eq_left (neg_neg τ), ite_eq_right (Module.Ray.ne_neg_self τ).symm, neg_neg]

open scoped Classical in
/-- **Signs of orientations along a composite.** If `F` carries `o` to `oT` up to the sign
`[F o = oT]`, then the sign `[(A ∘ F) o = τ]` is that sign times `[A oT = τ]`. -/
private theorem ite_mul_ite_map_trans {V T W ι : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] [Fintype ι] (F : V ≃ₗ[ℝ] T) (A : T ≃ₗ[ℝ] W) (o : Orientation ℝ V ι)
    {oT : Orientation ℝ T ι} {τ : Orientation ℝ W ι} (hT : Fintype.card ι = finrank ℝ T)
    (hW : Fintype.card ι = finrank ℝ W) :
    (if Orientation.map ι F o = oT then (1 : ℤ) else -1) *
        (if Orientation.map ι (F.trans A) o = τ then 1 else -1) =
      if Orientation.map ι A oT = τ then 1 else -1 := by
  rw [Orientation.map_trans]
  rcases (Orientation.map ι F o).eq_or_eq_neg oT hT with h | h
  · simp only [h, ite_eq_left, one_mul]
  · rw [h, Orientation.map_neg, ite_eq_right (Module.Ray.ne_neg_self oT).symm,
      ite_neg_eq_neg_ite hW, neg_one_mul, neg_neg]

omit [CompactSpace M] [T2Space M] in
/-- Read through a map `g : M → E` preserving the orientations `oM` and `oE` at `y`, a linear
isomorphism `F` onto the tangent space at `y` carries an orientation `o` to that of `M` exactly when
its composite with the derivative of `g` carries `o` to that of `E`. -/
private theorem exists_map_eq_orientationAt_iff {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] {oM : Manifold.Orientation 𝓘(ℝ, E) M ι} {oE : Manifold.Orientation 𝓘(ℝ, E) E ι}
    {g : M → E} {y : M} (hg : oM.IsOrientationPreservingAt oE g y)
    (F : V ≃ₗ[ℝ] TangentSpace 𝓘(ℝ, E) y) (o : Orientation ℝ V ι) :
    ∃ e : TangentSpace 𝓘(ℝ, E) y ≃L[ℝ] TangentSpace 𝓘(ℝ, E) (g y),
      (e : TangentSpace 𝓘(ℝ, E) y →L[ℝ] TangentSpace 𝓘(ℝ, E) (g y)) =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g y ∧
      (Orientation.map ι F o = oM.orientationAt y ↔
        Orientation.map ι (F.trans e.toLinearEquiv) o = oE.orientationAt (g y)) := by
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 hg
  refine ⟨e, he, ?_⟩
  rw [Orientation.map_trans, ← hmap]
  exact (Orientation.map ι e.toLinearEquiv).injective.eq_iff.symm

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- **The flow of an adapted pseudo-gradient preserves every orientation** of `M`, at every time
and every point. -/
theorem isOrientationPreservingAt_flow {ι : Type*} [Fintype ι]
    (o : Manifold.Orientation 𝓘(ℝ, E) M ι) (t : ℝ) (y : M) :
    o.IsOrientationPreservingAt o (hX.flow t) y := by
  have h := Manifold.Orientation.isOrientationPreservingAt_family_iff o o
    (hX.contMDiff_flow_uncurry.of_le (by simp)) y
    (fun s ↦ by
      have hs : (fun z ↦ hX.flow s z) = hX.flowDiffeomorph s :=
        funext fun z ↦ (hX.flowDiffeomorph_apply s z).symm
      exact hs ▸ (hX.flowDiffeomorph s).isInvertible_mfderiv (x := y) (by simp)) t 0
  simp only [Flow.map_zero] at h
  exact h.2 (Manifold.Orientation.isOrientationPreservingAt_id o y)

variable {hX}

variable (hX) in
open scoped Classical in
/-- The **fundamental sign** of a critical point `p` for an orientation `oM` of `M`. When `p` has
Morse index `n = dim M`, the orientation `𝔬.orientation p` of the coordinates of negative weight is
carried by the unstable frame at `p` to an orientation of the tangent space `T_p M`; the sign is
`1` if this is the orientation `oM` of `M` at `p`, and `-1` otherwise. At the critical points of
index less than `n` the sign is `0`. -/
noncomputable def fundamentalSign (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) (p : criticalPoints 𝓘(ℝ, E) f) :
    ℤ :=
  if h : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E ∧
      Bijective (hX.unstableFrame (𝔬.chart p) p) then
    if Orientation.map _
        (LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) p).toLinearMap h.2)
        ((𝔬.orientation p).reindex ℝ _ (finCongr h.1)) = oM.orientationAt p then 1 else -1
  else 0

variable {𝔬 : MorseOrientation f X} {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}

/-- The unstable frame at a critical point of top index is bijective. -/
theorem bijective_unstableFrame_self (𝔬 : MorseOrientation f X) {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    Bijective (hX.unstableFrame (𝔬.chart p) p) :=
  bijective_unstableFrame (𝔬.coord_mfderiv_chart p) hp
    (mem_linearBackwardTimes_self (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2) 0)

open scoped Classical in
/-- At a critical point of top index, the fundamental sign compares the orientation of the
unstable manifold carried by the unstable frame with the orientation of `M`. -/
theorem fundamentalSign_of_morseIndex_eq {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.fundamentalSign 𝔬 oM p =
      if Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) p).toLinearMap
          (bijective_unstableFrame_self 𝔬 hp))
          ((𝔬.orientation p).reindex ℝ _ (finCongr hp)) = oM.orientationAt p then 1 else -1 := by
  rw [fundamentalSign, dite_eq_left ⟨hp, bijective_unstableFrame_self 𝔬 hp⟩]

/-- The fundamental sign vanishes at the critical points of index less than `dim M`. -/
@[simp]
theorem fundamentalSign_of_morseIndex_ne {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ finrank ℝ E) : hX.fundamentalSign 𝔬 oM p = 0 :=
  dite_eq_right fun h ↦ hp h.1

/-- At a critical point of top index the fundamental sign is `±1`. -/
theorem fundamentalSign_eq_one_or_eq_neg_one {p : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E) :
    hX.fundamentalSign 𝔬 oM p = 1 ∨ hX.fundamentalSign 𝔬 oM p = -1 := by
  rw [fundamentalSign_of_morseIndex_eq hp]
  split_ifs <;> simp

/-- Modulo two, the fundamental sign is `1` at the critical points of top index and `0`
elsewhere, whatever the orientations. -/
theorem intCast_fundamentalSign (p : criticalPoints 𝓘(ℝ, E) f) :
    (hX.fundamentalSign 𝔬 oM p : ZMod 2) =
      if manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E then 1 else 0 := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [ite_eq_left hp]
    rcases fundamentalSign_eq_one_or_eq_neg_one (𝔬 := 𝔬) (oM := oM) hp with h | h <;>
      rw [h] <;> decide
  · rw [ite_eq_right hp, fundamentalSign_of_morseIndex_ne hp, Int.cast_zero]

/-- **Reversing the orientation of `M` reverses the fundamental signs.** -/
@[simp]
theorem fundamentalSign_neg (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.fundamentalSign 𝔬 (-oM) p = -hX.fundamentalSign 𝔬 oM p := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [fundamentalSign_of_morseIndex_eq hp, fundamentalSign_of_morseIndex_eq hp,
      Manifold.Orientation.orientationAt_neg]
    exact ite_eq_neg_ite (Fintype.card_fin _)
  · simp [hp]

/-- **Reversing orientations changes the fundamental signs** at the critical points of the
reversed set. -/
theorem fundamentalSign_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f)) [DecidablePred (· ∈ S)]
    (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.fundamentalSign (𝔬.reverse S) oM p =
      (if p ∈ S then -1 else 1) * hX.fundamentalSign 𝔬 oM p := by
  by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
  · rw [fundamentalSign_of_morseIndex_eq hp, fundamentalSign_of_morseIndex_eq hp]
    -- The reversed data has the same charts, so both signs use the same unstable frame. The
    -- transported orientations are compared first, since `simp` cannot rewrite `reverse_chart`
    -- inside the dependent types of the frame and the orientation.
    have hmap : Orientation.map _ (LinearEquiv.ofBijective
          (hX.unstableFrame ((𝔬.reverse S).chart p) p).toLinearMap
          (bijective_unstableFrame_self (hX := hX) (𝔬.reverse S) hp))
          (((𝔬.reverse S).orientation p).reindex ℝ _ (finCongr hp)) =
        if p ∈ S then -Orientation.map _ (LinearEquiv.ofBijective
          (hX.unstableFrame (𝔬.chart p) p).toLinearMap
          (bijective_unstableFrame_self (hX := hX) 𝔬 hp))
          ((𝔬.orientation p).reindex ℝ _ (finCongr hp))
        else Orientation.map _ (LinearEquiv.ofBijective
          (hX.unstableFrame (𝔬.chart p) p).toLinearMap
          (bijective_unstableFrame_self (hX := hX) 𝔬 hp))
          ((𝔬.orientation p).reindex ℝ _ (finCongr hp)) := by
      rw [MorseOrientation.reverse_orientation]
      split_ifs
      · exact (congrArg _ (Orientation.reindex_neg _ _)).trans (Orientation.map_neg _ _)
      · rfl
    rw [hmap]
    by_cases hS : p ∈ S
    · rw [ite_eq_left hS, ite_eq_left hS, neg_one_mul]
      exact ite_neg_eq_neg_ite (Fintype.card_fin _)
    · rw [ite_eq_right hS, ite_eq_right hS, one_mul]
  · simp [hp]

/-- **The orientation of `M` along an unstable manifold.** Let `p` be a critical point and `op` an
orientation of the coordinates of negative weight of a Morse chart at `p` in which `X` is linear.
At every point `y` of `W^u(p)` where the unstable frame is an isomorphism, as it is when `p` has
index `n`, the unstable frame carries `op` to the orientation of `M` exactly when it does so at
`p`. -/
theorem map_unstableFrame_eq_orientationAt_iff (hf : IsMorse 𝓘(ℝ, E) f) {p : M}
    {φ : MorseChart E f p}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (finrank ℝ E))) {y : M}
    (hy : y ∈ hX.flow.unstableSet p) (hby : Bijective (hX.unstableFrame φ y))
    (hbp : Bijective (hX.unstableFrame φ p)) :
    Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φ y).toLinearMap hby) op =
        oM.orientationAt y ↔
      Orientation.map _ (LinearEquiv.ofBijective (hX.unstableFrame φ p).toLinearMap hbp) op =
        oM.orientationAt p := by
  -- An orientation of the model space for which the chart preserves orientations near `p`.
  obtain ⟨oE, hU⟩ := Manifold.Orientation.exists_eventually_isOrientationPreservingAt
    (contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one φ.mem_source)
    (isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source) oM
  -- Flow `y` back close to `p`, to a time of linear backward flow.
  have hlim : Tendsto (fun T ↦ hX.flow (-T) y) atTop (𝓝 p) :=
    (Flow.mem_unstableSet.1 hy).comp tendsto_neg_atTop_atBot
  obtain ⟨T, hT, hTU⟩ :=
    ((hX.eventually_mem_linearBackwardTimes hφ hf hy).and (hlim.eventually hU)).exists
  have hTp : T ∈ hX.linearBackwardTimes φ p := mem_linearBackwardTimes_self hp T
  -- The map `φ ∘ Φ_{-T}` preserves orientations at `y` and at `p`.
  have hg {z : M} (hz : oM.IsOrientationPreservingAt oE φ.toChart (hX.flow (-T) z)) :
      oM.IsOrientationPreservingAt oE (φ.toChart ∘ hX.flow (-T)) z :=
    hz.comp (hX.isOrientationPreservingAt_flow oM (-T) z)
  have hpU : oM.IsOrientationPreservingAt oE φ.toChart (hX.flow (-T) p) := by
    rw [hX.flow_apply_of_mfderiv_eq_zero hp]
    exact hU.self_of_nhds
  -- Through it, both frames become `e^{-T}` times the extension by zero.
  obtain ⟨ey, hey, hy'⟩ := exists_map_eq_orientationAt_iff (hg hTU)
    (LinearEquiv.ofBijective (hX.unstableFrame φ y).toLinearMap hby) op
  obtain ⟨ep, hep, hp'⟩ := exists_map_eq_orientationAt_iff (hg hpU)
    (LinearEquiv.ofBijective (hX.unstableFrame φ p).toLinearMap hbp) op
  have hL : ((LinearEquiv.ofBijective (hX.unstableFrame φ y).toLinearMap hby).trans
        ey.toLinearEquiv : _ ≃ₗ[ℝ] E) =
      (LinearEquiv.ofBijective (hX.unstableFrame φ p).toLinearMap hbp).trans ep.toLinearEquiv :=
    LinearEquiv.ext fun c ↦ (congrArg (· (hX.unstableFrame φ y c)) hey).trans
      ((mfderiv_unstableFrame hφ hT c).trans ((mfderiv_unstableFrame hφ hTp c).symm.trans
        (congrArg (· (hX.unstableFrame φ p c)) hep).symm))
  have key := congrArg (fun L : _ ≃ₗ[ℝ] E ↦ Orientation.map (Fin (finrank ℝ E)) L op) hL
  rw [hy', hp', Manifold.Orientation.orientationAt_eq_orientationAt oE
    ((φ.toChart ∘ hX.flow (-T)) y) ((φ.toChart ∘ hX.flow (-T)) p)]
  exact ⟨fun h ↦ key.symm.trans h, fun h ↦ key.trans h⟩

/-! ### The two trajectories into a critical point of index `n - 1` -/

/-- **Normal form of a point of the stable manifold near a critical point of index `n - 1`.**
Flowing a point `y ≠ q` of `W^s(q)` forward for a long time brings it to a point `z` with linear
forward flow at time `0`, satisfying any property `P` that holds near `q`, whose only nonzero
coordinate in the Morse chart is the coordinate `b` of positive weight. -/
private theorem exists_flow_eq_smul_single {q : M}
    {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hneg : ∀ i, i ≠ j → φ.weight i < 0) {y : M}
    (hy : y ∈ hX.flow.stableSet q) (hyq : y ≠ q) {P : M → Prop} (hP : ∀ᶠ z in 𝓝 q, P z) :
    ∃ T b : ℝ, 0 ∈ hX.linearForwardTimes φ (hX.flow T y) ∧ P (hX.flow T y) ∧ b ≠ 0 ∧
      φ.coord (φ.toChart (hX.flow T y)) = b • Pi.single j 1 := by
  obtain ⟨ε, hε, hloc⟩ := hX.exists_forall_mem_stableSet_iff φ hφ
  have hc : ContinuousAt (fun z ↦ ‖φ.coord (φ.toChart z)‖) q :=
    φ.continuous_coord.norm.continuousAt.comp (φ.toChart.continuousAt φ.mem_source)
  have hnear : ∀ᶠ z in 𝓝 q, P z ∧ z ∈ φ.toChart.source ∧ ‖φ.coord (φ.toChart z)‖ < ε :=
    hP.and ((φ.toChart.open_source.eventually_mem φ.mem_source).and
      (hc.eventually (gt_mem_nhds (by simp [hε]))))
  obtain ⟨T, hT, hPT, hsrc, hsmall⟩ := ((hX.eventually_mem_linearForwardTimes hφ hy).and
    ((Flow.mem_stableSet.1 hy).eventually hnear)).exists
  have hzs : hX.flow T y ∈ hX.flow.stableSet q := (Flow.apply_mem_stableSet_iff _ T).2 hy
  have hzero := (hloc _ hsrc hsmall).1 hzs
  set b := φ.coord (φ.toChart (hX.flow T y)) j
  have hcoord : φ.coord (φ.toChart (hX.flow T y)) = b • Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp [b]
    · simp [hi, hzero i (hneg i hi)]
  refine ⟨T, b, (mem_linearForwardTimes_flow (hX := hX)).2 (by rwa [zero_add]), hPT,
    fun hb ↦ hyq ?_, hcoord⟩
  -- A vanishing coordinate `b` puts the point at the centre `q` of the chart.
  rw [hb, zero_smul, ← map_zero φ.coord] at hcoord
  have hq := (φ.toChart_eq_zero_iff hsrc).1 (φ.coord.injective hcoord)
  calc y = hX.flow (-T) (hX.flow T y) := by rw [← Flow.map_add, neg_add_cancel, Flow.map_zero_apply]
    _ = hX.flow (-T) q := by rw [hq]
    _ = q := hX.flow_apply_of_mfderiv_eq_zero (hX.mfderiv_eq_zero_of_mem_stableSet hy) (-T)

/-- Two points of the stable manifold with linear forward flow at time `0`, whose only nonzero
coordinates are coordinates `b₁`, `b₂` of positive weight with `0 < b₂ / b₁ ≤ 1`, lie on one
orbit: the flow for the time `-log (b₂ / b₁)` takes the first to the second. -/
private theorem flow_eq_of_coord_eq_smul_single {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hpos : 0 < b₂ / b₁)
    (hle : b₂ / b₁ ≤ 1) : hX.flow (-Real.log (b₂ / b₁)) z₁ = z₂ := by
  have hb₁0 : b₁ ≠ 0 := fun h ↦ by simp [h] at hpos
  obtain ⟨hs, hcoord⟩ := add_mem_linearForwardTimes hφ h₁
    (neg_nonneg.2 (Real.log_nonpos hpos.le hle))
  rw [add_zero] at hs hcoord
  rw [Flow.map_zero_apply, hb₁, φ.linearFlow_smul, φ.linearFlow_single_of_weight_eq_one hj,
    neg_neg, Real.exp_log hpos, smul_smul, mul_div_cancel₀ _ hb₁0, ← hb₂] at hcoord
  have h₂src : z₂ ∈ φ.toChart.source := by
    simpa using ((mem_linearForwardTimes hX φ).1 h₂).1
  exact φ.toChart.injOn ((mem_linearForwardTimes hX φ).1 hs).1 h₂src
    (φ.coord.injective hcoord)

/-- **The two trajectories into a critical point of index `n - 1` arrive from opposite sides.**
Two points of the stable manifold on different orbits, with linear forward flow at time `0` and
whose only nonzero coordinates are coordinates `b₁`, `b₂` of positive weight, have `b₁ b₂ < 0`. -/
private theorem mul_neg_of_notMem_orbit {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁0 : b₁ ≠ 0) (hb₂0 : b₂ ≠ 0) (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hne : z₂ ∉ hX.flow.orbit z₁) :
    b₁ * b₂ < 0 := by
  by_contra hle
  have hpos : 0 < b₁ * b₂ := lt_of_le_of_ne (not_lt.1 hle) (mul_ne_zero hb₁0 hb₂0).symm
  have h₂₁ : 0 < b₂ / b₁ := by
    rw [show b₂ / b₁ = b₁ * b₂ / (b₁ * b₁) by field_simp]
    exact div_pos hpos (mul_self_pos.2 hb₁0)
  rcases le_total (b₂ / b₁) 1 with hle₁ | hle₁
  · exact hne ((hX.flow.mem_orbit_iff).2
      ⟨_, flow_eq_of_coord_eq_smul_single hφ hj h₁ h₂ hb₁ hb₂ h₂₁ hle₁⟩)
  · -- Otherwise the flow takes `z₂` to `z₁`.
    have h₁₂ : b₁ / b₂ = (b₂ / b₁)⁻¹ := (inv_div b₂ b₁).symm
    have h := flow_eq_of_coord_eq_smul_single hφ hj h₂ h₁ hb₂ hb₁ (h₁₂ ▸ inv_pos.2 h₂₁)
      (h₁₂ ▸ inv_le_one_of_one_le₀ hle₁)
    refine hne ((hX.flow.mem_orbit_iff).2 ⟨Real.log (b₁ / b₂), ?_⟩)
    rw [← h, ← Flow.map_add, add_neg_cancel, Flow.map_zero_apply]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- At a point of a Morse chart whose only nonzero coordinate is a coordinate `b` of weight `1`,
the linear field `X` is `-b` times the corresponding coordinate vector. -/
private theorem mfderiv_toChart_apply_eq_smul {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1) {z : M} (hz : z ∈ φ.toChart.source) {b : ℝ}
    (hb : φ.coord (φ.toChart z) = b • Pi.single j 1) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z (X z) = -b • φ.coord.symm (Pi.single j 1) := by
  refine φ.coord.injective ?_
  rw [hφ z hz, hb, map_smul, LinearEquiv.apply_symm_apply]
  funext i
  by_cases hi : i = j
  · subst hi
    simp [hj]
  · simp [hi]

/-- **The stable comparison map near a critical point of index `n - 1`.** Let `z` be a point of
the Morse chart at `q` with linear forward flow at time `0` whose only nonzero coordinate is a
coordinate `b` of weight `1`, at which the chart preserves the orientations `oM` and `oE`. The map
`v ↦ (df_z v, N_q v)`, read through the chart, is an isomorphism `Ψ` of `E` with `ℝ × V_q` whose
second component is the coordinates of negative weight, and which sends the coordinate vector of
weight `1` to `(a, 0)` with `a` of the sign of `b`. -/
private theorem exists_linearEquiv_stableComparison {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1)
    {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    {oE₀ : Orientation ℝ E (Fin (finrank ℝ E))} (hoE : ∀ x, oE.orientationAt x = oE₀) {z : M}
    (hz : 0 ∈ hX.linearForwardTimes φ z) {b : ℝ} (hb : φ.coord (φ.toChart z) = b • Pi.single j 1)
    (hb0 : b ≠ 0) (hcrit : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z ≠ 0)
    (hpres : oM.IsOrientationPreservingAt oE φ.toChart z)
    (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z))) :
    ∃ Ψ : E ≃ₗ[ℝ] ℝ × ({i // φ.weight i < 0} → ℝ),
      Orientation.map _
          (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z)).toLinearMap
            hA) (oM.orientationAt z) = Orientation.map _ Ψ oE₀ ∧
      (∀ u, (Ψ u).2 = φ.negativeCoord u) ∧
      ∃ a, Ψ (φ.coord.symm (Pi.single j 1)) = (a, 0) ∧ 0 < a * b := by
  obtain ⟨e, he, hmap⟩ := (Manifold.Orientation.isOrientationPreservingAt_iff _ _ _ _).1 hpres
  have hsrc : z ∈ φ.toChart.source := by simpa using ((mem_linearForwardTimes hX φ).1 hz).1
  set 𝒜 :=
    LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φ z)).toLinearMap hA
  have he' (v : TangentSpace 𝓘(ℝ, E) z) : e v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart z v := by
    rw [← he]
    rfl
  refine ⟨e.symm.toLinearEquiv.trans 𝒜, ?_, fun u ↦ ?_, ?_⟩
  · -- Transport the orientation of `M` at `z` to that of `E` through the chart.
    have h1 : Orientation.map _ 𝒜 (oM.orientationAt z) = Orientation.map _
        (e.symm.toLinearEquiv.trans 𝒜) (oE.orientationAt (φ.toChart z)) := by
      rw [← hmap, ← Orientation.map_trans]
      congr 2
      refine LinearEquiv.ext fun v ↦ ?_
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply]
      exact congrArg 𝒜 (e.symm_apply_apply v).symm
    rw [h1, hoE]
    rfl
  · -- By definition, `(Ψ u).2` is the normal coordinates of `e⁻¹ u`.
    calc _ = hX.stableNormal φ z (e.symm u) := rfl
      _ = φ.negativeCoord u := by
        rw [stableNormal_apply_of_zero_mem hφ hz, ← he']
        exact congrArg φ.negativeCoord (e.apply_symm_apply u)
  · -- The coordinate vector of weight `1` is read back as `-1 / b` times the velocity.
    have hX' : e.symm (φ.coord.symm (Pi.single j 1)) = (-b⁻¹) • X z := by
      have h : e (X z) = -b • φ.coord.symm (Pi.single j 1) :=
        (he' _).trans (mfderiv_toChart_apply_eq_smul hφ hj hsrc hb)
      have h' : e ((-b⁻¹) • X z) = φ.coord.symm (Pi.single j 1) := by
        rw [map_smul, h]
        exact (smul_smul _ _ _).trans (by rw [neg_mul_neg, inv_mul_cancel₀ hb0]; exact one_smul _ _)
      rw [← h', e.symm_apply_apply]
    refine ⟨-b⁻¹ * mvfderiv 𝓘(ℝ, E) f z (X z), Prod.ext ?_ ?_, ?_⟩
    · -- By definition, `(Ψ v).1` is the derivative of `f` at `e⁻¹ v`.
      calc _ = mvfderiv 𝓘(ℝ, E) f z (e.symm (φ.coord.symm (Pi.single j 1))) := rfl
        _ = _ := by rw [hX', map_smul, smul_eq_mul]
    · -- By definition, `(Ψ v).2` is the normal coordinates of `e⁻¹ v`.
      calc _ = hX.stableNormal φ z (e.symm (φ.coord.symm (Pi.single j 1))) := rfl
        _ = φ.negativeCoord (φ.coord.symm (Pi.single j 1)) := by
          rw [stableNormal_apply_of_zero_mem hφ hz, ← he']
          exact congrArg φ.negativeCoord (e.apply_symm_apply _)
        _ = 0 := ?_
      funext i
      rw [MorseChart.negativeCoord_apply, LinearEquiv.apply_symm_apply,
        Pi.single_eq_of_ne (fun h ↦ (lt_irrefl (0 : ℝ)) (by
          have := i.2
          rw [h, hj] at this
          linarith)), Pi.zero_apply]
    · have hdf := hX.mvfderiv_apply_lt_zero z hcrit
      rw [mul_comm, ← mul_assoc, mul_neg, mul_inv_cancel₀ hb0]
      linarith

/-- **The stable comparison maps on the two sides of a critical point of index `n - 1`.** At two
points `z₁`, `z₂` as in `exists_linearEquiv_stableComparison`, on opposite sides (`b₁ b₂ < 0`), the
maps `v ↦ (df_z v, N_q v)` carry the orientation of `M` to opposite orientations of `ℝ × V_q`. -/
private theorem map_stableComparison_eq_neg {q : M} {φ : MorseChart E f q}
    (hφ : ∀ y ∈ φ.toChart.source, φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E)
    {j : Fin (finrank ℝ E)} (hj : φ.weight j = 1)
    {oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    {oE₀ : Orientation ℝ E (Fin (finrank ℝ E))} (hoE : ∀ x, oE.orientationAt x = oE₀) {z₁ z₂ : M}
    (h₁ : 0 ∈ hX.linearForwardTimes φ z₁) (h₂ : 0 ∈ hX.linearForwardTimes φ z₂) {b₁ b₂ : ℝ}
    (hb₁ : φ.coord (φ.toChart z₁) = b₁ • Pi.single j 1)
    (hb₂ : φ.coord (φ.toChart z₂) = b₂ • Pi.single j 1) (hb : b₁ * b₂ < 0)
    (hcrit₁ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z₁ ≠ 0) (hcrit₂ : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f z₂ ≠ 0)
    (hpres₁ : oM.IsOrientationPreservingAt oE φ.toChart z₁)
    (hpres₂ : oM.IsOrientationPreservingAt oE φ.toChart z₂)
    (hA₁ : Bijective ((mvfderiv 𝓘(ℝ, E) f z₁).prod (hX.stableNormal φ z₁)))
    (hA₂ : Bijective ((mvfderiv 𝓘(ℝ, E) f z₂).prod (hX.stableNormal φ z₂))) :
    Orientation.map _
        (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z₂).prod (hX.stableNormal φ z₂)).toLinearMap
          hA₂) (oM.orientationAt z₂) =
      -Orientation.map _
        (LinearEquiv.ofBijective ((mvfderiv 𝓘(ℝ, E) f z₁).prod (hX.stableNormal φ z₁)).toLinearMap
          hA₁) (oM.orientationAt z₁) := by
  obtain ⟨Ψ₁, hΨ₁, hs₁, a₁, ha₁, hab₁⟩ := exists_linearEquiv_stableComparison hφ hj hoE h₁ hb₁
    (left_ne_zero_of_mul hb.ne) hcrit₁ hpres₁ hA₁
  obtain ⟨Ψ₂, hΨ₂, hs₂, a₂, ha₂, hab₂⟩ := exists_linearEquiv_stableComparison hφ hj hoE h₂ hb₂
    (right_ne_zero_of_mul hb.ne) hcrit₂ hpres₂ hA₂
  rw [hΨ₁, hΨ₂]
  -- `Ψ₂ = B ∘ Ψ₁`, where `B` fixes the second component and has determinant `a₂ / a₁ < 0`.
  set B := Ψ₁.symm.trans Ψ₂
  have hΨ : Ψ₂ = Ψ₁.trans B := LinearEquiv.ext fun u ↦ by simp [B]
  have hB (v : ℝ × ({i // φ.weight i < 0} → ℝ)) : (B v).2 = v.2 := by
    simp only [B, LinearEquiv.trans_apply]
    rw [hs₂, ← hs₁, Ψ₁.apply_symm_apply]
  have ha₁0 : a₁ ≠ 0 := left_ne_zero_of_mul hab₁.ne'
  have hB₁ : B (1, 0) = a₁⁻¹ • (a₂, 0) := by
    have hsymm : Ψ₁.symm (1, 0) = a₁⁻¹ • φ.coord.symm (Pi.single j 1) := by
      rw [LinearEquiv.symm_apply_eq, map_smul, ha₁, Prod.smul_mk, smul_eq_mul,
        inv_mul_cancel₀ ha₁0, smul_zero]
    simp only [B, LinearEquiv.trans_apply]
    rw [hsymm, map_smul, ha₂]
  have hdet : LinearMap.det B.toLinearMap < 0 := by
    rw [LinearMap.det_eq_fst_of_snd_eq _ hB, LinearEquiv.coe_coe, hB₁, Prod.smul_fst,
      smul_eq_mul]
    have : a₁ * a₂ < 0 := by nlinarith [mul_pos hab₁ hab₂]
    rw [show a₁⁻¹ * a₂ = a₁ * a₂ / (a₁ * a₁) by field_simp]
    exact div_neg_of_neg_of_pos this (mul_self_pos.2 ha₁0)
  rw [hΨ, Orientation.map_trans, Orientation.map_eq_neg_iff_det_neg _ _ ?_]
  · exact hdet
  · rw [Fintype.card_fin, finrank_prod, finrank_self, φ.finrank_negativeWeight_fun, add_comm, hq]

/-- **The stable comparison map along a trajectory from a critical point of top index.** At a
point `z` of a trajectory from a critical point `p` of index `n` to a critical point `q` of index
`n - 1`, the map `v ↦ (df_z v, N_q v)` is an isomorphism: it is the comparison map after the
inverse of the unstable frame of `p`. -/
private theorem bijective_stableComparison (hMS : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)
    {p q : M} {φp : MorseChart E f p} {φq : MorseChart E f q}
    (hφp : ∀ y ∈ φp.toChart.source, φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
    (hφq : ∀ y ∈ φq.toChart.source, φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal φq z)) := by
  obtain ⟨S, hS⟩ := (hX.eventually_mem_linearBackwardTimes hφp hf hz.1).exists
  refine (Bijective.of_comp_iff _ (bijective_unstableFrame hφp hp hS)).1 ?_
  convert bijective_trajectoryComparison hφp hφq hMS hf hpq hz using 1
  funext c
  rw [comp_apply, trajectoryComparison_apply]
  rfl

open scoped Classical in
/-- **A trajectory into a critical point of index `n - 1`, read against the orientation of `M`.**
Let `p` have index `n` and `q` index `n - 1`, and let `z` lie on a trajectory from `p` to `q`. The
sign of the trajectory, multiplied by the fundamental sign of `p`, is `1` exactly when the map
`v ↦ (df_z v, N_q v)` carries the orientation of `M` at `z` to the standard orientation of `ℝ`
followed by the orientation of the unstable manifold of `q`. -/
private theorem fundamentalSign_mul_trajectorySign (hMS : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) {p q : criticalPoints 𝓘(ℝ, E) f}
    (hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {z : M}
    (hz : z ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hA : Bijective ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z))) :
    hX.fundamentalSign 𝔬 oM p * hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p)
        (𝔬.orientation q) hpq z =
      if Orientation.map _ (LinearEquiv.ofBijective
          ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z)).toLinearMap hA)
          (oM.orientationAt z) =
        ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod (𝔬.orientation q)
          (Module.finrank_self ℝ) (𝔬.chart q).finrank_negativeWeight_fun).reindex ℝ _
          (finCongr (by omega)) then 1 else -1 := by
  obtain ⟨T, hT⟩ := (hX.eventually_mem_linearBackwardTimes (𝔬.coord_mfderiv_chart p) hf hz.1).exists
  have hF := bijective_unstableFrame (𝔬.coord_mfderiv_chart p) hp hT
  have hC := bijective_trajectoryComparison (𝔬.coord_mfderiv_chart p) (𝔬.coord_mfderiv_chart q)
    hMS hf hpq hz
  set 𝒜 := LinearEquiv.ofBijective
    ((mvfderiv 𝓘(ℝ, E) f z).prod (hX.stableNormal (𝔬.chart q) z)).toLinearMap hA
  set 𝓕 := LinearEquiv.ofBijective (hX.unstableFrame (𝔬.chart p) z).toLinearMap hF
  -- The comparison map is the stable comparison map after the unstable frame.
  have hC𝓕 : LinearEquiv.ofBijective
      (hX.trajectoryComparison (𝔬.chart p) (𝔬.chart q) z).toLinearMap hC = 𝓕.trans 𝒜 :=
    LinearEquiv.ext fun c ↦ by
      rw [LinearEquiv.ofBijective_apply, ContinuousLinearMap.coe_coe, trajectoryComparison_apply]
      rfl
  -- Index all orientations by `Fin n`.
  set op := (𝔬.orientation p).reindex ℝ _ (finCongr hp)
  set τ := ((Module.Basis.singleton (Fin 1) ℝ).orientation.prod (𝔬.orientation q)
    (Module.finrank_self ℝ) (𝔬.chart q).finrank_negativeWeight_fun).reindex ℝ _
    (finCongr (by omega : 1 + manifoldMorseIndex 𝓘(ℝ, E) f q = finrank ℝ E))
  have hτ : Orientation.map _ (LinearEquiv.ofBijective
      (hX.trajectoryComparison (𝔬.chart p) (𝔬.chart q) z).toLinearMap hC) (𝔬.orientation p) =
        (𝔬.chart q).trajectoryTargetOrientation (𝔬.orientation q) hpq ↔
      Orientation.map _ (𝓕.trans 𝒜) op = τ := by
    have hτp : τ = ((𝔬.chart q).trajectoryTargetOrientation (𝔬.orientation q) hpq).reindex ℝ _
        (finCongr hp) := by
      rw [MorseChart.trajectoryTargetOrientation_def, Orientation.reindex_finCongr_reindex_finCongr]
    rw [← hC𝓕, Orientation.map_reindex, hτp]
    exact (Orientation.reindex ℝ _ (finCongr hp)).injective.eq_iff.symm
  rw [fundamentalSign_of_morseIndex_eq hp, trajectorySign_of_bijective hC,
    ← map_unstableFrame_eq_orientationAt_iff hf (𝔬.coord_mfderiv_chart p)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2) oM op hz.1 hF, if_congr hτ rfl rfl]
  refine ite_mul_ite_map_trans 𝓕 𝒜 op (Fintype.card_fin _) ?_
  rw [Fintype.card_fin, finrank_prod, finrank_self, (𝔬.chart q).finrank_negativeWeight_fun]
  omega

/-! ### The fundamental chain is a cycle -/

namespace IsMorseSmale

variable (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) (𝔬 : MorseOrientation f X)
  (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E)))
include h hf

/-- **The two trajectories into a critical point of index `n - 1` cancel.** Let `q` have index
`n - 1`, and let `w 0`, `w 1` be points on two different trajectories into `q`, coming from
critical points `a 0`, `a 1` of index `n`. Weighted by the fundamental signs of their sources, the
two trajectories carry opposite signs. -/
private theorem fundamentalSign_mul_trajectorySign_eq_neg {q : criticalPoints 𝓘(ℝ, E) f}
    (hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E) {a : Fin 2 → criticalPoints 𝓘(ℝ, E) f}
    (ha : ∀ i, manifoldMorseIndex 𝓘(ℝ, E) f (a i) = finrank ℝ E) {w : Fin 2 → M}
    (hw : ∀ i, w i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q)
    (hw1 : w 1 ∉ hX.flow.orbit (w 0))
    (hpq : ∀ i, manifoldMorseIndex 𝓘(ℝ, E) f (a i) = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.fundamentalSign 𝔬 oM (a 1) * hX.trajectorySign (𝔬.chart (a 1)) (𝔬.chart q)
        (𝔬.orientation (a 1)) (𝔬.orientation q) (hpq 1) (w 1) =
      -(hX.fundamentalSign 𝔬 oM (a 0) * hX.trajectorySign (𝔬.chart (a 0)) (𝔬.chart q)
        (𝔬.orientation (a 0)) (𝔬.orientation q) (hpq 0) (w 0)) := by
  set φ := 𝔬.chart q
  have hφ := 𝔬.coord_mfderiv_chart q
  obtain ⟨j, hj, hneg⟩ := φ.exists_weight_eq_one_of_add_one_eq_finrank hq
  -- An orientation of the model space for which the chart preserves orientations near `q`.
  obtain ⟨oE, hU⟩ := Manifold.Orientation.exists_eventually_isOrientationPreservingAt
    (contMDiffAt_of_mem_maximalAtlas φ.mem_maximalAtlas_one φ.mem_source)
    (isInvertible_mfderiv_chart φ.mem_maximalAtlas_one φ.mem_source) oM
  have hoE (x : E) : oE.orientationAt x = oE.orientationAt 0 :=
    Manifold.Orientation.orientationAt_eq_orientationAt oE x 0
  have hne (i : Fin 2) : (a i : M) ≠ q := fun he ↦ by
    have := ha i
    rw [Subtype.coe_injective he] at this
    omega
  have hcrit (i : Fin 2) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (w i) ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hne i) (hw i)
  have hwq (i : Fin 2) : w i ≠ q := fun he ↦ hcrit i
    (he ▸ mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2)
  -- Flow both points close to `q`, into the normal form of the chart.
  choose T b h0 hpres hb0 hb using fun i ↦
    exists_flow_eq_smul_single hφ hneg (hw i).2 (hwq i) hU
  set z : Fin 2 → M := fun i ↦ hX.flow (T i) (w i)
  have hz (i : Fin 2) : z i ∈ hX.flow.unstableSet (a i) ∩ hX.flow.stableSet q :=
    ⟨(Flow.apply_mem_unstableSet_iff _ _).2 (hw i).1, (Flow.apply_mem_stableSet_iff _ _).2 (hw i).2⟩
  have hcritz (i : Fin 2) : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f (z i) ≠ 0 :=
    hX.mfderiv_ne_zero_of_mem_unstableSet_inter_stableSet (hne i) (hz i)
  have hA (i : Fin 2) := bijective_stableComparison h hf (𝔬.coord_mfderiv_chart (a i)) hφ (ha i)
    (hpq i) (hz i)
  -- The two points are on opposite sides of `q`.
  have hz1 : z 1 ∉ hX.flow.orbit (z 0) := fun hmem ↦ hw1 (by
    obtain ⟨t, ht⟩ := (hX.flow.mem_orbit_iff).1 hmem
    refine (hX.flow.mem_orbit_iff).2 ⟨-T 1 + (t + T 0), ?_⟩
    simp only [z] at ht
    rw [Flow.map_add, Flow.map_add, ht, ← Flow.map_add, neg_add_cancel, Flow.map_zero_apply])
  have hbb := mul_neg_of_notMem_orbit hφ hj (h0 0) (h0 1) (hb0 0) (hb0 1) (hb 0) (hb 1) hz1
  have hflip := map_stableComparison_eq_neg hφ hq hj hoE (h0 0) (h0 1) (hb 0) (hb 1) hbb
    (hcritz 0) (hcritz 1) (hpres 0) (hpres 1) (hA 0) (hA 1)
  -- Each weighted sign compares the orientation of `M` with the same orientation of `ℝ × V_q`.
  rw [← trajectorySign_flow (𝔬.coord_mfderiv_chart (a 1)) hφ h hf (hw 1) (T 1),
    ← trajectorySign_flow (𝔬.coord_mfderiv_chart (a 0)) hφ h hf (hw 0) (T 0),
    fundamentalSign_mul_trajectorySign h hf 𝔬 oM (ha 1) (hpq 1) (hz 1) (hA 1),
    fundamentalSign_mul_trajectorySign h hf 𝔬 oM (ha 0) (hpq 0) (hz 0) (hA 0)]
  rw [hflip]
  refine ite_neg_eq_neg_ite ?_
  rw [Fintype.card_fin, finrank_prod, finrank_self, φ.finrank_negativeWeight_fun]
  omega


/-- **The boundary coefficients into a critical point, weighted by the fundamental signs, add up
to zero.** For every critical point `q`, the coefficients of `q` in the integral boundaries of the
critical points `p`, weighted by the fundamental signs of `p`, add up to zero. -/
theorem finsum_fundamentalSign_mul_signedMorseBoundaryCoeff (q : criticalPoints 𝓘(ℝ, E) f) :
    ∑ᶠ p, hX.fundamentalSign 𝔬 oM p * hX.signedMorseBoundaryCoeff 𝔬 p q = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  rw [finsum_eq_sum_of_fintype]
  by_cases hq : manifoldMorseIndex 𝓘(ℝ, E) f q + 1 = finrank ℝ E
  swap
  · -- Away from index `n - 1`, no critical point of index `n` reaches `q`.
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    by_cases hp : manifoldMorseIndex 𝓘(ℝ, E) f p = finrank ℝ E
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one (by omega), mul_zero]
    · rw [fundamentalSign_of_morseIndex_ne hp, zero_mul]
  -- The two trajectories into `q` cross the middle levels at `w i` and start at `ac i`.
  obtain ⟨w, a, ha, hwmem, hw1, hwinj, hslice⟩ :=
    h.exists_morseTrajectorySlice_eq_image_of_add_one_eq_finrank hf
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) hq
  set ac : Fin 2 → criticalPoints 𝓘(ℝ, E) f :=
    fun i ↦ ⟨a i, mem_criticalPoints_iff_mfderiv_eq_zero.2 (ha i).1⟩
  have hpq (i : Fin 2) : manifoldMorseIndex 𝓘(ℝ, E) f (ac i) =
      manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := (ha i).2.trans hq.symm
  set s : Fin 2 → ℤ := fun i ↦ hX.fundamentalSign 𝔬 oM (ac i) * hX.trajectorySign
    (𝔬.chart (ac i)) (𝔬.chart q) (𝔬.orientation (ac i)) (𝔬.orientation q) (hpq i) (w i)
  have hs : s 1 = -s 0 :=
    fundamentalSign_mul_trajectorySign_eq_neg h hf 𝔬 oM hq (fun i ↦ (ha i).2) hwmem hw1 hpq
  -- The weighted coefficient of `q` in the boundary of `p` is the sum of the signs of the
  -- trajectories starting at `p`.
  have hp (p : criticalPoints 𝓘(ℝ, E) f) :
      hX.fundamentalSign 𝔬 oM p * hX.signedMorseBoundaryCoeff 𝔬 p q =
        ∑ i ∈ Finset.univ.filter (fun i ↦ ac i = p), s i := by
    by_cases hpi : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
    swap
    · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpi, mul_zero, eq_comm]
      exact Finset.sum_eq_zero fun i hi ↦ absurd ((Finset.mem_filter.1 hi).2 ▸ hpq i) hpi
    have hne : (p : M) ≠ q := fun he ↦ by
      rw [Subtype.coe_injective he] at hpi
      omega
    rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpi, signedTrajectoryCount_def,
      hslice p hne, finsum_mem_image hwinj.injOn,
      finsum_mem_eq_finite_toFinset_sum _ (toFinite _), Finset.mul_sum]
    refine Finset.sum_congr (by ext; simp [ac, Subtype.ext_iff]) fun i hi ↦ ?_
    obtain rfl : ac i = p := by simpa [ac, Subtype.ext_iff] using hi
    rfl
  rw [Finset.sum_congr rfl fun p _ ↦ hp p, Finset.sum_fiberwise, Fin.sum_univ_two, hs,
    add_neg_cancel]

end IsMorseSmale

variable (hX) in
/-- The **fundamental chain** of the integral Morse complex with coefficients in a ring `R`, for
an orientation `oM` of `M`: the sum of the critical points of index `n = dim M`, each weighted by
its fundamental sign. -/
noncomputable def signedMorseFundamentalChain (𝔬 : MorseOrientation f X)
    (oM : Manifold.Orientation 𝓘(ℝ, E) M (Fin (finrank ℝ E))) (hf : IsMorse 𝓘(ℝ, E) f)
    (R : Type*) [Ring R] : criticalPoints 𝓘(ℝ, E) f →₀ R :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.ofSupportFinite (fun p ↦ (hX.fundamentalSign 𝔬 oM p : R)) (toFinite _)

variable (hf : IsMorse 𝓘(ℝ, E) f) {R : Type*} [Ring R]

/-- The coefficient of a critical point in the fundamental chain is its fundamental sign. -/
@[simp]
theorem signedMorseFundamentalChain_apply (p : criticalPoints 𝓘(ℝ, E) f) :
    hX.signedMorseFundamentalChain 𝔬 oM hf R p = hX.fundamentalSign 𝔬 oM p := by
  rw [signedMorseFundamentalChain, Finsupp.ofSupportFinite_coe]

/-- **Reversing the orientation of `M` negates the fundamental chain.** -/
@[simp]
theorem signedMorseFundamentalChain_neg :
    hX.signedMorseFundamentalChain 𝔬 (-oM) hf R = -hX.signedMorseFundamentalChain 𝔬 oM hf R := by
  ext p
  simp

/-- **Reversing orientations changes the fundamental chain by the sign reversal** of the chains on
the reversed set. -/
theorem signedMorseFundamentalChain_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] :
    hX.signedMorseFundamentalChain (𝔬.reverse S) oM hf R =
      Finsupp.signReversal R S (hX.signedMorseFundamentalChain 𝔬 oM hf R) := by
  ext p
  rw [signedMorseFundamentalChain_apply, Finsupp.signReversal_apply,
    signedMorseFundamentalChain_apply, fundamentalSign_reverse]
  by_cases hS : p ∈ S <;> simp [hS]

/-- **Change of coefficients.** A ring homomorphism `g : R → R'` sends the fundamental chain with
coefficients in `R` to that with coefficients in `R'`. -/
theorem mapRange_signedMorseFundamentalChain {R' F : Type*} [Ring R'] [FunLike F R R']
    [RingHomClass F R R'] (g : F) :
    Finsupp.mapRange g (map_zero g) (hX.signedMorseFundamentalChain 𝔬 oM hf R) =
      hX.signedMorseFundamentalChain 𝔬 oM hf R' := by
  ext p
  simp

/-- **With coefficients in `ZMod 2`, the fundamental chain is the mod-two fundamental chain**, the
sum of the critical points of top index, whatever the orientations. -/
theorem signedMorseFundamentalChain_eq_morseFundamentalChain :
    hX.signedMorseFundamentalChain 𝔬 oM hf (ZMod 2) = morseFundamentalChain hf := by
  ext p
  rw [signedMorseFundamentalChain_apply, intCast_fundamentalSign, morseFundamentalChain_apply]

/-- **The fundamental chain is a cycle.** For a Morse–Smale pseudo-gradient on a compact oriented
manifold, the integral Morse boundary of the sum of the critical points of top index, weighted by
their fundamental signs, is zero: `∂ [M] = 0`, with coefficients in any ring. -/
@[simp]
theorem IsMorseSmale.signedMorseBoundary_signedMorseFundamentalChain (h : hX.IsMorseSmale) :
    hX.signedMorseBoundary 𝔬 hf R (hX.signedMorseFundamentalChain 𝔬 oM hf R) = 0 := by
  classical
  have := hf.finite_criticalPoints.fintype
  ext q
  have hsum := h.finsum_fundamentalSign_mul_signedMorseBoundaryCoeff hf 𝔬 oM q
  rw [finsum_eq_sum_of_fintype] at hsum
  rw [signedMorseBoundary_apply, Finsupp.zero_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [signedMorseFundamentalChain_apply]
  rw [← Int.cast_zero, ← hsum]
  push_cast
  rfl

end IsAdaptedPseudoGradient

end TauCeti
