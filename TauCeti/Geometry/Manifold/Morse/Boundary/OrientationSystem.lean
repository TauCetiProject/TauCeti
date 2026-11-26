/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.DualOrientation
public import TauCeti.Geometry.Manifold.Morse.Boundary.ReversedSign
public import TauCeti.Geometry.Manifold.Morse.Boundary.LocalCoefficient
public import TauCeti.Geometry.Manifold.Morse.Stable.OrientationCover
public import TauCeti.Topology.VectorBundle.Orientation.LocalSystem
import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# The Morse boundary of the opposite function with coefficients in the orientation system

Let `f` be a Morse function on a compact boundaryless manifold `M` of dimension `n`, not assumed
orientable, and `X` a Morse–Smale pseudo-gradient adapted to `f`. Then `-X` is a Morse–Smale
pseudo-gradient adapted to `-f`, and a trajectory of `X` from `p` to `q`, run backwards, is a
trajectory of `-X` from `q` to `p`. On an oriented manifold, compatible orientation data make
every such trajectory count for `-f` with `(-1) ^ ind_f p` times its sign for `f`
(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_of_unstableFrameOrientation`). This file
removes the orientation of `M`: the trajectory then also records how the orientation local system
of `M` twists along it.

At each critical point `x`, orientations `ox` of the unstable manifold of `X` and `ox'` of the
unstable manifold of `-X` give the orientation of `T_x M` with `ox` first
(`TauCeti.IsAdaptedPseudoGradient.criticalOrientation`). For a trajectory from `p` to `q`, compare
the transport of this orientation at `p` along the path the trajectory traces
(`TauCeti.VectorBundleOrientationCover.orientationTransport`, the monodromy of the orientation
double cover of `M`) with the orientation at `q`, and let `τ` be `1` if they agree and `-1`
otherwise. Then

`sign_{-X}(y) = (-1) ^ ind_f p * τ(y) * sign_X(y)`

(`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign_eq_ite_orientationTransport`). On an oriented
manifold with the orientations chosen to orient `M` at every critical point, `τ = 1` and this is
the oriented rule. The proof cuts the trajectory at the point `y`: the half from `p` to `y` lies in
the unstable manifold of `p` and the half from `y` to `q` in the stable manifold of `q`, along
which the frame orientations are continuous in the orientation double cover
(`TauCeti.IsAdaptedPseudoGradient.orientationTransport_unstableFrameOrientation`,
`TauCeti.IsAdaptedPseudoGradient.orientationTransport_stableNormalOrientation`). So `τ` is the
comparison of the two frame orientations at `y` in the general sign rule
`TauCeti.IsAdaptedPseudoGradient.neg_trajectorySign`, up to the sign of exchanging the factors at
`q`.

**The opposite function with coefficients in the orientation system.** Given orientation data `𝔬`
for `f` and orientations `o'` of the unstable manifolds of `-X` in the negated Morse charts
(`TauCeti.MorseOrientation.neg`), let `o(TM)` be the orientation local system of `M` with
coefficients in a ring `R` (`TauCeti.VectorBundleOrientationCover.signLocalSystem`), whose fibre
over `x` is a copy of `R` with the two orientations of `T_x M` as opposite generators. Evaluation
at the orientation `ox` followed by `ox'` identifies its fibre at each critical point with `R`.
Read through these identifications, the component from `q` to `p` of the Morse boundary of `-f`
with coefficients in `o(TM)` is multiplication by `(-1) ^ ind_f p` times the coefficient of `q` in
the integral Morse boundary of `p` for `f`
(`IsMorseSmale.signLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg` in the namespace
`TauCeti.IsAdaptedPseudoGradient`):
the factor `τ` of each trajectory is exactly the transport of `o(TM)` along it. So the Morse
complex of `-f` with coefficients in the orientation system is, up to the signs `(-1) ^ ind_f p`,
the dual of the integral Morse complex of `f`, with the degrees exchanged as `k ↔ n - k`, on every
compact manifold. This is the chain-level comparison behind Poincaré duality with coefficients in
the orientation system, which on a nonorientable manifold such as `ℝP²` differs from untwisted
duality: there `H₂(ℝP²; ℤ) = 0` while `H⁰(ℝP²; ℤ) = ℤ`.

## Main definitions

* `TauCeti.IsAdaptedPseudoGradient.criticalOrientation`: the orientation of `T_x M` at a critical
  point given by an orientation of the unstable manifold of `X` followed by one of the unstable
  manifold of `-X`.
* `TauCeti.MorseOrientation.neg`: orientation data for `-X` in the negated Morse charts of `𝔬`, with
  chosen orientations.

## Main results

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `neg_trajectorySign_eq_ite_orientationTransport`: the sign rule for the reversed
  pseudo-gradient on a manifold that need not be orientable.
* `IsMorseSmale.signLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg`: the Morse boundary of `-f`
  with coefficients in the orientation system is the signed transpose of the integral Morse
  boundary of `f`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations) and §3, Exercise 5 (the Morse complex of
  `-f` and Poincaré duality).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (Poincaré duality with
  coefficients in the orientation system).
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-! ### Cutting a path at its midpoint -/

section Halves

variable {α : Type*} [TopologicalSpace α] {a b m : α}

/-- The first half of a path, ending at its midpoint `m`. -/
private noncomputable def firstHalf (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    Path a m where
  toFun t := γ ⟨(t : ℝ) / 2, by have := t.property.1; positivity,
    by have := t.property.2; linarith⟩
  continuous_toFun := γ.continuous.comp (by fun_prop)
  source' := by
    convert γ.source using 2
    ext
    simp
  target' := by
    convert hm using 2

/-- The second half of a path, starting at its midpoint `m`. -/
private noncomputable def secondHalf (γ : Path a b) (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    Path m b where
  toFun t := γ ⟨(1 + (t : ℝ)) / 2, by have := t.property.1; positivity,
    by have := t.property.2; linarith⟩
  continuous_toFun := γ.continuous.comp (by fun_prop)
  source' := by
    convert hm using 2
    ext
    simp
  target' := by
    convert γ.target using 2
    ext
    norm_num

private theorem firstHalf_trans_secondHalf (γ : Path a b)
    (hm : γ ⟨1 / 2, by norm_num, by norm_num⟩ = m) :
    (firstHalf γ hm).trans (secondHalf γ hm) = γ := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  -- Both halves are `γ` at a reparametrized time; unfold them to compare the times.
  · change γ _ = γ t
    congr 1
    ext
    simp only
    ring
  · change γ _ = γ t
    congr 1
    ext
    simp only
    ring

end Halves

namespace IsAdaptedPseudoGradient

/-- The path traced by a connecting trajectory of `X` lies in the unstable manifold of its start
before its end. -/
private theorem connectingPath_mem_unstableSet {hX : IsAdaptedPseudoGradient f X} {p q y : M}
    (hpu : p ∈ hX.flow.unstableSet p) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    {s : unitInterval} (hs : (s : ℝ) < 1) :
    Flow.connectingPath hy.1 hy.2 s ∈ hX.flow.unstableSet p := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rwa [Path.source]
  · rw [Flow.connectingPath_apply_of_mem_Ioo hy.1 hy.2 ⟨unitInterval.pos_iff_ne_zero.2 hs0, hs⟩,
      Flow.apply_mem_unstableSet_iff]
    exact hy.1

/-- The path traced by a connecting trajectory of `X` lies in the stable manifold of its end after
its start. -/
private theorem connectingPath_mem_stableSet {hX : IsAdaptedPseudoGradient f X} {p q y : M}
    (hqs : q ∈ hX.flow.stableSet q) (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    {s : unitInterval} (hs : 0 < (s : ℝ)) :
    Flow.connectingPath hy.1 hy.2 s ∈ hX.flow.stableSet q := by
  rcases eq_or_ne s 1 with rfl | hs1
  · rwa [Path.target]
  · rw [Flow.connectingPath_apply_of_mem_Ioo hy.1 hy.2
      ⟨hs, unitInterval.lt_one_iff_ne_one.2 hs1⟩, Flow.apply_mem_stableSet_iff]
    exact hy.2

/-! ### The orientation at a critical point -/

section CriticalOrientation

variable (hX : IsAdaptedPseudoGradient f X) {x : M} {φ : MorseChart E f x}
  (hφ : ∀ y ∈ φ.toChart.source,
    φ.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φ.toChart y (X y)) =
      fun i ↦ -(φ.weight i * φ.coord (φ.toChart y) i))

/-- The orientation of `T_x M` at a critical point `x` given by an orientation `op` of the
coordinates of negative weight of a Morse chart, the unstable directions of `X`, followed by an
orientation `op'` of those of positive weight, the unstable directions of `-X`: the frame
orientation `unstableFrameOrientation` at `x`, indexed by `Fin n` for the dimension `n` of `M`. -/
noncomputable def criticalOrientation (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x))) :
    Orientation ℝ (TangentSpace 𝓘(ℝ, E) x) (Fin (Module.finrank ℝ E)) :=
  Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
      hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
    (unstableFrameOrientation hφ hf hx op op' (hX.mem_unstableSet_self hx.mem_criticalPoints))

/-- The defining formula of `criticalOrientation`. -/
theorem criticalOrientation_def (hf : IsMorse 𝓘(ℝ, E) f)
    (hx : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f x)
    (op : Orientation ℝ ({i // φ.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f x)))
    (op' : Orientation ℝ ({i // (φ.neg hx).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) x))) :
    hX.criticalOrientation hφ hf hx op op' =
      Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
          hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
        (unstableFrameOrientation hφ hf hx op op'
          (hX.mem_unstableSet_self hx.mem_criticalPoints)) :=
  (rfl)

end CriticalOrientation

/-! ### The sign rule without an orientation of `M` -/

section SignRule

variable {hX : IsAdaptedPseudoGradient f X} {p q : M} {φp : MorseChart E f p}
  {φq : MorseChart E f q}
  (hφp : ∀ y ∈ φp.toChart.source,
    φp.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φp.toChart y (X y)) =
      fun i ↦ -(φp.weight i * φp.coord (φp.toChart y) i))
  (hφq : ∀ y ∈ φq.toChart.source,
    φq.coord (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) φq.toChart y (X y)) =
      fun i ↦ -(φq.weight i * φq.coord (φq.toChart y) i))
  (hf : IsMorse 𝓘(ℝ, E) f) (hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p)
  (hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q)
  (op : Orientation ℝ ({i // φp.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f p)))
  (op' : Orientation ℝ ({i // (φp.neg hp).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
  (oq : Orientation ℝ ({i // φq.weight i < 0} → ℝ) (Fin (manifoldMorseIndex 𝓘(ℝ, E) f q)))
  (oq' : Orientation ℝ ({i // (φq.neg hq).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) q)))

include hφp hφq

open scoped Classical in
/-- Along the path traced by a trajectory from `p` to `q` through `y`, orientation transport
carries the orientation at `p` given by `op` and `op'` to the orientation at `q` given by `oq` and
`oq'` exactly when the two frame orientations at `y` compared by the sign rule
`neg_trajectorySign` agree, up to the sign `(-1) ^ (ind_f q * ind_{-f} q)` of exchanging the
factors at `q`. -/
private theorem orientationTransport_connectingPath_criticalOrientation
    {y : M} (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    VectorBundleOrientationCover.orientationTransport (TangentSpace 𝓘(ℝ, E) : M → Type _)
        (Fintype.card_fin _) (Flow.connectingPath hy.1 hy.2)
        (hX.criticalOrientation hφp hf hp op op') =
      ((-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) q) *
        (if Orientation.reindex ℝ (TangentSpace 𝓘(ℝ, E) y) (finCongr (by
              rw [hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq, hpq]; ring))
            (stableNormalOrientation hφq hf hq oq' oq hy.2) =
          unstableFrameOrientation hφp hf hp op op' hy.1 then 1 else -1)) •
        hX.criticalOrientation hφq hf hq oq oq' := by
  have hpu := hX.mem_unstableSet_self hp.mem_criticalPoints
  have hqs := hX.mem_stableSet_self hq.mem_criticalPoints
  have hqu := hX.mem_unstableSet_self hq.mem_criticalPoints
  set γ := Flow.connectingPath hy.1 hy.2
  have hm := Flow.connectingPath_apply_half hy.1 hy.2
  -- Cut the path at `y`: the first half lies in `W^u(p)`, the second in `W^s(q)`.
  have h₁ : ∀ t, firstHalf γ hm t ∈ hX.flow.unstableSet p := fun t ↦
    connectingPath_mem_unstableSet hpu hy (s := ⟨(t : ℝ) / 2,
      by have := t.property.1; positivity, by have := t.property.2; linarith⟩)
      -- The time of `firstHalf γ hm t` on `γ` is `t / 2`.
      (by have := t.property.2; change (t : ℝ) / 2 < 1; linarith)
  have h₂ : ∀ t, secondHalf γ hm t ∈ hX.flow.stableSet q := fun t ↦
    connectingPath_mem_stableSet hqs hy (s := ⟨(1 + (t : ℝ)) / 2,
      by have := t.property.1; positivity, by have := t.property.2; linarith⟩)
      -- The time of `secondHalf γ hm t` on `γ` is `(1 + t) / 2`.
      (by have := t.property.1; change 0 < (1 + (t : ℝ)) / 2; linarith)
  have T₁ := orientationTransport_unstableFrameOrientation hφp hf hp op op'
    (finCongr ((add_comm _ _).trans hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
    (firstHalf γ hm) h₁ hpu hy.1
  have T₂ := orientationTransport_stableNormalOrientation hφq hf hq oq' oq
    (finCongr hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank) (secondHalf γ hm) h₂
    hy.2 hqs
  -- At `q` the frame orientation along `W^s(q)` is the one along `W^u(q)` up to the exchange sign.
  have hself : Orientation.reindex ℝ _
      (finCongr hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank)
      (stableNormalOrientation hφq hf hq oq' oq hqs) =
      (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) q) •
        hX.criticalOrientation hφq hf hq oq oq' := by
    rw [stableNormalOrientation_self hφq hf hq oq oq' hqs hqu, Orientation.reindex_units_smul,
      criticalOrientation_def, Orientation.reindex_finCongr_reindex_finCongr]
  rw [← firstHalf_trans_secondHalf γ hm, VectorBundleOrientationCover.orientationTransport_trans,
    Equiv.trans_apply, criticalOrientation_def, T₁]
  -- Compare the two frame orientations at `y`, both indexed by `Fin n`.
  split_ifs with hc
  · rw [← hc, Orientation.reindex_finCongr_reindex_finCongr, T₂, hself, mul_one]
  · have hc' : Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
          hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))
          (unstableFrameOrientation hφp hf hp op op' hy.1) =
        -Orientation.reindex ℝ _
          (finCongr hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank)
          (stableNormalOrientation hφq hf hq oq' oq hy.2) := by
      refine (Orientation.eq_or_eq_neg _ _ (by simp)).resolve_left fun h ↦ hc ?_
      apply (Orientation.reindex ℝ _ (finCongr ((add_comm _ _).trans
        hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank))).injective
      rw [h, Orientation.reindex_finCongr_reindex_finCongr]
    rw [hc', VectorBundleOrientationCover.orientationTransport_neg, T₂, hself, mul_neg_one]
    exact (Module.Ray.neg_units_smul _ _).symm

open scoped Classical in
/-- **The sign rule for the reversed pseudo-gradient, without an orientation of `M`.** Let `y` be a
point of a trajectory of `X` from `p` to `q`, with `ind p = ind q + 1`. Orient `T_p M` by `op`
followed by `op'` and `T_q M` by `oq` followed by `oq'` (`criticalOrientation`). If orientation
transport along the path traced by the trajectory carries the first to the second, the trajectory
counts for `-f` with `(-1) ^ ind_f p` times its sign for `f`; otherwise with the opposite sign. -/
theorem neg_trajectorySign_eq_ite_orientationTransport (hMS : hX.IsMorseSmale)
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet p ∩ hX.flow.stableSet q) :
    (hX.neg hf).trajectorySign (φq.neg hq) (φp.neg hp) oq' op'
        (hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq) y =
      (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
        (if VectorBundleOrientationCover.orientationTransport
            (TangentSpace 𝓘(ℝ, E) : M → Type _) (Fintype.card_fin _)
            (Flow.connectingPath hy.1 hy.2) (hX.criticalOrientation hφp hf hp op op') =
          hX.criticalOrientation hφq hf hq oq oq' then 1 else -1) *
        hX.trajectorySign φp φq op oq hpq y := by
  have hT := orientationTransport_connectingPath_criticalOrientation hφp hφq hf hp hq op op' oq oq'
    hy hpq
  rw [neg_trajectorySign hφp hφq hMS hf hp hq hpq hy op op' oq oq', hT]
  have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q = manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 :=
    hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq
  set Θ := hX.criticalOrientation hφq hf hq oq oq'
  set k := manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) p
  -- Since `ind_{-f} q = ind_{-f} p + 1`, `(-1) ^ (ind_f q * ind_{-f} q) = (-1) ^ (k + ind_f q)`.
  have hk : (-1 : ℝˣ) ^ (manifoldMorseIndex 𝓘(ℝ, E) f q * manifoldMorseIndex 𝓘(ℝ, E) (-f) q) =
      (-1) ^ k * (-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f q := by
    rw [hq', mul_add, mul_one, pow_add]
  have hp' : (-1 : ℤ) ^ manifoldMorseIndex 𝓘(ℝ, E) f p =
      -(-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f q := by
    rw [hpq, pow_succ, mul_neg_one]
  rw [hk, hp']
  have hne : -Θ ≠ Θ := Module.Ray.ne_neg_self Θ |>.symm
  rcases Nat.even_or_odd k with hk' | hk' <;>
    rcases Nat.even_or_odd (manifoldMorseIndex 𝓘(ℝ, E) f q) with hq'' | hq'' <;>
    split_ifs <;>
    simp_all [hk'.neg_one_pow, hq''.neg_one_pow, Module.Ray.neg_units_smul]

end SignRule

end IsAdaptedPseudoGradient

/-! ### Orientation data for the reversed pseudo-gradient -/

namespace MorseOrientation

variable (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)

/-- **Orientation data for `-X` with chosen orientations.** The negated Morse charts of `𝔬`, in
which `-X` is linear, with the orientations `o' p` of their coordinates of negative weight, the
unstable directions of `-X`. On an oriented manifold, choosing for `o' p` the orientation that
completes `𝔬.orientation p` to the orientation of `M` gives the dual orientation data
(`TauCeti.MorseOrientation.dual`); without an orientation there is no preferred choice. -/
-- The body is exposed: the type of `orientation` depends on `chart`, and stating
-- `neg_orientation` needs `(𝔬.neg hf o').chart` to reduce to the negated chart.
@[expose]
noncomputable def neg (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
      Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
        (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
          (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
        (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p))) :
    MorseOrientation (-f) (-X) where
  chart p := (𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property)
  coord_mfderiv_chart _ := (𝔬.chart _).coord_mfderiv_neg (𝔬.coord_mfderiv_chart _) _
  orientation := o'

variable (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
  Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
    (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
    (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The charts of `𝔬.neg hf o'` are the negated charts of `𝔬`. -/
@[simp]
theorem neg_chart (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.neg hf o').chart p = (𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (Set.equivOfEq criticalPoints_neg p).property) :=
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] in
/-- The orientations of `𝔬.neg hf o'` are the chosen orientations `o'`. -/
@[simp]
theorem neg_orientation (p : criticalPoints 𝓘(ℝ, E) (-f)) :
    (𝔬.neg hf o').orientation p = o' p :=
  rfl

end MorseOrientation

/-! ### The Morse boundary of `-f` with coefficients in the orientation system -/

namespace IsAdaptedPseudoGradient


variable {hX : IsAdaptedPseudoGradient f X} (𝔬 : MorseOrientation f X) (hf : IsMorse 𝓘(ℝ, E) f)
  (o' : ∀ p : criticalPoints 𝓘(ℝ, E) (-f),
    Orientation ℝ ({i // ((𝔬.chart (Set.equivOfEq criticalPoints_neg p)).neg
      (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
        (Set.equivOfEq criticalPoints_neg p).property)).weight i < 0} → ℝ)
      (Fin (manifoldMorseIndex 𝓘(ℝ, E) (-f) p)))
  {R : Type*} [Ring R]

/-- **One trajectory of the opposite function with coefficients in the orientation system.** For a
trajectory of `X` from `p` to `q` through `y`, run backwards as a trajectory of `-X`, its sign for
`-f` times transport in `o(TM)` along it, read at the orientations of `q` and `p`, is
`(-1) ^ ind_f p` times its sign for `f`. -/
private theorem trajectorySign_smul_signLocalSystemFiberEquiv_transport (hMS : hX.IsMorseSmale)
    (q p : criticalPoints 𝓘(ℝ, E) (-f))
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg p) =
      manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg q) + 1)
    (hqp : manifoldMorseIndex 𝓘(ℝ, E) (-f) q = manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1) {y : M}
    (hy : y ∈ hX.flow.unstableSet (Set.equivOfEq criticalPoints_neg p : M) ∩
      hX.flow.stableSet (Set.equivOfEq criticalPoints_neg q : M))
    (P : Path.Homotopic.Quotient (q : M) p)
    (hP : P = .mk (Flow.connectingPath hy.1 hy.2).symm)
    (c : (VectorBundleOrientationCover.signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type _) R
      (Fintype.card_fin (Module.finrank ℝ E))).obj (FundamentalGroupoid.mk (q : M))) :
    (hX.neg hf).trajectorySign ((𝔬.neg hf o').chart q) ((𝔬.neg hf o').chart p)
        ((𝔬.neg hf o').orientation q) ((𝔬.neg hf o').orientation p) hqp y •
      VectorBundleOrientationCover.signLocalSystemFiberEquiv (Fintype.card_fin _)
        (hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf
          (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
            (Set.equivOfEq criticalPoints_neg p).property)
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))
        (LocalCoefficientSystem.transport (VectorBundleOrientationCover.signLocalSystem E
          (TangentSpace 𝓘(ℝ, E) : M → Type _) R (Fintype.card_fin _)) P c) =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
          hX.trajectorySign (𝔬.chart (Set.equivOfEq criticalPoints_neg p))
            (𝔬.chart (Set.equivOfEq criticalPoints_neg q))
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg p))
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) hpq y) •
        VectorBundleOrientationCover.signLocalSystemFiberEquiv (Fintype.card_fin _)
          (hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf
            (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
              (Set.equivOfEq criticalPoints_neg q).property)
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)) c := by
  subst hP
  set Θp := hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p))
    hf _ (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p)
  set Θq := hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q))
    hf _ (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)
  set γ := Flow.connectingPath hy.1 hy.2
  have hsign := neg_trajectorySign_eq_ite_orientationTransport
    (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p))
    (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf _ _
    (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p)
    (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q) hMS hpq hy
  have hpe : manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg p) =
      manifoldMorseIndex 𝓘(ℝ, E) f p := rfl
  -- The fibres over `p` and over its image in the critical points of `f` are the same, so the
  -- steps below are made by unification rather than by rewriting.
  by_cases hT : VectorBundleOrientationCover.orientationTransport
    (TangentSpace 𝓘(ℝ, E) : M → Type _) (Fintype.card_fin _) γ Θp = Θq
  · -- Transport along the trajectory keeps the orientations.
    refine (congrArg _ (VectorBundleOrientationCover.signLocalSystemFiberEquiv_transport_mk
      (R := R) (Fintype.card_fin _) γ.symm (o := Θq) (o' := Θp) (by
        rw [VectorBundleOrientationCover.orientationTransport_symm, Equiv.symm_apply_eq, hT])
      c)).trans ?_
    congr 1
    -- `hsign` is stated at the point `y` of `M`, the goal at its image in the slice of `-X`.
    erw [hsign]
    rw [ite_eq_left hT, hpe, mul_one]
  · -- Transport along the trajectory reverses the orientations.
    have hT' : VectorBundleOrientationCover.orientationTransport
        (TangentSpace 𝓘(ℝ, E) : M → Type _) (Fintype.card_fin _) γ Θp = -Θq :=
      ((VectorBundleOrientationCover.orientationTransport _ _ γ Θp).eq_or_eq_neg Θq
        (by simp)).resolve_left hT
    refine (congrArg _ ((VectorBundleOrientationCover.signLocalSystemFiberEquiv_transport_mk
      (R := R) (Fintype.card_fin _) γ.symm (o := -Θq) (o' := Θp) (by
        rw [VectorBundleOrientationCover.orientationTransport_symm, Equiv.symm_apply_eq, hT'])
      c).trans (VectorBundleOrientationCover.signLocalSystemFiberEquiv_neg _ Θq c))).trans
      ((smul_neg _ _).trans ((neg_smul _ _).symm.trans ?_))
    congr 1
    -- `hsign` is stated at the point `y` of `M`, the goal at its image in the slice of `-X`.
    erw [hsign]
    rw [ite_eq_right hT, hpe]
    ring

/-- **The Morse boundary of `-f` with coefficients in the orientation system.** Let `o(TM)` be the
orientation local system of `M` with coefficients in `R`. Orient `T_p M`, at each critical point
`p`, by `𝔬.orientation p` followed by `o' p` (`criticalOrientation`), and read the fibre of `o(TM)`
at `p` as `R` by evaluation at this orientation. Then the component from `q` to `p` of the Morse
boundary of `-f`, for the orientation data `𝔬.neg hf o'` and with coefficients in `o(TM)`, is
multiplication by `(-1) ^ ind_f p` times the coefficient of `q` in the integral Morse boundary of
`p` for `f`. No orientation of `M` is assumed: the transport of `o(TM)` along each trajectory
cancels the twist in its sign (`neg_trajectorySign_eq_ite_orientationTransport`). -/
theorem IsMorseSmale.signLocalSystemFiberEquiv_twistedMorseBoundaryMap_neg
    (hMS : hX.IsMorseSmale) (q p : criticalPoints 𝓘(ℝ, E) (-f))
    (c : (VectorBundleOrientationCover.signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type _) R
      (Fintype.card_fin (Module.finrank ℝ E))).obj (FundamentalGroupoid.mk (q : M))) :
    VectorBundleOrientationCover.signLocalSystemFiberEquiv (Fintype.card_fin _)
        (hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg p)) hf
          (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
            (Set.equivOfEq criticalPoints_neg p).property)
          (𝔬.orientation (Set.equivOfEq criticalPoints_neg p)) (o' p))
        ((hX.neg hf).twistedMorseBoundaryMap (𝔬.neg hf o')
          (VectorBundleOrientationCover.signLocalSystem E (TangentSpace 𝓘(ℝ, E) : M → Type _) R
            (Fintype.card_fin _)) q p c) =
      ((-1) ^ manifoldMorseIndex 𝓘(ℝ, E) f p *
          hX.signedMorseBoundaryCoeff 𝔬 (Set.equivOfEq criticalPoints_neg p)
            (Set.equivOfEq criticalPoints_neg q) : ℤ) •
        VectorBundleOrientationCover.signLocalSystemFiberEquiv (Fintype.card_fin _)
          (hX.criticalOrientation (𝔬.coord_mfderiv_chart (Set.equivOfEq criticalPoints_neg q)) hf
            (hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
              (Set.equivOfEq criticalPoints_neg q).property)
            (𝔬.orientation (Set.equivOfEq criticalPoints_neg q)) (o' q)) c := by
  have hp : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f p :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg p).property
  have hq : IsManifoldNondegenerateCriticalPoint 𝓘(ℝ, E) f q :=
    hf.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints
      (Set.equivOfEq criticalPoints_neg q).property
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · have hqp := hp.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one hq hpq
    have hpq' : manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg p) =
        manifoldMorseIndex 𝓘(ℝ, E) f (Set.equivOfEq criticalPoints_neg q) + 1 := hpq
    have := (hMS.finite_morseTrajectorySlice hf hpq').to_subtype
    have := Fintype.ofFinite (hX.morseTrajectorySlice (Set.equivOfEq criticalPoints_neg p)
      (Set.equivOfEq criticalPoints_neg q))
    rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hqp,
      signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq', signedTrajectoryCount_def,
      ← finsum_subtype_eq_finsum_cond]
    -- Read the trajectories of `-X` from `q` to `p` as those of `X` from `p` to `q`.
    have hslice : ∀ y, y ∈ hX.morseTrajectorySlice (Set.equivOfEq criticalPoints_neg p : M)
        (Set.equivOfEq criticalPoints_neg q) ↔ y ∈ (hX.neg hf).morseTrajectorySlice q p :=
      fun y ↦ (Set.ext_iff.1 (hX.neg_morseTrajectorySlice hf p q) y).symm
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight hslice), finsum_eq_sum_of_fintype,
      finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine (map_sum _ _ _).trans ?_
    rw [Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    have hy := hX.mem_morseTrajectorySlice.1 y.property
    have hy' : (y : M) ∈ hX.flow.unstableSet (Set.equivOfEq criticalPoints_neg p : M) ∩
        hX.flow.stableSet (Set.equivOfEq criticalPoints_neg q : M) := ⟨hy.1, hy.2.1⟩
    refine (map_zsmul _ _ _).trans ?_
    exact trajectorySign_smul_signLocalSystemFiberEquiv_transport 𝔬 hf o' hMS q p hpq' hqp hy' _
      ((hX.neg_trajectoryPathClass hf y _ (Equiv.subtypeEquivRight_apply_coe _ _)).trans (by
        rw [trajectoryPathClass_def]
        exact (Path.Homotopic.Quotient.mk_symm _).symm)) c
  · have hq' : manifoldMorseIndex 𝓘(ℝ, E) (-f) q ≠ manifoldMorseIndex 𝓘(ℝ, E) (-f) p + 1 := by
      have := hp.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      have := hq.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
      omega
    rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hq',
      signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one
        (p := Set.equivOfEq criticalPoints_neg p) (q := Set.equivOfEq criticalPoints_neg q) hpq,
      mul_zero, zero_smul, LinearMap.zero_apply]
    exact map_zero _

end IsAdaptedPseudoGradient

end TauCeti
