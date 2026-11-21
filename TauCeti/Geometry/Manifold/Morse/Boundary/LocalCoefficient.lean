/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.LocalCoefficient
public import TauCeti.Dynamics.Flow.ConnectingOrbit
public import TauCeti.Geometry.Manifold.Morse.Boundary.BrokenSign

/-!
# The Morse boundary with coefficients in a local system

Let `f` be a Morse function on a compact boundaryless manifold `M`, `X` a pseudo-gradient adapted
to `f`, `𝔬 : TauCeti.MorseOrientation f X` a choice of orientations of the unstable manifolds, and
`L` a local coefficient system of `R`-modules on `M` (`TauCeti.LocalCoefficientSystem`), a functor
from the fundamental groupoid of `M` to `R`-modules. This file defines the Morse boundary with
coefficients in `L`: the chains are the families `c` with `c p` in the fibre `L(p)` at each
critical point `p`, and a trajectory from `p` to `q` acts by parallel transport along it,
weighted by its sign.

A trajectory through a point `y` of the middle-level slice from `p` to `q`
(`TauCeti.IsAdaptedPseudoGradient.morseTrajectorySlice`) traces a path from `p` to `q`
(`Flow.connectingPath`), whose homotopy class is
`TauCeti.IsAdaptedPseudoGradient.trajectoryPathClass`. The component `L(p) → L(q)` of the
boundary (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`) is, when
`ind p = ind q + 1`, the sum over these trajectories of their signs
`TauCeti.IsAdaptedPseudoGradient.trajectorySign` times the transports along them, and `0`
otherwise; the boundary (`TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundary`) assembles these
components. As for the integral boundary, the definitions take no Morse–Smale hypothesis, and are
the signed counts of trajectories only when `X` is Morse–Smale.

The main results, all but the reversal formula under the Morse–Smale condition, are:

* **constant coefficients** (`IsMorseSmale.twistedMorseBoundary_constant`): for the constant system
  with fibre `N`, transport is the identity and the boundary is the integral boundary acting on
  `N`-valued chains; for `N = R` it is `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary`
  (`IsMorseSmale.twistedMorseBoundary_constant_eq_signedMorseBoundary`);
* **naturality** (`IsMorseSmale.twistedMorseBoundary_naturality`): a morphism of local systems
  commutes with the boundaries;
* **reversal of orientations** (`twistedMorseBoundaryMap_reverse`, with no Morse–Smale
  hypothesis): reversing the orientations at the critical points of a set `S` changes the sign of
  the component from `p` to `q` once for each of `p` and `q` that lies in `S`;
* **the square of the boundary**
  (`IsMorseSmale.twistedMorseBoundary_twistedMorseBoundary_single_apply`): the component
  `L(p) → L(r)` of `∂ ∘ ∂` is the sum over the broken index-two trajectories from `p` to `r`
  (`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet`) of their signs
  `TauCeti.IsAdaptedPseudoGradient.brokenTrajectorySign` times the transports along their
  concatenated paths (`TauCeti.IsAdaptedPseudoGradient.brokenTrajectoryPathClass`). Hence
  `∂ ∘ ∂ = 0` exactly when these sums vanish
  (`IsMorseSmale.twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero_iff`).

The last statement is the algebraic half of `∂² = 0` with local coefficients. The geometric half is
that the broken trajectories from `p` to `r` are the ends of the compact one-dimensional space of
index-two trajectories, that the two ends of each of its arcs carry opposite signs, and that the
arc is a homotopy between their concatenated paths, so that their transports agree.

## Main definitions

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `trajectoryPathClass`: the homotopy class of the path traced by a trajectory.
* `brokenTrajectoryPathClass`: the homotopy class of the concatenated path of a broken trajectory.
* `twistedMorseBoundaryMap`: the component `L(p) → L(q)` of the twisted Morse boundary.
* `twistedMorseBoundary`: the Morse boundary with coefficients in `L`.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §2.3 (orientations and the Morse complex over `ℤ`).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §3.H (local coefficients).
-/

public section

open CategoryTheory Set
open scoped ContDiff Manifold

universe u v w

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type v} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}
  {R : Type u} [Ring R]

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-! ### Paths along trajectories -/

/-- The homotopy class of the path from `p` to `q` traced by the trajectory through a point `y` of
the middle-level slice of trajectories from `p` to `q` (`Flow.connectingPath`). -/
noncomputable def trajectoryPathClass {p q : M} (y : hX.morseTrajectorySlice p q) :
    Path.Homotopic.Quotient p q :=
  .mk (Flow.connectingPath (hX.mem_morseTrajectorySlice.1 y.2).1
    (hX.mem_morseTrajectorySlice.1 y.2).2.1)

/-- The path class of a trajectory is the class of the path it traces. -/
theorem trajectoryPathClass_def {p q : M} (y : hX.morseTrajectorySlice p q) :
    hX.trajectoryPathClass y =
      .mk (Flow.connectingPath (hX.mem_morseTrajectorySlice.1 y.2).1
        (hX.mem_morseTrajectorySlice.1 y.2).2.1) :=
  (rfl)

/-- The homotopy class of the path from `p` to `r` traced by a broken trajectory `(q, z₁, z₂)`:
the trajectory through `z₁` from `p` to `q` followed by the trajectory through `z₂` from `q` to
`r`. -/
noncomputable def brokenTrajectoryPathClass {p r : M} (x : hX.morseBrokenTrajectorySet p r) :
    Path.Homotopic.Quotient p r :=
  (hX.trajectoryPathClass ⟨x.1.2.1, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.1⟩).trans
    (hX.trajectoryPathClass ⟨x.1.2.2, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.2⟩)

/-- The path class of a broken trajectory is the concatenation of the path classes of its two
components. -/
theorem brokenTrajectoryPathClass_def {p r : M} (x : hX.morseBrokenTrajectorySet p r) :
    hX.brokenTrajectoryPathClass x =
      (hX.trajectoryPathClass ⟨x.1.2.1, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.1⟩).trans
        (hX.trajectoryPathClass ⟨x.1.2.2, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.2⟩) :=
  (rfl)

/-- The broken index-two trajectories from `p` to `r`, sorted by their intermediate critical point
`q`: each is a pair of trajectories from `p` to `q` and from `q` to `r`, with `q` of the
intermediate index. -/
private def brokenTrajectoryEquiv (p r : criticalPoints 𝓘(ℝ, E) f) :
    hX.morseBrokenTrajectorySet p r ≃
      Σ q : {q : criticalPoints 𝓘(ℝ, E) f //
          manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
            manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1},
        hX.morseTrajectorySlice p q × hX.morseTrajectorySlice q r where
  toFun x :=
    ⟨⟨x.1.1, (hX.mem_morseBrokenTrajectorySet.1 x.2).1,
        (hX.mem_morseBrokenTrajectorySet.1 x.2).2.1⟩,
      ⟨x.1.2.1, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.1⟩,
      ⟨x.1.2.2, (hX.mem_morseBrokenTrajectorySet.1 x.2).2.2.2⟩⟩
  invFun s := ⟨(s.1.1, s.2.1.1, s.2.2.1),
    hX.mem_morseBrokenTrajectorySet.2 ⟨s.1.2.1, s.1.2.2, s.2.1.2, s.2.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The twisted boundary -/

variable (𝔬 : MorseOrientation f X) (L : LocalCoefficientSystem.{u, v, w} R (TopCat.of M))

/-- **The component `L(p) → L(q)` of the Morse boundary with coefficients in `L`.** When
`ind p = ind q + 1`, it is the sum over the trajectories from `p` to `q`, read on the middle-level
slice, of their signs times the parallel transports along them; otherwise it is `0`. When `X` is
Morse–Smale the sum is finite; otherwise it is a junk value. -/
noncomputable def twistedMorseBoundaryMap (p q : criticalPoints 𝓘(ℝ, E) f) :
    L.obj (FundamentalGroupoid.mk (p : M)) →ₗ[R] L.obj (FundamentalGroupoid.mk (q : M)) :=
  if hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
    ∑ᶠ y : hX.morseTrajectorySlice p q,
      hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq y •
        (LocalCoefficientSystem.transport L (hX.trajectoryPathClass y)).toLinearMap
  else 0

variable {hX 𝔬 L}

/-- For critical points of consecutive index, the component of the twisted boundary is the sum of
the signed transports along the trajectories. -/
theorem twistedMorseBoundaryMap_of_morseIndex_eq_add_one {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.twistedMorseBoundaryMap 𝔬 L p q =
      ∑ᶠ y : hX.morseTrajectorySlice p q,
        hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq y •
          (LocalCoefficientSystem.transport L (hX.trajectoryPathClass y)).toLinearMap :=
  dite_eq_left hpq

/-- The component of the twisted boundary vanishes unless the index drops by one. -/
@[simp]
theorem twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : ¬manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    hX.twistedMorseBoundaryMap 𝔬 L p q = 0 :=
  dite_eq_right hpq

/-- **Reversing orientations changes the signs of the components of the twisted boundary.**
Reversing the orientations at the critical points of `S` multiplies the component from `p` to `q`
by `-1` for each of `p` and `q` that lies in `S`. -/
theorem twistedMorseBoundaryMap_reverse (S : Set (criticalPoints 𝓘(ℝ, E) f))
    [DecidablePred (· ∈ S)] (p q : criticalPoints 𝓘(ℝ, E) f) :
    hX.twistedMorseBoundaryMap (𝔬.reverse S) L p q =
      ((if p ∈ S then -1 else 1) * (if q ∈ S then -1 else 1) : ℤ) •
        hX.twistedMorseBoundaryMap 𝔬 L p q := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hpq,
      twistedMorseBoundaryMap_of_morseIndex_eq_add_one hpq, MorseOrientation.reverse_orientation,
      MorseOrientation.reverse_orientation]
    by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;>
      simp [hp, hq, MorseOrientation.reverse_chart, finsum_neg_distrib]
  · simp [hpq]

variable (hX 𝔬 L) in
/-- **The Morse boundary with coefficients in a local system `L`.** The `R`-linear map on the
families `c` with `c p ∈ L(p)` at each critical point `p` whose `q`-component is the sum over the
critical points `p` of the components `TauCeti.IsAdaptedPseudoGradient.twistedMorseBoundaryMap`
from `p` to `q` applied to `c p`. When `X` is Morse–Smale, these components are the signed sums of
the transports along the trajectories from `p` to `q`; otherwise they are built from junk values. -/
noncomputable def twistedMorseBoundary (hf : IsMorse 𝓘(ℝ, E) f) :
    ((p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M))) →ₗ[R]
      ((q : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (q : M))) where
  toFun c q := ∑ᶠ p, hX.twistedMorseBoundaryMap 𝔬 L p q (c p)
  map_add' c d := by
    have := hf.finite_criticalPoints.to_subtype
    funext q
    simp only [Pi.add_apply, map_add]
    exact finsum_add_distrib (toFinite _) (toFinite _)
  map_smul' a c := by
    have := hf.finite_criticalPoints.to_subtype
    funext q
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
    exact (smul_finsum' a (toFinite _)).symm

variable (hf : IsMorse 𝓘(ℝ, E) f)

/-- The `q`-component of the twisted boundary of a chain `c` is the sum over the critical points
`p` of the components from `p` to `q` applied to `c p`. -/
theorem twistedMorseBoundary_apply
    (c : (p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M)))
    (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.twistedMorseBoundary 𝔬 L hf c q = ∑ᶠ p, hX.twistedMorseBoundaryMap 𝔬 L p q (c p) :=
  (rfl)

/-- The twisted boundary of a chain supported at one critical point `p` has `q`-component the
component from `p` to `q`. -/
@[simp]
theorem twistedMorseBoundary_single_apply [DecidableEq (criticalPoints 𝓘(ℝ, E) f)]
    (p : criticalPoints 𝓘(ℝ, E) f) (a : L.obj (FundamentalGroupoid.mk (p : M)))
    (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.twistedMorseBoundary 𝔬 L hf (Pi.single p a) q = hX.twistedMorseBoundaryMap 𝔬 L p q a := by
  rw [twistedMorseBoundary_apply, finsum_eq_single _ p fun p' hp' ↦ by
    rw [Pi.single_eq_of_ne hp', map_zero], Pi.single_eq_same]

namespace IsMorseSmale

variable (h : hX.IsMorseSmale)

include h hf in
/-- Under the Morse–Smale condition, the component of the twisted boundary from `p` to `q`, applied
to `a`, is the finite sum of the signed transports of `a` along the trajectories. -/
theorem twistedMorseBoundaryMap_apply {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1)
    (a : L.obj (FundamentalGroupoid.mk (p : M))) :
    hX.twistedMorseBoundaryMap 𝔬 L p q a =
      ∑ᶠ y : hX.morseTrajectorySlice p q,
        hX.trajectorySign (𝔬.chart p) (𝔬.chart q) (𝔬.orientation p) (𝔬.orientation q) hpq y •
          LocalCoefficientSystem.transport L (hX.trajectoryPathClass y) a := by
  have := (h.finite_morseTrajectorySlice hf hpq).to_subtype
  have := Fintype.ofFinite (hX.morseTrajectorySlice p q)
  rw [twistedMorseBoundaryMap_of_morseIndex_eq_add_one hpq, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, LinearEquiv.coe_coe]

include h hf in
/-- **Constant coefficients.** For the constant local system with fibre `N`, the component of the
twisted boundary from `p` to `q` is multiplication by the integral boundary coefficient
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff`: transport along every path is the
identity. -/
theorem twistedMorseBoundaryMap_constant (N : ModuleCat.{w} R) (p q : criticalPoints 𝓘(ℝ, E) f)
    (a : N) :
    hX.twistedMorseBoundaryMap 𝔬
        ((LocalCoefficientSystem.constantFunctor (TopCat.of M)).obj N) p q a =
      hX.signedMorseBoundaryCoeff 𝔬 p q • a := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · have := (h.finite_morseTrajectorySlice hf hpq).to_subtype
    -- The fibres of the constant system are `N` only up to unfolding `constantFunctor`, so the
    -- general formulas are applied to `a : N` in term mode rather than by rewriting.
    refine (h.twistedMorseBoundaryMap_apply hf hpq
      (L := (LocalCoefficientSystem.constantFunctor (TopCat.of M)).obj N) a).trans ?_
    rw [signedMorseBoundaryCoeff_of_morseIndex_eq_add_one hpq, signedTrajectoryCount_def,
      ← finsum_set_coe_eq_finsum_mem, finsum_smul' (toFinite _)]
    simp only [LocalCoefficientSystem.transport_constantFunctor]
    exact finsum_congr fun y ↦ congrArg _ (LinearEquiv.refl_apply a)
  · rw [signedMorseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hpq, zero_smul]
    exact (LinearMap.congr_fun (twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hpq
      (L := (LocalCoefficientSystem.constantFunctor (TopCat.of M)).obj N)) a).trans
        (LinearMap.zero_apply a)

include h in
/-- **Constant coefficients.** For the constant local system with fibre `N`, the twisted boundary
is the integral boundary acting on `N`-valued chains: the `q`-component of the boundary of `c` is
the sum over the critical points `p` of the integral boundary coefficients from `p` to `q` times
`c p`. -/
theorem twistedMorseBoundary_constant (N : ModuleCat.{w} R)
    (c : criticalPoints 𝓘(ℝ, E) f → N) (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.twistedMorseBoundary 𝔬 ((LocalCoefficientSystem.constantFunctor (TopCat.of M)).obj N) hf
        c q =
      ∑ᶠ p, hX.signedMorseBoundaryCoeff 𝔬 p q • c p :=
  finsum_congr fun p ↦ h.twistedMorseBoundaryMap_constant hf N p q (c p)

include h in
/-- **The twisted boundary generalizes the integral boundary.** For the constant local system with
fibre `R`, the twisted boundary of a finitely supported chain is its boundary
`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary` with coefficients in `R`. -/
theorem twistedMorseBoundary_constant_eq_signedMorseBoundary
    (c : criticalPoints 𝓘(ℝ, E) f →₀ R) (q : criticalPoints 𝓘(ℝ, E) f) :
    hX.twistedMorseBoundary 𝔬
        ((LocalCoefficientSystem.constantFunctor (TopCat.of M)).obj (ModuleCat.of R R)) hf
        (fun p ↦ c p) q =
      hX.signedMorseBoundary 𝔬 hf R c q := by
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  rw [h.twistedMorseBoundary_constant hf, signedMorseBoundary_apply,
    Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [zsmul_eq_mul, Int.cast_comm]

include h hf in
/-- **Naturality in the local system.** A morphism of local systems `η : L ⟶ K` commutes with the
components of the twisted boundaries. -/
theorem twistedMorseBoundaryMap_naturality {K : LocalCoefficientSystem.{u, v, w} R (TopCat.of M)}
    (η : L ⟶ K) (p q : criticalPoints 𝓘(ℝ, E) f) (a : L.obj (FundamentalGroupoid.mk (p : M))) :
    η.app (FundamentalGroupoid.mk (q : M)) (hX.twistedMorseBoundaryMap 𝔬 L p q a) =
      hX.twistedMorseBoundaryMap 𝔬 K p q (η.app (FundamentalGroupoid.mk (p : M)) a) := by
  by_cases hpq : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1
  · have := (h.finite_morseTrajectorySlice hf hpq).to_subtype
    rw [h.twistedMorseBoundaryMap_apply hf hpq, h.twistedMorseBoundaryMap_apply hf hpq,
      map_finsum _ (toFinite _)]
    refine finsum_congr fun y ↦ ?_
    rw [map_zsmul, LocalCoefficientSystem.transport_naturality]
  · simp [hpq]

include h in
/-- **Naturality in the local system.** A morphism of local systems `η : L ⟶ K` commutes with the
twisted boundaries. -/
theorem twistedMorseBoundary_naturality {K : LocalCoefficientSystem.{u, v, w} R (TopCat.of M)}
    (η : L ⟶ K) (c : (p : criticalPoints 𝓘(ℝ, E) f) → L.obj (FundamentalGroupoid.mk (p : M)))
    (q : criticalPoints 𝓘(ℝ, E) f) :
    η.app (FundamentalGroupoid.mk (q : M)) (hX.twistedMorseBoundary 𝔬 L hf c q) =
      hX.twistedMorseBoundary 𝔬 K hf (fun p ↦ η.app (FundamentalGroupoid.mk (p : M)) (c p)) q := by
  have := hf.finite_criticalPoints.to_subtype
  rw [twistedMorseBoundary_apply, twistedMorseBoundary_apply, map_finsum _ (toFinite _)]
  exact finsum_congr fun p ↦ h.twistedMorseBoundaryMap_naturality hf η p q (c p)

include h in
/-- **`∂ ∘ ∂` counts broken trajectories with signs and transports.** For the Morse boundary with
coefficients in a local system `L`, the `r`-component of the boundary of the boundary of `a ∈ L(p)`
is the sum over the broken index-two trajectories from `p` to `r` of their signs times the
transports of `a` along their concatenated paths. -/
theorem twistedMorseBoundary_twistedMorseBoundary_single_apply
    [DecidableEq (criticalPoints 𝓘(ℝ, E) f)] (p r : criticalPoints 𝓘(ℝ, E) f)
    (a : L.obj (FundamentalGroupoid.mk (p : M))) :
    hX.twistedMorseBoundary 𝔬 L hf (hX.twistedMorseBoundary 𝔬 L hf (Pi.single p a)) r =
      ∑ᶠ x : hX.morseBrokenTrajectorySet p r,
        hX.brokenTrajectorySign 𝔬 p r x •
          LocalCoefficientSystem.transport L (hX.brokenTrajectoryPathClass x) a := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  have := (h.finite_morseBrokenTrajectorySet hf p r).to_subtype
  set P : criticalPoints 𝓘(ℝ, E) f → Prop := fun q ↦
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1
  have hfin₁ (q : {q // P q}) := (h.finite_morseTrajectorySlice hf q.2.1).to_subtype
  have hfin₂ (q : {q // P q}) := (h.finite_morseTrajectorySlice hf q.2.2).to_subtype
  have := fun q : {q // P q} ↦ Fintype.ofFinite (hX.morseTrajectorySlice p q)
  have := fun q : {q // P q} ↦ Fintype.ofFinite (hX.morseTrajectorySlice q r)
  -- Sort the broken trajectories by their intermediate critical point.
  rw [← finsum_comp_equiv (hX.brokenTrajectoryEquiv p r).symm, finsum_eq_sum_of_fintype,
    Fintype.sum_sigma, twistedMorseBoundary_apply, finsum_eq_sum_of_fintype,
    ← Fintype.sum_subtype_add_sum_subtype P]
  simp only [twistedMorseBoundary_single_apply]
  -- Away from the intermediate index, one of the two components vanishes.
  have hzero : ∑ q : {q // ¬P q},
      hX.twistedMorseBoundaryMap 𝔬 L q r (hX.twistedMorseBoundaryMap 𝔬 L p q a) = 0 := by
    refine Fintype.sum_eq_zero _ fun q ↦ ?_
    rcases not_and_or.1 q.2 with hpq | hqr
    · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hpq, LinearMap.zero_apply,
        map_zero]
    · rw [twistedMorseBoundaryMap_of_not_morseIndex_eq_add_one hqr, LinearMap.zero_apply]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- Through an intermediate critical point `q`, expand both components as finite sums.
  rw [h.twistedMorseBoundaryMap_apply hf q.2.1, finsum_eq_sum_of_fintype, map_sum]
  simp_rw [map_zsmul, h.twistedMorseBoundaryMap_apply hf q.2.2, finsum_eq_sum_of_fintype,
    Finset.smul_sum, smul_smul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y₁ _ ↦ Finset.sum_congr rfl fun y₂ _ ↦ ?_
  rw [brokenTrajectoryPathClass_def, LocalCoefficientSystem.transport_trans,
    LinearEquiv.trans_apply]
  exact congrArg₂ _ (brokenTrajectorySign_of_morseIndex_eq_add_one
    (x := ((q : criticalPoints 𝓘(ℝ, E) f), (y₁ : M), (y₂ : M))) q.2.1 q.2.2).symm rfl

include h in
/-- **`∂² = 0` with local coefficients reduces to broken trajectories.** The Morse boundary with
coefficients in a local system `L` squares to zero exactly when, between any two critical points
`p` and `r`, the signed sum of the transports along the broken index-two trajectories from `p` to
`r` vanishes on `L(p)`. -/
theorem twistedMorseBoundary_comp_twistedMorseBoundary_eq_zero_iff :
    hX.twistedMorseBoundary 𝔬 L hf ∘ₗ hX.twistedMorseBoundary 𝔬 L hf = 0 ↔
      ∀ (p r : criticalPoints 𝓘(ℝ, E) f) (a : L.obj (FundamentalGroupoid.mk (p : M))),
        ∑ᶠ x : hX.morseBrokenTrajectorySet p r,
          hX.brokenTrajectorySign 𝔬 p r x •
            LocalCoefficientSystem.transport L (hX.brokenTrajectoryPathClass x) a = 0 := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  simp_rw [← h.twistedMorseBoundary_twistedMorseBoundary_single_apply hf]
  constructor
  · intro h0 p r a
    simpa using congr_fun (LinearMap.congr_fun h0 (Pi.single p a)) r
  · intro h0
    refine LinearMap.pi_ext fun p a ↦ funext fun r ↦ ?_
    simpa using h0 p r a

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
