/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Coordinates

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import TauCeti.Analysis.Normed.Module.Ball.Exterior

/-!
# Asymptotically Euclidean ends

Let `M` be a manifold modelled on `EuclideanSpace ℝ (Fin n)` whose tangent bundle carries a
Riemannian metric. An *asymptotically Euclidean end* of `M` of decay order `t` consists of an
excision radius `R > 0` and a smooth parametrization `φ` of an open subset of `M` by the exterior
`{x ∈ ℝⁿ : R < ‖x‖}`, injective there with bijective differential, in which the pulled-back metric
coefficients `g_ij(x) = ⟪dφ_x e_i, dφ_x e_j⟫` (`TauCeti.pullbackMetricCoeff`, defined in
`TauCeti.Geometry.Manifold.Riemannian.Pullback.Coordinates`) satisfy
`|∂^α (g_ij - δ_ij)| ≤ C ‖x‖ ^ (-t - |α|)` for `|α| ≤ 2` (Cecchini-Zeidler, Definition 2.1;
Lee-Parker, Sections 8 and 9). Integrability of the scalar curvature on the end is kept separate
from this decay structure and supplied as a hypothesis where needed.

To ensure that `AsymptoticallyEuclideanEnd` carries no unconstrained free data on the excised ball
`{x : ‖x‖ ≤ R}`, the function `toFun : EuclideanSpace ℝ (Fin n) → M` is canonically fixed to
`Classical.choice ⟨toFun 0⟩` on `{x : ‖x‖ ≤ R}`. Two ends therefore agree as soon as they have the
same radius and agree on `{x : R < ‖x‖}` (`AsymptoticallyEuclideanEnd.ext`), while
`AsymptoticallyEuclideanEnd.ofFun` and `AsymptoticallyEuclideanEnd.ofInjectiveMfderiv` build an end
from any parametrization `φ : EuclideanSpace ℝ (Fin n) → M` satisfying the exterior conditions.

A *finite-ended asymptotically Euclidean structure* `FiniteEndedAE n M t` packages a finite
nonempty family of ends whose open images are pairwise disjoint and have compact complement in `M`
(Cecchini-Zeidler, Definition 2.3, boundaryless case). Requiring `0 < numEnds` rules out the empty
family of ends, whose complement would vacuously be `Set.univ` (compact whenever `M` is compact).
In positive dimension `1 ≤ n` with positive decay order `0 < t` on a compact Hausdorff `C¹`
manifold carrying a continuous Riemannian metric, a nonempty end family has infinite Riemannian
volume and therefore excludes closed manifolds such as flat tori (at `n = 0` the coordinate
exterior `{x : radius < ‖x‖}` is empty, and at `t ≤ 0` the decay bound does not force
`g_ij → δ_ij` as `‖x‖ → ∞`).

## Main definitions

* `TauCeti.AsymptoticallyEuclideanEnd`: an asymptotically Euclidean end of decay order `t`.
* `TauCeti.AsymptoticallyEuclideanEnd.ofFun`,
  `TauCeti.AsymptoticallyEuclideanEnd.ofInjectiveMfderiv`: constructors from an arbitrary exterior
  parametrization `φ : ℝⁿ → M`.
* `TauCeti.AsymptoticallyEuclideanEnd.endRadius`: the coordinate radius `‖φ⁻¹(·)‖` on the open end
  image, taking values in `Set.Ioi E.radius`.
* `TauCeti.FiniteEndedAE`: a finite nonempty family of pairwise disjoint asymptotically Euclidean
  ends whose union has compact complement.
* `TauCeti.AsymptoticallyEuclideanEnd.euclidean` and `TauCeti.FiniteEndedAE.euclidean`: flat
  Euclidean space `ℝⁿ` as an asymptotically Euclidean manifold of every order `t`.

## Main results

* `TauCeti.AsymptoticallyEuclideanEnd.isConnected_image`: for `2 ≤ n`, the image of an end is
  connected.
* `TauCeti.AsymptoticallyEuclideanEnd.homeomorphImage` and
  `TauCeti.AsymptoticallyEuclideanEnd.partialDiffeomorph`: on a `C¹` manifold, an end restricts to a
  homeomorphism from `{x : R < ‖x‖}` onto its open image, and on a smooth manifold to a smooth
  partial diffeomorphism.
* `TauCeti.AsymptoticallyEuclideanEnd.isProperMap_endRadius`: on a `C¹` manifold, the coordinate
  radius `‖φ⁻¹(·)‖ : E.image → Set.Ioi E.radius` is a proper map.
* `TauCeti.not_exists_pullbackMetricCoeff_smul_decay` and
  `TauCeti.not_exists_pullbackMetricCoeff_two_smul_decay`: rescaling `x ↦ c • x` (`|c| ≠ 1`, in
  particular `x ↦ 2 • x`) on flat `ℝⁿ` (`1 ≤ n`) does not decay at any positive order `t > 0`.

## References

* S. Cecchini and R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, Trans. Amer. Math. Soc. 377 (2024), 5271-5288 (arXiv:2108.11972), Section 2
  (Definitions 2.1 and 2.3).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37-91,
  Sections 8 and 9.
-/

public section

noncomputable section

open Bundle Function Filter Metric Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace TauCeti

/-! ### Asymptotically Euclidean ends -/

/-- Canonicalize an exterior parametrization `φ : EuclideanSpace ℝ (Fin n) → M` outside the open
exterior `{x | r < ‖x‖}` by setting it to `Classical.choice ⟨φ 0⟩` on `{x | ‖x‖ ≤ r}`. -/
private def canonicalizeExterior {n : ℕ} {M : Type*} (r : ℝ)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n)) : M :=
  open Classical in
  if r < ‖x‖ then φ x else Classical.choice ⟨φ 0⟩

private theorem canonicalizeExterior_of_lt {n : ℕ} {M : Type*} {r : ℝ}
    (φ : EuclideanSpace ℝ (Fin n) → M) {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖) :
    canonicalizeExterior r φ x = φ x := by
  simp [canonicalizeExterior, hx]

private theorem canonicalizeExterior_of_le {n : ℕ} {M : Type*} {r : ℝ}
    (φ : EuclideanSpace ℝ (Fin n) → M) {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ r) :
    canonicalizeExterior r φ x = Classical.choice ⟨canonicalizeExterior r φ 0⟩ := by
  have hx' : ¬ r < ‖x‖ := not_lt.2 hx
  simp only [canonicalizeExterior, hx', ↓reduceIte]

/-- An asymptotically Euclidean end of `M` of order `t`: an excision radius `radius > 0` and a
smooth parametrization `toFun` of an open subset of `M` by `{x : radius < ‖x‖}`, injective there
with bijective differential, in which the metric coefficients satisfy
`|∂^α (g_ij - δ_ij)| ≤ C ‖x‖ ^ (-t - |α|)` for `|α| ≤ 2` (Cecchini-Zeidler, Definition 2.1).
On the excised ball `{x : ‖x‖ ≤ radius}`, `toFun` is canonically fixed to
`Classical.choice ⟨toFun 0⟩` so that an end carries no unconstrained data outside its domain. -/
structure AsymptoticallyEuclideanEnd (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The radius of the excised coordinate ball. -/
  radius : ℝ
  /-- The excised coordinate ball has positive radius. -/
  radius_pos : 0 < radius
  /-- The end parametrization, meaningful on `{x : radius < ‖x‖}` and canonically constant on
  `{x : ‖x‖ ≤ radius}`. -/
  toFun : EuclideanSpace ℝ (Fin n) → M
  /-- On `{x : ‖x‖ ≤ radius}`, `toFun` takes the canonical value `Classical.choice ⟨toFun 0⟩`. -/
  toFun_of_norm_le : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ radius →
    toFun x = Classical.choice ⟨toFun 0⟩
  /-- Smoothness of the parametrization on `{x : radius < ‖x‖}`. -/
  contMDiffOn : ContMDiffOn (𝓡 n) (𝓡 n) ∞ toFun {x | radius < ‖x‖}
  /-- Injectivity of the parametrization on `{x : radius < ‖x‖}`. -/
  injOn : InjOn toFun {x | radius < ‖x‖}
  /-- Openness of the end image in `M`. -/
  isOpen_image_exterior : IsOpen (toFun '' {x | radius < ‖x‖})
  /-- Bijectivity of the differential at every point of `{x : radius < ‖x‖}`. -/
  mfderiv_bijective : ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ →
    Bijective (mfderiv (𝓡 n) (𝓡 n) toFun x)
  /-- Asymptotic Euclidean decay of order `t` up to second derivatives. -/
  decay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), radius < ‖x‖ → ∀ i j : Fin n,
    |pullbackMetricCoeff toFun x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y => pullbackMetricCoeff toFun y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff toFun y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)

namespace AsymptoticallyEuclideanEnd

section Basic

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- Two asymptotically Euclidean ends are equal if and only if they have the same excision radius
and agree on the exterior `{x | radius < ‖x‖}`. -/
@[ext]
theorem ext {E₁ E₂ : AsymptoticallyEuclideanEnd n M t} (hradius : E₁.radius = E₂.radius)
    (htoFun : ∀ x : EuclideanSpace ℝ (Fin n), E₁.radius < ‖x‖ → E₁.toFun x = E₂.toFun x) :
    E₁ = E₂ := by
  rcases E₁ with ⟨r₁, hr₁, f₁, hle₁, hcmd₁, hinj₁, hop₁, hbij₁, hdec₁⟩
  rcases E₂ with ⟨r₂, hr₂, f₂, hle₂, hcmd₂, hinj₂, hop₂, hbij₂, hdec₂⟩
  simp only at hradius htoFun
  subst hradius
  have hne : (⟨f₁ 0⟩ : Nonempty M) = ⟨f₂ 0⟩ := Subsingleton.elim _ _
  have hf : f₁ = f₂ := funext fun x ↦ by
    rcases lt_or_ge r₁ ‖x‖ with hx | hx
    · exact htoFun x hx
    · rw [hle₁ x hx, hle₂ x hx, hne]
  subst hf
  rfl

/-- The coordinate exterior `{x : E.radius < ‖x‖}` is open. -/
theorem isOpen_exterior (E : AsymptoticallyEuclideanEnd n M t) :
    IsOpen {x : EuclideanSpace ℝ (Fin n) | E.radius < ‖x‖} :=
  isOpen_lt continuous_const continuous_norm

/-- The open subset of `M` parametrized by an end `E`. -/
def image (E : AsymptoticallyEuclideanEnd n M t) : Set M :=
  E.toFun '' {x | E.radius < ‖x‖}

/-- Unfolding lemma for `TauCeti.AsymptoticallyEuclideanEnd.image`. -/
theorem image_def (E : AsymptoticallyEuclideanEnd n M t) :
    E.image = E.toFun '' {x | E.radius < ‖x‖} := (rfl)

/-- Membership in `E.image` means being the image under `E.toFun` of an exterior point
`x` with `E.radius < ‖x‖`. -/
theorem mem_image_iff (E : AsymptoticallyEuclideanEnd n M t) {p : M} :
    p ∈ E.image ↔ ∃ x : EuclideanSpace ℝ (Fin n), E.radius < ‖x‖ ∧ E.toFun x = p :=
  Iff.rfl

/-- The image `E.image` of an asymptotically Euclidean end is open in `M`. -/
theorem isOpen_image (E : AsymptoticallyEuclideanEnd n M t) : IsOpen E.image :=
  E.isOpen_image_exterior

/-- Construct an `AsymptoticallyEuclideanEnd` from any parametrization
`φ : EuclideanSpace ℝ (Fin n) → M` satisfying the smoothness, injectivity, open-image,
invertible-differential, and decay conditions on `{x | r < ‖x‖}`. Values of `φ` on `{x | ‖x‖ ≤ r}`
are discarded and replaced by the canonical value. -/
def ofFun (r : ℝ) (hr : 0 < r) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hcmd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | r < ‖x‖}) (hinj : InjOn φ {x | r < ‖x‖})
    (hop : IsOpen (φ '' {x | r < ‖x‖}))
    (hbij : ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → Bijective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t := by
  have hU : IsOpen {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  have heq : EqOn (canonicalizeExterior r φ) φ {x | r < ‖x‖} :=
    fun _ hx ↦ canonicalizeExterior_of_lt φ hx
  refine
    { radius := r
      radius_pos := hr
      toFun := canonicalizeExterior r φ
      toFun_of_norm_le := fun x hx ↦ canonicalizeExterior_of_le φ hx
      contMDiffOn := hcmd.congr heq
      injOn := hinj.congr heq.symm
      isOpen_image_exterior := by rwa [image_congr heq]
      mfderiv_bijective := fun x hx ↦ by
        have hnhds : canonicalizeExterior r φ =ᶠ[𝓝 x] φ :=
          Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq
        rw [hnhds.mfderiv_eq]
        exact (tangentSpaceCast (𝓡 n) (φ x) (canonicalizeExterior r φ x)).bijective.comp
          (hbij x hx)
      decay := by
        obtain ⟨C, hC⟩ := hdecay
        refine ⟨C, fun x hx i j ↦ ?_⟩
        have hg : (fun y ↦ pullbackMetricCoeff (canonicalizeExterior r φ) y i j) =ᶠ[𝓝 x]
            (fun y ↦ pullbackMetricCoeff φ y i j) :=
          pullbackMetricCoeff_eventuallyEq_nhds
            (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) heq) i j
        have hg1 : fderiv ℝ (fun y ↦ pullbackMetricCoeff (canonicalizeExterior r φ) y i j) =ᶠ[𝓝 x]
            fderiv ℝ (fun y ↦ pullbackMetricCoeff φ y i j) := hg.fderiv
        rw [hg.eq_of_nhds, hg.fderiv_eq, hg1.fderiv_eq]
        exact hC x hx i j }

section OfFun

variable {r : ℝ} (hr : 0 < r) (φ : EuclideanSpace ℝ (Fin n) → M)
  (hcmd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | r < ‖x‖})
  (hinj : InjOn φ {x | r < ‖x‖})
  (hop : IsOpen (φ '' {x | r < ‖x‖}))
  (hbij : ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → Bijective (mfderiv (𝓡 n) (𝓡 n) φ x))
  (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
    |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2))

/-- Excision radius of `AsymptoticallyEuclideanEnd.ofFun`. -/
@[simp]
theorem ofFun_radius : (ofFun r hr φ hcmd hinj hop hbij hdecay).radius = r := (rfl)

/-- On `{x | r < ‖x‖}`, `AsymptoticallyEuclideanEnd.ofFun` agrees with `φ`. -/
@[simp]
theorem ofFun_toFun_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖) :
    (ofFun r hr φ hcmd hinj hop hbij hdecay).toFun x = φ x :=
  canonicalizeExterior_of_lt φ hx

/-- End image of `AsymptoticallyEuclideanEnd.ofFun`. -/
@[simp]
theorem ofFun_image : (ofFun r hr φ hcmd hinj hop hbij hdecay).image = φ '' {x | r < ‖x‖} :=
  image_congr fun _ hx ↦ canonicalizeExterior_of_lt φ hx

/-- On `{x | r < ‖x‖}`, `pullbackMetricCoeff` of `AsymptoticallyEuclideanEnd.ofFun` agrees with
that of `φ`. -/
theorem ofFun_pullbackMetricCoeff_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖)
    (i j : Fin n) :
    pullbackMetricCoeff (ofFun r hr φ hcmd hinj hop hbij hdecay).toFun x i j =
      pullbackMetricCoeff φ x i j :=
  pullbackMetricCoeff_congr_nhds
    (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun _ hy ↦ ofFun_toFun_of_lt hr φ hcmd hinj hop hbij hdecay hy)
    i j

end OfFun

/-- Monotonicity in the decay order: an asymptotically Euclidean end of order `t` is also an end of
any order `s ≤ t`, with the same radius and parametrization. -/
def ofLE {s : ℝ} (hst : s ≤ t) (E : AsymptoticallyEuclideanEnd n M t) :
    AsymptoticallyEuclideanEnd n M s where
  radius := E.radius
  radius_pos := E.radius_pos
  toFun := E.toFun
  toFun_of_norm_le := E.toFun_of_norm_le
  contMDiffOn := E.contMDiffOn
  injOn := E.injOn
  isOpen_image_exterior := E.isOpen_image_exterior
  mfderiv_bijective := E.mfderiv_bijective
  decay := by
    obtain ⟨C, hC⟩ := E.decay
    refine ⟨max C 0 * E.radius ^ (s - t), fun x hx i j ↦ ?_⟩
    obtain ⟨h0, h1, h2⟩ := hC x hx i j
    have hr0 : 0 < E.radius := E.radius_pos
    have hx0 : 0 < ‖x‖ := hr0.trans hx
    have hC0 : 0 ≤ max C 0 := le_max_right C 0
    have hrpow (k : ℝ) : ‖x‖ ^ (-t - k) ≤ E.radius ^ (s - t) * ‖x‖ ^ (-s - k) := by
      have hle : (‖x‖ / E.radius) ^ (-t - k) ≤ (‖x‖ / E.radius) ^ (-s - k) :=
        Real.rpow_le_rpow_of_exponent_le ((one_le_div hr0).2 hx.le) (by linarith)
      rw [Real.div_rpow hx0.le hr0.le, Real.div_rpow hx0.le hr0.le,
        div_le_div_iff₀ (Real.rpow_pos_of_pos hr0 _) (Real.rpow_pos_of_pos hr0 _)] at hle
      have hr_pow : E.radius ^ (-t - k) = E.radius ^ (s - t) * E.radius ^ (-s - k) := by
        rw [← Real.rpow_add hr0]; congr 1; ring
      have hexp : ‖x‖ ^ (-s - k) * E.radius ^ (-t - k) =
          (E.radius ^ (s - t) * ‖x‖ ^ (-s - k)) * E.radius ^ (-s - k) := by rw [hr_pow]; ring
      exact le_of_mul_le_mul_right (hle.trans_eq hexp) (Real.rpow_pos_of_pos hr0 (-s - k))
    have hleC (a p : ℝ) (ha : a ≤ C * ‖x‖ ^ p) : a ≤ max C 0 * ‖x‖ ^ p :=
      ha.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hx0.le p))
    refine ⟨?_, ?_, ?_⟩
    · simpa [sub_zero, mul_assoc] using (hleC _ _ h0).trans
        (by simpa [sub_zero] using mul_le_mul_of_nonneg_left (hrpow 0) hC0)
    · exact (hleC _ _ h1).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hrpow 1) hC0)
    · exact (hleC _ _ h2).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hrpow 2) hC0)

@[simp]
theorem ofLE_radius {s : ℝ} (hst : s ≤ t) (E : AsymptoticallyEuclideanEnd n M t) :
    (E.ofLE hst).radius = E.radius := (rfl)

@[simp]
theorem ofLE_toFun {s : ℝ} (hst : s ≤ t) (E : AsymptoticallyEuclideanEnd n M t) :
    (E.ofLE hst).toFun = E.toFun := (rfl)

@[simp]
theorem ofLE_image {s : ℝ} (hst : s ≤ t) (E : AsymptoticallyEuclideanEnd n M t) :
    (E.ofLE hst).image = E.image := (rfl)

/-- Every exterior point `x` with `E.radius < ‖x‖` maps into `E.image`. -/
theorem toFun_mem_image (E : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) : E.toFun x ∈ E.image := ⟨x, hx, rfl⟩

/-- In positive dimension `1 ≤ n`, the coordinate exterior and the end image are nonempty. -/
theorem image_nonempty (hn : 1 ≤ n) (E : AsymptoticallyEuclideanEnd n M t) : E.image.Nonempty := by
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ ⟨0, by omega⟩
  refine ⟨E.toFun ((E.radius + 1) • e₀), (E.radius + 1) • e₀, ?_, rfl⟩
  have he₀ : ‖e₀‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 ⟨0, by omega⟩
  have hpos : 0 < E.radius + 1 := by linarith [E.radius_pos]
  simp only [mem_ofPred_eq, norm_smul, Real.norm_of_nonneg hpos.le, he₀, mul_one]
  linarith

/-- For `2 ≤ n`, the image of an asymptotically Euclidean end is connected. -/
theorem isConnected_image (hn : 2 ≤ n) (E : AsymptoticallyEuclideanEnd n M t) :
    IsConnected E.image := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by omega : 1 < n)
  have hconn : IsConnected {x : EuclideanSpace ℝ (Fin n) | E.radius < ‖x‖} := by
    convert (isPathConnected_compl_closedBall hrank 0 E.radius).isConnected using 1
    ext x
    simp
  exact hconn.image E.toFun E.contMDiffOn.continuousOn

/-- The inverse parametrization on `E.image`, defined via `Function.invFunOn` on
`{x | E.radius < ‖x‖}`. -/
def invFun (E : AsymptoticallyEuclideanEnd n M t) : M → EuclideanSpace ℝ (Fin n) :=
  invFunOn E.toFun {x | E.radius < ‖x‖}

/-- Unfolding lemma for `TauCeti.AsymptoticallyEuclideanEnd.invFun`. -/
theorem invFun_def (E : AsymptoticallyEuclideanEnd n M t) :
    E.invFun = invFunOn E.toFun {x | E.radius < ‖x‖} := (rfl)

/-- Left-inverse law for `AsymptoticallyEuclideanEnd.invFun` on `{x | E.radius < ‖x‖}`. -/
@[simp]
theorem invFun_toFun (E : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) :
    E.invFun (E.toFun x) = x := E.injOn.leftInvOn_invFunOn hx

/-- Right-inverse law for `AsymptoticallyEuclideanEnd.invFun` on `E.image`. -/
@[simp]
theorem toFun_invFun (E : AsymptoticallyEuclideanEnd n M t) {p : M} (hp : p ∈ E.image) :
    E.toFun (E.invFun p) = p := invFunOn_eq hp

/-- For `p ∈ E.image`, `E.invFun p` lies in `{x | E.radius < ‖x‖}`. -/
theorem radius_lt_norm_invFun (E : AsymptoticallyEuclideanEnd n M t) {p : M} (hp : p ∈ E.image) :
    E.radius < ‖E.invFun p‖ := invFunOn_mem hp

/-- The end coordinate radius `‖φ⁻¹(p)‖` on `E.image`, taking values in `Set.Ioi E.radius`. -/
def endRadius (E : AsymptoticallyEuclideanEnd n M t) (p : E.image) : Ioi E.radius :=
  ⟨‖E.invFun p‖, E.radius_lt_norm_invFun p.2⟩

/-- Coercion of `TauCeti.AsymptoticallyEuclideanEnd.endRadius` to `ℝ`. -/
theorem coe_endRadius (E : AsymptoticallyEuclideanEnd n M t) (p : E.image) :
    (E.endRadius p : ℝ) = ‖E.invFun p‖ := (rfl)

/-- Evaluating `E.endRadius` at `E.toFun x` recovers `‖x‖`. -/
@[simp]
theorem coe_endRadius_toFun (E : AsymptoticallyEuclideanEnd n M t)
    {x : EuclideanSpace ℝ (Fin n)} (hx : E.radius < ‖x‖) :
    (E.endRadius ⟨E.toFun x, E.toFun_mem_image hx⟩ : ℝ) = ‖x‖ := by
  rw [coe_endRadius, invFun_toFun E hx]

end Basic

/-! ### Local diffeomorphism, inverse chart and properness of the end radius -/

section ManifoldOne

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

private theorem isLocalDiffeomorphOn_one (E : AsymptoticallyEuclideanEnd n M t) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) 1 E.toFun {x | E.radius < ‖x‖} := fun ⟨x, hx⟩ ↦
  isLocalDiffeomorphAt_of_injective_mfderiv (E.contMDiffOn.of_le (by simp)) E.isOpen_exterior hx
    BoundarylessManifold.isInteriorPoint le_rfl (E.mfderiv_bijective x hx).injective rfl

/-- Construct an `AsymptoticallyEuclideanEnd` on a `C¹` manifold `M` from a smooth injective map
on `{x | r < ‖x‖}` whose differential is everywhere injective there. Both surjectivity of the
differential and openness of the image follow automatically from the manifold inverse function
theorem in equal finite dimensions. -/
def ofInjectiveMfderiv (r : ℝ) (hr : 0 < r) (φ : EuclideanSpace ℝ (Fin n) → M)
    (hcmd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | r < ‖x‖}) (hinj : InjOn φ {x | r < ‖x‖})
    (hmf : ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → Injective (mfderiv (𝓡 n) (𝓡 n) φ x))
    (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
      ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2)) :
    AsymptoticallyEuclideanEnd n M t := by
  have hU : IsOpen {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖} :=
    isOpen_lt continuous_const continuous_norm
  have hloc : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) 1 φ {x | r < ‖x‖} := fun ⟨x, hx⟩ ↦
    isLocalDiffeomorphAt_of_injective_mfderiv (hcmd.of_le (by simp)) hU hx
      BoundarylessManifold.isInteriorPoint le_rfl (hmf x hx) rfl
  exact ofFun r hr φ hcmd hinj (hloc.isLocalHomeomorphOn.isOpen_image hU)
    (fun x hx ↦ ((hloc ⟨x, hx⟩).isInvertible_mfderiv one_ne_zero).bijective) hdecay

section OfInjectiveMfderiv

variable {r : ℝ} (hr : 0 < r) (φ : EuclideanSpace ℝ (Fin n) → M)
  (hcmd : ContMDiffOn (𝓡 n) (𝓡 n) ∞ φ {x | r < ‖x‖}) (hinj : InjOn φ {x | r < ‖x‖})
  (hmf : ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → Injective (mfderiv (𝓡 n) (𝓡 n) φ x))
  (hdecay : ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
    |pullbackMetricCoeff φ x i j - if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) ∧
    ‖fderiv ℝ (fun y => pullbackMetricCoeff φ y i j) x‖ ≤ C * ‖x‖ ^ (-t - 1) ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => pullbackMetricCoeff φ y i j)) x‖ ≤ C * ‖x‖ ^ (-t - 2))

@[simp]
theorem ofInjectiveMfderiv_radius :
    (ofInjectiveMfderiv r hr φ hcmd hinj hmf hdecay).radius = r := (rfl)

@[simp]
theorem ofInjectiveMfderiv_toFun_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖) :
    (ofInjectiveMfderiv r hr φ hcmd hinj hmf hdecay).toFun x = φ x :=
  canonicalizeExterior_of_lt φ hx

@[simp]
theorem ofInjectiveMfderiv_image :
    (ofInjectiveMfderiv r hr φ hcmd hinj hmf hdecay).image = φ '' {x | r < ‖x‖} :=
  image_congr fun _ hx ↦ canonicalizeExterior_of_lt φ hx

/-- On `{x | r < ‖x‖}`, `pullbackMetricCoeff` of `AsymptoticallyEuclideanEnd.ofInjectiveMfderiv`
agrees with that of `φ`. -/
theorem ofInjectiveMfderiv_pullbackMetricCoeff_of_lt {x : EuclideanSpace ℝ (Fin n)} (hx : r < ‖x‖)
    (i j : Fin n) :
    pullbackMetricCoeff (ofInjectiveMfderiv r hr φ hcmd hinj hmf hdecay).toFun x i j =
      pullbackMetricCoeff φ x i j :=
  pullbackMetricCoeff_congr_nhds
    (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun _ hy ↦ ofInjectiveMfderiv_toFun_of_lt hr φ hcmd hinj hmf hdecay hy)
    i j

end OfInjectiveMfderiv

/-- Restrict an asymptotically Euclidean end to a larger excision radius `r' ≥ E.radius`. -/
def increaseRadius {r' : ℝ} (E : AsymptoticallyEuclideanEnd n M t) (hr' : E.radius ≤ r') :
    AsymptoticallyEuclideanEnd n M t :=
  have hsub : {x : EuclideanSpace ℝ (Fin n) | r' < ‖x‖} ⊆ {x | E.radius < ‖x‖} :=
    fun _ hx ↦ hr'.trans_lt hx
  ofInjectiveMfderiv r' (E.radius_pos.trans_le hr') E.toFun (E.contMDiffOn.mono hsub)
    (E.injOn.mono hsub) (fun x hx ↦ (E.mfderiv_bijective x (hsub hx)).injective)
    (let ⟨C, hC⟩ := E.decay; ⟨C, fun x hx ↦ hC x (hsub hx)⟩)

/-- Excision radius of `AsymptoticallyEuclideanEnd.increaseRadius`. -/
@[simp]
theorem increaseRadius_radius {r' : ℝ} (E : AsymptoticallyEuclideanEnd n M t)
    (hr' : E.radius ≤ r') :
    (E.increaseRadius hr').radius = r' := (rfl)

/-- On `{x | r' < ‖x‖}`, `E.increaseRadius hr'` agrees with `E.toFun`. -/
@[simp]
theorem increaseRadius_toFun_of_lt {r' : ℝ} (E : AsymptoticallyEuclideanEnd n M t)
    (hr' : E.radius ≤ r') {x : EuclideanSpace ℝ (Fin n)} (hx : r' < ‖x‖) :
    (E.increaseRadius hr').toFun x = E.toFun x := by
  simp [increaseRadius, hx]

/-- End image of `AsymptoticallyEuclideanEnd.increaseRadius`. -/
@[simp]
theorem increaseRadius_image {r' : ℝ} (E : AsymptoticallyEuclideanEnd n M t)
    (hr' : E.radius ≤ r') :
    (E.increaseRadius hr').image = E.toFun '' {x | r' < ‖x‖} := by
  simp [increaseRadius]

/-- On `{x | r' < ‖x‖}`, `pullbackMetricCoeff` of `E.increaseRadius hr'` agrees with that of
`E.toFun`. -/
theorem increaseRadius_pullbackMetricCoeff_of_lt {r' : ℝ} (E : AsymptoticallyEuclideanEnd n M t)
    (hr' : E.radius ≤ r') {x : EuclideanSpace ℝ (Fin n)} (hx : r' < ‖x‖) (i j : Fin n) :
    pullbackMetricCoeff (E.increaseRadius hr').toFun x i j =
      pullbackMetricCoeff E.toFun x i j :=
  pullbackMetricCoeff_congr_nhds
    (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hx)
      fun _ hy ↦ E.increaseRadius_toFun_of_lt hr' hy)
    i j

/-- The homeomorphism from the coordinate exterior `{x | E.radius < ‖x‖}` onto `E.image`. -/
def homeomorphImage (E : AsymptoticallyEuclideanEnd n M t) :
    ({x : EuclideanSpace ℝ (Fin n) | E.radius < ‖x‖} : Set (EuclideanSpace ℝ (Fin n))) ≃ₜ
      E.image :=
  (E.isLocalDiffeomorphOn_one.partialDiffeomorphOfInjOn E.isOpen_exterior
    E.injOn).toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
    (by simp) (by simp [image_def])

@[simp]
theorem coe_homeomorphImage_apply (E : AsymptoticallyEuclideanEnd n M t)
    (x : ({x : EuclideanSpace ℝ (Fin n) | E.radius < ‖x‖} : Set (EuclideanSpace ℝ (Fin n)))) :
    (E.homeomorphImage x : M) = E.toFun x := by
  simp [homeomorphImage]

@[simp]
theorem coe_homeomorphImage_symm_apply (E : AsymptoticallyEuclideanEnd n M t) (p : E.image) :
    (E.homeomorphImage.symm p : EuclideanSpace ℝ (Fin n)) = E.invFun p := by
  simp [homeomorphImage, invFun_def]

/-- **Properness of the end radius.** On a `C¹` manifold, the coordinate radius
`E.endRadius : E.image → Set.Ioi E.radius` is a proper map. -/
theorem isProperMap_endRadius (E : AsymptoticallyEuclideanEnd n M t) :
    IsProperMap E.endRadius := by
  have hnorm : IsProperMap (norm : EuclideanSpace ℝ (Fin n) → ℝ) := by
    simpa only [dist_zero] using isProperMap_dist (0 : EuclideanSpace ℝ (Fin n))
  let g := (Ioi E.radius).restrictPreimage (norm : EuclideanSpace ℝ (Fin n) → ℝ)
  have hg : IsProperMap g := hnorm.restrictPreimage (Ioi E.radius)
  have hp : IsProperMap (g ∘ E.homeomorphImage.symm) :=
    hg.comp E.homeomorphImage.symm.isProperMap
  have heq : g ∘ E.homeomorphImage.symm = E.endRadius :=
    funext fun p ↦ Subtype.ext <|
      (Set.restrictPreimage_coe (Ioi E.radius) norm (E.homeomorphImage.symm p)).trans <|
        (congrArg norm (E.coe_homeomorphImage_symm_apply p)).trans (E.coe_endRadius p).symm
  exact heq ▸ hp

end ManifoldOne

section ManifoldSmooth

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- On a smooth manifold `M`, an asymptotically Euclidean end is a smooth local diffeomorphism at
every point of `{x | E.radius < ‖x‖}`. -/
theorem isLocalDiffeomorphOn (E : AsymptoticallyEuclideanEnd n M t) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ E.toFun {x | E.radius < ‖x‖} := fun ⟨x, hx⟩ ↦
  isLocalDiffeomorphAt_of_injective_mfderiv E.contMDiffOn E.isOpen_exterior hx
    BoundarylessManifold.isInteriorPoint (by simp) (E.mfderiv_bijective x hx).injective rfl

/-- An asymptotically Euclidean end packaged as a smooth partial diffeomorphism from
`{x | E.radius < ‖x‖}` onto `E.image`. -/
def partialDiffeomorph (E : AsymptoticallyEuclideanEnd n M t) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞ :=
  E.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn E.isOpen_exterior E.injOn

@[simp]
theorem partialDiffeomorph_source (E : AsymptoticallyEuclideanEnd n M t) :
    E.partialDiffeomorph.source = {x | E.radius < ‖x‖} :=
  E.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn_source E.isOpen_exterior E.injOn

@[simp]
theorem partialDiffeomorph_target (E : AsymptoticallyEuclideanEnd n M t) :
    E.partialDiffeomorph.target = E.image :=
  E.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn_target E.isOpen_exterior E.injOn

@[simp]
theorem coe_partialDiffeomorph (E : AsymptoticallyEuclideanEnd n M t) :
    ⇑E.partialDiffeomorph = E.toFun :=
  E.isLocalDiffeomorphOn.coe_partialDiffeomorphOfInjOn E.isOpen_exterior E.injOn

@[simp]
theorem partialDiffeomorph_symm_apply (E : AsymptoticallyEuclideanEnd n M t) (p : M) :
    E.partialDiffeomorph.toPartialEquiv.symm p = E.invFun p :=
  E.isLocalDiffeomorphOn.partialDiffeomorphOfInjOn_symm_apply E.isOpen_exterior E.injOn p

/-- Pointwise inverse of `E.partialDiffeomorph` as a function `M → ℝⁿ`. Not tagged `@[simp]`
because `simp` normalizes `E.partialDiffeomorph.symm p` through
`PartialDiffeomorph.symm_toPartialEquiv` and `partialDiffeomorph_symm_apply`. -/
theorem coe_partialDiffeomorph_symm (E : AsymptoticallyEuclideanEnd n M t) :
    ⇑E.partialDiffeomorph.symm = E.invFun :=
  funext fun _ ↦ by simp

/-- On a smooth manifold, the inverse parametrization `E.invFun` is smooth on `E.image`. -/
theorem contMDiffOn_invFun (E : AsymptoticallyEuclideanEnd n M t) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ E.invFun E.image :=
  E.isLocalDiffeomorphOn.contMDiffOn_invFunOn E.isOpen_exterior E.injOn

end ManifoldSmooth

end AsymptoticallyEuclideanEnd

/-! ### Finite-ended asymptotically Euclidean manifolds -/

/-- A finite-ended asymptotically Euclidean structure of order `t` on `M`: a finite nonempty family
of asymptotically Euclidean ends with pairwise disjoint open images whose union has compact
complement in `M` (Cecchini-Zeidler, Definition 2.3, without boundary). Requiring `0 < numEnds`
rules out the empty family of ends (whose complement is `Set.univ`); in positive dimension `1 ≤ n`
with positive decay order `0 < t` on a compact Hausdorff `C¹` manifold carrying a continuous
Riemannian metric, a nonempty end family has infinite Riemannian volume and thus excludes closed
manifolds such as flat tori (at `n = 0` the exterior `{x : radius < ‖x‖}` is empty, and at `t ≤ 0`
the decay bound does not force `g_ij → δ_ij`). -/
structure FiniteEndedAE (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] (t : ℝ) where
  /-- The number of ends. -/
  numEnds : ℕ
  /-- Nonemptiness of the end family, ruling out the empty family of ends. -/
  numEnds_pos : 0 < numEnds
  /-- The family of ends. -/
  ends : Fin numEnds → AsymptoticallyEuclideanEnd n M t
  /-- Pairwise disjointness of the open end images. -/
  pairwise_disjoint : Pairwise fun a b => Disjoint (ends a).image (ends b).image
  /-- Compactness of the remainder outside the union of all end images. -/
  isCompact_compl : IsCompact (⋃ a, (ends a).image)ᶜ

namespace FiniteEndedAE

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡 n) x)] {t : ℝ}

/-- Two finite-ended asymptotically Euclidean structures are equal if and only if they have the
same number of ends and the same end at each index. -/
@[ext (iff := false)]
theorem ext {A₁ A₂ : FiniteEndedAE n M t} (hnum : A₁.numEnds = A₂.numEnds)
    (hends : ∀ a : Fin A₁.numEnds, A₁.ends a = A₂.ends (a.cast hnum)) : A₁ = A₂ := by
  rcases A₁ with ⟨k₁, hk₁, e₁, hd₁, hc₁⟩
  rcases A₂ with ⟨k₂, hk₂, e₂, hd₂, hc₂⟩
  simp only at hnum hends
  subst hnum
  obtain rfl : e₁ = e₂ := funext hends
  rfl

/-- Package a single asymptotically Euclidean end whose image has compact complement as a
one-ended `FiniteEndedAE` structure. -/
def ofSingleEnd (E : AsymptoticallyEuclideanEnd n M t)
    (hc : IsCompact E.imageᶜ) : FiniteEndedAE n M t where
  numEnds := 1
  numEnds_pos := zero_lt_one
  ends _ := E
  pairwise_disjoint a b hab := absurd (Subsingleton.elim a b) hab
  isCompact_compl := by convert hc using 2; ext p; simp

@[simp]
theorem ofSingleEnd_numEnds (E : AsymptoticallyEuclideanEnd n M t)
    (hc : IsCompact E.imageᶜ) :
    (ofSingleEnd E hc).numEnds = 1 := (rfl)

@[simp]
theorem ofSingleEnd_ends (E : AsymptoticallyEuclideanEnd n M t)
    (hc : IsCompact E.imageᶜ)
    (a : Fin (ofSingleEnd E hc).numEnds) :
    (ofSingleEnd E hc).ends a = E := (rfl)

/-- Monotonicity in the decay order for `FiniteEndedAE`: a finite-ended structure of order `t` is
also one of any order `s ≤ t`. -/
def ofLE {s : ℝ} (hst : s ≤ t) (A : FiniteEndedAE n M t) : FiniteEndedAE n M s where
  numEnds := A.numEnds
  numEnds_pos := A.numEnds_pos
  ends a := (A.ends a).ofLE hst
  pairwise_disjoint a b hab := by
    simpa only [AsymptoticallyEuclideanEnd.ofLE_image] using A.pairwise_disjoint hab
  isCompact_compl := by
    simpa only [AsymptoticallyEuclideanEnd.ofLE_image] using A.isCompact_compl

@[simp]
theorem ofLE_numEnds {s : ℝ} (hst : s ≤ t) (A : FiniteEndedAE n M t) :
    (A.ofLE hst).numEnds = A.numEnds := (rfl)

@[simp]
theorem ofLE_ends {s : ℝ} (hst : s ≤ t) (A : FiniteEndedAE n M t)
    (a : Fin (A.ofLE hst).numEnds) :
    (A.ofLE hst).ends a = (A.ends (a.cast (ofLE_numEnds hst A))).ofLE hst := (rfl)

end FiniteEndedAE

/-! ### Euclidean checks: flat space and failure of decay under non-isometric scaling -/

/-- Flat Euclidean space `ℝⁿ` in the identity parametrization outside the unit ball is an
asymptotically Euclidean end of every decay order `t : ℝ`. -/
def AsymptoticallyEuclideanEnd.euclidean (n : ℕ) (t : ℝ) :
    AsymptoticallyEuclideanEnd n (EuclideanSpace ℝ (Fin n)) t :=
  AsymptoticallyEuclideanEnd.ofFun 1 zero_lt_one id contMDiffOn_id (injOn_id _)
    (by simpa using isOpen_lt continuous_const continuous_norm)
    (fun x _ ↦ by rw [mfderiv_id]; exact ContinuousLinearEquiv.refl ℝ _ |>.bijective)
    ⟨0, fun x _ i j ↦ by
      have hconst : (fun y : EuclideanSpace ℝ (Fin n) ↦
          pullbackMetricCoeff (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) y i j) =
          Function.const _ (if i = j then 1 else 0) :=
        funext fun y ↦ pullbackMetricCoeff_id y i j
      rw [hconst, fderiv_const, fderiv_zero]
      simp [ContinuousLinearMap.opNorm_zero]⟩

@[simp]
theorem AsymptoticallyEuclideanEnd.euclidean_radius (n : ℕ) (t : ℝ) :
    (AsymptoticallyEuclideanEnd.euclidean n t).radius = 1 := (rfl)

@[simp]
theorem AsymptoticallyEuclideanEnd.euclidean_toFun_of_lt {n : ℕ} (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 1 < ‖x‖) :
    (AsymptoticallyEuclideanEnd.euclidean n t).toFun x = x :=
  AsymptoticallyEuclideanEnd.ofFun_toFun_of_lt zero_lt_one id _ _ _ _ _ hx

@[simp]
theorem AsymptoticallyEuclideanEnd.euclidean_image (n : ℕ) (t : ℝ) :
    (AsymptoticallyEuclideanEnd.euclidean n t).image = {x | 1 < ‖x‖} := by
  simp [AsymptoticallyEuclideanEnd.euclidean]

/-- Outside the closed unit ball, the pulled-back metric coefficients of
`AsymptoticallyEuclideanEnd.euclidean n t` are the Kronecker delta `δ_ij`. -/
theorem AsymptoticallyEuclideanEnd.euclidean_pullbackMetricCoeff_of_lt {n : ℕ} (t : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : 1 < ‖x‖) (i j : Fin n) :
    pullbackMetricCoeff (AsymptoticallyEuclideanEnd.euclidean n t).toFun x i j =
      if i = j then 1 else 0 := by
  rw [AsymptoticallyEuclideanEnd.euclidean,
    AsymptoticallyEuclideanEnd.ofFun_pullbackMetricCoeff_of_lt _ _ _ _ _ _ _ hx,
    pullbackMetricCoeff_id]

/-- Flat Euclidean space `ℝⁿ` carries a one-ended `FiniteEndedAE` structure of every order `t : ℝ`:
the complement of `{x : 1 < ‖x‖}` is the compact closed unit ball. -/
def FiniteEndedAE.euclidean (n : ℕ) (t : ℝ) : FiniteEndedAE n (EuclideanSpace ℝ (Fin n)) t :=
  FiniteEndedAE.ofSingleEnd (AsymptoticallyEuclideanEnd.euclidean n t) <| by
    rw [AsymptoticallyEuclideanEnd.euclidean_image]
    convert isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 using 1
    ext x
    simp

@[simp]
theorem FiniteEndedAE.euclidean_numEnds (n : ℕ) (t : ℝ) :
    (FiniteEndedAE.euclidean n t).numEnds = 1 := (rfl)

@[simp]
theorem FiniteEndedAE.euclidean_ends (n : ℕ) (t : ℝ)
    (a : Fin (FiniteEndedAE.euclidean n t).numEnds) :
    (FiniteEndedAE.euclidean n t).ends a = AsymptoticallyEuclideanEnd.euclidean n t := (rfl)

/-- **Negative scaling check.** In positive dimension `1 ≤ n`, the homothety `x ↦ c • x` of flat
`ℝⁿ` with `|c| ≠ 1` has `g_ii - 1 = c ^ 2 - 1 ≠ 0`, so its metric coefficients do not decay at any
positive order `t > 0` on `{x : r < ‖x‖}`. -/
theorem not_exists_pullbackMetricCoeff_smul_decay {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : |c| ≠ 1) {r : ℝ} :
    ¬ ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) ↦ c • y) x i j -
        if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) := by
  rintro ⟨C, hC⟩
  let i₀ : Fin n := ⟨0, by omega⟩
  let e₀ : EuclideanSpace ℝ (Fin n) := EuclideanSpace.basisFun (Fin n) ℝ i₀
  have he₀ : ‖e₀‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i₀
  have hdiff : |c ^ 2 - 1| ≠ 0 := by
    rw [ne_eq, abs_eq_zero, sub_eq_zero, sq_eq_one_iff]
    rintro (rfl | rfl) <;> simp at hc
  have hd_pos : 0 < |c ^ 2 - 1| := abs_pos.2 (abs_ne_zero.1 hdiff)
  have htend : Tendsto (fun s : ℝ ↦ max C 0 * s ^ (-t)) atTop (𝓝 0) := by
    simpa [mul_zero] using
      (tendsto_rpow_neg_atTop ht).const_mul (max C 0)
  obtain ⟨S, hS⟩ := (htend.eventually (gt_mem_nhds hd_pos)).exists_forall_of_atTop
  set s := max (max (r + 1) 1) S
  have hsr : r < s := lt_of_lt_of_le (lt_add_one r) ((le_max_left _ _).trans (le_max_left _ _))
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_left _ _))
  have hnorm : ‖s • e₀‖ = s := by simp [norm_smul, Real.norm_of_nonneg hs0.le, he₀]
  have hle := hC (s • e₀) (by rwa [hnorm]) i₀ i₀
  simp only [pullbackMetricCoeff_const_smul, ↓reduceIte, mul_one, hnorm] at hle
  have hle' : |c ^ 2 - 1| ≤ max C 0 * s ^ (-t) :=
    hle.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.rpow_nonneg hs0.le _))
  exact (not_lt_of_ge hle') (hS s (le_max_right _ _))

/-- **Doubling check.** In positive dimension `1 ≤ n`, the parametrization `x ↦ (2 : ℝ) • x` of
flat `ℝⁿ` has `g_ij = 4 δ_ij` and does not satisfy the asymptotically Euclidean decay bound of any
order `t > 0`. -/
theorem not_exists_pullbackMetricCoeff_two_smul_decay {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t)
    {r : ℝ} :
    ¬ ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin n), r < ‖x‖ → ∀ i j : Fin n,
      |pullbackMetricCoeff (fun y : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) • y) x i j -
        if i = j then 1 else 0| ≤ C * ‖x‖ ^ (-t) :=
  not_exists_pullbackMetricCoeff_smul_decay hn ht (by norm_num)

end TauCeti
