/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.Map
public import TauCeti.Geometry.Manifold.Morse.Bott.Family
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Prod
import TauCeti.Geometry.Manifold.Morse.Submersion

/-!
# Morse–Bott functions on mapping tori

Let `φ` be a diffeomorphism of a manifold `M` and `h : M → ℝ` a function invariant under `φ`,
`h ∘ φ = h`. Then `[t, x] ↦ h x` is a well-defined function on the smooth mapping torus
`Y_φ = (ℝ × M) / ((t, x) ∼ (t + 1, φ⁻¹ x))` (`TauCeti.SmoothMappingTorus.liftOfInvariant`). This
file shows that the closed orbits of the suspension flow through the nondegenerate periodic critical
points of `h` are Morse–Bott critical submanifolds of the induced function, and that they exhibit it
as a Morse–Bott function when `h` is a Morse function whose critical points are fixed by `φ`.

On the cover `ℝ × M` the induced function is `h ∘ Prod.snd`, and the quotient map
`(t, x) ↦ [t, x]` is a local diffeomorphism. So `[t, x]` is a critical point exactly when `x` is a
critical point of `h` (`TauCeti.SmoothMappingTorus.mk_mem_criticalPoints_liftOfInvariant_iff`),
with the same Morse index (`TauCeti.SmoothMappingTorus.manifoldMorseIndex_liftOfInvariant_mk`): the
time direction contributes nothing to the Hessian. The critical set is therefore the union of the
suspension orbits through the critical points of `h`, which are invariant under `φ`. If `x` is a
critical point of least period `d` for `φ`, its suspension orbit is the closed orbit
`TauCeti.SmoothMappingTorus.closedOrbit`, a smoothly embedded circle `ℝ / dℤ → Y_φ`
(`TauCeti.SmoothMappingTorus.closedOrbitEmbedding`). When `x` is nondegenerate, the kernel of the
critical Hessian at a point of this circle is spanned by the suspension vector field `∂_t`, which
is the velocity of the circle; so the circle is a Morse–Bott critical submanifold
(`TauCeti.SmoothMappingTorus.isNondegenerateCriticalSubmanifold_closedOrbitEmbedding`), whose
negative normal space has the rank of the Morse index of `h` at `x`.

When every critical point of the Morse function `h` is fixed by `φ`, these circles, one for each
critical point, exhibit the induced function as a Morse–Bott function
(`TauCeti.SmoothMappingTorus.isMorseBottFamily_liftOfInvariant`).

An instance is the function induced by `z + ε cos θ` on the oriented mapping torus of `S² × S¹` by a
pair of reflections (`TauCeti.Geometry.Manifold.Morse.Bott.Examples.SphereCircle`), whose four
critical circles have Morse indices `3`, `2`, `1` and `0`.

## Main results

* `TauCeti.SmoothMappingTorus.mk_mem_criticalPoints_liftOfInvariant_iff`: the critical points of the
  induced function lie over the critical points of `h`.
* `TauCeti.SmoothMappingTorus.manifoldMorseIndex_liftOfInvariant_mk`: its Morse index at `[t, x]` is
  that of `h` at `x`.
* `TauCeti.SmoothMappingTorus.isNondegenerateCriticalSubmanifold_closedOrbitEmbedding`: the closed
  orbit through a nondegenerate periodic critical point is a Morse–Bott critical submanifold.
* `TauCeti.SmoothMappingTorus.isMorseBottFamily_liftOfInvariant`: if `h` is Morse and `φ` fixes its
  critical points, the closed orbits through them exhibit the induced function as a Morse–Bott
  function.

## References

* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 6.2 (Morse–Bott functions and the orientations of
  their trajectory spaces).
-/

public section

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-! ### Critical points and Morse indices -/

section Critical

variable {n : ℕ∞ω} (φ : M ≃ₘ^n⟮I, I⟯ M) {h : M → ℝ} (hh : ∀ x, h (φ x) = h x)
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

/-- **The critical points of the induced function** lie over the critical points of `h`: for
`1 ≤ n`, the point `[t, x]` is a critical point of `[t, x] ↦ h x` exactly when `x` is a critical
point of `h`. -/
theorem mk_mem_criticalPoints_liftOfInvariant_iff (hn : 1 ≤ n) (t : ℝ) (x : M) :
    mk φ t x ∈ criticalPoints (𝓘(ℝ).prod I) (liftOfInvariant φ h hh) ↔ x ∈ criticalPoints I h := by
  rw [← uncurry_apply_pair (mk φ) t x,
    ← (isLocalDiffeomorph_uncurry_mk φ (t, x)).mem_criticalPoints_comp_iff hn,
    liftOfInvariant_comp_uncurry_mk, mem_criticalPoints_comp_snd_iff]

/-- **The Morse index of the induced function** at `[t, x]` is the Morse index of `h` at a critical
point `x` at which `h` is `C²`, for `2 ≤ n`: the time direction contributes nothing to the
Hessian. -/
theorem manifoldMorseIndex_liftOfInvariant_mk [I.Boundaryless] (hn : 2 ≤ n) {t : ℝ} {x : M}
    (hs : ContMDiffAt I 𝓘(ℝ) 2 h x) (hx : x ∈ criticalPoints I h) :
    manifoldMorseIndex (𝓘(ℝ).prod I) (liftOfInvariant φ h hh) (mk φ t x) =
      manifoldMorseIndex I h x := by
  rw [← uncurry_apply_pair (mk φ) t x,
    ← (isLocalDiffeomorph_uncurry_mk φ (t, x)).manifoldMorseIndex_comp hn
      (contMDiffAt_liftOfInvariant_mk φ hn hh hs)
      ((mk_mem_criticalPoints_liftOfInvariant_iff φ hh (one_le_two.trans hn) t x).2 hx),
    liftOfInvariant_comp_uncurry_mk, manifoldMorseIndex_comp_snd]

end Critical

/-! ### Closed orbits through critical points -/

section ClosedOrbit

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] [I.Boundaryless]
  [FiniteDimensional ℝ E] (φ : M ≃ₘ⟮I, I⟯ M) {d : ℕ} [Fact (0 < (d : ℝ))] {x : M}

variable {h : M → ℝ} (hh : ∀ x, h (φ x) = h x)

/-- **Closed orbits through nondegenerate critical points are Morse–Bott.** Let `h` be a
`φ`-invariant function and `x` a nondegenerate critical point of `h` of least period `d` for `φ`.
Then the closed orbit `t ↦ [t, x]` is a Morse–Bott critical submanifold of the induced function
`[t, x] ↦ h x`: along it, the kernel of the critical Hessian is the line spanned by the suspension
vector field `∂_t`. -/
theorem isNondegenerateCriticalSubmanifold_closedOrbitEmbedding (hx : IsPeriodicPt φ d x)
    (hd : minimalPeriod φ x = d) (hcrit : IsManifoldNondegenerateCriticalPoint I h x) :
    (closedOrbitEmbedding hx (by simp) hd).IsNondegenerateCriticalSubmanifold
      (liftOfInvariant φ h hh) := by
  have hl (t : ℝ) : ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) 2 (liftOfInvariant φ h hh) (mk φ t x) :=
    contMDiffAt_liftOfInvariant_mk φ (by simp) hh hcrit.contMDiffAt
  have hcrit' (t : ℝ) : mk φ t x ∈ criticalPoints (𝓘(ℝ).prod I) (liftOfInvariant φ h hh) :=
    (mk_mem_criticalPoints_liftOfInvariant_iff φ hh (by simp) t x).2 hcrit.mem_criticalPoints
  refine ⟨⟨fun s ↦ ?_, fun s ↦ ?_⟩, fun s v hv ↦ ?_⟩
  · induction s using QuotientAddGroup.induction_on with | H t => ?_
    rw [coe_closedOrbitEmbedding, closedOrbit_coe]
    exact hl t
  · induction s using QuotientAddGroup.induction_on with | H t => ?_
    rw [coe_closedOrbitEmbedding, closedOrbit_coe]
    exact hcrit' t
  induction s using QuotientAddGroup.induction_on with | H t => ?_
  rw [coe_closedOrbitEmbedding, closedOrbit_coe] at hv
  rw [coe_closedOrbitEmbedding, mfderiv_closedOrbit, closedOrbit_coe]
  set q := uncurry (mk φ)
  have hq := isLocalDiffeomorph_uncurry_mk φ (t, x)
  have hreg : IsRegularPoint (𝓘(ℝ).prod I) (𝓘(ℝ).prod I) q (t, x) :=
    isRegularPoint_iff.2 (hq.isInvertible_mfderiv (by simp)).surjective
  -- Lift `v` to a tangent vector `u` of `ℝ × M` at `(t, x)`.
  obtain ⟨u, rfl⟩ := isRegularPoint_iff.1 hreg v
  have hu : u ∈ (criticalHessian (𝓘(ℝ).prod I) (h ∘ Prod.snd) (t, x)).ker := by
    rw [← liftOfInvariant_comp_uncurry_mk φ hh, hreg.ker_criticalHessian_comp (hl t)
      (hq.contMDiffAt.of_le (by simp)) (hcrit' t)]
    exact hv
  -- The projection to `M` is onto, and the Hessian of `h` at `x` is injective, so `u` has no
  -- component along `M`.
  have hsnd : IsRegularPoint (𝓘(ℝ).prod I) I (Prod.snd : ℝ × M → M) (t, x) :=
    isRegularPoint_iff.2 fun w ↦ ⟨(Manifold.tangentSpaceProdEquiv (t, x)).symm (0, w), by
      rw [mfderiv_snd_apply, Manifold.tangentSpaceProdEquiv_symm_apply]⟩
  rw [hsnd.ker_criticalHessian_comp hcrit.contMDiffAt contMDiffAt_snd hcrit.mem_criticalPoints,
    Submodule.mem_comap, mfderiv_snd] at hu
  have hu2 : (Manifold.tangentSpaceProdEquiv (t, x) u).2 = 0 := by
    have h0 := LinearMap.mem_ker.1 hu
    simp only [ContinuousLinearMap.coe_coe] at h0
    rw [Manifold.tangentSpaceProdEquiv_apply]
    exact hcrit.isInvertible_criticalHessian.injective (h0.trans (map_zero _).symm)
  -- So `u = a • (1, 0)`, which the quotient map sends to `a • ∂_t`.
  set a : ℝ := (Manifold.tangentSpaceProdEquiv (t, x) u).1
  have hu' : u = a • (Manifold.tangentSpaceProdEquiv (t, x)).symm (1, 0) := by
    apply (Manifold.tangentSpaceProdEquiv (t, x)).injective
    rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst]
      exact (mul_one a).symm
    · rw [hu2, Prod.smul_snd, smul_zero]
  refine ⟨a, ?_⟩
  rw [hu', map_smul, ← timeVectorField_mk]
  -- `exact` sees through the tangent space synonym `TangentSpace 𝓘(ℝ) t = ℝ` that blocks `rw`.
  exact ContinuousLinearMap.smulRight_apply.trans
    (congrArg (· • _) (one_apply_eq_self (F := ℝ →L[ℝ] ℝ) a))

/-- **The induced function of a Morse function is Morse–Bott.** Let `h` be a `φ`-invariant Morse
function all of whose critical points are fixed by `φ`. Then the closed orbits through the critical
points of `h`, embedded circles `ℝ / ℤ → Y_φ`, exhibit the induced function `[t, x] ↦ h x` on the
mapping torus as a Morse–Bott function. -/
theorem isMorseBottFamily_liftOfInvariant (hm : IsMorse I h)
    (hfix : ∀ x ∈ criticalPoints I h, IsFixedPt φ x) :
    IsMorseBottFamily (fun x : criticalPoints I h ↦ closedOrbitEmbedding
      ((hfix x x.property).isPeriodicPt 1)
          (by simp) (minimalPeriod_eq_one_iff_isFixedPt.2 (hfix x x.property)))
      (liftOfInvariant φ h hh) := by
  refine .of_pairwise_disjoint (by simp) (contMDiff_liftOfInvariant φ le_rfl hh hm.contMDiff)
    (fun x ↦ isNondegenerateCriticalSubmanifold_closedOrbitEmbedding φ hh _ _
      (hm.isManifoldNondegenerateCriticalPoint_of_mem_criticalPoints x.property))
    (fun x y hxy ↦ ?_) fun z hz ↦ ?_
  · simp only [onFun, coe_closedOrbitEmbedding]
    refine (disjoint_range_closedOrbit_iff _ _).2 fun ⟨j, hj⟩ ↦ hxy (Subtype.ext ?_)
    rw [← hj, ((hfix x x.property).iterate j).eq]
  · obtain ⟨⟨t, x⟩, rfl⟩ := uncurry_mk_surjective φ z
    have hx := (mk_mem_criticalPoints_liftOfInvariant_iff φ hh (by simp) t x).1 hz
    exact mem_iUnion.2 ⟨⟨x, hx⟩, t, by simp⟩

end ClosedOrbit

end TauCeti.SmoothMappingTorus
