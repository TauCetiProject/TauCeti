/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Ramification
public import TauCeti.Analysis.Complex.UpperHalfPlane.Meromorphic

/-!
# Meromorphic descent to the coarse Fuchsian quotient

Let `Γ ≤ PSL(2, ℝ)` act properly discontinuously on the upper half-plane, so that the coarse orbit
quotient `Γ \ ℍ` is a Riemann surface and the orbit projection `π : ℍ → Γ \ ℍ` is holomorphic.
This file proves the meromorphic counterpart of the holomorphic descent criterion
`Subgroup.mdifferentiable_iff_comp_quotientMk`, together with the order formula at elliptic
points.

A function `F` on `Γ \ ℍ` is meromorphic at the orbit of `z` exactly when its pullback `F ∘ π` is
meromorphic at `z` (`Subgroup.meromorphicAt_comp_quotientMk_iff`). One direction is pullback along
the holomorphic map `π`. For the other, in the chart at the orbit of `z` the projection is
`u ↦ u ^ m` in a disc coordinate `u` centred at `z`, where `m` is the order of the stabilizer of
`z`, so the chart representative of `F` is the descent of a meromorphic function through the power
map, which is meromorphic by `TauCeti.meromorphicAt_descendPow`.

The orders satisfy
`ord_z (F ∘ π) = m * ord_{π z} F`
(`Subgroup.meromorphicOrderAt_comp_quotientMk`), the local multiplicity of `π` at `z` being `m`
(`Subgroup.localMultiplicity_quotientMk`). In particular an invariant function meromorphic on the
upper half-plane descends uniquely to a meromorphic function on `Γ \ ℍ`
(`Subgroup.existsUnique_meromorphicAt_quotientMk`), and its order at a point of stabilizer order
`m` is `m` times the order of the descended function at the image orbit. Orders upstairs may be
computed from `f ∘ ofComplex` by
`TauCeti.UpperHalfPlane.meromorphicOrderAt_eq_meromorphicOrderAt_comp_ofComplex`.

## Main declarations

* `Subgroup.meromorphicAt_comp_quotientMk_iff`: the pullback criterion for meromorphy.
* `Subgroup.meromorphicOrderAt_comp_quotientMk`: pulling back multiplies the order by the order
  of the stabilizer.
* `Subgroup.existsUnique_meromorphicAt_quotientMk`: invariant meromorphic functions descend
  uniquely.

## References

* Hershel Farkas and Irwin Kra, *Riemann Surfaces*, Graduate Texts in Mathematics 71, Springer,
  second edition, 1992, Chapter I §§4–5.
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter III §§3–4.
-/

public noncomputable section

open Filter IsManifold Metric MulAction Set TauCeti Topology UpperHalfPlane

open scoped ComplexConjugate Manifold MatrixGroups

namespace Subgroup

variable (Γ : Subgroup PSL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Meromorphic descent at an orbit.** A function on the coarse quotient is meromorphic at the
orbit of `z` as soon as its pullback to the upper half-plane is meromorphic at `z`, including at
elliptic points. -/
theorem meromorphicAt_of_meromorphicAt_comp_quotientMk {F : orbitRel.Quotient Γ ℍ → E} {z : ℍ}
    (hF : RiemannSurface.MeromorphicAt (F ∘ Quotient.mk _) z) :
    RiemannSurface.MeromorphicAt F (Quotient.mk _ z) := by
  have : Finite (stabilizer Γ z) := (ProperlyDiscontinuousSMul.finite_stabilizer z).to_subtype
  have : NeZero (Nat.card (stabilizer Γ z)) := ⟨Nat.card_pos.ne'⟩
  obtain ⟨ε, hε, hopen⟩ := exists_pos_isOpenEmbedding_stabilizerBallQuotientToQuotient Γ z
  set e := stabilizerBallQuotientChart hε hopen with he_def
  set m := Nat.card (stabilizer Γ z) with hm
  have hsource : Quotient.mk _ z ∈ e.source :=
    (mem_stabilizerBallQuotientChart_source_iff hε hopen).2 ⟨1, by simpa using hε⟩
  have he : e ∈ maximalAtlas 𝓘(ℂ) 1 (orbitRel.Quotient Γ ℍ) :=
    subset_maximalAtlas (stabilizerBallQuotientChart_mem_atlas Γ hε hopen)
  have hez : e (Quotient.mk _ z) = 0 := by
    rw [he_def, stabilizerBallQuotientChart_mk hε hopen (by rwa [dist_self]), discCoordinate_self,
      zero_pow (NeZero.ne _)]
  rw [RiemannSurface.meromorphicAt_iff_of_mem_maximalAtlas he hsource, hez]
  -- The explicit inverse `ψ` of the disc coordinate at `z`, analytic at `0` with `ψ 0 = z`.
  set ψ : ℂ → ℂ := fun w ↦ ((z : ℂ) - conj (z : ℂ) * w) / (1 - w) with hψ
  have hψ0 : ψ 0 = z := by simp [hψ]
  have hψa : AnalyticAt ℂ ψ 0 :=
    analyticOnNhd_discCoordinateHomeomorph_symm z 0 (mem_ball_self one_pos)
  have hr : 0 < Real.tanh (ε / 2) := by
    rw [← Real.tanh_zero]
    exact Real.tanh_strictMono (by linarith)
  -- Pulled back along `u ↦ u ^ m`, the chart representative of `F` is `F ∘ π` read in the disc
  -- coordinate at `z`, which is meromorphic at `0`.
  have hpull : (fun w ↦ (F ∘ e.symm) (w ^ m)) =ᶠ[𝓝 0]
      ((F ∘ Quotient.mk _) ∘ ofComplex) ∘ ψ := by
    filter_upwards [ball_mem_nhds 0 hr] with w hw
    have hw' := mem_ball_zero_iff.1 hw
    simp only [Function.comp_apply]
    rw [hm, stabilizerBallQuotientChart_symm_pow hε hopen hw',
      ← ofComplex_apply ((discCoordinateHomeomorph z).symm _),
      coe_discCoordinateHomeomorph_symm_apply, Complex.UnitDisc.coe_mk]
  rw [TauCeti.UpperHalfPlane.meromorphicAt_iff_meromorphicAt_comp_ofComplex, ← hψ0] at hF
  have hmero : _root_.MeromorphicAt (fun w ↦ (F ∘ e.symm) (w ^ m)) 0 :=
    (hF.comp_analyticAt hψa).congr (hpull.symm.filter_mono nhdsWithin_le_nhds)
  -- That pullback is invariant under the `m`-th roots of unity, so it descends through the power
  -- map to the chart representative of `F`, which is therefore meromorphic.
  have hd := meromorphicAt_descendPow (m := m) hmero
    (.of_forall fun u ζ ↦ congrArg (F ∘ e.symm) (rootsOfUnity.smul_pow ζ u))
  rwa [descendPow_comp_pow] at hd

/-- **The pullback criterion for meromorphy.** A function on the coarse quotient is meromorphic at
the orbit of `z` exactly when its pullback to the upper half-plane is meromorphic at `z`. -/
@[simp]
theorem meromorphicAt_comp_quotientMk_iff {F : orbitRel.Quotient Γ ℍ → E} {z : ℍ} :
    RiemannSurface.MeromorphicAt (F ∘ Quotient.mk _) z ↔
      RiemannSurface.MeromorphicAt F (Quotient.mk _ z) :=
  ⟨Γ.meromorphicAt_of_meromorphicAt_comp_quotientMk,
    fun hF ↦ hF.comp (.of_forall (mdifferentiable_quotientMk Γ))⟩

/-- **The order formula for descent.** Pulling a function on the coarse quotient back to the upper
half-plane multiplies its order at the orbit of `z` by the order `m` of the stabilizer of `z`:
`ord_z (F ∘ π) = m * ord_{π z} F`. Applied to the descent of an invariant meromorphic function
(`Subgroup.existsUnique_meromorphicAt_quotientMk`), this computes the order of the function
upstairs from that of its descent. Both sides are the junk value `0` when `F` is not meromorphic
at the orbit of `z`. -/
theorem meromorphicOrderAt_comp_quotientMk (F : orbitRel.Quotient Γ ℍ → E) (z : ℍ) :
    RiemannSurface.meromorphicOrderAt (F ∘ Quotient.mk (orbitRel Γ ℍ)) z =
      Nat.card (stabilizer Γ z) *
        RiemannSurface.meromorphicOrderAt F (Quotient.mk (orbitRel Γ ℍ) z) := by
  by_cases hF : RiemannSurface.MeromorphicAt F (Quotient.mk (orbitRel Γ ℍ) z)
  · rw [RiemannSurface.meromorphicOrderAt_comp hF (.of_forall (mdifferentiable_quotientMk Γ))
      (Γ.not_eventuallyConst_quotientMk z), localMultiplicity_quotientMk, mul_comm]
  · rw [RiemannSurface.meromorphicOrderAt_of_not_meromorphicAt hF,
      RiemannSurface.meromorphicOrderAt_of_not_meromorphicAt
        (mt (Γ.meromorphicAt_comp_quotientMk_iff).1 hF), mul_zero]

/-- **Meromorphic descent.** Every invariant function on the upper half-plane that is meromorphic
at every point descends uniquely to a function on the coarse quotient that is meromorphic at every
point, with no freeness assumption. Its orders are related to those upstairs by
`Subgroup.meromorphicOrderAt_comp_quotientMk`. -/
theorem existsUnique_meromorphicAt_quotientMk (f : ℍ → E)
    (hinv : ∀ (g : Γ) (z : ℍ), f (g • z) = f z)
    (hf : ∀ z, RiemannSurface.MeromorphicAt f z) :
    ∃! F : orbitRel.Quotient Γ ℍ → E,
      (∀ q, RiemannSurface.MeromorphicAt F q) ∧ F ∘ Quotient.mk _ = f := by
  let F : orbitRel.Quotient Γ ℍ → E := Quotient.lift f (by
    intro z w h
    obtain ⟨g, rfl⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
    exact hinv g w)
  refine ⟨F, ⟨fun q ↦ ?_, rfl⟩, fun G hG ↦ ?_⟩
  · induction q using Quotient.inductionOn with
    | h z => exact Γ.meromorphicAt_of_meromorphicAt_comp_quotientMk (hf z)
  · funext q
    induction q using Quotient.inductionOn with
    | h z => exact congrFun hG.2 z

end Subgroup
