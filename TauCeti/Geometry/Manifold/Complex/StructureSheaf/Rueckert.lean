/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import TauCeti.Analysis.Analytic.SingularDirection
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks satisfy the Rückert hypotheses

Let `E` be a finite-dimensional complex normed space, `x₀ : E`, and `w₀ : ℂ`. Evaluating
polynomials vertically (`TauCeti.holomorphicStructureSheaf.evalVertical`) gives a ring homomorphism
`(𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` that satisfies the Rückert hypotheses
(`RingHom.IsRueckert`) with respect to the polynomials distinguished at the maximal ideal of
`𝒪_{E, x₀}`:

* monic divisors of distinguished polynomials remain distinguished
  (`Polynomial.IsDistinguishedAt.of_dvd`);
* Weierstrass division identifies divisibility and remainders modulo distinguished polynomials
  (`TauCeti.holomorphicStructureSheaf.evalVertical_dvd_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.existsUnique_weierstrassDivision_of_isDistinguishedAt`);
* every nonzero germ at `(x₀, w₀)` becomes regular in the vertical coordinate after an affine
  biholomorphism fixing `(x₀, w₀)`
  (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`), so Weierstrass preparation
  expresses it as a unit times the evaluation of a distinguished polynomial.

Abstract Rückert descent (`TauCeti.RingTheory.Polynomial.Rueckert`) then passes Noetherianity and
unique factorisation from `𝒪_{E, x₀}` to `𝒪_{E × ℂ, (x₀, w₀)}`
(`TauCeti.holomorphicStructureSheaf.stalkIsNoetherianRing`,
`TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`).

## Main declarations

* `TauCeti.holomorphicStructureSheaf.exists_ringEquiv_mul_eq_evalVertical`: a nonzero germ becomes
  a unit multiple of the vertical evaluation of a distinguished polynomial after an affine change
  of coordinates fixing the base point, acting on function germs by composition.
* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: vertical polynomial evaluation at
  `(x₀, w₀)` satisfies the Rückert hypotheses for distinguished polynomials.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Vertical regularity after a change of coordinates.** Every nonzero holomorphic germ `b` at
`(x₀, w₀)` becomes a unit multiple of `evalVertical x₀ w₀ P`, for a distinguished polynomial `P`,
after an affine change of coordinates fixing `(x₀, w₀)`. The change of coordinates is a ring
automorphism `α` of the stalk acting on function germs by composition with a map `φ` that tends
to `(x₀, w₀)`. -/
theorem exists_ringEquiv_mul_eq_evalVertical (x₀ : E) (w₀ : ℂ)
    {b : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)} (hb : b ≠ 0) :
    ∃ (φ : E × ℂ → E × ℂ) (hφ : Tendsto φ (𝓝 (x₀, w₀)) (𝓝 (x₀, w₀)))
      (α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀))
      (u : ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀))ˣ)
      (P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]),
      (∀ c, toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α c) =
        (toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl c).compTendsto φ hφ) ∧
      P.IsDistinguishedAt
          (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ∧
        (u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) * α b =
          evalVertical x₀ w₀ P := by
  obtain ⟨F, hF, hbF⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) b
  have hF0 : ¬F =ᶠ[𝓝 (x₀, w₀)] 0 := (eq_zero_iff_of_toFilterGerm_eq (hbF _ le_rfl)).not.1 hb
  obtain ⟨L, q, hLq, hslice⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_ne_top hF0
  -- Center the linear change of coordinates at `(x₀, w₀)` so that it fixes `(x₀, w₀)`.
  let φ : E × ℂ → E × ℂ := fun p ↦ (x₀, w₀) + L (p - (x₀, w₀))
  let ψ : E × ℂ → E × ℂ := fun p ↦ (x₀, w₀) + L.symm (p - (x₀, w₀))
  have hφ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω φ := contMDiff_iff_contDiff.2 (by fun_prop)
  have hψ : ContMDiff 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω ψ := contMDiff_iff_contDiff.2 (by fun_prop)
  have hφ0 : φ (x₀, w₀) = (x₀, w₀) := by simp [φ]
  let f := stalkPullback (I := 𝓘(ℂ, E × ℂ)) (J := 𝓘(ℂ, E × ℂ)) (f := φ) (a := (x₀, w₀))
    (Eventually.of_forall fun _ ↦ hφ.contMDiffAt)
  have hbij := stalkPullback_bijective (I := 𝓘(ℂ, E × ℂ)) (J := 𝓘(ℂ, E × ℂ)) (a := (x₀, w₀))
    (Eventually.of_forall fun _ ↦ hφ.contMDiffAt)
    (Eventually.of_forall fun _ ↦ hψ.contMDiffAt)
    (Eventually.of_forall fun p ↦ by simp [φ, ψ]) (Eventually.of_forall fun p ↦ by simp [φ, ψ])
  let α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) :=
    (RingEquiv.cast (R := fun p ↦
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p) hφ0.symm).trans
      (RingEquiv.ofBijective f hbij)
  have hφt : Tendsto φ (𝓝 (x₀, w₀)) (𝓝 (x₀, w₀)) := by
    simpa only [hφ0] using hφ.continuous.tendsto (x₀, w₀)
  have hα (c : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)) :
      toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α c) =
        (toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl c).compTendsto φ hφt := by
    obtain ⟨C, -, hC⟩ := exists_toFilterGerm_eq (x₀, w₀) c
    simp only [α, RingEquiv.trans_apply, RingEquiv.ofBijective_apply, f,
      toFilterGerm_stalkPullback, toFilterGerm_ringEquivCast hφ0.symm (hC _ le_rfl), hC _ le_rfl,
      Germ.coe_compTendsto]
  have hαb : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α b) =
      fun p ↦ F (φ p) := by
    rw [hα, hbF _ le_rfl, Germ.coe_compTendsto]
    rfl
  have hφ_slice : ∀ w : ℂ, φ (x₀, w) = L (q.1, q.2 + (w - w₀)) := fun w ↦ by
    have hsub : (x₀, w) - (x₀, w₀) = ((0 : E), w - w₀) := by ext <;> simp
    calc
      φ (x₀, w) = (x₀, w₀) + L ((0 : E), w - w₀) := by dsimp only [φ]; rw [hsub]
      _ = L q + L ((0 : E), w - w₀) := by rw [hLq]
      _ = L (q.1, q.2 + (w - w₀)) := by rw [← L.map_add, Prod.mk_add_mk, add_zero]
  have hslice' : analyticOrderAt (fun w ↦ F (φ (x₀, w))) w₀ ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    refine fun h0 ↦ hslice ?_
    rw [analyticOrderAt_eq_top]
    have htend : Tendsto (fun t : ℂ ↦ w₀ + (t - q.2)) (𝓝 q.2) (𝓝 w₀) := by
      have : Continuous fun t : ℂ ↦ w₀ + (t - q.2) := by fun_prop
      simpa using this.tendsto q.2
    filter_upwards [htend.eventually h0] with t ht
    simpa [hφ_slice] using ht
  obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, _⟩ := existsUnique_weierstrassPreparation
    ((map_residue_verticalPowerSeries_ne_zero_iff hαb).2 hslice')
  refine ⟨φ, hφt, α, hu.unit⁻¹, P, hα, hP, ?_⟩
  rw [hfac, mul_left_comm, hu.val_inv_mul, mul_one]

/-- Vertical polynomial evaluation `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}`
satisfies the Rückert hypotheses for the polynomials distinguished at the maximal ideal of
`𝒪_{E, x₀}`. -/
theorem isRueckert_evalVertical (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw := hw.of_dvd (Ideal.IsPrime.isRadical inferInstance) hp hpw
  dvd_iff hw P := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub {w} hw b := by
    obtain ⟨⟨q, r⟩, ⟨_, hdiv⟩, _⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, ⟨q, by linear_combination hdiv⟩⟩
  exists_mul_eq hb :=
    let ⟨_, _, α, u, P, _, hP, hu⟩ := exists_ringEquiv_mul_eq_evalVertical x₀ w₀ hb
    ⟨α, u, P, hP, hu⟩

end TauCeti.holomorphicStructureSheaf
