/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks are unique factorization domains

At any point `x` of a finite-dimensional complex manifold `X` without boundary, the stalk `𝒪_{X, x}`
of holomorphic germs and the stalk of Mathlib's complex-smooth structure sheaf are unique
factorization domains (and hence integrally closed via
`UniqueFactorizationMonoid.instIsIntegrallyClosed`). The same holds chart-locally at any point in
the domain of a holomorphic chart into a finite-dimensional complex normed space, without assuming
a global manifold structure.

On a finite-dimensional complex normed space `E`, vertical polynomial evaluation
`evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies the abstract Rückert
hypotheses (`RingHom.IsRueckert`) with respect to the polynomials distinguished at the maximal ideal
of `𝒪_{E, x₀}`. Consequently, a distinguished polynomial `P` over `𝒪_{E, x₀}` generates a prime
ideal, is prime, or is irreducible in `(𝒪_{E, x₀})[X]` if and only if `evalVertical x₀ w₀ P` is so
in `𝒪_{E × ℂ, (x₀, w₀)}`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: `evalVertical x₀ w₀` satisfies
  `RingHom.IsRueckert` for polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`,
  `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: stalks of the
  holomorphic and complex-smooth structure sheaves are unique factorization domains.
* `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`: primality
  and irreducibility of distinguished Weierstrass polynomials match those of their vertical
  evaluations.
* `OpenPartialHomeomorph.uniqueFactorizationMonoid_holomorphicStalk`: unique factorization of the
  holomorphic stalk at any point in the domain of a holomorphic chart.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, (2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II, §B.
* H. Grauert and R. Remmert, *Coherent Analytic Sheaves*, Chapter 2, §2.
-/

public noncomputable section

open Filter IsLocalRing IsManifold Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Rueckert

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Pullback along the affine linear automorphism `z ↦ p₀ + L (z - p₀)` fixing `p₀`, as a ring
automorphism of the holomorphic stalk at `p₀`. -/
private def centeredLinearStalkEquiv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (p₀ : V) (L : V ≃L[ℂ] V) :
    (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p₀ ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p₀ :=
  have hφ : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω (fun z ↦ p₀ + L (z - p₀)) :=
    contMDiff_iff_contDiff.2
      (contDiff_const.add (L.contDiff.comp (contDiff_id.sub contDiff_const)))
  have hψ : ContMDiff 𝓘(ℂ, V) 𝓘(ℂ, V) ω (fun z ↦ p₀ + L.symm (z - p₀)) :=
    contMDiff_iff_contDiff.2
      (contDiff_const.add (L.symm.contDiff.comp (contDiff_id.sub contDiff_const)))
  (RingEquiv.cast (R := fun q ↦ (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk q)
    (by simp : p₀ = p₀ + L (p₀ - p₀))).trans <|
    RingEquiv.ofBijective _ <| stalkPullback_bijective (a := p₀)
      (Eventually.of_forall fun _ ↦ hφ.contMDiffAt)
      (Eventually.of_forall fun _ ↦ hψ.contMDiffAt)
      (Eventually.of_forall fun z ↦ by simp)
      (Eventually.of_forall fun z ↦ by simp)

private theorem toFilterGerm_centeredLinearStalkEquiv {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] {p₀ : V} (L : V ≃L[ℂ] V)
    {b : (holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk p₀} {F : V → ℂ}
    (hbF : toFilterGerm 𝓘(ℂ, V) V p₀ (𝓝 p₀) le_rfl b = ↑F) :
    toFilterGerm 𝓘(ℂ, V) V p₀ (𝓝 p₀) le_rfl (centeredLinearStalkEquiv p₀ L b) =
      ↑(F ∘ fun z ↦ p₀ + L (z - p₀)) := by
  rw [centeredLinearStalkEquiv, RingEquiv.trans_apply, RingEquiv.ofBijective_apply,
    toFilterGerm_stalkPullback, toFilterGerm_ringEquivCast _ hbF, Germ.coe_compTendsto]

/-- Any nonzero holomorphic germ on `E × ℂ` at `(x₀, w₀)` becomes regular in the vertical variable
after a stalk automorphism fixing `(x₀, w₀)`. -/
private theorem exists_ringEquiv_map_residue_verticalPowerSeries_ne_zero {x₀ : E} {w₀ : ℂ}
    {b : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    (hb : b ≠ 0) :
    ∃ α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀),
      (verticalPowerSeries x₀ w₀ (α b)).map
        (residue ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)) ≠ 0 := by
  let p₀ : E × ℂ := (x₀, w₀)
  obtain ⟨F, hF, hbF⟩ := exists_analyticAt_toFilterGerm_eq p₀ b
  have hF0 : AnalyticAt ℂ F (p₀ + 0) := by simpa using hF
  have hG : AnalyticAt ℂ (fun z : E × ℂ ↦ F (p₀ + z)) 0 :=
    hF0.comp (analyticAt_const.add analyticAt_id)
  have hG0 : ¬(fun z : E × ℂ ↦ F (p₀ + z)) =ᶠ[𝓝 0] 0 := by
    intro h0
    apply (eq_zero_iff_of_toFilterGerm_eq (hbF _ le_rfl)).not.1 hb
    have hcont : Continuous fun z : E × ℂ ↦ z - p₀ := by fun_prop
    have ht : Tendsto (fun z : E × ℂ ↦ z - p₀) (𝓝 p₀) (𝓝 0) := by
      simpa using hcont.tendsto p₀
    filter_upwards [ht.eventually h0] with z hz
    simpa using hz
  obtain ⟨L, q, hLq, hslice₀⟩ := hG.exists_continuousLinearEquiv_analyticOrderAt_ne_top hG0
  obtain rfl : q = 0 := L.injective (hLq.trans (map_zero L).symm)
  refine ⟨centeredLinearStalkEquiv p₀ L,
    (map_residue_verticalPowerSeries_ne_zero_iff
      (toFilterGerm_centeredLinearStalkEquiv L (hbF _ le_rfl))).2 ?_⟩
  rw [Ne, analyticOrderAt_eq_top]
  intro hw
  apply hslice₀
  rw [analyticOrderAt_eq_top]
  have hcont : Continuous fun t : ℂ ↦ w₀ + t := by fun_prop
  have ht : Tendsto (fun t : ℂ ↦ w₀ + t) (𝓝 0) (𝓝 w₀) := by
    simpa using hcont.tendsto 0
  filter_upwards [ht.eventually hw] with t ht
  have hφt : (x₀, w₀ + t) - (x₀, w₀) = (0, t) := by
    rw [Prod.mk_sub_mk, sub_self, add_sub_cancel_left]
  simpa only [Function.comp_apply, p₀, hφt, Prod.fst_zero] using ht

variable [FiniteDimensional ℂ E]

/-- **Vertical polynomial evaluation satisfies the Rückert hypotheses.** On a finite-dimensional
complex normed space `E`, `evalVertical x₀ w₀` satisfies `RingHom.IsRueckert` with respect to the
polynomials over `𝒪_{E, x₀}` distinguished at its maximal ideal. -/
theorem isRueckert_evalVertical (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw := hw.of_dvd hp hpw
  dvd_iff hw p := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub {P} hP b := by
    obtain ⟨⟨q, r⟩, ⟨-, hdiv⟩, -⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hP b
    exact ⟨r, q, by linear_combination hdiv⟩
  exists_mul_eq {b} hb := by
    obtain ⟨α, hα⟩ := exists_ringEquiv_map_residue_verticalPowerSeries_ne_zero hb
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, -⟩ := existsUnique_weierstrassPreparation hα
    refine ⟨α, hu.unit⁻¹, P, hP, ?_⟩
    rw [hfac, mul_comm _ u, ← mul_assoc, hu.val_inv_mul, one_mul]

/-- A distinguished polynomial over `𝒪_{E, x₀}` generates a prime ideal after vertical evaluation
at `(x₀, w₀)` if and only if it generates a prime ideal in `(𝒪_{E, x₀})[X]`. -/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime :=
  (isRueckert_evalVertical x₀ w₀).isPrime_span_apply_iff hP

/-- A distinguished polynomial over `𝒪_{E, x₀}` has prime vertical evaluation at `(x₀, w₀)` if and
only if it is prime in `(𝒪_{E, x₀})[X]`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P :=
  (isRueckert_evalVertical x₀ w₀).prime_apply_iff hP

private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, V, _, _, _, hV, x => by
    have := finrank_zero_iff.1 hV
    exact (evalRingEquivOfSingletonMemNhds 𝓘(ℂ, V)
      ((isOpen_discrete _).mem_nhds rfl)).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have := uniqueFactorizationMonoid_stalk_of_finrank_eq n (Fin n → ℂ) (by simp) (e x).1
    have hprod := (isRueckert_evalVertical (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end Rueckert

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Holomorphic stalks are unique factorization domains.** At any point of a finite-dimensional
complex manifold without boundary, the stalk of holomorphic germs is a unique factorization
domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let V := Fin (finrank ℂ E) → ℂ
  let L : E ≃L[ℂ] V := ContinuousLinearEquiv.ofFinrankEq (by simp [V])
  have hV := uniqueFactorizationMonoid_stalk_of_finrank_eq (finrank ℂ E) V (by simp [V])
    ((L ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x L)).toMulEquiv
    |>.uniqueFactorizationMonoid hV

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

end Manifold

section Irreducible

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A distinguished polynomial over `𝒪_{E, x₀}` has irreducible vertical evaluation at `(x₀, w₀)`
if and only if it is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P :=
  (isRueckert_evalVertical x₀ w₀).irreducible_apply_iff hP

end Irreducible

end TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

open TauCeti TauCeti.holomorphicStructureSheaf

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X) {x : X} (hx : x ∈ e.source)

include he hx in
/-- At any point in the domain of a holomorphic chart into a finite-dimensional complex normed
space `E`, the holomorphic stalk is a unique factorization domain, without assuming a global
manifold structure on `X`. -/
theorem uniqueFactorizationMonoid_holomorphicStalk :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
  let L : E ≃L[ℂ] Fin (finrank ℂ E) → ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp)
  exact (RingEquiv.ofBijective _
    (e.holomorphicStalkPullback_comp_bijective he hx L)).toMulEquiv.uniqueFactorizationMonoid
      inferInstance

end OpenPartialHomeomorph
