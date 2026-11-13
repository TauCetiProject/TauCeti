/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks are unique factorisation domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorisation domain.

The proof follows Rückert's inductive descent along Weierstrass preparation and division. At a
point `(x₀, w₀)` of `E × ℂ`, evaluating polynomials vertically (`evalVertical x₀ w₀`) sends
distinguished polynomials over `𝒪_{E, x₀}` into `𝒪_{E × ℂ, (x₀, w₀)}`, and satisfies the Rückert
hypotheses (`RingHom.IsRueckert`):

* monic divisors of distinguished polynomials remain distinguished
  (`Polynomial.IsDistinguishedAt.of_dvd`);
* Weierstrass division identifies divisibility and remainders modulo distinguished
  polynomials (`evalVertical_dvd_iff_of_isDistinguishedAt`,
  `existsUnique_weierstrassDivision_of_isDistinguishedAt`);
* every nonzero germ at `(x₀, w₀)` becomes regular in the vertical coordinate after an affine
  biholomorphism fixing `(x₀, w₀)`
  (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`), so Weierstrass preparation
  expresses it as a unit times the evaluation of a distinguished polynomial.

Rückert's factorial descent (`RingHom.IsRueckert.uniqueFactorizationMonoid`) then passes unique
factorisation from `𝒪_{E, x₀}` to `𝒪_{E × ℂ, (x₀, w₀)}`. Starting from `ℂ` in dimension zero,
induction on the complex dimension handles every finite-dimensional model space, and charts transfer
the property to arbitrary finite-dimensional complex manifolds without boundary, as well as to
Mathlib's native complex-smooth structure sheaf via `smoothStalkIso`.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.isRueckert_evalVertical`: vertical polynomial evaluation at
  `(x₀, w₀)` satisfies the Rückert hypotheses for distinguished polynomials.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are
  unique factorisation domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: so are the stalks of
  Mathlib's complex-smooth structure sheaf.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, Theorem (2.10).
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Ch. II, §B.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5 (for Rückert descent).
-/

public noncomputable section

open Filter Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section ModelSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

private def stalkEquivOfEq {p q : E} (hpq : p = q) :
    (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk p ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk q := by
  subst hpq
  exact RingEquiv.refl _

private theorem toFilterGerm_stalkEquivOfEq {p q : E} (hpq : p = q)
    (s : (holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk p) {F : E → ℂ}
    (hF : toFilterGerm 𝓘(ℂ, E) E p (𝓝 p) le_rfl s = F) :
    toFilterGerm 𝓘(ℂ, E) E q (𝓝 q) le_rfl (stalkEquivOfEq hpq s) = F := by
  subst hpq
  exact hF

private theorem exists_aut_mul_eq_evalVertical [FiniteDimensional ℂ E] (x₀ : E) (w₀ : ℂ)
    {b : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)} (hb : b ≠ 0) :
    ∃ (α : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀) ≃+*
        (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀))
      (u : ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀))ˣ)
      (P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]),
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
    (stalkEquivOfEq hφ0.symm).trans (RingEquiv.ofBijective f hbij)
  have hαb : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α b) =
      fun p ↦ F (φ p) := by
    simp only [α, RingEquiv.trans_apply, RingEquiv.ofBijective_apply, f,
      toFilterGerm_stalkPullback, toFilterGerm_stalkEquivOfEq hφ0.symm b (hbF _ le_rfl),
      Germ.coe_compTendsto]
    rfl
  have hφ_slice : ∀ w : ℂ, φ (x₀, w) = L (q.1, q.2 + (w - w₀)) := fun w ↦ by
    have hsub : (x₀, w) - (x₀, w₀) = ((0 : E), w - w₀) := by ext <;> simp
    calc
      φ (x₀, w) = (x₀, w₀) + L ((0 : E), w - w₀) := by dsimp only [φ]; rw [hsub]
      _ = L q + L ((0 : E), w - w₀) := by rw [hLq]
      _ = L (q.1, q.2 + (w - w₀)) := by rw [← L.map_add, Prod.mk_add_mk, add_zero]
  have hslice' : analyticOrderAt (fun w ↦ F (φ (x₀, w))) w₀ ≠ ⊤ := by
    have hφ_an : AnalyticAt ℂ φ (x₀, w₀) :=
      analyticAt_const.add ((L.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
    have hline_an : AnalyticAt ℂ (fun w : ℂ ↦ (x₀, w)) w₀ := analyticAt_const.prod analyticAt_id
    have _ : AnalyticAt ℂ (fun w ↦ F (φ (x₀, w))) w₀ :=
      ((hφ0.symm ▸ hF).comp hφ_an).comp hline_an
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
  refine ⟨α, hu.unit⁻¹, P, hP, ?_⟩
  rw [hfac, mul_left_comm, hu.val_inv_mul, mul_one]

variable [FiniteDimensional ℂ E]

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
  exists_mul_eq hb := exists_aut_mul_eq_evalVertical x₀ w₀ hb

/-- On a zero-dimensional space, evaluation identifies every holomorphic stalk with `ℂ`, hence it is
a unique factorisation domain. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq_zero (hE : finrank ℂ E = 0) (x : E) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x) := by
  have : Subsingleton E := Module.finrank_zero_iff.1 hE
  exact (evalEquivOfNhdsEqPure (I := 𝓘(ℂ, E)) (congrFun (nhds_discrete E) x)).symm.toMulEquiv
    |>.uniqueFactorizationMonoid inferInstance

/-- If the holomorphic stalks of `E` are unique factorisation domains, so are those of `E × ℂ`. -/
private theorem uniqueFactorizationMonoid_stalk_prod
    (hE : ∀ x : E,
      UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x))
    (p : E × ℂ) :
    UniqueFactorizationMonoid
      ((holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p) := by
  have := hE p.1
  exact (isRueckert_evalVertical p.1 p.2).uniqueFactorizationMonoid

/-- Holomorphic stalks of a finite-dimensional complex normed space are unique factorisation
domains, by induction on the complex dimension. -/
private theorem uniqueFactorizationMonoid_stalk_of_finrank_eq :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V],
      finrank ℂ V = n → ∀ x : V,
        UniqueFactorizationMonoid ((holomorphicStructureSheaf 𝓘(ℂ, V) V).presheaf.stalk x)
  | 0, _, _, _, _, hV, x => uniqueFactorizationMonoid_stalk_of_finrank_eq_zero hV x
  | n + 1, V, _, _, _, hV, x => by
    let e : V ≃L[ℂ] (Fin n → ℂ) × ℂ := ContinuousLinearEquiv.ofFinrankEq (by simp [hV])
    have hprod := uniqueFactorizationMonoid_stalk_prod
      (uniqueFactorizationMonoid_stalk_of_finrank_eq n (Fin n → ℂ) (by simp)) (e x)
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- The stalk of holomorphic functions at any point of a finite-dimensional complex manifold
without boundary is a unique factorisation domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  -- Pass via a chart and a linear equivalence to a model space in `Type`.
  obtain ⟨E', _, _, _, ⟨e⟩⟩ : ∃ (E' : Type) (_ : NormedAddCommGroup E') (_ : NormedSpace ℂ E')
      (_ : FiniteDimensional ℂ E'), Nonempty (E ≃L[ℂ] E') :=
    ⟨Fin (finrank ℂ E) → ℂ, inferInstance, inferInstance, inferInstance,
      ⟨ContinuousLinearEquiv.ofFinrankEq (by simp)⟩⟩
  have hm := uniqueFactorizationMonoid_stalk_of_finrank_eq _ E' rfl ((e ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x e)).toMulEquiv
    |>.uniqueFactorizationMonoid hm

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorisation domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end TauCeti.holomorphicStructureSheaf
