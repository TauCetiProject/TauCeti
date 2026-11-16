/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.SmoothComparison
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Weierstrass
public import TauCeti.RingTheory.Polynomial.Rueckert

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Domain
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.StalkPullback
import TauCeti.RingTheory.Polynomial.Distinguished

/-!
# Holomorphic stalks are unique factorization domains

The ring `𝒪_{X, x}` of germs of holomorphic functions at a point of a finite-dimensional complex
manifold without boundary is a unique factorization domain (factorial domain). Through the
comparison `smoothStalkIso`, the same holds for the stalks of Mathlib's complex-smooth structure
sheaf.

The proof follows the classical induction on the complex dimension `n = Module.finrank ℂ E` via
Weierstrass preparation and Rückert's descent (`RingHom.IsRueckert`):

* For `n = 0`, evaluation identifies the stalk with `ℂ`, a field and hence a unique factorization
  domain.
* On a product `E × ℂ` with `E` finite-dimensional, vertical polynomial evaluation
  `evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies `RingHom.IsRueckert`
  for the set of polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`
  (`TauCeti.holomorphicStructureSheaf.evalVertical_isRueckert`). Every nonzero germ becomes regular
  in the last variable after an affine automorphism fixing `(x₀, w₀)`
  (`AnalyticAt.exists_continuousLinearEquiv_analyticOrderAt_ne_top`), Weierstrass preparation and
  division supply the factorization and quotient comparison, and monic factors of distinguished
  polynomials remain distinguished (`Polynomial.IsDistinguishedAt.of_dvd`).
* `RingHom.IsRueckert.uniqueFactorizationMonoid` passes unique factorization from `𝒪_{E, x₀}` to
  `𝒪_{E × ℂ, (x₀, w₀)}`, and charts composed with a linear equivalence `E ≃L[ℂ] (Fin n → ℂ)`
  transport the result to arbitrary finite-dimensional complex manifolds without boundary.

As immediate consequences of the Rückert hypotheses and factoriality, a distinguished polynomial
`P ∈ (𝒪_{E, x₀})[X]` is prime (respectively irreducible) in `(𝒪_{E, x₀})[X]` if and only if
`evalVertical x₀ w₀ P` is prime (respectively irreducible) in `𝒪_{E × ℂ, (x₀, w₀)}`, and the same
holds for any germ admitting `P` as its Weierstrass polynomial.

## Main declarations

* `TauCeti.holomorphicStructureSheaf.evalVertical_isRueckert`: `evalVertical x₀ w₀` satisfies the
  Rückert hypotheses for the distinguished polynomials over `𝒪_{E, x₀}`.
* `TauCeti.holomorphicStructureSheaf.stalkUniqueFactorizationMonoid`: holomorphic stalks are unique
  factorization domains.
* `TauCeti.holomorphicStructureSheaf.smoothStalkUniqueFactorizationMonoid`: so are the stalks of
  Mathlib's complex-smooth structure sheaf.
* `TauCeti.holomorphicStructureSheaf.isPrime_span_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.prime_evalVertical_iff_of_isDistinguishedAt`,
  `TauCeti.holomorphicStructureSheaf.irreducible_evalVertical_iff_of_isDistinguishedAt`:
  primality and irreducibility of a distinguished polynomial agree in `(𝒪_{E, x₀})[X]` and in
  `𝒪_{E × ℂ, (x₀, w₀)}`.
* `TauCeti.holomorphicStructureSheaf.prime_iff_of_weierstrassPreparation`,
  `TauCeti.holomorphicStructureSheaf.irreducible_iff_of_weierstrassPreparation`: the same
  comparison for any Weierstrass factorization `f = evalVertical x₀ w₀ P * u`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, Theorem 2.10.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II, §B.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §6.1.
* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.2.5.
-/

public noncomputable section

open Filter Module Polynomial Topology
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

section Rueckert

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Transporting a stalk along an equality of base points as a ring isomorphism. -/
private def stalkEquivOfEq {q₁ q₂ : E × ℂ} (h : q₁ = q₂) :
    (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk q₁ ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk q₂ := by
  subst h
  exact RingEquiv.refl _

/-- Transporting a stalk element along an equality of base points preserves its function germ. -/
private theorem toFilterGerm_stalkEquivOfEq {q₁ q₂ : E × ℂ} (h : q₁ = q₂)
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk q₁} {F : E × ℂ → ℂ}
    (hfF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) q₁ (𝓝 q₁) le_rfl f = F) :
    toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) q₂ (𝓝 q₂) le_rfl (stalkEquivOfEq h f) = F := by
  subst h
  exact hfF

/-- Pullback along the affine automorphism `z ↦ L (z - p) + p`, fixing `p`, as a ring automorphism
of the holomorphic stalk at `p`. -/
private def affineStalkAut (L : (E × ℂ) ≃L[ℂ] (E × ℂ)) (p : E × ℂ) :
    (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p ≃+*
      (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p :=
  let ψ : E × ℂ → E × ℂ := fun z ↦ L (z - p) + p
  let ψ' : E × ℂ → E × ℂ := fun z ↦ L.symm (z - p) + p
  have hψp : p = ψ p := by simp [ψ]
  have hψ : ∀ᶠ z in 𝓝 p, ContMDiffAt 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω ψ z :=
    Eventually.of_forall fun _ ↦
      ((L.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const).contMDiff.contMDiffAt
  have hψ' : ∀ᶠ z in 𝓝 (ψ p), ContMDiffAt 𝓘(ℂ, E × ℂ) 𝓘(ℂ, E × ℂ) ω ψ' z :=
    Eventually.of_forall fun _ ↦
      ((L.symm.contDiff.comp (contDiff_id.sub contDiff_const)).add
        contDiff_const).contMDiff.contMDiffAt
  have hbij : Function.Bijective (stalkPullback hψ) :=
    stalkPullback_bijective hψ hψ'
      (Eventually.of_forall fun z ↦ by simp [ψ, ψ'])
      (Eventually.of_forall fun z ↦ by simp [ψ, ψ'])
  (stalkEquivOfEq hψp).trans (RingEquiv.ofBijective _ hbij)

/-- The function germ of a stalk element pulled back by `affineStalkAut L p`. -/
private theorem toFilterGerm_affineStalkAut (L : (E × ℂ) ≃L[ℂ] (E × ℂ)) {p : E × ℂ}
    {f : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk p} {F : E × ℂ → ℂ}
    (hfF : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) p (𝓝 p) le_rfl f = F) :
    toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) p (𝓝 p) le_rfl (affineStalkAut L p f) =
      (fun z ↦ F (L (z - p) + p) : E × ℂ → ℂ) := by
  dsimp only [affineStalkAut, RingEquiv.trans_apply, RingEquiv.ofBijective_apply]
  rw [toFilterGerm_stalkPullback, toFilterGerm_stalkEquivOfEq _ hfF, Filter.Germ.coe_compTendsto]
  rfl

variable [FiniteDimensional ℂ E]

/-- **Holomorphic stalks satisfy the Rückert hypotheses.** Vertical polynomial evaluation
`evalVertical x₀ w₀ : (𝒪_{E, x₀})[X] →+* 𝒪_{E × ℂ, (x₀, w₀)}` satisfies `RingHom.IsRueckert` with
the set of polynomials distinguished at the maximal ideal of `𝒪_{E, x₀}`. -/
theorem evalVertical_isRueckert (x₀ : E) (w₀ : ℂ) :
    (evalVertical x₀ w₀).IsRueckert
      {P | P.IsDistinguishedAt
        (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))} where
  injective := evalVertical_injective x₀ w₀
  monic hw := hw.monic
  mem_of_dvd hw hp hpw :=
    hw.of_dvd (IsLocalRing.maximalIdeal.isMaximal _).isPrime.isRadical hp hpw
  dvd_iff hw p := (evalVertical_dvd_iff_of_isDistinguishedAt hw).symm
  exists_dvd_sub {w} hw b := by
    obtain ⟨⟨q, r⟩, ⟨-, hb⟩, -⟩ := existsUnique_weierstrassDivision_of_isDistinguishedAt hw b
    exact ⟨r, q, sub_eq_of_eq_add hb⟩
  exists_mul_eq {b} hb := by
    obtain ⟨F, hF, hbF⟩ := exists_analyticAt_toFilterGerm_eq (x₀, w₀) b
    obtain ⟨L, ⟨x₁, w₁⟩, hLq, hslice⟩ := hF.exists_continuousLinearEquiv_analyticOrderAt_ne_top
      ((eq_zero_iff_of_toFilterGerm_eq (hbF _ le_rfl)).not.1 hb)
    let α := affineStalkAut L (x₀, w₀)
    have hαb : toFilterGerm 𝓘(ℂ, E × ℂ) (E × ℂ) (x₀, w₀) (𝓝 (x₀, w₀)) le_rfl (α b) =
        (fun z ↦ F (L (z - (x₀, w₀)) + (x₀, w₀)) : E × ℂ → ℂ) :=
      toFilterGerm_affineStalkAut L (hbF _ le_rfl)
    -- Shifting the vertical slice at `x₀` by `w₀ - w₁` recovers the vertical slice of `F ∘ L`.
    have hslice' :
        analyticOrderAt (fun w ↦ F (L ((x₀, w) - (x₀, w₀)) + (x₀, w₀))) w₀ ≠ ⊤ := by
      rw [Ne, analyticOrderAt_eq_top] at hslice ⊢
      intro hzero
      apply hslice
      have ht : Tendsto (fun w : ℂ ↦ w₀ + (w - w₁)) (𝓝 w₁) (𝓝 w₀) := by
        have : Continuous fun w : ℂ ↦ w₀ + (w - w₁) := by fun_prop
        simpa using this.tendsto w₁
      filter_upwards [ht.eventually hzero] with w hw
      have hsub : ((x₀, w₀ + (w - w₁)) - (x₀, w₀) : E × ℂ) = (0, w - w₁) := by
        ext <;> simp
      have heq : L ((x₀, w₀ + (w - w₁)) - (x₀, w₀)) + (x₀, w₀) = L (x₁, w) := by
        rw [hsub, ← hLq, ← L.map_add]
        congr 1
        ext <;> simp
      simpa only [heq] using hw
    obtain ⟨⟨P, u⟩, ⟨hP, hu, hfac⟩, -⟩ :=
      existsUnique_weierstrassPreparation ((map_residue_verticalPowerSeries_ne_zero_iff hαb).2
        hslice')
    refine ⟨α, hu.unit⁻¹, P, hP, ?_⟩
    rw [hfac, mul_comm (evalVertical x₀ w₀ P), ← mul_assoc, IsUnit.val_inv_mul, one_mul]

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` generates a prime ideal after vertical
evaluation in `𝒪_{E × ℂ, (x₀, w₀)}` if and only if it generates a prime ideal in `(𝒪_{E, x₀})[X]`.
-/
theorem isPrime_span_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    (Ideal.span {evalVertical x₀ w₀ P}).IsPrime ↔ (Ideal.span {P}).IsPrime :=
  (evalVertical_isRueckert x₀ w₀).isPrime_span_apply_iff hP

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` becomes a prime germ under vertical evaluation
if and only if it is prime in `(𝒪_{E, x₀})[X]`. -/
theorem prime_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Prime (evalVertical x₀ w₀ P) ↔ Prime P :=
  (evalVertical_isRueckert x₀ w₀).prime_apply_iff hP

/-- For a Weierstrass factorization `f = evalVertical x₀ w₀ P * u`, the germ `f` is prime in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if the distinguished polynomial `P` is prime in
`(𝒪_{E, x₀})[X]`. -/
theorem prime_iff_of_weierstrassPreparation {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    Prime f ↔ Prime P := by
  rw [hf, prime_mul_iff, or_iff_left (fun h ↦ h.2.not_isUnit hu),
    and_iff_left hu, prime_evalVertical_iff_of_isDistinguishedAt hP]

end Rueckert

section Induction

/-- Holomorphic stalks of `Fin n → ℂ` are unique factorization domains, by induction on `n` using
evaluation at `n = 0` and Rückert's factorial descent for the inductive step. -/
private theorem uniqueFactorizationMonoid_stalk_fin :
    ∀ (n : ℕ) (x : Fin n → ℂ),
      UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, Fin n → ℂ) (Fin n → ℂ)).presheaf.stalk x)
  | 0, x => by
    let e : (holomorphicStructureSheaf 𝓘(ℂ, Fin 0 → ℂ) (Fin 0 → ℂ)).presheaf.stalk x ≃+* ℂ :=
      RingEquiv.ofBijective (eval 𝓘(ℂ, Fin 0 → ℂ) (Fin 0 → ℂ) x)
        ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ by
          obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
          refine (eq_zero_iff_of_toFilterGerm_eq (hφ _ le_rfl)).2 (Eventually.of_forall fun y ↦ ?_)
          rw [Subsingleton.elim y x, ← eval_eq_of_toFilterGerm_eq (hφ _ le_rfl), hs, Pi.zero_apply],
        eval_surjective _ _ x⟩
    exact e.symm.toMulEquiv.uniqueFactorizationMonoid inferInstance
  | n + 1, x => by
    let e : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin n → ℂ) × ℂ :=
      ContinuousLinearEquiv.ofFinrankEq (by simp)
    have := uniqueFactorizationMonoid_stalk_fin n (e x).1
    have hprod : UniqueFactorizationMonoid
        ((holomorphicStructureSheaf 𝓘(ℂ, (Fin n → ℂ) × ℂ) ((Fin n → ℂ) × ℂ)).presheaf.stalk
          (e x)) :=
      (evalVertical_isRueckert (e x).1 (e x).2).uniqueFactorizationMonoid
    exact (RingEquiv.ofBijective _ (e.holomorphicStalkPullback_bijective x)).toMulEquiv
      |>.uniqueFactorizationMonoid hprod

end Induction

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- **Holomorphic stalks are unique factorization domains.** The stalk of holomorphic functions at
any point of a finite-dimensional complex manifold without boundary is a factorial domain. -/
instance stalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let e : E ≃L[ℂ] (Fin (finrank ℂ E) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hfin := uniqueFactorizationMonoid_stalk_fin (finrank ℂ E) ((e ∘ extChartAt I x) x)
  exact (RingEquiv.ofBijective _ (stalkPullback_comp_extChartAt_bijective x e)).toMulEquiv
    |>.uniqueFactorizationMonoid hfin

/-- A stalk of Mathlib's complex-smooth structure sheaf on a finite-dimensional complex manifold
without boundary is a unique factorization domain, via its comparison with holomorphic germs. -/
instance smoothStalkUniqueFactorizationMonoid (x : X) :
    UniqueFactorizationMonoid ((smoothSheafCommRing I 𝓘(ℂ) X ℂ).presheaf.stalk x) :=
  (smoothStalkIso I X x).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
    inferInstance

end Manifold

section Irreducible

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- A distinguished polynomial `P ∈ (𝒪_{E, x₀})[X]` is irreducible in `𝒪_{E × ℂ, (x₀, w₀)}` after
vertical evaluation if and only if it is irreducible in `(𝒪_{E, x₀})[X]`. -/
theorem irreducible_evalVertical_iff_of_isDistinguishedAt {x₀ : E} {w₀ : ℂ}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀))) :
    Irreducible (evalVertical x₀ w₀ P) ↔ Irreducible P := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime,
    UniqueFactorizationMonoid.irreducible_iff_prime,
    prime_evalVertical_iff_of_isDistinguishedAt hP]

/-- For a Weierstrass factorization `f = evalVertical x₀ w₀ P * u`, the germ `f` is irreducible in
`𝒪_{E × ℂ, (x₀, w₀)}` if and only if its distinguished polynomial `P` is irreducible in
`(𝒪_{E, x₀})[X]`. -/
theorem irreducible_iff_of_weierstrassPreparation {x₀ : E} {w₀ : ℂ}
    {f u : (holomorphicStructureSheaf 𝓘(ℂ, E × ℂ) (E × ℂ)).presheaf.stalk (x₀, w₀)}
    {P : ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)[X]}
    (hP : P.IsDistinguishedAt
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) E).presheaf.stalk x₀)))
    (hu : IsUnit u) (hf : f = evalVertical x₀ w₀ P * u) :
    Irreducible f ↔ Irreducible P := by
  rw [UniqueFactorizationMonoid.irreducible_iff_prime,
    UniqueFactorizationMonoid.irreducible_iff_prime,
    prime_iff_of_weierstrassPreparation hP hu hf]

end Irreducible

end TauCeti.holomorphicStructureSheaf
