/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Dagger.DaggerAlgebra.ResidueNorm
public import TauCeti.RingTheory.Huber.PowerBounded

import TauCeti.RingTheory.Affinoid.Polyradius
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.Restricted
import TauCeti.RingTheory.Dagger.DaggerAlgebra.FaithfullyFlat
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Dagger.SupSeminorm
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Polynomial
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Radius
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Automatic continuity, canonical residue topology, and functoriality of completion

Let `K` be a complete nontrivially normed ultrametric field. Every `K`-algebra homomorphism
`ψ : W_σ →ₐ[K] E` from a finite-variable Monsky–Washnitzer algebra `W_σ = K⟨X_i⟩†` into an
affinoid `K`-algebra `E` extends uniquely to a `K`-algebra homomorphism `T_σ →ₐ[K] E` from the
unit-radius Tate algebra `T_σ = K⟨X_i⟩`. Indeed, after equipping `E` with a complete ultrametric
algebra norm, every element of `W_σ` with Gauss norm at most `1` (in particular each variable
`X_i`) maps to a power-bounded element of `E`; the universal property of `T_σ` produces a
continuous map `ψ̂ : T_σ →ₐ[K] E` sending each `X_i` to `ψ X_i`. Each `f ∈ W_σ` lies in `T_σ(ρ)`
for some `ρ > 1` in the divisible hull of `|Kˣ|`, where `T_σ(ρ)` is strictly affinoid. By
automatic continuity for affinoid algebras, the restrictions of `ψ` and `ψ̂` to `T_σ(ρ)` are both
continuous and agree on the dense polynomial subalgebra, hence coincide at `f`.

Passing to quotients gives the universal property of the completion `τ : A → Â` of any `K`-dagger
algebra `A`: every `K`-algebra homomorphism `φ : A →ₐ[K] E` into an affinoid `K`-algebra `E`
factors uniquely through `τ`, with no continuity assumed on `φ` or norm fixed on `E`. Whenever
`E` carries a complete ultrametric `K`-algebra norm, `φ` is automatically continuous for the
residue norm of `A`. Specialising to `E = B̂` for a second dagger algebra `B` yields automatic
continuity of every `K`-algebra homomorphism `φ : A →ₐ[K] B` (and of every `W_σ ⧸ I →ₐ[K] W_τ ⧸ J`
for quotient Gauss norms), equivalence of the residue norms of any two presentations of `A`, open
quotient mapping for presentations and surjective morphisms, and functoriality and presentation
independence of the completion `A ↦ Â`.

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.liftToAffinoid`: unique extension of `W_σ →ₐ[K] E` to
  `T_σ →ₐ[K] E` for any affinoid `K`-algebra `E`.
* `TauCeti.Dagger.washnitzerAlgebra.liftQuotientToAffinoid`: unique extension of
  `W_σ ⧸ I →ₐ[K] E` to `T_σ ⧸ I T_σ →ₐ[K] E` for any affinoid `K`-algebra `E`.
* `TauCeti.Dagger.liftToAffinoid`: unique extension of `φ : A →ₐ[K] E` to `Â →ₐ[K] E` for a
  dagger algebra `A` and an affinoid `K`-algebra `E`.
* `TauCeti.Dagger.toContinuousAlgEquiv` and `TauCeti.Dagger.presentationContinuousAlgEquiv`:
  algebra isomorphisms of dagger algebras and comparisons between any two presentations are
  homeomorphisms for the residue norms.
* `TauCeti.Dagger.quotientKerContinuousAlgEquiv`: for any surjective morphism `φ : A →ₐ[K] B` of
  dagger algebras, `A ⧸ ker φ ≃A[K] B` is a homeomorphism for the residue norms.
* `TauCeti.Dagger.mapCompletion` and `TauCeti.Dagger.mapCompletionEquiv`: the completion functor
  `φ ↦ φ̂ : Â →ₐ[K] B̂` and its action on algebra equivalences.
* `TauCeti.Dagger.presentationCompletionEquiv`: for any presentation `π : W_σ ↠ A`, the canonical
  continuous algebra isomorphism `T_σ ⧸ (ker π) T_σ ≃A[K] Â` under `A`.
* `TauCeti.Dagger.completionWashnitzerEquiv`, `TauCeti.Dagger.completionSelfEquiv`, and
  `TauCeti.Dagger.completionQuotientEquiv`: explicit identifications of the completions of `W_σ`,
  `K`, and quotients `A ⧸ I`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.isPowerBounded_map_of_norm_le_one`,
  `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_affinoid`, and
  `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_quotient`: power-boundedness preservation and
  automatic continuity for homomorphisms out of `W_σ` and its quotients `W_σ ⧸ I`.
* `TauCeti.Dagger.existsUnique_algHom_toCompletion`: universal property of `toCompletion K A`
  into affinoid `K`-algebras.
* `TauCeti.Dagger.continuous_algHom` and `TauCeti.Dagger.isPowerBounded_map`: every `K`-algebra
  homomorphism of dagger algebras is continuous for the residue norms and preserves power-bounded
  elements.
* `TauCeti.Dagger.isClosed_ideal`, `TauCeti.Dagger.isOpenQuotientMap_of_presentation`, and
  `TauCeti.Dagger.isOpenQuotientMap`: every ideal of a dagger algebra is closed for the residue
  norm, and every presentation and every surjective morphism is an open quotient map.
* `TauCeti.Dagger.mapCompletion_id`, `TauCeti.Dagger.mapCompletion_comp`,
  `TauCeti.Dagger.continuous_mapCompletion`, `TauCeti.Dagger.mapCompletion_surjective`, and
  `TauCeti.Dagger.isOpenQuotientMap_mapCompletion`: functoriality, continuity, surjectivity, and
  open quotient mapping for `mapCompletion`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 and Theorem 1.7 (1).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries

/-- If an algebra homomorphism `g` vanishes on `f '' I`, then it vanishes on `I.map f`. -/
private theorem algHom_eq_zero_of_mem_ideal_map {k R S T : Type*} [CommSemiring k] [CommRing R]
    [CommRing S] [CommRing T] [Algebra k R] [Algebra k S] [Algebra k T]
    (f : R →ₐ[k] S) (g : S →ₐ[k] T) {I : Ideal R} (h : ∀ a ∈ I, g (f a) = 0)
    {x : S} (hx : x ∈ I.map f) : g x = 0 :=
  RingHom.mem_ker.mp ((Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    simpa [Ideal.mem_comap, RingHom.mem_ker] using h a ha) hx)

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Monsky–Washnitzer algebras into affinoid algebras -/

namespace washnitzerAlgebra

variable {σ : Type*} [Finite σ]

local notation "W " α:max => washnitzerAlgebra α K
local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism from a finite-variable Monsky–Washnitzer algebra into a
completely normed affinoid `K`-algebra maps every element of Gauss norm at most `1` to a
power-bounded element. -/
theorem isPowerBounded_map_of_norm_le_one {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (ψ : W σ →ₐ[K] E) {f : W σ} (hf : ‖f‖ ≤ 1) : Huber.IsPowerBounded (ψ f) := by
  rw [hE.isPowerBounded_iff_forall_pointNorm_le_one]
  intro x
  rw [← hE.pointNorm_maximalSpectrumComap ψ x]
  exact (pointNorm_le_norm _ _).trans hf

/-- Two `K`-algebra homomorphisms from `T_σ` into an affinoid `K`-algebra that agree on the
overconvergent subalgebra `W_σ` are equal. No norm or continuity hypothesis is required. -/
theorem algHom_toTate_ext {E : Type*} [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    {χ₁ χ₂ : T σ →ₐ[K] E} (h : ∀ f : W σ, χ₁ (toTate σ K f) = χ₂ (toTate σ K f)) :
    χ₁ = χ₂ := by
  let := hE.residueNormedCommRing
  let := hE.residueNormedAlgebra
  have := hE.isUltrametricDist_residueNormedCommRing
  have := hE.completeSpace_residueNormedCommRing
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  ext g
  exact congrFun
    ((hE.continuous_algHom χ₁).ext_on denseRange_toTate (hE.continuous_algHom χ₂) <| by
      rintro _ ⟨f, rfl⟩
      exact h f) g

/-- Construct the Tate extension of `ψ : W_σ →ₐ[K] E` when `E` already carries a complete
ultrametric `K`-algebra norm. -/
private noncomputable def liftToAffinoidNormed {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (ψ : W σ →ₐ[K] E) : T σ →ₐ[K] E :=
  let e : σ ≃ Fin (Nat.card σ) := Finite.equivFin σ
  let r : T σ ≃ₐ[K] T (Fin (Nat.card σ)) := IsRestricted.renameAlgEquiv (R := K) e fun _ ↦ 1
  let hb : ∀ j : Fin (Nat.card σ), Huber.IsPowerBounded (ψ (X σ K (e.symm j))) :=
    fun j ↦ isPowerBounded_map_of_norm_le_one hE ψ (norm_X (e.symm j)).le
  (isAffinoidAlgebra_self.restrictedLift hE (Algebra.ofId K E) hb).comp r.toAlgHom

/-- The normed Tate extension agrees with `ψ` on every coordinate variable. -/
private theorem liftToAffinoidNormed_X {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (ψ : W σ →ₐ[K] E) (i : σ) :
    liftToAffinoidNormed hE ψ ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ = ψ (X σ K i) := by
  dsimp only [liftToAffinoidNormed, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [IsRestricted.renameAlgEquiv_X (c := fun _ ↦ (1 : ℝ)), IsAffinoidAlgebra.restrictedLift_X,
    Equiv.symm_apply_apply]

/-- The normed Tate extension extends `ψ` along `toTate`. -/
private theorem liftToAffinoidNormed_toTate {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (ψ : W σ →ₐ[K] E) (f : W σ) :
    liftToAffinoidNormed hE ψ (toTate σ K f) = ψ f := by
  obtain ⟨ρ, hρ1, ⟨m, hm0, a, hpow⟩, hfρ⟩ :=
    mem_washnitzerAlgebra_iff_exists_pow_eq_norm.mp f.2
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ1
  have ha0 : a ≠ 0 := norm_pos_iff.mp (hpow ▸ pow_pos hρ0 m)
  have : Fact (0 < ρ) := ⟨hρ0⟩
  have hTρ : IsAffinoidAlgebra K (IsRestricted.subring (R := K) (fun _ : σ ↦ ρ)) :=
    isAffinoidAlgebra_isRestricted_of_pow_eq_norm fun _ ↦
      ⟨m, Nat.pos_of_ne_zero hm0, Units.mk0 a ha0, hpow⟩
  have := hTρ.isNoetherianRing
  let g₁ : IsRestricted.subring (R := K) (fun _ : σ ↦ ρ) →ₐ[K] E :=
    ψ.comp (ofRestricted hρ1 fun _ ↦ le_rfl)
  let g₂ : IsRestricted.subring (R := K) (fun _ : σ ↦ ρ) →ₐ[K] E :=
    (liftToAffinoidNormed hE ψ).comp
      (MvPowerSeries.restrictedRadiusAlgHom (fun _ ↦ zero_le_one) fun _ ↦ hρ1.le)
  have hpoly :
      g₁.comp (MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ ρ)) =
        g₂.comp (MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ ρ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    have h1 : ofRestricted hρ1 (fun _ ↦ le_rfl)
        (MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ ρ) (MvPolynomial.X i)) = X σ K i :=
      Subtype.ext (by simp)
    have h2 : MvPowerSeries.restrictedRadiusAlgHom (R := K) (fun _ ↦ zero_le_one)
        (fun _ ↦ hρ1.le)
        (MvPowerSeries.polynomialToRestricted (fun _ : σ ↦ ρ) (MvPolynomial.X i)) =
        ⟨MvPowerSeries.X i, isRestricted_X _ i⟩ :=
      Subtype.ext (by simp [MvPowerSeries.restrictedRadiusAlgHom_apply])
    simp only [AlgHom.comp_apply, g₁, g₂, h1, h2, liftToAffinoidNormed_X]
  have heq : (g₁ : _ → E) = g₂ :=
    (hE.continuous_algHom g₁).ext_on
      (MvPowerSeries.denseRange_polynomialToRestricted (R := K) (c := fun _ : σ ↦ ρ))
      (hE.continuous_algHom g₂) <| by
        rintro _ ⟨p, rfl⟩
        exact AlgHom.congr_fun hpoly p
  have hval := congrFun heq ⟨(f : MvPowerSeries σ K), hfρ⟩
  have h1f : ofRestricted hρ1 (fun _ ↦ le_rfl) ⟨(f : MvPowerSeries σ K), hfρ⟩ = f :=
    Subtype.ext (coe_ofRestricted hρ1 (fun _ ↦ le_rfl) _)
  have h2f : MvPowerSeries.restrictedRadiusAlgHom (R := K) (fun _ ↦ zero_le_one)
      (fun _ ↦ hρ1.le) ⟨(f : MvPowerSeries σ K), hfρ⟩ = toTate σ K f :=
    Subtype.ext (by simp [MvPowerSeries.restrictedRadiusAlgHom_apply])
  simpa only [g₁, g₂, AlgHom.comp_apply, h1f, h2f] using hval.symm

/-- **Extension from `W_σ` to `T_σ` into an affinoid algebra.** Every `K`-algebra homomorphism
`ψ : W_σ →ₐ[K] E` into an affinoid `K`-algebra extends uniquely to `T_σ →ₐ[K] E`. No norm or
continuity hypothesis on `E` or `ψ` is required. -/
noncomputable def liftToAffinoid {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) : T σ →ₐ[K] E :=
  let := hE.residueNormedCommRing
  let := hE.residueNormedAlgebra
  have := hE.isUltrametricDist_residueNormedCommRing
  have := hE.completeSpace_residueNormedCommRing
  liftToAffinoidNormed hE ψ

/-- `liftToAffinoid` extends `ψ` along the inclusion `W_σ ⊆ T_σ`. -/
@[simp]
theorem liftToAffinoid_toTate {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) (f : W σ) :
    liftToAffinoid hE ψ (toTate σ K f) = ψ f := by
  let := hE.residueNormedCommRing
  let := hE.residueNormedAlgebra
  have := hE.isUltrametricDist_residueNormedCommRing
  have := hE.completeSpace_residueNormedCommRing
  exact liftToAffinoidNormed_toTate hE ψ f

/-- `liftToAffinoid` factors `ψ` through `toTate`. -/
@[simp]
theorem liftToAffinoid_comp_toTate {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) :
    (liftToAffinoid hE ψ).comp (toTate σ K) = ψ :=
  AlgHom.ext (liftToAffinoid_toTate hE ψ)

/-- `liftToAffinoid` is the unique `K`-algebra homomorphism `T_σ →ₐ[K] E` extending `ψ`. -/
theorem liftToAffinoid_unique {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) {χ : T σ →ₐ[K] E}
    (hχ : ∀ f : W σ, χ (toTate σ K f) = ψ f) : χ = liftToAffinoid hE ψ :=
  algHom_toTate_ext hE fun f ↦ (hχ f).trans (liftToAffinoid_toTate hE ψ f).symm

/-- **Universal property of `toTate : W_σ → T_σ` for affinoid targets.** Every `K`-algebra
homomorphism from `W_σ` into an affinoid `K`-algebra extends uniquely to `T_σ`. -/
theorem existsUnique_algHom_toTate {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) :
    ∃! χ : T σ →ₐ[K] E, χ.comp (toTate σ K) = ψ :=
  ⟨liftToAffinoid hE ψ, liftToAffinoid_comp_toTate hE ψ,
    fun _ hχ ↦ liftToAffinoid_unique hE ψ (AlgHom.congr_fun hχ)⟩

/-- For any complete ultrametric algebra norm on an affinoid `K`-algebra `E`, the extension
`liftToAffinoid hE ψ : T_σ →ₐ[K] E` is continuous. -/
theorem continuous_liftToAffinoid {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) :
    Continuous (liftToAffinoid hE ψ) := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact hE.continuous_algHom (liftToAffinoid hE ψ)

/-- **Automatic continuity on `W_σ` into affinoid algebras.** Every `K`-algebra homomorphism from
a finite-variable Monsky–Washnitzer algebra into a completely normed affinoid `K`-algebra is
continuous for the unit Gauss norm. -/
theorem continuous_algHom_affinoid {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E) (ψ : W σ →ₐ[K] E) :
    Continuous ψ := by
  have h : (ψ : W σ → E) = (liftToAffinoid hE ψ) ∘ (toTate σ K) :=
    funext fun f ↦ (liftToAffinoid_toTate hE ψ f).symm
  rw [h]
  exact (continuous_liftToAffinoid hE ψ).comp isometry_toTate.continuous

/-! ### Presentation quotients `W_σ ⧸ I` -/

/-- Two `K`-algebra homomorphisms from `T_σ ⧸ I T_σ` into an affinoid `K`-algebra that agree on
`W_σ ⧸ I` are equal. -/
theorem algHom_quotientMap_toTate_ext {I : Ideal (W σ)} {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) {χ₁ χ₂ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] E}
    (h : ∀ x : W σ ⧸ I,
      χ₁ (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map x) =
        χ₂ (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map x)) :
    χ₁ = χ₂ := by
  have hcomp :
      χ₁.comp (Ideal.Quotient.mkₐ K (I.map (toTate σ K))) =
        χ₂.comp (Ideal.Quotient.mkₐ K (I.map (toTate σ K))) :=
    algHom_toTate_ext hE fun f ↦ by simpa [Ideal.quotient_map_mkₐ] using h (Ideal.Quotient.mk I f)
  exact AlgHom.ext fun y ↦ by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact AlgHom.congr_fun hcomp g

/-- **Extension from `W_σ ⧸ I` to `T_σ ⧸ I T_σ` into an affinoid algebra.** Every `K`-algebra
homomorphism `φ : W_σ ⧸ I →ₐ[K] E` into an affinoid `K`-algebra extends uniquely along
`W_σ ⧸ I → T_σ ⧸ I T_σ`. -/
noncomputable def liftQuotientToAffinoid {I : Ideal (W σ)} {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (φ : (W σ ⧸ I) →ₐ[K] E) :
    (T σ ⧸ I.map (toTate σ K)) →ₐ[K] E :=
  Ideal.Quotient.liftₐ (I.map (toTate σ K)) (liftToAffinoid hE (φ.comp (Ideal.Quotient.mkₐ K I)))
    fun _ ↦ algHom_eq_zero_of_mem_ideal_map (toTate σ K) _ fun _ hf ↦ by
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hf]

/-- `liftQuotientToAffinoid` evaluated on the class of an overconvergent series `toTate f`. -/
@[simp]
theorem liftQuotientToAffinoid_mk_toTate {I : Ideal (W σ)} {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (φ : (W σ ⧸ I) →ₐ[K] E) (f : W σ) :
    liftQuotientToAffinoid hE φ (Ideal.Quotient.mk (I.map (toTate σ K)) (toTate σ K f)) =
      φ (Ideal.Quotient.mk I f) := by
  rw [liftQuotientToAffinoid, ← Ideal.Quotient.mkₐ_eq_mk K, ← AlgHom.comp_apply,
    Ideal.Quotient.liftₐ_comp]
  simp

/-- `liftQuotientToAffinoid` extends `φ` along `W_σ ⧸ I → T_σ ⧸ I T_σ`. -/
@[simp]
theorem liftQuotientToAffinoid_quotientMap {I : Ideal (W σ)} {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (φ : (W σ ⧸ I) →ₐ[K] E) (x : W σ ⧸ I) :
    liftQuotientToAffinoid hE φ
      (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map x) = φ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp [Ideal.quotient_map_mkₐ]

/-- `liftQuotientToAffinoid` is the unique `K`-algebra homomorphism `T_σ ⧸ I T_σ →ₐ[K] E`
extending `φ`. -/
theorem liftQuotientToAffinoid_unique {I : Ideal (W σ)} {E : Type*} [CommRing E] [Algebra K E]
    (hE : IsAffinoidAlgebra K E) (φ : (W σ ⧸ I) →ₐ[K] E)
    {χ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] E}
    (hχ : ∀ x : W σ ⧸ I,
      χ (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map x) = φ x) :
    χ = liftQuotientToAffinoid hE φ :=
  algHom_quotientMap_toTate_ext hE fun x ↦
    (hχ x).trans (liftQuotientToAffinoid_quotientMap hE φ x).symm

/-- For any complete ultrametric algebra norm on an affinoid `K`-algebra `E`,
`liftQuotientToAffinoid hE φ` is continuous. -/
theorem continuous_liftQuotientToAffinoid {I : Ideal (W σ)} {E : Type*} [NormedCommRing E]
    [NormedAlgebra K E] [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (φ : (W σ ⧸ I) →ₐ[K] E) : Continuous (liftQuotientToAffinoid hE φ) := by
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact continuous_coinduced_dom.mpr <|
    hE.continuous_algHom ((liftQuotientToAffinoid hE φ).comp
      (Ideal.Quotient.mkₐ K (I.map (toTate σ K))))

/-- **Automatic continuity on `W_σ ⧸ I` into affinoid algebras.** Every `K`-algebra homomorphism
from a presentation quotient `W_σ ⧸ I` into a completely normed affinoid `K`-algebra is continuous
for the quotient Gauss norm. -/
theorem continuous_algHom_quotient_affinoid {I : Ideal (W σ)} {E : Type*} [NormedCommRing E]
    [NormedAlgebra K E] [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E)
    (φ : (W σ ⧸ I) →ₐ[K] E) : Continuous φ := by
  have h : (φ : (W σ ⧸ I) → E) =
      (liftQuotientToAffinoid hE φ) ∘
        (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) :=
    funext fun x ↦ (liftQuotientToAffinoid_quotientMap hE φ x).symm
  rw [h]
  exact (continuous_liftQuotientToAffinoid hE φ).comp I.isometry_quotientMap_toTate.continuous

/-- **Automatic continuity for presentation quotients** (Grosse-Klönne, Proposition 1.6 (2)).
Every `K`-algebra homomorphism `W_σ ⧸ I →ₐ[K] W_τ ⧸ J` between quotients of finite-variable
Monsky–Washnitzer algebras is continuous for their quotient Gauss norms. -/
theorem continuous_algHom_quotient {τ : Type*} [Finite τ] {I : Ideal (W σ)} {J : Ideal (W τ)}
    (φ : (W σ ⧸ I) →ₐ[K] (W τ ⧸ J)) : Continuous φ := by
  have hcont : Continuous
      ((Ideal.quotientMapₐ (J.map (toTate τ K)) (toTate τ K) Ideal.le_comap_map).comp φ) :=
    continuous_algHom_quotient_affinoid (K := K) (E := T τ ⧸ J.map (toTate τ K))
      ((isAffinoidAlgebra_tate (K := K) (σ := τ)).quotient _) _
  exact J.isometry_quotientMap_toTate.isEmbedding.isInducing.continuous_iff.mpr hcont

end washnitzerAlgebra

/-! ### Universal property of completion and automatic continuity for dagger algebras -/

section DaggerAlgebra

variable {A B E : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]

/-- Two `K`-algebra homomorphisms out of `completion K A` into an affinoid `K`-algebra that agree
on `A` are equal. No norm or continuity hypothesis is required. -/
theorem algHom_toCompletion_ext [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    {χ₁ χ₂ : completion K A →ₐ[K] E}
    (h : ∀ a : A, χ₁ (toCompletion K A a) = χ₂ (toCompletion K A a)) : χ₁ = χ₂ :=
  washnitzerAlgebra.algHom_quotientMap_toTate_ext hE fun x ↦ by
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa [Ideal.quotient_map_mkₐ, toCompletion_presentation] using h (presentation K A f)

/-- **Universal property of the completion of a dagger algebra (construction).** Every `K`-algebra
homomorphism `φ : A →ₐ[K] E` from a dagger algebra into an affinoid `K`-algebra factors uniquely
through `toCompletion K A : A →ₐ[K] completion K A`. -/
noncomputable def liftToAffinoid [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    (φ : A →ₐ[K] E) : completion K A →ₐ[K] E :=
  washnitzerAlgebra.liftQuotientToAffinoid hE (φ.comp (residueAlgEquiv K A).symm.toAlgHom)

/-- `liftToAffinoid` extends `φ` along `toCompletion K A`. -/
@[simp]
theorem liftToAffinoid_toCompletion [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    (φ : A →ₐ[K] E) (a : A) : liftToAffinoid hE φ (toCompletion K A a) = φ a := by
  obtain ⟨f, rfl⟩ := presentation_surjective K A a
  simp [liftToAffinoid]

/-- `liftToAffinoid` factors `φ` through `toCompletion K A`. -/
@[simp]
theorem liftToAffinoid_comp_toCompletion [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    (φ : A →ₐ[K] E) : (liftToAffinoid hE φ).comp (toCompletion K A) = φ :=
  AlgHom.ext (liftToAffinoid_toCompletion hE φ)

/-- `liftToAffinoid` is the unique `K`-algebra homomorphism `completion K A →ₐ[K] E` extending
`φ`. -/
theorem liftToAffinoid_unique [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    (φ : A →ₐ[K] E) {χ : completion K A →ₐ[K] E}
    (hχ : ∀ a : A, χ (toCompletion K A a) = φ a) : χ = liftToAffinoid hE φ :=
  algHom_toCompletion_ext hE fun a ↦ (hχ a).trans (liftToAffinoid_toCompletion hE φ a).symm

/-- **Universal property of `toCompletion K A`.** The completion `Â` is the reflection of a dagger
algebra `A` into affinoid `K`-algebras: every `K`-algebra homomorphism from `A` into an affinoid
`K`-algebra factors uniquely through `toCompletion K A`. -/
theorem existsUnique_algHom_toCompletion [CommRing E] [Algebra K E] (hE : IsAffinoidAlgebra K E)
    (φ : A →ₐ[K] E) : ∃! χ : completion K A →ₐ[K] E, χ.comp (toCompletion K A) = φ :=
  ⟨liftToAffinoid hE φ, liftToAffinoid_comp_toCompletion hE φ,
    fun _ hχ ↦ liftToAffinoid_unique hE φ (AlgHom.congr_fun hχ)⟩

/-- For any complete ultrametric algebra norm on an affinoid `K`-algebra `E`,
`liftToAffinoid hE φ : completion K A →ₐ[K] E` is continuous. -/
theorem continuous_liftToAffinoid {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E) (φ : A →ₐ[K] E) :
    Continuous (liftToAffinoid hE φ) :=
  washnitzerAlgebra.continuous_liftQuotientToAffinoid hE _

/-- **Automatic continuity into affinoid algebras.** Every `K`-algebra homomorphism from a dagger
algebra into a completely normed affinoid `K`-algebra is continuous for the residue norm. -/
theorem continuous_algHom_affinoid {E : Type*} [NormedCommRing E] [NormedAlgebra K E]
    [IsUltrametricDist E] [CompleteSpace E] (hE : IsAffinoidAlgebra K E) (φ : A →ₐ[K] E) :
    letI := residueNormedCommRing K A
    Continuous φ := by
  let := residueNormedCommRing K A
  have h : (φ : A → E) = (liftToAffinoid hE φ) ∘ (toCompletion K A) :=
    funext fun a ↦ (liftToAffinoid_toCompletion hE φ a).symm
  rw [h]
  exact (continuous_liftToAffinoid hE φ).comp (isometry_toCompletion K A).continuous

/-- **Automatic continuity for morphisms of dagger algebras** (Grosse-Klönne, Proposition 1.6 (2)).
Every `K`-algebra homomorphism between dagger algebras is continuous for their residue norms. -/
theorem continuous_algHom (φ : A →ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Continuous φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  exact (isometry_toCompletion K B).isEmbedding.isInducing.continuous_iff.mpr <|
    continuous_algHom_affinoid (K := K) (E := completion K B)
      (isAffinoidAlgebra_completion (K := K) (A := B)) ((toCompletion K B).comp φ)

/-- Every `K`-algebra homomorphism between dagger algebras maps power-bounded elements to
power-bounded elements for the residue-norm topologies. -/
theorem isPowerBounded_map (φ : A →ₐ[K] B) {a : A} :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    Huber.IsPowerBounded a → Huber.IsPowerBounded (φ a) := by
  let := residueNormedCommRing K A
  let := residueNormedAlgebra K A
  let := residueNormedCommRing K B
  let := residueNormedAlgebra K B
  have := isUltrametricDist_residueNormedCommRing K A
  have := isUltrametricDist_residueNormedCommRing K B
  have := Huber.IsTateRing.of_normedAlgebra K A
  have := Huber.IsTateRing.of_normedAlgebra K B
  intro ha
  exact ha.map_of_isTateRing (f := (φ : A →+* B)) (continuous_algHom φ).continuousAt

variable (K) in
/-- Every ideal of a dagger algebra is closed for the residue norm. -/
theorem isClosed_ideal (I : Ideal A) :
    letI := residueNormedCommRing K A
    IsClosed (I : Set A) := by
  let := residueNormedCommRing K A
  have hc : IsClosed (I.map (toCompletion K A) : Set (completion K A)) :=
    IsAffinoidAlgebra.isClosed_ideal (K := K) (A := completion K A)
      isAffinoidAlgebra_completion _
  exact comap_map_toCompletion K I ▸ hc.preimage (isometry_toCompletion K A).continuous

/-- **Algebra isomorphisms of dagger algebras are homeomorphisms.** Every `K`-algebra isomorphism
between dagger algebras is continuous in both directions for their residue norms. -/
noncomputable def toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    A ≃A[K] B :=
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  { e with
    continuous_toFun := continuous_algHom e.toAlgHom
    continuous_invFun := continuous_algHom e.symm.toAlgHom }

/-- The homeomorphism attached to an algebra isomorphism has the same underlying function. -/
@[simp]
theorem coe_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    ⇑(toContinuousAlgEquiv e) = e :=
  (rfl)

/-- The homeomorphism attached to an algebra isomorphism has that isomorphism as its underlying
algebra isomorphism. -/
@[simp]
theorem toAlgEquiv_toContinuousAlgEquiv (e : A ≃ₐ[K] B) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (toContinuousAlgEquiv e).toAlgEquiv = e :=
  (rfl)

/-- **Independence of presentation for the residue topology.** Any two presentations of a dagger
algebra give homeomorphic residue algebras for their quotient Gauss norms: the residue norms of
any two presentations are equivalent and define a canonical topology on `A`. -/
noncomputable def presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    (washnitzerAlgebra σ K ⧸ RingHom.ker π₁) ≃A[K]
      (washnitzerAlgebra τ K ⧸ RingHom.ker π₂) :=
  let e := (Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
    (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm
  { e with
    continuous_toFun := washnitzerAlgebra.continuous_algHom_quotient e.toAlgHom
    continuous_invFun := washnitzerAlgebra.continuous_algHom_quotient e.symm.toAlgHom }

/-- The underlying function of `presentationContinuousAlgEquiv` is the algebraic comparison. -/
theorem coe_presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂) :
    ⇑(presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂) =
      ⇑((Ideal.quotientKerAlgEquivOfSurjective hπ₁).trans
        (Ideal.quotientKerAlgEquivOfSurjective hπ₂).symm) :=
  (rfl)

/-- The presentation comparison commutes with both presentations. -/
@[simp]
theorem kerLiftAlg_presentationContinuousAlgEquiv {σ τ : Type*} [Finite σ] [Finite τ]
    {C : Type*} [CommRing C] [Algebra K C]
    (π₁ : washnitzerAlgebra σ K →ₐ[K] C) (hπ₁ : Function.Surjective π₁)
    (π₂ : washnitzerAlgebra τ K →ₐ[K] C) (hπ₂ : Function.Surjective π₂)
    (x : washnitzerAlgebra σ K ⧸ RingHom.ker π₁) :
    Ideal.kerLiftAlg π₂ (presentationContinuousAlgEquiv π₁ hπ₁ π₂ hπ₂ x) =
      Ideal.kerLiftAlg π₁ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨g, hg⟩ := hπ₂ (π₁ f)
  simp [coe_presentationContinuousAlgEquiv, ← hg]

/-- Every presentation `π : W_σ ↠ A` of a dagger algebra is an open quotient map for the Gauss
norm on `W_σ` and the residue norm on `A`. -/
theorem isOpenQuotientMap_of_presentation {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    letI := residueNormedCommRing K A
    IsOpenQuotientMap π := by
  let := residueNormedCommRing K A
  let iso : A ≃ᵢ (washnitzerAlgebra _ K ⧸ RingHom.ker (presentation K A)) :=
    { (residueAlgEquiv K A).toEquiv with isometry_toFun := isometry_residueAlgEquiv K A }
  let e : (washnitzerAlgebra σ K ⧸ RingHom.ker π) ≃A[K] A :=
    (presentationContinuousAlgEquiv π hπ (presentation K A) (presentation_surjective K A)).trans
      { (residueAlgEquiv K A).symm with
        continuous_toFun := iso.symm.continuous
        continuous_invFun := iso.continuous }
  have hcomp : (e : _ → A) ∘ (Ideal.Quotient.mk (RingHom.ker π)) = π := funext fun f ↦ by
    rw [Function.comp_apply, ContinuousAlgEquiv.trans_apply]
    exact (residueAlgEquiv_symm_apply K A _).trans <| by
      simpa only [Ideal.kerLiftAlg_mk] using
        kerLiftAlg_presentationContinuousAlgEquiv π hπ (presentation K A)
          (presentation_surjective K A) (Ideal.Quotient.mk (RingHom.ker π) f)
  rw [← hcomp]
  exact e.toHomeomorph.isOpenQuotientMap.comp QuotientAddGroup.isOpenQuotientMap_mk

/-- **Surjective morphisms of dagger algebras are open quotient maps.** Every surjective
`K`-algebra homomorphism `φ : A →ₐ[K] B` between dagger algebras is an open quotient map for the
residue norms, so `B` carries the quotient topology induced by `φ`. -/
theorem isOpenQuotientMap (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    IsOpenQuotientMap φ := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  have hπA := isOpenQuotientMap_of_presentation (presentation K A) (presentation_surjective K A)
  have hπB := isOpenQuotientMap_of_presentation (φ.comp (presentation K A))
    (hφ.comp (presentation_surjective K A))
  refine ⟨hφ, continuous_algHom φ, fun U hU ↦ ?_⟩
  rw [← Set.image_preimage_eq U (presentation_surjective K A), ← Set.image_comp]
  exact hπB.isOpenMap _ (hU.preimage hπA.continuous)

/-- **Topological first isomorphism theorem for dagger algebras.** For a surjective `K`-algebra
homomorphism `φ : A →ₐ[K] B`, the algebraic isomorphism `A ⧸ ker φ ≃ B` is a homeomorphism for the
quotient residue topology on `A ⧸ ker φ` and the residue topology on `B`. -/
noncomputable def quotientKerContinuousAlgEquiv (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (A ⧸ RingHom.ker φ) ≃A[K] B :=
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  let e := Ideal.quotientKerAlgEquivOfSurjective hφ
  have he : (e : A ⧸ RingHom.ker φ → B) = RingHom.kerLift (φ : A →+* B) := funext fun x ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.quotientKerAlgEquivOfSurjective_mk hφ a).trans
      (RingHom.kerLift_mk (f := (φ : A →+* B)) a).symm
  have h : IsHomeomorph e :=
    he ▸ RingHom.isHomeomorph_kerLift (isOpenQuotientMap φ hφ).isQuotientMap
  { e with
    continuous_toFun := h.continuous
    continuous_invFun :=
      (e.toEquiv.toHomeomorphOfContinuousOpen h.continuous h.isOpenMap).symm.continuous }

/-- The underlying algebra isomorphism is the algebraic first isomorphism theorem. -/
@[simp]
theorem toAlgEquiv_quotientKerContinuousAlgEquiv (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    (quotientKerContinuousAlgEquiv φ hφ).toAlgEquiv =
      Ideal.quotientKerAlgEquivOfSurjective hφ :=
  (rfl)

/-- The topological first isomorphism theorem sends the class of `a` to `φ a`. -/
@[simp]
theorem quotientKerContinuousAlgEquiv_mk (φ : A →ₐ[K] B) (hφ : Function.Surjective φ) (a : A) :
    letI := residueNormedCommRing K A
    letI := residueNormedCommRing K B
    quotientKerContinuousAlgEquiv φ hφ (Ideal.Quotient.mk (RingHom.ker φ) a) = φ a := by
  let := residueNormedCommRing K A
  let := residueNormedCommRing K B
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, toAlgEquiv_quotientKerContinuousAlgEquiv,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end DaggerAlgebra

/-! ### Functoriality and presentation independence of completion -/

section Functoriality

variable {A B C : Type*} [CommRing A] [Algebra K A] [IsDaggerAlgebra K A]
  [CommRing B] [Algebra K B] [IsDaggerAlgebra K B]
  [CommRing C] [Algebra K C] [IsDaggerAlgebra K C]

/-- **Functoriality of completion** (Grosse-Klönne, Theorem 1.7 (1)). Every `K`-algebra
homomorphism `φ : A →ₐ[K] B` of dagger algebras extends uniquely to a `K`-algebra homomorphism
`mapCompletion φ : Â →ₐ[K] B̂`. -/
noncomputable def mapCompletion (φ : A →ₐ[K] B) : completion K A →ₐ[K] completion K B :=
  liftToAffinoid isAffinoidAlgebra_completion ((toCompletion K B).comp φ)

/-- `mapCompletion φ` intertwines the completion maps `toCompletion`. -/
@[simp]
theorem mapCompletion_toCompletion (φ : A →ₐ[K] B) (a : A) :
    mapCompletion φ (toCompletion K A a) = toCompletion K B (φ a) :=
  liftToAffinoid_toCompletion isAffinoidAlgebra_completion ((toCompletion K B).comp φ) a

/-- `mapCompletion φ ∘ toCompletion K A = toCompletion K B ∘ φ`. -/
@[simp]
theorem mapCompletion_comp_toCompletion (φ : A →ₐ[K] B) :
    (mapCompletion φ).comp (toCompletion K A) = (toCompletion K B).comp φ :=
  AlgHom.ext (mapCompletion_toCompletion φ)

/-- `mapCompletion φ` is continuous for the quotient Gauss norms on `Â` and `B̂`. -/
theorem continuous_mapCompletion (φ : A →ₐ[K] B) : Continuous (mapCompletion φ) :=
  continuous_liftToAffinoid (K := K) (E := completion K B) isAffinoidAlgebra_completion _

/-- `mapCompletion φ` is the unique `K`-algebra homomorphism `Â →ₐ[K] B̂` compatible with `φ`. -/
theorem mapCompletion_unique (φ : A →ₐ[K] B) {χ : completion K A →ₐ[K] completion K B}
    (hχ : ∀ a : A, χ (toCompletion K A a) = toCompletion K B (φ a)) : χ = mapCompletion φ :=
  liftToAffinoid_unique isAffinoidAlgebra_completion ((toCompletion K B).comp φ) hχ

/-- Completion of the identity is the identity. -/
@[simp]
theorem mapCompletion_id :
    mapCompletion (AlgHom.id K A) = AlgHom.id K (completion K A) :=
  (mapCompletion_unique (AlgHom.id K A) fun _ ↦ rfl).symm

/-- Completion preserves composition of morphisms. -/
@[simp]
theorem mapCompletion_comp (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    mapCompletion (ψ.comp φ) = (mapCompletion ψ).comp (mapCompletion φ) :=
  (mapCompletion_unique (ψ.comp φ) fun a ↦ by simp).symm

/-- Applying `mapCompletion φ` and then `mapCompletion ψ` equals `mapCompletion (ψ.comp φ)`. -/
theorem mapCompletion_mapCompletion (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) (x : completion K A) :
    mapCompletion ψ (mapCompletion φ x) = mapCompletion (ψ.comp φ) x :=
  (AlgHom.congr_fun (mapCompletion_comp ψ φ) x).symm

/-- **Functoriality of completion on algebra isomorphisms.** An isomorphism `e : A ≃ₐ[K] B` of
dagger algebras induces a continuous algebra isomorphism `Â ≃A[K] B̂`. -/
noncomputable def mapCompletionEquiv (e : A ≃ₐ[K] B) : completion K A ≃A[K] completion K B :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion
    (AlgEquiv.ofAlgHom (mapCompletion e.toAlgHom) (mapCompletion e.symm.toAlgHom)
      (by rw [← mapCompletion_comp, AlgEquiv.comp_symm, mapCompletion_id])
      (by rw [← mapCompletion_comp, AlgEquiv.symm_comp, mapCompletion_id]))

/-- The underlying `K`-algebra homomorphism of `mapCompletionEquiv e` is `mapCompletion e`. -/
@[simp]
theorem toAlgHom_mapCompletionEquiv (e : A ≃ₐ[K] B) :
    (mapCompletionEquiv e).toAlgEquiv.toAlgHom = mapCompletion e.toAlgHom := by
  rw [mapCompletionEquiv, IsAffinoidAlgebra.toAlgEquiv_toContinuousAlgEquiv,
    AlgEquiv.toAlgHom_ofAlgHom]

/-- `mapCompletionEquiv e` acts as `mapCompletion e`. -/
@[simp]
theorem coe_mapCompletionEquiv (e : A ≃ₐ[K] B) :
    ⇑(mapCompletionEquiv e) = mapCompletion e.toAlgHom := by
  rw [← ContinuousAlgEquiv.coe_toAlgEquiv, ← AlgEquiv.coe_toAlgHom, toAlgHom_mapCompletionEquiv]

/-- `mapCompletionEquiv e` intertwines the completion maps. -/
theorem mapCompletionEquiv_toCompletion (e : A ≃ₐ[K] B) (a : A) :
    mapCompletionEquiv e (toCompletion K A a) = toCompletion K B (e a) := by
  simp

/-- The inverse of `mapCompletionEquiv e` intertwines the completion maps along `e.symm`. -/
theorem mapCompletionEquiv_symm_toCompletion (e : A ≃ₐ[K] B) (b : B) :
    (mapCompletionEquiv e).symm (toCompletion K B b) = toCompletion K A (e.symm b) := by
  rw [ContinuousAlgEquiv.symm_apply_eq, mapCompletionEquiv_toCompletion, AlgEquiv.apply_symm_apply]

/-- `mapCompletionEquiv` preserves the identity isomorphism. -/
@[simp]
theorem mapCompletionEquiv_refl :
    mapCompletionEquiv (AlgEquiv.refl : A ≃ₐ[K] A) = ContinuousAlgEquiv.refl K (completion K A) :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ by
    simp [coe_mapCompletionEquiv]

/-- `mapCompletionEquiv` preserves composition of isomorphisms. -/
@[simp]
theorem mapCompletionEquiv_trans (e₁ : A ≃ₐ[K] B) (e₂ : B ≃ₐ[K] C) :
    mapCompletionEquiv (e₁.trans e₂) =
      (mapCompletionEquiv e₁).trans (mapCompletionEquiv e₂) :=
  ContinuousAlgEquiv.ext <| funext fun x ↦ by
    rw [coe_mapCompletionEquiv, ContinuousAlgEquiv.trans_apply, coe_mapCompletionEquiv,
      coe_mapCompletionEquiv, mapCompletion_mapCompletion]
    exact congrArg (fun φ ↦ mapCompletion φ x)
      (AlgHom.ext fun a ↦ AlgEquiv.trans_apply e₁ e₂ a)

/-- `mapCompletionEquiv` commutes with taking inverses. -/
@[simp]
theorem mapCompletionEquiv_symm (e : A ≃ₐ[K] B) :
    (mapCompletionEquiv e).symm = mapCompletionEquiv e.symm :=
  ContinuousAlgEquiv.ext <| funext fun b ↦ by
    apply EquivLike.injective (mapCompletionEquiv e)
    simp [mapCompletion_mapCompletion]

/-- **Presentation independence of completion.** For any surjection `π : W_σ ↠ A` from a
finite-variable Monsky–Washnitzer algebra, the affinoid quotient `T_σ ⧸ (ker π) T_σ` is
canonically continuously isomorphic to `completion K A` under `A`. -/
noncomputable def presentationCompletionEquiv {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π) :
    (IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
      (RingHom.ker π).map (washnitzerAlgebra.toTate σ K)) ≃A[K] completion K A :=
  let eA : (washnitzerAlgebra σ K ⧸ RingHom.ker π) ≃ₐ[K] A :=
    Ideal.quotientKerAlgEquivOfSurjective hπ
  let toFun : _ →ₐ[K] completion K A :=
    washnitzerAlgebra.liftQuotientToAffinoid isAffinoidAlgebra_completion
      ((toCompletion K A).comp eA.toAlgHom)
  let invFun : completion K A →ₐ[K] _ :=
    liftToAffinoid ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
      ((Ideal.quotientMapₐ ((RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
        (washnitzerAlgebra.toTate σ K) Ideal.le_comap_map).comp eA.symm.toAlgHom)
  have hleft : toFun.comp invFun = AlgHom.id K (completion K A) :=
    algHom_toCompletion_ext isAffinoidAlgebra_completion fun a ↦ by
      simp only [AlgHom.comp_apply, AlgHom.id_apply, invFun, liftToAffinoid_toCompletion, toFun,
        washnitzerAlgebra.liftQuotientToAffinoid_quotientMap, AlgEquiv.coe_toAlgHom,
        AlgEquiv.apply_symm_apply]
  have hright : invFun.comp toFun = AlgHom.id K _ :=
    washnitzerAlgebra.algHom_quotientMap_toTate_ext
      ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _) fun x ↦ by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, toFun,
          washnitzerAlgebra.liftQuotientToAffinoid_quotientMap, invFun,
          liftToAffinoid_toCompletion, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply]
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) ⧸
      (RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
    (B := completion K A) isAffinoidAlgebra_completion
    (AlgEquiv.ofAlgHom toFun invFun hleft hright)

/-- `presentationCompletionEquiv` sends the class of `toTate f` to `toCompletion K A (π f)`. -/
@[simp]
theorem presentationCompletionEquiv_mk_toTate {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    presentationCompletionEquiv π hπ
      (Ideal.Quotient.mk ((RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
        (washnitzerAlgebra.toTate σ K f)) = toCompletion K A (π f) := by
  rw [presentationCompletionEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv]
  simp

/-- The inverse of `presentationCompletionEquiv` sends `toCompletion K A (π f)` to the class of
`toTate f`. -/
@[simp]
theorem presentationCompletionEquiv_symm_toCompletion {σ : Type*} [Finite σ]
    (π : washnitzerAlgebra σ K →ₐ[K] A) (hπ : Function.Surjective π)
    (f : washnitzerAlgebra σ K) :
    (presentationCompletionEquiv π hπ).symm (toCompletion K A (π f)) =
      Ideal.Quotient.mk ((RingHom.ker π).map (washnitzerAlgebra.toTate σ K))
        (washnitzerAlgebra.toTate σ K f) := by
  rw [← presentationCompletionEquiv_mk_toTate π hπ f, ContinuousAlgEquiv.symm_apply_apply]

/-- A surjective morphism of dagger algebras induces a surjective morphism on completions. -/
theorem mapCompletion_surjective {φ : A →ₐ[K] B} (hφ : Function.Surjective φ) :
    Function.Surjective (mapCompletion φ) := by
  set πA := presentation K A
  set πB := φ.comp πA
  have hπB : Function.Surjective πB := hφ.comp (presentation_surjective K A)
  have hle : (RingHom.ker πA).map (washnitzerAlgebra.toTate _ K) ≤
      (RingHom.ker πB).map (washnitzerAlgebra.toTate _ K) :=
    Ideal.map_mono fun f hf ↦ by
      rw [RingHom.mem_ker] at hf ⊢
      simp [πB, hf]
  let q : completion K A →ₐ[K]
      IsRestricted.subring (R := K) (fun _ ↦ (1 : ℝ)) ⧸
        (RingHom.ker πB).map (washnitzerAlgebra.toTate _ K) :=
    Ideal.quotientMapₐ _ (AlgHom.id K _) (by simpa using hle)
  have hq : Function.Surjective q := fun y ↦ by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ g, by simp [q, Ideal.quotient_map_mkₐ]⟩
  have heq : ((presentationCompletionEquiv πB hπB).toAlgEquiv.toAlgHom).comp q =
      mapCompletion φ :=
    mapCompletion_unique φ fun a ↦ by
      obtain ⟨f, rfl⟩ := presentation_surjective K A a
      simp [q, πB, πA, toCompletion_presentation]
  rw [← heq]
  exact (presentationCompletionEquiv πB hπB).surjective.comp hq

/-- A surjective morphism of dagger algebras induces an open quotient map on completions. -/
theorem isOpenQuotientMap_mapCompletion {φ : A →ₐ[K] B} (hφ : Function.Surjective φ) :
    IsOpenQuotientMap (mapCompletion φ) := by
  have := (isAffinoidAlgebra_completion (K := K) (A := A)).isNoetherianRing
  exact IsAffinoidAlgebra.isOpenQuotientMap (K := K) (A := completion K A) (B := completion K B)
    isAffinoidAlgebra_completion (mapCompletion φ) (mapCompletion_surjective hφ)

variable (K) in
/-- **The completion of `W_σ` is `T_σ`.** The completion of the Monsky–Washnitzer algebra in
finitely many variables is canonically continuously isomorphic to the unit-radius Tate algebra,
intertwining `toCompletion` and `toTate`. -/
noncomputable def completionWashnitzerEquiv (σ : Type*) [Finite σ] :
    completion K (washnitzerAlgebra σ K) ≃A[K]
      IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)) :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K)
    (A := completion K (washnitzerAlgebra σ K))
    (B := IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ)))
    isAffinoidAlgebra_tate
    (AlgEquiv.ofAlgHom
      (liftToAffinoid isAffinoidAlgebra_tate (washnitzerAlgebra.toTate σ K))
      (washnitzerAlgebra.liftToAffinoid isAffinoidAlgebra_completion
        (toCompletion K (washnitzerAlgebra σ K)))
      (washnitzerAlgebra.algHom_toTate_ext isAffinoidAlgebra_tate fun f ↦ by simp)
      (algHom_toCompletion_ext isAffinoidAlgebra_completion fun f ↦ by simp))

/-- `completionWashnitzerEquiv` sends `toCompletion f` to `toTate f`. -/
@[simp]
theorem completionWashnitzerEquiv_toCompletion {σ : Type*} [Finite σ] (f : washnitzerAlgebra σ K) :
    completionWashnitzerEquiv K σ (toCompletion K (washnitzerAlgebra σ K) f) =
      washnitzerAlgebra.toTate σ K f := by
  rw [completionWashnitzerEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv,
    AlgEquiv.ofAlgHom_apply, liftToAffinoid_toCompletion]

/-- The inverse of `completionWashnitzerEquiv` sends `toTate f` to `toCompletion f`. -/
@[simp]
theorem completionWashnitzerEquiv_symm_toTate {σ : Type*} [Finite σ] (f : washnitzerAlgebra σ K) :
    (completionWashnitzerEquiv K σ).symm (washnitzerAlgebra.toTate σ K f) =
      toCompletion K (washnitzerAlgebra σ K) f := by
  rw [ContinuousAlgEquiv.symm_apply_eq, completionWashnitzerEquiv_toCompletion]

variable (K) in
/-- **The completion of the coefficient field is itself.** -/
noncomputable def completionSelfEquiv : completion K K ≃A[K] K :=
  IsAffinoidAlgebra.toContinuousAlgEquiv (K := K) (A := completion K K) (B := K)
    isAffinoidAlgebra_self
    (AlgEquiv.ofAlgHom
      (liftToAffinoid isAffinoidAlgebra_self (AlgHom.id K K))
      (Algebra.ofId K (completion K K))
      (AlgHom.ext fun c ↦ by simp)
      (algHom_toCompletion_ext isAffinoidAlgebra_completion fun c ↦ by
        simp only [AlgHom.comp_apply, AlgHom.id_apply, liftToAffinoid_toCompletion,
          Algebra.ofId_apply]
        exact (AlgHom.commutes (toCompletion K K) c).symm))

/-- `completionSelfEquiv` sends `toCompletion K K c` to `c`. -/
@[simp]
theorem completionSelfEquiv_toCompletion (c : K) :
    completionSelfEquiv K (toCompletion K K c) = c := by
  rw [completionSelfEquiv, IsAffinoidAlgebra.coe_toContinuousAlgEquiv,
    AlgEquiv.ofAlgHom_apply, liftToAffinoid_toCompletion, AlgHom.id_apply]

/-- The inverse of `completionSelfEquiv` is `toCompletion K K`. -/
@[simp]
theorem completionSelfEquiv_symm_apply (c : K) :
    (completionSelfEquiv K).symm c = toCompletion K K c := by
  rw [ContinuousAlgEquiv.symm_apply_eq, completionSelfEquiv_toCompletion]

/-- The forward map `completion K (A ⧸ I) →ₐ[K] Â ⧸ I Â` of `completionQuotientEquiv`. -/
private noncomputable def completionQuotientToFun (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {A : Type*} [CommRing A] [Algebra K A]
    [IsDaggerAlgebra K A] (I : Ideal A) :
    completion K (A ⧸ I) →ₐ[K] (completion K A ⧸ I.map (toCompletion K A)) :=
  liftToAffinoid ((isAffinoidAlgebra_completion (K := K) (A := A)).quotient _)
    (Ideal.quotientMapₐ (I.map (toCompletion K A)) (toCompletion K A) Ideal.le_comap_map)

/-- The inverse map `Â ⧸ I Â →A[K] completion K (A ⧸ I)` of `completionQuotientEquiv`. -/
private noncomputable def completionQuotientInvFun (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {A : Type*} [CommRing A] [Algebra K A]
    [IsDaggerAlgebra K A] (I : Ideal A) :
    (completion K A ⧸ I.map (toCompletion K A)) →A[K] completion K (A ⧸ I) :=
  Ideal.Quotient.liftA (I.map (toCompletion K A))
    ⟨mapCompletion (Ideal.Quotient.mkₐ K I), continuous_mapCompletion _⟩
    fun _ ↦ algHom_eq_zero_of_mem_ideal_map (toCompletion K A)
      (mapCompletion (Ideal.Quotient.mkₐ K I)) fun _ ha ↦ by
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr ha]

/-- `completionQuotientInvFun` sends the quotient class of `z ∈ Â` to `mapCompletion mk z`. -/
private theorem completionQuotientInvFun_mk (I : Ideal A) (z : completion K A) :
    completionQuotientInvFun K I (Ideal.Quotient.mk (I.map (toCompletion K A)) z) =
      mapCompletion (Ideal.Quotient.mkₐ K I) z := by
  rw [completionQuotientInvFun, Ideal.Quotient.liftA_mk]
  exact congrFun (ContinuousAlgHom.coe_mk' _ _) z

/-- `completionQuotientToFun` is a left inverse to `completionQuotientInvFun`. -/
private theorem completionQuotientToFun_comp_invFun (I : Ideal A) :
    (completionQuotientToFun K I).comp (completionQuotientInvFun K I).toAlgHom = AlgHom.id K _ := by
  have hQ : IsAffinoidAlgebra K (completion K A ⧸ I.map (toCompletion K A)) :=
    (isAffinoidAlgebra_completion (K := K) (A := A)).quotient _
  have hcomp :
      ((completionQuotientToFun K I).comp (completionQuotientInvFun K I).toAlgHom).comp
          (Ideal.Quotient.mkₐ K (I.map (toCompletion K A))) =
        Ideal.Quotient.mkₐ K (I.map (toCompletion K A)) :=
    algHom_toCompletion_ext hQ fun a ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ContinuousAlgHom.coe_coe,
        completionQuotientInvFun_mk, mapCompletion_toCompletion, completionQuotientToFun,
        liftToAffinoid_toCompletion, Ideal.quotient_map_mkₐ]
  exact AlgHom.ext fun y ↦ by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact AlgHom.congr_fun hcomp x

/-- `completionQuotientInvFun` is a left inverse to `completionQuotientToFun`. -/
private theorem completionQuotientInvFun_comp_toFun (I : Ideal A) :
    (completionQuotientInvFun K I).toAlgHom.comp (completionQuotientToFun K I) =
      AlgHom.id K (completion K (A ⧸ I)) :=
  algHom_toCompletion_ext isAffinoidAlgebra_completion fun q ↦ by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [AlgHom.comp_apply, AlgHom.id_apply, ContinuousAlgHom.coe_coe,
      completionQuotientToFun, liftToAffinoid_toCompletion, Ideal.quotient_map_mkₐ,
      completionQuotientInvFun_mk, mapCompletion_toCompletion, Ideal.Quotient.mkₐ_eq_mk]

/-- The forward map of `completionQuotientEquiv` is continuous. -/
private theorem continuous_completionQuotientToFun (I : Ideal A) :
    Continuous (completionQuotientToFun K I) :=
  (isOpenQuotientMap_mapCompletion
    (φ := Ideal.Quotient.mkₐ K I) Ideal.Quotient.mk_surjective).isQuotientMap.continuous_iff.mpr <|
    by
      have h : ⇑(completionQuotientToFun K I) ∘ ⇑(mapCompletion (Ideal.Quotient.mkₐ K I)) =
          ⇑(Ideal.Quotient.mkA K (I.map (toCompletion K A))) := funext fun x ↦ by
        rw [Function.comp_apply, Ideal.Quotient.mkA_apply, ← completionQuotientInvFun_mk I x,
          ← ContinuousAlgHom.coe_coe (completionQuotientInvFun K I), ← AlgHom.comp_apply,
          completionQuotientToFun_comp_invFun, AlgHom.id_apply]
      rw [h]
      exact (Ideal.Quotient.mkA K (I.map (toCompletion K A))).continuous

/-- **Completion commutes with quotients.** For any ideal `I` of a dagger algebra `A`, the
completion of `A ⧸ I` is canonically continuously isomorphic to `Â ⧸ I Â`. -/
noncomputable def completionQuotientEquiv (I : Ideal A) :
    completion K (A ⧸ I) ≃A[K] (completion K A ⧸ I.map (toCompletion K A)) :=
  { AlgEquiv.ofAlgHom (completionQuotientToFun K I) (completionQuotientInvFun K I).toAlgHom
      (completionQuotientToFun_comp_invFun I) (completionQuotientInvFun_comp_toFun I) with
    continuous_toFun :=
      (continuous_completionQuotientToFun I).congr fun x ↦
        (AlgEquiv.ofAlgHom_apply (completionQuotientToFun K I)
          (completionQuotientInvFun K I).toAlgHom (completionQuotientToFun_comp_invFun I)
          (completionQuotientInvFun_comp_toFun I) x).symm
    continuous_invFun :=
      (completionQuotientInvFun K I).continuous.congr fun y ↦
        (congrFun (ContinuousAlgHom.coe_coe (completionQuotientInvFun K I)) y).symm.trans
          (AlgEquiv.ofAlgHom_symm_apply (completionQuotientToFun K I)
            (completionQuotientInvFun K I).toAlgHom (completionQuotientToFun_comp_invFun I)
            (completionQuotientInvFun_comp_toFun I) y).symm }

/-- `completionQuotientEquiv` sends `toCompletion (mk a)` to `mk (toCompletion a)`. -/
@[simp]
theorem completionQuotientEquiv_toCompletion_mk (I : Ideal A) (a : A) :
    completionQuotientEquiv I (toCompletion K (A ⧸ I) (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I.map (toCompletion K A)) (toCompletion K A a) := by
  simp only [completionQuotientEquiv, ContinuousAlgEquiv.coe_mk, AlgEquiv.ofAlgHom_apply,
    completionQuotientToFun, liftToAffinoid_toCompletion, Ideal.quotient_map_mkₐ,
    Ideal.Quotient.mkₐ_eq_mk]

/-- The inverse of `completionQuotientEquiv` sends `mk (toCompletion a)` to
`toCompletion (mk a)`. -/
@[simp]
theorem completionQuotientEquiv_symm_mk_toCompletion (I : Ideal A) (a : A) :
    (completionQuotientEquiv I).symm
      (Ideal.Quotient.mk (I.map (toCompletion K A)) (toCompletion K A a)) =
        toCompletion K (A ⧸ I) (Ideal.Quotient.mk I a) := by
  rw [← completionQuotientEquiv_toCompletion_mk I a, ContinuousAlgEquiv.symm_apply_apply]

end Functoriality

end TauCeti.Dagger
