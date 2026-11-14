/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Basic
public import TauCeti.RingTheory.Dagger.WashnitzerAlgebra
public import TauCeti.RingTheory.Huber.PowerBounded

import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.Restricted
import TauCeti.RingTheory.Dagger.SupSeminorm
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# Universal extension of homomorphisms from Monsky–Washnitzer to Tate algebras

Let `K` be a complete nontrivially normed ultrametric field, `W_σ = K⟨Xᵢ⟩†` the Monsky–Washnitzer
algebra in a finite family `σ` of variables, and `T_σ = K⟨Xᵢ⟩` the unit-radius Tate algebra. This
file proves that `toTate σ K : W_σ →ₐ[K] T_σ` is initial among `K`-algebra homomorphisms from `W_σ`
into `K`-affinoid algebras, with no norm or continuity assumed on the target, and deduces the
corresponding universal property for every presentation quotient `W_σ ⧸ I → T_σ ⧸ I T_σ`:

* Every classical point of an affinoid algebra `S` contracts along `ψ : W_σ →ₐ[K] S` to a classical
  point of `W_σ`, where each variable `Xᵢ` has absolute value at most `‖Xᵢ‖ = 1`. Equipping `S`
  with its residue norm (`TauCeti.IsAffinoidAlgebra.residueNormedCommRing`), `|ψ Xᵢ|sup ≤ 1`, so
  `ψ Xᵢ` is power-bounded (`TauCeti.IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`).
* Restricted evaluation (`TauCeti.IsAffinoidAlgebra.restrictedLift`) gives a `K`-algebra
  homomorphism `Ψ : T_σ →ₐ[K] S` sending each `Xᵢ` to `ψ Xᵢ`. Because `S` is noetherian and its
  quotients `S ⧸ m ^ k` by powers of maximal ideals are finite over `K`, `Ψ ∘ toTate` and `ψ` agree
  modulo every `m ^ k` (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral`), hence
  globally by Krull's intersection theorem (`Ideal.iInf_isMaximal_pow_eq_bot`).
* Uniqueness on `T_σ` and on `T_σ ⧸ I T_σ` follows from automatic continuity into `S` together with
  density of `W_σ` in `T_σ` (`TauCeti.IsAffinoidAlgebra.algHom_ext_of_denseRange`).

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.liftToTate`: the unique `K`-algebra extension `T_σ →ₐ[K] S` of
  a homomorphism `W_σ →ₐ[K] S` into an affinoid algebra.
* `TauCeti.Dagger.washnitzerAlgebra.liftToTateQuotient`: the induced `K`-algebra extension
  `(T_σ ⧸ I T_σ) →ₐ[K] S` of a homomorphism `W_σ →ₐ[K] S` vanishing on an ideal `I`.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isNoetherianRing` and
  `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isAffinoidAlgebra`: `K`-algebra maps out of `W_σ`
  into a noetherian `K`-algebra with finite maximal-power quotients (in particular any affinoid
  algebra) are determined by the coordinate variables.
* `TauCeti.Dagger.washnitzerAlgebra.isPowerBounded_map_X`: any `K`-algebra map from `W_σ` into a
  completely normed affinoid algebra sends each variable `Xᵢ` to a power-bounded element.
* `TauCeti.Dagger.washnitzerAlgebra.tate_algHom_ext_of_isAffinoidAlgebra`,
  `TauCeti.Dagger.washnitzerAlgebra.tateQuotient_algHom_ext_of_isAffinoidAlgebra`,
  `TauCeti.Dagger.washnitzerAlgebra.existsUnique_algHom_toTate`, and
  `TauCeti.Dagger.washnitzerAlgebra.existsUnique_algHom_tateQuotient`: uniqueness and universal
  properties of `W_σ → T_σ` and `W_σ ⧸ I → T_σ ⧸ I T_σ` for affinoid targets.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1.2 and Theorem 1.7 (1).
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.3.

The extension and uniqueness arguments adapt the restricted-series universal property in
`TauCeti.RingTheory.Affinoid.Restricted` and automatic continuity in
`TauCeti.RingTheory.Affinoid.Continuity` and `TauCeti.RingTheory.Affinoid.QuotientNorm` to
Monsky–Washnitzer algebras.
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

section AlgHomExt

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **Homomorphisms from `W_σ` separated by finite maximal-power quotients are determined by the
variables.** If `R` is a noetherian `K`-algebra whose quotients `R ⧸ m ^ k` by all powers of
maximal ideals are finite over `K`, then two `K`-algebra homomorphisms `W_σ →ₐ[K] R` agreeing on
every coordinate variable are equal. No continuity or norm on `R` is assumed. -/
theorem algHom_ext_of_isNoetherianRing {R : Type*} [CommRing R] [Algebra K R]
    [IsNoetherianRing R]
    (hfin : ∀ (m : Ideal R) [m.IsMaximal] (k : ℕ), Module.Finite K (R ⧸ m ^ k))
    {φ ψ : washnitzerAlgebra σ K →ₐ[K] R} (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  ext f
  suffices φ f - ψ f ∈ (⊥ : Ideal R) from sub_eq_zero.mp this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm k _
  let := hm
  have := hfin m k
  have : Algebra.IsIntegral K (R ⧸ m ^ k) := Algebra.IsIntegral.of_finite K _
  let q := Ideal.Quotient.mkₐ K (m ^ k)
  have hq : q.comp φ = q.comp ψ := algHom_ext_of_isIntegral fun i ↦ by simp [h i]
  exact Ideal.Quotient.eq_zero_iff_mem.mp
    (by simpa [q, map_sub] using sub_eq_zero.mpr (AlgHom.congr_fun hq f))

/-- **`K`-algebra homomorphisms from `W_σ` into an affinoid algebra are determined by the
variables**, with no continuity assumed. -/
theorem algHom_ext_of_isAffinoidAlgebra {R : Type*} [CommRing R] [Algebra K R]
    (hR : IsAffinoidAlgebra K R) {φ ψ : washnitzerAlgebra σ K →ₐ[K] R}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ :=
  have := hR.isNoetherianRing
  algHom_ext_of_isNoetherianRing (fun m _ k ↦ hR.finite_quotient_pow m k) h

end AlgHomExt

section TateLift

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "T " α:max => IsRestricted.subring (R := K) (fun _ : α ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism from `W_σ` into a completely normed affinoid algebra maps each
coordinate variable to a power-bounded element. -/
theorem isPowerBounded_map_X {S : Type*} [NormedCommRing S] [NormedAlgebra K S]
    [IsUltrametricDist S] [CompleteSpace S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (i : σ) : Huber.IsPowerBounded (ψ (X σ K i)) := by
  rw [hS.isPowerBounded_iff_supSeminorm_le_one]
  refine supSeminorm_le zero_le_one fun x ↦ ?_
  rw [← hS.pointNorm_maximalSpectrumComap ψ x]
  exact (pointNorm_le_norm _ (X σ K i)).trans_eq (norm_X i)

/-- Two `K`-algebra homomorphisms from the Tate algebra `T_σ` into an affinoid algebra that agree on
`W_σ` are equal. No norm or continuity on the target is required. -/
theorem tate_algHom_ext_of_isAffinoidAlgebra {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) {Φ₁ Φ₂ : T σ →ₐ[K] S}
    (h : ∀ f, Φ₁ (toTate σ K f) = Φ₂ (toTate σ K f)) : Φ₁ = Φ₂ :=
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  hS.algHom_ext_of_denseRange denseRange_toTate h

/-- **Extension of homomorphisms along `W_σ ⊆ T_σ`.** Every `K`-algebra homomorphism
`ψ : W_σ →ₐ[K] S` into an affinoid algebra extends to a `K`-algebra homomorphism `T_σ →ₐ[K] S`. -/
noncomputable def liftToTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) : T σ →ₐ[K] S :=
  letI := Fintype.ofFinite σ
  letI := hS.residueNormedCommRing
  letI := hS.residueNormedAlgebra
  haveI := hS.isUltrametricDist_residueNormedCommRing
  haveI := hS.completeSpace_residueNormedCommRing
  let e := Fintype.equivFin σ
  (isAffinoidAlgebra_self.restrictedLift hS (Algebra.ofId K S)
    (b := fun j ↦ ψ (X σ K (e.symm j)))
    (fun j ↦ isPowerBounded_map_X hS ψ (e.symm j))).comp
    (IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ))).toAlgHom

/-- `liftToTate` sends each variable `Xᵢ` of `T_σ` to `ψ (Xᵢ)`. -/
@[simp]
theorem liftToTate_X {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (i : σ) :
    liftToTate hS ψ ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ = ψ (X σ K i) := by
  let := Fintype.ofFinite σ
  let := hS.residueNormedCommRing
  let := hS.residueNormedAlgebra
  have := hS.isUltrametricDist_residueNormedCommRing
  have := hS.completeSpace_residueNormedCommRing
  let e := Fintype.equivFin σ
  have hren := IsRestricted.renameAlgEquiv_X (R := K) e (fun _ ↦ (1 : ℝ)) i
  simp [liftToTate, e, hren]

/-- `liftToTate` restricts to `ψ` along `toTate`. -/
@[simp]
theorem liftToTate_comp_toTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) : (liftToTate hS ψ).comp (toTate σ K) = ψ := by
  refine algHom_ext_of_isAffinoidAlgebra hS fun i ↦ ?_
  have hX : toTate σ K (X σ K i) = ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ :=
    Subtype.ext (by simp)
  simp [hX]

/-- `liftToTate` agrees with `ψ` on every overconvergent series. -/
@[simp]
theorem liftToTate_toTate {S : Type*} [CommRing S] [Algebra K S] (hS : IsAffinoidAlgebra K S)
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (f : washnitzerAlgebra σ K) :
    liftToTate hS ψ (toTate σ K f) = ψ f :=
  AlgHom.congr_fun (liftToTate_comp_toTate hS ψ) f

/-- **Universal property of `toTate`.** Every `K`-algebra homomorphism from `W_σ` into an affinoid
algebra extends uniquely along `W_σ → T_σ`. -/
theorem existsUnique_algHom_toTate {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (ψ : washnitzerAlgebra σ K →ₐ[K] S) :
    ∃! Φ : T σ →ₐ[K] S, Φ.comp (toTate σ K) = ψ :=
  ⟨liftToTate hS ψ, liftToTate_comp_toTate hS ψ, fun _ hΦ ↦
    tate_algHom_ext_of_isAffinoidAlgebra hS fun f ↦ by
      rw [← AlgHom.comp_apply, hΦ, liftToTate_toTate]⟩

/-- Two `K`-algebra homomorphisms from a Tate presentation quotient `T_σ ⧸ I T_σ` into an affinoid
algebra that agree on the image of `W_σ` are equal. No norm or continuity on the target is
required. -/
theorem tateQuotient_algHom_ext_of_isAffinoidAlgebra {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) {I : Ideal (washnitzerAlgebra σ K)}
    {Φ₁ Φ₂ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] S}
    (h : ∀ f, Φ₁ (Ideal.Quotient.mk _ (toTate σ K f)) =
      Φ₂ (Ideal.Quotient.mk _ (toTate σ K f))) : Φ₁ = Φ₂ := by
  have := ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient
    (I.map (toTate σ K))).isNoetherianRing
  have hd : DenseRange (Ideal.Quotient.mk (I.map (toTate σ K)) ∘ toTate σ K) :=
    Ideal.Quotient.mk_surjective.denseRange.comp denseRange_toTate continuous_quot_mk
  exact hS.algHom_ext_of_denseRange
    (g := Ideal.Quotient.mk (I.map (toTate σ K)) ∘ toTate σ K) hd h

/-- **Extension of homomorphisms to Tate quotients.** Every `K`-algebra homomorphism
`ψ : W_σ →ₐ[K] S` into an affinoid algebra that vanishes on an ideal `I` extends across
`W_σ ⊆ T_σ` and descends to a `K`-algebra homomorphism `(T_σ ⧸ I T_σ) →ₐ[K] S`. -/
noncomputable def liftToTateQuotient {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (I : Ideal (washnitzerAlgebra σ K))
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (hI : ∀ f ∈ I, ψ f = 0) :
    (T σ ⧸ I.map (toTate σ K)) →ₐ[K] S :=
  have hker : I.map (toTate σ K) ≤ RingHom.ker (liftToTate hS ψ) :=
    Ideal.map_le_iff_le_comap.mpr fun f hf ↦ by
      rw [Ideal.mem_comap, RingHom.mem_ker, liftToTate_toTate, hI f hf]
  Ideal.Quotient.liftₐ (I.map (toTate σ K)) (liftToTate hS ψ)
    fun _ hx ↦ RingHom.mem_ker.mp (hker hx)

/-- `liftToTateQuotient` evaluates as `ψ` on the quotient class of `toTate σ K f`. -/
@[simp]
theorem liftToTateQuotient_mk_toTate {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (I : Ideal (washnitzerAlgebra σ K))
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (hI : ∀ f ∈ I, ψ f = 0)
    (f : washnitzerAlgebra σ K) :
    liftToTateQuotient hS I ψ hI (Ideal.Quotient.mk _ (toTate σ K f)) = ψ f :=
  (Ideal.Quotient.lift_mk _ _ _).trans (liftToTate_toTate hS ψ f)

/-- Precomposing `liftToTateQuotient` with the canonical map `W_σ ⧸ I →ₐ[K] T_σ ⧸ I T_σ` recovers
`Ideal.Quotient.liftₐ I ψ hI`. -/
@[simp]
theorem liftToTateQuotient_comp_quotientMap {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (I : Ideal (washnitzerAlgebra σ K))
    (ψ : washnitzerAlgebra σ K →ₐ[K] S) (hI : ∀ f ∈ I, ψ f = 0) :
    (liftToTateQuotient hS I ψ hI).comp
      (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) =
      Ideal.Quotient.liftₐ I ψ hI :=
  Ideal.Quotient.algHom_ext K (AlgHom.ext (liftToTateQuotient_mk_toTate hS I ψ hI))

/-- **Universal property of `W_σ ⧸ I → T_σ ⧸ I T_σ`.** Every `K`-algebra homomorphism from a
Monsky–Washnitzer presentation quotient `W_σ ⧸ I` into an affinoid algebra extends uniquely along
the canonical map `W_σ ⧸ I →ₐ[K] T_σ ⧸ I T_σ`. -/
theorem existsUnique_algHom_tateQuotient {S : Type*} [CommRing S] [Algebra K S]
    (hS : IsAffinoidAlgebra K S) (I : Ideal (washnitzerAlgebra σ K))
    (φ : (washnitzerAlgebra σ K ⧸ I) →ₐ[K] S) :
    ∃! Φ : (T σ ⧸ I.map (toTate σ K)) →ₐ[K] S,
      Φ.comp (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) = φ := by
  have hI : ∀ f ∈ I, (φ.comp (Ideal.Quotient.mkₐ K I)) f = 0 := fun f hf ↦ by
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
  refine ⟨liftToTateQuotient hS I (φ.comp (Ideal.Quotient.mkₐ K I)) hI, ?_, fun Φ hΦ ↦ ?_⟩
  · dsimp only
    rw [liftToTateQuotient_comp_quotientMap]
    exact Ideal.Quotient.algHom_ext K (AlgHom.ext fun _ ↦ rfl)
  · refine tateQuotient_algHom_ext_of_isAffinoidAlgebra hS fun f ↦ ?_
    simpa using AlgHom.congr_fun hΦ (Ideal.Quotient.mk I f)

end TateLift

end TauCeti.Dagger.washnitzerAlgebra
