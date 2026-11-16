/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Continuity
public import TauCeti.RingTheory.Dagger.ClosedIdeal

import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Dagger.QuotientCompletion
import TauCeti.RingTheory.Dagger.SupSeminorm
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.RingTheory.Huber.OpenIdeal
import TauCeti.RingTheory.Ideal.KrullIntersection
import TauCeti.RingTheory.Ideal.Quotient.Integral
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniversalProperty

/-!
# Automatic continuity and Tate extensions of Monsky–Washnitzer homomorphisms

Let `K` be a complete ultrametric normed field, `W = K⟨X⟩†` the Monsky–Washnitzer algebra of
overconvergent power series in finitely many variables `σ`, and `T = K⟨X⟩` the corresponding
unit-radius Tate algebra.

First, `K`-algebra homomorphisms from `W` into a noetherian `K`-algebra whose maximal ideals have
residue fields integral over `K` are determined by their values on the variables `Xᵢ`, with no
continuity assumption (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral_quotient`).
Indeed, modulo every power `m ^ n` of a maximal ideal `m`, the quotient is integral over `K`, so
the two homomorphisms agree there by Weierstrass division
(`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral`); Krull's intersection theorem then
forces them to agree globally, including when the target is nonreduced. In particular this applies
to every `K`-affinoid algebra (`TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isAffinoidAlgebra`).

Over a nontrivially normed `K`, every `K`-algebra homomorphism `ψ : W → C` into a `K`-affinoid
algebra extends uniquely to a `K`-algebra homomorphism `Ψ : T → C` along `W ⊆ T`
(`TauCeti.Dagger.washnitzerAlgebra.toTateLift`), and no continuity is assumed on either `ψ` or `Ψ`.
At every classical point of `C`, the absolute value of `ψ(Xᵢ)` is bounded by `‖Xᵢ‖ = 1`, so each
`ψ(Xᵢ)` is power-bounded for any complete ultrametric algebra norm on `C`. The universal property
of the Tate algebra (`TauCeti.MvPowerSeries.restrictedLift`) supplies a continuous `Ψ : T → C`
with `Ψ(Xᵢ) = ψ(Xᵢ)`, and `algHom_ext_of_isAffinoidAlgebra` forces `Ψ ∘ toTate = ψ`. Consequently
`ψ` is automatically continuous for the Gauss norm on `W`
(`TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_of_isAffinoidAlgebra`).

The same argument descends to quotients: for an ideal `I` of `W`, every `K`-algebra homomorphism
`W ⧸ I → C` into an affinoid algebra extends uniquely to `T ⧸ I T → C`
(`TauCeti.Dagger.washnitzerAlgebra.quotientToTateLift`) and is automatically continuous for the
residue Gauss norm. Since `W' ⧸ J → T' ⧸ J T'` is an isometry, every `K`-algebra homomorphism
`W ⧸ I → W' ⧸ J` between presentation quotients is automatically continuous for their residue
Gauss norms (`TauCeti.Dagger.washnitzerAlgebra.continuous_quotient_algHom`).

## Main definitions

* `TauCeti.Dagger.washnitzerAlgebra.toTateLift`: the unique `K`-algebra extension `T →ₐ[K] C`
  of a `K`-algebra homomorphism `W →ₐ[K] C` into an affinoid algebra.
* `TauCeti.Dagger.washnitzerAlgebra.quotientToTateLift`: the unique `K`-algebra extension
  `(T ⧸ I T) →ₐ[K] C` of a `K`-algebra homomorphism `(W ⧸ I) →ₐ[K] C` into an affinoid algebra.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isIntegral_quotient` and
  `TauCeti.Dagger.washnitzerAlgebra.algHom_ext_of_isAffinoidAlgebra`: `K`-algebra homomorphisms
  out of `W` into a noetherian algebra with integral residue fields (in particular an affinoid
  algebra) are determined by their values on the variables.
* `TauCeti.Dagger.washnitzerAlgebra.toTateLift_toTate`,
  `TauCeti.Dagger.washnitzerAlgebra.toTateLift_unique`,
  `TauCeti.Dagger.washnitzerAlgebra.existsUnique_algHom_comp_toTate`: universal property of
  `W ⊆ T` for homomorphisms into affinoid algebras.
* `TauCeti.Dagger.washnitzerAlgebra.continuous_algHom_of_isAffinoidAlgebra` and
  `TauCeti.Dagger.washnitzerAlgebra.isPowerBounded_map_of_isAffinoidAlgebra`: automatic continuity
  and preservation of power-boundedness for `W →ₐ[K] C`.
* `TauCeti.Dagger.washnitzerAlgebra.continuous_quotient_algHom_of_isAffinoidAlgebra` and
  `TauCeti.Dagger.washnitzerAlgebra.continuous_quotient_algHom`: automatic continuity for
  homomorphisms out of quotients `W ⧸ I` into affinoid algebras and into quotients `W' ⧸ J`.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, Proposition 1.6 (2).
-/

public section

namespace TauCeti.Dagger.washnitzerAlgebra

open _root_.MvPowerSeries

section Extensionality

variable {K σ : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ]

/-- **Homomorphisms from `W` into noetherian algebras with integral residue fields are determined
by the variables.** If `B` is a noetherian `K`-algebra whose quotient by every maximal ideal is
integral over `K`, then two `K`-algebra homomorphisms `K⟨X⟩† → B` agreeing on every variable `Xᵢ`
are equal. No continuity, norm, or reducedness hypothesis is needed. -/
theorem algHom_ext_of_isIntegral_quotient {B : Type*} [CommRing B] [Algebra K B]
    [IsNoetherianRing B] (hB : ∀ (m : Ideal B) [m.IsMaximal], Algebra.IsIntegral K (B ⧸ m))
    {φ ψ : washnitzerAlgebra σ K →ₐ[K] B} (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ := by
  ext f
  rw [← sub_eq_zero]
  suffices φ f - ψ f ∈ (⊥ : Ideal B) from this
  rw [← Ideal.iInf_isMaximal_pow_eq_bot]
  simp only [Ideal.mem_iInf]
  intro m hm n _
  have := hm
  have := hB m
  have : Algebra.IsIntegral K (B ⧸ m ^ n) := ⟨fun x ↦ by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact TauCeti.isIntegral_quotient_pow_of_isIntegral_quotient
      (Algebra.IsIntegral.isIntegral (Ideal.Quotient.mk m b)) n⟩
  have heq : (Ideal.Quotient.mkₐ K (m ^ n)).comp φ = (Ideal.Quotient.mkₐ K (m ^ n)).comp ψ :=
    algHom_ext_of_isIntegral fun i ↦ congrArg (Ideal.Quotient.mkₐ K (m ^ n)) (h i)
  exact Ideal.Quotient.eq.mp (DFunLike.congr_fun heq f)

/-- **Homomorphisms from `W` into an affinoid algebra are determined by the variables.** Two
`K`-algebra homomorphisms `K⟨X⟩† → C` into an affinoid algebra agreeing on every `Xᵢ` are equal,
with no continuity or norm assumed. -/
theorem algHom_ext_of_isAffinoidAlgebra {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) {φ ψ : washnitzerAlgebra σ K →ₐ[K] C}
    (h : ∀ i, φ (X σ K i) = ψ (X σ K i)) : φ = ψ :=
  have := hC.isNoetherianRing
  algHom_ext_of_isIntegral_quotient (fun m _ ↦
    have := hC.finite_quotient_of_isMaximal m
    Algebra.IsIntegral.of_finite K _) h

end Extensionality

section TateLift

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W" => washnitzerAlgebra σ K
local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- Every `K`-algebra homomorphism from `W` into a completely normed affinoid algebra sends each
variable `Xᵢ` to a power-bounded element. -/
private theorem isPowerBounded_map_X {C : Type*} [NormedCommRing C] [NormedAlgebra K C]
    [IsUltrametricDist C] [CompleteSpace C] (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) (i : σ) :
    Huber.IsPowerBounded (ψ (X σ K i)) := by
  rw [hC.isPowerBounded_iff_forall_pointNorm_le_one]
  intro y
  rw [← hC.pointNorm_maximalSpectrumComap ψ y]
  exact (pointNorm_le_norm _ (X σ K i)).trans (norm_X i).le

/-- Construction of the Tate-algebra extension when the affinoid target already carries a complete
ultrametric `K`-algebra norm. -/
private noncomputable def toTateLiftAux {C : Type*} [NormedCommRing C] [NormedAlgebra K C]
    [IsUltrametricDist C] [CompleteSpace C] (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) :
    T →ₐ[K] C :=
  let e : σ ≃ Fin (Finite.exists_equiv_fin σ).choose :=
    (Finite.exists_equiv_fin σ).choose_spec.some
  let ren : T ≃ₐ[K] IsRestricted.subring (R := K) (fun _ : Fin _ ↦ (1 : ℝ)) :=
    IsRestricted.renameAlgEquiv e fun _ ↦ 1
  let lift : IsRestricted.subring (R := K) (fun _ : Fin _ ↦ (1 : ℝ)) →ₐ[K] C :=
    { TauCeti.MvPowerSeries.restrictedLift (φ := algebraMap K C) (continuous_algebraMap K C)
        (fun j ↦ isPowerBounded_map_X hC ψ (e.symm j)) with
      commutes' := TauCeti.MvPowerSeries.restrictedLift_algebraMap _ _ }
  lift.comp ren.toAlgHom

private theorem toTateLiftAux_toTate_X {C : Type*} [NormedCommRing C] [NormedAlgebra K C]
    [IsUltrametricDist C] [CompleteSpace C] (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) (i : σ) :
    toTateLiftAux hC ψ (toTate σ K (X σ K i)) = ψ (X σ K i) := by
  simp only [toTateLiftAux, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_mk]
  set e : σ ≃ Fin (Finite.exists_equiv_fin σ).choose :=
    (Finite.exists_equiv_fin σ).choose_spec.some
  have hren : IsRestricted.renameAlgEquiv e (fun _ ↦ (1 : ℝ)) (toTate σ K (X σ K i)) =
      ⟨_root_.MvPowerSeries.X (e i), isRestricted_X _ (e i)⟩ := by
    apply Subtype.ext
    rw [IsRestricted.coe_renameAlgEquiv]
    simp
  rw [hren, TauCeti.MvPowerSeries.restrictedLift_X, Equiv.symm_apply_apply]

private theorem toTateLiftAux_comp_toTate {C : Type*} [NormedCommRing C] [NormedAlgebra K C]
    [IsUltrametricDist C] [CompleteSpace C] (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) :
    (toTateLiftAux hC ψ).comp (toTate σ K) = ψ :=
  algHom_ext_of_isAffinoidAlgebra hC fun i ↦ toTateLiftAux_toTate_X hC ψ i

/-- **The Tate-algebra extension of a Monsky–Washnitzer homomorphism.** Every `K`-algebra
homomorphism `ψ : K⟨X⟩† → C` into a `K`-affinoid algebra extends uniquely to a `K`-algebra
homomorphism `K⟨X⟩ → C` along `W ⊆ T`. No norm or continuity is assumed on `C` or `ψ`. -/
noncomputable def toTateLift {C : Type*} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : W →ₐ[K] C) : T →ₐ[K] C :=
  letI := hC.residueNormedCommRing
  letI := hC.residueNormedAlgebra
  have := hC.isUltrametricDist_residueNormedCommRing
  have := hC.completeSpace_residueNormedCommRing
  toTateLiftAux hC ψ

/-- `toTateLift hC ψ` restricts to `ψ` along `W ⊆ T`. -/
@[simp]
theorem toTateLift_comp_toTate {C : Type*} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : W →ₐ[K] C) : (toTateLift hC ψ).comp (toTate σ K) = ψ :=
  letI := hC.residueNormedCommRing
  letI := hC.residueNormedAlgebra
  have := hC.isUltrametricDist_residueNormedCommRing
  have := hC.completeSpace_residueNormedCommRing
  toTateLiftAux_comp_toTate hC ψ

/-- `toTateLift hC ψ` extends `ψ` on every overconvergent series. -/
@[simp]
theorem toTateLift_toTate {C : Type*} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : W →ₐ[K] C) (f : W) : toTateLift hC ψ (toTate σ K f) = ψ f :=
  DFunLike.congr_fun (toTateLift_comp_toTate hC ψ) f

/-- `toTateLift hC ψ` sends each Tate variable `Xᵢ` to `ψ(Xᵢ)`. -/
@[simp]
theorem toTateLift_X {C : Type*} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    (ψ : W →ₐ[K] C) (i : σ) :
    toTateLift hC ψ ⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ = ψ (X σ K i) := by
  have hX : (⟨_root_.MvPowerSeries.X i, isRestricted_X _ i⟩ : T) = toTate σ K (X σ K i) :=
    Subtype.ext (by simp)
  rw [hX, toTateLift_toTate]

/-- **Uniqueness of the Tate-algebra extension.** Any `K`-algebra homomorphism `K⟨X⟩ → C` into an
affinoid algebra restricting to `ψ` on `K⟨X⟩†` equals `toTateLift hC ψ`. No continuity is assumed
on `Φ` or `ψ`. -/
theorem toTateLift_unique {C : Type*} [CommRing C] [Algebra K C] (hC : IsAffinoidAlgebra K C)
    {ψ : W →ₐ[K] C} {Φ : T →ₐ[K] C} (hΦ : Φ.comp (toTate σ K) = ψ) :
    Φ = toTateLift hC ψ := by
  let := hC.residueNormedCommRing
  let := hC.residueNormedAlgebra
  have := hC.isUltrametricDist_residueNormedCommRing
  have := hC.completeSpace_residueNormedCommRing
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  exact DFunLike.coe_injective <| denseRange_toTate.equalizer (hC.continuous_algHom Φ)
    (hC.continuous_algHom (toTateLift hC ψ))
    (funext fun f ↦ (DFunLike.congr_fun hΦ f).trans (toTateLift_toTate hC ψ f).symm)

/-- **Universal property of `W ⊆ T` for affinoid targets.** Every `K`-algebra homomorphism
`K⟨X⟩† → C` into a `K`-affinoid algebra extends uniquely to `K⟨X⟩ → C`. -/
theorem existsUnique_algHom_comp_toTate {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) :
    ∃! Φ : T →ₐ[K] C, Φ.comp (toTate σ K) = ψ :=
  ⟨toTateLift hC ψ, toTateLift_comp_toTate hC ψ, fun _ hΦ ↦ toTateLift_unique hC hΦ⟩

/-- Extending the inclusion `W ⊆ T` itself yields the identity on `T`. -/
@[simp]
theorem toTateLift_toTate_id :
    toTateLift (isAffinoidAlgebra_tate (K := K) (σ := σ)) (toTate σ K) = AlgHom.id K T :=
  (toTateLift_unique isAffinoidAlgebra_tate (AlgHom.id_comp _)).symm

/-- Naturality of `toTateLift`: postcomposing with an algebra map between affinoid algebras
commutes with extending to the Tate algebra. -/
theorem toTateLift_comp {C D : Type*} [CommRing C] [Algebra K C] [CommRing D] [Algebra K D]
    (hC : IsAffinoidAlgebra K C) (hD : IsAffinoidAlgebra K D) (θ : C →ₐ[K] D) (ψ : W →ₐ[K] C) :
    toTateLift hD (θ.comp ψ) = θ.comp (toTateLift hC ψ) :=
  (toTateLift_unique hD (by rw [AlgHom.comp_assoc, toTateLift_comp_toTate])).symm

section NormedTarget

variable {C : Type*} [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]

/-- The Tate-algebra extension `toTateLift hC ψ` is continuous for every complete ultrametric
algebra norm on the affinoid target `C`. -/
theorem continuous_toTateLift (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) :
    Continuous (toTateLift hC ψ) :=
  have := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  hC.continuous_algHom (toTateLift hC ψ)

/-- **Automatic continuity for Monsky–Washnitzer algebras.** Every `K`-algebra homomorphism
`K⟨X⟩† → C` into a completely normed affinoid algebra is continuous for the unit Gauss norm. -/
theorem continuous_algHom_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C) :
    Continuous ψ := by
  rw [← toTateLift_comp_toTate hC ψ]
  exact (continuous_toTateLift hC ψ).comp isometry_toTate.continuous

/-- Every `K`-algebra homomorphism `K⟨X⟩† → C` into a completely normed affinoid algebra preserves
power-bounded elements. -/
theorem isPowerBounded_map_of_isAffinoidAlgebra (hC : IsAffinoidAlgebra K C) (ψ : W →ₐ[K] C)
    {f : W} (hf : Huber.IsPowerBounded f) : Huber.IsPowerBounded (ψ f) :=
  have := Huber.IsTateRing.of_normedAlgebra K W
  have := Huber.IsTateRing.of_normedAlgebra K C
  hf.map_of_isTateRing (f := (ψ : W →+* C))
    (continuous_algHom_of_isAffinoidAlgebra hC ψ).continuousAt

end NormedTarget

end TateLift

section Quotient

variable {K σ : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [Finite σ]

local notation "W" => washnitzerAlgebra σ K
local notation "T" => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- **The Tate-quotient extension of a homomorphism out of `W ⧸ I`.** Every `K`-algebra
homomorphism `ψ : W ⧸ I → C` into a `K`-affinoid algebra extends uniquely to `T ⧸ I T → C` along
`W ⧸ I → T ⧸ I T`. No norm or continuity is assumed on `C` or `ψ`. -/
noncomputable def quotientToTateLift {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) :
    (T ⧸ I.map (toTate σ K)) →ₐ[K] C :=
  Ideal.Quotient.liftₐ (I.map (toTate σ K)) (toTateLift hC (ψ.comp (Ideal.Quotient.mkₐ K I)))
    fun t ht ↦ by
      have hle : I.map (toTate σ K) ≤
          RingHom.ker (toTateLift hC (ψ.comp (Ideal.Quotient.mkₐ K I))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        rw [Ideal.mem_comap, RingHom.mem_ker, toTateLift_toTate, AlgHom.comp_apply,
          Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hf, map_zero]
      exact RingHom.mem_ker.mp (hle ht)

/-- `quotientToTateLift hC ψ` sends the class of `toTate f` in `T ⧸ I T` to `ψ(mk f)`. -/
@[simp]
theorem quotientToTateLift_mk {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) (f : W) :
    quotientToTateLift hC ψ (Ideal.Quotient.mk (I.map (toTate σ K)) (toTate σ K f)) =
      ψ (Ideal.Quotient.mk I f) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk K, ← AlgHom.comp_apply, quotientToTateLift,
    Ideal.Quotient.liftₐ_comp, toTateLift_toTate, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- `quotientToTateLift hC ψ` extends `ψ` along the canonical map `W ⧸ I → T ⧸ I T`. -/
@[simp]
theorem quotientToTateLift_quotientMap {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) (x : W ⧸ I) :
    quotientToTateLift hC ψ
      (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map x) = ψ x := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk, quotientToTateLift_mk]

/-- `quotientToTateLift hC ψ` restricts to `ψ` along `W ⧸ I → T ⧸ I T`. -/
@[simp]
theorem quotientToTateLift_comp_quotientMap {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) :
    (quotientToTateLift hC ψ).comp
      (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) = ψ :=
  AlgHom.ext (quotientToTateLift_quotientMap hC ψ)

/-- **Uniqueness of the Tate-quotient extension.** Any `K`-algebra homomorphism `T ⧸ I T → C` into
an affinoid algebra restricting to `ψ` on `W ⧸ I` equals `quotientToTateLift hC ψ`. -/
theorem quotientToTateLift_unique {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) {ψ : (W ⧸ I) →ₐ[K] C} {Φ : (T ⧸ I.map (toTate σ K)) →ₐ[K] C}
    (hΦ : Φ.comp (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) = ψ) :
    Φ = quotientToTateLift hC ψ := by
  have hcomp : Φ.comp (Ideal.Quotient.mkₐ K (I.map (toTate σ K))) =
      toTateLift hC (ψ.comp (Ideal.Quotient.mkₐ K I)) := by
    refine toTateLift_unique hC (AlgHom.ext fun f ↦ ?_)
    have hf := DFunLike.congr_fun hΦ (Ideal.Quotient.mk I f)
    simpa [Ideal.quotient_map_mkₐ] using hf
  ext x
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun hcomp t

/-- **Universal property of `W ⧸ I → T ⧸ I T` for affinoid targets.** Every `K`-algebra
homomorphism `W ⧸ I → C` into a `K`-affinoid algebra extends uniquely to `T ⧸ I T → C`. -/
theorem existsUnique_algHom_comp_quotientMap {I : Ideal W} {C : Type*} [CommRing C] [Algebra K C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) :
    ∃! Φ : (T ⧸ I.map (toTate σ K)) →ₐ[K] C,
      Φ.comp (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) = ψ :=
  ⟨quotientToTateLift hC ψ, quotientToTateLift_comp_quotientMap hC ψ,
    fun _ hΦ ↦ quotientToTateLift_unique hC hΦ⟩

/-- Extending the canonical map `W ⧸ I → T ⧸ I T` itself yields the identity on `T ⧸ I T`. -/
@[simp]
theorem quotientToTateLift_quotientMap_id {I : Ideal W} :
    quotientToTateLift
      ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient (I.map (toTate σ K)))
      (Ideal.quotientMapₐ (I.map (toTate σ K)) (toTate σ K) Ideal.le_comap_map) =
        AlgHom.id K (T ⧸ I.map (toTate σ K)) :=
  (quotientToTateLift_unique ((isAffinoidAlgebra_tate (K := K) (σ := σ)).quotient _)
    (AlgHom.id_comp _)).symm

/-- Naturality of `quotientToTateLift` with respect to algebra homomorphisms of affinoid targets. -/
theorem quotientToTateLift_comp {I : Ideal W} {C D : Type*} [CommRing C] [Algebra K C]
    [CommRing D] [Algebra K D] (hC : IsAffinoidAlgebra K C) (hD : IsAffinoidAlgebra K D)
    (θ : C →ₐ[K] D) (ψ : (W ⧸ I) →ₐ[K] C) :
    quotientToTateLift hD (θ.comp ψ) = θ.comp (quotientToTateLift hC ψ) :=
  (quotientToTateLift_unique hD
    (by rw [AlgHom.comp_assoc, quotientToTateLift_comp_quotientMap])).symm

/-- The Tate-quotient extension `quotientToTateLift hC ψ` is continuous for every complete
ultrametric algebra norm on the affinoid target `C`. -/
theorem continuous_quotientToTateLift {I : Ideal W} {C : Type*} [NormedCommRing C]
    [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C] (hC : IsAffinoidAlgebra K C)
    (ψ : (W ⧸ I) →ₐ[K] C) : Continuous (quotientToTateLift hC ψ) :=
  (I.map (toTate σ K)).isQuotientMap_mkQ.continuous_iff.mpr <| by
    have hcomp : (quotientToTateLift hC ψ) ∘ (I.map (toTate σ K)).mkQ =
        toTateLift hC (ψ.comp (Ideal.Quotient.mkₐ K I)) := by
      ext t
      exact Ideal.Quotient.liftₐ_apply _ _ _ _
    rw [hcomp]
    exact continuous_toTateLift hC _

/-- **Automatic continuity for quotients of `W` into affinoid algebras.** Every `K`-algebra
homomorphism `W ⧸ I → C` into a completely normed affinoid algebra is continuous for the residue
Gauss norm on `W ⧸ I`. -/
theorem continuous_quotient_algHom_of_isAffinoidAlgebra {I : Ideal W} {C : Type*}
    [NormedCommRing C] [NormedAlgebra K C] [IsUltrametricDist C] [CompleteSpace C]
    (hC : IsAffinoidAlgebra K C) (ψ : (W ⧸ I) →ₐ[K] C) : Continuous ψ := by
  rw [← quotientToTateLift_comp_quotientMap hC ψ]
  exact (continuous_quotientToTateLift hC ψ).comp I.isometry_quotientMap_toTate.continuous

/-- **Automatic continuity between Monsky–Washnitzer quotients.** Every `K`-algebra homomorphism
`W_σ ⧸ I → W_τ ⧸ J` between presentation quotients is continuous for their residue Gauss norms,
with no continuity hypothesis. -/
theorem continuous_quotient_algHom {τ : Type*} [Finite τ] {I : Ideal W}
    {J : Ideal (washnitzerAlgebra τ K)}
    (ψ : (W ⧸ I) →ₐ[K] (washnitzerAlgebra τ K ⧸ J)) : Continuous ψ :=
  J.isometry_quotientMap_toTate.comp_continuous_iff.mp <| by
    let C := IsRestricted.subring (R := K) (fun _ : τ ↦ (1 : ℝ)) ⧸ J.map (toTate τ K)
    have h := continuous_quotient_algHom_of_isAffinoidAlgebra (K := K) (C := C)
      ((isAffinoidAlgebra_tate (K := K) (σ := τ)).quotient (J.map (toTate τ K)))
      ((Ideal.quotientMapₐ (J.map (toTate τ K)) (toTate τ K) Ideal.le_comap_map).comp ψ)
    simpa only [AlgHom.coe_comp] using h

end Quotient

end TauCeti.Dagger.washnitzerAlgebra
