/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Distinguished
public import TauCeti.RingTheory.PowerSeries.Weierstrass.Quotient
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The Nullstellensatz for Tate algebras

Let `K` be a complete nonarchimedean field and `Tₙ = K⟨X₁, …, Xₙ⟩` the Tate algebra of restricted
power series in finitely many variables. This file proves that for every maximal ideal `m` of `Tₙ`
the residue field `Tₙ ⧸ m` is a finite extension of `K`, and so is the residue field of every
maximal ideal of a quotient of `Tₙ`. When `K` is algebraically closed these residue fields are
therefore `K` itself. This is the input that makes a maximal ideal of an affinoid algebra a point
of its adic spectrum, by extending the norm of `K` to the finite extension.

The proof is the Noether normalisation argument of Bosch–Güntzer–Remmert, by induction on the
number of variables. A maximal ideal `m` of `K⟨X, Y⟩` contains a nonzero series `f`, since the
variable `Y` is not a unit. An automorphism of `K⟨X, Y⟩` makes `f` distinguished in `Y` with a
unit dominant coefficient (`TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished_isUnit`), and
Weierstrass division then makes `K⟨X⟩⟨Y⟩ ⧸ (f)` a finite module over `K⟨X⟩`
(`TauCeti.PowerSeries.IsDistinguished.finite_quotient`). So the residue field of `m` is finite
over `K⟨X⟩`, and integral over the quotient of `K⟨X⟩` by the contraction of `m`. That quotient is
therefore a field, finite over `K` by induction.

## Main results

* `TauCeti.MvPowerSeries.finite_quotient_of_isMaximal`: the residue field of a maximal ideal of
  `K⟨X₁, …, Xₙ⟩` is finite over `K`.
* `TauCeti.MvPowerSeries.finite_quotient_of_surjective`: the same for every quotient of
  `K⟨X₁, …, Xₙ⟩`, which is Wedhorn's Proposition 5.61.
* `TauCeti.MvPowerSeries.bijective_algebraMap_quotient_of_surjective`: over an algebraically
  closed `K` these residue fields are `K`.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.2,
  Corollary 3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 5.61.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- A maximal ideal of the Tate algebra with at least one variable contains a nonzero series:
the variable `X none` is not a unit, since its constant coefficient is zero. -/
private theorem exists_mem_ne_zero_of_isMaximal {σ : Type*} (m : Ideal (Tate (Option σ)))
    [hm : m.IsMaximal] : ∃ f ∈ m, f ≠ 0 := by
  let x : Tate (Option σ) := ⟨X none, isRestricted_monomial _ (Finsupp.single none 1) 1⟩
  have hx : ¬ IsUnit x := fun h ↦ by
    simpa [x] using h.map ((constantCoeff (σ := Option σ) (R := K)).comp
      (IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)).subtype)
  by_cases hxm : x ∈ m
  · refine ⟨x, hxm, fun h ↦ ?_⟩
    simpa [x] using congrArg (fun g : Tate (Option σ) ↦
      coeff (Finsupp.single none 1) (g : MvPowerSeries (Option σ) K)) h
  · obtain ⟨y, i, him, hyi⟩ := hm.exists_inv hxm
    exact ⟨i, him, fun h ↦ hx (.of_mul_eq_one_right y (by rwa [h, add_zero] at hyi))⟩

variable [CompleteSpace K]

/-- The inductive step: if every residue field of `K⟨X⟩` is finite over `K`, so is every residue
field of `K⟨X, Y⟩`. -/
private theorem finite_quotient_option {σ : Type*} [Finite σ]
    (ih : ∀ m : Ideal (Tate σ), m.IsMaximal → Module.Finite K (Tate σ ⧸ m))
    (m : Ideal (Tate (Option σ))) [m.IsMaximal] : Module.Finite K (Tate (Option σ) ⧸ m) := by
  obtain ⟨f, hfm, hf⟩ := exists_mem_ne_zero_of_isMaximal m
  obtain ⟨e, s, hd, hu⟩ := exists_algEquiv_isDistinguished_isUnit f hf
  -- Separate the variable `Y = X none`: `K⟨X, Y⟩ ≅ S = K⟨X⟩⟨Y⟩`, as `K`-algebras.
  let R := Tate σ
  let S := PowerSeries.IsRestricted.subring (R := R) 1
  let _ : Algebra K S := ((algebraMap R S).comp (algebraMap K R)).toAlgebra
  have : IsScalarTower K R S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Φ : Tate (Option σ) ≃ₐ[K] S :=
    e.trans (AlgEquiv.ofRingEquiv (f := Huber.restrictedOptionEquiv)
      Huber.restrictedOptionEquiv_algebraMap)
  let m' := m.map (Φ : Tate (Option σ) →+* S)
  have : m'.IsMaximal := Ideal.map_isMaximal_of_equiv (Φ : Tate (Option σ) ≃+* S)
  -- `S ⧸ m'` is a quotient of `S ⧸ (Φ f)`, which is finite over `R` by Weierstrass division.
  have := hd.finite_quotient zero_lt_one hu
  have hle : Ideal.span {Huber.restrictedOptionEquiv (e f)} ≤ m' :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (Ideal.mem_map_of_mem _ hfm))
  have : Module.Finite R (S ⧸ m') :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  -- The contraction `p` of `m'` to `R` is maximal, since `S ⧸ m'` is a field integral over
  -- `R ⧸ p`, and `R ⧸ p` is finite over `K` by induction.
  let p := m'.under R
  -- Mathlib's `Ideal.Quotient.isScalarTower_of_liesOver` concerns the `R ⧸ p`-algebra structure
  -- `Ideal.Quotient.algebraOfLiesOver`, but the one found here is `Ideal.quotientAlgebra`, so
  -- instance search fails; both maps `R → S ⧸ m'` reduce to the quotient of `algebraMap R S`.
  have : IsScalarTower R (R ⧸ p) (S ⧸ m') :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := R ⧸ p) (A := S ⧸ m') fun _ ↦ rfl
  have : Module.Finite (R ⧸ p) (S ⧸ m') := Module.Finite.of_restrictScalars_finite R _ _
  have : Algebra.IsIntegral (R ⧸ p) (S ⧸ m') := Algebra.IsIntegral.of_finite _ _
  have : p.IsMaximal := Ideal.Quotient.maximal_of_isField _ <|
    isField_of_isIntegral_of_isField Ideal.algebraMap_quotient_injective
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m').mp ‹_›)
  have := ih p ‹_›
  have : Module.Finite K (S ⧸ m') := Module.Finite.trans (R ⧸ p) _
  exact Module.Finite.equiv (Ideal.quotientEquivAlg m m' Φ rfl).symm.toLinearEquiv

/-- **The Nullstellensatz for Tate algebras** (Bosch–Güntzer–Remmert, §6.1.2, Corollary 3).
Over a complete nonarchimedean field `K`, the residue field `K⟨X₁, …, Xₙ⟩ ⧸ m` of every maximal
ideal of the Tate algebra in finitely many variables is a finite extension of `K`. -/
theorem finite_quotient_of_isMaximal {σ : Type*} [Finite σ] (m : Ideal (Tate σ)) [m.IsMaximal] :
    Module.Finite K (Tate σ ⧸ m) := by
  revert m
  refine Finite.induction_empty_option
    (P := fun σ ↦ ∀ m : Ideal (Tate σ), m.IsMaximal → Module.Finite K (Tate σ ⧸ m))
    (fun {α β} e h m hm ↦ ?_) (fun m _ ↦ ?_) (fun ih m _ ↦ finite_quotient_option ih m) σ
  · -- Renaming the variables along `e : α ≃ β` is a `K`-algebra isomorphism of Tate algebras.
    let r : Tate α ≃ₐ[K] Tate β := IsRestricted.renameAlgEquiv e fun _ ↦ 1
    have : (m.comap r).IsMaximal := Ideal.comap_isMaximal_of_surjective _ r.surjective
    have := h (m.comap r) this
    have hm : m = (m.comap r).map r := (Ideal.map_comap_of_surjective _ r.surjective m).symm
    exact Module.Finite.equiv (Ideal.quotientEquivAlg (m.comap r) m r hm).toLinearEquiv
  · -- Without variables every series is a constant, so the Tate algebra is `K`.
    have := Module.Finite.of_surjective (Algebra.linearMap K (Tate PEmpty))
      algebraMap_isRestrictedSubring_surjective
    exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective K m)

/-- **Residue fields of quotients of Tate algebras.** If a `K`-algebra `B` is a quotient of the
Tate algebra `K⟨X₁, …, Xₙ⟩` over a complete nonarchimedean field `K`, then the residue field
`B ⧸ m` of every maximal ideal of `B` is a finite extension of `K`. -/
theorem finite_quotient_of_surjective {B : Type*} [CommRing B] [Algebra K B] {σ : Type*}
    [Finite σ] {φ : Tate σ →ₐ[K] B} (hφ : Function.Surjective φ) (m : Ideal B) [m.IsMaximal] :
    Module.Finite K (B ⧸ m) := by
  have : (m.comap φ).IsMaximal := Ideal.comap_isMaximal_of_surjective φ hφ
  have := finite_quotient_of_isMaximal (m.comap φ)
  exact Module.Finite.of_surjective (Ideal.quotientMapₐ m φ le_rfl).toLinearMap
    (Ideal.quotientMap_surjective (H := le_rfl) hφ)

/-- **Residue fields over an algebraically closed field.** If `K` is an algebraically closed
complete nonarchimedean field and the `K`-algebra `B` is a quotient of the Tate algebra
`K⟨X₁, …, Xₙ⟩`, then the residue field of every maximal ideal `m` of `B` is `K`: the structure
map `K → B ⧸ m` is bijective. -/
theorem bijective_algebraMap_quotient_of_surjective [IsAlgClosed K] {B : Type*} [CommRing B]
    [Algebra K B] {σ : Type*} [Finite σ] {φ : Tate σ →ₐ[K] B} (hφ : Function.Surjective φ)
    (m : Ideal B) [m.IsMaximal] : Function.Bijective (algebraMap K (B ⧸ m)) := by
  have := finite_quotient_of_surjective hφ m
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end TauCeti.MvPowerSeries
