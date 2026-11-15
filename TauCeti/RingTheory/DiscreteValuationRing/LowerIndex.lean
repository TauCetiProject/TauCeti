/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
public import TauCeti.RingTheory.Invariant.Basic
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
public import TauCeti.RingTheory.Valuation.AddValuation
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import TauCeti.RingTheory.IsGaloisGroup.Dedekind

/-!
# The lower index of a quotient, over discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B` by `A`-algebra
automorphisms, with invariants the discrete valuation ring `A`, and let `H` be a normal subgroup.
Mathlib makes `G ⧸ H` act on the fixed ring `B^H = FixedPoints.subalgebra A B H`, with invariants
`A`; this is the integer ring of the fixed field `L^H` of a finite Galois extension `L/K`, with
`Gal(L^H/K) = G ⧸ H`. This file shows that `B^H` is again a discrete valuation ring, and proves
Serre's formula comparing Serre's lower index `i_G(σ) = min_x v_B(σ x - x)`
(`TauCeti.IsLocalRing.lowerIndex`) on `B` and on `B^H`: when the residue extension of `B` over
`A` is separable,

`e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`,

where `e` is the ramification index of `B` over `B^H`. Neither completeness of `A` nor finiteness
of its residue field is assumed. Separability enters only through generators: `B` and `B^H` are
then generated over `A` by single elements `x` and `y`, at which the lower indices are read, and
`σ y - y` is associated in `B` with `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` for the characteristic
polynomial `f` of `x` under `H`. Without separability the formula fails.

The formula is the input to Herbrand's theorem on the compatibility of the lower numbering with
quotients. The counting form records Serre's lemma: if `σ` has the largest lower index `j` in its
coset `σ H`, then `i_G(σ τ) = min (i_H(τ), j)` for `τ ∈ H`, and so
`e · i_{G/H}(σ H) = ∑_{k < j} #H_k`. The nonarchimedean local field case is
`TauCeti.LocalFieldsRamification.ramificationIndex_mul_lowerIndex_restrictNormal_eq_sum`.

## Main results

* `TauCeti.FixedPoints.isDiscreteValuationRing_subalgebra`: the invariants `B^H` of any subgroup
  form a discrete valuation ring.
* `TauCeti.FixedPoints.exists_adjoin_eq_top`: for separable residue extension, `B^H` is generated
  over `A` by a single element.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_finsum`: **Serre's quotient formula**
  `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`.
* `TauCeti.IsLocalRing.ramificationIdx_mul_lowerIndex_mk_eq_sum_card`: its counting form
  `e · i_{G/H}(σ H) = ∑_{k < j} #H_k` for `σ` of largest lower index `j` in `σ H`, and
  `TauCeti.IsLocalRing.lowerIndex_mk_ne_top`: the class of every `σ ∉ H` has finite lower index.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3, and §3, Lemma 5.
-/

public section

open IsLocalRing

namespace TauCeti

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

namespace FixedPoints

/-- The invariants `B^H` of a subgroup `H` are again a discrete valuation ring. They form a
valuation ring, since a quotient in `B` of two `H`-invariants is `H`-invariant, and they are
Noetherian, as an `A`-submodule of the finite `A`-module `B`. -/
instance isDiscreteValuationRing_subalgebra (H : Subgroup G) :
    IsDiscreteValuationRing (FixedPoints.subalgebra A B H) := by
  have : IsLocalRing (FixedPoints.subalgebra A B H) :=
    (algebraMap (FixedPoints.subalgebra A B H) B).domain_isLocalRing
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  have : IsNoetherianRing (FixedPoints.subalgebra A B H) := by
    have : IsNoetherian A (FixedPoints.subalgebra A B H) :=
      isNoetherian_of_injective (Subalgebra.val _).toLinearMap Subtype.val_injective
    exact isNoetherian_of_tower A this
  have := Algebra.IsInvariant.isIntegral (FixedPoints.subalgebra A B H) B H
  have hnf : ¬ IsField (FixedPoints.subalgebra A B H) := fun h ↦
    IsDiscreteValuationRing.not_isField B (isField_of_isIntegral_of_isField' h)
  -- Divisibility between invariants in `B` holds in `B^H`, since `B` is a domain.
  have hdvd : ∀ a b : FixedPoints.subalgebra A B H, (a : B) ∣ b → a ∣ b := by
    rintro a b ⟨c, hc⟩
    rcases eq_or_ne (a : B) 0 with ha | ha
    · rw [ha, zero_mul, ZeroMemClass.coe_eq_zero] at hc
      exact hc ▸ dvd_zero a
    refine ⟨⟨c, fun τ ↦ mul_left_cancel₀ ha ?_⟩, Subtype.ext hc⟩
    rw [← hc, ← b.2 τ, hc, smul_mul', a.2 τ]
  refine ((IsDiscreteValuationRing.TFAE _ hnf).out 1 2).2 <|
    ValuationRing.iff_dvd_total.2 ⟨fun a b ↦ ?_⟩
  exact (ValuationRing.dvd_total (a : B) b).imp (hdvd a b) (hdvd b a)

variable [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

variable (A B) in
/-- For separable residue extension of `B` over `A`, the invariants `B^H` of a subgroup are
generated over `A` by a single element: `B^H` is finite over `A`, and its residue extension over
`A` is separable, as a subextension of that of `B`. -/
theorem exists_adjoin_eq_top (H : Subgroup G) :
    ∃ y : FixedPoints.subalgebra A B H, Algebra.adjoin A {y} = ⊤ := by
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  have : Module.Finite A (FixedPoints.subalgebra A B H) :=
    Module.Finite.of_injective (Subalgebra.val _).toLinearMap Subtype.val_injective
  have : IsLocalHom (algebraMap A (FixedPoints.subalgebra A B H)) := by
    have : IsLocalHom ((algebraMap (FixedPoints.subalgebra A B H) B).comp
        (algebraMap A (FixedPoints.subalgebra A B H))) := by
      rw [← IsScalarTower.algebraMap_eq]
      infer_instance
    exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B H) B)
  have : IsLocalHom (IsScalarTower.toAlgHom A (FixedPoints.subalgebra A B H) B) :=
    ⟨fun c hc ↦ (isUnit_map_iff (algebraMap (FixedPoints.subalgebra A B H) B) c).1 hc⟩
  have : Algebra.IsSeparable (ResidueField A) (ResidueField (FixedPoints.subalgebra A B H)) :=
    Algebra.IsSeparable.of_algHom _ (ResidueField B)
      (ResidueField.mapAlgHom' (IsScalarTower.toAlgHom A (FixedPoints.subalgebra A B H) B))
  exact IsDiscreteValuationRing.exists_adjoin_eq_top

end FixedPoints

namespace IsLocalRing

variable [IsLocalHom (algebraMap A B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  (H : Subgroup G) [H.Normal]

variable (A B) in
/-- **Serre's quotient formula for the lower index.** Let `G` act faithfully on the discrete
valuation ring `B` with invariants `A` and separable residue extension, and let `H` be a normal
subgroup. Then for every `σ : G`, `e · i_{G/H}(σ H) = ∑_{τ ∈ H} i_G(σ τ)`, where `e` is the
ramification index of `B` over the invariants `B^H` and `i_{G/H}` is the lower index of the action
of `G ⧸ H` on `B^H`. Both sides are `⊤` for `σ ∈ H`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_finsum (σ : G) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ᶠ τ : H, lowerIndex B (σ * τ) := by
  have := Fintype.ofFinite H
  have : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := B)
  obtain ⟨y, hy⟩ := FixedPoints.exists_adjoin_eq_top A B H
  have hinj : Function.Injective fun τ : H ↦ τ • x :=
    (smul_left_injective_of_adjoin_singleton_eq_top (G := G) hx).comp Subtype.val_injective
  -- `σ y - y` and `(σ f)(x) = ∏_{τ ∈ H} (x - σ τ x)` divide each other in `B`, for `f` the
  -- characteristic polynomial of `x` under `H`: the `H`-invariants are the elements of `B^H`,
  -- generated over `A` by `y`.
  have key : _root_.IsDiscreteValuationRing.addVal B (σ • (y : B) - y) =
      _root_.IsDiscreteValuationRing.addVal B
        ((σ • MulSemiringAction.charpoly H x).eval x) := by
    refine (_root_.IsDiscreteValuationRing.addVal_eq_iff_associated _ _).2 <|
      associated_of_dvd_dvd (MulSemiringAction.dvd_eval_smul_charpoly (fun c hc ↦ ?_) x)
      (dvd_sub_comm.1 (MulSemiringAction.eval_smul_charpoly_dvd_sub_smul hx hinj
        (fun τ ↦ y.2 τ) σ))
    simpa using map_dvd (algebraMap (FixedPoints.subalgebra A B H) B)
      (smul_sub_dvd_smul_sub_of_adjoin_singleton_eq_top hy (σ : G ⧸ H) ⟨c, hc⟩)
  rw [finsum_eq_sum_of_fintype, lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hy,
    ← nsmul_eq_mul, ← IsDiscreteValuationRing.addVal_algebraMap, map_sub]
  simp_rw [lowerIndex_eq_addVal_of_adjoin_singleton_eq_top hx, AddValuation.map_sub_swap _ _ x,
    ← AddValuation.map_prod, mul_smul]
  rw [MulSemiringAction.eval_smul_charpoly] at key
  simpa only [Subalgebra.algebraMap_apply, FixedPoints.coe_mk_smul, Subgroup.smul_def] using key

variable (A) in
/-- **Serre's lemma on the lower index of a quotient**, in counting form. If `σ` has the largest
lower index in its coset `σ H`, and `i_G(σ) = j` is finite, then
`e · i_{G/H}(σ H) = ∑_{k < j} #H_k`, where `H_k` are the ramification groups of `H` acting on `B`
and `e` is the ramification index of `B` over `B^H`. -/
theorem ramificationIdx_mul_lowerIndex_mk_eq_sum_card {σ : G} {j : ℕ}
    (hj : lowerIndex B σ = j) (hσ : ∀ τ ∈ H, lowerIndex B (σ * τ) ≤ lowerIndex B σ) :
    ((maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B H) : ℕ∞) *
        lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) =
      ∑ k ∈ Finset.range j, (Nat.card (ramificationGroup H B k) : ℕ∞) := by
  have := Fintype.ofFinite H
  rw [ramificationIdx_mul_lowerIndex_mk_eq_finsum A B, finsum_eq_sum_of_fintype,
    ← sum_min_lowerIndex_natCast (G := H) (S := B) j]
  refine Finset.sum_congr rfl fun τ _ ↦ ?_
  rw [lowerIndex_mul_eq_min_of_le (hσ τ τ.2), lowerIndex_coe, hj]

variable (A) in
/-- The class in `G ⧸ H` of every `σ ∉ H` has finite lower index on `B^H`. Choosing `σ τ₀` of
largest lower index in the coset `σ H`, this is the counting form, as `i_G(σ τ₀)` is finite. -/
theorem lowerIndex_mk_ne_top {σ : G} (hσ : σ ∉ H) :
    lowerIndex (FixedPoints.subalgebra A B H) (σ : G ⧸ H) ≠ ⊤ := by
  obtain ⟨τ₀, hτ₀H, hτ₀⟩ := exists_mem_forall_lowerIndex_mul_le (S := B) H σ
  have hne : lowerIndex B (σ * τ₀) ≠ ⊤ := by
    rw [Ne, lowerIndex_eq_top_iff, mul_eq_one_iff_eq_inv]
    rintro rfl
    exact hσ (H.inv_mem hτ₀H)
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 hne
  intro htop
  have he := Ideal.ramificationIdx_pos_of_isDedekindDomain'
    (p := maximalIdeal (FixedPoints.subalgebra A B H)) (maximalIdeal B)
    (_root_.IsDiscreteValuationRing.not_a_field _)
  have hsum := ramificationIdx_mul_lowerIndex_mk_eq_sum_card A H hj.symm hτ₀
  rw [QuotientGroup.mk_mul_of_mem σ hτ₀H, htop, ENat.mul_top (by exact_mod_cast he.ne'),
    ← Nat.cast_sum] at hsum
  exact ENat.natCast_ne_top _ hsum.symm

end IsLocalRing

end TauCeti
