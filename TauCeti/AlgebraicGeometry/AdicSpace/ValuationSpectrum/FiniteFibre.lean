/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.AlgebraicGeometry.AdicSpace.ResidueField.Basic
import Mathlib.RingTheory.Artinian.Module
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.LinearIndependent

/-!
# Fibres of valuation spectra along finite ring maps

Let `A → B` be a ring map making `B` a finite `A`-module, and `v` a point of `Spv A` with support
`𝔭`. This file shows that only finitely many points of `Spv B` pull back to `v`, at most the
dimension of the fibre algebra `κ(𝔭) ⊗[A] B` over the residue field `κ(𝔭)`. When `B` is moreover
flat over `A`, that dimension is the rank of `B` at `𝔭`, so a finite locally free algebra of
rank `n` has at most `n` points of `Spv` over each point of `Spv A`. This is the fibre bound for
the adic spectrum of a finite étale algebra over a Huber pair.

## Method

The question is first moved to the fibre algebra `C = κ(𝔭) ⊗[A] B`, a finite-dimensional algebra
over the field `K = κ(𝔭)`: a point `w` of `Spv B` over `v` is the pullback of the valuation of its
residue field along the canonical map `C → κ(supp w)`, which is a point of `Spv C` over the point
of `K` given by `v`. Let `O ⊆ K` be the valuation subring of that point.

Over `C` the bound is a linear independence statement. Given distinct points `w₁, …, wₙ` of
`Spv C` over the same point of `K`, it suffices to find `e₁, …, eₙ ∈ C` such that each `eᵢ` is
strictly the largest of them for `wᵢ` (`Valuation.linearIndependent_of_map_lt`). The supports of
the `wᵢ` are maximal ideals of the artinian ring `C`, so an element in all of them but one picks
out a support. For points with a common support `Q`, the valuation subrings of the field `κ(Q)`
attached to them all lie over `O`, and `κ(Q)` is a finite extension of `K`; those subrings are
separated by `ValuationSubring.exists_valuation_eq_one_and_lt_one`, and the separating elements
lift along the surjection `C → κ(Q)`.

## Main results

* `TauCeti.ValuationSpectrum.finite_preimage_comap_singleton`: for a finite `A`-algebra `B`, only
  finitely many points of `Spv B` lie over a given point of `Spv A`.
* `TauCeti.ValuationSpectrum.ncard_preimage_comap_singleton_le`: their number is at most the
  dimension of the fibre algebra `κ(𝔭) ⊗[A] B`.
* `TauCeti.ValuationSpectrum.ncard_preimage_comap_singleton_le_finrank`: over a field `K`, the
  number of points of `Spv C` over a point of `Spv K` is at most `dim_K C`.
* `TauCeti.ValuationSpectrum.ncard_preimage_comap_singleton_le_rankAtStalk`: for `B` finite and
  flat, it is at most the rank of `B` at the support `𝔭`.

## References

* A. J. Engler and A. Prestel, *Valued Fields*, Springer Monographs in Mathematics, 2005, §3.2,
  for the bound on the number of extensions of a valuation to a finite field extension.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §2.4, for the description of a
  point of `Spv A` by its support and a valuation of the residue field.
-/

public section

namespace TauCeti

namespace ValuationSpectrum

section Field

variable {K C : Type*} [Field K] [CommRing C] [Algebra K C] [Module.Finite K C]

/-- Comparison of values at a point with support `Q`, read in the valuation subring of `κ(Q)`
through which the point factors. -/
private theorem valuation_le_iff_of_comap_eq {Q : Ideal C} [Q.IsPrime] {w : Spv C}
    {w' : Spv Q.ResidueField} (hw : comap (algebraMap C Q.ResidueField) w' = w) (x y : C) :
    w.valuation x ≤ w.valuation y ↔
      w'.valuation.valuationSubring.valuation (algebraMap C Q.ResidueField x) ≤
        w'.valuation.valuationSubring.valuation (algebraMap C Q.ResidueField y) := by
  rw [← hw, valuation_le_iff, comap_vle, ← valuation_le_iff]
  exact Valuation.isEquiv_valuation_valuationSubring _ _ _

/-- **Separating points with a common support.** For a finite set `s` of points of `Spv C` over a
point `vK` of `Spv K` and an ideal `Q`, there is a family `ε` such that, among the points of `s`
with support `Q`, each `ε w` is nonzero at `w` and strictly larger at `w` than every `ε w'`. -/
private theorem exists_valuation_ne_zero_and_lt (vK : Spv K) (s : Finset (Spv C))
    (hs : ∀ w ∈ s, comap (algebraMap K C) w = vK) (Q : Ideal C) :
    ∃ ε : Spv C → C, ∀ w ∈ s, w.supp = Q → w.valuation (ε w) ≠ 0 ∧
      ∀ w' ∈ s, w'.supp = Q → w' ≠ w → w'.valuation (ε w) < w'.valuation (ε w') := by
  classical
  by_cases hQ : ∃ w ∈ s, w.supp = Q
  swap
  · exact ⟨0, fun w hw hwQ ↦ (hQ ⟨w, hw, hwQ⟩).elim⟩
  obtain ⟨w₀, -, rfl⟩ := hQ
  have : IsArtinianRing C := IsArtinianRing.of_finite K C
  have : w₀.supp.IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  -- `κ(Q)` is a quotient of `C`, hence a finite extension of `K`
  have hsurj := Ideal.algebraMap_residueField_surjective w₀.supp
  have : Module.Finite K w₀.supp.ResidueField :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom K C w₀.supp.ResidueField).toLinearMap hsurj
  -- each point with support `Q` comes from a point of `Spv κ(Q)`
  have : Nonempty (Spv w₀.supp.ResidueField) := ⟨ofValuation (residueFieldValuation w₀)⟩
  set g := comap (algebraMap C w₀.supp.ResidueField) with hg
  have hlift (w : Spv C) (hw : w.supp = w₀.supp) : g (Function.invFun g w) = w :=
    Function.invFun_eq ((mem_range_comap_algebraMap_residueField_iff _ w).mpr hw)
  set ρ : Spv C → ValuationSubring w₀.supp.ResidueField :=
    fun w ↦ (Function.invFun g w).valuation.valuationSubring
  -- their valuation subrings lie over the valuation subring of `vK`
  have hρ (w : Spv C) (hw : w ∈ s) (hwQ : w.supp = w₀.supp) :
      (ρ w).comap (algebraMap K w₀.supp.ResidueField) = vK.valuation.valuationSubring := by
    rw [← valuationSubring_valuation_comap, IsScalarTower.algebraMap_eq K C, ← comap_comap, ← hg,
      hlift w hwQ, hs w hw]
  have hρinj {w w' : Spv C} (hwQ : w.supp = w₀.supp) (hw'Q : w'.supp = w₀.supp)
      (h : ρ w = ρ w') : w = w' := by
    rw [← hlift w hwQ, ← hlift w' hw'Q,
      ← ofValuation_valuationSubring_valuation (Function.invFun g w),
      ← ofValuation_valuationSubring_valuation (Function.invFun g w')]
    exact congrArg (fun V ↦ g (ofValuation (ValuationSubring.valuation V))) h
  set S := (s.filter (·.supp = w₀.supp)).image ρ
  have hmem {w : Spv C} (hw : w ∈ s) (hwQ : w.supp = w₀.supp) : ρ w ∈ S :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hw, hwQ⟩)
  obtain ⟨e, he⟩ := ValuationSubring.exists_valuation_eq_one_and_lt_one
    vK.valuation.valuationSubring S fun A hA ↦ by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hA
      exact hρ w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  -- lift the separating elements of `κ(Q)` to `C`
  refine ⟨fun w ↦ Function.surjInv hsurj (e (ρ w)), fun w hw hwQ ↦ ⟨?_, fun w' hw' hw'Q hne ↦ ?_⟩⟩
  · rw [ne_eq, ← le_zero_iff, ← map_zero w.valuation,
      valuation_le_iff_of_comap_eq (hlift w hwQ), Function.surjInv_eq hsurj, map_zero,
      map_zero, (he _ (hmem hw hwQ)).1]
    exact not_le.mpr zero_lt_one
  · rw [← not_le, valuation_le_iff_of_comap_eq (hlift w' hw'Q), Function.surjInv_eq hsurj,
      Function.surjInv_eq hsurj, (he _ (hmem hw' hw'Q)).1, not_le]
    exact (he _ (hmem hw hwQ)).2 _ (hmem hw' hw'Q) fun h ↦ hne (hρinj hw'Q hwQ h)

/-- **The fibre bound over a field.** Points of `Spv C` over a common point of `Spv K` number at
most the dimension of `C` over `K`. -/
private theorem card_le_finrank (vK : Spv K) (s : Finset (Spv C))
    (hs : ∀ w ∈ s, comap (algebraMap K C) w = vK) : s.card ≤ Module.finrank K C := by
  classical
  have : IsArtinianRing C := IsArtinianRing.of_finite K C
  -- an element in every support but one picks out that support
  have hδ (Q : Ideal C) : ∃ δ : C, ∀ w ∈ s, w.supp = Q →
      δ ∉ Q ∧ ∀ w' ∈ s, w'.supp ≠ Q → δ ∈ w'.supp := by
    by_cases hQ : ∃ w ∈ s, w.supp = Q
    swap
    · exact ⟨0, fun w hw hwQ ↦ (hQ ⟨w, hw, hwQ⟩).elim⟩
    obtain ⟨w₀, -, rfl⟩ := hQ
    set T := (s.image supp).erase w₀.supp
    have hT : ¬ T.inf id ≤ w₀.supp := by
      rw [Ideal.IsPrime.inf_le' inferInstance]
      rintro ⟨Q', hQ', hle⟩
      obtain ⟨hne, hQ's⟩ := Finset.mem_erase.mp hQ'
      obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp hQ's
      exact hne ((IsArtinianRing.isMaximal_of_isPrime w'.supp).eq_of_le
        Ideal.IsPrime.ne_top' hle)
    obtain ⟨δ, hδT, hδ⟩ := IsConcreteLE.not_le_iff_exists.mp hT
    refine ⟨δ, fun w _ _ ↦ ⟨hδ, fun w' hw' hne ↦ ?_⟩⟩
    exact Finset.inf_le (f := id) (Finset.mem_erase.mpr ⟨hne, Finset.mem_image_of_mem _ hw'⟩) hδT
  choose δ hδ using hδ
  choose ε hε using exists_valuation_ne_zero_and_lt vK s hs
  have hδ0 {w : Spv C} (hw : w ∈ s) : w.valuation (δ w.supp) ≠ 0 := by
    rw [ne_eq, ← Valuation.mem_supp_iff, ← supp_eq_valuation_supp]
    exact (hδ w.supp w hw rfl).1
  have hli : LinearIndependent K fun w : s ↦ δ w.1.supp * ε w.1.supp w.1 := by
    refine Valuation.linearIndependent_of_map_lt (O := vK.valuation.valuationSubring)
      (fun w : s ↦ w.1.valuation) (fun w a ha ↦ ?_) (fun w ↦ ?_) fun w w' hne ↦ ?_
    · -- the points of `s` are at most `1` on the valuation subring of `vK`
      rw [← map_one w.1.valuation, ← map_one (algebraMap K C), valuation_le_iff, ← comap_vle,
        hs w.1 w.2, ← valuation_le_iff, map_one]
      exact ha
    · rw [map_mul]
      exact mul_ne_zero (hδ0 w.2) (hε _ w.1 w.2 rfl).1
    · -- `w'` is the element, `w` the valuation
      rw [map_mul, map_mul]
      by_cases hsupp : w'.1.supp = w.1.supp
      · rw [hsupp, mul_lt_mul_iff_right₀ (pos_iff_ne_zero.mpr (hδ0 w.2))]
        exact (hε _ w'.1 w'.2 hsupp).2 w.1 w.2 rfl fun h ↦ hne (Subtype.ext h).symm
      · have : w.1.valuation (δ w'.1.supp) = 0 := by
          rw [← Valuation.mem_supp_iff, ← supp_eq_valuation_supp]
          exact (hδ w'.1.supp w'.1 w'.2 rfl).2 w.1 w.2 (Ne.symm hsupp)
        rw [this, zero_mul, pos_iff_ne_zero]
        exact mul_ne_zero (hδ0 w.2) (hε _ w.1 w.2 rfl).1
  simpa using hli.fintype_card_le_finrank

/-- **The fibre bound over a field.** For a finite `K`-algebra `C`, the number of points of `Spv C`
over a point of `Spv K` is at most the dimension of `C` over `K`. (These points form a finite set
by `finite_preimage_comap_singleton`.) -/
theorem ncard_preimage_comap_singleton_le_finrank (vK : Spv K) :
    (comap (algebraMap K C) ⁻¹' {vK}).ncard ≤ Module.finrank K C := by
  by_cases hfin : (comap (algebraMap K C) ⁻¹' {vK}).Finite
  · rw [Set.ncard_eq_toFinset_card _ hfin]
    exact card_le_finrank vK _ fun w hw ↦ by simpa using hw
  · simp [Set.Infinite.ncard hfin]

end Field

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- A point `w` of `Spv B` over `v ∈ Spv A` comes from a point of the fibre algebra
`κ(supp v) ⊗[A] B` over the point of `κ(supp v)` given by `v`. -/
private theorem exists_comap_includeRight_eq (v : Spv A) {w : Spv B}
    (hw : comap (algebraMap A B) w = v) :
    ∃ W : Spv (v.supp.Fiber B),
      comap Algebra.TensorProduct.includeRight.toRingHom W = w ∧
        comap (algebraMap v.supp.ResidueField (v.supp.Fiber B)) W =
          ofValuation (residueFieldValuation v) := by
  have hq : v.supp = w.supp.comap (Algebra.ofId A B).toRingHom := by
    rw [← hw, supp_comap, AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId]
  set f := Ideal.ResidueField.mapₐ v.supp w.supp (Algebra.ofId A B) hq
  set φ := Algebra.TensorProduct.lift f (IsScalarTower.toAlgHom A B w.supp.ResidueField)
    fun _ _ ↦ .all _ _
  set w' := ofValuation (residueFieldValuation w)
  have hw' : comap (algebraMap B w.supp.ResidueField) w' = w :=
    comap_algebraMap_residueField_ofValuation w
  have hφB : φ.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      algebraMap B w.supp.ResidueField := by
    ext b
    simp [φ]
  have hφA : φ.toRingHom.comp ((algebraMap v.supp.ResidueField (v.supp.Fiber B)).comp
      (algebraMap A v.supp.ResidueField)) = (algebraMap B w.supp.ResidueField).comp
        (algebraMap A B) := by
    ext a
    simp [φ, f, Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply A B w.supp.ResidueField]
  refine ⟨comap φ.toRingHom w', ?_, ?_⟩
  · rw [comap_comap, hφB, hw']
  · -- both sides pull back to `v` along `A → κ(supp v)`
    refine comap_algebraMap_residueField_injective v.supp ?_
    rw [comap_comap, comap_comap, hφA, ← comap_comap, hw', hw,
      comap_algebraMap_residueField_ofValuation]

variable [Module.Finite A B]

/-- Any finite set of points of `Spv B` over `v` has at most `dim κ(𝔭) ⊗[A] B` elements. -/
private theorem card_le_finrank_fiber (v : Spv A) (s : Finset (Spv B))
    (hs : ∀ w ∈ s, comap (algebraMap A B) w = v) :
    s.card ≤ Module.finrank v.supp.ResidueField (v.supp.Fiber B) := by
  classical
  choose W hW using fun w (hw : w ∈ s) ↦ exists_comap_includeRight_eq v (hs w hw)
  have hinj : Function.Injective fun w : s ↦ W w.1 w.2 := fun w w' h ↦
    Subtype.ext (by rw [← (hW w.1 w.2).1, ← (hW w'.1 w'.2).1]; exact congrArg _ h)
  rw [← Finset.card_attach, ← Finset.card_image_of_injective _ hinj]
  refine card_le_finrank (ofValuation (residueFieldValuation v)) _ fun W' hW' ↦ ?_
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hW'
  exact (hW w.1 w.2).2

/-- **The fibres of `Spv B → Spv A` are finite** for a finite `A`-algebra `B`. -/
theorem finite_preimage_comap_singleton (v : Spv A) :
    (comap (algebraMap A B) ⁻¹' {v}).Finite := by
  by_contra h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h
    (Module.finrank v.supp.ResidueField (v.supp.Fiber B) + 1)
  have := card_le_finrank_fiber v s fun w hw ↦ hs hw
  omega

/-- **The fibre bound for valuation spectra.** For a finite `A`-algebra `B`, the number of points
of `Spv B` over a point `v` of `Spv A` with support `𝔭` is at most the dimension of the fibre
algebra `κ(𝔭) ⊗[A] B` over `κ(𝔭)`. -/
theorem ncard_preimage_comap_singleton_le (v : Spv A) :
    (comap (algebraMap A B) ⁻¹' {v}).ncard ≤
      Module.finrank v.supp.ResidueField (v.supp.Fiber B) := by
  have hfin := finite_preimage_comap_singleton (B := B) v
  rw [Set.ncard_eq_toFinset_card _ hfin]
  exact card_le_finrank_fiber v _ fun w hw ↦ by simpa using hw

/-- **The fibre bound for a finite flat algebra.** For a finite flat `A`-algebra `B`, the number of
points of `Spv B` over a point `v` of `Spv A` is at most the rank of `B` at the support of `v`. -/
theorem ncard_preimage_comap_singleton_le_rankAtStalk [Module.Flat A B] (v : Spv A) :
    (comap (algebraMap A B) ⁻¹' {v}).ncard ≤ Module.rankAtStalk (R := A) B (suppFun v) := by
  have hv : suppFun v = ⟨v.supp, inferInstance⟩ := PrimeSpectrum.ext (suppFun_asIdeal v)
  rw [hv, ← Ideal.finrank_fiber_eq_rankAtStalk]
  exact ncard_preimage_comap_singleton_le v

end Fibre

end ValuationSpectrum

end TauCeti
