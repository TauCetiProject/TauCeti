/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import TauCeti.Algebra.Lie.Derivation.JordanChevalley

/-!
# Abstract Jordan decomposition in Killing Lie algebras

Let `L` be a finite-dimensional Lie algebra with nondegenerate Killing form over a field `K`.
Every element `x : L` whose adjoint action `ad x` is split (its generalized eigenspaces span `L`,
which is automatic when `K` is algebraically closed) decomposes as `x = n + s` with
`⁅n, s⁆ = 0`, `ad n` nilpotent and `ad s` semisimple. When `K` is perfect these parts are
unique. This is the abstract (or internal) Jordan decomposition: the
Jordan–Chevalley decomposition of the endomorphism `ad x` does not a priori have its parts
in the image of `ad`, and the decomposition here reconstructs them inside `L`.

The proof applies the Jordan–Chevalley decomposition of derivations
(`LieDerivation.exists_isNilpotent_isSemisimple_of_iSup_maxGenEigenspace_eq_top`) to the inner
derivation `ad x`: both parts are derivations, hence inner because every derivation of a Killing
Lie algebra is inner (`LieDerivation.IsKilling.exists_eq_ad`), and `ad` is injective because the
center is trivial. Uniqueness is the uniqueness of the Jordan–Chevalley decomposition of `ad x`
together with injectivity of `ad`; it only needs `L` to act faithfully on itself and `K` to be
perfect.

## Main results

* `TauCeti.exists_isNilpotent_ad_isSemisimple_ad_of_iSup_maxGenEigenspace_eq_top`: existence of
  the decomposition for an element whose adjoint action is split.
* `TauCeti.exists_isNilpotent_ad_isSemisimple_ad`: existence over an algebraically closed field.
* `TauCeti.isNilpotent_ad_isSemisimple_ad_unique`: uniqueness, for a finite-dimensional Lie
  algebra with trivial center over a perfect field.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §5.4
  (abstract Jordan decomposition).
-/

public section

open LieAlgebra Module.End

namespace TauCeti

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

section Existence

variable [IsKilling K L]

/-- **Abstract Jordan decomposition, existence for split elements.** In a finite-dimensional
Lie algebra with nondegenerate Killing form, an element `x` whose adjoint action has spanning
generalized eigenspaces is a sum `n + s` of commuting elements with `ad n` nilpotent and `ad s`
semisimple. Both `ad n` and `ad s` are polynomials in `ad x`. -/
theorem exists_isNilpotent_ad_isSemisimple_ad_of_iSup_maxGenEigenspace_eq_top (x : L)
    (hx : ⨆ μ, maxGenEigenspace (ad K L x) μ = ⊤) :
    ∃ n s : L, ad K L n ∈ Algebra.adjoin K {ad K L x} ∧ ad K L s ∈ Algebra.adjoin K {ad K L x} ∧
      IsNilpotent (ad K L n) ∧ IsSemisimple (ad K L s) ∧ ⁅n, s⁆ = 0 ∧ x = n + s := by
  obtain ⟨N, S, hN, hS, hN_nil, hS_ss, hxNS⟩ :=
    (LieDerivation.ad K L x).exists_isNilpotent_isSemisimple_of_iSup_maxGenEigenspace_eq_top
      (by rwa [LieDerivation.coe_ad_apply_eq_ad_apply])
  have hNS : Commute (N : Module.End K L) S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS
      (Algebra.commute_of_mem_adjoin_self hN).symm
  obtain ⟨n, rfl⟩ := LieDerivation.IsKilling.exists_eq_ad N
  obtain ⟨s, rfl⟩ := LieDerivation.IsKilling.exists_eq_ad S
  have hns : LieDerivation.ad K L ⁅n, s⁆ = 0 := by
    ext z
    rw [LieHom.map_lie, LieDerivation.commutator_apply, LieDerivation.zero_apply, sub_eq_zero]
    exact LinearMap.congr_fun hNS.eq z
  simp only [LieDerivation.coe_ad_apply_eq_ad_apply] at hN hS hN_nil hS_ss
  exact ⟨n, s, hN, hS, hN_nil, hS_ss, (LieDerivation.IsKilling.ad_apply_eq_zero_iff K L _).mp hns,
    LieDerivation.injective_ad_of_center_eq_bot (center_eq_bot K L) (by rw [map_add, hxNS])⟩

/-- **Abstract Jordan decomposition, existence.** In a finite-dimensional Lie algebra with
nondegenerate Killing form over an algebraically closed field, every element `x` is a sum
`n + s` of commuting elements with `ad n` nilpotent and `ad s` semisimple. Both `ad n` and
`ad s` are polynomials in `ad x`. -/
theorem exists_isNilpotent_ad_isSemisimple_ad [IsAlgClosed K] (x : L) :
    ∃ n s : L, ad K L n ∈ Algebra.adjoin K {ad K L x} ∧ ad K L s ∈ Algebra.adjoin K {ad K L x} ∧
      IsNilpotent (ad K L n) ∧ IsSemisimple (ad K L s) ∧ ⁅n, s⁆ = 0 ∧ x = n + s :=
  exists_isNilpotent_ad_isSemisimple_ad_of_iSup_maxGenEigenspace_eq_top x
    (iSup_maxGenEigenspace_eq_top _)

end Existence

/-- **Abstract Jordan decomposition, uniqueness.** In a finite-dimensional Lie algebra with
trivial center over a perfect field, if `n₁ + s₁ = n₂ + s₂` where `⁅nᵢ, sᵢ⁆ = 0`, `ad nᵢ` is
nilpotent and `ad sᵢ` is semisimple, then `n₁ = n₂` and `s₁ = s₂`. -/
theorem isNilpotent_ad_isSemisimple_ad_unique [LieModule.IsFaithful K L L] [PerfectField K]
    {n₁ s₁ n₂ s₂ : L} (hn₁ : IsNilpotent (ad K L n₁)) (hs₁ : IsSemisimple (ad K L s₁))
    (hn₂ : IsNilpotent (ad K L n₂)) (hs₂ : IsSemisimple (ad K L s₂))
    (hc₁ : ⁅n₁, s₁⁆ = 0) (hc₂ : ⁅n₂, s₂⁆ = 0) (h : n₁ + s₁ = n₂ + s₂) :
    n₁ = n₂ ∧ s₁ = s₂ := by
  have hcomm {n s : L} (h : ⁅n, s⁆ = 0) : Commute (ad K L n) (ad K L s) :=
    LinearMap.ext fun z ↦ by simp [leibniz_lie n s z, h]
  obtain ⟨hn, hs⟩ := isNilpotent_isSemisimple_unique hn₁ hs₁ hn₂ hs₂ (hcomm hc₁) (hcomm hc₂)
    (by rw [← map_add, ← map_add, h])
  exact ⟨(LieModule.toEnd_eq_iff K L L).mp hn, (LieModule.toEnd_eq_iff K L L).mp hs⟩

end TauCeti
