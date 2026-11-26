/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Algebra.MvPolynomial.Cardinal
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Localization.Cardinality
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Embeddings of countable rings into algebraically closed fields and `ℓ`-adic algebraicity

This file records a Steinitz-type extension theorem for embeddings of countable commutative rings
into uncountable algebraically closed fields of the same cardinality, applies it to compare `ℂ`
with the algebraic closure `PadicAlgCl ℓ` of `ℚ_ℓ`, and deduces an `ℓ`-adic criterion for
algebraicity of complex numbers.

## Main results

* `TauCeti.exists_ringEquiv_extend`: given a countable commutative ring `K`, two uncountable
  algebraically closed fields `E` and `L` of the same cardinality, and injective ring
  homomorphisms `f : K →+* E`, `g : K →+* L`, there exists a ring isomorphism `σ : E ≃+* L`
  satisfying `σ (f a) = g a` for all `a : K`.
* `TauCeti.exists_ringHom_extend_of_cardinal_le`: an embedding of a countable ring `D` into an
  uncountable algebraically closed field `E` extends along any embedding `D →+* K` into a field `K`
  with `#K ≤ #E`.
* `TauCeti.mk_complex_eq_mk_padicAlgCl`: `#ℂ = #(PadicAlgCl p)` for every prime `p`.
* `TauCeti.isAlgebraic_of_forall_norm_ringEquiv_le`: if `x : ℂ` has uniformly bounded spectral
  norm `‖ι x‖ ≤ c` across all ring isomorphisms `ι : ℂ ≃+* PadicAlgCl ℓ`, then `x` is algebraic
  over `ℚ`.

## References

* E. Steinitz, *Algebraische Theorie der Körper*, J. Reine Angew. Math. **137** (1910), 167–309.
* Adapted from `New.exists_ringEquiv_extend` and `New.exists_ringHom_complex_extend` in
  `src/Lib/General/Geometry/GaloisCovers.lean`, `New.mk_complex_eq_mk_padicAlgCl` in
  `src/Lib/General/Padics/Ainf.lean`, and `New.isAlgebraic_of_norm_complexToCp_le` in
  `src/Lib/General/NumberTheory/PadicLimitsValuation.lean` of `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open Cardinal IsAlgClosed

namespace TauCeti

/-- **Steinitz extension for countable subrings.** Let `K` be a countable commutative ring, `E` and
`L` uncountable algebraically closed fields of the same cardinality, and `f : K →+* E`,
`g : K →+* L` injective ring homomorphisms. Then there is a ring isomorphism `σ : E ≃+* L`
satisfying `σ (f a) = g a` for every `a : K`. -/
theorem exists_ringEquiv_extend {E L : Type u} {K : Type*} [Field E] [IsAlgClosed E]
    [Field L] [IsAlgClosed L] [CommRing K] [Countable K]
    (hE : ℵ₀ < #E) (h_mk : #E = #L) (f : K →+* E) (g : K →+* L)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : E ≃+* L, ∀ a : K, σ (f a) = g a := by
  algebraize [f, g]
  have : FaithfulSMul K E := (faithfulSMul_iff_algebraMap_injective K E).2 hf
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).2 hg
  have : Nontrivial K := f.domain_nontrivial
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis K E
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis K L
  have hs_card : #E = #s := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ hs mk_le_aleph0 hE
  have ht_card : #L = #t := by
    simpa using cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht mk_le_aleph0
      (hE.trans_eq h_mk)
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1 (by rw [← hs_card, ← ht_card, h_mk])
  let Ks : Subalgebra K E := Algebra.adjoin K (Set.range (Subtype.val : s → E))
  let Kt : Subalgebra K L := Algebra.adjoin K (Set.range (Subtype.val : t → L))
  let φ : Ks ≃ₐ[K] Kt :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv K e).trans ht.1.aevalEquiv)
  have : IsAlgClosure Ks E := isAlgClosure_of_transcendence_basis Subtype.val hs
  have : IsAlgClosure Kt L := isAlgClosure_of_transcendence_basis Subtype.val ht
  refine ⟨IsAlgClosure.equivOfEquiv E L φ.toRingEquiv, fun a ↦ ?_⟩
  calc IsAlgClosure.equivOfEquiv E L φ.toRingEquiv (f a)
      = algebraMap Kt L (φ (algebraMap K Ks a)) :=
        IsAlgClosure.equivOfEquiv_algebraMap E L φ.toRingEquiv (algebraMap K Ks a)
    _ = g a := by rw [φ.commutes]; rfl

/-- Let `D` be a countable commutative ring, `E` an uncountable algebraically closed field, `K` a
field with `#K ≤ #E`, and `f : D →+* K`, `φ : D →+* E` injective ring homomorphisms. Then `φ`
extends along `f` to a ring homomorphism `ψ : K →+* E`. -/
theorem exists_ringHom_extend_of_cardinal_le {D : Type*} {K E : Type u} [CommRing D] [Countable D]
    [Field K] [Field E] [IsAlgClosed E] (hE : ℵ₀ < #E)
    {f : D →+* K} {φ : D →+* E} (hf : Function.Injective f) (hφ : Function.Injective φ)
    (h_le : #K ≤ #E) :
    ∃ ψ : K →+* E, ψ.comp f = φ := by
  let F : Type u := FractionRing (MvPolynomial E K)
  let L : Type u := AlgebraicClosure F
  have hF : #F = #E := by
    rw [Cardinal.mk_fractionRing, MvPolynomial.cardinalMk_eq_max]
    simp [hE.le, h_le]
  have h_card : #E = #L := by
    rw [← hF]
    refine le_antisymm (Cardinal.mk_le_of_injective (algebraMap F L).injective) ?_
    simpa [hF, hE.le] using Algebra.IsAlgebraic.cardinalMk_le_max F L
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extend hE h_card φ ((algebraMap K L).comp f) hφ
    ((algebraMap K L).injective.comp hf)
  exact ⟨(σ.symm : L →+* E).comp (algebraMap K L),
    RingHom.ext fun a ↦ σ.symm_apply_eq.2 (hσ a).symm⟩

/-- For every prime `p`, the complex numbers `ℂ` and the algebraic closure `PadicAlgCl p` of `ℚ_p`
have the same cardinality. -/
theorem mk_complex_eq_mk_padicAlgCl (p : ℕ) [Fact p.Prime] : #ℂ = #(PadicAlgCl p) := by
  have h_padic : #ℚ_[p] ≤ continuum := mk_quotient_le.trans ((mk_subtype_le _).trans (by simp))
  refine mk_complex.trans ((continuum_le_cardinal_of_module ℚ_[p] _).antisymm ?_)
  exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans
    (max_le h_padic aleph0_le_continuum)

/-- **`ℓ`-adic criterion for algebraicity of complex numbers.** Let `ℓ` be a prime. If the
spectral norms `‖ι x‖` of `x : ℂ` under all ring isomorphisms `ι : ℂ ≃+* PadicAlgCl ℓ` have a
common upper bound `c`, then `x` is algebraic over `ℚ`. -/
theorem isAlgebraic_of_forall_norm_ringEquiv_le {ℓ : ℕ} [Fact ℓ.Prime] {x : ℂ} {c : ℝ}
    (h_bound : ∀ ι : ℂ ≃+* PadicAlgCl ℓ, ‖ι x‖ ≤ c) : IsAlgebraic ℚ x := by
  by_contra hx
  obtain ⟨y, hy, hcy⟩ : ∃ y : PadicAlgCl ℓ, ¬IsAlgebraic ℚ y ∧ c < ‖y‖ :=
    ((Algebraic.countable ℚ (PadicAlgCl ℓ)).dense_compl ℚ_[ℓ]).exists_mem_open
      (isOpen_Ioi.preimage continuous_norm) (NormedField.exists_lt_norm _ c)
  have : Countable (Polynomial ℚ) :=
    Cardinal.mk_le_aleph0_iff.1 (by simpa using Polynomial.cardinalMk_le_max (R := ℚ))
  rw [isAlgebraic_iff_not_injective, not_not] at hx hy
  have hC : ℵ₀ < #ℂ := by simp [aleph0_lt_continuum]
  obtain ⟨ι, hι⟩ : ∃ ι : ℂ ≃+* PadicAlgCl ℓ, ∀ P : Polynomial ℚ,
      ι (Polynomial.aeval x P) = Polynomial.aeval y P :=
    exists_ringEquiv_extend hC (mk_complex_eq_mk_padicAlgCl ℓ) _ _ hx hy
  have hιx : ι x = y := by simpa using hι Polynomial.X
  exact hcy.not_ge (hιx ▸ h_bound ι)

end TauCeti

end
