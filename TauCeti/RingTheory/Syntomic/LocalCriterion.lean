/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import TauCeti.RingTheory.Syntomic.StandardSyntomic
import TauCeti.RingTheory.Extension.Presentation.LocalizationAway
import TauCeti.RingTheory.Finiteness.Nakayama
import TauCeti.RingTheory.KrullDimension.Localization

/-!
# A local presentation criterion for standard syntomic algebras over a field

Let `P` present a `k`-algebra `A` as `k[x₁, …, x_m] ⧸ I`, and let `q` be a prime of `A`. If the
fibre of `I` at some field-valued point killing `q` has dimension at most `m - n`, and all primes
of `A` near `q` have height at most `n`, then `q` has a standard syntomic neighbourhood `A[1/g]`
of relative dimension `n` over `k`
(`TauCeti.exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_finrank_le`).
By Nakayama's lemma the kernel `I` needs at most `m - n` generators after inverting one element,
and Krull's height theorem forces the localization to have the expected dimension.

This is the common last step of descending standard syntomic algebras along field extensions
(`TauCeti.RingTheory.Syntomic.Descent`) and along étale maps of the source
(`TauCeti.RingTheory.Syntomic.SourceDescent`).
-/

public section

open TensorProduct

namespace TauCeti

variable {n : ℕ} {k A : Type*} [Field k] [CommRing A] [Algebra k A]

/-- **A presentation criterion for standard syntomic charts.** Let `P` present a `k`-algebra `A`
with finitely many generators indexed by `ι`, and let `q` be a prime of `A`. Suppose that some
field-valued point `P.Ring → F`, killing the inverse image of `q` in `P.Ring`, satisfies
`dim_F (F ⊗[P.Ring] P.ker) + n ≤ #ι`, and that every prime of `A` avoiding some `a ∉ q` has height
at most `n`. Then `q` has a neighbourhood `A[1/g]`, `g ∉ q`, which is standard syntomic of
relative dimension `n` over `k`. -/
theorem exists_notMem_isStandardSyntomicOfRelativeDimension_localization_away_of_finrank_le
    {ι : Type*} [Finite ι] (P : _root_.Algebra.Generators k A ι) (q : Ideal A)
    [q.IsPrime] (F : Type*) [Field F] [_root_.Algebra P.Ring F]
    (hF : ∀ r : P.Ring, algebraMap P.Ring A r ∈ q → algebraMap P.Ring F r = 0)
    (hfin : Module.finrank F (F ⊗[P.Ring] P.ker) + n ≤ Nat.card ι) {a : A} (ha : a ∉ q)
    (hdim : ∀ p : Ideal A, p.IsPrime → a ∉ p → Ideal.height p ≤ n) :
    ∃ g ∉ q, Algebra.IsStandardSyntomicOfRelativeDimension n k (Localization.Away g) := by
  classical
  -- `P.Ring` is Noetherian, so its ideal `P.ker` is finitely generated.
  have : Module.Finite P.Ring P.ker := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  -- By Nakayama's lemma, after inverting some `r` the kernel needs at most `#ι - n` generators.
  obtain ⟨s, hs, r, hr, hrs⟩ :=
    Module.exists_finset_card_le_finrank_and_smul_mem_span (R := P.Ring) (M := P.ker) (F := F)
  let ϕ : P.Ring →ₐ[k] A := MvPolynomial.aeval P.val
  have hker : RingHom.ker ϕ = P.ker := P.ker_eq_ker_aeval_val.symm
  have hk : ∀ l : s, (l : P.ker).val ∈ RingHom.ker ϕ := fun l ↦ by
    rw [hker]
    exact (l : P.ker).property
  obtain ⟨b, rfl⟩ := P.aeval_val_surjective a
  have hg : ∀ x ∈ RingHom.ker ϕ,
      r * b * x ∈ Ideal.span (Set.range fun l : s ↦ (l : P.ker).val) := by
    intro x hx
    rw [hker] at hx
    have := Submodule.mem_map_of_mem (f := P.ker.subtype) (hrs ⟨x, hx⟩)
    rw [Submodule.map_span] at this
    have hrange : (Set.range fun l : s ↦ (l : P.ker).val) = P.ker.subtype '' s := by
      ext
      simp
    rw [mul_right_comm, hrange]
    exact Ideal.mul_mem_right _ _ this
  obtain ⟨PB⟩ := _root_.Algebra.Presentation.nonempty_presentation_localizationAway
    P.aeval_val_surjective hk hg
  have hrq : ϕ (r * b) ∉ q := by
    rw [map_mul]
    exact ‹q.IsPrime›.mul_notMem
      (fun h' ↦ hr (hF r (by rwa [_root_.Algebra.Generators.algebraMap_apply]))) ha
  refine ⟨ϕ (r * b), hrq, ?_⟩
  -- `A[1/ϕ (r b)]` is nonzero, its primes have height at most `n`, and its presentation has at
  -- least `n` more generators than relations.
  have hdisj : Disjoint (Submonoid.powers (ϕ (r * b)) : Set A) q :=
    (Ideal.disjoint_powers_iff_notMem _ ‹q.IsPrime›.isRadical).mpr hrq
  have hqB : (q.map (algebraMap A (Localization.Away (ϕ (r * b))))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ _ q inferInstance hdisj
  have : Nontrivial (Localization.Away (ϕ (r * b))) := PrimeSpectrum.nontrivial ⟨_, hqB⟩
  refine PB.isStandardSyntomicOfRelativeDimension_of_ringKrullDim_le ?_
    (ringKrullDim_localization_le_of_height_le (.powers (ϕ (r * b))) fun p hp hdisj ↦
      hdim p hp fun hbp ↦
        ((Ideal.disjoint_powers_iff_notMem _ hp.isRadical).mp hdisj)
          (map_mul ϕ r b ▸ p.mul_mem_left _ hbp))
  have := Fintype.ofFinite ι
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_coe] at hfin ⊢
  omega

end TauCeti
