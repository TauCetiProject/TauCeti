/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Algebra
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Extension
public import TauCeti.RingTheory.Idempotents.Clopen.Basic
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

import TauCeti.LinearAlgebra.Pi
import TauCeti.RingTheory.Idempotents.BalancedExtension
import TauCeti.RingTheory.Idempotents.Projective

/-!
# Clopen-glued finitely generated projective modules

For a locally constant function `f : PrimeSpectrum R → ℕ`, the compact space `Spec R` forces the
range of `f` to be finite, so the clopen fibers `f⁻¹{k}` yield a complete orthogonal family of
idempotents. Gluing free modules of rank `k` over each fiber defines the finitely generated
projective module `TauCeti.ClopenRankModule R f` of stalk rank `f`, compatible with arbitrary
scalar extension and specializing to `0` and `Rⁿ` on zero and constant functions.

## Main definitions

* `TauCeti.ClopenRankModule`: the finitely generated projective `R`-module of prescribed locally
  constant rank `f : LocallyConstant (PrimeSpectrum R) ℕ`.
* `TauCeti.ClopenRankModule.balancedExtensionEquiv`: compatibility of `ClopenRankModule` with
  arbitrary extension of scalars.

## Main results

* `TauCeti.ClopenRankModule.rankAtStalk_eq`: `ClopenRankModule R f` has stalk rank `f`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2, pp. 71–72
  and Exercise II.2.6, p. 79.
-/

public section

open scoped TensorProduct
open TopologicalSpace
open PrimeSpectrum (isIdempotentElemEquivClopens)

universe u v

namespace TauCeti

/-- The finitely generated projective `R`-module obtained by gluing free modules of rank `f p`
along the clopen rank fibers of a locally constant function `f : PrimeSpectrum R → ℕ`. -/
def ClopenRankModule (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ) :
    Type u :=
  ∀ k : f.range_finite.toFinset, Fin k.val →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R)

namespace ClopenRankModule

variable (R : Type u) [CommRing R] (f : LocallyConstant (PrimeSpectrum R) ℕ)

noncomputable instance instAddCommGroup : AddCommGroup (ClopenRankModule R f) :=
  inferInstanceAs (AddCommGroup (∀ k : f.range_finite.toFinset, Fin k.val →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R)))

noncomputable instance instModule : Module R (ClopenRankModule R f) :=
  inferInstanceAs (Module R (∀ k : f.range_finite.toFinset, Fin k.val →
    (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R)))

/-- The defining identification of `ClopenRankModule R f` with the product over the finite range
of `f`. -/
noncomputable def equivPi :
    ClopenRankModule R f ≃ₗ[R]
      ∀ k : f.range_finite.toFinset, Fin k.val →
        (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R) :=
  LinearEquiv.refl R _

private theorem instFinite_factor (k : f.range_finite.toFinset) :
    Module.Finite R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span_singleton _)

private theorem instProjective_factor (k : f.range_finite.toFinset) :
    Module.Projective R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R) :=
  (isIdempotentElemEquivClopens.symm _).property.projective_span_singleton

private theorem instProjective_pi_factor (k : f.range_finite.toFinset) :
    Module.Projective R (Fin k.val →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R)) :=
  have := instProjective_factor R f k
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := R))

instance instFinite : Module.Finite R (ClopenRankModule R f) :=
  have := instFinite_factor R f
  Module.Finite.equiv (equivPi R f).symm

instance instProjective : Module.Projective R (ClopenRankModule R f) :=
  have := instProjective_pi_factor R f
  Module.Projective.of_equiv
    ((DFinsupp.linearEquivFunOnFintype (R := R)).trans (equivPi R f).symm)

/-- `ClopenRankModule R f` has stalk rank `f p` at every prime `p`. -/
@[simp]
theorem rankAtStalk_eq (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (ClopenRankModule R f) p = f p := by
  have := instFinite_factor R f
  have := instProjective_factor R f
  have := instProjective_pi_factor R f
  have (k : f.range_finite.toFinset) : Module.Flat R
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R) :=
    Module.Flat.of_projective
  have (k : f.range_finite.toFinset) : Module.Flat R (Fin k.val →
      (Ideal.span {(isIdempotentElemEquivClopens.symm (f.fiberClopens k.val)).val} : Ideal R)) :=
    Module.Flat.of_projective
  rw [Module.rankAtStalk_eq_of_equiv (equivPi R f), Module.rankAtStalk_pi,
    finsum_eq_sum_of_fintype,
    Finset.sum_eq_single_of_mem ⟨f p, f.range_finite.mem_toFinset.2 ⟨p, rfl⟩⟩ (Finset.mem_univ _)]
  · rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
    simp [(isIdempotentElemEquivClopens.symm _).property.rankAtStalk_span_singleton,
      PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff]
  · intro k _ hkne
    rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
    have hne : f p ≠ k.val := fun h ↦ hkne (Subtype.ext h.symm)
    simp [(isIdempotentElemEquivClopens.symm _).property.rankAtStalk_span_singleton,
      PrimeSpectrum.mem_asIdeal_isIdempotentElemEquivClopens_symm_iff, hne]

/-- The clopen-glued module for the zero rank function is trivial. -/
instance subsingleton_zero : Subsingleton (ClopenRankModule R 0) :=
  let z : LocallyConstant (PrimeSpectrum R) ℕ := 0
  (equivPi R z).toEquiv.subsingleton_congr.2 <|
    have (k : z.range_finite.toFinset) : Subsingleton (Fin k.val →
        (Ideal.span {(isIdempotentElemEquivClopens.symm (z.fiberClopens k.val)).val} : Ideal R)) :=
      by
      obtain ⟨_, hp⟩ := z.range_finite.mem_toFinset.1 k.property
      have hk : k.val = 0 := hp.symm
      rw [hk]
      infer_instance
    inferInstance

/-- Reindexing equivalence between clopen-glued modules for equal locally constant rank
functions. -/
noncomputable def equivOfEq {f₁ f₂ : LocallyConstant (PrimeSpectrum R) ℕ} (h : f₁ = f₂) :
    ClopenRankModule R f₁ ≃ₗ[R] ClopenRankModule R f₂ := by
  subst h
  exact LinearEquiv.refl R _

/-- The clopen-glued module for the constant rank function `n` is linearly isomorphic to `Rⁿ`. -/
noncomputable def constEquiv (n : ℕ) :
    ClopenRankModule R (LocallyConstant.const (PrimeSpectrum R) n) ≃ₗ[R] (Fin n → R) := by
  classical
  by_cases hR : Subsingleton R
  · have := Module.subsingleton R (ClopenRankModule R (LocallyConstant.const (PrimeSpectrum R) n))
    have := Module.subsingleton R (Fin n → R)
    exact LinearEquiv.ofSubsingleton _ _
  · have : Nontrivial R := not_subsingleton_iff_nontrivial.1 hR
    let c := LocallyConstant.const (PrimeSpectrum R) n
    let k₀ : c.range_finite.toFinset :=
      ⟨n, c.range_finite.mem_toFinset.2 ⟨Classical.arbitrary _, rfl⟩⟩
    have huniq (k : c.range_finite.toFinset) : k = k₀ :=
      let ⟨_, hp⟩ := c.range_finite.mem_toFinset.1 k.property; Subtype.ext hp.symm
    have htop : c.fiberClopens n = ⊤ := Clopens.ext (by ext p; simp [c])
    have he1 : (isIdempotentElemEquivClopens.symm (c.fiberClopens n)).val = 1 := by
      rw [htop, PrimeSpectrum.isIdempotentElemEquivClopens_symm_top]
    exact (equivPi R c).trans
      { toFun x i := (x k₀ i : R)
        map_add' _ _ := rfl
        map_smul' _ _ := rfl
        invFun y k i := ⟨y (Fin.cast (congrArg Subtype.val (huniq k)) i), by
          have hk : k.val = n := congrArg Subtype.val (huniq k)
          have hek : (isIdempotentElemEquivClopens.symm (c.fiberClopens k.val)).val = 1 := by
            rw [hk, he1]
          rw [hek, Ideal.span_singleton_one]; trivial⟩
        left_inv x := by funext k; cases huniq k; rfl
        right_inv _ := rfl }

/-- Extension of scalars along `φ : R →+* S` carries `ClopenRankModule R f` to the clopen-glued
module of the pulled-back rank function on `Spec S`. -/
noncomputable def balancedExtensionEquiv {S : Type v} [CommRing S] (φ : R →+* S) :
    BalancedExtension φ (ClopenRankModule R f) ≃ₗ[S]
      ClopenRankModule S (f.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩) := by
  let f' := f.comap ⟨PrimeSpectrum.comap φ, PrimeSpectrum.continuous_comap φ⟩
  have hsub : (f'.range_finite.toFinset : Set ℕ) ⊆ (f.range_finite.toFinset : Set ℕ) :=
    fun k hk ↦
      let ⟨q, hq⟩ := f'.range_finite.mem_toFinset.1 (Finset.mem_coe.1 hk)
      Finset.mem_coe.2 <| f.range_finite.mem_toFinset.2 ⟨PrimeSpectrum.comap φ q, hq⟩
  have hsubsingleton (k : ℕ) (_ : k ∈ (f.range_finite.toFinset : Set ℕ))
      (hk : k ∉ (f'.range_finite.toFinset : Set ℕ)) :
      Subsingleton (Fin k →
        (Ideal.span {(isIdempotentElemEquivClopens.symm (f'.fiberClopens k)).val} : Ideal S)) := by
    have hbot : f'.fiberClopens k = ⊥ := Clopens.ext <| Set.eq_empty_iff_forall_notMem.2
      fun q hq ↦ hk (Finset.mem_coe.2 <| f'.range_finite.mem_toFinset.2 ⟨q, by simpa using hq⟩)
    have : Subsingleton
        (Ideal.span {(isIdempotentElemEquivClopens.symm (f'.fiberClopens k)).val} : Ideal S) := by
      rw [hbot, PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot, Ideal.span_singleton_zero]
      infer_instance
    infer_instance
  have hmap (k : ℕ) : φ (isIdempotentElemEquivClopens.symm (f.fiberClopens k)).val =
      (isIdempotentElemEquivClopens.symm (f'.fiberClopens k)).val := by
    rw [PrimeSpectrum.map_isIdempotentElemEquivClopens_symm φ (f.fiberClopens k),
      LocallyConstant.preimage_fiberClopens]
  exact ((BalancedExtension.congr φ (equivPi R f)).trans <|
    (BalancedExtension.piEquiv φ _ _).trans <|
      LinearEquiv.piCongrRight fun k ↦
        (BalancedExtension.piEquiv φ _ _).trans <|
          LinearEquiv.piCongrRight fun _ ↦
            ((isIdempotentElemEquivClopens.symm
              _).property.balancedExtensionSpanSingletonEquiv φ).trans
              (LinearEquiv.ofEq _ _ (by rw [hmap]))).trans
    ((LinearEquiv.piRestrictOfSubsingleton S _ hsub hsubsingleton).trans (equivPi S f').symm)

end ClopenRankModule

end TauCeti
