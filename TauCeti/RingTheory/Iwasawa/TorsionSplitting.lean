/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.Iwasawa.PseudoIsomorphism

import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Finiteness
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.Support

/-!
# Splitting off the torsion submodule up to pseudo-isomorphism

Let `A` be a noetherian integrally closed domain and `M` a finitely generated `A`-module with
torsion submodule `T = torsion A M`. The exact sequence `0 → T → M → M ⧸ T → 0` need not split,
but it splits up to pseudo-isomorphism: there is a linear map `φ : M → T` such that
`m ↦ (φ m, m mod T)` is a pseudo-isomorphism `M → T × M ⧸ T`. This reduces the structure theory of
finitely generated modules over such rings, and in particular over the Iwasawa algebra
`Λ = O⟦T⟧`, to the torsion and the torsion-free cases separately.

The proof is local at the finitely many primes of height one in the support of `T`. At such a
prime `𝔭` the ring `A_𝔭` is a discrete valuation ring, so the finitely generated torsion-free
module `(M ⧸ T)_𝔭` is free and the localized sequence splits. Its splitting descends to a map
`φ : M → T` restricting to multiplication by some `s ∉ 𝔭` on `T`, and by prime avoidance one `s`
works at every such prime. The final step is `TauCeti.Iwasawa.isPseudoIsomorphism_prod_mkQ`: if
`φ : M → N` restricts to multiplication by `a` on a finitely generated submodule `N`, then
`(φ, mod N)` is a pseudo-isomorphism once `a` lies in no prime of height at most one in the
support of `N`.

## Main results

* `TauCeti.Iwasawa.exists_isPseudoIsomorphism_prod_torsion_mkQ`: over a noetherian integrally
  closed domain, a finitely generated module `M` admits a pseudo-isomorphism
  `M → torsion A M × M ⧸ torsion A M` whose second component is the quotient map.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, (5.1.7) and Remarks 1–2
  after it.
-/

public section

namespace TauCeti.Iwasawa

open Submodule

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- Over a noetherian integrally closed domain, at a prime `𝔭` of height one, some `φ : M → T`
restricts to multiplication by an element `s ∉ 𝔭` on the torsion submodule `T`: the localized
sequence `0 → T_𝔭 → M_𝔭 → (M ⧸ T)_𝔭 → 0` splits, as `(M ⧸ T)_𝔭` is free over the discrete
valuation ring `A_𝔭`. -/
private theorem exists_comp_torsion_subtype_eq_lsmul [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] {𝔭 : Ideal A} [𝔭.IsPrime] (h𝔭 : 𝔭.height = 1) :
    ∃ s ∉ 𝔭, ∃ φ : M →ₗ[A] torsion A M,
      φ ∘ₗ (torsion A M).subtype = LinearMap.lsmul A (torsion A M) s := by
  set T := torsion A M
  set S := 𝔭.primeCompl
  have := IsLocalization.AtPrime.isDiscreteValuationRing_of_height_eq_one h𝔭
    (Localization.AtPrime 𝔭)
  have := Module.finitePresentation_of_finite A M
  have hex : Function.Exact (LocalizedModule.map S T.subtype) (LocalizedModule.map S T.mkQ) := by
    simp only [LocalizedModule.coe_map_eq (LocalizedModule.mkLinearMap S _)
      (LocalizedModule.mkLinearMap S _), IsLocalizedModule.iso_localizedModule_eq_refl,
      LinearEquiv.refl_symm]
    exact LocalizedModule.map_exact S _ _ (LinearMap.exact_subtype_mkQ T)
  have hsurj := LocalizedModule.map_surjective S _ T.mkQ_surjective
  -- `(M ⧸ T)_𝔭` is projective, so the localized quotient map has a section, and hence the
  -- localized inclusion has a retraction.
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (LocalizedModule.map S T.mkQ) LinearMap.id
    hsurj
  have hsplit := Function.Exact.split_tfae (f := LocalizedModule.map S T.subtype) hex
    (LocalizedModule.map_injective S _ T.injective_subtype) hsurj
  obtain ⟨ρ, hρ⟩ := (hsplit.out 1 2 rfl rfl).mp ⟨σ, hσ⟩
  exact T.subtype.exists_comp_eq_lsmul_of_comp_localizedModule_map_eq_id hρ

/-- **Splitting off the torsion submodule.** Over a noetherian integrally closed domain `A`, a
finitely generated module `M` admits a pseudo-isomorphism `M → torsion A M × M ⧸ torsion A M`
whose second component is the quotient map. Neukirch–Schmidt–Wingberg, (5.1.7). -/
theorem exists_isPseudoIsomorphism_prod_torsion_mkQ [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Module.Finite A M] :
    ∃ φ : M →ₗ[A] torsion A M, IsPseudoIsomorphism (φ.prod (torsion A M).mkQ) := by
  set T := torsion A M
  have hT : Module.IsTorsion A T := torsion_isTorsion
  -- The scalars `s` for which some `φ : M → T` restricts to multiplication by `s` on `T`.
  let I : Ideal A := (LinearMap.range (LinearMap.lcomp A T T.subtype)).comap
    (LinearMap.toSpanSingleton A (T →ₗ[A] T) LinearMap.id)
  have hI (s : A) : s ∈ I ↔ ∃ φ : M →ₗ[A] T, φ ∘ₗ T.subtype = LinearMap.lsmul A T s := by
    have hs : LinearMap.lsmul A T s = s • LinearMap.id := by ext; simp
    simp [I, hs, LinearMap.lcomp_apply']
  -- Each prime of height at most one in the support of `T` has height exactly one, so it omits
  -- an element of `I`. By prime avoidance a single element of `I` lies in none of them.
  obtain ⟨a, haI, ha⟩ := hT.exists_mem_forall_notMem_of_forall_not_le (I := I)
    fun 𝔭 hmem hht hle ↦ by
      have h𝔭 : 𝔭.asIdeal.height = 1 := by
        refine le_antisymm hht (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr fun h0 ↦ ?_))
        exact hT.notMem_support_of_mem_minimalPrimes (Ideal.height_eq_zero_iff.mp h0) hmem
      obtain ⟨s, hs, hsI⟩ := exists_comp_torsion_subtype_eq_lsmul (M := M) h𝔭
      exact hs (hle ((hI s).mpr hsI))
  obtain ⟨φ, hφ⟩ := (hI a).mp haI
  exact ⟨φ, isPseudoIsomorphism_prod_mkQ hφ ha⟩

end TauCeti.Iwasawa
