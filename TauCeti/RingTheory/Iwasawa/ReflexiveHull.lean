/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.Iwasawa.PseudoIsomorphism
public import TauCeti.RingTheory.RegularLocalRing.Basic

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.Localization.Module
import TauCeti.RingTheory.RegularLocalRing.DimensionTwo

/-!
# The reflexive hull up to pseudo-isomorphism

Let `A` be a noetherian integrally closed domain and `M` a finitely generated torsion-free
`A`-module. The canonical map `M → M**` into the reflexive hull is a pseudo-isomorphism: at a
prime `𝔭` of height at most one, the ring `A_𝔭` is a field or a discrete valuation ring, so
`M_𝔭` is free and hence reflexive, and taking double duals commutes with localization for
finitely presented modules.

Over a regular local ring of dimension at most two, such as the Iwasawa algebra `Λ = O⟦T⟧`,
reflexive modules are free (`TauCeti.IsRegularLocalRing.free_of_isReflexive`), so every finitely
generated torsion-free module is pseudo-isomorphic to a free module of finite rank. Together with
the splitting off of the torsion submodule
(`TauCeti.Iwasawa.exists_isPseudoIsomorphism_prod_torsion_mkQ`), this reduces the structure
theorem for finitely generated modules over such rings to the torsion case.

## Main results

* `TauCeti.Iwasawa.isPseudoIsomorphism_dual_eval`: over a noetherian integrally closed domain,
  `M → M**` is a pseudo-isomorphism for every finitely generated torsion-free module `M`.
* `TauCeti.Iwasawa.exists_isPseudoIsomorphism_pi_of_isTorsionFree`: over a regular local ring of
  dimension at most two, a finitely generated torsion-free module admits a pseudo-isomorphism to
  `Aⁿ` for some `n`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter V, §1, where these
  facts enter the proof of the structure theorem (5.1.10).
* N. Bourbaki, *Commutative Algebra*, Chapter VII, §4.
-/

public section

namespace TauCeti.Iwasawa

open Module

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- **The reflexive hull.** Over a noetherian integrally closed domain, the canonical map
`M → M**` of a finitely generated torsion-free module into its double dual is a
pseudo-isomorphism. -/
theorem isPseudoIsomorphism_dual_eval [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Module.Finite A M] [IsTorsionFree A M] : IsPseudoIsomorphism (Dual.eval A M) := by
  have := finitePresentation_of_finite A M
  have := finitePresentation_of_finite A (Dual A M)
  refine .of_bijective_localizedModule_map fun 𝔭 h𝔭 ↦ ?_
  -- `A_𝔭` is a principal ideal domain, so the finite torsion-free module `M_𝔭` is free and hence
  -- reflexive.
  have := IsLocalization.AtPrime.isPrincipalIdealRing_of_height_le_one h𝔭
    (Localization.AtPrime 𝔭.asIdeal)
  exact (LocalizedModule.bijective_map_dual_eval_iff 𝔭.asIdeal.primeCompl
    (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule.mkLinearMap _ M)).mpr
    (bijective_dual_eval (Localization.AtPrime 𝔭.asIdeal) (LocalizedModule 𝔭.asIdeal.primeCompl M))

/-- Over a regular local ring of dimension at most two, a finitely generated torsion-free module
`M` admits a pseudo-isomorphism `M → Aⁿ` for some `n`: its reflexive hull is free. -/
theorem exists_isPseudoIsomorphism_pi_of_isTorsionFree [IsRegularLocalRing A]
    (hdim : ringKrullDim A ≤ 2) [Module.Finite A M] [IsTorsionFree A M] :
    ∃ (n : ℕ) (f : M →ₗ[A] Fin n → A), IsPseudoIsomorphism f := by
  have := IsRegularLocalRing.free_dual hdim (Dual A M)
  have := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two hdim
  let b := finBasis A (Dual A (Dual A M))
  exact ⟨_, b.equivFun.toLinearMap ∘ₗ Dual.eval A M,
    (IsPseudoIsomorphism.of_bijective b.equivFun.bijective).comp isPseudoIsomorphism_dual_eval⟩

end TauCeti.Iwasawa
