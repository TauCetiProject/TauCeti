/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham.Basic

/-!
# Positive-characteristic counterexamples for the overconvergent de Rham complex

Over a complete ultrametric normed field `K` of prime characteristic `p > 0`, the overconvergent de
Rham complex of `K⟨X₀⟩†` fails to be exact in degree `1`, and `H¹_dR(K⟨X₀⟩† / K)` is nontrivial
(witnessed by `X₀ ^ (p - 1) dX₀`).
-/

public section

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra

section CharP

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- In characteristic `p > 0`, `deRhamComplex K (K⟨X₀⟩†)` is not exact in degree `1`. -/
theorem not_exactAt_deRhamComplex_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬(deRhamComplex K (washnitzerAlgebra (Fin 1) K)).ExactAt 1 := by
  rw [exactAt_deRhamComplex_succ_iff K (washnitzerAlgebra (Fin 1) K) 0]; intro hex
  let W := washnitzerAlgebra (Fin 1) K
  let ω : ⋀[W]^1 (Omega K W) := (exteriorPower.oneEquiv W _).symm
    (X (Fin 1) K 0 ^ (p - 1) • d K W (X (Fin 1) K 0))
  have hclosed : ω ∈ closedForms K W 1 := by
    have := subsingleton_forms_washnitzer_of_card_lt (σ := Fin 1) (K := K) (q := 2) (by simp)
    rw [mem_closedForms]; exact Subsingleton.elim _ 0
  obtain ⟨f₀, hf₀⟩ := LinearMap.mem_range.mp ((exactForms_succ K W 0) ▸ hex.symm ▸ hclosed)
  obtain ⟨c, rfl⟩ := (exteriorPower.zeroEquiv W _).symm.surjective f₀
  exact not_exists_d_eq_X_pow_sub_one_smul_d_X_charP p
    ⟨c, (exteriorPower.oneEquiv W _).symm.injective (by rwa [exteriorDeriv_zero_symm] at hf₀)⟩

/-- In characteristic `p > 0`, `H¹_dR(K⟨X₀⟩† / K)` is nontrivial. -/
theorem nontrivial_deRhamCohomology_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    Nontrivial (deRhamCohomology K (washnitzerAlgebra (Fin 1) K) 1) :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    not_exactAt_deRhamComplex_washnitzer_one_charP (K := K) p <|
      (HomologicalComplex.exactAt_iff_isZero_homology _ 1).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr ‹_›)

end CharP

end TauCeti.Dagger.Omega
