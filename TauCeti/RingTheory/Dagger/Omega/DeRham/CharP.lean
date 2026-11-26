/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham.Basic

/-!
# Positive-characteristic counterexamples for the overconvergent de Rham complex

Over a complete ultrametric normed field `K` of prime characteristic `p > 0`, both the degree-zero
and degree-one Poincaré lemmas fail on `K⟨X₀⟩†`: `d (X₀ ^ p) = 0` with `X₀ ^ p` non-constant,
`X₀ ^ (p - 1) dX₀` has no potential in `K⟨X₀⟩†`, the overconvergent de Rham complex fails to be
exact in degree `1`, and `H¹_dR(K⟨X₀⟩† / K)` is nontrivial.
-/

public section

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra

section CharP

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- In characteristic `p`, `d (X₀ ^ p) = 0` in `Ω¹_{K⟨X₀⟩† / K}`. -/
theorem d_X_pow_charP (p : ℕ) [CharP K p] :
    d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0 ^ p) = 0 := by
  rw [(d K _).leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

omit [CompleteSpace K] in
/-- **Failure of the degree-zero Poincaré lemma in characteristic `p > 0`.** -/
theorem exists_d_eq_zero_and_notMem_range_algebraMap_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ∃ f : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) f = 0 ∧
        f ∉ Set.range (algebraMap K (washnitzerAlgebra (Fin 1) K)) :=
  ⟨X (Fin 1) K 0 ^ p, d_X_pow_charP p, X_pow_notMem_range_algebraMap 0 (Fact.out : p.Prime).pos⟩

/-- **Failure of the degree-one Poincaré lemma in characteristic `p > 0`**: `X₀ ^ (p - 1) • d X₀`
has no potential `g ∈ K⟨X₀⟩†`. -/
theorem not_exists_d_eq_X_pow_sub_one_smul_d_X_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    ¬∃ g : washnitzerAlgebra (Fin 1) K,
      d K (washnitzerAlgebra (Fin 1) K) g =
        X (Fin 1) K 0 ^ (p - 1) • d K (washnitzerAlgebra (Fin 1) K) (X (Fin 1) K 0) := by
  rintro ⟨g, hg⟩
  have hrepr := congrArg (fun ω ↦ (washnitzerBasis (Fin 1) K).repr ω 0) hg
  rw [washnitzerBasis_repr_d, LinearEquiv.map_smul, ← washnitzerBasis_apply,
    Module.Basis.repr_self, Finsupp.smul_single_one, Finsupp.single_eq_same] at hrepr
  let e : Fin 1 →₀ ℕ := Finsupp.single 0 (p - 1)
  have hcoeff := congrArg (fun f : washnitzerAlgebra (Fin 1) K ↦ MvPowerSeries.coeff e f.val) hrepr
  have hlhs : MvPowerSeries.coeff e (pderiv (Fin 1) K 0 g).val = 0 := by
    rw [coe_pderiv, MvPowerSeries.coeff_pderiv, Finsupp.single_eq_same, ← Nat.cast_add_one,
      Nat.sub_add_cancel (Fact.out : p.Prime).pos, CharP.cast_eq_zero, mul_zero]
  rw [hlhs, SubmonoidClass.coe_pow, coe_X, MvPowerSeries.coeff_X_pow, ite_eq_left rfl] at hcoeff
  exact zero_ne_one hcoeff

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
    ⟨c, (exteriorPower.oneEquiv W _).symm.injective
      (by rwa [extDerivPow_zero_zeroEquiv_symm] at hf₀)⟩

/-- In characteristic `p > 0`, `H¹_dR(K⟨X₀⟩† / K)` is nontrivial. -/
theorem nontrivial_deRhamCohomology_washnitzer_one_charP (p : ℕ) [CharP K p] [Fact p.Prime] :
    Nontrivial (deRhamCohomology K (washnitzerAlgebra (Fin 1) K) 1) :=
  not_subsingleton_iff_nontrivial.mp fun _ ↦
    not_exactAt_deRhamComplex_washnitzer_one_charP (K := K) p <|
      (HomologicalComplex.exactAt_iff_isZero_homology _ 1).mpr
        (ModuleCat.isZero_iff_subsingleton.mpr ‹_›)

end CharP

end TauCeti.Dagger.Omega
