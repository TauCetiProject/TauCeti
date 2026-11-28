/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.Omega.DeRham.Basic

/-!
# Positive-characteristic counterexamples for the overconvergent de Rham complex

Over a base ring `R` of characteristic `p`, `d R A (f ^ p) = 0` for every `f : A` in any
`R`-algebra `A` (`d_pow_charP`). Over a complete ultrametric normed field `K` of prime
characteristic `p > 0`, the degree-zero Poincaré lemma fails on every nonempty dagger polydisc
`K⟨X_σ⟩†` (`d(Xᵢ ^ p) = 0`), on every nonempty finite dagger polydisc `K⟨X_σ⟩†` the form
`Xᵢ ^ (p - 1) • d Xᵢ` is not exact (has no potential in `K⟨X_σ⟩†`), and on `K⟨X₀⟩†` it is
closed so the degree-one Poincaré lemma fails (the overconvergent de Rham complex is not exact
in degree `1` and `H¹_dR(K⟨X₀⟩† / K)` is nontrivial).
-/

public section

namespace TauCeti.Dagger.Omega

open TauCeti.Dagger.washnitzerAlgebra

section CharP

/-- In characteristic `p`, `d (f ^ p) = 0` in `Omega R A` for every `R`-algebra `A` when
`CharP R p`. -/
theorem d_pow_charP {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (p : ℕ) [CharP R p] (f : A) :
    d R A (f ^ p) = 0 := by
  rw [(d R A).leibniz_pow, ← Nat.cast_smul_eq_nsmul R, CharP.cast_eq_zero, zero_smul]

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- In characteristic `p`, `d (Xᵢ ^ p) = 0` in `Ω¹_{K⟨X_σ⟩† / K}`. -/
theorem d_X_pow_charP {σ : Type*} (i : σ) (p : ℕ) [CharP K p] :
    d K (washnitzerAlgebra σ K) (X σ K i ^ p) = 0 :=
  d_pow_charP p _

omit [CompleteSpace K] in
/-- **Failure of the degree-zero Poincaré lemma in characteristic `p > 0`** on every dagger
polydisc with at least one variable `i : σ`. -/
theorem exists_d_eq_zero_and_notMem_range_algebraMap_charP {σ : Type*} (i : σ)
    (p : ℕ) [CharP K p] [Fact p.Prime] :
    ∃ f : washnitzerAlgebra σ K,
      d K (washnitzerAlgebra σ K) f = 0 ∧
        f ∉ Set.range (algebraMap K (washnitzerAlgebra σ K)) :=
  ⟨X σ K i ^ p, d_X_pow_charP i p, X_pow_notMem_range_algebraMap i (Fact.out : p.Prime).pos⟩

/-- In characteristic `p > 0`, on every finite dagger polydisc `K⟨X_σ⟩†` with a variable `i : σ`,
the `1`-form `Xᵢ ^ (p - 1) • d Xᵢ` is not exact (has no potential `g ∈ K⟨X_σ⟩†`). -/
theorem not_exists_d_eq_X_pow_sub_one_smul_d_X_charP {σ : Type*} [Finite σ] (i : σ) (p : ℕ)
    [CharP K p] [Fact p.Prime] :
    ¬∃ g : washnitzerAlgebra σ K,
      d K (washnitzerAlgebra σ K) g =
        X σ K i ^ (p - 1) • d K (washnitzerAlgebra σ K) (X σ K i) := by
  classical
  rintro ⟨g, hg⟩
  have hrepr := congrArg (fun ω ↦ (washnitzerBasis σ K).repr ω i) hg
  simp only [washnitzerBasis_repr_d, map_smul, ← washnitzerBasis_apply, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_eq_same] at hrepr
  let e : σ →₀ ℕ := Finsupp.single i (p - 1)
  have hcoeff := congrArg (fun f : washnitzerAlgebra σ K ↦ MvPowerSeries.coeff e f.val) hrepr
  have hp : ((p - 1 : ℕ) + 1 : K) = 0 := by
    rw [← Nat.cast_add_one, Nat.sub_add_cancel (Fact.out : p.Prime).pos, CharP.cast_eq_zero]
  simp [e, coe_pderiv, MvPowerSeries.coeff_pderiv, hp, MvPowerSeries.coeff_X_pow] at hcoeff

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
  exact not_exists_d_eq_X_pow_sub_one_smul_d_X_charP (σ := Fin 1) 0 p
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
