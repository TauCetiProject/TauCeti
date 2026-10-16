/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.LocalField.IntegerRing.Padic
public import TauCeti.NumberTheory.LocalField.NormalBasis
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.PadicInt

/-!
# The lattice defect of the ring of integers

Let `L/K` be a finite Galois extension of nonarchimedean local fields with Galois group
`G = L ≃ₐ[K] L`, where `K` is a finite extension of `ℚ_[p]`, and let `k` be a field of
characteristic `p`. This file computes the lattice defect (`TauCeti.latticeDefect`) of the
`G`-module `𝒪[L]` in the Grothendieck group `G₀(k[G])`:

`latticeDefect 𝒪[L] = [K : ℚ_p] · [k[G]]`
(`TauCeti.latticeDefect_integerRing_eq_finrank_smul`).

The ring `𝒪[L]` need not be free over `𝒪[K][G]`, but it contains a lattice which is. For
`θ ∈ 𝒪[L]` whose conjugates form a `K`-basis of `L`, a scaled normal basis element
(`TauCeti.exists_linearIndependent_algEquiv_apply_integerRing`), the `𝒪[K]`-span `M` of the
orbit of `θ` contains a power of `𝓂[L]` (`TauCeti.exists_pow_maximalIdeal_le_span_orbit`), so it
has finite index in `𝒪[L]`, and the two have the same defect
(`TauCeti.latticeDefect_eq_of_finiteIndex`). Through a basis `b` of `𝒪[K]` over `ℤ_p`, the
elements `b_j • σ θ` form a `ℤ_p`-basis of `M` permuted by `G`, so `M` is the `p`-adic
permutation lattice `ℤ_p[X]` on the disjoint union `X` of `[K : ℚ_p]` copies of `G`. Finally
`ℤ[X] ⊆ ℤ_p[X]` has a uniquely `p`-divisible cokernel, so `ℤ_p[X]` has the defect of the
permutation lattice `ℤ[X]`, which is the permutation class `[k[X]] = [K : ℚ_p] · [k[G]]`
(`TauCeti.latticeDefect_finsupp_padicInt`, `TauCeti.permK0_sigma_fin`).

## Main results

* `TauCeti.latticeDefect_integerRing_eq_finrank_smul`: the `p`-defect of `𝒪[L]` is
  `[K : ℚ_p] · [k[G]]`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  §VII.3, proof of (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, Lemma 2.12 and the proof of
  Theorem 2.8.
-/

public section

open Function ValuativeRel IsNonarchimedeanLocalField Module
open scoped Pointwise

namespace TauCeti

section Galois

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [IsGalois K L]

variable (k : Type) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] [FinitePadicExtension K p]
  [NeZero (p : L)]

/-- **The lattice defect of the ring of integers**: for a finite Galois extension `L/K` of
nonarchimedean local fields, with `K/ℚ_p` finite, the `p`-defect of `𝒪[L]` in `G₀(k[Gal(L/K)])` is
`[K : ℚ_p] · [k[G]]`, for `k` of characteristic `p`. The instance `NeZero (p : L)`, which holds
since `L` has characteristic zero, is what makes the defect of `𝒪[L]` defined. -/
theorem latticeDefect_integerRing_eq_finrank_smul :
    latticeDefect k (L ≃ₐ[K] L) p 𝒪[L] =
      finrank ℚ_[p] K • permK0 k (L ≃ₐ[K] L) (L ≃ₐ[K] L) := by
  classical
  set d := finrank ℚ_[p] K
  -- `θ ∈ 𝒪[L]` whose conjugates form a `K`-basis of `L`, and whose orbit spans a lattice
  obtain ⟨θ, hθ⟩ := exists_linearIndependent_algEquiv_apply_integerRing K L
  obtain ⟨n, hn⟩ := exists_pow_maximalIdeal_le_span_orbit hθ
  -- `𝒪[K]` and `𝒪[L]` as `ℤ_p`-algebras, through `𝒪[ℚ_p] ≃ ℤ_p` and `𝒪[K] → 𝒪[L]`
  let : Algebra ℤ_[p] 𝒪[K] :=
    ((algebraMap 𝒪[ℚ_[p]] 𝒪[K]).comp (Padic.integerRingEquiv p).symm.toRingHom).toAlgebra
  let : Algebra ℤ_[p] 𝒪[L] := ((algebraMap 𝒪[K] 𝒪[L]).comp (algebraMap ℤ_[p] 𝒪[K])).toAlgebra
  have : IsScalarTower ℤ_[p] 𝒪[K] 𝒪[L] := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let b : Basis (Fin d) ℤ_[p] 𝒪[K] :=
    (Module.finBasisOfFinrankEq 𝒪[ℚ_[p]] 𝒪[K] (finrank_integerRing ℚ_[p] K)).mapCoeffs
      (Padic.integerRingEquiv p) fun c x ↦ by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
          RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  -- the lattice `∑_{j,σ} ℤ_p b_j σθ = ∑_σ 𝒪[K] σθ`, free over `ℤ_p[G]`
  let e : (Σ _ : Fin d, L ≃ₐ[K] L) → 𝒪[L] := fun x ↦ b x.1 • x.2 • θ
  have he : LinearIndependent ℤ_[p] e :=
    (linearIndependent_smul b.linearIndependent (linearIndependent_smul_integerRing hθ)).comp
      (Equiv.sigmaEquivProd _ _) (Equiv.injective _)
  let ψ : ((Σ _ : Fin d, L ≃ₐ[K] L) →₀ ℤ_[p]) →+[L ≃ₐ[K] L] 𝒪[L] :=
    { (Finsupp.linearCombination ℤ_[p] e).toAddMonoidHom with
      map_smul' g f := by
        -- the underlying function of `ψ` is `Finsupp.linearCombination ℤ_[p] e`
        change Finsupp.linearCombination ℤ_[p] e (g • f) = g • Finsupp.linearCombination ℤ_[p] e f
        induction f using Finsupp.induction_linear with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | add f₁ f₂ h₁ h₂ => rw [smul_add, map_add, map_add, smul_add, h₁, h₂]
        | single x c =>
          obtain ⟨j, σ⟩ := x
          rw [Finsupp.comapSMul_single, Finsupp.linearCombination_single,
            Finsupp.linearCombination_single, ← algebraMap_smul 𝒪[K] c,
            ← algebraMap_smul 𝒪[K] c (e _), smul_comm g (algebraMap ℤ_[p] 𝒪[K] c)]
          -- unfold `e` at `g • ⟨j, σ⟩ = ⟨j, g • σ⟩`
          change _ • b j • (g • σ) • θ = _ • g • b j • σ • θ
          rw [smul_comm g (b j), smul_eq_mul, mul_smul] }
  have : (ψ : ((Σ _ : Fin d, L ≃ₐ[K] L) →₀ ℤ_[p]) →+ 𝒪[L]).range.FiniteIndex := by
    -- a quotient by an ideal is by definition the quotient by its additive subgroup
    have : Finite (𝒪[L] ⧸ (𝓂[L] ^ n).toAddSubgroup) :=
      Ring.HasFiniteQuotients.finiteQuotient (pow_ne_zero n (IsDiscreteValuationRing.not_a_field _))
    have := AddSubgroup.finiteIndex_of_finite_quotient (H := (𝓂[L] ^ n).toAddSubgroup)
    refine AddSubgroup.finiteIndex_of_le (H := (𝓂[L] ^ n).toAddSubgroup) fun y hy ↦ ?_
    have hmem : y ∈ (Submodule.span 𝒪[K] (MulAction.orbit (L ≃ₐ[K] L) θ)).restrictScalars
        ℤ_[p] := hn hy
    have hrange : Set.range b • MulAction.orbit (L ≃ₐ[K] L) θ = Set.range e := by
      rw [MulAction.orbit, Set.range_smul_range]
      exact ((Equiv.sigmaEquivProd _ _).surjective.range_comp _).symm
    rw [← Submodule.span_smul_of_span_eq_top b.span_eq, hrange,
      ← Finsupp.range_linearCombination] at hmem
    exact hmem
  rw [← latticeDefect_eq_of_finiteIndex k _ p ψ he, latticeDefect_finsupp_padicInt,
    permK0_sigma_fin]

end Galois

end TauCeti
