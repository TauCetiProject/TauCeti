/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Finiteness.Nakayama
public import TauCeti.Algebra.Module.Generator

/-!
# Faithful finite projective modules are generators

Let `M` be a finitely generated projective module over a commutative ring `R`, and `T` the ideal of
`R` spanned by the values of linear forms on `M` (the trace ideal). By the dual basis lemma every
element of `M` is a combination `∑ fᵢ(m) xᵢ`, so `M = T • M`. If `M` is faithful, Nakayama's lemma
forces `T = R`: otherwise `T` lies in a maximal ideal `m` with `M = m • M`, and some `r ≡ 1 mod m`
kills `M`, so `r = 0` and `1 ∈ m`. Hence `M` is a generator
(`TauCeti.Module.IsGenerator.of_faithfulSMul`).

Being a generator, `∑ φᵢ(mᵢ) = 1`, is preserved by base change to any `R`-algebra `S`
(`TauCeti.Module.IsGenerator.baseChange`), and a generator is faithful. So faithfulness of finite
projective modules is stable under base change (`TauCeti.Module.faithfulSMul_baseChange`).

## Main results

* `TauCeti.Module.IsGenerator.of_faithfulSMul`: a faithful finite projective module over a
  commutative ring is a generator.
* `TauCeti.Module.IsGenerator.baseChange`: generators are stable under base change.
* `TauCeti.Module.faithfulSMul_baseChange`: for faithful finite projective `M`, the `S`-module
  `S ⊗[R] M` is faithful.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, GTM 189, §18.
-/

public section

open TensorProduct

namespace TauCeti.Module

open _root_.Module

universe u v w

section CommSemiring

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- For a projective module, every element lies in the trace ideal times the module (the dual basis
lemma). -/
theorem top_le_iSup_range_smul_top [Projective R M] :
    (⊤ : Submodule R M) ≤ (⨆ φ : M →ₗ[R] R, LinearMap.range φ) • ⊤ := by
  obtain ⟨s, hs⟩ := projective_def'.mp (inferInstance : Projective R M)
  intro m _
  have hm : m = (s m).sum fun x c ↦ c • x := by
    simpa [Finsupp.linearCombination_apply] using (LinearMap.congr_fun hs m).symm
  rw [hm]
  exact Submodule.sum_mem _ fun x _ ↦ Submodule.smul_mem_smul
    (Submodule.mem_iSup_of_mem ((Finsupp.lapply x).comp s) (LinearMap.mem_range_self _ m))
    Submodule.mem_top

/-- **Generators are stable under base change**: if `∑ φᵢ(mᵢ) = 1` in `R`, then the base changes
of the `φᵢ` and the vectors `1 ⊗ mᵢ` give `∑ = 1` in `S`. -/
instance IsGenerator.baseChange (S : Type w) [Semiring S] [Algebra R S] [IsGenerator R M] :
    IsGenerator S (S ⊗[R] M) := by
  obtain ⟨n, φ, m, h⟩ := isGenerator_iff_exists_sum_eq_one.mp (inferInstance : IsGenerator R M)
  refine isGenerator_iff_exists_sum_eq_one.mpr
    ⟨n, fun i ↦ (AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ (φ i).baseChange S,
      fun i ↦ 1 ⊗ₜ m i, ?_⟩
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul, AlgebraTensorModule.rid_tmul]
  rw [← Finset.sum_smul, h, one_smul]

end CommSemiring

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **A faithful finite projective module is a generator**: the values of linear forms span the
ring, by the dual basis lemma and Nakayama's lemma. -/
theorem IsGenerator.of_faithfulSMul [Module.Finite R M] [Projective R M] [FaithfulSMul R M] :
    IsGenerator R M := by
  rw [isGenerator_iff_iSup_range_eq_top]
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤
    Module.Finite.fg_top (top_le_iSup_range_smul_top.trans (Submodule.smul_mono_left hle))
  have : r = 0 := FaithfulSMul.eq_of_smul_eq_smul (α := M) fun x ↦ by
    rw [hr0 x Submodule.mem_top, zero_smul]
  exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa [this] using m.neg_mem hr))

/-- **Faithfulness of finite projective modules is stable under base change.** For a faithful
finite projective `R`-module `M` and an `R`-algebra `S`, the `S`-module `S ⊗[R] M` is faithful. -/
instance faithfulSMul_baseChange (S : Type w) [Semiring S] [Algebra R S] [Module.Finite R M]
    [Projective R M] [FaithfulSMul R M] : FaithfulSMul S (S ⊗[R] M) :=
  have := IsGenerator.of_faithfulSMul (R := R) (M := M)
  inferInstance

end CommRing

end TauCeti.Module
