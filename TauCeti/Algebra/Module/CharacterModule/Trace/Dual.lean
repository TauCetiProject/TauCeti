/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule.MatlisGenerator
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Comparing linear duals and additive characters by a trace

Let `R` be a finite commutative ring and `χ : CharacterModule R` a Matlis generator. Composition
with `χ` identifies `Hom_R(M, R)` with `Hom_ℤ(M, ℚ/ℤ)` for every `R`-module `M`, without a
freeness assumption. The construction uses Mathlib's `CharacterModule.homEquiv` and the
identification `R ≃ₗ[R] CharacterModule R` supplied by the generator.

The comparison is natural in `M` and scales by a unit when the generator does. A linear form
vanishes on an `R`-submodule exactly when its additive character vanishes there. In particular,
annihilators computed by linear duality agree with those computed by additive duality, even
though the trace character itself need not be injective as an additive map.

Pairing applications are developed in
`TauCeti.Algebra.Module.CharacterModule.Trace.Pairing`.

These comparisons are the algebraic input for expressing finite Cartier duality and its local
annihilators over self-injective coefficient rings. No Galois action or Tate twist is imposed
here; naturality supplies the compatibility with coefficient automorphisms.

## References

* D. Burns, R. Sakamoto and T. Sano, *On the theory of higher rank Euler, Kolyvagin and Stark
  systems, II*, arXiv:1805.08448v1, §3.1.1 and Theorem 3.1.
-/

public section

noncomputable section

namespace CharacterModule

variable {R : Type*} [CommRing R] [Finite R]
  {χ : CharacterModule R}
  (hχ : χ.IsMatlisGenerator)
  (M : Type*) [AddCommGroup M] [Module R M]

/-- A Matlis generator identifies the `R`-linear dual of any `R`-module with its additive
character module, by composition with the generator. -/
def IsMatlisGenerator.dualEquiv : Module.Dual R M ≃ₗ[R] CharacterModule M :=
  (LinearEquiv.congrRight hχ.linearEquiv).trans <|
    homEquiv.trans (congr (TensorProduct.rid R M))

variable {M}

/-- The character associated to a linear form is its composition with the trace. -/
@[simp]
theorem IsMatlisGenerator.dualEquiv_apply (f : Module.Dual R M) (m : M) :
    hχ.dualEquiv M f m = χ (f m) := by
  -- The character and tensor adjunction wrappers block rewriting directly at `m`.
  -- After evaluation at `m ⊗ 1`, only the public evaluation lemma for `linearEquiv` is needed.
  change hχ.linearEquiv (f m) 1 = χ (f m)
  simp

/-- The inverse comparison is characterized by its trace on every scalar multiple. -/
theorem IsMatlisGenerator.trace_mul_dualEquiv_symm_apply (η : CharacterModule M) (r : R) (m : M) :
    χ (r * (hχ.dualEquiv M).symm η m) = η (r • m) := by
  rw [← smul_eq_mul, ← map_smul, ← hχ.dualEquiv_apply]
  exact DFunLike.congr_fun ((hχ.dualEquiv M).apply_symm_apply η) (r • m)

/-- Applying the trace to the inverse comparison recovers the original character. -/
@[simp]
theorem IsMatlisGenerator.trace_dualEquiv_symm_apply (η : CharacterModule M) (m : M) :
    χ ((hχ.dualEquiv M).symm η m) = η m := by
  simpa only [one_mul, one_smul] using hχ.trace_mul_dualEquiv_symm_apply η 1 m

/-- Compute the inverse comparison at `m` by applying the inverse trace identification to
the character `r ↦ η (r • m)`. -/
theorem IsMatlisGenerator.dualEquiv_symm_apply (η : CharacterModule M) (m : M) :
    (hχ.dualEquiv M).symm η m =
      hχ.linearEquiv.symm (CharacterModule.dual (LinearMap.toSpanSingleton R M m) η) := by
  apply hχ.linearEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  ext r
  rw [IsMatlisGenerator.linearEquiv_apply, smul_apply, smul_eq_mul]
  exact (congrArg χ (mul_comm _ r)).trans (hχ.trace_mul_dualEquiv_symm_apply η r m)

/-- Trace comparison commutes with precomposition by a coefficient map. This includes the
inverse automorphisms used in contragredient actions. -/
theorem IsMatlisGenerator.dualEquiv_comp_dualMap
    {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (hχ.dualEquiv M).toLinearMap.comp f.dualMap =
      (CharacterModule.dual f).comp (hχ.dualEquiv N).toLinearMap := by
  ext g m
  exact (hχ.dualEquiv_apply _ _).trans (hχ.dualEquiv_apply g (f m)).symm

/-- Replacing a trace by a unit multiple scales the comparison by that unit. -/
theorem IsMatlisGenerator.dualEquiv_units_smul (u : Rˣ) (f : Module.Dual R M) :
    (hχ.units_smul u).dualEquiv M f = (u : R) • hχ.dualEquiv M f := by
  ext m
  simp only [IsMatlisGenerator.dualEquiv_apply, smul_apply, map_smul, smul_eq_mul]

/-- The trace comparison detects membership in the linear annihilator of a submodule. -/
theorem IsMatlisGenerator.mem_dualAnnihilator_iff (S : Submodule R M) (f : Module.Dual R M) :
    f ∈ S.dualAnnihilator ↔ ∀ m ∈ S, hχ.dualEquiv M f m = 0 := by
  simp only [Submodule.mem_dualAnnihilator, IsMatlisGenerator.dualEquiv_apply]
  exact (hχ.forall_apply_eq_zero_iff S f).symm

/-- Restricting an additive character to a submodule vanishes exactly when the corresponding
linear form belongs to its linear annihilator. -/
theorem IsMatlisGenerator.comap_ker_dual_subtype (S : Submodule R M) :
    (CharacterModule.dual S.subtype).ker.comap (hχ.dualEquiv M).toLinearMap =
      S.dualAnnihilator := by
  ext f
  rw [Submodule.mem_comap, LinearMap.mem_ker, hχ.mem_dualAnnihilator_iff]
  constructor
  · intro h m hm
    exact DFunLike.congr_fun h ⟨m, hm⟩
  · intro h
    ext m
    exact h m m.property

end CharacterModule
