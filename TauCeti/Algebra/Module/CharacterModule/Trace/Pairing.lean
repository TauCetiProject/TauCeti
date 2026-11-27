/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule.Trace.Dual
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import TauCeti.Algebra.Module.Injective.Bidual

/-!
# Lifting additive pairings through a Matlis trace

Let `R` be a finite commutative ring and `χ : CharacterModule R` a Matlis generator.
`CharacterModule.IsMatlisGenerator.liftPairing` recovers an `R`-valued bilinear pairing from an
`R`-linear pairing into additive characters using the trace comparison from
`TauCeti.Algebra.Module.CharacterModule.Trace.Dual`. Its trace determines it uniquely. Scaling
both the trace and the additive pairing by the same unit leaves it unchanged. If the additive
pairing identifies one module with the character module of a finitely generated module, the
recovered pairing is perfect. Its orthogonals in either argument agree with those computed by
the additive pairing.

These are the algebraic pairing comparisons used for finite Cartier duality over self-injective
coefficient rings.

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
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The `R`-valued bilinear pairing whose trace is the given `R`-linear pairing into additive
characters. -/
def IsMatlisGenerator.liftPairing (b : M →ₗ[R] CharacterModule N) : M →ₗ[R] N →ₗ[R] R :=
  (hχ.dualEquiv N).symm.toLinearMap.comp b

/-- Evaluating a lifted pairing applies the inverse trace comparison to the additive character. -/
@[simp]
theorem IsMatlisGenerator.liftPairing_apply (b : M →ₗ[R] CharacterModule N) (m : M) :
    hχ.liftPairing b m = (hχ.dualEquiv N).symm (b m) :=
  (rfl)

/-- Composing a lifted pairing with the trace recovers its additive character. -/
@[simp↓]
theorem IsMatlisGenerator.dualEquiv_liftPairing (b : M →ₗ[R] CharacterModule N) (m : M) :
    hχ.dualEquiv N (hχ.liftPairing b m) = b m :=
  (hχ.dualEquiv N).apply_symm_apply (b m)

/-- The trace identity characterizing the lifted pairing. -/
@[simp↓]
theorem IsMatlisGenerator.trace_liftPairing_apply (b : M →ₗ[R] CharacterModule N) (m : M) (n : N) :
    χ (hχ.liftPairing b m n) = b m n := by
  rw [← hχ.dualEquiv_apply, hχ.dualEquiv_liftPairing]

/-- The trace identity holds with every scalar inserted, as required to recover an `R`-valued
pairing from an additive duality. -/
theorem IsMatlisGenerator.trace_mul_liftPairing_apply
    (b : M →ₗ[R] CharacterModule N) (r : R) (m : M) (n : N) :
    χ (r * hχ.liftPairing b m n) = b (r • m) n := by
  rw [map_smul, smul_apply, ← hχ.trace_liftPairing_apply b m (r • n), map_smul, smul_eq_mul]

/-- A bilinear pairing is the lifted pairing exactly when its trace is the original additive
pairing. This proves uniqueness without requiring the trace to be additively injective. -/
theorem IsMatlisGenerator.liftPairing_eq_iff (b : M →ₗ[R] CharacterModule N)
    (B : M →ₗ[R] N →ₗ[R] R) :
    hχ.liftPairing b = B ↔ ∀ m n, χ (B m n) = b m n := by
  refine ⟨fun h m n ↦ h ▸ hχ.trace_liftPairing_apply b m n, fun h ↦ ?_⟩
  apply LinearMap.ext
  intro m
  apply (hχ.dualEquiv N).injective
  ext n
  simp only [hχ.dualEquiv_apply, hχ.trace_liftPairing_apply, h]

/-- Scaling the trace and the additive pairing by the same unit leaves the recovered
`R`-valued pairing unchanged. -/
theorem IsMatlisGenerator.liftPairing_units_smul (b : M →ₗ[R] CharacterModule N) (u : Rˣ) :
    (hχ.units_smul u).liftPairing ((u : R) • b) = hχ.liftPairing b := by
  apply ((hχ.units_smul u).liftPairing_eq_iff _ _).mpr
  intro m n
  simpa only [smul_apply, smul_eq_mul, LinearMap.smul_apply, map_smul] using
    hχ.trace_mul_liftPairing_apply b (u : R) m n

/-- Trace transport preserves the bijectivity of the map into the dual. -/
theorem IsMatlisGenerator.bijective_liftPairing_iff (b : M →ₗ[R] CharacterModule N) :
    Function.Bijective (hχ.liftPairing b) ↔ Function.Bijective b :=
  (hχ.dualEquiv N).symm.bijective.of_comp_iff' b

/-- A perfect additive duality with a finitely generated module over a finite ring with a
Matlis generator lifts to a perfect `R`-valued pairing. Reflexivity is supplied by
self-injectivity of the ring, so neither module is required to be free. -/
theorem IsMatlisGenerator.isPerfPair_liftPairing [Module.Finite R N]
    (b : M →ₗ[R] CharacterModule N) (hb : Function.Bijective b) :
    (hχ.liftPairing b).IsPerfPair := by
  let : Module.Injective R R := hχ.moduleInjective
  exact LinearMap.IsPerfPair.of_bijective _ ((hχ.bijective_liftPairing_iff b).mpr hb)

/-- The orthogonal of a submodule for the lifted pairing is computed by the original additive
pairing. The submodule condition is needed to detect vanishing after applying the trace. -/
@[simp high]
theorem IsMatlisGenerator.mem_orthogonalBilin_liftPairing_iff
    (b : M →ₗ[R] CharacterModule N) (S : Submodule R M) (n : N) :
    n ∈ S.orthogonalBilin (hχ.liftPairing b) ↔ ∀ m ∈ S, b m n = 0 := by
  rw [Submodule.mem_orthogonalBilin]
  simpa only [LinearMap.flip_apply, hχ.trace_liftPairing_apply] using
    (hχ.forall_apply_eq_zero_iff S ((hχ.liftPairing b).flip n)).symm

/-- The orthogonal in the other argument of the lifted pairing is computed by the original
additive pairing. -/
@[simp high]
theorem IsMatlisGenerator.mem_orthogonalBilin_flip_liftPairing_iff
    (b : M →ₗ[R] CharacterModule N) (T : Submodule R N) (m : M) :
    m ∈ T.orthogonalBilin (hχ.liftPairing b).flip ↔ ∀ n ∈ T, b m n = 0 := by
  rw [Submodule.mem_orthogonalBilin]
  simpa only [LinearMap.flip_apply, hχ.trace_liftPairing_apply] using
    (hχ.forall_apply_eq_zero_iff T (hχ.liftPairing b m)).symm

end CharacterModule
