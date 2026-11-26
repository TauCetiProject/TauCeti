/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule.MatlisGenerator
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import TauCeti.Algebra.Module.Injective.Bidual
import Mathlib.LinearAlgebra.TensorProduct.Associator
import TauCeti.Algebra.Module.CharacterModule

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

`CharacterModule.IsMatlisGenerator.liftPairing` recovers an `R`-valued bilinear pairing from an
`R`-linear pairing into additive characters. Its trace determines it uniquely. Scaling both
the trace and the additive pairing by the same unit leaves it unchanged. If the additive
pairing identifies one module with the character module of a finitely generated module, the
recovered pairing is perfect.

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
theorem IsMatlisGenerator.dualEquiv_dualMap
    {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (g : Module.Dual R N) :
    hχ.dualEquiv M (f.dualMap g) = CharacterModule.dual f (hχ.dualEquiv N g) := by
  ext m
  exact (hχ.dualEquiv_apply _ _).trans (hχ.dualEquiv_apply g (f m)).symm

/-- Replacing a trace by a unit multiple scales the comparison by that unit. -/
theorem IsMatlisGenerator.dualEquiv_units_smul (u : Rˣ) (f : Module.Dual R M) :
    (hχ.units_smul u).dualEquiv M f = (u : R) • hχ.dualEquiv M f := by
  ext m
  simp only [IsMatlisGenerator.dualEquiv_apply, smul_apply, map_smul, smul_eq_mul]

omit [Finite R] in
include hχ in
/-- A linear form vanishes on a submodule if and only if its trace character does. Multiplying
elements of the submodule by all scalars is essential: the trace can have an additive kernel. -/
theorem IsMatlisGenerator.forall_apply_eq_zero_iff (S : Submodule R M) (f : Module.Dual R M) :
    (∀ m ∈ S, χ (f m) = 0) ↔ ∀ m ∈ S, f m = 0 := by
  refine ⟨fun h m hm ↦ ?_, fun h m hm ↦ by rw [h m hm, map_zero]⟩
  apply (isMatlisGenerator_iff_injective.mp hχ)
  rw [map_zero]
  ext r
  simpa only [LinearMap.toSpanSingleton_apply, smul_apply, smul_eq_mul, zero_mul, map_zero,
    map_smul, mul_comm, TauCeti.CharacterModule.zero_apply] using h (r • m) (S.smul_mem r hm)

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

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The `R`-valued bilinear pairing whose trace is the given `R`-linear pairing into additive
characters. -/
def IsMatlisGenerator.liftPairing (b : M →ₗ[R] CharacterModule N) : M →ₗ[R] N →ₗ[R] R :=
  (hχ.dualEquiv N).symm.toLinearMap.comp b

/-- Composing a lifted pairing with the trace recovers its additive character. -/
@[simp]
theorem IsMatlisGenerator.dualEquiv_liftPairing (b : M →ₗ[R] CharacterModule N) (m : M) :
    hχ.dualEquiv N (hχ.liftPairing b m) = b m :=
  (hχ.dualEquiv N).apply_symm_apply (b m)

/-- The trace identity characterizing the lifted pairing. -/
@[simp]
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

end CharacterModule
