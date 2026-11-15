/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
public import Mathlib.RingTheory.Derivation.Lie

/-!
# Derivations of a symmetric algebra induced by endomorphisms

A linear endomorphism `f` of a module `M` over a commutative ring `R` extends uniquely to a
derivation of the symmetric algebra `SymmetricAlgebra R M`, sending each generator `ι x` to
`ι (f x)`. The assignment `f ↦` (its derivation) is a homomorphism of Lie algebras from
`Module.End R M`, with the commutator bracket, to the derivation Lie algebra of the symmetric
algebra. It is natural with respect to symmetric-algebra maps, and each induced derivation
preserves every homogeneous submodule. When an algebra map out of the symmetric algebra turns `f`
into multiplication by a scalar `c` on generators, it turns the induced derivation into
multiplication by `n * c` in degree `n`, a twisted form of Euler's identity.

Specialising `f` to the endomorphisms `⁅x, -⁆` of a Lie module gives the action of a Lie algebra
on its symmetric algebra, including the adjoint action; see
`TauCeti.LinearAlgebra.SymmetricAlgebra.LieModule`.

## Main definitions and results

* `SymmetricAlgebra.derivationOfEnd`: the Lie algebra homomorphism from `Module.End R M`
  to derivations of `SymmetricAlgebra R M`.
* `SymmetricAlgebra.derivationOfEnd_ι`: the induced derivation sends `ι x` to `ι (f x)`.
* `SymmetricAlgebra.iterate_derivationOfEnd_ι`: its iterates send `ι x` to `ι (fⁿ x)`.
* `SymmetricAlgebra.map_apply_derivationOfEnd`: naturality under a linear map intertwining
  two endomorphisms.
* `SymmetricAlgebra.derivationOfEnd_mem_homogeneousSubmodule`: the induced derivation
  preserves each homogeneous submodule.
* `AlgHom.apply_derivationOfEnd_eq_mul_of_mem_homogeneousSubmodule`: Euler's identity for the
  induced derivation, after an algebra map turning `f` into a scalar on generators.
-/

public section

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

universe u v w

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The derivation of `SymmetricAlgebra R M` induced by a linear endomorphism `f` of `M`: the
unique derivation sending each generator `ι x` to `ι (f x)`. The assignment is a homomorphism of
Lie algebras from `Module.End R M`, with the commutator bracket, to the derivation Lie algebra. -/
noncomputable def derivationOfEnd :
    Module.End R M →ₗ⁅R⁆ Derivation R (SymmetricAlgebra R M) (SymmetricAlgebra R M) where
  toLinearMap := mkDerivation ∘ₗ LinearMap.llcomp R M M (SymmetricAlgebra R M) (ι R M)
  map_lie' {f g} := derivation_ext fun x => by
    simp [Derivation.commutator_apply, LieRing.of_associative_ring_bracket]

/-- The derivation induced by `f` is the derivation extending `ι ∘ f`. -/
theorem derivationOfEnd_apply (f : Module.End R M) :
    derivationOfEnd R M f = mkDerivation ((ι R M).comp f) :=
  (rfl)

/-- The derivation induced by `f` sends the generator `ι x` to `ι (f x)`. -/
@[simp]
theorem derivationOfEnd_ι (f : Module.End R M) (x : M) :
    derivationOfEnd R M f (ι R M x) = ι R M (f x) := by
  rw [derivationOfEnd_apply, mkDerivation_ι, LinearMap.comp_apply]

/-- The iterates of the derivation induced by `f` act on generators by the powers of `f`. -/
@[simp]
theorem iterate_derivationOfEnd_ι (f : Module.End R M) (n : ℕ) (x : M) :
    (derivationOfEnd R M f)^[n] (ι R M x) = ι R M ((f ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, derivationOfEnd_ι, ih, pow_succ,
      mul_apply_eq_comp]

section Naturality

variable {M} {N : Type w} [AddCommGroup N] [Module R N]

/-- A symmetric-algebra map induced by a linear map intertwining two endomorphisms intertwines the
induced derivations. -/
theorem map_apply_derivationOfEnd (φ : M →ₗ[R] N) {f : Module.End R M} {g : Module.End R N}
    (h : φ ∘ₗ f = g ∘ₗ φ) (p : SymmetricAlgebra R M) :
    map R φ (derivationOfEnd R M f p) = derivationOfEnd R N g (map R φ p) := by
  induction p using _root_.SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x =>
      have hx : φ (f x) = g (φ x) := LinearMap.congr_fun h x
      simp [hx]
  | mul p q hp hq => simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hq]
  | add p q hp hq => simp only [map_add, hp, hq]

end Naturality

/-- The derivation induced by a linear endomorphism preserves every homogeneous submodule. -/
theorem derivationOfEnd_mem_homogeneousSubmodule (f : Module.End R M) {n : ℕ}
    {p : SymmetricAlgebra R M} (hp : p ∈ homogeneousSubmodule R M n) :
    derivationOfEnd R M f p ∈ homogeneousSubmodule R M n :=
  derivation_mem_homogeneousSubmodule R M _
    (fun x => by rw [derivationOfEnd_ι]; exact ι_mem_homogeneousSubmodule R M (f x)) hp

variable {R M} in
/-- **Euler's identity, twisted by an endomorphism.** If an algebra map `φ` turns `f` into
multiplication by `c` on generators, `φ (ι (f x)) = c * φ (ι x)`, then on a homogeneous element of
degree `n` it turns the derivation induced by `f` into multiplication by `n * c`. For `f = 1` and
`φ` the identity this is Euler's identity `D p = n • p` for the Euler derivation `D`. -/
theorem _root_.AlgHom.apply_derivationOfEnd_eq_mul_of_mem_homogeneousSubmodule {A : Type*}
    [CommSemiring A] [Algebra R A] (φ : SymmetricAlgebra R M →ₐ[R] A) {f : Module.End R M} {c : A}
    (h : ∀ x, φ (ι R M (f x)) = c * φ (ι R M x)) {n : ℕ} {p : SymmetricAlgebra R M}
    (hp : p ∈ homogeneousSubmodule R M n) :
    φ (derivationOfEnd R M f p) = n * c * φ p := by
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y _ _ _ ihx ihy => simp [ihx, ihy, mul_add]
  | mem_mul m hm i x _ ih =>
    obtain ⟨y, rfl⟩ := hm
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, derivationOfEnd_ι, h, ih]
    push_cast
    ring

end SymmetricAlgebra
