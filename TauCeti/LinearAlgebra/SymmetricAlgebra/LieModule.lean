/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Derivation.OfEnd
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.Algebra.DirectSum.Internal

/-!
# The symmetric algebra of a Lie module and its invariants

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module. Each endomorphism
`m ↦ ⁅x, m⁆` of `M` extends uniquely to a derivation of the symmetric algebra `S(M)`, and these
derivations preserve brackets, so `S(M)` is again a Lie module over `L` and the generic Lie-module
API applies to it. For `M = L` this is the adjoint action of `L` on `S(L)`; for the dual `M = L*`,
with Mathlib's contragredient action `⁅x, φ⁆ = -φ ∘ ad x`, it is the coadjoint action on `S(L*)`,
the algebra of polynomial functions on `L`. The action is natural in `M`, and for the adjoint
action also in `L`.

The elements of `S(M)` killed by every derivation `⁅x, -⁆` form a subalgebra, the **Lie
invariants** `S(M)^L`. The derivations preserve each homogeneous degree, so the homogeneous
components of an invariant are again invariant. A Lie module equivalence `M ≃ N` induces an
algebra equivalence `S(M) ≃ S(N)` intertwining the two actions, which therefore carries `S(M)^L`
onto `S(N)^L`.

For a finite-dimensional semisimple Lie algebra over an algebraically closed field of
characteristic zero, the invariants `S(L)^L` are the leading symbols of the centre of the
enveloping algebra, and Chevalley's restriction theorem identifies the invariant polynomial
functions `S(L*)^L` with the Weyl-invariant polynomial functions on a Cartan subalgebra.

## Main definitions

* `TauCeti.SymmetricAlgebra.lieModuleDerivation`: the action of `L` on `S(M)` by derivations.
* `TauCeti.SymmetricAlgebra.instLieRingModule`, `TauCeti.SymmetricAlgebra.instLieModule`: `S(M)`
  is a Lie module over `L` through these derivations, with
  `TauCeti.SymmetricAlgebra.lie_eq_lieModuleDerivation` identifying the bracket.
* `TauCeti.SymmetricAlgebra.lieInvariants`: the subalgebra `S(M)^L` of Lie invariants.

## Main results

* `TauCeti.SymmetricAlgebra.lieModuleDerivation_ι`: `x` sends a generator `ι m` to `ι ⁅x, m⁆`.
* `LieModuleHom.map_apply_lieModuleDerivation`: naturality under Lie module maps.
* `LieHom.map_apply_lieModuleDerivation`: naturality of the adjoint action under Lie algebra maps.
* `TauCeti.SymmetricAlgebra.lieModuleDerivation_mem_homogeneousSubmodule`: the action preserves
  each homogeneous degree.
* `TauCeti.SymmetricAlgebra.mem_lieInvariants_iff_mem_maxTrivSubmodule`: the invariants are the
  maximal trivial submodule of the Lie module `S(M)`.
* `TauCeti.SymmetricAlgebra.decompose_mem_lieInvariants_iff`: an element is invariant exactly when
  all of its homogeneous components are.
* `LieModuleEquiv.map_lieInvariants`: a Lie module equivalence carries the invariants
  onto the invariants.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1 and
  §23.3, where `L` acts on `S(L)` and on the polynomial functions `S(L*)` by derivations.
* J. Dixmier, *Enveloping Algebras*, §2.4.
-/

public section

namespace TauCeti.SymmetricAlgebra

open _root_.SymmetricAlgebra

universe u v w w'

variable (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "S" => SymmetricAlgebra R M
attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The action by derivations -/

/-- The action of `L` on the symmetric algebra of a Lie module `M`, by derivations: `x` acts by the
derivation extending the endomorphism `m ↦ ⁅x, m⁆` of `M`. For `M = L` this is the adjoint action
of `L` on `S(L)`, by the derivations extending `LieAlgebra.ad`. -/
noncomputable def lieModuleDerivation : L →ₗ⁅R⁆ Derivation R S S :=
  (derivationOfEnd R M).comp (LieModule.toEnd R L M)

/-- The derivation by which `x` acts is the derivation induced by the endomorphism `⁅x, -⁆`. -/
theorem lieModuleDerivation_apply (x : L) :
    lieModuleDerivation R L M x = derivationOfEnd R M (LieModule.toEnd R L M x) :=
  (rfl)

/-- The action of `x` sends a symmetric generator `ι m` to `ι ⁅x, m⁆`. -/
@[simp]
theorem lieModuleDerivation_ι (x : L) (m : M) :
    lieModuleDerivation R L M x (ι R M m) = ι R M ⁅x, m⁆ := by
  rw [lieModuleDerivation_apply, derivationOfEnd_ι, LieModule.toEnd_apply_apply]

/-- The symmetric algebra of `M` is a Lie ring module over `L` through the derivations
`lieModuleDerivation`. -/
noncomputable instance instLieRingModule : LieRingModule L S :=
  LieRingModule.compLieHom S (lieModuleDerivation R L M)

/-- The symmetric algebra of `M` is a Lie module over `L` through the derivations
`lieModuleDerivation`. -/
noncomputable instance instLieModule : LieModule R L S :=
  LieModule.compLieHom S (lieModuleDerivation R L M)

/-- The bracket of `x : L` with `p ∈ S(M)` is the derivation by which `x` acts, applied to `p`. -/
@[simp]
theorem lie_eq_lieModuleDerivation (x : L) (p : S) : ⁅x, p⁆ = lieModuleDerivation R L M x p :=
  (rfl)

/-- The action of `L` preserves each homogeneous submodule of the symmetric algebra. -/
theorem lieModuleDerivation_mem_homogeneousSubmodule (x : L) {n : ℕ} {p : S}
    (hp : p ∈ homogeneousSubmodule R M n) :
    lieModuleDerivation R L M x p ∈ homogeneousSubmodule R M n :=
  derivationOfEnd_mem_homogeneousSubmodule R M _ hp

/-- The action of `L` commutes with the projections onto the homogeneous components. -/
theorem lieModuleDerivation_decompose (x : L) (p : S) (n : ℕ) :
    lieModuleDerivation R L M x (DirectSum.decompose (homogeneousSubmodule R M) p n : S) =
      (DirectSum.decompose (homogeneousSubmodule R M) (lieModuleDerivation R L M x p) n : S) :=
  DirectSum.map_decompose_shift (homogeneousSubmodule R M) (homogeneousSubmodule R M)
    (lieModuleDerivation R L M x).toLinearMap.toAddMonoidHom id
    Function.injective_id (fun _ _ hq ↦ lieModuleDerivation_mem_homogeneousSubmodule R L M x hq)
    n p

section Naturality

variable {R L M}

section LieModuleHom

variable {N : Type w'} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The symmetric-algebra map induced by a morphism of Lie modules intertwines the actions. -/
theorem _root_.LieModuleHom.map_apply_lieModuleDerivation (f : M →ₗ⁅R,L⁆ N) (x : L) (p : S) :
    map R (f : M →ₗ[R] N) (lieModuleDerivation R L M x p) =
      lieModuleDerivation R L N x (map R (f : M →ₗ[R] N) p) :=
  map_apply_derivationOfEnd R (f : M →ₗ[R] N) (f := LieModule.toEnd R L M x)
    (g := LieModule.toEnd R L N x) (LinearMap.ext fun m ↦ by simp) p

end LieModuleHom

section LieHom

variable {L' : Type w'} [LieRing L'] [LieAlgebra R L']

/-- The symmetric-algebra map induced by a Lie algebra homomorphism intertwines the adjoint
actions. -/
theorem _root_.LieHom.map_apply_lieModuleDerivation (f : L →ₗ⁅R⁆ L') (x : L)
    (p : SymmetricAlgebra R L) :
    map R f.toLinearMap (lieModuleDerivation R L L x p) =
      lieModuleDerivation R L' L' (f x) (map R f.toLinearMap p) :=
  map_apply_derivationOfEnd R f.toLinearMap (f := LieModule.toEnd R L L x)
    (g := LieModule.toEnd R L' L' (f x)) (LinearMap.ext fun y ↦ by simp) p

end LieHom

end Naturality

/-! ### The invariants -/

/-- The **Lie invariants** `S(M)^L`: the elements of the symmetric algebra killed by the action of
every element of `L`. -/
noncomputable def lieInvariants : Subalgebra R S where
  carrier := {p | ∀ x : L, lieModuleDerivation R L M x p = 0}
  mul_mem' {p q} hp hq x := by simp [Derivation.leibniz, hp x, hq x]
  add_mem' {p q} hp hq x := by simp [hp x, hq x]
  algebraMap_mem' r x := (lieModuleDerivation R L M x).map_algebraMap r

variable {R L M}

/-- Membership in the invariants: `p` is killed by the action of every element of `L`. -/
theorem mem_lieInvariants {p : S} :
    p ∈ lieInvariants R L M ↔ ∀ x : L, lieModuleDerivation R L M x p = 0 :=
  Iff.rfl

/-- The invariants of `S(M)` are the vectors of the Lie module `S(M)` killed by `L`. -/
theorem mem_lieInvariants_iff_mem_maxTrivSubmodule {p : S} :
    p ∈ lieInvariants R L M ↔ p ∈ LieModule.maxTrivSubmodule R L S := by
  rw [mem_lieInvariants, LieModule.mem_maxTrivSubmodule]
  simp only [lie_eq_lieModuleDerivation]

/-- The generator `ι m` of a vector `m` killed by `L` is invariant. -/
theorem ι_mem_lieInvariants {m : M} (hm : ∀ x : L, ⁅x, m⁆ = 0) :
    ι R M m ∈ lieInvariants R L M :=
  mem_lieInvariants.mpr fun x ↦ by simp [hm x]

/-- **The invariants are graded**: an element of the symmetric algebra is invariant exactly when
each of its homogeneous components is. -/
theorem decompose_mem_lieInvariants_iff {p : S} :
    (∀ n, (DirectSum.decompose (homogeneousSubmodule R M) p n : S) ∈ lieInvariants R L M) ↔
      p ∈ lieInvariants R L M := by
  simp only [mem_lieInvariants, lieModuleDerivation_decompose]
  refine ⟨fun h x ↦ ?_, fun h n x ↦ by simp [h x]⟩
  refine (DirectSum.decompose (homogeneousSubmodule R M)).injective ?_
  ext n
  simpa using h n x

/-- A homogeneous component of an invariant is invariant. -/
theorem decompose_mem_lieInvariants {p : S} (hp : p ∈ lieInvariants R L M) (n : ℕ) :
    (DirectSum.decompose (homogeneousSubmodule R M) p n : S) ∈ lieInvariants R L M :=
  decompose_mem_lieInvariants_iff.mpr hp n

section Equiv

variable {N : Type w'} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The symmetric-algebra map induced by a Lie module equivalence intertwines the actions. -/
theorem _root_.LieModuleEquiv.map_apply_lieModuleDerivation (e : M ≃ₗ⁅R,L⁆ N) (x : L) (p : S) :
    map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) (lieModuleDerivation R L M x p) =
      lieModuleDerivation R L N x (map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) p) :=
  map_apply_derivationOfEnd R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) (f := LieModule.toEnd R L M x)
    (g := LieModule.toEnd R L N x)
    (LinearMap.ext fun m ↦ by simpa [-LieModuleHom.map_lie] using (e : M →ₗ⁅R,L⁆ N).map_lie x m) p

/-- An element is invariant exactly when its image under the symmetric-algebra map of a Lie module
equivalence is. -/
@[simp]
theorem _root_.LieModuleEquiv.map_mem_lieInvariants_iff (e : M ≃ₗ⁅R,L⁆ N) {p : S} :
    map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) p ∈ lieInvariants R L N ↔ p ∈ lieInvariants R L M := by
  rw [mem_lieInvariants, mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  rw [← e.map_apply_lieModuleDerivation, ← mapEquiv_apply, EmbeddingLike.map_eq_zero_iff]

/-- **Transport of invariants**: the symmetric-algebra map of a Lie module equivalence carries the
invariants onto the invariants. -/
theorem _root_.LieModuleEquiv.map_lieInvariants (e : M ≃ₗ⁅R,L⁆ N) :
    (lieInvariants R L M).map (map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N)) = lieInvariants R L N := by
  ext q
  rw [Subalgebra.mem_map]
  refine ⟨fun ⟨p, hp, hpq⟩ ↦ hpq ▸ e.map_mem_lieInvariants_iff.mpr hp, fun hq ↦ ?_⟩
  have hq' : map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) ((mapEquiv R (e : M ≃ₗ[R] N)).symm q) = q := by
    rw [← mapEquiv_apply, AlgEquiv.apply_symm_apply]
  exact ⟨_, e.map_mem_lieInvariants_iff.mp (hq'.symm ▸ hq), hq'⟩

end Equiv

end TauCeti.SymmetricAlgebra
