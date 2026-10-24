/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.LinearAlgebra.SymmetricAlgebra.AdjointAction
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
import TauCeti.Algebra.DirectSum.Internal

/-!
# The symmetric algebra of a Lie module and its invariants

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module. Each endomorphism
`m ↦ ⁅x, m⁆` of `M` extends uniquely to a derivation of the symmetric algebra `S(M)`, and these
derivations preserve brackets. For `M = L` this is the adjoint action of `L` on `S(L)`
(`TauCeti.SymmetricAlgebra.adjointDerivation`); for the dual `M = L*`, with Mathlib's contragredient
action `⁅x, φ⁆ = -φ ∘ ad x`, it is the coadjoint action on `S(L*)`, the algebra of polynomial
functions on `L`.

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
* `TauCeti.SymmetricAlgebra.lieInvariants`: the subalgebra `S(M)^L` of Lie invariants.

## Main results

* `TauCeti.SymmetricAlgebra.lieModuleDerivation_ι`: `x` sends a generator `ι m` to `ι ⁅x, m⁆`.
* `LieModuleHom.map_apply_lieModuleDerivation`: naturality under Lie module maps.
* `TauCeti.SymmetricAlgebra.mem_lieInvariants_self_iff`: for the adjoint action, the invariants
  are the maximal trivial submodule of the Lie module `S(L)`.
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
derivation extending the endomorphism `m ↦ ⁅x, m⁆` of `M`. -/
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

/-- For `L` acting on itself, the action on `S(L)` is the adjoint action. -/
theorem lieModuleDerivation_self : lieModuleDerivation R L L = adjointDerivation R L :=
  LieHom.ext fun x ↦ by
    rw [lieModuleDerivation_apply, adjointDerivation_apply]
    exact congrArg _ (LinearMap.ext fun y ↦ by simp)

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

variable {R L M} {N : Type w'} [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

/-- The symmetric-algebra map induced by a morphism of Lie modules intertwines the actions. -/
theorem _root_.LieModuleHom.map_apply_lieModuleDerivation (f : M →ₗ⁅R,L⁆ N) (x : L) (p : S) :
    map R (f : M →ₗ[R] N) (lieModuleDerivation R L M x p) =
      lieModuleDerivation R L N x (map R (f : M →ₗ[R] N) p) :=
  map_apply_derivationOfEnd R (f : M →ₗ[R] N) (f := LieModule.toEnd R L M x)
    (g := LieModule.toEnd R L N x) (LinearMap.ext fun m ↦ by simp) p

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

/-- For `L` acting on itself, the invariants of `S(L)` are the vectors of the adjoint module `S(L)`
killed by `L`. -/
theorem mem_lieInvariants_self_iff {p : SymmetricAlgebra R L} :
    p ∈ lieInvariants R L L ↔ p ∈ LieModule.maxTrivSubmodule R L (SymmetricAlgebra R L) := by
  simp [mem_lieInvariants, LieModule.mem_maxTrivSubmodule, lieModuleDerivation_self]

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

/-- An element is invariant exactly when its image under the symmetric-algebra map of a Lie module
equivalence is. -/
@[simp]
theorem _root_.LieModuleEquiv.map_mem_lieInvariants_iff (e : M ≃ₗ⁅R,L⁆ N) {p : S} :
    map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) p ∈ lieInvariants R L N ↔ p ∈ lieInvariants R L M := by
  have hinj : Function.Injective (map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N)) := fun a b h ↦
    (mapEquiv R (e : M ≃ₗ[R] N)).injective (by simpa only [mapEquiv_apply] using h)
  rw [mem_lieInvariants, mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  have h : map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) (lieModuleDerivation R L M x p) =
      lieModuleDerivation R L N x (map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N) p) :=
    (e : M →ₗ⁅R,L⁆ N).map_apply_lieModuleDerivation x p
  rw [← h, ← map_zero (map R ((e : M ≃ₗ[R] N) : M →ₗ[R] N)), hinj.eq_iff]

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
