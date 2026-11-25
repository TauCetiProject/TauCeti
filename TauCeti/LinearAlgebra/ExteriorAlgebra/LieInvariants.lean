/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.TraceForm
public import TauCeti.LinearAlgebra.ExteriorAlgebra.Derivation.OfEnd
import TauCeti.Algebra.Lie.ExteriorPower
import TauCeti.LinearAlgebra.ExteriorAlgebra.AlgebraMapInv

/-!
# The invariants of the exterior algebra of a Lie module

Let `L` be a Lie algebra over a commutative ring `R` and `M` a Lie module. Each endomorphism
`m ↦ ⁅x, m⁆` of `M` extends uniquely to a derivation of the exterior algebra `⋀ M`
(`ExteriorAlgebra.derivationOfEnd`), which makes `⋀ M` a Lie module over `L`
(`ExteriorAlgebra.LieAction.instLieRingModule`). The elements killed by all of these derivations
form a subalgebra, the **Lie invariants** `(⋀ M)^L`, and its elements with zero constant term form
its positive-degree **augmentation ideal**.

The derivations preserve each exterior power `⋀ᵏ M`, so the invariants are graded: an element is
invariant exactly when each of its homogeneous components is. For a free module `M`, an
endomorphism acts on the exterior power of degree `finrank R M` by its trace, so this exterior power
is invariant as soon as `L` acts with trace zero, for instance when `L` is perfect. When `M` is
finite free over a nontrivial ring this is the top exterior power.

For the adjoint representation of a finite-dimensional semisimple Lie algebra `𝔤` over a field of
characteristic zero, `(⋀ 𝔤)^𝔤` is the cohomology ring of `𝔤`. Under the quantization map
`⋀ 𝔤 ≃ Cl(𝔤, κ)` of the Clifford algebra of the Killing form, it is identified with the commutant
of the image of the enveloping algebra (`CliffordAlgebra.equivExterior_mem_lieInvariants_iff`),
and its augmentation ideal `I` and the square `I * I` are the input to Kostant's space of
primitive invariants, the orthogonal complement of `I * I` in `I` for the form induced by the
Killing form.

This is the exterior counterpart of `TauCeti.SymmetricAlgebra.lieInvariants`.

## Main definitions

* `TauCeti.ExteriorAlgebra.lieInvariants`: the subalgebra `(⋀ M)^L` of Lie invariants.
* `TauCeti.ExteriorAlgebra.lieInvariantsAugmentation`: its augmentation ideal, the invariants
  with zero constant term.

## Main results

* `TauCeti.ExteriorAlgebra.toSubmodule_lieInvariants`: the invariants are the maximal trivial
  submodule of the Lie module `⋀ M`.
* `TauCeti.ExteriorAlgebra.ι_mem_lieInvariants_iff`: the invariants of degree one are the
  generators of the vectors killed by `L`.
* `TauCeti.ExteriorAlgebra.decompose_mem_lieInvariants_iff`: an element is invariant exactly when
  all of its homogeneous components are.
* `TauCeti.ExteriorAlgebra.exteriorPower_finrank_le_lieInvariants`: if `L` acts on a free module
  with trace zero, the exterior power in degree `finrank R M` is invariant;
  `TauCeti.ExteriorAlgebra.exteriorPower_finrank_le_lieInvariants_of_derivedSeries_eq_top`: this
  holds for every free module over a perfect Lie algebra.
* `TauCeti.ExteriorAlgebra.toSubmodule_lieInvariants_mul_lieInvariantsAugmentation_le` and
  `TauCeti.ExteriorAlgebra.lieInvariantsAugmentation_mul_toSubmodule_lieInvariants_le`: the
  augmentation ideal is a two-sided ideal of the invariants, `E * I ≤ I` and `I * E ≤ I`; in
  particular `I * I ≤ I` (`TauCeti.ExteriorAlgebra.lieInvariantsAugmentation_mul_self_le`).
* `TauCeti.ExteriorAlgebra.lieInvariantsAugmentation_eq_bot_of_subsingleton`: for `M = 0` the
  augmentation ideal vanishes.

## References

* C. Chevalley and S. Eilenberg, *Cohomology theory of Lie groups and Lie algebras*, Trans. Amer.
  Math. Soc. 63 (1948), 85--124, §§19--20.
* B. Kostant, *Clifford algebra analogue of the Hopf--Koszul--Samelson theorem, the ρ-decomposition
  `C(𝔤) = End V_ρ ⊗ C(P)`, and the `𝔤`-module structure of `⋀𝔤`*, Adv. Math. 125 (1997), 275--350.
-/

public section

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M]

/-- The **Lie invariants** `(⋀ M)^L`: the elements of the exterior algebra killed by the derivation
`ExteriorAlgebra.derivationOfEnd R M (LieModule.toEnd R L M x)` of every `x : L`. -/
noncomputable def lieInvariants : Subalgebra R (ExteriorAlgebra R M) where
  carrier := {y | ∀ x : L,
    (derivationOfEnd R M (toEnd R L M x) : Module.End R (ExteriorAlgebra R M)) y = 0}
  mul_mem' hy hz x := derivationLieAlgebra.apply_mul_eq_zero (hy x) (hz x)
  add_mem' hy hz x := by rw [map_add, hy x, hz x, add_zero]
  algebraMap_mem' r x := derivationLieAlgebra.map_algebraMap _ r

variable {R L M}

/-- Membership in the invariants: `y` is killed by the derivation of every element of `L`. -/
theorem mem_lieInvariants {y : ExteriorAlgebra R M} :
    y ∈ lieInvariants R L M ↔
      ∀ x : L, (derivationOfEnd R M (toEnd R L M x) : Module.End R (ExteriorAlgebra R M)) y = 0 :=
  Iff.rfl

section LieAction

open scoped _root_.ExteriorAlgebra.LieAction

variable (R L M) in
/-- **The invariants are the maximal trivial submodule** of the Lie module `⋀ M` of
`ExteriorAlgebra.LieAction.instLieRingModule`. -/
theorem toSubmodule_lieInvariants :
    Subalgebra.toSubmodule (lieInvariants R L M) =
      (maxTrivSubmodule R L (ExteriorAlgebra R M) : Submodule R (ExteriorAlgebra R M)) := by
  ext y
  rw [Subalgebra.mem_toSubmodule, LieSubmodule.mem_toSubmodule, mem_lieInvariants,
    mem_maxTrivSubmodule]
  simp only [LieAction.lie_def]

end LieAction

/-- The generator `ι m` is invariant exactly when the vector `m` is killed by `L`. -/
@[simp]
theorem ι_mem_lieInvariants_iff {m : M} :
    ι R m ∈ lieInvariants R L M ↔ ∀ x : L, ⁅x, m⁆ = 0 := by
  simp only [mem_lieInvariants, derivationOfEnd_ι, toEnd_apply_apply, ι_eq_zero_iff]

/-- **The invariants are graded**: an element of the exterior algebra is invariant exactly when
each of its homogeneous components is. -/
theorem decompose_mem_lieInvariants_iff {y : ExteriorAlgebra R M} :
    (∀ k, (DirectSum.decompose (fun i : ℕ ↦ ⋀[R]^i M) y k : ExteriorAlgebra R M) ∈
        lieInvariants R L M) ↔ y ∈ lieInvariants R L M := by
  simp only [mem_lieInvariants, derivationOfEnd_decompose]
  refine ⟨fun h x ↦ ?_, fun h k x ↦ by simp [h x]⟩
  refine (DirectSum.decompose (fun i : ℕ ↦ ⋀[R]^i M)).injective ?_
  ext k
  simpa using h k x

/-- A homogeneous component of an invariant is invariant. -/
theorem decompose_mem_lieInvariants {y : ExteriorAlgebra R M} (hy : y ∈ lieInvariants R L M)
    (k : ℕ) :
    (DirectSum.decompose (fun i : ℕ ↦ ⋀[R]^i M) y k : ExteriorAlgebra R M) ∈
      lieInvariants R L M :=
  decompose_mem_lieInvariants_iff.mpr hy k

/-- **The exterior power of degree `finrank R M` is invariant under a trace-free action.** If
every element of `L` acts on the free module `M` with trace zero, then `L` kills the exterior power
in degree `finrank R M`, on which an endomorphism acts by its trace
(`exteriorPower.lieMap_finrank_apply`). For `M` finite free over a nontrivial ring this is the top
exterior power. -/
theorem exteriorPower_finrank_le_lieInvariants [Module.Free R M]
    (h : ∀ x : L, LinearMap.trace R M (toEnd R L M x) = 0) :
    ⋀[R]^(Module.finrank R M) M ≤ Subalgebra.toSubmodule (lieInvariants R L M) := by
  intro y hy x
  have hy' : y = ((⟨y, hy⟩ : ⋀[R]^(Module.finrank R M) M) : ExteriorAlgebra R M) := rfl
  rw [hy', derivationOfEnd_apply_coe, exteriorPower.lieMap_finrank_apply, h x, zero_smul,
    ZeroMemClass.coe_zero]

/-- **The exterior power of degree `finrank R M` is invariant under a perfect Lie algebra.** If
`⁅L, L⁆ = L`, every element of `L` acts on the free module `M` with trace zero, so `L` kills the
exterior power in degree `finrank R M`. -/
theorem exteriorPower_finrank_le_lieInvariants_of_derivedSeries_eq_top [Module.Free R M]
    (hL : _root_.LieAlgebra.derivedSeries R L 1 = ⊤) :
    ⋀[R]^(Module.finrank R M) M ≤ Subalgebra.toSubmodule (lieInvariants R L M) :=
  exteriorPower_finrank_le_lieInvariants fun x ↦
    trace_toEnd_eq_zero_of_mem_lcs R L M le_rfl <|
      derivedSeries_le_lowerCentralSeries R L 1 <| hL ▸ LieSubmodule.mem_top x

variable (R L M) in
/-- The **augmentation ideal** of the invariants: the invariants with zero constant term, that is,
with zero component in exterior degree zero. -/
noncomputable def lieInvariantsAugmentation : Submodule R (ExteriorAlgebra R M) :=
  Subalgebra.toSubmodule (lieInvariants R L M) ⊓
    LinearMap.ker (algebraMapInv : ExteriorAlgebra R M →ₐ[R] R).toLinearMap

/-- Membership in the augmentation ideal: `y` is invariant and has zero constant term. -/
@[simp]
theorem mem_lieInvariantsAugmentation {y : ExteriorAlgebra R M} :
    y ∈ lieInvariantsAugmentation R L M ↔ y ∈ lieInvariants R L M ∧ algebraMapInv y = 0 := by
  rw [lieInvariantsAugmentation, Submodule.mem_inf, Subalgebra.mem_toSubmodule, LinearMap.mem_ker,
    AlgHom.toLinearMap_apply]

/-- The augmentation ideal consists of invariants. -/
theorem lieInvariantsAugmentation_le :
    lieInvariantsAugmentation R L M ≤ Subalgebra.toSubmodule (lieInvariants R L M) :=
  inf_le_left

/-- The invariants of a positive exterior degree lie in the augmentation ideal. -/
theorem toSubmodule_lieInvariants_inf_exteriorPower_le {k : ℕ} (hk : k ≠ 0) :
    Subalgebra.toSubmodule (lieInvariants R L M) ⊓ ⋀[R]^k M ≤ lieInvariantsAugmentation R L M :=
  fun _ hy ↦ mem_lieInvariantsAugmentation.mpr
    ⟨hy.1, algebraMapInv_eq_zero_of_mem_exteriorPower hk hy.2⟩

/-- **The augmentation ideal absorbs invariants on the left**: `E * I ≤ I`. -/
theorem toSubmodule_lieInvariants_mul_lieInvariantsAugmentation_le :
    Subalgebra.toSubmodule (lieInvariants R L M) * lieInvariantsAugmentation R L M ≤
      lieInvariantsAugmentation R L M :=
  Submodule.mul_le.mpr fun a ha b hb ↦ by
    rw [mem_lieInvariantsAugmentation] at hb ⊢
    exact ⟨mul_mem ha hb.1, by rw [map_mul, hb.2, mul_zero]⟩

/-- **The augmentation ideal absorbs invariants on the right**: `I * E ≤ I`. -/
theorem lieInvariantsAugmentation_mul_toSubmodule_lieInvariants_le :
    lieInvariantsAugmentation R L M * Subalgebra.toSubmodule (lieInvariants R L M) ≤
      lieInvariantsAugmentation R L M :=
  Submodule.mul_le.mpr fun a ha b hb ↦ by
    rw [mem_lieInvariantsAugmentation] at ha ⊢
    exact ⟨mul_mem ha.1 hb, by rw [map_mul, ha.2, zero_mul]⟩

/-- **The augmentation ideal is closed under multiplication**: `I * I ≤ I`. -/
theorem lieInvariantsAugmentation_mul_self_le :
    lieInvariantsAugmentation R L M * lieInvariantsAugmentation R L M ≤
      lieInvariantsAugmentation R L M :=
  Submodule.mul_le.mpr fun _ ha _ hb ↦ lieInvariantsAugmentation_mul_toSubmodule_lieInvariants_le <|
    Submodule.mul_mem_mul ha (lieInvariantsAugmentation_le hb)

/-- For the zero module, `⋀ M` is the scalars and the augmentation ideal vanishes. -/
theorem lieInvariantsAugmentation_eq_bot_of_subsingleton [Subsingleton M] :
    lieInvariantsAugmentation R L M = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun y hy ↦ by
    rw [← algebraMap_algebraMapInv y, (mem_lieInvariantsAugmentation.mp hy).2, map_zero]

end TauCeti.ExteriorAlgebra
