/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Symmetrization.Equiv
import TauCeti.LinearAlgebra.SymmetricAlgebra.Powers

/-!
# Adjoint equivariance and filtration of PBW symmetrization

Let `L` be a Lie algebra over a commutative `ℚ`-algebra `R`. A linear map
`e : Sym_R(L) → U_R(L)` is a *PBW symmetrization* (`IsPBWSymmetrization`) when it sends a product
of `d` generators to `1/d!` times the sum of their products in all `d!` orders. The formula
determines `e` (`IsPBWSymmetrization.unique`), since pure powers span the symmetric algebra, and the
canonical global symmetrization `pbwSymmetrizationMap` satisfies this formula.

The canonical map intertwines the adjoint actions and identifies the word filtration on
`Sym(L)` with the PBW filtration on `U(L)`. Since the formula determines the map, these
properties hold for every PBW symmetrization. An element of `Sym(L)` is a Lie invariant
exactly when its symmetrization is central in `U(L)`.

## Main definitions and results

* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization`: the permutation-average formula.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.map_lie`: adjoint equivariance.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.mem_pbwFiltration_iff`: the two-sided
  filtration statement.
* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrization_lie_and_mem_pbwFiltration_iff`: both
  properties together.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.injective`: injectivity.
* `TauCeti.UniversalEnvelopingAlgebra.IsPBWSymmetrization.mem_center_iff`: the centre criterion.
* `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_lie` and
  `TauCeti.UniversalEnvelopingAlgebra.pbwSymmetrizationMap_mem_center_iff`: the canonical map.

## References

* J. Dixmier, *Enveloping Algebras*, §2.4.
* P. Etingof, *Representations of Lie groups*, proof of Theorem 13.5.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.SymmetricAlgebra

universe u v

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R L
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι R (L := L)
local notation "𝒮" => homogeneousSubmodule R L
local notation "F" => TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R L)

/-- A linear map `Sym_R(L) → U_R(L)` is a **PBW symmetrization** when it sends a product of `d`
generators to `1/d!` times the sum of their products in all `d!` orders. The empty product is
sent to `1`. -/
structure IsPBWSymmetrization (e : SymmetricAlgebra R L →ₗ[R] U) : Prop where
  /-- The permutation-average formula on a product of generators. -/
  apply_prod_ι (d : ℕ) (x : Fin d → L) :
    e (∏ j, SymmetricAlgebra.ι R L (x j)) =
      algebraMap ℚ R (d.factorial : ℚ)⁻¹ • ∑ σ : Equiv.Perm (Fin d),
        (List.ofFn fun j ↦ ι (x (σ j))).prod

/-- The canonical symmetrization intertwines the adjoint actions on the symmetric and
enveloping algebras. -/
theorem pbwSymmetrizationMap_lie (x : L) (p : SymmetricAlgebra R L) :
    pbwSymmetrizationMap R L ⁅x, p⁆ =
      ι x * pbwSymmetrizationMap R L p - pbwSymmetrizationMap R L p * ι x := by
  let s := pbwSymmetrizationMap R L
  let D := lieModuleDerivation R L L x
  have h : s ∘ₗ D.toLinearMap = LieAlgebra.ad R U (ι x) ∘ₗ s := by
    refine linearMap_ext_ι_pow R L fun y n ↦ ?_
    have hy : SymmetricAlgebra.ι R L y ^ n ∈ 𝒮 n := by
      simpa using prod_map_ι_mem_homogeneousSubmodule R L (List.replicate n y)
    have hDy : D (SymmetricAlgebra.ι R L y ^ n) ∈ 𝒮 n :=
      lieModuleDerivation_mem_homogeneousSubmodule R L L x hy
    simp only [s, LinearMap.comp_apply, Derivation.coeFn_coe, LieAlgebra.ad_apply,
      pbwSymmetrizationMap_of_mem R L hy, pbwSymmetrizationMap_of_mem R L hDy]
    exact (lie_ι_pbwHomogeneousSymmetrization R L n
      (IsUnit.natCast_factorial_of_algebra ℚ n) x (p := ⟨_, hy⟩) (q := ⟨_, hDy⟩) rfl).symm
  simpa only [s, D, LinearMap.comp_apply, Derivation.coeFn_coe, LieAlgebra.ad_apply,
    LieRing.of_associative_ring_bracket, lie_eq_lieModuleDerivation] using LinearMap.congr_fun h p

/-- The symmetrization of an element of `Sym(L)` is central exactly when the element is a Lie
invariant. -/
@[simp]
theorem pbwSymmetrizationMap_mem_center_iff {p : SymmetricAlgebra R L} :
    pbwSymmetrizationMap R L p ∈ Subalgebra.center R U ↔ p ∈ lieInvariants R L L := by
  rw [mem_center_iff_forall_lie_ι, mem_lieInvariants]
  refine forall_congr' fun x ↦ ?_
  rw [← lie_skew, neg_eq_zero, LieRing.of_associative_ring_bracket,
    ← pbwSymmetrizationMap_lie, lie_eq_lieModuleDerivation,
    map_eq_zero_iff _ (pbwSymmetrizationMap_injective R L)]

variable {R L} in
/-- The permutation-average formula determines the symmetrization, since pure powers span. -/
theorem IsPBWSymmetrization.unique {e e' : SymmetricAlgebra R L →ₗ[R] U}
    (he : IsPBWSymmetrization R L e) (he' : IsPBWSymmetrization R L e') : e = e' := by
  refine linearMap_ext_ι_pow R L fun x n ↦ ?_
  have h : SymmetricAlgebra.ι R L x ^ n = ∏ _ : Fin n, SymmetricAlgebra.ι R L x := by simp
  rw [h, he.apply_prod_ι, he'.apply_prod_ι]

/-- The canonical global map `pbwSymmetrizationMap` is a PBW symmetrization. -/
theorem isPBWSymmetrization_pbwSymmetrizationMap :
    IsPBWSymmetrization R L (pbwSymmetrizationMap R L) :=
  ⟨pbwSymmetrizationMap_prod_ι R L⟩

variable {R L} in
/-- A linear map is a PBW symmetrization exactly when it is the canonical map. -/
theorem isPBWSymmetrization_iff_eq_pbwSymmetrizationMap
    {e : SymmetricAlgebra R L →ₗ[R] _root_.UniversalEnvelopingAlgebra R L} :
    IsPBWSymmetrization R L e ↔ e = pbwSymmetrizationMap R L :=
  ⟨fun he ↦ he.unique (isPBWSymmetrization_pbwSymmetrizationMap R L),
    fun he ↦ he ▸ isPBWSymmetrization_pbwSymmetrizationMap R L⟩

variable {R L}

namespace IsPBWSymmetrization

variable {e : SymmetricAlgebra R L →ₗ[R] _root_.UniversalEnvelopingAlgebra R L}
  (he : IsPBWSymmetrization R L e)
include he

/-- A PBW symmetrization fixes pure powers: `e (x ^ n) = ι x ^ n`. -/
@[simp high] -- Normalize pure powers before expanding the permutation sum.
theorem apply_ι_pow (x : L) (n : ℕ) : e (SymmetricAlgebra.ι R L x ^ n) = ι x ^ n := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_ι_pow R L x n

/-- PBW symmetrization intertwines the adjoint actions. -/
theorem map_lie (x : L) (p : SymmetricAlgebra R L) : e ⁅x, p⁆ = ι x * e p - e p * ι x := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_lie R L x p

/-- PBW symmetrization sends the `k`-th degree step into the `k`-th PBW filtration step. -/
theorem mem_pbwFiltration {k : ℕ} {p : SymmetricAlgebra R L} (hp : p ∈ F k) :
    e p ∈ pbwFiltration R L k := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_mem_pbwFiltration R L hp

/-- A symmetric tensor has degree at most `k` exactly when its symmetrization belongs to the
`k`-th PBW filtration step. -/
@[simp]
theorem mem_pbwFiltration_iff {k : ℕ} {p : SymmetricAlgebra R L} :
    e p ∈ pbwFiltration R L k ↔ p ∈ F k := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_mem_pbwFiltration_iff R L

/-- PBW symmetrization is injective. -/
theorem injective : Function.Injective e := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_injective R L

/-- A symmetrization commutes with the enveloping algebra exactly when the original element is a
Lie invariant. -/
@[simp]
theorem mem_center_iff {p : SymmetricAlgebra R L} :
    e p ∈ Subalgebra.center R U ↔ p ∈ lieInvariants R L L := by
  rw [isPBWSymmetrization_iff_eq_pbwSymmetrizationMap.mp he]
  exact pbwSymmetrizationMap_mem_center_iff R L

end IsPBWSymmetrization

/-- PBW symmetrization intertwines the adjoint actions and identifies the two filtrations. -/
theorem pbwSymmetrization_lie_and_mem_pbwFiltration_iff
    {e : SymmetricAlgebra R L →ₗ[R] U} (he : IsPBWSymmetrization R L e) :
    (∀ (x : L) (p : SymmetricAlgebra R L), e ⁅x, p⁆ = ι x * e p - e p * ι x) ∧
      ∀ (n : ℕ) (p : SymmetricAlgebra R L), e p ∈ pbwFiltration R L n ↔ p ∈ F n :=
  ⟨he.map_lie, fun _ _ ↦ he.mem_pbwFiltration_iff⟩

end TauCeti.UniversalEnvelopingAlgebra
