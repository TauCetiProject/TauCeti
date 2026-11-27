/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.List.Rotate
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.Trace

import Mathlib.LinearAlgebra.Dimension.Free
import TauCeti.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Basic facts about the trace

Mathlib's `LinearMap.trace R M` is defined through a finite basis of `M`, and is `0` when `M` has
none. This file names that case of the definition, so that proofs need not unfold
`LinearMap.trace`. It also computes the trace of an endomorphism whose range lies in a free
submodule with a given basis, as the trace of its matrix in that basis, and the trace of an
endomorphism mapping a basis into itself, as the number of basis vectors it fixes.

## Main results

* `TauCeti.LinearMap.trace_eq_zero_of_not_exists_basis`: the trace vanishes on a module with no
  finite basis.
* `TauCeti.LinearMap.trace_eq_zero_of_not_finite`: the trace vanishes on a module that is not
  finite.
* `LinearMap.trace_eq_zero_of_subsingleton`: the trace vanishes on a subsingleton module.
* `LinearMap.trace_list_prod_rotate`, `LinearMap.trace_list_prod_of_isRotated`:
  the trace of a product of endomorphisms is invariant under cyclic rotation of the factors.
* `LinearMap.trace_list_ofFn_prod_orbit_eq_of_orbitRel`: the trace of the ordered product of
  `f` along a `⟨σ⟩`-orbit does not depend on the starting point of the orbit.
* `LinearMap.eq_trace_smul_one_of_finrank_eq_one`: on a free module of rank one, an
  endomorphism is its trace times the identity.
* `LinearMap.trace_eq_sum_of_range_le_of_apply_single_eq`: the trace of an endomorphism whose
  range lies in a free submodule `ι → R` is the trace of its matrix there.
* `LinearMap.trace_eq_natCard_of_apply_basis_eq`: an endomorphism sending each basis vector `b i`
  to a basis vector `b (π i)` has trace the number of fixed points of `π`.
* `LinearMap.trace_eq_neg_of_toMatrix_eq_neg_transpose`: endomorphisms with matrices `A` and
  `-Aᵀ` have opposite traces.
-/

public section

namespace TauCeti.LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The trace vanishes on a module with no finite basis. This is the endomorphism counterpart of
`Algebra.trace_eq_zero_of_not_exists_basis`. -/
theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset M, Nonempty (Module.Basis s R M)) :
    _root_.LinearMap.trace R M = 0 :=
  dite_eq_right fun hb ↦ (h hb).elim

/-- The trace vanishes on a module that is not finite. -/
theorem trace_eq_zero_of_not_finite (h : ¬Module.Finite R M) : _root_.LinearMap.trace R M = 0 :=
  trace_eq_zero_of_not_exists_basis fun ⟨_, ⟨b⟩⟩ ↦ h (.of_basis b)

end TauCeti.LinearMap

namespace LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The trace vanishes on a subsingleton module. -/
theorem trace_eq_zero_of_subsingleton [Subsingleton M] (f : M →ₗ[R] M) :
    _root_.LinearMap.trace R M f = 0 := by
  rw [Subsingleton.elim f 0, map_zero]

/-- **Cyclic invariance of the trace of a product.** Rotating the list of factors of a product of
endomorphisms does not change its trace. -/
theorem trace_list_prod_rotate (l : List (M →ₗ[R] M)) (n : ℕ) :
    _root_.LinearMap.trace R M (l.rotate n).prod = _root_.LinearMap.trace R M l.prod := by
  induction n with
  | zero => rw [List.rotate_zero]
  | succ n ih =>
    rw [← List.rotate_rotate, ← ih]
    rcases l.rotate n with _ | ⟨a, l'⟩
    · rfl
    · rw [List.rotate_cons_succ, List.rotate_zero, List.prod_append, List.prod_singleton,
        List.prod_cons, _root_.LinearMap.trace_mul_comm]

/-- The trace of a product of endomorphisms depends only on the cyclic order of the factors. -/
theorem trace_list_prod_of_isRotated {l₁ l₂ : List (M →ₗ[R] M)} (h : l₁ ~r l₂) :
    _root_.LinearMap.trace R M l₁.prod = _root_.LinearMap.trace R M l₂.prod := by
  obtain ⟨n, rfl⟩ := h
  exact (trace_list_prod_rotate l₁ n).symm

/-- The trace of the ordered product of `f` along a `⟨σ⟩`-orbit does not depend on the starting
point: starting at `(σ ^ d) x` instead of `x` rotates the list of factors by `d`. -/
theorem trace_list_ofFn_prod_orbit_eq_of_orbitRel {ι : Type*} [Finite ι] (σ : Equiv.Perm ι)
    (f : ι → M →ₗ[R] M) {x y : ι} (h : MulAction.orbitRel (Subgroup.zpowers σ) ι y x) :
    _root_.LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) y) ↦
        f ((σ ^ (t : ℕ)) y)).prod =
      _root_.LinearMap.trace R M (List.ofFn fun t : Fin (Function.minimalPeriod (σ • ·) x) ↦
        f ((σ ^ (t : ℕ)) x)).prod := by
  obtain ⟨d, rfl⟩ :=
    (σ.sameCycle_iff_mem_orbit_zpowers.mpr (MulAction.orbitRel_apply.mp h)).exists_nat_pow_eq
  have hx : x ∈ Function.periodicPts σ := σ.injective.mem_periodicPts x
  have hper : Function.minimalPeriod (σ • ·) ((σ ^ d) x) = Function.minimalPeriod (σ • ·) x := by
    rw [Equiv.Perm.coe_pow]
    exact Function.minimalPeriod_apply_iterate hx d
  refine (trace_list_prod_of_isRotated
    ⟨d, List.ext_getElem (by simpa using hper.symm) fun m h₁ h₂ ↦ ?_⟩).symm
  simp only [List.getElem_rotate, List.getElem_ofFn, List.length_ofFn]
  rw [← Equiv.Perm.mul_apply, ← pow_add, Equiv.Perm.coe_pow, Equiv.Perm.coe_pow]
  exact congrArg f (Function.iterate_mod_minimalPeriod_eq (f := σ))

end LinearMap

namespace LinearMap

/-- On a free module of rank one, an endomorphism is its trace times the identity. -/
theorem eq_trace_smul_one_of_finrank_eq_one {R V : Type*} [CommSemiring R]
    [AddCommMonoid V] [Module R V] [Module.Free R V]
    (h : Module.finrank R V = 1) (f : V →ₗ[R] V) :
    f = LinearMap.trace R V f • (1 : V →ₗ[R] V) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have := Module.subsingleton R V
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
  let b := Module.Free.chooseBasis R V
  -- A basis of a module of rank one has at most one element.
  have hle : Cardinal.mk (Module.Free.ChooseBasisIndex R V) ≤ 1 := by
    simpa [Module.rank_eq_one_iff_finrank_eq_one.2 h] using b.linearIndependent.cardinal_le_rank
  have : Subsingleton (Module.Free.ChooseBasisIndex R V) := Cardinal.le_one_iff_subsingleton.1 hle
  rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex R V) with hι | hι
  · have : Subsingleton V := b.repr.toEquiv.subsingleton
    exact LinearMap.ext fun _ ↦ Subsingleton.elim _ _
  · have : Unique (Module.Free.ChooseBasisIndex R V) := uniqueOfSubsingleton hι.some
    apply (LinearMap.toMatrix b b).injective
    ext i j
    obtain rfl : i = default := Subsingleton.elim _ _
    obtain rfl : j = default := Subsingleton.elim _ _
    simp [LinearMap.trace_eq_matrix_trace R b, Matrix.trace, Module.End.one_eq_id,
      LinearMap.toMatrix_id]

/-- **The trace of an endomorphism with range in a free submodule.** Let `φ` be an injective
linear map from `ι → R` to `M`, and let `L` be an endomorphism whose range lies in the range of `φ`
and that sends the image under `φ` of the `j`-th standard basis vector of `ι → R` to `φ (a j)`.
Then the trace of `L` is the trace `∑ j, a j j` of `a`. -/
theorem trace_eq_sum_of_range_le_of_apply_single_eq {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [Fintype ι]
    [DecidableEq ι] {φ : (ι → R) →ₗ[R] M} (hφ : Function.Injective φ) {L : M →ₗ[R] M}
    (hL : LinearMap.range L ≤ LinearMap.range φ) {a : ι → ι → R}
    (hLa : ∀ j, L (φ (Pi.single j 1)) = φ (a j)) : trace R M L = ∑ j, a j j := by
  let ρ : M →ₗ[R] ι → R := (LinearEquiv.ofInjective φ hφ).symm.toLinearMap ∘ₗ
    L.codRestrict (LinearMap.range φ) fun s ↦ hL ⟨s, rfl⟩
  have hφρ : φ ∘ₗ ρ = L := LinearMap.ext fun s ↦ by
    have h := congrArg Subtype.val
      ((LinearEquiv.ofInjective φ hφ).apply_symm_apply ⟨L s, hL ⟨s, rfl⟩⟩)
    rwa [LinearEquiv.ofInjective_apply] at h
  have hmat : ρ ∘ₗ φ = Matrix.toLin' (Matrix.of fun l j ↦ a j l) := by
    ext j l
    have hj : ρ (φ (Pi.single j 1)) = a j := hφ (by rw [← LinearMap.comp_apply, hφρ, hLa])
    simp [hj]
  rw [← hφρ, LinearMap.trace_comp_comm', hmat, Matrix.trace_toLin'_eq]
  simp [Matrix.trace]

/-- **The trace of an endomorphism that maps a basis into itself** is the number of basis vectors
it fixes: if `f (b i) = b (π i)` for every `i`, the trace of `f` is the number of fixed points of
`π`, cast into `R`. The map `π` need not be a permutation; when it is, this is the coordinate-free
form of `Matrix.trace_permutation`. -/
theorem trace_eq_natCard_of_apply_basis_eq {R M ι : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] [Finite ι] (b : Module.Basis ι R M) {f : M →ₗ[R] M} {π : ι → ι}
    (h : ∀ i, f (b i) = b (π i)) : trace R M f = Nat.card {i // π i = i} := by
  classical
  have := Fintype.ofFinite ι
  rw [trace_eq_matrix_trace R b, Matrix.trace]
  simp [LinearMap.toMatrix_apply, h, Finsupp.single_apply, Fintype.card_subtype]

open scoped Matrix in
/-- Endomorphisms whose matrices in some bases indexed by the same type are `A` and `-Aᵀ` have
opposite traces. This is the trace relation between a representation and its dual. -/
theorem trace_eq_neg_of_toMatrix_eq_neg_transpose {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) {f : M →ₗ[R] M} {g : N →ₗ[R] N}
    (h : LinearMap.toMatrix b' b' g = -(LinearMap.toMatrix b b f)ᵀ) :
    trace R N g = -trace R M f := by
  simp [trace_eq_matrix_trace R b, trace_eq_matrix_trace R b', h]

end LinearMap
