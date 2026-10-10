/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.Chains

/-!
# Normalized cubical chains

The **degenerate chains** `D_n(X; R)` are the span of the degenerate singular `n`-cubes inside the
unnormalized cubical chains.  They form a subcomplex: on a cube `c` degenerate at the coordinate
`i`, the two `i`-terms of `∂ c` cancel, because the two `i`-faces of `c` coincide
(`face_eq_of_isDegenerateAt`), and every other term is a degenerate cube
(`isDegenerate_face_of_ne`).  The **normalized cubical chains** `C^□_n(X; R)` are the quotient
`CubicalChain X R n ⧸ D_n`, with the induced boundary, and they are the cubical singular chains of
Massey, *Singular Homology Theory*, Chapter II.

Degenerate cubes are preserved by composition with a continuous map, so the push-forward descends
to the quotient and the normalized chains are functorial.

## Main definitions

* `TauCeti.CubicalChain.degenerate X R n`: the submodule spanned by the degenerate `n`-cubes.
* `TauCeti.NormalizedCubicalChain X R n`: the normalized cubical `n`-chains.
* `TauCeti.NormalizedCubicalChain.boundary X R n`: the induced boundary.
* `TauCeti.NormalizedCubicalChain.map R f n`: the push-forward along a continuous map.
* `TauCeti.NormalizedCubicalChain.cast R h`: reindexing along an equality of dimensions.

## Main results

* `TauCeti.CubicalChain.degenerate_def`, `TauCeti.CubicalChain.degenerate_induction`: the
  degenerate chains as a span, and induction on them.
* `TauCeti.CubicalChain.boundary_mem_degenerate`: the boundary of a degenerate chain is degenerate.
* `TauCeti.CubicalChain.degenerate_zero`: there are no degenerate `0`-chains.
* `TauCeti.NormalizedCubicalChain.boundary_boundary`: `∂ ∘ ∂ = 0` on normalized chains.
* `TauCeti.NormalizedCubicalChain.map_boundary`: the boundary is natural.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace CubicalChain

open SingularCube

section Semiring

variable (R : Type*) [Semiring R]

variable (X) in
/-- The **degenerate `n`-chains**: the span of the degenerate singular `n`-cubes. -/
def degenerate (n : ℕ) : Submodule R (CubicalChain X R n) :=
  Submodule.span R {f | ∃ c : SingularCube X n, IsDegenerate c ∧ f = single c 1}

variable (X) in
/-- The degenerate `n`-chains are the span of the chains of the degenerate `n`-cubes. -/
theorem degenerate_def (n : ℕ) : degenerate X R n =
    Submodule.span R {f | ∃ c : SingularCube X n, IsDegenerate c ∧ f = single c 1} :=
  (rfl)

/-- **Induction on degenerate chains**: a property of chains which holds for `0` and for the chain
of each degenerate cube, and is stable under sums and scalar multiples, holds for every degenerate
chain. -/
theorem degenerate_induction {n : ℕ} {P : CubicalChain X R n → Prop} (zero : P 0)
    (hsingle : ∀ c : SingularCube X n, IsDegenerate c → P (single c 1))
    (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (r : R) f, P f → P (r • f))
    {g : CubicalChain X R n} (hg : g ∈ degenerate X R n) : P g := by
  rw [degenerate_def] at hg
  induction hg using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    exact hsingle c hc
  | zero => exact zero
  | add f g _ _ hf hg => exact hadd f g hf hg
  | smul r f _ hf => exact hsmul r f hf

theorem single_mem_degenerate {n : ℕ} {c : SingularCube X n} (hc : IsDegenerate c) (a : R) :
    single c a ∈ degenerate X R n := by
  rw [← smul_single_one]
  exact Submodule.smul_mem _ a (Submodule.subset_span ⟨c, hc, rfl⟩)

/-- There are no degenerate `0`-chains: a `0`-cube is a point. -/
@[simp]
theorem degenerate_zero : degenerate X R 0 = ⊥ := by
  rw [degenerate, Submodule.span_eq_bot]
  rintro f ⟨c, hc, rfl⟩
  exact (not_isDegenerate_zero c hc).elim

/-- The push-forward of a degenerate chain is degenerate. -/
theorem map_mem_degenerate (f : C(X, Y)) {n : ℕ} {g : CubicalChain X R n}
    (hg : g ∈ degenerate X R n) : map R f n g ∈ degenerate Y R n := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc, rfl⟩ := hg
    rw [map_single]
    exact single_mem_degenerate R (hc.comp f) 1
  | zero => simp
  | add g h _ _ hg hh => rw [map_add]; exact Submodule.add_mem _ hg hh
  | smul a g _ hg => rw [map_smul]; exact Submodule.smul_mem _ a hg

private theorem degenerate_le_comap_map (f : C(X, Y)) (n : ℕ) :
    degenerate X R n ≤ (degenerate Y R n).comap (map R f n) :=
  fun _ hg ↦ map_mem_degenerate R f hg

/-- Reindexing preserves degenerate chains. -/
theorem cast_mem_degenerate {n m : ℕ} (h : n = m) {f : CubicalChain X R n}
    (hf : f ∈ degenerate X R n) : cast R h f ∈ degenerate X R m := by
  subst h
  simpa using hf

end Semiring

section Ring

variable (R : Type*) [Ring R]

/-- The boundary of a degenerate cube is a degenerate chain: the two terms of the degenerate
coordinate cancel, and every other face is degenerate. -/
theorem boundary_single_mem_degenerate {n : ℕ} {c : SingularCube X (n + 1)}
    (hc : IsDegenerate c) : boundary X R n (single c 1) ∈ degenerate X R n := by
  obtain ⟨i, hi⟩ := isDegenerate_iff.1 hc
  rw [boundary_single]
  refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ?_
  by_cases hij : i = j
  · subst hij
    rw [face_eq_of_isDegenerateAt hi 0 1, sub_self]
    exact Submodule.zero_mem _
  · exact Submodule.sub_mem _ (single_mem_degenerate R (isDegenerate_face_of_ne hi hij 0) 1)
      (single_mem_degenerate R (isDegenerate_face_of_ne hi hij 1) 1)

/-- The degenerate chains form a subcomplex. -/
theorem boundary_mem_degenerate {n : ℕ} {f : CubicalChain X R (n + 1)}
    (hf : f ∈ degenerate X R (n + 1)) : boundary X R n f ∈ degenerate X R n := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    exact boundary_single_mem_degenerate R hc
  | zero => simp
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ a hf

private theorem degenerate_le_comap_boundary (n : ℕ) :
    degenerate X R (n + 1) ≤ (degenerate X R n).comap (boundary X R n) :=
  fun _ hf ↦ boundary_mem_degenerate R hf

end Ring

end CubicalChain

/-- The **normalized cubical `n`-chains** of `X` with coefficients in `R`: the unnormalized chains
modulo the degenerate ones. -/
abbrev NormalizedCubicalChain (X : Type*) [TopologicalSpace X] (R : Type*) [Ring R]
    (n : ℕ) : Type _ :=
  CubicalChain X R n ⧸ CubicalChain.degenerate X R n

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [Ring R]

variable (X) in
/-- The class of a singular cube in the normalized chains. -/
def ofCube {n : ℕ} (c : SingularCube X n) : NormalizedCubicalChain X R n :=
  Submodule.Quotient.mk (single c 1)

theorem ofCube_def {n : ℕ} (c : SingularCube X n) :
    ofCube X R c = Submodule.Quotient.mk (single c 1) := by
  rw [ofCube]

@[simp]
theorem ofCube_eq_zero {n : ℕ} {c : SingularCube X n} (hc : SingularCube.IsDegenerate c) :
    ofCube X R c = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 (single_mem_degenerate R hc 1)

variable (X) in
/-- The boundary of normalized cubical chains, induced by the boundary of the unnormalized ones. -/
def boundary (n : ℕ) : NormalizedCubicalChain X R (n + 1) →ₗ[R] NormalizedCubicalChain X R n :=
  Submodule.mapQ _ _ (CubicalChain.boundary X R n) (degenerate_le_comap_boundary R n)

@[simp]
theorem boundary_mk {n : ℕ} (f : CubicalChain X R (n + 1)) :
    boundary X R n (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (CubicalChain.boundary X R n f) :=
  Submodule.mapQ_apply _ _ _ f

/-- The boundary of a boundary vanishes. -/
theorem boundary_boundary (n : ℕ) : boundary X R n ∘ₗ boundary X R (n + 1) = 0 := by
  rw [boundary, boundary, ← Submodule.mapQ_comp]
  simp only [CubicalChain.boundary_boundary, Submodule.mapQ_zero]

/-- The boundary of the class of a cube is the signed sum of the classes of its faces. -/
@[simp]
theorem boundary_ofCube {n : ℕ} (c : SingularCube X (n + 1)) :
    boundary X R n (ofCube X R c) =
      ∑ i : Fin (n + 1), (-1 : R) ^ (i : ℕ) •
        (ofCube X R (SingularCube.face i 0 c) - ofCube X R (SingularCube.face i 1 c)) := by
  rw [ofCube_def, boundary_mk, CubicalChain.boundary_single_one, CubicalChain.boundaryCube_def]
  simp only [ofCube_def, ← Submodule.mkQ_apply, map_sum, map_smul, map_sub]

/-- Normalized cubical chains pushed forward along a continuous map. -/
def map (f : C(X, Y)) (n : ℕ) : NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain Y R n :=
  Submodule.mapQ _ _ (CubicalChain.map R f n) (degenerate_le_comap_map R f n)

@[simp]
theorem map_mk (f : C(X, Y)) {n : ℕ} (g : CubicalChain X R n) :
    map R f n (Submodule.Quotient.mk g) = Submodule.Quotient.mk (CubicalChain.map R f n g) :=
  Submodule.mapQ_apply _ _ _ g

/-- The push-forward of the class of a cube is the class of the composed cube. -/
@[simp]
theorem map_ofCube (f : C(X, Y)) {n : ℕ} (c : SingularCube X n) :
    map R f n (ofCube X R c) = ofCube Y R (f.comp c) := by
  rw [ofCube_def, ofCube_def, map_mk, CubicalChain.map_single]

@[simp]
theorem map_id (n : ℕ) : map R (ContinuousMap.id X) n = LinearMap.id := by
  unfold map
  simp only [CubicalChain.map_id, Submodule.mapQ_id]

theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (n : ℕ) :
    map R (g.comp f) n = map R g n ∘ₗ map R f n := by
  unfold map
  simp only [CubicalChain.map_comp]
  exact Submodule.mapQ_comp _ _ _ _ _ (degenerate_le_comap_map R f n)
    (degenerate_le_comap_map R g n)

/-- The boundary is natural. -/
theorem map_boundary (f : C(X, Y)) (n : ℕ) :
    map R f n ∘ₗ boundary X R n = boundary Y R n ∘ₗ map R f (n + 1) := by
  unfold map boundary
  rw [← Submodule.mapQ_comp, ← Submodule.mapQ_comp]
  simp only [CubicalChain.map_boundary]

/-- Reindex normalized chains along an equality of dimensions. -/
def cast {n m : ℕ} (h : n = m) : NormalizedCubicalChain X R n →ₗ[R] NormalizedCubicalChain X R m :=
  Submodule.mapQ _ _ (CubicalChain.cast R h) fun _ hf ↦ CubicalChain.cast_mem_degenerate R h hf

@[simp]
theorem cast_mk {n m : ℕ} (h : n = m) (f : CubicalChain X R n) :
    cast R h (Submodule.Quotient.mk f) = Submodule.Quotient.mk (CubicalChain.cast R h f) :=
  Submodule.mapQ_apply _ _ _ f

/-- Reindexing along successive dimension equalities is reindexing along their composite. -/
@[simp]
theorem cast_cast {n m k : ℕ} (h : n = m) (h' : m = k) (c : NormalizedCubicalChain X R n) :
    cast R h' (cast R h c) = cast R (h.trans h') c := by
  induction c using Submodule.Quotient.induction_on with
  | H c => simp

/-- Reindexing along `rfl` is the identity. -/
@[simp]
theorem cast_rfl {n : ℕ} (c : NormalizedCubicalChain X R n) : cast R rfl c = c := by
  induction c using Submodule.Quotient.induction_on with
  | H c => simp

/-- Reindexing commutes with the push-forward. -/
theorem map_cast (f : C(X, Y)) {n m : ℕ} (h : n = m) (c : NormalizedCubicalChain X R n) :
    map R f m (cast R h c) = cast R h (map R f n c) := by
  subst h
  simp

/-- Reindexing commutes with the boundary. -/
theorem boundary_cast {n m : ℕ} (h : n = m) (c : NormalizedCubicalChain X R (n + 1)) :
    boundary X R m (cast R (congrArg Nat.succ h) c) = cast R h (boundary X R n c) := by
  subst h
  simp

/-- Reindexing is injective. -/
theorem cast_injective {n m : ℕ} (h : n = m) :
    Function.Injective (cast (X := X) R h) := fun a b hab ↦ by
  simpa using congrArg (cast R h.symm) hab

end NormalizedCubicalChain

end TauCeti

end
