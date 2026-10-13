/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.HomologyZero

/-!
# The degree-zero projection of the loop chain algebra

For a pointed space `(B, b)` the algebra `C_*(Ω_b B; R)` of normalized cubical chains on the Moore
loop space maps to the group algebra `R[π₁(B, b)]` by the zeroth-homology projection
`loopZeroChainToGroupAlgebra` in dimension zero and by zero in positive dimensions.  This is the
ring map through which `C_*(Ω_b B; R)` acts on the fiber of a classical local system.

## Main definitions

* `TauCeti.loopChainToGroupAlgebra`: the algebra map to the group algebra `R[π₁(B, b)]`.

## Main results

* `TauCeti.loopChainToGroupAlgebra_lof_zero`, `TauCeti.loopChainToGroupAlgebra_lof_succ`: the values
  on chains of a given dimension.
* `TauCeti.loopChainToGroupAlgebra_differential`: it kills boundaries.
* `TauCeti.loopChainToGroupAlgebra_eq_zero_of_mem`: it kills elements of nonzero cohomological
  degree.
* `TauCeti.loopChainToGroupAlgebra_loopChainMap`: naturality in based maps.
-/

public section

noncomputable section

namespace TauCeti

section DegreeZero

universe u

variable (B : Type u) [TopologicalSpace B] (b : B) (R : Type u) [CommRing R]

/-- The component of `loopChainToGroupAlgebra` in dimension `n`: the class map in dimension zero and
zero in positive dimensions. -/
private def loopChainToGroupAlgebraComponent :
    (n : ℕ) → NormalizedCubicalChain (MooreLoopSpace B b) R n →ₗ[R]
      MonoidAlgebra R (FundamentalGroup B b)
  | 0 => loopZeroChainToGroupAlgebra B b R
  | _ + 1 => 0

variable {B b R}

private theorem loopChainToGroupAlgebraComponent_zero :
    loopChainToGroupAlgebraComponent B b R 0 = loopZeroChainToGroupAlgebra B b R :=
  (rfl)

private theorem loopChainToGroupAlgebraComponent_eq_zero {n : ℕ} (h : n ≠ 0)
    (x : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainToGroupAlgebraComponent B b R n x = 0 := by
  cases n with
  | zero => exact absurd rfl h
  | succ n => rfl

variable (B b R)

/-- **The degree-zero ring map**: the algebra map from the chains on the Moore loop space to the
group ring of the fundamental group, which is `loopZeroChainToGroupAlgebra` on `0`-chains and zero
on chains of positive dimension. -/
def loopChainToGroupAlgebra : loopChainAlgebra B b R →ₐ[R] MonoidAlgebra R (FundamentalGroup B b) :=
  DirectSum.toAlgebra R _ (loopChainToGroupAlgebraComponent B b R)
    (by simp [loopChainToGroupAlgebraComponent])
    (fun {i j} x y ↦ by
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · subst hi hj
          simp [loopChainToGroupAlgebraComponent]
        · rw [loopChainToGroupAlgebraComponent_eq_zero (by omega),
            loopChainToGroupAlgebraComponent_eq_zero hj, mul_zero]
      · rw [loopChainToGroupAlgebraComponent_eq_zero (by omega),
          loopChainToGroupAlgebraComponent_eq_zero hi, zero_mul])

variable {B b R}

private theorem loopChainToGroupAlgebra_lof_component (n : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R n) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R n y) =
      loopChainToGroupAlgebraComponent B b R n y := by
  rw [loopChainToGroupAlgebra, DirectSum.toAlgebra_apply, cubicalChainLof, DirectSum.lof_eq_of]
  exact DirectSum.toSemiring_of _ _ _ n y

/-- The degree-zero ring map on a `0`-chain is the projection to the group algebra. -/
@[simp]
theorem loopChainToGroupAlgebra_lof_zero (y : NormalizedCubicalChain (MooreLoopSpace B b) R 0) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R 0 y) =
      loopZeroChainToGroupAlgebra B b R y :=
  loopChainToGroupAlgebra_lof_component 0 y

/-- The degree-zero ring map kills the chains of positive dimension. -/
@[simp]
theorem loopChainToGroupAlgebra_lof_succ (k : ℕ)
    (y : NormalizedCubicalChain (MooreLoopSpace B b) R (k + 1)) :
    loopChainToGroupAlgebra B b R (cubicalChainLof (MooreLoopSpace B b) R (k + 1) y) = 0 :=
  (loopChainToGroupAlgebra_lof_component (k + 1) y).trans
    (loopChainToGroupAlgebraComponent_eq_zero k.succ_ne_zero y)

/-- The degree-zero ring map kills boundaries. -/
@[simp]
theorem loopChainToGroupAlgebra_differential (a : loopChainAlgebra B b R) :
    loopChainToGroupAlgebra B b R (cubicalChainDifferential (MooreLoopSpace B b) R a) = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    cases n with
    | zero =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_zero, map_zero]
    | succ k =>
      rw [← DirectSum.lof_eq_of R, cubicalChainDifferential_lof_succ]
      cases k with
      | zero =>
        rw [loopChainToGroupAlgebra_lof_zero]
        exact loopZeroChainToGroupAlgebra_boundary y
      | succ k => simp
  | add x y hx hy => simp [hx, hy]

/-- The degree-zero ring map kills homogeneous elements of nonzero cohomological degree. -/
theorem loopChainToGroupAlgebra_eq_zero_of_mem {i : ℤ} (hi : i ≠ 0) {a : loopChainAlgebra B b R}
    (ha : a ∈ cubicalChainGrading (MooreLoopSpace B b) R i) :
    loopChainToGroupAlgebra B b R a = 0 := by
  rcases (mem_cubicalChainGrading_iff _ _).1 ha with rfl | ⟨n, y, hn, rfl⟩
  · exact map_zero _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact loopChainToGroupAlgebra_lof_succ k y

/-- **Naturality of the degree-zero ring map**: it intertwines `C_*(Ωf)` with the map of group
rings induced by `π₁(f)`. -/
@[simp]
theorem loopChainToGroupAlgebra_loopChainMap {B' : Type u} [TopologicalSpace B'] {b' : B'}
    (f : C(B, B')) (hf : f b = b') (a : loopChainAlgebra B b R) :
    loopChainToGroupAlgebra B' b' R (loopChainMap R f hf a) =
      MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf)
        (loopChainToGroupAlgebra B b R a) := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n y =>
    have h : loopChainToGroupAlgebraComponent B' b' R n
        (NormalizedCubicalChain.map R (MooreLoopSpace.map f hf : C(_, _)) n y) =
        MonoidAlgebra.mapDomainRingHom R (FundamentalGroup.mapOfEq f hf)
          (loopChainToGroupAlgebraComponent B b R n y) := by
      cases n with
      | zero =>
        rw [loopChainToGroupAlgebraComponent_zero, loopChainToGroupAlgebraComponent_zero]
        exact loopZeroChainToGroupAlgebra_map f hf y
      | succ n =>
        rw [loopChainToGroupAlgebraComponent_eq_zero n.succ_ne_zero,
          loopChainToGroupAlgebraComponent_eq_zero n.succ_ne_zero, map_zero]
    rw [← DirectSum.lof_eq_of R]
    exact ((congrArg _ (loopChainMap_lof R f hf n y)).trans
      (loopChainToGroupAlgebra_lof_component n _)).trans
      (h.trans (congrArg _ (loopChainToGroupAlgebra_lof_component n y)).symm)
  | add x y hx hy => simp only [map_add, hx, hy]

end DegreeZero

end TauCeti

end
