/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.HomotopyGroup
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup
public import TauCeti.Topology.Grassmannian.SphereBundle
public import TauCeti.Topology.Homotopy.SerreFibration.FiberEmbedding

/-!
# The homotopy exact sequence of `SO(n) → SO(1 + n) → Sⁿ`

For `n ≥ 1`, evaluation on the first coordinate vector, `SO(1 + n) → Sⁿ`, `A ↦ A e₀`
(`TauCeti.specialOrthogonalSphereMap`), is a Serre fibration whose fibre over `e₀` is the block
subgroup `diag(1, SO(n))`. This file records its exact homotopy sequence

`π_{k+1}(SO(1 + n)) → π_{k+1}(Sⁿ) → π_k(SO(n)) → π_k(SO(1 + n)) → π_k(Sⁿ)`,

at the identity and at `e₀`, with the fibre map the block embedding
`B ↦ diag(1, B)` (`Matrix.SpecialOrthogonalGroup.fromBlocksOne`) and the boundary map
`TauCeti.specialOrthogonalSphereBoundary`. Here `k` is the cardinality of a finite index type `N`,
and `π_{k+1}` is modelled on the cube `I^(Option N)`.

Three consequences are drawn.

* **Torsion boundary.** If `π_k(SO(n))` is a torsion group, `k ≥ 1`, then every class of
  `π_{k+1}(Sⁿ)` has a positive power coming from `π_{k+1}(SO(1 + n))`
  (`TauCeti.exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap`). With `k = n - 1`
  and `n` odd, this is the step of the first proof of Barraud–Damian–Humilière–Oancea,
  Proposition 6.34, that produces a class of `π_n(SO(n + 1))` mapping to a positive power of any
  given class of `π_n(Sⁿ)`, such as the class of the identity. For `n = 3`, `π₂(SO(3)) = 0` makes
  `π₃(SO(4)) → π₃(S³)` surjective
  (`TauCeti.surjective_homotopyGroupMap_specialOrthogonalSphereMap_three`).
* **Stabilization.** Since `Sⁿ` is `(n - 1)`-connected, the block embedding induces a surjection
  `π_k(SO(n)) → π_k(SO(1 + n))` for `k < n`
  (`TauCeti.surjective_homotopyGroupMap_fromBlocksOne`) and an injection for `1 ≤ k` and
  `k + 1 < n` (`TauCeti.injective_homotopyGroupMap_fromBlocksOne`).

## Main definitions

* `TauCeti.specialOrthogonalSphereBoundary`: the boundary map `π_{k+1}(Sⁿ) → π_k(SO(n))`.
* `TauCeti.specialOrthogonalSphereBoundaryHom`: the same map as a group homomorphism, `k ≥ 1`.

## Main results

* `TauCeti.mem_range_specialOrthogonalSphereBoundary_iff`,
  `TauCeti.mem_range_homotopyGroupMap_fromBlocksOne_iff`,
  `TauCeti.mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff`: exactness at `π_k(SO(n))`,
  `π_k(SO(1 + n))` and `π_{k+1}(Sⁿ)`.
* `TauCeti.exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap`: torsion of
  `π_k(SO(n))` makes the image of `π_{k+1}(SO(1 + n)) → π_{k+1}(Sⁿ)` of torsion index.
* `TauCeti.surjective_homotopyGroupMap_fromBlocksOne`,
  `TauCeti.injective_homotopyGroupMap_fromBlocksOne`: the stable range.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, §4.2 (the fibrations
  `SO(n) → SO(n + 1) → Sⁿ` and the stability of `π_k(SO(n))`).
* N. Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951, §25.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.34.
-/

public section

noncomputable section

open Matrix Metric Set Topology
open scoped Topology.Homotopy

namespace TauCeti

variable {n : ℕ} {N : Type*}

/-- The homotopy groups of `Sⁿ` vanish below dimension `n`. -/
private theorem subsingleton_homotopyGroup_sphere {M : Type*} [Finite M] (hM : Nat.card M < n) :
    Subsingleton (HomotopyGroup M (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) :=
  subsingleton_homotopyGroup_sphere_of_lt (by simp [add_comm]) hM _

variable [NeZero n]

/-- The **boundary map** `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)` of the fibration
`SO(n) → SO(1 + n) → Sⁿ`, where `k` is the cardinality of `N`. -/
def specialOrthogonalSphereBoundary [Finite N] :
    HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
        (specialOrthogonalSphereMap n 1) →
      HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1 :=
  TopCat.fibrationBoundaryOfIsEmbedding (specialOrthogonalSphereMap_mem_serreFibrations (n := n))
    (j := ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩)
    (finiteOrthonormalFrame.isEmbedding_fromBlocksOne 1 n)
    range_fromBlocksOne_eq_preimage_specialOrthogonalSphereMap (e := ⟨1, rfl⟩)
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))

/-- **Exactness at `π_k(SO(n))`.** A class of `SO(n)` is a boundary exactly when its image in
`SO(1 + n)` is trivial. -/
theorem mem_range_specialOrthogonalSphereBoundary_iff [Finite N]
    {a : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1} :
    a ∈ range (specialOrthogonalSphereBoundary (n := n)) ↔
      HomotopyGroup.map ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
          (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n)) a =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin (1 + n)) ℝ) 1) :=
  TopCat.mem_range_fibrationBoundaryOfIsEmbedding_iff _ _ _ _

/-- **Exactness at `π_k(SO(1 + n))`.** A class of `SO(1 + n)` comes from `SO(n)` exactly when its
image in `Sⁿ` is trivial. -/
theorem mem_range_homotopyGroupMap_fromBlocksOne_iff [Finite N]
    {a : HomotopyGroup N (specialOrthogonalGroup (Fin (1 + n)) ℝ) 1} :
    a ∈ range (HomotopyGroup.map ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))) ↔
      HomotopyGroup.map ⟨_, continuous_specialOrthogonalSphereMap n⟩ rfl a =
        (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
          (specialOrthogonalSphereMap n 1)) :=
  TopCat.mem_range_homotopyGroupMap_iff_of_isEmbedding
    specialOrthogonalSphereMap_mem_serreFibrations
    (finiteOrthonormalFrame.isEmbedding_fromBlocksOne 1 n)
    range_fromBlocksOne_eq_preimage_specialOrthogonalSphereMap (e := ⟨1, rfl⟩) _

/-- **Exactness at `π_{k+1}(Sⁿ)`.** A class of `Sⁿ` comes from `SO(1 + n)` exactly when its
boundary in `SO(n)` is trivial. -/
theorem mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff [Finite N]
    {a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)} :
    a ∈ range (HomotopyGroup.map ⟨_, continuous_specialOrthogonalSphereMap n⟩ rfl) ↔
      specialOrthogonalSphereBoundary a =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1) :=
  TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundaryOfIsEmbedding_eq
    specialOrthogonalSphereMap_mem_serreFibrations
    (j := ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩)
    (finiteOrthonormalFrame.isEmbedding_fromBlocksOne 1 n)
    range_fromBlocksOne_eq_preimage_specialOrthogonalSphereMap (e := ⟨1, rfl⟩)
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))

/-- For `k ≥ 1`, the boundary map `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)` as a group homomorphism. -/
def specialOrthogonalSphereBoundaryHom [DecidableEq N] [Finite N] [Nonempty N] :
    HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
        (specialOrthogonalSphereMap n 1) →*
      HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1 :=
  TopCat.fibrationBoundaryOfIsEmbeddingHom specialOrthogonalSphereMap_mem_serreFibrations
    (j := ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩)
    (finiteOrthonormalFrame.isEmbedding_fromBlocksOne 1 n)
    range_fromBlocksOne_eq_preimage_specialOrthogonalSphereMap (e := ⟨1, rfl⟩)
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))

@[simp]
theorem coe_specialOrthogonalSphereBoundaryHom [DecidableEq N] [Finite N] [Nonempty N] :
    ⇑(specialOrthogonalSphereBoundaryHom (n := n) (N := N)) = specialOrthogonalSphereBoundary :=
  TopCat.coe_fibrationBoundaryOfIsEmbeddingHom specialOrthogonalSphereMap_mem_serreFibrations
    (j := ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩)
    (finiteOrthonormalFrame.isEmbedding_fromBlocksOne 1 n)
    range_fromBlocksOne_eq_preimage_specialOrthogonalSphereMap (e := ⟨1, rfl⟩)
    (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))

/-- If `π_k(SO(n))` is trivial, then `π_{k+1}(SO(1 + n)) → π_{k+1}(Sⁿ)` is surjective. -/
theorem surjective_homotopyGroupMap_specialOrthogonalSphereMap [Finite N]
    [Subsingleton (HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1)] :
    Function.Surjective (HomotopyGroup.map (N := Option N) (x := 1)
      ⟨_, continuous_specialOrthogonalSphereMap n⟩ rfl) := fun _ ↦
  mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff.2 (Subsingleton.elim _ _)

/-- **Torsion boundary.** If `π_k(SO(n))`, `k ≥ 1`, is a torsion group, then every class of
`π_{k+1}(Sⁿ)` has a positive power in the image of `π_{k+1}(SO(1 + n))`. -/
theorem exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap [DecidableEq N]
    [Finite N] [Nonempty N]
    (h : IsMulTorsion (HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1))
    (a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) :
    ∃ ℓ, 0 < ℓ ∧ a ^ ℓ ∈ range (HomotopyGroup.map ⟨_, continuous_specialOrthogonalSphereMap n⟩
      (rfl : specialOrthogonalSphereMap n 1 = _)) := by
  obtain ⟨ℓ, hℓ, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 (h (specialOrthogonalSphereBoundary a))
  refine ⟨ℓ, hℓ, mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff.2 ?_⟩
  rw [HomotopyGroup.mk_const_eq_one, ← coe_specialOrthogonalSphereBoundaryHom, map_pow,
    coe_specialOrthogonalSphereBoundaryHom, hpow]

/-- `π₃(SO(4)) → π₃(S³)` is surjective, since `π₂(SO(3)) = 0`. -/
theorem surjective_homotopyGroupMap_specialOrthogonalSphereMap_three [Finite N]
    (hN : Nat.card N = 2) :
    Function.Surjective (HomotopyGroup.map (N := Option N) (x := 1)
      ⟨_, continuous_specialOrthogonalSphereMap 3⟩ rfl) :=
  have := subsingleton_homotopyGroup_specialOrthogonalGroup_three hN 1
  surjective_homotopyGroupMap_specialOrthogonalSphereMap

/-! ### The stable range -/

/-- **Stabilization, surjectivity.** For `k < n`, the block embedding `SO(n) → SO(1 + n)` induces
a surjection `π_k(SO(n)) → π_k(SO(1 + n))`. -/
theorem surjective_homotopyGroupMap_fromBlocksOne [Finite N] (hN : Nat.card N < n) :
    Function.Surjective (HomotopyGroup.map (N := N) ⟨_,
      finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))) := fun _ ↦
  have := subsingleton_homotopyGroup_sphere hN
  mem_range_homotopyGroupMap_fromBlocksOne_iff.2 (Subsingleton.elim _ _)

/-- **Stabilization, injectivity.** For `1 ≤ k` and `k + 1 < n`, the block embedding
`SO(n) → SO(1 + n)` induces an injection `π_k(SO(n)) → π_k(SO(1 + n))`. -/
theorem injective_homotopyGroupMap_fromBlocksOne [Finite N] [Nonempty N]
    (hN : Nat.card N + 1 < n) :
    Function.Injective (HomotopyGroup.map (N := N) ⟨_,
      finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))) := by
  classical
  have := subsingleton_homotopyGroup_sphere (M := Option N)
    (by simpa [Nat.card_eq_fintype_card] using hN)
  refine (injective_iff_map_eq_one (HomotopyGroup.mapHom (N := N)
    ⟨_, finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
      (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n)))).2 fun a ha ↦ ?_
  rw [HomotopyGroup.mapHom_apply, ← HomotopyGroup.mk_const_eq_one,
    ← mem_range_specialOrthogonalSphereBoundary_iff] at ha
  obtain ⟨c, rfl⟩ := ha
  rw [Subsingleton.elim c 1, ← coe_specialOrthogonalSphereBoundaryHom, map_one]

end TauCeti
