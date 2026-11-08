/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.SphereBundle.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact
import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.HomotopyGroup

/-!
# The exact homotopy sequence of `SO(n) → SO(1 + n) → Sⁿ`

For `n ≥ 1`, evaluation on the first coordinate vector, `A ↦ A e₀`, is a Serre fibration
`SO(1 + n) → Sⁿ` (`TauCeti.specialOrthogonalSphereMap_mem_serreFibrations`). Its fibre over `e₀`
is `SO(n)`, embedded as the block subgroup `diag(1, SO(n))`
(`TauCeti.specialOrthogonalSphereFiberHomeomorph`). This file reads off the exact homotopy
sequence of a Serre fibration for this bundle, with the fibre replaced by `SO(n)` and the fibre
inclusion by the block embedding `B ↦ diag(1, B)`:

`⋯ → π_{k+1}(SO(1 + n)) → π_{k+1}(Sⁿ) → π_k(SO(n)) → π_k(SO(1 + n)) → π_k(Sⁿ) → ⋯`,

all based at the identity and at `e₀`. The boundary map is
`TauCeti.specialOrthogonalSphereBoundary`, and the sequence is exact at its three kinds of terms.

The segment `π_n(SO(1 + n)) → π_n(Sⁿ) → π_{n-1}(SO(n))` decides which classes of `π_n(Sⁿ)` come
from `SO(1 + n)`. For `k ≥ 1`, if the boundary of a class `a ∈ π_{k+1}(Sⁿ)` has finite order,
for instance because `π_k(SO(n))` is a torsion group, then a positive power of `a` comes from
`SO(1 + n)`
(`TauCeti.exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap_of_isOfFinOrder`). If
`π_k(SO(n))` is trivial, every class of `π_{k+1}(Sⁿ)` comes from `SO(1 + n)`. Since
`π₂(SO(3)) = 0`, this is the case for `π₃(SO(4)) → π₃(S³)`
(`TauCeti.surjective_homotopyGroupMap_specialOrthogonalSphereMap_three`).

Homotopy groups are indexed as in `TauCeti.TopCat.fibrationBoundary`: `π_k` is modelled on the
cube `I^N` for a finite type `N` of cardinality `k`, and `π_{k+1}` on `I^(Option N)`.

## Main definitions

* `TauCeti.specialOrthogonalSphereBoundary`: the boundary map `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)`.
* `TauCeti.specialOrthogonalSphereBoundaryHom`: for `k ≥ 1`, the boundary map as a group
  homomorphism.

## Main results

* `TauCeti.mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff`: exactness at `π_{k+1}(Sⁿ)`.
* `TauCeti.mem_range_specialOrthogonalSphereBoundary_iff`: exactness at `π_k(SO(n))`.
* `TauCeti.mem_range_homotopyGroupMap_fromBlocksOne_iff`: exactness at `π_k(SO(1 + n))`.
* `TauCeti.specialOrthogonalSphereBoundary_apply`: the boundary map is the boundary map of the
  Serre fibration `A ↦ A e₀`, read in `SO(n)`.
* `TauCeti.specialOrthogonalSphereBoundary_mul`: for `k ≥ 1` the boundary is multiplicative.
* `TauCeti.surjective_homotopyGroupMap_specialOrthogonalSphereMap`: if `π_k(SO(n))` is trivial,
  every class of `π_{k+1}(Sⁿ)` comes from `SO(1 + n)`.
* `TauCeti.exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap_of_isOfFinOrder`: a
  positive power of a class whose boundary has finite order comes from `SO(1 + n)`.
* `TauCeti.surjective_homotopyGroupMap_specialOrthogonalSphereMap_three`: `π₃(SO(4)) → π₃(S³)` is
  surjective.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.41 and §4.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Proposition 6.34 and Lemma 6.35.
-/

public section

noncomputable section

open CategoryTheory Matrix Metric Set
open scoped Topology.Homotopy

namespace TauCeti

variable {n : ℕ}

/-! ### The boundary map -/

/-- The evaluation map `SO(1 + n) → Sⁿ`, `A ↦ A e₀`, as a morphism of `TopCat`, to which the exact
homotopy sequence of a Serre fibration applies. -/
private abbrev sphereHom (n : ℕ) :
    _root_.TopCat.of (specialOrthogonalGroup (Fin (1 + n)) ℝ) ⟶
      _root_.TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1) :=
  _root_.TopCat.ofHom ⟨specialOrthogonalSphereMap n, continuous_specialOrthogonalSphereMap n⟩

/-- The identity, as the base point of the fibre of `sphereHom n` over `e₀`. -/
private abbrev fiberOne (n : ℕ) : (sphereHom n).fiber (specialOrthogonalSphereMap n 1) :=
  ⟨1, rfl⟩

/-- The identification `π_N(F, 1) ≃ π_N(SO(n), 1)` of the homotopy groups of the fibre `F` of
`A ↦ A e₀` over `e₀` with those of `SO(n)`. -/
private def fiberEquiv (n : ℕ) (N : Type*) :
    HomotopyGroup N ((sphereHom n).fiber (specialOrthogonalSphereMap n 1)) (fiberOne n) ≃
      HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1 :=
  HomotopyGroup.homeomorphEquivOfEq (specialOrthogonalSphereFiberHomeomorph n).symm
    ((specialOrthogonalSphereFiberHomeomorph n).symm_apply_eq.2
      specialOrthogonalSphereFiberHomeomorph_one.symm)

/-- The inverse of `fiberEquiv` followed by the fibre inclusion is the map induced by the block
embedding `B ↦ diag(1, B)`. -/
private theorem map_fiberι_fiberEquiv_symm {N : Type*}
    (c : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1) :
    HomotopyGroup.map ((sphereHom n).fiberι _).hom
        (TopCat.Hom.fiberι_apply (sphereHom n) _ (fiberOne n)) ((fiberEquiv n N).symm c) =
      HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
        finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n)) c := by
  rw [fiberEquiv, HomotopyGroup.homeomorphEquivOfEq_symm_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr
    (ContinuousMap.ext fun B ↦ (TopCat.Hom.fiberι_apply (sphereHom n) _
      (specialOrthogonalSphereFiberHomeomorph n B)).trans
        (coe_specialOrthogonalSphereFiberHomeomorph_apply B)) _ _ c

variable (n) in
/-- The **boundary map** `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)` of the sphere bundle
`SO(n) → SO(1 + n) → Sⁿ`, for `n ≥ 1`, where `k` is the cardinality of `N`. It is the boundary
map of the Serre fibration `A ↦ A e₀` (`TauCeti.TopCat.fibrationBoundary`), read in `SO(n)`
through `TauCeti.specialOrthogonalSphereFiberHomeomorph`. -/
def specialOrthogonalSphereBoundary [NeZero n] (N : Type*) [Finite N] :
    HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
        (specialOrthogonalSphereMap n 1) →
      HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1 :=
  fiberEquiv n N ∘ TopCat.fibrationBoundary specialOrthogonalSphereMap_mem_serreFibrations
    (fiberOne n)

variable {N : Type*} [Finite N]

/-- The boundary map of the sphere bundle is the boundary map of the Serre fibration `A ↦ A e₀`,
read in `SO(n)` through the identification `TauCeti.specialOrthogonalSphereFiberHomeomorph` of
the fibre with `SO(n)`. -/
theorem specialOrthogonalSphereBoundary_apply [NeZero n]
    (a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) :
    specialOrthogonalSphereBoundary n N a =
      HomotopyGroup.homeomorphEquivOfEq (specialOrthogonalSphereFiberHomeomorph n).symm
        ((specialOrthogonalSphereFiberHomeomorph n).symm_apply_eq.2
          specialOrthogonalSphereFiberHomeomorph_one.symm)
        (TopCat.fibrationBoundary specialOrthogonalSphereMap_mem_serreFibrations ⟨1, rfl⟩ a) :=
  (rfl)

omit [Finite N] in
/-- `fiberEquiv` preserves the class of the constant generalized loop. -/
private theorem fiberEquiv_mk_const :
    fiberEquiv n N ⟦GenLoop.const⟧ =
      (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1) :=
  congrArg _ (GenLoop.map_const _ _)

/-- The boundary map of the sphere bundle sends the class of the constant loop to the class of
the constant loop. -/
@[simp]
theorem specialOrthogonalSphereBoundary_const [NeZero n] :
    specialOrthogonalSphereBoundary n N
        (⟦GenLoop.const⟧ : HomotopyGroup (Option N)
          (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1) (specialOrthogonalSphereMap n 1)) =
      ⟦GenLoop.const⟧ :=
  (congrArg (fiberEquiv n N) (TopCat.fibrationBoundary_const _)).trans fiberEquiv_mk_const

/-- For `k ≥ 1`, the boundary map `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)` of the sphere bundle is
multiplicative. -/
theorem specialOrthogonalSphereBoundary_mul [NeZero n] [DecidableEq N] [Nonempty N]
    (a a' : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) :
    specialOrthogonalSphereBoundary n N (a * a') =
      specialOrthogonalSphereBoundary n N a * specialOrthogonalSphereBoundary n N a' := by
  -- The group structures on the homotopy groups of `TopCat.of X` and of `X` agree only after
  -- unfolding `TopCat.of`, which `rw` does not do; checking it by `exact` times out, so the
  -- multiplicativity of the boundary is applied with `erw`.
  rw [specialOrthogonalSphereBoundary_apply, specialOrthogonalSphereBoundary_apply,
    specialOrthogonalSphereBoundary_apply]
  erw [TopCat.fibrationBoundary_mul]
  exact HomotopyGroup.map_mul _ _ _ _

variable (n N) in
/-- For `k ≥ 1`, the boundary map `π_{k+1}(Sⁿ, e₀) → π_k(SO(n), 1)` of the sphere bundle as a group
homomorphism. -/
def specialOrthogonalSphereBoundaryHom [NeZero n] [DecidableEq N] [Nonempty N] :
    HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
        (specialOrthogonalSphereMap n 1) →*
      HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1 :=
  MonoidHom.mk' (specialOrthogonalSphereBoundary n N) specialOrthogonalSphereBoundary_mul

@[simp]
theorem coe_specialOrthogonalSphereBoundaryHom [NeZero n] [DecidableEq N] [Nonempty N] :
    ⇑(specialOrthogonalSphereBoundaryHom n N) = specialOrthogonalSphereBoundary n N :=
  (rfl)

/-- For `k ≥ 1`, the boundary map of the sphere bundle sends the identity to the identity. -/
@[simp]
theorem specialOrthogonalSphereBoundary_one [NeZero n] [DecidableEq N] [Nonempty N] :
    specialOrthogonalSphereBoundary n N 1 = 1 :=
  map_one (specialOrthogonalSphereBoundaryHom n N)

/-- For `k ≥ 1`, the boundary map of the sphere bundle commutes with powers. -/
@[simp]
theorem specialOrthogonalSphereBoundary_pow [NeZero n] [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) (k : ℕ) :
    specialOrthogonalSphereBoundary n N (a ^ k) = specialOrthogonalSphereBoundary n N a ^ k :=
  map_pow (specialOrthogonalSphereBoundaryHom n N) a k

/-- For `k ≥ 1`, the boundary map of the sphere bundle commutes with inverses. -/
@[simp]
theorem specialOrthogonalSphereBoundary_inv [NeZero n] [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)) :
    specialOrthogonalSphereBoundary n N a⁻¹ = (specialOrthogonalSphereBoundary n N a)⁻¹ :=
  map_inv (specialOrthogonalSphereBoundaryHom n N) a

/-! ### Exactness -/

/-- **Exactness at `π_{k+1}(Sⁿ)`.** A class of `π_{k+1}(Sⁿ, e₀)` comes from `SO(1 + n)` exactly
when its boundary in `π_k(SO(n))` is trivial. -/
theorem mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff [NeZero n]
    {a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)} :
    a ∈ range (HomotopyGroup.map
        ⟨specialOrthogonalSphereMap n, continuous_specialOrthogonalSphereMap n⟩ rfl) ↔
      specialOrthogonalSphereBoundary n N a =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1) :=
  (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq _).trans
    ((fiberEquiv n N).injective.eq_iff' fiberEquiv_mk_const).symm

/-- **Exactness at `π_k(SO(n))`.** A class of `π_k(SO(n), 1)` is a boundary exactly when it
becomes trivial in `SO(1 + n)` under the block embedding `B ↦ diag(1, B)`. -/
theorem mem_range_specialOrthogonalSphereBoundary_iff [NeZero n]
    {c : HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1} :
    c ∈ range (specialOrthogonalSphereBoundary n N) ↔
      HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
          finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
          (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n)) c =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin (1 + n)) ℝ) 1) := by
  rw [specialOrthogonalSphereBoundary, range_comp, mem_image_equiv, ← map_fiberι_fiberEquiv_symm]
  exact TopCat.mem_range_fibrationBoundary_iff _

/-- **Exactness at `π_k(SO(1 + n))`.** A class of `π_k(SO(1 + n), 1)` comes from `SO(n)` under the
block embedding `B ↦ diag(1, B)` exactly when it becomes trivial in `π_k(Sⁿ, e₀)`. -/
theorem mem_range_homotopyGroupMap_fromBlocksOne_iff [NeZero n]
    {d : HomotopyGroup N (specialOrthogonalGroup (Fin (1 + n)) ℝ) 1} :
    d ∈ range (HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
        finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))) ↔
      HomotopyGroup.map ⟨specialOrthogonalSphereMap n, continuous_specialOrthogonalSphereMap n⟩
        rfl d =
        (⟦GenLoop.const⟧ : HomotopyGroup N (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
          (specialOrthogonalSphereMap n 1)) := by
  have h : range (HomotopyGroup.map (N := N) ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n,
      finiteOrthonormalFrame.continuous_fromBlocksOne n⟩
      (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ 1 n))) =
      range (HomotopyGroup.map ((sphereHom n).fiberι _).hom
        (TopCat.Hom.fiberι_apply (sphereHom n) _ (fiberOne n))) := by
    rw [← (fiberEquiv n N).symm.surjective.range_comp]
    exact congrArg range (funext fun c ↦ (map_fiberι_fiberEquiv_symm c).symm)
  rw [h]
  exact TopCat.mem_range_homotopyGroupMap_fiberι_iff specialOrthogonalSphereMap_mem_serreFibrations

/-! ### Classes of `SO(1 + n)` over the sphere -/

/-- **A positive power of a class lifts to `SO(1 + n)` when its boundary has finite order.** For
`k ≥ 1`, if the boundary of `a ∈ π_{k+1}(Sⁿ, e₀)` in `π_k(SO(n))` has finite order, then some
positive power of `a` comes from `π_{k+1}(SO(1 + n), 1)`. When `π_k(SO(n))` is a torsion group this
applies to every `a`. -/
theorem exists_pow_mem_range_homotopyGroupMap_specialOrthogonalSphereMap_of_isOfFinOrder
    [NeZero n]
    [DecidableEq N] [Nonempty N]
    {a : HomotopyGroup (Option N) (sphere (0 : EuclideanSpace ℝ (Fin (1 + n))) 1)
      (specialOrthogonalSphereMap n 1)}
    (ha : IsOfFinOrder (specialOrthogonalSphereBoundary n N a)) :
    ∃ k, 0 < k ∧ a ^ k ∈ range (HomotopyGroup.map
      ⟨specialOrthogonalSphereMap n, continuous_specialOrthogonalSphereMap n⟩ rfl) := by
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  refine ⟨k, hk, mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff.2 ?_⟩
  rw [specialOrthogonalSphereBoundary_pow, hak, HomotopyGroup.mk_const_eq_one]

/-- If `π_k(SO(n))` is trivial, then every class of `π_{k+1}(Sⁿ, e₀)` comes from
`π_{k+1}(SO(1 + n), 1)`. -/
theorem surjective_homotopyGroupMap_specialOrthogonalSphereMap [NeZero n]
    [Subsingleton (HomotopyGroup N (specialOrthogonalGroup (Fin n) ℝ) 1)] :
    Function.Surjective (HomotopyGroup.map (N := Option N) (x := 1)
      ⟨specialOrthogonalSphereMap n, continuous_specialOrthogonalSphereMap n⟩ rfl) := fun _ ↦
  mem_range_homotopyGroupMap_specialOrthogonalSphereMap_iff.2 (Subsingleton.elim _ _)

/-- **`π₃(SO(4)) → π₃(S³)` is surjective.** Since `π₂(SO(3)) = 0`, every class of `π₃(S³)` comes
from `SO(4)` under `A ↦ A e₀`. Here `π₃` is modelled on `I^(Option N)` for a type `N` with two
elements. -/
theorem surjective_homotopyGroupMap_specialOrthogonalSphereMap_three {N : Type*}
    (hN : Nat.card N = 2) :
    Function.Surjective (HomotopyGroup.map (N := Option N) (x := 1)
      ⟨specialOrthogonalSphereMap 3, continuous_specialOrthogonalSphereMap 3⟩ rfl) :=
  have : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have := subsingleton_homotopyGroup_specialOrthogonalGroup_three hN 1
  surjective_homotopyGroupMap_specialOrthogonalSphereMap

end TauCeti
