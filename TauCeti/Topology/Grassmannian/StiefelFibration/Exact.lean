/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.StiefelFibration.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# The exact homotopy sequence of `SO(m) → SO(r + m) → V_r(ℝ^(r + m))`

For `m ≥ 1`, the Stiefel map `SO(r + m) → V_r(ℝ^(r + m))`, `A ↦ (A e₀, …, A e_{r-1})`, is a Serre
fibration (`TauCeti.specialOrthogonalFrameMap_mem_serreFibrations`). Its fibre over the standard
frame `e` is `SO(m)`, embedded as the block subgroup `diag(1_r, SO(m))`
(`TauCeti.specialOrthogonalFrameFiberHomeomorph`). This file reads off the exact homotopy
sequence of a Serre fibration for this bundle, with the fibre replaced by `SO(m)` and the fibre
inclusion by the block embedding `B ↦ diag(1_r, B)`:

`⋯ → π_{k+1}(SO(r + m)) → π_{k+1}(V_r(ℝ^(r + m))) → π_k(SO(m)) → π_k(SO(r + m)) →
  π_k(V_r(ℝ^(r + m))) → ⋯`,

all based at the identity and at the standard frame. The boundary map is
`TauCeti.specialOrthogonalFrameBoundary`, and the sequence is exact at its three kinds of terms.

For `r = 2` and `m = n` this is the sequence of `SO(n) → SO(n + 2) → V₂(ℝ^(n + 2))`, whose segment
`π_n(SO(n + 2)) → π_n(V₂(ℝ^(n + 2))) → π_{n-1}(SO(n)) → π_{n-1}(SO(n + 2))` relates
`π_{n-1}(SO(n))` to the stable group `π_{n-1}(SO(n + 2))` and to the Stiefel term
`π_n(V₂(ℝ^(n + 2)))`. For `r = 1` the base is the unit sphere, and the sequence is also
`TauCeti.Topology.Grassmannian.SphereBundle.Exact`, stated there for the sphere itself.

Homotopy groups are indexed as in `TauCeti.TopCat.fibrationBoundary`: `π_k` is modelled on the
cube `I^N` for a finite type `N` of cardinality `k`, and `π_{k+1}` on `I^(Option N)`.

## Main definitions

* `TauCeti.specialOrthogonalFrameBoundary`: the boundary map
  `π_{k+1}(V_r(ℝ^(r + m)), e) → π_k(SO(m), 1)`.
* `TauCeti.specialOrthogonalFrameBoundaryHom`: for `k ≥ 1`, the boundary map as a group
  homomorphism.

## Main results

* `TauCeti.mem_range_homotopyGroupMap_specialOrthogonalFrameMap_iff`: exactness at
  `π_{k+1}(V_r(ℝ^(r + m)))`.
* `TauCeti.mem_range_specialOrthogonalFrameBoundary_iff`: exactness at `π_k(SO(m))`.
* `TauCeti.mem_range_homotopyGroupMap_fromBlocksOne_iff_specialOrthogonalFrameMap`: exactness at
  `π_k(SO(r + m))`.
* `TauCeti.specialOrthogonalFrameBoundary_apply`: the boundary map is the boundary map of the
  Serre fibration `A ↦ (A e₀, …, A e_{r-1})`, read in `SO(m)`.
* `TauCeti.specialOrthogonalFrameBoundary_mul`: for `k ≥ 1` the boundary is multiplicative.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.41 and §4.2.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 6.35.
-/

public section

noncomputable section

open CategoryTheory Matrix Set
open scoped Topology.Homotopy

namespace TauCeti

variable {r m : ℕ}

/-! ### The boundary map -/

/-- The frame map `SO(r + m) → V_r(ℝ^(r + m))` as a morphism of `TopCat`, to which the exact
homotopy sequence of a Serre fibration applies. -/
private abbrev frameHom (r m : ℕ) :
    _root_.TopCat.of (specialOrthogonalGroup (Fin (r + m)) ℝ) ⟶
      _root_.TopCat.of (finiteOrthonormalFrame ℝ r (r + m)) :=
  _root_.TopCat.ofHom ⟨specialOrthogonalFrameMap r m, continuous_specialOrthogonalFrameMap r m⟩

/-- The identity, as the base point of the fibre of `frameHom r m` over the standard frame. -/
private abbrev fiberOne (r m : ℕ) : (frameHom r m).fiber (specialOrthogonalFrameMap r m 1) :=
  ⟨1, rfl⟩

/-- The identification `π_N(F, 1) ≃ π_N(SO(m), 1)` of the homotopy groups of the fibre `F` of the
frame map over the standard frame with those of `SO(m)`. -/
private def fiberEquiv (r m : ℕ) (N : Type*) :
    HomotopyGroup N ((frameHom r m).fiber (specialOrthogonalFrameMap r m 1)) (fiberOne r m) ≃
      HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1 :=
  HomotopyGroup.homeomorphEquivOfEq (specialOrthogonalFrameFiberHomeomorph r m).symm
    ((specialOrthogonalFrameFiberHomeomorph r m).symm_apply_eq.2
      specialOrthogonalFrameFiberHomeomorph_one.symm)

/-- The inverse of `fiberEquiv` followed by the fibre inclusion is the map induced by the block
embedding `B ↦ diag(1_r, B)`. -/
private theorem map_fiberι_fiberEquiv_symm {N : Type*}
    (c : HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1) :
    HomotopyGroup.map ((frameHom r m).fiberι _).hom
        (TopCat.Hom.fiberι_apply (frameHom r m) _ (fiberOne r m)) ((fiberEquiv r m N).symm c) =
      HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ r m,
        finiteOrthonormalFrame.continuous_fromBlocksOne m⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ r m)) c := by
  rw [fiberEquiv, HomotopyGroup.homeomorphEquivOfEq_symm_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr
    (ContinuousMap.ext fun B ↦ (TopCat.Hom.fiberι_apply (frameHom r m) _
      (specialOrthogonalFrameFiberHomeomorph r m B)).trans
        (coe_specialOrthogonalFrameFiberHomeomorph_apply B)) _ _ c

variable (r m) in
/-- The **boundary map** `π_{k+1}(V_r(ℝ^(r + m)), e) → π_k(SO(m), 1)` of the Stiefel fibration
`SO(m) → SO(r + m) → V_r(ℝ^(r + m))`, for `m ≥ 1`, where `k` is the cardinality of `N` and `e` is
the standard frame. It is the boundary map of the Serre fibration `A ↦ (A e₀, …, A e_{r-1})`
(`TauCeti.TopCat.fibrationBoundary`), read in `SO(m)` through
`TauCeti.specialOrthogonalFrameFiberHomeomorph`. -/
def specialOrthogonalFrameBoundary [NeZero m] (N : Type*) [Finite N] :
    HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
        (specialOrthogonalFrameMap r m 1) →
      HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1 :=
  fiberEquiv r m N ∘ TopCat.fibrationBoundary specialOrthogonalFrameMap_mem_serreFibrations
    (fiberOne r m)

variable {N : Type*} [Finite N]

/-- The boundary map of the Stiefel fibration is the boundary map of the Serre fibration
`A ↦ (A e₀, …, A e_{r-1})`, read in `SO(m)` through the identification
`TauCeti.specialOrthogonalFrameFiberHomeomorph` of the fibre with `SO(m)`. -/
theorem specialOrthogonalFrameBoundary_apply [NeZero m]
    (a : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
      (specialOrthogonalFrameMap r m 1)) :
    specialOrthogonalFrameBoundary r m N a =
      HomotopyGroup.homeomorphEquivOfEq (specialOrthogonalFrameFiberHomeomorph r m).symm
        ((specialOrthogonalFrameFiberHomeomorph r m).symm_apply_eq.2
          specialOrthogonalFrameFiberHomeomorph_one.symm)
        (TopCat.fibrationBoundary specialOrthogonalFrameMap_mem_serreFibrations ⟨1, rfl⟩ a) :=
  (rfl)

omit [Finite N] in
/-- `fiberEquiv` preserves the class of the constant generalized loop. -/
private theorem fiberEquiv_mk_const :
    fiberEquiv r m N ⟦GenLoop.const⟧ =
      (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1) :=
  congrArg _ (GenLoop.map_const _ _)

/-- The boundary map of the Stiefel fibration sends the class of the constant loop to the class of
the constant loop. -/
@[simp]
theorem specialOrthogonalFrameBoundary_const [NeZero m] :
    specialOrthogonalFrameBoundary r m N
        (⟦GenLoop.const⟧ : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
          (specialOrthogonalFrameMap r m 1)) =
      ⟦GenLoop.const⟧ :=
  (congrArg (fiberEquiv r m N) (TopCat.fibrationBoundary_const _)).trans fiberEquiv_mk_const

/-- For `k ≥ 1`, the boundary map `π_{k+1}(V_r(ℝ^(r + m)), e) → π_k(SO(m), 1)` of the Stiefel
fibration is multiplicative. -/
theorem specialOrthogonalFrameBoundary_mul [NeZero m] [DecidableEq N] [Nonempty N]
    (a a' : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
      (specialOrthogonalFrameMap r m 1)) :
    specialOrthogonalFrameBoundary r m N (a * a') =
      specialOrthogonalFrameBoundary r m N a * specialOrthogonalFrameBoundary r m N a' := by
  -- The group structures on the homotopy groups of `TopCat.of X` and of `X` agree only after
  -- unfolding `TopCat.of`, which `rw` does not do; checking it by `exact` times out, so the
  -- multiplicativity of the boundary is applied with `erw`.
  rw [specialOrthogonalFrameBoundary_apply, specialOrthogonalFrameBoundary_apply,
    specialOrthogonalFrameBoundary_apply]
  erw [TopCat.fibrationBoundary_mul]
  exact HomotopyGroup.map_mul _ _ _ _

variable (r m N) in
/-- For `k ≥ 1`, the boundary map `π_{k+1}(V_r(ℝ^(r + m)), e) → π_k(SO(m), 1)` of the Stiefel
fibration as a group homomorphism. -/
def specialOrthogonalFrameBoundaryHom [NeZero m] [DecidableEq N] [Nonempty N] :
    HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
        (specialOrthogonalFrameMap r m 1) →*
      HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1 :=
  MonoidHom.mk' (specialOrthogonalFrameBoundary r m N) specialOrthogonalFrameBoundary_mul

@[simp]
theorem coe_specialOrthogonalFrameBoundaryHom [NeZero m] [DecidableEq N] [Nonempty N] :
    ⇑(specialOrthogonalFrameBoundaryHom r m N) = specialOrthogonalFrameBoundary r m N :=
  (rfl)

/-- For `k ≥ 1`, the boundary map of the Stiefel fibration sends the identity to the identity. -/
@[simp]
theorem specialOrthogonalFrameBoundary_one [NeZero m] [DecidableEq N] [Nonempty N] :
    specialOrthogonalFrameBoundary r m N 1 = 1 :=
  map_one (specialOrthogonalFrameBoundaryHom r m N)

/-- For `k ≥ 1`, the boundary map of the Stiefel fibration commutes with powers. -/
@[simp]
theorem specialOrthogonalFrameBoundary_pow [NeZero m] [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
      (specialOrthogonalFrameMap r m 1)) (k : ℕ) :
    specialOrthogonalFrameBoundary r m N (a ^ k) = specialOrthogonalFrameBoundary r m N a ^ k :=
  map_pow (specialOrthogonalFrameBoundaryHom r m N) a k

/-- For `k ≥ 1`, the boundary map of the Stiefel fibration commutes with inverses. -/
@[simp]
theorem specialOrthogonalFrameBoundary_inv [NeZero m] [DecidableEq N] [Nonempty N]
    (a : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
      (specialOrthogonalFrameMap r m 1)) :
    specialOrthogonalFrameBoundary r m N a⁻¹ = (specialOrthogonalFrameBoundary r m N a)⁻¹ :=
  map_inv (specialOrthogonalFrameBoundaryHom r m N) a

/-! ### Exactness -/

/-- **Exactness at `π_{k+1}(V_r(ℝ^(r + m)))`.** A class of `π_{k+1}(V_r(ℝ^(r + m)), e)` comes from
`SO(r + m)` exactly when its boundary in `π_k(SO(m))` is trivial. -/
theorem mem_range_homotopyGroupMap_specialOrthogonalFrameMap_iff [NeZero m]
    {a : HomotopyGroup (Option N) (finiteOrthonormalFrame ℝ r (r + m))
      (specialOrthogonalFrameMap r m 1)} :
    a ∈ range (HomotopyGroup.map
        ⟨specialOrthogonalFrameMap r m, continuous_specialOrthogonalFrameMap r m⟩ rfl) ↔
      specialOrthogonalFrameBoundary r m N a =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1) :=
  (TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq _).trans
    ((fiberEquiv r m N).injective.eq_iff' fiberEquiv_mk_const).symm

/-- **Exactness at `π_k(SO(m))`.** A class of `π_k(SO(m), 1)` is a boundary exactly when it
becomes trivial in `SO(r + m)` under the block embedding `B ↦ diag(1_r, B)`. -/
theorem mem_range_specialOrthogonalFrameBoundary_iff [NeZero m]
    {c : HomotopyGroup N (specialOrthogonalGroup (Fin m) ℝ) 1} :
    c ∈ range (specialOrthogonalFrameBoundary r m N) ↔
      HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ r m,
          finiteOrthonormalFrame.continuous_fromBlocksOne m⟩
          (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ r m)) c =
        (⟦GenLoop.const⟧ : HomotopyGroup N (specialOrthogonalGroup (Fin (r + m)) ℝ) 1) := by
  rw [specialOrthogonalFrameBoundary, range_comp, mem_image_equiv, ← map_fiberι_fiberEquiv_symm]
  exact TopCat.mem_range_fibrationBoundary_iff _

/-- **Exactness at `π_k(SO(r + m))`.** A class of `π_k(SO(r + m), 1)` comes from `SO(m)` under the
block embedding `B ↦ diag(1_r, B)` exactly when it becomes trivial in
`π_k(V_r(ℝ^(r + m)), e)`. -/
theorem mem_range_homotopyGroupMap_fromBlocksOne_iff_specialOrthogonalFrameMap [NeZero m]
    {d : HomotopyGroup N (specialOrthogonalGroup (Fin (r + m)) ℝ) 1} :
    d ∈ range (HomotopyGroup.map ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ r m,
        finiteOrthonormalFrame.continuous_fromBlocksOne m⟩
        (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ r m))) ↔
      HomotopyGroup.map ⟨specialOrthogonalFrameMap r m, continuous_specialOrthogonalFrameMap r m⟩
        rfl d =
        (⟦GenLoop.const⟧ : HomotopyGroup N (finiteOrthonormalFrame ℝ r (r + m))
          (specialOrthogonalFrameMap r m 1)) := by
  have h : range (HomotopyGroup.map (N := N) ⟨SpecialOrthogonalGroup.fromBlocksOne ℝ r m,
      finiteOrthonormalFrame.continuous_fromBlocksOne m⟩
      (map_one (SpecialOrthogonalGroup.fromBlocksOne ℝ r m))) =
      range (HomotopyGroup.map ((frameHom r m).fiberι _).hom
        (TopCat.Hom.fiberι_apply (frameHom r m) _ (fiberOne r m))) := by
    rw [← (fiberEquiv r m N).symm.surjective.range_comp]
    exact congrArg range (funext fun c ↦ (map_fiberι_fiberEquiv_symm c).symm)
  rw [h]
  exact TopCat.mem_range_homotopyGroupMap_fiberι_iff specialOrthogonalFrameMap_mem_serreFibrations

end TauCeti
