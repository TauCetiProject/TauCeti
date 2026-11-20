/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Geometry.Manifold.Diffeomorph.Basic
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
public import TauCeti.GroupTheory.GroupAction.Hom
import TauCeti.Geometry.Manifold.MFDeriv.Basic

/-!
# The fixed tangent subspace of a group action

Let a group `K` act on a manifold `M`. At a point `p` of `M`, the tangent vectors fixed by the
differential at `p` of every element of the stabilizer of `p` form a subspace

`V_p = {v ∈ T_p M | d(k •)_p v = v for every k ∈ stabilizer K p}`

(`TauCeti.fixedTangentSubspace I K p`) of `T_p M`. It is the space of invariant vectors of the
tangent representation of the stabilizer whenever that representation is defined
(`TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`). At a point of the common
fixed set `M^K` the stabilizer is all of `K`, so `V_p` consists of the vectors fixed by the
differential of every element of `K`.

Grouping the points of `M^K` by the dimension of `V_p` gives the sets
`M^K_d = {p ∈ M^K | dim V_p = d}` (`TauCeti.fixedPointsOfFinrank I K M d`), which partition the
fixed set. No metric, topology on `K` or smoothness of the action is needed for these
definitions; for a group of isometries the sets `M^K_d` are embedded submanifolds
(`TauCeti.exists_isSmoothEmbedding_fixedPointsOfFinrank`).

These objects are natural under equivariant maps. If `f ∘ g = h ∘ f` and `g` fixes `p`, then
differentiating at `p` shows that `df_p` intertwines `dg_p` and `dh_(f p)`
(`TauCeti.mfderiv_comp_mfderiv_of_comp_eq`). For an equivariant `f : M → N`, that is
`f (k • x) = k • f x`, this applies with `g` and `h` the actions of an element `k` fixing `p`.
So `df_p` sends `V_p` into `V_(f p)` as soon as every element fixing `f p` also fixes `p`
(`TauCeti.map_mfderiv_fixedTangentSubspace_le`), and when moreover `df_p` is injective, `V_p` is
exactly the preimage of `V_(f p)` (`TauCeti.comap_mfderiv_fixedTangentSubspace`). For an
equivariant diffeomorphism `F : M → N` this gives `dF_p (V_p) = V_(F p)`
(`Diffeomorph.map_mfderiv_fixedTangentSubspace`), hence `F (M^K_d) = N^K_d`
(`Diffeomorph.image_fixedPointsOfFinrank`). Already an equivariant bijection carries `M^K` onto
`N^K` (`Equiv.image_fixedPoints`), and an equivariant homeomorphism carries each connected
component of `M^K` onto the component of `N^K` through the image point
(`Homeomorph.image_connectedComponentIn_fixedPoints`); these two hold for any monoid action.

## Main definitions

* `TauCeti.fixedTangentSubspace I K p`: the tangent vectors at `p` fixed by the differential of
  every element of the stabilizer of `p`.
* `TauCeti.fixedPointsOfFinrank I K M d`: the points of `M^K` at which this subspace has dimension
  `d`.

## Main results

* `TauCeti.mem_fixedTangentSubspace_iff_of_mem_fixedPoints`: at a point of the fixed set, the
  fixed tangent subspace consists of the vectors fixed by the differential of every element of `K`.
* `TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`: it is the space of invariant
  vectors of the tangent representation.
* `TauCeti.iUnion_fixedPointsOfFinrank`, `TauCeti.pairwise_disjoint_fixedPointsOfFinrank`: the
  sets `M^K_d` partition the fixed set.
* `TauCeti.comap_mfderiv_fixedTangentSubspace`: an equivariant map with injective differential,
  preserving the stabilizer of `p`, pulls the fixed tangent subspace at `f p` back to the one at
  `p`.
* `Diffeomorph.map_mfderiv_fixedTangentSubspace`: an equivariant diffeomorphism carries fixed
  tangent subspaces onto fixed tangent subspaces.
* `Diffeomorph.image_fixedPointsOfFinrank`: it carries the parts of the fixed set of each dimension
  onto those of the target.
-/

public section

open Set MulAction
open scoped Manifold

noncomputable section

namespace TauCeti

section FixedTangentSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} (K : Type*) [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]

variable (I) in
/-- The tangent vectors at `p` fixed by the differential at `p` of the action of every element
of the stabilizer of `p`; these are the invariant vectors of the tangent representation
(`TauCeti.invariants_tangentRepresentation_eq_fixedTangentSubspace`). At a point of the fixed set
`M^K` the stabilizer is all of `K` (`TauCeti.mem_fixedTangentSubspace_iff_of_mem_fixedPoints`). -/
def fixedTangentSubspace (p : M) : Submodule ℝ (TangentSpace I p) where
  carrier := {v | ∀ k ∈ stabilizer K p, mfderiv I I (k • ·) p v = v}
  -- The differentials land in `T_(k • p) M`, which like `T_p M` is the model space `E`; `rfl`
  -- identifies the two copies of the remaining operation.
  add_mem' hv hw k hk := by
    simp only [map_add, hv k hk, hw k hk]
    rfl
  zero_mem' k _ := by
    simp only [map_zero]
    rfl
  smul_mem' c v hv k hk := by
    simp only [map_smul, hv k hk]
    rfl

variable {K} in
@[simp]
theorem mem_fixedTangentSubspace {p : M} {v : TangentSpace I p} :
    v ∈ fixedTangentSubspace I K p ↔ ∀ k ∈ stabilizer K p, mfderiv I I (k • ·) p v = v :=
  Iff.rfl

variable {K} in
/-- At a point of the fixed set, the stabilizer is all of `K`, so the fixed tangent subspace
consists of the tangent vectors fixed by the differential of every element of `K`. -/
theorem mem_fixedTangentSubspace_iff_of_mem_fixedPoints {p : M} (hp : p ∈ MulAction.fixedPoints K M)
    {v : TangentSpace I p} :
    v ∈ fixedTangentSubspace I K p ↔ ∀ k : K, mfderiv I I (k • ·) p v = v :=
  ⟨fun h k ↦ h k (hp k), fun h k _ ↦ h k⟩

variable {K} in
/-- The fixed tangent subspace is the space of invariant vectors of the tangent representation of
the stabilizer. -/
theorem invariants_tangentRepresentation_eq_fixedTangentSubspace {p : M}
    (hd : ∀ g ∈ stabilizer K p, MDifferentiableAt I I (fun y : M ↦ g • y) p) :
    (tangentRepresentation hd).toRepresentation.invariants = fixedTangentSubspace I K p :=
  Submodule.ext fun _ ↦ mem_invariants_tangentRepresentation_iff hd

variable (I M) in
/-- The points of the fixed set `M^K` at which the tangent vectors fixed by the differentials of
all elements of `K` form a space of dimension `d`. -/
def fixedPointsOfFinrank (d : ℕ) : Set M :=
  {p | p ∈ MulAction.fixedPoints K M ∧ Module.finrank ℝ (fixedTangentSubspace I K p) = d}

variable {K} in
@[simp]
theorem mem_fixedPointsOfFinrank {d : ℕ} {p : M} :
    p ∈ fixedPointsOfFinrank I K M d ↔
      p ∈ MulAction.fixedPoints K M ∧ Module.finrank ℝ (fixedTangentSubspace I K p) = d :=
  Iff.rfl

variable {K} in
/-- Each part of the fixed set of a given dimension lies in the fixed set. -/
theorem fixedPointsOfFinrank_subset_fixedPoints (d : ℕ) :
    fixedPointsOfFinrank I K M d ⊆ MulAction.fixedPoints K M :=
  fun _ hp ↦ hp.1

variable (I M) in
/-- The fixed set is the union of its parts of each dimension. -/
theorem iUnion_fixedPointsOfFinrank :
    ⋃ d, fixedPointsOfFinrank I K M d = MulAction.fixedPoints K M :=
  Subset.antisymm (iUnion_subset fixedPointsOfFinrank_subset_fixedPoints) fun _ hp ↦
    mem_iUnion.2 ⟨_, hp, rfl⟩

variable (I M) in
/-- The parts of the fixed set of different dimensions are disjoint. -/
theorem pairwise_disjoint_fixedPointsOfFinrank :
    Pairwise (Function.onFun Disjoint (fixedPointsOfFinrank I K M)) :=
  fun _ _ hde ↦ disjoint_left.2 fun _ hp hq ↦ hde (hp.2.symm.trans hq.2)

end FixedTangentSubspace

section Map

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MulAction K N]
  {f : M → N} {p : M}

/-- **Semiconjugate maps intertwine the differentials.** If `f ∘ g = h ∘ f` and `g` fixes `p`,
then `df_p ∘ dg_p = dh_(f p) ∘ df_p`. Where `f` is not differentiable both sides vanish. For an
equivariant map, `g` and `h` are the actions of an element fixing `p`. -/
theorem mfderiv_comp_mfderiv_of_comp_eq {g : M → M} {h : N → N} (hfg : f ∘ g = h ∘ f)
    (hp : g p = p) (hg : MDifferentiableAt I I g p) (hh : MDifferentiableAt I' I' h (f p)) :
    (mfderiv I I' f p).comp (mfderiv I I g p) =
      (mfderiv I' I' h (f p)).comp (mfderiv I I' f p) := by
  by_cases hfp : MDifferentiableAt I I' f p
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hfp]
    exact (ContinuousLinearMap.zero_comp _).trans (ContinuousLinearMap.comp_zero _).symm
  rw [← mfderiv_comp_of_apply_eq_self hfp hg hp, hfg, mfderiv_comp p hh hfp]

/-- **Equivariant maps preserve fixed tangent vectors.** If `f` is equivariant, and every element
fixing `f p` also fixes `p` (for instance when `p` lies in the fixed set, or when `f` is
injective), then `df_p` sends the fixed tangent subspace at `p` into the fixed
tangent subspace at `f p`. -/
theorem map_mfderiv_fixedTangentSubspace_le (hf : ∀ (k : K) (x : M), f (k • x) = k • f x)
    (hstab : stabilizer K (f p) ≤ stabilizer K p)
    (hdM : ∀ k ∈ stabilizer K (f p), MDifferentiableAt I I (k • ·) p)
    (hdN : ∀ k ∈ stabilizer K (f p), MDifferentiableAt I' I' (k • ·) (f p)) :
    (fixedTangentSubspace I K p).map (mfderiv I I' f p).toLinearMap ≤
      fixedTangentSubspace I' K (f p) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
  rw [mem_fixedTangentSubspace] at hv ⊢
  intro k hk
  have h := congrArg (· v)
    (mfderiv_comp_mfderiv_of_comp_eq (funext (hf k)) (hstab hk) (hdM k hk) (hdN k hk))
  exact h.symm.trans (congrArg (mfderiv I I' f p) (hv k (hstab hk)))

/-- **Fixed tangent vectors are detected by an equivariant map with injective differential.** If
`f` is equivariant with injective differential at `p`, and every element fixing `f p` also fixes
`p` (for instance when `f` is injective), then a tangent vector at `p` is fixed by the stabilizer of
`p` exactly when its image under `df_p` is fixed by the stabilizer of `f p`. -/
theorem comap_mfderiv_fixedTangentSubspace (hf : ∀ (k : K) (x : M), f (k • x) = k • f x)
    (hstab : stabilizer K (f p) ≤ stabilizer K p) (hdf : Function.Injective (mfderiv I I' f p))
    (hdM : ∀ k ∈ stabilizer K p, MDifferentiableAt I I (k • ·) p)
    (hdN : ∀ k ∈ stabilizer K p, MDifferentiableAt I' I' (k • ·) (f p)) :
    (fixedTangentSubspace I' K (f p)).comap (mfderiv I I' f p).toLinearMap =
      fixedTangentSubspace I K p := by
  -- Every element fixing `p` fixes `f p` by equivariance, so the two stabilizers agree.
  replace hstab : stabilizer K (f p) = stabilizer K p :=
    hstab.antisymm fun k hk ↦ by rw [mem_stabilizer_iff, ← hf, mem_stabilizer_iff.1 hk]
  refine le_antisymm (fun v hv ↦ ?_) (Submodule.map_le_iff_le_comap.1 <|
    map_mfderiv_fixedTangentSubspace_le hf hstab.le (hstab ▸ hdM) (hstab ▸ hdN))
  rw [Submodule.mem_comap, mem_fixedTangentSubspace] at hv
  rw [mem_fixedTangentSubspace]
  intro k hk
  have h := congrArg (· v)
    (mfderiv_comp_mfderiv_of_comp_eq (funext (hf k)) hk (hdM k hk) (hdN k hk))
  exact hdf (h.trans (hv k (hstab ▸ hk)))

end Map

end TauCeti

namespace Diffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MulAction K N]
  {n : WithTop ℕ∞} (F : M ≃ₘ^n⟮I, I'⟯ N) [ContMDiffConstSMul I n K M]
  [ContMDiffConstSMul I' n K N]

/-- **An equivariant diffeomorphism carries fixed tangent subspaces onto fixed tangent
subspaces:** `dF_p (V_p) = V_(F p)`. -/
theorem map_mfderiv_fixedTangentSubspace (hn : n ≠ 0)
    (hF : ∀ (k : K) (x : M), F (k • x) = k • F x) (p : M) :
    (fixedTangentSubspace I K p).map (mfderiv I I' F p).toLinearMap =
      fixedTangentSubspace I' K (F p) := by
  have hsurj := (F.mfderivToContinuousLinearEquiv hn p).toLinearEquiv.surjective
  have hinj := (F.mfderivToContinuousLinearEquiv hn p).toLinearEquiv.injective
  rw [← LinearEquiv.coe_coe, F.mfderivToContinuousLinearEquiv_toLinearMap hn] at hsurj hinj
  rw [← comap_mfderiv_fixedTangentSubspace hF
      (MulAction.stabilizer_eq_of_injective F (EquivLike.injective F) hF p).le hinj
      (fun k _ ↦ (contMDiff_const_smul k).mdifferentiable hn p)
      (fun k _ ↦ (contMDiff_const_smul k).mdifferentiable hn (F p)),
    Submodule.map_comap_eq_of_surjective hsurj]

/-- An equivariant diffeomorphism preserves the dimension of the fixed tangent subspace. -/
theorem finrank_fixedTangentSubspace_apply (hn : n ≠ 0)
    (hF : ∀ (k : K) (x : M), F (k • x) = k • F x) (p : M) :
    Module.finrank ℝ (fixedTangentSubspace I' K (F p)) =
      Module.finrank ℝ (fixedTangentSubspace I K p) := by
  rw [← F.map_mfderiv_fixedTangentSubspace hn hF p,
    ← F.mfderivToContinuousLinearEquiv_toLinearMap hn]
  exact (F.mfderivToContinuousLinearEquiv hn p).toLinearEquiv.finrank_map_eq _

/-- An equivariant diffeomorphism maps a point into the part `N^K_d` of the fixed set exactly when
the point lies in `M^K_d`. -/
theorem apply_mem_fixedPointsOfFinrank_iff (hn : n ≠ 0)
    (hF : ∀ (k : K) (x : M), F (k • x) = k • F x) {d : ℕ} {x : M} :
    F x ∈ fixedPointsOfFinrank I' K N d ↔ x ∈ fixedPointsOfFinrank I K M d := by
  rw [mem_fixedPointsOfFinrank, mem_fixedPointsOfFinrank,
    MulAction.apply_mem_fixedPoints_iff_of_injective hF (EquivLike.injective F),
    F.finrank_fixedTangentSubspace_apply hn hF]

/-- **An equivariant diffeomorphism carries each part of the fixed set of a given dimension onto
the part of the same dimension:** `F (M^K_d) = N^K_d`. -/
theorem image_fixedPointsOfFinrank (hn : n ≠ 0)
    (hF : ∀ (k : K) (x : M), F (k • x) = k • F x) (d : ℕ) :
    F '' fixedPointsOfFinrank I K M d = fixedPointsOfFinrank I' K N d :=
  (F.toEquiv.eq_preimage_iff_image_eq _ _).1 <| Set.ext fun _ ↦
    (F.apply_mem_fixedPointsOfFinrank_iff hn hF).symm

end Diffeomorph
