/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.Geometry.Manifold.GroupAction.TangentRepresentation
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.Diffeomorph.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.GroupTheory.GroupAction.Hom
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

Two cases are computed. If every element of `K` acts as the identity, as for the trivial group,
then `M^K = M` and every tangent vector is fixed, so `M^K` is the single part `M^K_d` with
`d = dim M`. If `K` acts by continuous linear maps on a normed space `E`, viewed as a manifold
modelled on itself, then the differential of each `k •` is `k •` itself. So at a point of `E^K`
the fixed tangent subspace is, through the canonical identification of the tangent space with
`E`, the subspace `E^K` of invariant vectors, and `E^K` is the single part `E^K_d` with
`d = dim E^K`.

These objects are natural under equivariant maps. If `f ∘ g = h ∘ f` and `g` fixes `p`, then
differentiating at `p` shows that `df_p` intertwines `dg_p` and `dh_(f p)`
(`TauCeti.mfderiv_comp_mfderiv_of_comp_eq`). For an equivariant `f : M → N`, that is
`f (k • x) = k • f x`, this applies with `g` and `h` the actions of an element `k` fixing `p`.
So `df_p` sends `V_p` into `V_(f p)` as soon as every element fixing `f p` also fixes `p`
(`TauCeti.map_mfderiv_fixedTangentSubspace_le`), and when moreover `df_p` is injective, `V_p` is
exactly the preimage of `V_(f p)` (`TauCeti.comap_mfderiv_fixedTangentSubspace`).

Diffeomorphisms need equivariance only near `p`. If a diffeomorphism `ψ : M → N`
commutes with the action of every `k ∈ K` near `p`, the chain rule gives
`d(k •)_(ψ p) ∘ dψ_p = dψ_(k • p) ∘ d(k •)_p`, and `ψ` preserves the stabilizer of `p`; so the
differential `dψ_p` carries `V_p` onto `V_(ψ p)`
(`Diffeomorph.map_fixedTangentSubspace`). A globally equivariant diffeomorphism therefore carries
the fixed set, its parts `M^K_d` and the connected components of the fixed set onto those of `N`
(`TauCeti.MulAction.image_fixedPoints_of_bijective`, `Diffeomorph.image_fixedPointsOfFinrank`,
`Homeomorph.image_connectedComponentIn_fixedPoints`). No smoothness of the actions is used in
these diffeomorphism results: where `k •` is not differentiable, the chain rule through a
diffeomorphism still holds with both sides zero. Applied to the diffeomorphisms `a •` of a group
acting smoothly on `M`, they show that for a subgroup `K` every element of the centralizer of `K`
maps each part `M^K_d` onto itself (`TauCeti.smul_mem_fixedPointsOfFinrank_iff`).

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
* `TauCeti.fixedPointsOfFinrank_finrank_of_smul_eq_self`: for an action by identity maps, the
  whole manifold is the part of dimension `dim M`.
* `TauCeti.map_fromTangentSpace_fixedTangentSubspace`: for a continuous linear action on a normed
  space, the fixed tangent subspace at a fixed point is the subspace of invariant vectors.
* `TauCeti.fixedPointsOfFinrank_finrank_invariants`,
  `TauCeti.fixedPointsOfFinrank_eq_empty_of_ne_finrank_invariants`: for such an action the fixed
  set is the single part of dimension `dim E^K`.
* `TauCeti.mfderiv_comp_mfderiv_of_comp_eq`: semiconjugate maps intertwine the differentials at a
  fixed point of the inner map.
* `TauCeti.map_mfderiv_fixedTangentSubspace_le`, `TauCeti.comap_mfderiv_fixedTangentSubspace`: an
  equivariant map sends the fixed tangent subspace at `p` into that at `f p`, and pulls the latter
  back to the former when its differential is injective and it preserves the stabilizer of `p`.
* `Diffeomorph.mfderiv_smul_mfderiv_of_mem_stabilizer`: the differential at `p` of a
  diffeomorphism that is equivariant near `p` intertwines the actions of the stabilizer of `p` on
  the tangent spaces at `p` and at `ψ p`; no smoothness of the actions is needed.
* `Diffeomorph.map_fixedTangentSubspace`: the differential of a diffeomorphism that is
  equivariant near `p` carries the fixed tangent subspace at `p` onto that at `ψ p`.
* `Diffeomorph.fixedTangentSubspaceEquiv`: this differential as a linear equivalence between the
  fixed tangent subspaces.
* `Diffeomorph.image_fixedPointsOfFinrank`: an equivariant diffeomorphism carries each part
  `M^K_d` of the fixed set onto the corresponding part of the target.
* `TauCeti.smul_mem_fixedPointsOfFinrank_iff`: the centralizer of a subgroup `K` preserves each
  part `M^K_d` of the fixed set of `K`.
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

section Trivial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]

/-- If every group element acts as the identity, every tangent vector is fixed. -/
theorem fixedTangentSubspace_eq_top_of_smul_eq_self (h : ∀ (k : K) (x : M), k • x = x) (p : M) :
    fixedTangentSubspace I K p = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun v ↦ mem_fixedTangentSubspace.2 fun k _ ↦ ?_
  rw [show (fun y : M ↦ k • y) = id from funext (h k), mfderiv_id]
  exact ContinuousLinearMap.id_apply v

variable (I) in
/-- **The fixed set of a trivial action.** If every group element acts as the identity, as for the
trivial group, the fixed set is the whole manifold, with every tangent vector fixed, so it is the
single part of the dimension of the model space. -/
theorem fixedPointsOfFinrank_finrank_of_smul_eq_self (h : ∀ (k : K) (x : M), k • x = x) :
    fixedPointsOfFinrank I K M (Module.finrank ℝ E) = univ := by
  refine eq_univ_of_forall fun p ↦ mem_fixedPointsOfFinrank.2 ⟨fun k ↦ h k p, ?_⟩
  rw [fixedTangentSubspace_eq_top_of_smul_eq_self h, finrank_top]
  -- The tangent space `T_p M` is the model space `E`.
  rfl

end Trivial

section Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Type*} [Group K]
  [DistribMulAction K E] [SMulCommClass K ℝ E] [ContinuousConstSMul K E]

/-- **The fixed tangent subspace of a linear action.** For a group acting on a normed space `E` by
continuous linear maps, the fixed tangent subspace at a fixed point is, through the canonical
identification of the tangent space with `E`, the subspace of invariant vectors. -/
theorem map_fromTangentSpace_fixedTangentSubspace {p : E} (hp : p ∈ fixedPoints K E) :
    (fixedTangentSubspace 𝓘(ℝ, E) K p).map
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) p).toLinearEquiv.toLinearMap =
      (Representation.ofDistribMulAction ℝ K E).invariants := by
  ext w
  simp only [Submodule.mem_map, Representation.mem_invariants,
    Representation.ofDistribMulAction_apply_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩ k
    simpa [NormedSpace.fromTangentSpace_apply] using
      ((mvfderiv_smul_left (𝕜 := ℝ) k p v).symm.trans (mvfderiv_apply_eq_mfderiv_apply _ p v)).trans
        ((mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp).1 hv k)
  · intro hw
    refine ⟨(NormedSpace.fromTangentSpace p).symm w,
      (mem_fixedTangentSubspace_iff_of_mem_fixedPoints hp).2 fun k ↦ ?_, by simp⟩
    refine (mvfderiv_apply_eq_mfderiv_apply (fun x : E ↦ k • x) p _).symm.trans <|
      (mvfderiv_smul_left k p _).trans ?_
    rw [ContinuousLinearEquiv.apply_symm_apply]
    simpa [NormedSpace.fromTangentSpace_symm_apply] using hw k

/-- For a group acting on a normed space by continuous linear maps, the fixed tangent subspace at
every fixed point has the dimension of the subspace of invariant vectors. -/
theorem finrank_fixedTangentSubspace_eq_finrank_invariants {p : E} (hp : p ∈ fixedPoints K E) :
    Module.finrank ℝ (fixedTangentSubspace 𝓘(ℝ, E) K p) =
      Module.finrank ℝ (Representation.ofDistribMulAction ℝ K E).invariants := by
  rw [← map_fromTangentSpace_fixedTangentSubspace hp, LinearEquiv.finrank_map_eq]

variable (K E) in
/-- **The fixed set of a linear action.** For a group acting on a normed space `E` by continuous
linear maps, the whole fixed set is the part of the dimension `dim E^K` of the subspace of
invariant vectors. -/
theorem fixedPointsOfFinrank_finrank_invariants :
    fixedPointsOfFinrank 𝓘(ℝ, E) K E
        (Module.finrank ℝ (Representation.ofDistribMulAction ℝ K E).invariants) =
      fixedPoints K E :=
  Subset.antisymm (fixedPointsOfFinrank_subset_fixedPoints _) fun _ hp ↦
    mem_fixedPointsOfFinrank.2 ⟨hp, finrank_fixedTangentSubspace_eq_finrank_invariants hp⟩

variable (K E) in
/-- For a group acting on a normed space `E` by continuous linear maps, the fixed set has no part
of dimension other than `dim E^K`. -/
theorem fixedPointsOfFinrank_eq_empty_of_ne_finrank_invariants {d : ℕ}
    (hd : d ≠ Module.finrank ℝ (Representation.ofDistribMulAction ℝ K E).invariants) :
    fixedPointsOfFinrank 𝓘(ℝ, E) K E d = ∅ :=
  eq_empty_of_forall_notMem fun _ hp ↦ by
    obtain ⟨hp', rfl⟩ := mem_fixedPointsOfFinrank.1 hp
    exact hd (finrank_fixedTangentSubspace_eq_finrank_invariants hp')

end Linear

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

/-! ### Naturality under equivariant diffeomorphisms -/

namespace Diffeomorph

open TauCeti Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {K : Type*} [Group K]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction K M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MulAction K N]
  {n : ℕ∞ω}

/-- The differential at a point `p` of a diffeomorphism that commutes with the action of every
element of the stabilizer of `p` near `p` intertwines the actions of the stabilizer on the
tangent spaces at `p` and at `ψ p`. -/
theorem mfderiv_smul_mfderiv_of_mem_stabilizer (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {k : K}
    {p : M} (h : ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ) (hk : k ∈ MulAction.stabilizer K p)
    (v : TangentSpace I p) :
    mfderiv J J (k • ·) (ψ p) (mfderiv I J ψ p v) =
      mfderiv I J ψ p (mfderiv I I (k • ·) p v) := by
  rw [ψ.mfderiv_apply_mfderiv_of_comp_eventuallyEq hn h]
  -- The differentials of `ψ` at `k • p` and at `p` agree once `k • p = p`; the tangent spaces at
  -- both points are the model space, so the vector can be fed to either.
  have key (q : M) (hq : q = p) (u : TangentSpace I q) : mfderiv I J ψ q u = mfderiv I J ψ p u := by
    subst hq
    rfl
  exact key _ (MulAction.mem_stabilizer_iff.1 hk) _

/-- **Naturality of the fixed tangent subspace.** The differential at `p` of a diffeomorphism
that commutes near `p` with the action of every element of `K` carries the fixed tangent
subspace at `p` onto the fixed tangent subspace at `ψ p`. -/
theorem map_fixedTangentSubspace (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {p : M}
    (h : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ) :
    (fixedTangentSubspace I K p).map
        (ψ.mfderivToContinuousLinearEquiv hn p).toLinearEquiv.toLinearMap =
      fixedTangentSubspace J K (ψ p) := by
  have hstab : MulAction.stabilizer K (ψ p) = MulAction.stabilizer K p :=
    TauCeti.MulAction.stabilizer_eq_of_injective ψ ψ.injective fun k ↦ (h k).self_of_nhds
  have hinj : Function.Injective (mfderiv I J ψ p) := (ψ.isInvertible_mfderiv hn).injective
  ext w
  simp only [Submodule.mem_map, LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv,
    Diffeomorph.mfderivToContinuousLinearEquiv_apply, mem_fixedTangentSubspace, hstab]
  constructor
  · rintro ⟨v, hv, rfl⟩ k hk
    rw [ψ.mfderiv_smul_mfderiv_of_mem_stabilizer hn (h k) hk, hv k hk]
  · intro hw
    obtain ⟨v, rfl⟩ := (ψ.isInvertible_mfderiv hn).surjective w
    refine ⟨v, fun k hk ↦ hinj ?_, rfl⟩
    rw [← ψ.mfderiv_smul_mfderiv_of_mem_stabilizer hn (h k) hk, hw k hk]

/-- The differential at `p` of a diffeomorphism that commutes near `p` with the action of every
element of `K`, as a linear equivalence between the fixed tangent subspaces at `p` and at
`ψ p`. -/
def fixedTangentSubspaceEquiv (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {p : M}
    (h : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ) :
    fixedTangentSubspace I K p ≃ₗ[ℝ] fixedTangentSubspace J K (ψ p) :=
  (ψ.mfderivToContinuousLinearEquiv hn p).toLinearEquiv.ofSubmodules _ _
    (ψ.map_fixedTangentSubspace hn h)

@[simp]
theorem coe_fixedTangentSubspaceEquiv_apply (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {p : M}
    (h : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ) (v : fixedTangentSubspace I K p) :
    (ψ.fixedTangentSubspaceEquiv hn h v : TangentSpace J (ψ p)) = mfderiv I J ψ p v := by
  simp [fixedTangentSubspaceEquiv]

/-- A diffeomorphism that commutes near `p` with the action of every element of `K` preserves the
dimension of the fixed tangent subspace at `p`. -/
theorem finrank_fixedTangentSubspace (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {p : M}
    (h : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 p] (k • ·) ∘ ψ) :
    Module.finrank ℝ (fixedTangentSubspace J K (ψ p)) =
      Module.finrank ℝ (fixedTangentSubspace I K p) := by
  rw [← ψ.map_fixedTangentSubspace hn h, LinearEquiv.finrank_map_eq]

/-- A diffeomorphism that commutes near `x` with the action of every element of `K` sends `x` to a
fixed point with a fixed tangent subspace of dimension `d` exactly when `x` is such a fixed
point. -/
theorem apply_mem_fixedPointsOfFinrank_iff (ψ : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) {x : M}
    (h : ∀ k : K, ψ ∘ (k • ·) =ᶠ[𝓝 x] (k • ·) ∘ ψ) {d : ℕ} :
    ψ x ∈ fixedPointsOfFinrank J K N d ↔ x ∈ fixedPointsOfFinrank I K M d := by
  rw [mem_fixedPointsOfFinrank, mem_fixedPointsOfFinrank,
    TauCeti.MulAction.apply_mem_fixedPoints_iff_of_injective (f := ψ) ψ.injective
      fun k ↦ (h k).self_of_nhds,
    ψ.finrank_fixedTangentSubspace hn h]

section Equivariant

variable (ψ : M ≃ₘ^n⟮I, J⟯ N) (hψ : ∀ (k : K) (x : M), ψ (k • x) = k • ψ x)
include hψ

/-- An equivariant diffeomorphism carries the part `M^K_d` of the fixed set, on which the fixed
tangent subspaces have dimension `d`, onto the corresponding part `N^K_d`. -/
theorem image_fixedPointsOfFinrank (hn : n ≠ 0) (d : ℕ) :
    ψ '' fixedPointsOfFinrank I K M d = fixedPointsOfFinrank J K N d := by
  ext y
  refine ⟨?_, fun hy ↦ ⟨ψ.symm y, ?_, ψ.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩
    exact (ψ.apply_mem_fixedPointsOfFinrank_iff hn fun k ↦ .of_forall (hψ k)).2 hx
  · rwa [← ψ.apply_mem_fixedPointsOfFinrank_iff hn fun k ↦ .of_forall (hψ k),
      ψ.apply_symm_apply]

end Equivariant

end Diffeomorph

/-! ### The centralizer of a subgroup -/

namespace TauCeti

open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MulAction G M]
  {n : ℕ∞ω} [ContMDiffConstSMul I n G M] {K : Subgroup G}

/-- **The centralizer of a subgroup preserves the parts of its fixed set.** If `a` commutes with
every element of the subgroup `K`, the diffeomorphism `a • ·` commutes with the action of `K`, so
`a • x` lies in `M^K_d` exactly when `x` does. -/
theorem smul_mem_fixedPointsOfFinrank_iff (hn : n ≠ 0) {a : G}
    (ha : a ∈ Subgroup.centralizer (K : Set G)) {x : M} {d : ℕ} :
    a • x ∈ fixedPointsOfFinrank I K M d ↔ x ∈ fixedPointsOfFinrank I K M d := by
  rw [← Diffeomorph.constSmul_apply (I := I) (n := n) a x]
  refine (Diffeomorph.constSmul I n a).apply_mem_fixedPointsOfFinrank_iff hn fun k : K ↦
    .of_forall fun y ↦ ?_
  simp only [Function.comp_apply, Diffeomorph.constSmul_apply, Subgroup.smul_def, smul_smul,
    Subgroup.mem_centralizer_iff.1 ha k k.property]

end TauCeti
