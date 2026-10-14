/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Topology.Subpath
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import TauCeti.Topology.UnitInterval
-- Private: `Path.Homotopic.map_trans_evalAt` is used only in the proof of
-- `map_nullhomotopic_of_nullhomotopic` below, so this import is not re-exported.
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Path homotopy helpers

Small path and path-homotopy lemmas, mostly for the universal-cover construction. The
quotient subpath identities are adapted from Kim Morrison's Mathlib universal-cover drafts,
especially [#31576](https://github.com/leanprover-community/mathlib4/pull/31576) and
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292), following the earlier
Tau Ceti work in [#42](https://github.com/TauCetiProject/TauCeti/pull/42).

`Path.exists_homotopy_forall_mem_of_isSimplyConnected` is not from that source: it records that
`SimplyConnectedSpace.paths_homotopic`, applied in a subspace `↥V`, yields a homotopy in the
ambient space whose intermediate paths all stay in `V`. Analytic continuation consumes it in
`Analysis/Complex/Conformal/GlobalBranch.lean`.

`Path.homotopic_of_continuous_square` is likewise adapted from Kim Morrison's
[#38292](https://github.com/leanprover-community/mathlib4/pull/38292). It is used by
`AlgebraicTopology/UniversalCover/BasedPath.lean`, where it previously lived privately, and by
`AlgebraicTopology/Sphere/Puncture.lean`. The lemma
`Path.Homotopic.refl_of_forall_mem_of_nullhomotopic` is not from #38292; it was factored out of
`AlgebraicTopology/SemilocallySimplyConnected/Basic.lean`.

`Path.exists_monotone_range_subpath_subset` subdivides a path, by the Lebesgue number lemma on the
unit interval, so that each consecutive subpath lies in a member of a given family of sets. It is
used for the generation half of the groupoid van Kampen theorem in
`AlgebraicTopology/FundamentalGroupoid/CoverGeneration.lean`, and, repackaged over a
`unitInterval.Partition` as `Path.exists_partition_with_property`, for the tube construction in
`Topology/Homotopy/TubeNeighborhood.lean`. That construction also uses
`unitInterval.exists_vertex_family`, the path-connected vertex neighbourhoods of such a
subdivision; `IsPathHomotopyTrivial`, the property of a set that paths in it with common endpoints
are homotopic in the ambient space; and the pasting lemma
`Path.Homotopic.trans_of_subpath_trans`, which assembles homotopies over the segments of a
partition into a homotopy of the whole paths.

`IsSimplyConnected.isPathHomotopyTrivial` records that a simply connected set is
path-homotopy-trivial. `AlgebraicTopology/ThricePuncturedSphere/LoopAtInfinity.lean` uses it to
compare paths inside a closed half-plane.

`Path.trans_apply_of_le` and `Path.trans_apply_of_ge` express a value of a concatenation as a
value of one of its two halves, and `Path.subpath_apply_mem` bounds the values of a subpath by the
values of the path on an interval containing its endpoints. They are used by the gluing
construction in `AlgebraicTopology/FundamentalGroupoid/Glue.lean`.

The path-homotopy quotient API also records that reversing twice is the identity and that the
reverse of the constant class is constant.
-/

public section

open scoped unitInterval
open Topology Set

namespace Path
variable {X : Type*} [TopologicalSpace X]

/-- Restrict a path whose image lies in a subset to a path in the corresponding subtype.
The source and target are the given subtype endpoints, and coercing the restricted path back to
`X` recovers the original path pointwise. -/
def codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    Path x y where
  toFun := s.codRestrict γ hmem
  continuous_toFun := γ.continuous.codRestrict hmem
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- The underlying point of `γ.codRestrict hmem` at time `t` is just `γ t`, viewed in `X`. -/
@[simp]
theorem codRestrict_coe {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) (t : I) :
    (γ.codRestrict hmem t : X) = γ t := by
  rfl

/-- Mapping `γ.codRestrict hmem` back along the subtype inclusion recovers `γ`. -/
@[simp]
theorem map_codRestrict {s : Set X} {x y : s} (γ : Path x.val y.val) (hmem : ∀ t, γ t ∈ s) :
    (γ.codRestrict hmem).map continuous_subtype_val = γ := by
  ext t
  simp

/-- Mapping a constant path gives the constant path at the image point. -/
@[simp]
theorem map_refl {Y : Type*} [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) (a : X) :
    (Path.refl a).map hf = Path.refl (f a) :=
  rfl

/-- The value of `γ.trans δ` at a parameter in the first half is a value of `γ`. -/
theorem trans_apply_of_le {x y z : X} (γ : Path x y) (δ : Path y z) {u : I}
    (hu : (u : ℝ) ≤ 1 / 2) (v : I) (hv : (v : ℝ) = 2 * u) : γ.trans δ u = γ v := by
  rw [trans_apply]
  split_ifs
  exact congrArg γ (Subtype.ext hv.symm)

/-- The value of `γ.trans δ` at a parameter in the second half is a value of `δ`. -/
theorem trans_apply_of_ge {x y z : X} (γ : Path x y) (δ : Path y z) {u : I}
    (hu : 1 / 2 ≤ (u : ℝ)) (v : I) (hv : (v : ℝ) = 2 * u - 1) : γ.trans δ u = δ v := by
  rw [trans_apply]
  split_ifs with h
  · have hu' : (u : ℝ) = 1 / 2 := le_antisymm h hu
    have hv_zero : v = 0 := Subtype.ext (by rw [hv, hu']; norm_num)
    rw [hv_zero, δ.source]
    convert γ.target using 2
    exact Subtype.ext (by norm_num [hu'])
  · exact congrArg δ (Subtype.ext hv.symm)

/-- A subpath of `γ` between two parameters of an interval that `γ` maps into `V` lies in `V`. -/
theorem subpath_apply_mem {x y : X} {γ : Path x y} {V : Set X} {lo hi : I}
    (hγ : ∀ t ∈ Icc lo hi, γ t ∈ V) {a b : I} (ha : a ∈ Icc lo hi) (hb : b ∈ Icc lo hi) (t : I) :
    γ.subpath a b t ∈ V := by
  obtain ⟨s, hs, hst⟩ : γ.subpath a b t ∈ γ '' uIcc a b :=
    range_subpath γ a b ▸ mem_range_self t
  exact hst ▸ hγ s (uIcc_subset_Icc ha hb hs)

/-- If the extended path stays inside `U` throughout `[t₀, t₁]`, then the truncated subpath has
range in `U`. -/
theorem truncateOfLE_range_subset {a b : X} (γ : Path a b) {t₀ t₁ : ℝ}
    (h : t₀ ≤ t₁) {U : Set X} (hU : Set.Icc t₀ t₁ ⊆ γ.extend ⁻¹' U) :
    Set.range (γ.truncateOfLE h) ⊆ U := by
  rintro _ ⟨s, rfl⟩
  dsimp [truncateOfLE, truncate]
  apply hU
  constructor
  · exact le_min (le_max_right _ _) h
  · exact min_le_right _ _

/-- The family of initial segments of `γ : Path a b`: at parameter `t : I`, the path
`s ↦ γ.extend (min s t)` from `a` to `γ t` (`initialSegmentFamily_apply`). At `t = 0` this is
the constant path at `a` (`initialSegmentFamily_zero`); at `t = 1` it is `γ` itself, up to a
trivial right-endpoint cast (`initialSegmentFamily_one`). The property consumers actually need
is joint continuity in `(t, s)`, recorded as `continuous_initialSegmentFamily_uncurry`. -/
noncomputable def initialSegmentFamily {a b : X} (γ : Path a b) (t : I) :
    Path a (γ t) :=
  (γ.truncate 0 t).cast (by rw [min_eq_left t.2.1, γ.extend_zero]) (γ.extend_apply t.2).symm

/-- Every point on a path lies in the path component of its source. -/
theorem mem_pathComponent {a b : X} (γ : Path a b) (t : I) : γ t ∈ pathComponent a :=
  ⟨γ.initialSegmentFamily t⟩

/-- A path whose source lies in a path component remains in that path component. -/
theorem mem_pathComponent_of_mem {a b x₀ : X} (γ : Path a b) (ha : a ∈ pathComponent x₀)
    (t : I) : γ t ∈ pathComponent x₀ :=
  Joined.mem_pathComponent (γ.mem_pathComponent t) ha

theorem continuous_initialSegmentFamily_uncurry {a b : X} (γ : Path a b) :
    Continuous ↿(initialSegmentFamily γ) := by
  have hincl : Continuous (fun ts : I × I ↦ ((ts.1 : ℝ), ts.2) : I × I → ℝ × I) := by fun_prop
  have htrunc : Continuous (fun ts : I × I ↦ γ.truncate 0 ts.1 ts.2 : I × I → X) :=
    (γ.truncate_const_continuous_family 0).comp hincl
  simpa [initialSegmentFamily] using! htrunc

@[simp] theorem initialSegmentFamily_apply {a b : X} (γ : Path a b) (t s : I) :
    initialSegmentFamily γ t s = γ.extend (min (s : ℝ) t) := by
  simp [initialSegmentFamily, Path.truncate, max_eq_left s.2.1]

@[simp] theorem initialSegmentFamily_zero {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 0 = (Path.refl a).cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, γ.extend_zero, Path.refl, min_eq_right s.2.1]
  -- `simp` unfolds `Path.refl` to its structure literal; applying that literal to `s` returns
  -- `a` by definition.
  rfl

@[simp] theorem initialSegmentFamily_one {a b : X} (γ : Path a b) :
    initialSegmentFamily γ 1 = γ.cast rfl (by simp) := by
  ext s
  simp [initialSegmentFamily_apply, min_eq_left s.2.2, γ.extend_apply s.2]

/-- **Two paths with the same endpoints in a simply connected set are homotopic inside it.** For
`p` and `q` running in `V` between the same two points of `V`, there is a homotopy from `p` to `q`
every intermediate path of which again lies in `V`.

The homotopy is stated in the ambient space rather than in `↥V`, with membership in `V` as a
separate conclusion: that is the form consumers want, and it spares them transporting along the
subtype. -/
theorem exists_homotopy_forall_mem_of_isSimplyConnected {V : Set X} (hV : IsSimplyConnected V)
    {a b : X} {p q : Path a b} (hp : ∀ t, p t ∈ V) (hq : ∀ t, q t ∈ V) :
    ∃ K : p.Homotopy q, ∀ t x, K (t, x) ∈ V := by
  have := hV.simplyConnectedSpace
  have haV : a ∈ V := p.source ▸ hp 0
  have hbV : b ∈ V := p.target ▸ hp 1
  obtain ⟨h⟩ := SimplyConnectedSpace.paths_homotopic
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq)
  -- map the subspace homotopy back down, and read its endpoints through `map_codRestrict`
  refine ⟨(h.map (⟨Subtype.val, continuous_subtype_val⟩ : C(V, X))).cast
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) p hp)
    (Path.map_codRestrict (x := ⟨a, haV⟩) (y := ⟨b, hbV⟩) q hq), fun t x => ?_⟩
  simp

/-- **A square with prescribed edges is a path homotopy.** A continuous map on `I × I` that
restricts to `p` at `t = 0` and to `q` at `t = 1`, and is constant along each of the edges `s = 0`
and `s = 1`, exhibits `p` and `q` as homotopic paths. -/
theorem homotopic_of_continuous_square {a b : X} {p q : Path a b} (K : I × I → X)
    (hK_cont : Continuous K) (hK_zero : ∀ s, K (0, s) = p s) (hK_one : ∀ s, K (1, s) = q s)
    (hK_left : ∀ t, K (t, 0) = a) (hK_right : ∀ t, K (t, 1) = b) : p.Homotopic q :=
  ⟨{ toFun := K
     continuous_toFun := hK_cont
     map_zero_left := hK_zero
     map_one_left := hK_one
     prop' := by
       intro t s hs
       rcases hs with rfl | hs
       · exact (hK_left t).trans p.source.symm
       · rw [Set.mem_singleton_iff] at hs
         subst hs
         exact (hK_right t).trans p.target.symm }⟩

/-- If every parameter `s` has some `γ ⁻¹' U i` as a neighbourhood, then `γ` can be subdivided
at finitely many monotone times, starting at `0` and ending at `1`, so that the subpath between
any two consecutive times has range in some `U i`. -/
theorem exists_monotone_range_subpath_subset {ι : Type*} {U : ι → Set X} {x y : X}
    (γ : Path x y) (hU : ∀ s, ∃ i, γ ⁻¹' U i ∈ 𝓝 s) :
    ∃ (n : ℕ) (t : Fin (n + 1) → I), t 0 = 0 ∧ t (Fin.last n) = 1 ∧ Monotone t ∧
      ∀ k : Fin n, ∃ i, range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ U i := by
  obtain ⟨t, ht0, ht_mono, ⟨N, hN⟩, ht_cover⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (c := fun i ↦ interior (γ ⁻¹' U i))
      (fun i ↦ isOpen_interior)
      (fun s _ ↦ by
        obtain ⟨i, hi⟩ := hU s
        exact mem_iUnion.2 ⟨i, mem_interior_iff_mem_nhds.2 hi⟩)
  refine ⟨N, fun k ↦ t k, by simpa using ht0, by simpa using hN N le_rfl,
    fun a b hab ↦ ht_mono (by simpa using hab), fun k ↦ ?_⟩
  obtain ⟨i, hi⟩ := ht_cover k
  refine ⟨i, ?_⟩
  rw [range_subpath_of_le _ _ _ (ht_mono (by simp))]
  rintro _ ⟨s, hs, rfl⟩
  have hs' : s ∈ γ ⁻¹' U i := interior_subset (hi (by simpa using hs))
  exact hs'

-- The statement is ported from https://github.com/leanprover-community/mathlib4/pull/44183.
/-- If every point on a path has an open neighborhood satisfying `P`, then there is a partition
`0 = t₀ ≤ ⋯ ≤ tₙ = 1` such that each segment `γ [tᵢ, tᵢ₊₁]` lies in an open set satisfying
`P`. -/
theorem exists_partition_with_property {x y : X} (γ : Path x y) (P : Set X → Prop)
    (h : ∀ z ∈ range γ, ∃ U : Set X, IsOpen U ∧ z ∈ U ∧ P U) :
    ∃ (n : ℕ) (part : unitInterval.Partition n),
      ∀ i : Fin n, ∃ U : Set X, IsOpen U ∧ P U ∧
        MapsTo γ (Icc (part.t i.castSucc) (part.t i.succ)) U := by
  choose U hU_open hU_mem hU_P using h
  obtain ⟨N, t, ht0, htN, ht_mono, ht_cover⟩ :=
    γ.exists_monotone_range_subpath_subset (U := fun z : range γ ↦ U z.val z.property)
      fun s ↦ ⟨⟨γ s, s, rfl⟩, γ.continuous.continuousAt.preimage_mem_nhds
        ((hU_open _ _).mem_nhds (hU_mem _ _))⟩
  refine ⟨N, ⟨t, ht_mono, ht0, htN⟩, fun i ↦ ?_⟩
  obtain ⟨⟨z, hz⟩, h_seg⟩ := ht_cover i
  rw [range_subpath_of_le _ _ _ (ht_mono i.castSucc_le_succ)] at h_seg
  exact ⟨U z hz, hU_open z hz, hU_P z hz, fun s hs ↦ h_seg ⟨s, hs, rfl⟩⟩

end Path

-- Ported from https://github.com/leanprover-community/mathlib4/pull/44183.
/-- Given open sets `U i` into which `f` maps the consecutive segments `[t i, t (i + 1)]` of a
monotone sequence in the unit interval, the path components of `f (t j)` in the intersections of
the adjacent `U i` are open, path-connected vertex sets, each contained in its adjacent `U i`. -/
theorem unitInterval.exists_vertex_family {X : Type*} [TopologicalSpace X]
    [LocallyPathConnectedSpace X] {n : ℕ} {f : I → X} {t : Fin (n + 1) → I} {U : Fin n → Set X}
    (h_mono : Monotone t)
    (hU_open : ∀ i, IsOpen (U i))
    (hU : ∀ i : Fin n, MapsTo f (Icc (t i.castSucc) (t i.succ)) (U i)) :
    ∃ V : Fin (n + 1) → Set X, (∀ j, IsOpen (V j)) ∧ (∀ j, IsPathConnected (V j)) ∧
      (∀ j, f (t j) ∈ V j) ∧ (∀ i : Fin n, V i.castSucc ⊆ U i) ∧ ∀ i : Fin n, V i.succ ⊆ U i := by
  let W : Fin (n + 1) → Set X := fun j ↦ ⋂ i : Fin n, ⋂ (_ : j = i.castSucc ∨ j = i.succ), U i
  have hW_open : ∀ j, IsOpen (W j) := fun j ↦
    isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun _ ↦ hU_open i
  have hfW : ∀ j, f (t j) ∈ W j := by
    intro j
    simp only [W, mem_iInter]
    rintro i (rfl | rfl)
    · exact hU i ⟨le_rfl, h_mono i.castSucc_lt_succ.le⟩
    · exact hU i ⟨h_mono i.castSucc_lt_succ.le, le_rfl⟩
  refine ⟨fun j ↦ pathComponentIn (W j) (f (t j)), fun j ↦ (hW_open j).pathComponentIn _,
    fun j ↦ isPathConnected_pathComponentIn (hfW j), fun j ↦ mem_pathComponentIn_self (hfW j),
    fun i ↦ pathComponentIn_subset.trans ?_, fun i ↦ pathComponentIn_subset.trans ?_⟩
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inl rfl))
  · exact iInter_subset_of_subset i (iInter_subset _ (Or.inr rfl))

namespace Path
variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Homotopic.Quotient

/-- Reversing a path-homotopy class twice recovers the original class. -/
@[simp]
theorem symm_symm {x₀ x₁ : X} (γ : Homotopic.Quotient x₀ x₁) : γ.symm.symm = γ := by
  induction γ using Quotient.ind with
  | mk γ => exact congrArg mk (Path.symm_symm γ)

/-- The reverse of the constant path-homotopy class is the constant class. -/
@[simp]
theorem symm_refl (x : X) : (refl x).symm = refl x := by
  rw [← mk_refl, ← mk_symm, Path.refl_symm, mk_refl]

/-- The quotient topology on path-homotopy classes. This instance is load-bearing:
`Path.Homotopic.Quotient` is a `def` over `Quotient`, and instance search does not unfold it to
find the generic `TopologicalSpace (Quotient _)`. -/
instance instTopologicalSpace (x₀ x : X) :
    TopologicalSpace (Path.Homotopic.Quotient x₀ x) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

/-- A set of path-homotopy classes is open exactly when its preimage under quotient
construction is open. -/
theorem isOpen_iff_preimage_mk {x₀ x₁ : X} {S : Set (Path.Homotopic.Quotient x₀ x₁)} :
    IsOpen S ↔ IsOpen ((Path.Homotopic.Quotient.mk : Path x₀ x₁ →
      Path.Homotopic.Quotient x₀ x₁) ⁻¹' S) :=
  -- `Iff.rfl` is valid because `instTopologicalSpace` above is by definition the quotient
  -- topology (`inferInstanceAs`), so `IsOpen S` unfolds to openness of the `mk`-preimage.
  Iff.rfl

/-- The concatenation identity `Path.Homotopic.mk_subpath_trans_mk_subpath` with endpoints
recast to given points. This cuts a path into pieces with prescribed, named endpoints. -/
theorem subpath_cast_trans {x y : X} (p : Path x y) (a b c : unitInterval) {x₀ x₁ x₂ : X}
    (h₀ : x₀ = p a) (h₁ : x₁ = p b) (h₂ : x₂ = p c) :
    trans (mk ((p.subpath a b).cast h₀ h₁)) (mk ((p.subpath b c).cast h₁ h₂)) =
      mk ((p.subpath a c).cast h₀ h₂) := by
  subst h₀ h₁ h₂
  simp

/-- A degenerate subpath represents the reflexivity class at its endpoint. -/
theorem subpath_self {x y : X} (p : Path x y) (a : unitInterval) :
    mk (p.subpath a a) = refl (p a) := by
  simp only [← mk_refl, eq]
  rw [Path.subpath_self]

/-- The full `[0,1]` subpath represents the original path, up to the endpoint casts inserted by
`Path.subpath`. -/
theorem subpath_zero_one {x y : X} (p : Path x y) :
    mk (p.subpath 0 1) = (mk p).cast (by simp) (by simp) := by
  simp only [← mk_cast, eq]
  rw [Path.subpath_zero_one]

end Homotopic.Quotient

end Path

namespace Path.Homotopic
variable {X : Type*} [TopologicalSpace X] {x₀ x₁ : X}

/-- Composing on the left with a null-homotopic loop does not change the homotopy class. -/
theorem trans_left_of_nullhomotopic {γ₀ : Path x₀ x₀} {γ₁ : Path x₀ x₁}
    (hγ₀ : γ₀.Homotopic (Path.refl x₀)) : (γ₀.trans γ₁).Homotopic γ₁ :=
  (hcomp hγ₀ (.refl γ₁)).trans (refl_trans γ₁)

/-- Composing on the right with a null-homotopic loop does not change the homotopy class. -/
theorem trans_right_of_nullhomotopic {γ₀ : Path x₀ x₁} {γ₁ : Path x₁ x₁}
    (hγ₁ : γ₁.Homotopic (Path.refl x₁)) : (γ₀.trans γ₁).Homotopic γ₀ :=
  (hcomp (.refl γ₀) hγ₁).trans (trans_refl γ₀)

/-- If `γ.trans γ'.symm` is nullhomotopic, then `γ` and `γ'` are homotopic.
This is the path-homotopy analogue of `a * b⁻¹ = 1 → a = b`. -/
theorem of_trans_symm {γ γ' : Path x₀ x₁}
    (h : (γ.trans γ'.symm).Homotopic (Path.refl x₀)) : γ.Homotopic γ' :=
  (trans_refl γ).symm |>.trans <|
  (hcomp (.refl γ) (symm_trans γ').symm) |>.trans <|
  (trans_assoc γ γ'.symm γ').symm |>.trans <|
  (hcomp h (.refl γ')) |>.trans <|
  refl_trans γ'

/-- Right cancellation in the fundamental groupoid: if `γ.trans e` and `δ.trans e` are homotopic,
then `γ` and `δ` are homotopic. This is the path-homotopy analogue of `a * c = b * c → a = b`. -/
theorem trans_right_cancel {x₀ x₁ x₂ : X} {γ δ : Path x₀ x₁} {e : Path x₁ x₂}
    (h : (γ.trans e).Homotopic (δ.trans e)) : γ.Homotopic δ := by
  have hγ : ((γ.trans e).trans e.symm).Homotopic γ :=
    (trans_assoc γ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  have hδ : ((δ.trans e).trans e.symm).Homotopic δ :=
    (trans_assoc δ e e.symm).trans (trans_right_of_nullhomotopic (trans_symm e))
  exact hγ.symm.trans ((h.hcomp (refl e.symm)).trans hδ)

/-- Left cancellation in the fundamental groupoid: if `e.trans γ` and `e.trans δ` are homotopic,
then `γ` and `δ` are homotopic. This is the path-homotopy analogue of `c * a = c * b → a = b`. -/
theorem trans_left_cancel {x₀ x₁ x₂ : X} {e : Path x₀ x₁} {γ δ : Path x₁ x₂}
    (h : (e.trans γ).Homotopic (e.trans δ)) : γ.Homotopic δ := by
  have hγ : (e.symm.trans (e.trans γ)).Homotopic γ :=
    (trans_assoc e.symm e γ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  have hδ : (e.symm.trans (e.trans δ)).Homotopic δ :=
    (trans_assoc e.symm e δ).symm.trans (trans_left_of_nullhomotopic (symm_trans e))
  exact hγ.symm.trans (((refl e.symm).hcomp h).trans hδ)

/-- A loop whose conjugate by a path is null-homotopic is itself null-homotopic. This is the
path-homotopy analogue of `a * b * a⁻¹ = 1 → b = 1`. -/
theorem of_conj_nullhomotopic {x₀ x₁ : X} {α : Path x₀ x₁} {δ : Path x₁ x₁}
    (h : ((α.trans δ).trans α.symm).Homotopic (Path.refl x₀)) :
    δ.Homotopic (Path.refl x₁) :=
  trans_left_cancel ((of_trans_symm h).trans (trans_refl α).symm)

/-- The image of a based loop under a null-homotopic continuous map is null-homotopic in the
target: a map homotopic to a constant collapses every loop to the constant loop. -/
theorem map_nullhomotopic_of_nullhomotopic {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)}
    (hf : f.Nullhomotopic) {a : X} (γ : Path a a) :
    (γ.map (map_continuous f)).Homotopic (Path.refl (f a)) := by
  obtain ⟨c, ⟨F⟩⟩ := hf
  have key := Path.Homotopic.map_trans_evalAt F γ
  have hconst : γ.map (map_continuous (ContinuousMap.const X c)) = Path.refl c := by ext t; rfl
  rw [hconst] at key
  exact Path.Homotopic.trans_right_cancel
    ((key.trans (Path.Homotopic.trans_refl _)).trans (Path.Homotopic.refl_trans _).symm)

/-- A loop that stays in a set whose inclusion is null-homotopic is itself null-homotopic in the
ambient space. -/
theorem refl_of_forall_mem_of_nullhomotopic {s : Set X}
    (hs : (ContinuousMap.mk (Subtype.val : s → X) continuous_subtype_val).Nullhomotopic)
    {x : X} (γ : Path x x) (hγ : ∀ t, γ t ∈ s) : γ.Homotopic (Path.refl x) := by
  have hx : x ∈ s := γ.source ▸ hγ 0
  have hmap := map_nullhomotopic_of_nullhomotopic hs
    (γ.codRestrict (x := ⟨x, hx⟩) (y := ⟨x, hx⟩) hγ)
  rwa [Path.map_codRestrict] at hmap

namespace Quotient
variable {x₀ x₁ : X}

/-- Casting the reflexivity class at `x` along `h : y = x` gives the reflexivity class at `y`. -/
@[simp, grind =]
theorem refl_cast {x y : X} (h : y = x) : (refl x).cast h h = refl y := by
  -- After `cases h` the cast is along `rfl`, and `Quotient.cast` on a literal `refl` class
  -- reduces definitionally, so `rfl` closes the goal.
  cases h; rfl

/-- If `trans γ (symm γ') = refl`, then `γ = γ'`.
This is the quotient analogue of `eq_of_div_eq_one : a / b = 1 → a = b`. -/
theorem eq_of_trans_symm {γ γ' : Homotopic.Quotient x₀ x₁}
    (h : trans γ (symm γ') = refl x₀) : γ = γ' := by
  induction γ using Quotient.ind with | mk γ =>
  induction γ' using Quotient.ind with | mk γ' =>
  simp only [← mk_trans, ← mk_symm, ← mk_refl] at h
  exact Quotient.sound (Homotopic.of_trans_symm (Quotient.exact h))

end Quotient
end Path.Homotopic

section IsPathHomotopyTrivial

variable {X : Type*} [TopologicalSpace X]

/-- A subset `U` of a topological space `X` is *path-homotopy-trivial* if any two paths
in `X` whose images lie in `U` and which share endpoints are homotopic in `X`.
This is the form of "`U` is simply connected" used in the universal-cover
construction: it is weaker than `IsSimplyConnected U` because the homotopy is not required
to lie inside `U` (`IsSimplyConnected.isPathHomotopyTrivial`). -/
def IsPathHomotopyTrivial (U : Set X) : Prop :=
  ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q

/-- The defining characterization of a path-homotopy-trivial set. -/
theorem isPathHomotopyTrivial_def {U : Set X} :
    IsPathHomotopyTrivial U ↔
      ∀ ⦃a b : X⦄ (p q : Path a b), range p ⊆ U → range q ⊆ U → Path.Homotopic p q :=
  Iff.rfl

/-- A loop in a path-homotopy-trivial set is nullhomotopic. -/
theorem IsPathHomotopyTrivial.nullhomotopic {U : Set X} (hU : IsPathHomotopyTrivial U)
    {x : X} (γ : Path x x) (hγ : range γ ⊆ U) : γ.Homotopic (Path.refl x) :=
  hU γ _ hγ (by simpa using hγ ⟨0, γ.source⟩)

/-- **A simply connected set is path-homotopy-trivial.** Two paths with the same endpoints whose
ranges lie in a simply connected set are homotopic in the ambient space. -/
theorem IsSimplyConnected.isPathHomotopyTrivial {U : Set X} (hU : IsSimplyConnected U) :
    IsPathHomotopyTrivial U :=
  isPathHomotopyTrivial_def.mpr fun _ _ _ _ hp hq ↦
    let ⟨K, _⟩ := Path.exists_homotopy_forall_mem_of_isSimplyConnected hU
      (range_subset_iff.1 hp) (range_subset_iff.1 hq)
    ⟨K⟩

end IsPathHomotopyTrivial

section Pasting
variable {X : Type*} [TopologicalSpace X] {n : ℕ}

-- Ported from https://github.com/leanprover-community/mathlib4/pull/44183.
/-- The class of `p.subpath` over the endpoints of a partition is the class of `p`. Casts keep the
endpoints fixed when rewriting the partition endpoints. -/
private theorem Path.Homotopic.Quotient.cast_mk_subpath_t_zero_t_last {x y : X} (p : Path x y)
    (part : unitInterval.Partition n) (h₁ : x = p (part.t 0)) (h₂ : y = p (part.t (Fin.last n))) :
    (Path.Homotopic.Quotient.mk (p.subpath (part.t 0) (part.t (Fin.last n)))).cast h₁ h₂ =
      Path.Homotopic.Quotient.mk p := by
  revert h₁ h₂
  rw [part.t_zero, part.t_last]
  intro h₁ h₂
  rw [Path.Homotopic.Quotient.subpath_zero_one]
  simp

/-- The pasting lemma. Let `γ : Path x y` and `γ' : Path x' y'`, and let `α j` be "rung" paths
from `γ (t j)` to `γ' (t j)` at the vertices of a partition. If on each segment
`γ|[tᵢ, tᵢ₊₁] · αᵢ₊₁` is homotopic to `αᵢ · γ'|[tᵢ, tᵢ₊₁]`, then `γ · αₙ` is homotopic to
`α₀ · γ'`. -/
theorem Path.Homotopic.trans_of_subpath_trans {x y x' y' : X}
    (γ : Path x y) (γ' : Path x' y') (part : unitInterval.Partition n)
    (α : (j : Fin (n + 1)) → Path (γ (part.t j)) (γ' (part.t j)))
    (h_rect : ∀ i : Fin n,
      ((γ.subpath (part.t i.castSucc) (part.t i.succ)).trans (α i.succ)).Homotopic
        ((α i.castSucc).trans (γ'.subpath (part.t i.castSucc) (part.t i.succ)))) :
    (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))).Homotopic
      (((α 0).cast (by simp) (by simp)).trans γ') := by
  open Path.Homotopic.Quotient in
  -- `γ_aux j` follows `γ` up to `t j`, crosses along `α j`, then follows `γ'`.
  let γ_aux : Fin (n + 1) → Path x y' := fun j ↦
    (((γ.subpath (part.t 0) (part.t j)).trans (α j)).trans
      (γ'.subpath (part.t j) (part.t (Fin.last n)))).cast (by simp) (by simp)
  have h_zero : (γ_aux 0).Homotopic (((α 0).cast (by simp) (by simp)).trans γ') := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [subpath_self, cast_mk_subpath_t_zero_t_last γ' part]
    simp
  have h_last : (γ_aux (Fin.last n)).Homotopic
      (γ.trans ((α (Fin.last n)).cast (by simp) (by simp))) := by
    apply Path.Homotopic.Quotient.exact
    dsimp [γ_aux]
    rw [subpath_self, cast_mk_subpath_t_zero_t_last γ part]
    simp
  have h_rect' : ∀ (i : Fin n) {w : X} (q : Path.Homotopic.Quotient (γ' (part.t i.succ)) w),
      (Path.Homotopic.Quotient.mk (γ.subpath (part.t i.castSucc) (part.t i.succ))).trans
          ((Path.Homotopic.Quotient.mk (α i.succ)).trans q) =
        (Path.Homotopic.Quotient.mk (α i.castSucc)).trans
          ((Path.Homotopic.Quotient.mk (γ'.subpath (part.t i.castSucc) (part.t i.succ))).trans
            q) := by
    intro i w q
    rw [← Path.Homotopic.Quotient.trans_assoc, ← Path.Homotopic.Quotient.trans_assoc]
    rw [← mk_trans, ← mk_trans, Path.Homotopic.Quotient.eq.mpr (h_rect i)]
  have h_step : ∀ i : Fin n, (γ_aux i.succ).Homotopic (γ_aux i.castSucc) := by
    intro i
    apply Path.Homotopic.Quotient.exact
    simp only [γ_aux, mk_trans, mk_cast]
    rw [← Path.Homotopic.mk_subpath_trans_mk_subpath γ (part.t 0) (part.t i.castSucc),
      ← Path.Homotopic.mk_subpath_trans_mk_subpath γ' (part.t i.castSucc) (part.t i.succ)]
    simp only [Path.Homotopic.Quotient.trans_assoc]
    rw [h_rect']
  have h_chain : ∀ j : Fin (n + 1), (γ_aux j).Homotopic (γ_aux 0) := by
    intro j
    induction j using Fin.induction with
    | zero => exact .refl _
    | succ i ih => exact (h_step i).trans ih
  exact h_last.symm.trans ((h_chain (Fin.last n)).trans h_zero)

end Pasting
