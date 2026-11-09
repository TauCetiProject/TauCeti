/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Toric.Algebraic.Lattice
public import TauCeti.Geometry.Toric.Delzant.Basic

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.LinearAlgebra.Finsupp.LinearCombination

/-!
# The kernel torus of a facet presentation

Let `i : N →+ V` be an integral lattice and `u : ι → N` a finite family of facet normals, as in
the Delzant construction of a symplectic toric manifold from its moment polytope. The normals
define the map of lattices

`β : ℤ^ι → N`, `k ↦ ∑ j, k j • u j` (`Fintype.linearCombination ℤ u`),

and its real extension `β_ℝ : ℝ^ι → V`, `t ↦ ∑ j, t j • i (u j)`, which agree on integral
vectors (`Fintype.linearCombination_intCast`). For a period `p`, the map `β_ℝ` descends to
a continuous homomorphism of quotient groups

`π : (ℝ / pℤ)^ι → V / p i(N)` (`TauCeti.Toric.facetTorusHom i u p`,
`TauCeti.Toric.continuous_facetTorusHom`).

For `p ≠ 0` and an integral lattice `i`, both quotients are tori. With the normalization
`p = 2π` used for symplectic toric manifolds, the target is the torus whose Lie algebra is `V`,
with integral cocharacters `N`, and `π` is the homomorphism of tori induced by `β`. For `p = 0`
the quotients are the vector groups `ℝ^ι` and `V`, and `π` is `β_ℝ` itself.

Suppose that `β` is surjective, which holds for the normals of a Delzant polytope
(`TauCeti.Toric.IsDelzant.surjective_linearCombination`) since the normals at a vertex form a
lattice basis. Then the lattice sequence `0 → ker β → ℤ^ι → N → 0` is exact, and:

* when `i(N)` spans `V`, as it does for an integral lattice, `β_ℝ` is surjective
  (`TauCeti.Toric.surjective_linearCombination_real`), so its kernel `𝔫 = ker β_ℝ` has
  dimension `#ι - dim V` (`TauCeti.Toric.finrank_ker_linearCombination_real_add_finrank`), and
  `π` is surjective (`TauCeti.Toric.surjective_facetTorusHom`);
* the kernel of `π` is the image of `𝔫` in `(ℝ / pℤ)^ι`
  (`TauCeti.Toric.coe_ker_facetTorusHom`). An element `[t]` of the kernel has `β_ℝ t = p i(n)`
  for some `n ∈ N`; writing `n = β k` and replacing `t` by `t - p k` gives a representative in
  `𝔫`. Hence the kernel is connected (`TauCeti.Toric.isConnected_ker_facetTorusHom`).

So for `p ≠ 0` and an integral lattice, the kernel of `π` is the connected subtorus `N_Δ` with
Lie algebra `𝔫` whose action on `ℂ^ι` is reduced in the Delzant construction; for `p = 0` it is
the vector subgroup `𝔫` itself. Without surjectivity of `β` the kernel of `π` can be
disconnected: the normal `2` in `ℤ` gives the map `θ ↦ 2θ` of circles, whose kernel has two
points.

## Main definitions

* `TauCeti.Toric.facetTorusHom i u p`: the homomorphism `(ℝ / pℤ)^ι → V / p i(N)`,
  `[t] ↦ [∑ j, t j • i (u j)]`, a homomorphism of tori when `p ≠ 0`.
* `TauCeti.Toric.faceSubtorus i u p s`: the image in `V / p i(N)` of the real span of the normals
  of the facets in `s`.

## Main results

* `TauCeti.Toric.IsDelzant.surjective_linearCombination`: the normals of a Delzant polytope
  generate the lattice.
* `TauCeti.Toric.continuous_facetTorusHom`: the homomorphism `π` is continuous.
* `TauCeti.Toric.coe_ker_facetTorusHom`: the kernel of `π` is the image of the kernel of `β_ℝ`.
* `TauCeti.Toric.isConnected_ker_facetTorusHom`,
  `TauCeti.Toric.IsDelzant.isConnected_ker_facetTorusHom`: the kernel of `π` is connected.
* `TauCeti.Toric.surjective_facetTorusHom`, `TauCeti.Toric.IsDelzant.surjective_facetTorusHom`:
  `π` is surjective.
* `TauCeti.Toric.exists_facetTorusHom_eq`: every element of `V / p i(N)` is the image under `π`
  of the classes of real angles.
* `TauCeti.Toric.eq_zero_of_mem_ker_facetTorusHom`: the kernel of `π` meets the coordinate
  subtorus of a lattice basis of normals trivially.
* `TauCeti.Toric.mem_faceSubtorus_iff_exists_facetTorusHom_eq`: the face subtorus of `s` is the
  image under `π` of the angles supported on `s`.
* `TauCeti.Toric.faceSubtorus_eq_bot_iff`, `TauCeti.Toric.faceSubtorus_eq_top_iff`: for a
  countable lattice, the face subtorus is trivial exactly when its normals vanish, and is the
  whole torus exactly when they span `V`.
* `TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`: a Delzant polytope has a point on no
  facet.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  (i : N →+ V) (u : ι → N)

/-! ### The lattice map and its real extension -/

variable {i u}

/-- If the normals generate the lattice and the lattice spans `V`, the real extension `β_ℝ` of
the lattice map is surjective. -/
theorem surjective_linearCombination_real (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff,
    ← hi, Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  obtain ⟨k, rfl⟩ := hu n
  rw [← Fintype.linearCombination_intCast (R := ℝ), ← Fintype.range_linearCombination]
  exact LinearMap.mem_range_self _ _

/-- If the normals generate the lattice and the lattice spans `V`, the kernel `𝔫` of `β_ℝ` has
dimension `#ι - dim V`. -/
theorem finrank_ker_linearCombination_real_add_finrank (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    Module.finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) +
      Module.finrank ℝ V = Fintype.card ι := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination ℝ fun j ↦ i (u j))
  rw [LinearMap.range_eq_top.2 (surjective_linearCombination_real hi hu), finrank_top,
    Module.finrank_fintype_fun_eq_card] at h
  omega

/-! ### The homomorphism of tori -/

variable (i u) (p : ℝ)

/-- The homomorphism of quotient groups `(ℝ / pℤ)^ι → V / p i(N)` induced by the normals `u`,
`[t] ↦ [∑ j, t j • i (u j)]`. For `p ≠ 0` and an integral lattice `i` it is a homomorphism of
tori. -/
def facetTorusHom : (ι → AddCircle p) →+ V ⧸ (p • i).range :=
  ∑ j, (QuotientAddGroup.map (AddSubgroup.zmultiples p) (p • i).range
      (LinearMap.toSpanSingleton ℝ V (i (u j))).toAddMonoidHom
      (AddSubgroup.zmultiples_le.2 ⟨u j, by simp⟩)).comp (Pi.evalAddMonoidHom _ j)

/-- The homomorphism `facetTorusHom` on classes of real vectors. -/
@[simp]
theorem facetTorusHom_coe (t : ι → ℝ) :
    facetTorusHom i u p (fun j ↦ (t j : AddCircle p)) =
      ((Fintype.linearCombination ℝ (fun j ↦ i (u j)) t : V) : V ⧸ (p • i).range) := by
  simp [facetTorusHom, Fintype.linearCombination_apply, QuotientAddGroup.mk_sum]

/-- The homomorphism `facetTorusHom` is continuous. -/
theorem continuous_facetTorusHom [TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul ℝ V] : Continuous (facetTorusHom i u p) := by
  simp only [facetTorusHom, AddMonoidHom.coe_finsetSum, Finset.sum_fn]
  refine continuous_finsetSum _ fun j _ ↦ ?_
  rw [AddMonoidHom.coe_comp]
  refine Continuous.comp ?_ (continuous_apply j)
  rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
  exact QuotientAddGroup.continuous_mk.comp (continuous_id.smul continuous_const)

variable {i u p}

/-- **The kernel torus.** If the normals generate the lattice, the kernel of the homomorphism
`(ℝ / pℤ)^ι → V / p i(N)` is the image of the kernel `𝔫` of `β_ℝ`. For `p ≠ 0` and an integral
lattice `i` this is a subtorus. -/
theorem coe_ker_facetTorusHom (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    ((facetTorusHom i u p).ker : Set (ι → AddCircle p)) =
      (fun (t : ι → ℝ) j ↦ (t j : AddCircle p)) ''
        LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j)) := by
  ext θ
  constructor
  · intro hθ
    choose t ht using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
    obtain rfl : (fun j ↦ (t j : AddCircle p)) = θ := funext ht
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, facetTorusHom_coe,
      QuotientAddGroup.eq_zero_iff] at hθ
    obtain ⟨n, hn⟩ := hθ
    obtain ⟨k, rfl⟩ := hu n
    refine ⟨t - p • fun j ↦ (k j : ℝ), ?_, funext fun j ↦ ?_⟩
    · rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul,
        Fintype.linearCombination_intCast, ← hn, AddMonoidHom.smul_apply, sub_self]
    · simp only [Pi.sub_apply, Pi.smul_apply]
      rw [QuotientAddGroup.mk_sub, sub_eq_self, AddCircle.coe_eq_zero_iff]
      exact ⟨k j, by simp [mul_comm]⟩
  · rintro ⟨t, ht, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker] at ht
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, facetTorusHom_coe, ht, QuotientAddGroup.mk_zero]

/-- **The kernel torus is connected.** If the normals generate the lattice, the kernel of the
homomorphism `(ℝ / pℤ)^ι → V / p i(N)` is connected. -/
theorem isConnected_ker_facetTorusHom
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    IsConnected ((facetTorusHom i u p).ker : Set (ι → AddCircle p)) := by
  rw [coe_ker_facetTorusHom hu]
  exact ((Submodule.convex _).isConnected ⟨0, Submodule.zero_mem _⟩).image _
    (continuous_pi fun j ↦ (AddCircle.continuous_mk' p).comp (continuous_apply j)).continuousOn

/-- If the normals generate the lattice and the lattice spans `V`, every element of
`V / p i(N)` is the class `facetTorusHom [θ]` of some real angles `θ`. -/
theorem exists_facetTorusHom_eq (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) (q : V ⧸ (p • i).range) :
    ∃ θ : ι → ℝ, facetTorusHom i u p (fun j ↦ (θ j : AddCircle p)) = q := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, rfl⟩ := surjective_linearCombination_real hi hu v
  exact ⟨t, facetTorusHom_coe i u p t⟩

/-- If the normals generate the lattice and the lattice spans `V`, the homomorphism
`(ℝ / pℤ)^ι → V / p i(N)` is surjective. -/
theorem surjective_facetTorusHom (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    Function.Surjective (facetTorusHom i u p) :=
  fun q ↦ let ⟨_, h⟩ := exists_facetTorusHom_eq hi hu q; ⟨_, h⟩

/-- **The kernel torus meets a coordinate subtorus of a lattice basis trivially.** Suppose that
the normals `u j` with `j ∈ s` form a basis of the integral lattice `N`. An element of the kernel
of `(ℝ / pℤ)^ι → V / p i(N)` whose coordinates outside `s` vanish is zero. -/
theorem eq_zero_of_mem_ker_facetTorusHom (hi : IsIntegralLattice i) {s : Set ι}
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) {θ : ι → AddCircle p}
    (hθ : θ ∈ (facetTorusHom i u p).ker) (hθs : ∀ j ∉ s, θ j = 0) : θ = 0 := by
  classical
  obtain ⟨b, hb⟩ := hs
  choose t ht using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
  -- Lift `θ` to angles supported in `s`.
  set t' : ι → ℝ := fun j ↦ if j ∈ s then t j else 0 with ht'
  have hθt' : θ = fun j ↦ (t' j : AddCircle p) := funext fun j ↦ by
    by_cases hj : j ∈ s
    · simp [t', hj, ht]
    · simp [t', hj, hθs j hj]
  rw [hθt', AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff] at hθ
  obtain ⟨n, hn⟩ := hθ
  -- Comparing coefficients in the real basis `i (u j)`, `j ∈ s`, of `V` gives `t j ∈ pℤ`.
  have hcoeff : ∀ j : s, t j = p * b.repr n j := by
    have hli := hi.linearIndependent_basis b
    simp only [hb] at hli
    have hsum : ∑ j : s, (t j - p * b.repr n j) • i (u j) = 0 := by
      have h1 : Fintype.linearCombination ℝ (fun j ↦ i (u j)) t' = ∑ j : s, t j • i (u j) := by
        rw [Fintype.linearCombination_apply]
        simp only [t', ite_smul, zero_smul]
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype _ (by simp) fun j ↦ t j • i (u j)
      have h2 : (p • i) n = ∑ j : s, (p * b.repr n j) • i (u j) := by
        conv_lhs => rw [← b.sum_repr n]
        simp only [AddMonoidHom.smul_apply, map_sum, map_zsmul, hb, mul_smul,
          Int.cast_smul_eq_zsmul]
        exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, hn, sub_self]
    intro j
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ hsum j)
  funext j
  by_cases hj : j ∈ s
  · rw [Pi.zero_apply, ← ht, hcoeff ⟨j, hj⟩, AddCircle.coe_eq_zero_iff]
    exact ⟨b.repr n ⟨j, hj⟩, by simp [mul_comm]⟩
  · exact hθs j hj

/-! ### Face subtori -/

section FaceSubtorus

omit [Fintype ι]

variable (i u p) in
/-- The *face subtorus* of a set `s` of facets: the image in `V / p i(N)` of the real span of the
normals `i (u j)`, `j ∈ s`. For `p ≠ 0` and an integral lattice `i`, these normals are lattice
vectors, so this is the subtorus of the torus `V / p i(N)` whose Lie algebra is their span. -/
def faceSubtorus (s : Set ι) : AddSubgroup (V ⧸ (p • i).range) :=
  (Submodule.span ℝ ((fun j ↦ i (u j)) '' s)).toAddSubgroup.map (QuotientAddGroup.mk' _)

/-- A class lies in the face subtorus of `s` exactly when it is the class of a vector in the span
of the normals `i (u j)`, `j ∈ s`. -/
@[simp]
theorem mem_faceSubtorus {s : Set ι} {q : V ⧸ (p • i).range} :
    q ∈ faceSubtorus i u p s ↔
      ∃ v ∈ Submodule.span ℝ ((fun j ↦ i (u j)) '' s), (v : V ⧸ (p • i).range) = q := by
  simp [faceSubtorus]

variable [Fintype ι] in
/-- The face subtorus of `s` is the image, under the homomorphism `facetTorusHom`, of the angles
supported on `s`. -/
theorem mem_faceSubtorus_iff_exists_facetTorusHom_eq {s : Set ι} {q : V ⧸ (p • i).range} :
    q ∈ faceSubtorus i u p s ↔
      ∃ t : ι → ℝ, (∀ j ∉ s, t j = 0) ∧ facetTorusHom i u p (fun j ↦ (t j : AddCircle p)) = q := by
  simp only [mem_faceSubtorus, Finsupp.mem_span_image_iff_linearCombination, facetTorusHom_coe]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    refine ⟨l, fun j hj ↦ Finsupp.notMem_support_iff.1 fun h ↦ hj (hl h), ?_⟩
    rw [← Finsupp.linearCombination_eq_fintype_linearCombination_apply]
    simp
  · rintro ⟨t, ht, rfl⟩
    refine ⟨_, ⟨(Finsupp.linearEquivFunOnFinite ℝ ℝ ι).symm t, fun j hj ↦ ?_, rfl⟩,
      congrArg _ (Finsupp.linearCombination_eq_fintype_linearCombination_apply ℝ _ t)⟩
    by_contra h
    exact (Finsupp.mem_support_iff.1 hj) (by simpa using ht j h)

variable (i u p) in
/-- Face subtori grow with the set of facets. -/
theorem faceSubtorus_mono : Monotone (faceSubtorus i u p) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono
    (Submodule.span_mono (image_mono h)))

variable (i u p) in
@[simp]
theorem faceSubtorus_empty : faceSubtorus i u p ∅ = ⊥ := by
  simp [faceSubtorus]

/-- **Trivial face subtori.** For a countable lattice, the face subtorus of `s` is trivial exactly
when the normals `i (u j)`, `j ∈ s`, vanish. -/
theorem faceSubtorus_eq_bot_iff [Countable N] {s : Set ι} :
    faceSubtorus i u p s = ⊥ ↔ ∀ j ∈ s, i (u j) = 0 := by
  refine ⟨fun h j hj ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    -- Every multiple `r • i (u j)` lies in `p i(N)`, so `r ↦ r • i (u j)` injects `ℝ` into it.
    have hmem (r : ℝ) : r • i (u j) ∈ (p • i).range := by
      have hq : ((r • i (u j) : V) : V ⧸ (p • i).range) ∈ faceSubtorus i u p s :=
        mem_faceSubtorus.2 ⟨_, Submodule.smul_mem _ r (Submodule.subset_span ⟨j, hj, rfl⟩), rfl⟩
      rwa [h, AddSubgroup.mem_bot, QuotientAddGroup.eq_zero_iff] at hq
    choose n hn using hmem
    have hinj : Function.Injective n := fun r r' hr ↦
      smul_left_injective ℝ hne (by simpa only [← hn] using congrArg (p • i) hr)
    have := hinj.countable
    exact Cardinal.not_countable_real countable_univ
  · rw [faceSubtorus, Submodule.span_eq_bot.2 (by rintro _ ⟨j, hj, rfl⟩; exact h j hj)]
    simp

/-- **Face subtori filling the torus.** For a countable lattice, the face subtorus of `s` is the
whole of `V / p i(N)` exactly when the normals `i (u j)`, `j ∈ s`, span `V`. -/
theorem faceSubtorus_eq_top_iff [Countable N] {s : Set ι} :
    faceSubtorus i u p s = ⊤ ↔ Submodule.span ℝ ((fun j ↦ i (u j)) '' s) = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    -- A nonzero functional `f` vanishing on the span takes each of its values on the countable
    -- group `p i(N)`, which is impossible.
    obtain ⟨f, hf, hfW⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hsub : range f ⊆ range fun n ↦ f ((p • i) n) := by
      rintro _ ⟨v, rfl⟩
      obtain ⟨w, hw, hwv⟩ := mem_faceSubtorus.1 (h ▸ AddSubgroup.mem_top (v : V ⧸ (p • i).range))
      obtain ⟨n, hn⟩ := QuotientAddGroup.eq.1 hwv
      have hfw : f w = 0 := LinearMap.le_ker_iff_map.2 hfW hw
      exact ⟨n, by simp only [hn, map_add, map_neg, hfw, neg_zero, zero_add]⟩
    refine Cardinal.not_countable_real ?_
    rw [← range_eq_univ.2 (LinearMap.surjective hf)]
    exact (countable_range _).mono hsub
  · rw [eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact mem_faceSubtorus.2 ⟨v, h ▸ Submodule.mem_top, rfl⟩

end FaceSubtorus

/-! ### Delzant polytopes -/

section Delzant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

namespace IsDelzant

variable (hΔ : IsDelzant i u c)
include hΔ

/-- The facet normals of a Delzant polytope generate the lattice: the normals at any vertex
already form a basis of it. -/
theorem surjective_linearCombination :
    Function.Surjective (Fintype.linearCombination ℤ u) := by
  obtain ⟨x, hx⟩ := hΔ.extremePoints_nonempty
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 (hΔ.isSmoothVertex x hx)
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← b.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j, (hb j).symm⟩

/-- The kernel of the homomorphism `facetTorusHom` of a Delzant polytope is connected. -/
theorem isConnected_ker_facetTorusHom (p : ℝ) :
    IsConnected ((facetTorusHom i u p).ker : Set (ι → AddCircle p)) :=
  Toric.isConnected_ker_facetTorusHom hΔ.surjective_linearCombination

/-- The homomorphism `facetTorusHom` of a Delzant polytope is surjective. -/
theorem surjective_facetTorusHom (hi : IsIntegralLattice i) (p : ℝ) :
    Function.Surjective (facetTorusHom i u p) :=
  Toric.surjective_facetTorusHom hi.span_range_eq_top hΔ.surjective_linearCombination

/-- The kernel `𝔫` of `β_ℝ` for a Delzant polytope with `d` facets in a space of dimension `n`
has dimension `d - n`. -/
theorem finrank_ker_linearCombination_real_add_finrank (hi : IsIntegralLattice i) :
    Module.finrank ℝ (LinearMap.ker (Fintype.linearCombination ℝ fun j ↦ i (u j))) +
      Module.finrank ℝ V = Fintype.card ι :=
  Toric.finrank_ker_linearCombination_real_add_finrank hi.span_range_eq_top
    hΔ.surjective_linearCombination

omit [FiniteDimensional ℝ V] [Fintype ι] in
open Filter Topology in
/-- **A Delzant polytope has a point on no facet.** Some point of the polytope satisfies every
facet inequality strictly. -/
theorem exists_activeSet_eq_empty [Finite ι] (hi : IsIntegralLattice i) :
    ∃ y ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c y = ∅ := by
  classical
  have := Fintype.ofFinite ι
  have := hi.finiteDimensional
  obtain ⟨v, hv⟩ := hΔ.extremePoints_nonempty
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 (hΔ.isSmoothVertex v hv)
  -- Move from `v` along a functional `w` that is `1` on the active normals; for small positive
  -- times every constraint is strict. Take for `w` the real extension of the integral character
  -- `n ↦ Σ_j b.coord j n`, which is `1` on the lattice basis of active normals.
  let w : StrongDual ℝ V :=
    LinearMap.toContinuousLinearMap (hi.realCharacter (∑ j, (b.coord j).toAddMonoidHom))
  have hw (j : ι) (hj : j ∈ activeSet (facetPairing i u) c v) : w (i (u j)) = 1 := by
    simp [w, ← hb ⟨j, hj⟩, Finsupp.single_apply]
  have hev (j : ι) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c j < (v + ε • w) (i (u j)) := by
    by_cases hj : j ∈ activeSet (facetPairing i u) c v
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hvj : v (i (u j)) = c j := by simpa using hj
      simp [hvj, hw j hj, hε]
    · have hlt : c j < v (i (u j)) :=
        (mem_facetPolyhedron.1 (extremePoints_subset hv) j).lt_of_ne fun h ↦
          hj (by simpa using h.symm)
      have hT : Tendsto (fun ε : ℝ ↦ (v + ε • w) (i (u j))) (𝓝[>] 0) (𝓝 (v (i (u j)))) := by
        have hc : Continuous fun ε : ℝ ↦ (v + ε • w) (i (u j)) := by
          simp only [add_apply, smul_apply, smul_eq_mul]
          fun_prop
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact hT.eventually_const_lt hlt
  obtain ⟨ε, hε⟩ := (eventually_all.2 hev).exists
  refine ⟨v + ε • w, mem_facetPolyhedron.2 fun j ↦ (hε j).le, eq_empty_iff_forall_notMem.2
    fun j hj ↦ (hε j).ne' ?_⟩
  simpa using hj

end IsDelzant

end Delzant

end TauCeti.Toric
