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
import Mathlib.LinearAlgebra.Dimension.RankNullity
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

For an integral lattice, the kernel of `π` meets the coordinate subtorus spanned by the
constraints active at a smooth vertex only in `0`
(`TauCeti.Toric.IsSmoothVertex.eq_zero_of_mem_ker_facetTorusHom`): those normals form a basis of
`N`, so a real combination of them lies in `p i(N)` only if its coefficients lie in `pℤ`. Since
the constraints active at any point of a Delzant polytope are active at some vertex, the same
holds for the coordinate subtorus of every face
(`TauCeti.Toric.IsDelzant.eq_zero_of_mem_ker_facetTorusHom`). This is why `N_Δ` acts freely on
the level set of the Delzant construction, where the stabilizers of the torus `(ℝ / 2πℤ)^ι` are
exactly these coordinate subtori.

## Main definitions

* `TauCeti.Toric.facetTorusHom i u p`: the homomorphism `(ℝ / pℤ)^ι → V / p i(N)`,
  `[t] ↦ [∑ j, t j • i (u j)]`, a homomorphism of tori when `p ≠ 0`.

## Main results

* `TauCeti.Toric.IsDelzant.surjective_linearCombination`: the normals of a Delzant polytope
  generate the lattice.
* `TauCeti.Toric.continuous_facetTorusHom`: the homomorphism `π` is continuous.
* `TauCeti.Toric.coe_ker_facetTorusHom`: the kernel of `π` is the image of the kernel of `β_ℝ`.
* `TauCeti.Toric.isConnected_ker_facetTorusHom`,
  `TauCeti.Toric.IsDelzant.isConnected_ker_facetTorusHom`: the kernel of `π` is connected.
* `TauCeti.Toric.surjective_facetTorusHom`, `TauCeti.Toric.IsDelzant.surjective_facetTorusHom`:
  `π` is surjective.
* `TauCeti.Toric.IsSmoothVertex.eq_zero_of_mem_ker_facetTorusHom`,
  `TauCeti.Toric.IsDelzant.eq_zero_of_mem_ker_facetTorusHom`: the kernel of `π` meets the
  coordinate subtorus of a vertex, and of every face of a Delzant polytope, trivially.

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

/-- If the normals generate the lattice and the lattice spans `V`, the homomorphism
`(ℝ / pℤ)^ι → V / p i(N)` is surjective. -/
theorem surjective_facetTorusHom (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    Function.Surjective (facetTorusHom i u p) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, rfl⟩ := surjective_linearCombination_real hi hu v
  exact ⟨_, facetTorusHom_coe i u p t⟩

/-! ### Delzant polytopes -/

section Delzant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

omit [FiniteDimensional ℝ V] in
/-- **The kernel torus meets the coordinate subtorus of a smooth vertex trivially.** For an
integral lattice and a smooth vertex `v`, an element of the kernel of
`(ℝ / pℤ)^ι → V / p i(N)` whose coordinates vanish off the constraints active at `v` is zero: the
normals active at `v` form a basis of `N`, so a combination of them with real coefficients lies
in `p i(N)` only if every coefficient lies in `pℤ`. -/
theorem IsSmoothVertex.eq_zero_of_mem_ker_facetTorusHom (hi : IsIntegralLattice i)
    {v : StrongDual ℝ V} (hv : IsSmoothVertex i u c v) {p : ℝ} {θ : ι → AddCircle p}
    (hθ : θ ∈ (facetTorusHom i u p).ker)
    (hA : ∀ j ∉ activeSet (facetPairing i u) c v, θ j = 0) : θ = 0 := by
  classical
  set A := activeSet (facetPairing i u) c v
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hv
  -- Lift `θ` to real coordinates vanishing off `A`.
  choose s hs using fun j ↦ QuotientAddGroup.mk_surjective (θ j)
  set t : ι → ℝ := fun j ↦ if j ∈ A then s j else 0
  have hθt : θ = fun j ↦ (t j : AddCircle p) := funext fun j ↦ by
    by_cases hj : j ∈ A
    · simp [t, hj, ← hs j]
    · simp [t, hj, hA j hj]
  rw [hθt, AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff] at hθ
  obtain ⟨n, hn⟩ := hθ
  -- In the basis `b` of `N`, the relation `∑ⱼ tⱼ i(uⱼ) = p i(n)` compares coefficients.
  have hsum : ∑ j, t j • i (u j) = ∑ a : A, t a • i (u a) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ A), add_eq_left]
    exact Finset.sum_eq_zero fun j _ ↦ by simp [t, j.2]
  have hin : (p • i) n = ∑ a : A, (p * b.repr n a) • i (u a) := by
    conv_lhs => rw [AddMonoidHom.smul_apply, ← b.sum_repr n, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [map_zsmul, hb, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
  have hrel : ∑ a : A, (t a - p * b.repr n a) • i (b a) = 0 := by
    simp only [hb, sub_smul, Finset.sum_sub_distrib, ← hsum, ← hin]
    rw [hn, Fintype.linearCombination_apply, sub_self]
  have hcoef := Fintype.linearIndependent_iff.1 (hi.linearIndependent_basis b) _ hrel
  rw [hθt]
  funext j
  by_cases hj : j ∈ A
  · rw [Pi.zero_apply, AddCircle.coe_eq_zero_iff]
    refine ⟨b.repr n ⟨j, hj⟩, ?_⟩
    have hj' := hcoef ⟨j, hj⟩
    simp only [t, hj, ite_true, sub_eq_zero] at hj' ⊢
    rw [zsmul_eq_mul, hj', mul_comm]
  · simp [t, hj]

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

/-- **The kernel torus meets the coordinate subtorus of every face trivially.** For a Delzant
polytope in an integral lattice and a point `x` of the polytope, an element of the kernel of
`(ℝ / pℤ)^ι → V / p i(N)` whose coordinates vanish off the constraints active at `x` is zero. -/
theorem eq_zero_of_mem_ker_facetTorusHom (hi : IsIntegralLattice i) {x : StrongDual ℝ V}
    (hx : x ∈ facetPolyhedron i u c) {p : ℝ} {θ : ι → AddCircle p}
    (hθ : θ ∈ (facetTorusHom i u p).ker)
    (hA : ∀ j ∉ activeSet (facetPairing i u) c x, θ j = 0) : θ = 0 := by
  obtain ⟨v, hv, hxv⟩ := hΔ.exists_mem_extremePoints_activeSet_subset hx
  exact (hΔ.isSmoothVertex v hv).eq_zero_of_mem_ker_facetTorusHom hi hθ
    fun j hj ↦ hA j fun hjx ↦ hj (hxv hjx)

end IsDelzant

end Delzant

end TauCeti.Toric
