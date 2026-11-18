/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic
public import TauCeti.Geometry.Toric.Delzant.Basic

import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dual.Lemmas
import TauCeti.Algebra.AddCircle
import TauCeti.LinearAlgebra.Basis.Basic
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
* `TauCeti.Toric.IsSmoothVertex.vertexTorusHom`: at a smooth vertex `x` with active facets `A`,
  the homomorphism `(ℝ / pℤ)^ι → (ℝ / pℤ)^A` reading `π` in the lattice basis of the active
  normals.
* `TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv`: the residual torus `(ℝ / pℤ)^ι / ker π` as the
  standard torus `(ℝ / pℤ)^A`, sending `φ` to the class of its extension by zero.

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
* `TauCeti.Toric.facetTorusHom_comp_equiv`, `TauCeti.Toric.ker_facetTorusHom_comp_left`:
  relabelling the facets relabels the angles, and a compatible change of lattice does not change
  the kernel of `π`.
* `TauCeti.Toric.eq_zero_of_mem_ker_facetTorusHom`: the kernel of `π` meets the coordinate
  subtorus of a lattice basis of normals trivially.
* `TauCeti.Toric.mem_ker_facetTorusHom_iff_of_basis`,
  `TauCeti.Toric.IsSmoothVertex.ker_vertexTorusHom`: the kernel of `π` in the coordinates of a
  lattice basis, and at a smooth vertex.
* `TauCeti.Toric.exists_basis_iff_forall_eq_zero_of_mem_ker_facetTorusHom`: conversely, for
  `p ≠ 0`, normals spanning `V` whose coordinate subtorus meets the kernel of `π` trivially form a
  lattice basis.
* `TauCeti.Toric.IsIntegralLattice.isClosed_ker_facetTorusHom`: for an integral lattice, the
  kernel of `π` is closed.
* `TauCeti.Toric.mem_faceSubtorus_iff_exists_facetTorusHom_eq`: the face subtorus of `s` is the
  image under `π` of the angles supported on `s`.
* `TauCeti.Toric.faceSubtorus_eq_bot_iff`, `TauCeti.Toric.faceSubtorus_eq_top_iff`: for a
  countable lattice, the face subtorus is trivial exactly when its normals vanish, and is the
  whole torus exactly when they span `V`.

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
    obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
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

/-- If the normals span `V` over `ℝ`, every element of `V / p i(N)` is the class
`facetTorusHom [θ]` of some real angles `θ`. -/
theorem exists_facetTorusHom_eq (hu : Submodule.span ℝ (Set.range fun j ↦ i (u j)) = ⊤)
    (q : V ⧸ (p • i).range) :
    ∃ θ : ι → ℝ, facetTorusHom i u p (fun j ↦ (θ j : AddCircle p)) = q := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨t, rfl⟩ : v ∈ LinearMap.range (Fintype.linearCombination ℝ fun j ↦ i (u j)) := by
    rw [Fintype.range_linearCombination, hu]
    exact Submodule.mem_top
  exact ⟨t, facetTorusHom_coe i u p t⟩

/-- If the normals generate the lattice and the lattice spans `V`, the homomorphism
`(ℝ / pℤ)^ι → V / p i(N)` is surjective. -/
theorem surjective_facetTorusHom (hi : Submodule.span ℝ (Set.range i) = ⊤)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) :
    Function.Surjective (facetTorusHom i u p) := by
  have hspan : Submodule.span ℝ (Set.range fun j ↦ i (u j)) = ⊤ := by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    exact surjective_linearCombination_real hi hu
  exact fun q ↦ let ⟨_, h⟩ := exists_facetTorusHom_eq hspan q; ⟨_, h⟩

/-- **The kernel torus in lattice coordinates.** Let `b` be a basis of the integral lattice `N`,
and write `u j = Σ_k a_(j k) b k` with integers `a_(j k)`. An element `θ` of `(ℝ / pℤ)^ι` lies in
the kernel of `(ℝ / pℤ)^ι → V / p i(N)` exactly when `Σ_j a_(j k) θ_j = 0` in `ℝ / pℤ` for every
`k`: these are the coordinates of `facetTorusHom θ` in the basis `i ∘ b`. -/
theorem mem_ker_facetTorusHom_iff_of_basis (hi : IsIntegralLattice i) {κ : Type*} [Finite κ]
    (b : Module.Basis κ ℤ N) {θ : ι → AddCircle p} :
    θ ∈ (facetTorusHom i u p).ker ↔ ∀ k, ∑ j, b.repr (u j) k • θ j = 0 := by
  have := Fintype.ofFinite κ
  obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
  -- Read `Σ_j t_j i(u_j)` and the lattice points `p i(n)` in the real basis `i ∘ b` of `V`.
  set B := hi.isBaseChange.basis b
  have hrepr (n : N) (k : κ) : B.repr (i n) k = b.repr n k := by
    simpa using hi.isBaseChange.basis_repr_comp_apply b n k
  have hx (k : κ) : B.repr (Fintype.linearCombination ℝ (fun j ↦ i (u j)) t) k =
      ∑ j, (b.repr (u j) k : ℝ) * t j := by
    simp [Fintype.linearCombination_apply, hrepr, mul_comm]
  have hcoe (k : κ) : ∑ j, b.repr (u j) k • (t j : AddCircle p) =
      ((∑ j, (b.repr (u j) k : ℝ) * t j : ℝ) : AddCircle p) := by
    simp [QuotientAddGroup.mk_sum, ← zsmul_eq_mul, QuotientAddGroup.mk_zsmul]
  simp only [hcoe, AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff,
    AddMonoidHom.mem_range, AddMonoidHom.smul_apply, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨n, hn⟩ k
    refine ⟨b.repr n k, ?_⟩
    rw [← hx, ← hn, map_smul, Finsupp.smul_apply, hrepr]
    simp [zsmul_eq_mul, mul_comm]
  · intro h
    choose m hm using h
    refine ⟨∑ k, m k • b k, B.ext_elem fun k ↦ ?_⟩
    rw [hx, ← hm, map_smul, Finsupp.smul_apply, hrepr, b.repr_sum_self]
    simp [zsmul_eq_mul, mul_comm]

/-- **The kernel torus meets a coordinate subtorus of a lattice basis trivially.** Suppose that
the normals `u j` with `j ∈ s` form a basis of the integral lattice `N`. An element of the kernel
of `(ℝ / pℤ)^ι → V / p i(N)` whose coordinates outside `s` vanish is zero. -/
theorem eq_zero_of_mem_ker_facetTorusHom (hi : IsIntegralLattice i) {s : Set ι}
    (hs : ∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) {θ : ι → AddCircle p}
    (hθ : θ ∈ (facetTorusHom i u p).ker) (hθs : ∀ j ∉ s, θ j = 0) : θ = 0 := by
  obtain ⟨b, hb⟩ := hs
  rw [mem_ker_facetTorusHom_iff_of_basis hi b] at hθ
  funext j
  by_cases hj : j ∈ s
  · -- In the basis `b` of normals indexed by `s`, the `j`-th coordinate equation reads `θ j = 0`.
    exact (b.sum_repr_smul_eq_of_forall_notMem hb hθs ⟨j, hj⟩).symm.trans (hθ ⟨j, hj⟩)
  · exact hθs j hj

/-- If the only element of the kernel of `(ℝ / pℤ)^ι → V / p i(N)` supported on `s` is zero, then
real angles supported on `s` whose combination of normals lies in `p i(N)` lie in `pℤ`. -/
private theorem exists_eq_intCast_mul_of_forall_mem_ker {s : Set ι}
    (h : ∀ θ ∈ (facetTorusHom i u p).ker, (∀ j ∉ s, θ j = 0) → θ = 0) {t : ι → ℝ}
    (hts : ∀ j ∉ s, t j = 0)
    (ht : Fintype.linearCombination ℝ (fun j ↦ i (u j)) t ∈ (p • i).range) (j : ι) :
    ∃ k : ℤ, t j = k * p := by
  have h0 := h (fun j ↦ (t j : AddCircle p))
    (by rwa [AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff])
    fun j hj ↦ by rw [hts j hj, AddCircle.coe_zero]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff p).1 (congrFun h0 j)
  exact ⟨k, by rw [← hk, zsmul_eq_mul]⟩

/-- For `p ≠ 0`, if the only element of the kernel of `(ℝ / pℤ)^ι → V / p i(N)` supported on `s`
is zero, then the normals in `s` are linearly independent: a real relation `r` among them would
give the elements `[t • r]` of the kernel for all real `t`. -/
private theorem linearIndepOn_of_forall_mem_ker (hp : p ≠ 0) {s : Set ι}
    (h : ∀ θ ∈ (facetTorusHom i u p).ker, (∀ j ∉ s, θ j = 0) → θ = 0) :
    LinearIndepOn ℤ u s := by
  have hR : LinearIndepOn ℝ (fun j ↦ i (u j)) s := by
    refine linearIndepOn_iff.2 fun l hl hl0 ↦ Finsupp.ext fun j ↦ by_contra fun hj ↦ ?_
    have hlc : Fintype.linearCombination ℝ (fun j ↦ i (u j)) l = 0 := by
      simpa [hl0] using
        (Finsupp.linearCombination_eq_fintype_linearCombination_apply ℝ (fun j ↦ i (u j)) ⇑l).symm
    -- Rescale the relation so that its `j`-th coefficient is `p / 2`, which is not in `pℤ`.
    obtain ⟨k, hk⟩ := exists_eq_intCast_mul_of_forall_mem_ker h (t := (p / (2 * l j)) • ⇑l)
      (fun j' hj' ↦ by simp [(Finsupp.mem_supported' ℝ l).1 hl j' hj'])
      ⟨0, by simp [hlc]⟩ j
    have hj' : l j ≠ 0 := hj
    simp only [Pi.smul_apply, smul_eq_mul] at hk
    have h1 : p / 2 = k * p := by rw [← hk]; field_simp
    have h2 : (1 : ℝ) * p = 2 * k * p := by linarith
    have : (1 : ℤ) = 2 * k := by exact_mod_cast mul_right_cancel₀ hp h2
    omega
  exact LinearIndependent.of_comp i.toIntLinearMap (hR.restrict_scalars' ℤ)

/-- For `p ≠ 0`, if the normals in `s` span `V` over `ℝ` and the only element of the kernel of
`(ℝ / pℤ)^ι → V / p i(N)` supported on `s` is zero, then the normals in `s` generate `N`: the
real coordinates of a lattice vector in these normals are integers. -/
private theorem span_eq_top_of_forall_mem_ker (hi : IsIntegralLattice i) (hp : p ≠ 0)
    {s : Set ι} (hs : Submodule.span ℝ ((fun j ↦ i (u j)) '' s) = ⊤)
    (h : ∀ θ ∈ (facetTorusHom i u p).ker, (∀ j ∉ s, θ j = 0) → θ = 0) :
    Submodule.span ℤ (u '' s) = ⊤ := by
  classical
  refine eq_top_iff.2 fun n _ ↦ ?_
  obtain ⟨l, hl, hln⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).1
    (hs ▸ Submodule.mem_top : i n ∈ Submodule.span ℝ ((fun j ↦ i (u j)) '' s))
  have hls := (Finsupp.mem_supported' ℝ l).1 hl
  have hlc : Fintype.linearCombination ℝ (fun j ↦ i (u j)) l = i n := by
    simpa [hln] using
      (Finsupp.linearCombination_eq_fintype_linearCombination_apply ℝ (fun j ↦ i (u j)) ⇑l).symm
  choose k hk using exists_eq_intCast_mul_of_forall_mem_ker h (t := p • ⇑l)
    (fun j hj ↦ by simp [hls j hj]) ⟨n, by rw [map_smul, hlc, AddMonoidHom.smul_apply]⟩
  have hlk (j : ι) : l j = k j := by
    have := hk j
    rw [Pi.smul_apply, smul_eq_mul, mul_comm] at this
    exact mul_right_cancel₀ hp this
  -- So `n` is the integral combination of the normals with the coefficients `k`, supported on `s`.
  have hn : n = Fintype.linearCombination ℤ u k := by
    refine hi.injective ?_
    rw [← Fintype.linearCombination_intCast (R := ℝ), ← hlc]
    exact congrArg _ (funext hlk)
  rw [hn, Fintype.linearCombination_apply]
  refine Submodule.sum_mem _ fun j _ ↦ ?_
  by_cases hj : j ∈ s
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  · rw [show k j = 0 by exact_mod_cast (hlk j).symm.trans (hls j hj), zero_smul]
    exact Submodule.zero_mem _

/-- **Lattice bases of normals, through the kernel torus.** Let `p ≠ 0` and suppose that the
normals `u j` with `j ∈ s` span `V` over `ℝ`. They form a basis of the integral lattice `N`
exactly when the only element of the kernel of `(ℝ / pℤ)^ι → V / p i(N)` whose coordinates
outside `s` vanish is zero. The forward direction is
`TauCeti.Toric.eq_zero_of_mem_ker_facetTorusHom`, which needs neither `p ≠ 0` nor the spanning
hypothesis. -/
theorem exists_basis_iff_forall_eq_zero_of_mem_ker_facetTorusHom (hi : IsIntegralLattice i)
    (hp : p ≠ 0) {s : Set ι} (hs : Submodule.span ℝ ((fun j ↦ i (u j)) '' s) = ⊤) :
    (∃ b : Module.Basis s ℤ N, ∀ j, b j = u j) ↔
      ∀ θ ∈ (facetTorusHom i u p).ker, (∀ j ∉ s, θ j = 0) → θ = 0 := by
  refine ⟨fun hb θ hθ hθs ↦ eq_zero_of_mem_ker_facetTorusHom hi hb hθ hθs, fun h ↦ ?_⟩
  have hli := linearIndepOn_of_forall_mem_ker hp h
  have hspan : Submodule.span ℤ (Set.range fun j : s ↦ u j) = ⊤ := by
    rw [← Set.image_eq_range]
    exact span_eq_top_of_forall_mem_ker hi hp hs h
  exact ⟨Module.Basis.mk hli hspan.ge, Module.Basis.mk_apply hli hspan.ge⟩

/-! ### Changes of presentation -/

section Presentation

variable {ι' N' V' : Type*} [Fintype ι'] [AddCommGroup N'] [AddCommGroup V'] [Module ℝ V']
  {i' : N' →+ V'} {p : ℝ}

variable (i u p) in
/-- **Relabelling the facets.** Listing the normals along a bijection `e : ι' ≃ ι` turns the
homomorphism `(ℝ / pℤ)^ι → V / p i(N)` into its composite with the relabelling `θ ↦ θ ∘ e.symm`
of angles. -/
theorem facetTorusHom_comp_equiv (e : ι' ≃ ι) (θ : ι' → AddCircle p) :
    facetTorusHom i (u ∘ e) p θ = facetTorusHom i u p (θ ∘ e.symm) := by
  obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
  -- The relabelled angles are the classes of the relabelled representatives `t ∘ e.symm`.
  refine (facetTorusHom_coe i (u ∘ e) p t).trans (Eq.trans ?_ (facetTorusHom_coe i u p
    (t ∘ e.symm)).symm)
  simp only [Fintype.linearCombination_apply, Function.comp_apply]
  exact congrArg _ (Fintype.sum_equiv e _ _ fun j ↦ by simp)

/-- **Changing the lattice.** For a surjective map of lattices `f` and an injective linear map `g`
with `g ∘ i = i' ∘ f`, the homomorphism of tori of the mapped normals `f ∘ u` has the same kernel
as that of `u`. -/
theorem ker_facetTorusHom_comp_left {f : N → N'} {g : V →ₗ[ℝ] V'} (hf : Function.Surjective f)
    (hg : Function.Injective g) (hfg : ∀ n, g (i n) = i' (f n)) :
    (facetTorusHom i' (fun j ↦ f (u j)) p).ker = (facetTorusHom i u p).ker := by
  ext θ
  obtain ⟨t, rfl⟩ := AddCircle.exists_pi_coe_eq θ
  have hβ : Fintype.linearCombination ℝ (fun j ↦ i' (f (u j))) t =
      g (Fintype.linearCombination ℝ (fun j ↦ i (u j)) t) := by
    simp [Fintype.linearCombination_apply, map_sum, hfg]
  simp only [AddMonoidHom.mem_ker, facetTorusHom_coe, QuotientAddGroup.eq_zero_iff,
    AddMonoidHom.mem_range, AddMonoidHom.smul_apply, hβ]
  constructor
  · rintro ⟨n', hn'⟩
    obtain ⟨n, rfl⟩ := hf n'
    exact ⟨n, hg (by rw [map_smul, hfg, hn'])⟩
  · rintro ⟨n, hn⟩
    exact ⟨f n, by rw [← hn, map_smul, hfg]⟩

end Presentation

/-! ### Closedness of the kernel -/

section Closed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V}

/-- **The kernel torus is closed.** For an integral lattice `i`, the kernel of the homomorphism
`(ℝ / pℤ)^ι → V / p i(N)` is a closed subgroup; for `p ≠ 0` it is therefore a compact subgroup of
the torus `(ℝ / pℤ)^ι`. -/
theorem IsIntegralLattice.isClosed_ker_facetTorusHom (hi : IsIntegralLattice i) (u : ι → N)
    (p : ℝ) : IsClosed ((facetTorusHom i u p).ker : Set (ι → AddCircle p)) := by
  have h0 : IsClosed ({0} : Set (V ⧸ (p • i).range)) := by
    rw [← (QuotientAddGroup.isQuotientMap_mk _).isClosed_preimage]
    convert hi.isClosed_range_smul p using 1
    ext v
    simp [QuotientAddGroup.eq_zero_iff]
  exact h0.preimage (continuous_facetTorusHom i u p)

end Closed

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

/-! ### Smooth vertices -/

section SmoothVertex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V} {u : ι → N}
  {c : ι → ℝ} {x : StrongDual ℝ V}

/-- The facet normals generate the lattice as soon as the presentation has a smooth vertex: the
normals active there already form a basis of it. -/
theorem IsSmoothVertex.surjective_linearCombination (hx : IsSmoothVertex i u c x) :
    Function.Surjective (Fintype.linearCombination ℤ u) := by
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, eq_top_iff, ← hx.basis.span_eq]
  refine Submodule.span_mono ?_
  rintro _ ⟨j, rfl⟩
  exact ⟨j, (hx.basis_apply j).symm⟩

/-- At a smooth vertex of a presentation in an integral lattice, the real extension `β_ℝ` of the
lattice map is surjective. -/
theorem IsSmoothVertex.surjective_linearCombination_real (hx : IsSmoothVertex i u c x)
    (hi : IsIntegralLattice i) :
    Function.Surjective (Fintype.linearCombination ℝ fun j ↦ i (u j)) :=
  Toric.surjective_linearCombination_real hi.span_range_eq_top hx.surjective_linearCombination

namespace IsSmoothVertex

variable (hx : IsSmoothVertex i u c x)

variable (p) in
/-- The homomorphism `facetTorusHom` read in the coordinates of the lattice basis formed by the
normals active at a smooth vertex `x`: writing `u j = Σ_(k ∈ A) a_(j k) u_k`, it sends `θ` to
`(Σ_j a_(j k) θ_j)_(k ∈ A)`. Its kernel is the kernel torus
(`TauCeti.Toric.IsSmoothVertex.ker_vertexTorusHom`). -/
def vertexTorusHom : (ι → AddCircle p) →+ (activeSet (facetPairing i u) c x → AddCircle p) where
  toFun θ k := ∑ j, hx.basis.repr (u j) k • θ j
  map_zero' := by ext; simp
  map_add' θ θ' := by ext; simp [smul_add, Finset.sum_add_distrib]

@[simp]
theorem vertexTorusHom_apply (θ : ι → AddCircle p) (k : activeSet (facetPairing i u) c x) :
    hx.vertexTorusHom p θ k = ∑ j, hx.basis.repr (u j) k • θ j :=
  (rfl)

/-- The homomorphism `vertexTorusHom` is continuous. -/
theorem continuous_vertexTorusHom : Continuous (hx.vertexTorusHom p) :=
  continuous_pi fun _ ↦ continuous_finsetSum _ fun j _ ↦
    (continuous_zsmul _).comp (continuous_apply j)

/-- The kernel of `vertexTorusHom` is the kernel torus. -/
theorem ker_vertexTorusHom (hi : IsIntegralLattice i) :
    (hx.vertexTorusHom p).ker = (facetTorusHom i u p).ker := by
  ext θ
  rw [mem_ker_facetTorusHom_iff_of_basis hi hx.basis, AddMonoidHom.mem_ker, funext_iff]
  simp only [vertexTorusHom_apply, Pi.zero_apply]

/-- `vertexTorusHom` is the identity on the angles supported on the active facets: it sends the
extension by zero of `φ : (ℝ / pℤ)^A` back to `φ`. -/
@[simp]
theorem vertexTorusHom_extend (φ : activeSet (facetPairing i u) c x → AddCircle p) :
    hx.vertexTorusHom p (Function.extend Subtype.val φ 0) = φ := by
  ext k
  rw [vertexTorusHom_apply, hx.basis.sum_repr_smul_eq_of_forall_notMem hx.basis_apply
    (fun j hj ↦ by rw [Function.extend_val_apply' hj, Pi.zero_apply]),
    Subtype.val_injective.extend_apply]

variable (p) in
/-- **The residual torus at a smooth vertex.** The homomorphism `vertexTorusHom` identifies the
residual torus `(ℝ / pℤ)^ι / N_Δ` with the standard torus `(ℝ / pℤ)^A` on the facets active at
`x`. Its inverse, this equivalence, sends `φ` to the class of the extension of `φ` by zero
(`TauCeti.Toric.IsSmoothVertex.vertexTorusEquiv_apply`). -/
def vertexTorusEquiv (hi : IsIntegralLattice i) :
    (activeSet (facetPairing i u) c x → AddCircle p) ≃+
      (ι → AddCircle p) ⧸ (facetTorusHom i u p).ker :=
  ((QuotientAddGroup.quotientAddEquivOfEq (hx.ker_vertexTorusHom hi).symm).trans
    (QuotientAddGroup.quotientKerEquivOfRightInverse (hx.vertexTorusHom p)
      (Function.extend Subtype.val · 0) hx.vertexTorusHom_extend)).symm

@[simp]
theorem vertexTorusEquiv_symm_mk (hi : IsIntegralLattice i) (θ : ι → AddCircle p) :
    (hx.vertexTorusEquiv p hi).symm θ = hx.vertexTorusHom p θ := by
  rw [vertexTorusEquiv, AddEquiv.symm_symm, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  -- The forward map of `quotientKerEquivOfRightInverse` is `kerLift` by definition.
  exact QuotientAddGroup.kerLift_mk (hx.vertexTorusHom p) θ

@[simp]
theorem vertexTorusEquiv_apply (hi : IsIntegralLattice i)
    (φ : activeSet (facetPairing i u) c x → AddCircle p) :
    hx.vertexTorusEquiv p hi φ =
      ((Function.extend Subtype.val φ 0 : ι → AddCircle p) :
        (ι → AddCircle p) ⧸ (facetTorusHom i u p).ker) := by
  rw [← AddEquiv.eq_symm_apply, vertexTorusEquiv_symm_mk, vertexTorusHom_extend]

end IsSmoothVertex

end SmoothVertex

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
    Function.Surjective (Fintype.linearCombination ℤ u) :=
  let ⟨x, hx⟩ := hΔ.extremePoints_nonempty
  (hΔ.isSmoothVertex x hx).surjective_linearCombination

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

end IsDelzant

end Delzant

end TauCeti.Toric
