/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Level

import Mathlib.Analysis.Real.Cardinality

/-!
# Orbits and stabilizers of the residual torus on the Delzant level

Let `i : N →+ V` be an integral lattice and `(u, c)` a facet presentation of a polytope
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`. Delzant's construction reduces `ℂ^ι` by the kernel
torus `N_Δ` of the homomorphism `π : (ℝ / 2πℤ)^ι → V / 2π i(N)`
(`TauCeti.Toric.facetTorusHom`), acting by `z_j ↦ exp(-i θ_j) z_j`, at the zero level `Z` of its
moment map (`TauCeti.Toric.delzantLevel`). The *residual torus* `V / 2π i(N)`, the image of `π`,
then acts on `Z / N_Δ`: the class `π [θ]` sends the `N_Δ`-orbit of `x` to that of the rotation of
`x` by `-θ`. This file describes the orbits and the stabilizers of this action in terms of the
faces of `Δ`, without constructing the quotient `Z / N_Δ` itself.

For a set `s` of facets, the *face subtorus* `TauCeti.Toric.faceSubtorus i u p s` is the image
in `V / p i(N)` of the real span of the normals `i (u j)`, `j ∈ s`; equivalently, it is the image
under `π` of the coordinate subtorus of the angles supported on `s`
(`TauCeti.Toric.mem_faceSubtorus_iff`).

* **Stabilizers.** Rotating `x` by `-θ` lands in the `N_Δ`-orbit of `x` exactly when `π [θ]`
  lies in the face subtorus of the facets `j` with `z_j = 0`
  (`TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus`). This needs no
  hypothesis on `x` or on the presentation. For a point of the level with moment value `y ∈ Δ`
  these are the facets active at `y`, so the residual stabilizer of a point over `y` is the
  face subtorus of the face of `Δ` containing `y` in its relative interior.
* **Free over the interior, fixed over the vertices.** The face subtorus is trivial exactly when
  the normals are zero, and is everything exactly when the normals span `V`
  (`TauCeti.Toric.faceSubtorus_eq_bot_iff`, `TauCeti.Toric.faceSubtorus_eq_top_iff`). Both use
  that the lattice is countable while every nonzero real line is not. Hence, when the normals
  are nonzero and generate the lattice, the residual torus acts freely on the orbit over `y`
  exactly when `y` lies on no facet, and fixes it exactly when `y` is a vertex of `Δ`.
* **Fibres.** The points of `ℂ^ι` with moment value `y` form a single orbit of `(ℝ / 2πℤ)^ι`
  (`TauCeti.Toric.setOf_forall_eq_eq_range_weightRotation_neg`), so the fibre of the residual
  moment map over each `y ∈ Δ` is a single orbit of the residual torus.
* **Effectiveness.** A Delzant polytope has a point lying on no facet
  (`TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`), so some point of the level has trivial
  residual stabilizer and the residual torus acts effectively.

## Main definitions

* `TauCeti.Toric.faceSubtorus i u p s`: the subgroup of `V / p i(N)` spanned by the normals of
  the facets in `s`.

## Main results

* `TauCeti.Toric.mem_faceSubtorus_iff`: the face subtorus is the image under `π` of the angles
  supported on `s`.
* `TauCeti.Toric.faceSubtorus_eq_bot_iff`, `TauCeti.Toric.faceSubtorus_eq_top_iff`: when the
  face subtorus is trivial, and when it is the whole torus.
* `TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus`,
  `TauCeti.Toric.exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet`: the
  residual stabilizer is the face subtorus of the active facets.
* `TauCeti.Toric.forall_exists_weightRotation_neg_apply_eq_iff_activeSet_eq_empty`: the residual
  torus acts freely exactly over the points of `Δ` lying on no facet.
* `TauCeti.Toric.forall_exists_weightRotation_neg_apply_eq_iff_mem_extremePoints`: the residual
  torus fixes the orbit over `y` exactly when `y` is a vertex of `Δ`.
* `TauCeti.Toric.setOf_forall_eq_eq_range_weightRotation_neg`: the moment fibres are single
  torus orbits.
* `TauCeti.Toric.IsDelzant.exists_activeSet_eq_empty`: a Delzant polytope has a point on no
  facet.
* `TauCeti.Toric.IsDelzant.exists_mem_delzantLevel_forall_exists_weightRotation_neg_apply_eq_iff`:
  some point of the level has trivial residual stabilizer.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Sections 28 and 29.
* V. Guillemin, *Moment Maps and Combinatorial Invariants of Hamiltonian `T^n`-spaces*,
  Birkhäuser, 1994, Chapter 1.
-/

public section

noncomputable section

open Set Real Filter Topology

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  {u : ι → N}

/-! ### Face subtori -/

variable (i u) in
/-- The *face subtorus* of a set `s` of facets: the image in `V / p i(N)` of the real span of the
normals `i (u j)`, `j ∈ s`. For `p ≠ 0` and an integral lattice `i`, these normals are lattice
vectors, so this is the subtorus of the torus `V / p i(N)` whose Lie algebra is their span. -/
def faceSubtorus (p : ℝ) (s : Set ι) : AddSubgroup (V ⧸ (p • i).range) :=
  (Submodule.span ℝ ((fun j ↦ i (u j)) '' s)).toAddSubgroup.map (QuotientAddGroup.mk' _)

/-- A class lies in the face subtorus of `s` exactly when it is the class of a vector in the span
of the normals `i (u j)`, `j ∈ s`. -/
theorem mem_faceSubtorus {p : ℝ} {s : Set ι} {q : V ⧸ (p • i).range} :
    q ∈ faceSubtorus i u p s ↔
      ∃ v ∈ Submodule.span ℝ ((fun j ↦ i (u j)) '' s), (v : V ⧸ (p • i).range) = q := by
  simp [faceSubtorus]

/-- The face subtorus of `s` is the image, under the homomorphism `facetTorusHom`, of the angles
supported on `s`. -/
theorem mem_faceSubtorus_iff [Fintype ι] {p : ℝ} {s : Set ι} {q : V ⧸ (p • i).range} :
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

variable (i u) in
/-- Face subtori grow with the set of facets. -/
theorem faceSubtorus_mono (p : ℝ) : Monotone (faceSubtorus i u p) :=
  fun _ _ h ↦ AddSubgroup.map_mono (Submodule.toAddSubgroup_mono
    (Submodule.span_mono (image_mono h)))

variable (i u) in
@[simp]
theorem faceSubtorus_empty (p : ℝ) : faceSubtorus i u p ∅ = ⊥ := by
  simp [faceSubtorus]

/-- **Trivial face subtori.** For a countable lattice, the face subtorus of `s` is trivial exactly
when the normals `i (u j)`, `j ∈ s`, vanish. -/
theorem faceSubtorus_eq_bot_iff [Countable N] {p : ℝ} {s : Set ι} :
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
theorem faceSubtorus_eq_top_iff [Countable N] {p : ℝ} {s : Set ι} :
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
      have hfw : f w ∈ (Submodule.span ℝ ((fun j ↦ i (u j)) '' s)).map f :=
        Submodule.mem_map_of_mem hw
      rw [hfW, Submodule.mem_bot] at hfw
      exact ⟨n, by simp only [hn, map_add, map_neg, hfw, neg_zero, zero_add]⟩
    refine Cardinal.not_countable_real ?_
    rw [← range_eq_univ.2 (LinearMap.surjective hf)]
    exact (countable_range _).mono hsub
  · rw [eq_top_iff]
    rintro q -
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact mem_faceSubtorus.2 ⟨v, h ▸ Submodule.mem_top, rfl⟩

/-! ### Stabilizers of the residual torus -/

variable [Fintype ι]

/-- The rotations of `x` by `-θ` and by `-t` agree exactly when `θ_j - t_j ∈ 2πℤ` at every
coordinate `z_j = q_j + i p_j` of `x` that is nonzero. -/
private theorem weightRotation_neg_apply_eq_iff (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι)
    (θ t : ι → ℝ) :
    weightRotation (-θ) x = weightRotation (-t) x ↔
      ∀ j, (x.1 j ≠ 0 ∨ x.2 j ≠ 0) → ((θ j - t j : ℝ) : AddCircle (2 * π)) = 0 := by
  have hθ : weightRotation (-θ) = (weightRotation (-t)).comp (weightRotation (-(θ - t))) := by
    rw [← weightRotation_add]
    congr 1
    abel
  have hinj : Function.Injective (weightRotation (-t)) := fun y z h ↦ by
    have h' := congrArg (weightRotation t) h
    simpa only [← ContinuousLinearMap.comp_apply, ← weightRotation_add, add_neg_cancel,
      weightRotation_zero, ContinuousLinearMap.id_apply] using h'
  rw [hθ, ContinuousLinearMap.comp_apply, hinj.eq_iff, weightRotation_apply_eq_self_iff]
  refine forall₂_congr fun j _ ↦ ?_
  rw [AddCircle.coe_eq_zero_iff]
  simp only [Pi.neg_apply, Pi.sub_apply, zsmul_eq_mul]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨-k, by push_cast; linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by push_cast; linarith⟩

/-- **The residual stabilizer.** The rotation of `x` by `-θ` lies in the orbit of `x` under the
kernel torus `N_Δ` of `facetTorusHom` exactly when the class of `θ` in the residual torus
`V / 2π i(N)` lies in the face subtorus of the facets `j` with `z_j = 0`. -/
theorem exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus
    (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) (θ : ι → ℝ) :
    (∃ t : ι → ℝ, (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
        weightRotation (-θ) x = weightRotation (-t) x) ↔
      facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) ∈
        faceSubtorus i u (2 * π) {j | x.1 j = 0 ∧ x.2 j = 0} := by
  classical
  have hsub (a b : ι → ℝ) : facetTorusHom i u (2 * π) (fun j ↦ ((a j - b j : ℝ) : AddCircle _)) =
      facetTorusHom i u (2 * π) (fun j ↦ (a j : AddCircle _)) -
        facetTorusHom i u (2 * π) (fun j ↦ (b j : AddCircle _)) := by
    rw [← map_sub]
    exact congrArg _ (funext fun j ↦ QuotientAddGroup.mk_sub _ (a j) (b j))
  simp_rw [weightRotation_neg_apply_eq_iff, mem_faceSubtorus_iff, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨t, ht, h⟩
    -- Keep the coordinates of `θ - t` along the vanishing coordinates of `x`.
    refine ⟨fun j ↦ if x.1 j = 0 ∧ x.2 j = 0 then θ j - t j else 0,
      fun j hj ↦ ite_eq_right hj, ?_⟩
    rw [← sub_zero (facetTorusHom i u (2 * π) fun j ↦ (θ j : AddCircle (2 * π))), ← ht, ← hsub]
    congr 1
    funext j
    dsimp only
    split_ifs with hj
    · rfl
    · exact (h j (not_and_or.1 hj)).symm
  · rintro ⟨s, hs, hsθ⟩
    refine ⟨θ - s, ?_, fun j hj ↦ ?_⟩
    · simp only [Pi.sub_apply, hsub, hsθ, sub_self]
    · simp [hs j (not_and_or.2 hj)]

section Level

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {i : N →+ V} {c : ι → ℝ}
  {x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι} {y : StrongDual ℝ V}

/-- **The residual stabilizer over a point of `Δ`.** If `μ(x) = β_ℝ^* y`, the rotation of `x` by
`-θ` lies in the orbit of `x` under the kernel torus exactly when the class of `θ` in the residual
torus lies in the face subtorus of the facets active at `y`. -/
theorem exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) (θ : ι → ℝ) :
    (∃ t : ι → ℝ, (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
        weightRotation (-θ) x = weightRotation (-t) x) ↔
      facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) ∈
        faceSubtorus i u (2 * π) (activeSet (facetPairing i u) c y) := by
  rw [activeSet_eq_of_forall_eq hy]
  exact exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus x θ

/-- If the normals generate the integral lattice, every element of the residual torus
`V / 2π i(N)` is the class `facetTorusHom [θ]` of some angles `θ`. -/
private theorem exists_facetTorusHom_eq (hi : IsIntegralLattice i)
    (hu : Function.Surjective (Fintype.linearCombination ℤ u)) (q : V ⧸ ((2 * π) • i).range) :
    ∃ θ : ι → ℝ, facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) = q := by
  obtain ⟨φ, rfl⟩ := surjective_facetTorusHom hi.span_range_eq_top hu q
  choose θ hθ using fun j ↦ QuotientAddGroup.mk_surjective (φ j)
  exact ⟨θ, congrArg _ (funext hθ)⟩

/-- **The residual torus acts freely exactly over the facet-free points.** Suppose that the
normals are nonzero and generate the integral lattice. If `μ(x) = β_ℝ^* y`, the only element of
the residual torus moving `x` within its orbit under the kernel torus is `0` exactly when `y`
lies on no facet of `Δ`. -/
theorem forall_exists_weightRotation_neg_apply_eq_iff_activeSet_eq_empty
    (hi : IsIntegralLattice i) (hu : Function.Surjective (Fintype.linearCombination ℤ u))
    (hu₀ : ∀ j, u j ≠ 0) (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    (∀ θ : ι → ℝ, (∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
        facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) = 0) ↔
      activeSet (facetPairing i u) c y = ∅ := by
  have := hi.finite
  have := Countable.of_moduleFinite (R := ℤ) (M := N)
  simp_rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hy]
  -- Both sides say that the face subtorus of the active facets is trivial.
  trans faceSubtorus i u (2 * π) (activeSet (facetPairing i u) c y) = ⊥
  · refine ⟨fun h ↦ eq_bot_iff.2 fun q hq ↦ ?_, fun h θ ↦ by rw [h, AddSubgroup.mem_bot]⟩
    obtain ⟨θ, rfl⟩ := exists_facetTorusHom_eq hi hu q
    exact (h θ).1 hq
  · rw [faceSubtorus_eq_bot_iff, eq_empty_iff_forall_notMem]
    exact forall₂_congr fun j _ ↦ by simpa using hu₀ j ∘ (map_eq_zero_iff i hi.injective).1

/-- **The residual torus fixes exactly the orbits over the vertices.** Suppose that the normals
generate the integral lattice. If `μ(x) = β_ℝ^* y`, every element of the residual torus moves `x`
within its orbit under the kernel torus exactly when `y` is a vertex of `Δ`. -/
theorem forall_exists_weightRotation_neg_apply_eq_iff_mem_extremePoints
    (hi : IsIntegralLattice i) (hu : Function.Surjective (Fintype.linearCombination ℤ u))
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    (∀ θ : ι → ℝ, ∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
      y ∈ (facetPolyhedron i u c).extremePoints ℝ := by
  have := hi.finite
  have := Countable.of_moduleFinite (R := ℤ) (M := N)
  have := hi.finiteDimensional
  simp_rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hy]
  rw [mem_extremePoints_facetPolyhedron_iff_span_eq_top, ← faceSubtorus_eq_top_iff (p := 2 * π),
    and_iff_right (mem_facetPolyhedron_of_forall_eq c hy), eq_top_iff]
  refine ⟨fun h q _ ↦ ?_, fun h θ ↦ h (AddSubgroup.mem_top _)⟩
  obtain ⟨θ, rfl⟩ := exists_facetTorusHom_eq hi hu q
  exact h θ

/-- **Moment fibres are torus orbits.** If `μ(x) = β_ℝ^* y`, the points `x'` of `ℂ^ι` with
`μ(x') = β_ℝ^* y` are exactly the rotations of `x` by the torus `(ℝ / 2πℤ)^ι`. In particular they
lie on the level, and they form a single orbit of the residual torus modulo the kernel torus. -/
theorem setOf_forall_eq_eq_range_weightRotation_neg
    (hy : ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))) :
    {x' : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι |
        ∀ j, (x'.1 j ^ 2 + x'.2 j ^ 2) / 2 + c j = y (i (u j))} =
      range fun θ : ι → ℝ ↦ weightRotation (-θ) x := by
  ext x'
  have hneg : (∃ θ : ι → ℝ, weightRotation (-θ) x = x') ↔ ∃ θ, weightRotation θ x = x' :=
    ⟨fun ⟨θ, h⟩ ↦ ⟨-θ, h⟩, fun ⟨θ, h⟩ ↦ ⟨-θ, by rwa [neg_neg]⟩⟩
  rw [mem_ofPred_eq, mem_range, hneg, exists_weightRotation_apply_eq_iff]
  exact forall_congr' fun j ↦ ⟨fun h ↦ by linarith [hy j], fun h ↦ by linarith [hy j]⟩

end Level

/-! ### Delzant polytopes -/

namespace IsDelzant

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {i : N →+ V} {c : ι → ℝ} (hΔ : IsDelzant i u c) (hi : IsIntegralLattice i)
include hΔ hi

omit [Fintype ι] in
/-- **A Delzant polytope has a point on no facet.** Some point of the polytope satisfies every
facet inequality strictly. -/
theorem exists_activeSet_eq_empty [Finite ι] :
    ∃ y ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c y = ∅ := by
  classical
  have := Fintype.ofFinite ι
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

/-- **The residual torus acts effectively.** Some point of the level of a Delzant polytope has
trivial residual stabilizer: the only element of the residual torus moving it within its orbit
under the kernel torus is `0`. -/
theorem exists_mem_delzantLevel_forall_exists_weightRotation_neg_apply_eq_iff :
    ∃ x ∈ delzantLevel i u c, ∀ θ : ι → ℝ, (∃ t : ι → ℝ,
        (fun j ↦ (t j : AddCircle (2 * π))) ∈ (facetTorusHom i u (2 * π)).ker ∧
          weightRotation (-θ) x = weightRotation (-t) x) ↔
        facetTorusHom i u (2 * π) (fun j ↦ (θ j : AddCircle (2 * π))) = 0 := by
  obtain ⟨y, hy, hA⟩ := hΔ.exists_activeSet_eq_empty hi
  rw [← setOf_exists_mem_delzantLevel i u c] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨x, hx, fun θ ↦ ?_⟩
  rw [exists_weightRotation_neg_apply_eq_iff_mem_faceSubtorus_activeSet hxy, hA,
    faceSubtorus_empty, AddSubgroup.mem_bot]

end IsDelzant

end TauCeti.Toric
