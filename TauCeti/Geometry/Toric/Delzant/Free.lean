/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Delzant.Interval
public import TauCeti.Geometry.Toric.Delzant.Level

/-!
# Freeness of the kernel torus and labelled facet presentations

Let `i : N →+ V` be an integral lattice and `(u, c)` a facet presentation of a bounded polyhedron
`Δ = {y ∈ V* | c j ≤ ⟨y, u j⟩ for every j}`. Delzant's construction reduces `ℂ^ι` by the kernel
torus `N_Δ ⊆ (ℝ / 2πℤ)^ι` of `TauCeti.Toric.facetTorusHom` at the zero level `Z` of its moment map
(`TauCeti.Toric.delzantLevel`). The stabilizers of `N_Δ` on `Z` are the local groups of the reduced
space `Z / N_Δ`, which is an ordinary manifold rather than an orbifold when they are trivial. This
file shows that freeness of `N_Δ` on `Z` is exactly the smoothness condition on the vertices of
Delzant polytopes.

* **Stabilizers.** If `μ(x) = β_ℝ^* y`, an element of `(ℝ / 2πℤ)^ι` fixes `x ∈ Z` exactly when its
  coordinates off the facets active at `y` vanish
  (`TauCeti.Toric.vadd_eq_self_iff_of_forall_eq`).
* **Pointwise criterion.** Over a vertex `y` of `Δ`, the kernel torus acts freely at `x` exactly
  when `y` is a smooth vertex, that is, the active normals form a basis of the lattice
  (`TauCeti.Toric.isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self`). This is
  `TauCeti.Toric.exists_basis_iff_forall_eq_zero_of_mem_ker_facetTorusHom` for the active facets,
  whose normals span `V` at a vertex.
* **Global criterion.** For bounded `Δ`, the kernel torus acts freely on all of `Z` exactly when
  every vertex of `Δ` is smooth
  (`TauCeti.Toric.forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self`): the facets active at
  any point of `Δ` are active at some vertex. Hence a bounded irredundant presentation is Delzant
  exactly when its kernel torus acts freely on its level
  (`TauCeti.Toric.isDelzant_iff_forall_eq_zero_of_vadd_eq_self`).

**Labels.** A labelled polytope in the sense of Lerman and Tolman attaches a positive integer
`m j` to each facet; its orbifold is Delzant's construction for the normals `m j • u j` and the
support constants `m j * c j`, which describe the same polyhedron with the same active facets, and
whose smooth vertices are the smooth vertices of `(u, c)` at which every active label is one
(`TauCeti.Toric.isSmoothVertex_nsmul_iff`). So when every facet meets `Δ`, the kernel torus of the
labelled normals acts freely on its level exactly when all labels are one and every vertex of `Δ`
is smooth (`TauCeti.Toric.forall_eq_zero_of_vadd_eq_self_nsmul_iff`): with unit labels the kernel
torus acts freely precisely when every vertex cone is unimodular, and any other label leaves a
nontrivial stabilizer. For a Delzant polytope, freeness holds exactly for unit labels
(`TauCeti.Toric.IsDelzant.forall_eq_zero_of_vadd_eq_self_nsmul_iff`). For instance, doubling both
normals of the interval `[0, a]` gives a kernel torus with a nontrivial stabilizer
(`TauCeti.Toric.not_forall_eq_zero_of_vadd_eq_self_interval_two`), although the polyhedron is
unchanged.

## Main results

* `TauCeti.Toric.isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self`: over a vertex, the kernel
  torus acts freely exactly when the vertex is smooth.
* `TauCeti.Toric.forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self`: for a bounded
  polyhedron, the kernel torus acts freely on the level exactly when every vertex is smooth.
* `TauCeti.Toric.isDelzant_iff_forall_eq_zero_of_vadd_eq_self`: Delzant presentations are the
  bounded irredundant ones with free kernel torus.
* `TauCeti.Toric.forall_eq_zero_of_vadd_eq_self_nsmul_iff`,
  `TauCeti.Toric.IsDelzant.forall_eq_zero_of_vadd_eq_self_nsmul_iff`: the kernel torus of a
  labelled presentation acts freely exactly for unit labels and smooth vertices.

## References

* T. Delzant, *Hamiltoniens périodiques et images convexes de l'application moment*,
  Bull. Soc. Math. France 116 (1988), 315–339.
* E. Lerman, S. Tolman, *Hamiltonian torus actions on symplectic orbifolds and toric varieties*,
  Trans. Amer. Math. Soc. 349 (1997), 4201–4230.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 29.
-/

public section

noncomputable section

open Set Real

namespace TauCeti.Toric

variable {ι N V : Type*} [Fintype ι] [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ}

/-! ### Freeness of the kernel torus -/

/-- **Stabilizers on the level.** If `μ(x) = β_ℝ^* y`, an element `θ` of `(ℝ / 2πℤ)^ι` fixes the
point `x` of the level exactly when `θ j = 0` for every facet `j` not active at `y`. -/
theorem vadd_eq_self_iff_of_forall_eq {x : delzantLevel i u c} {y : StrongDual ℝ V}
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + c j = y (i (u j)))
    (θ : ι → AddCircle (2 * π)) :
    θ +ᵥ x = x ↔ ∀ j ∉ activeSet (facetPairing i u) c y, θ j = 0 := by
  rw [← Subtype.coe_inj, coe_vadd_delzantLevel, torusRotation_apply_eq_self_iff,
    activeSet_eq_of_forall_eq hy]
  simp only [mem_ofPred_eq, not_and_or]

/-- **Freeness over a vertex.** Let `y` be a vertex of `Δ` and `x` a point of the level with
`μ(x) = β_ℝ^* y`. Then `y` is a smooth vertex exactly when the only element of the kernel torus
fixing `x` is zero. -/
theorem isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self (hi : IsIntegralLattice i)
    {x : delzantLevel i u c} {y : StrongDual ℝ V}
    (hy : ∀ j, ((x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).1 j ^ 2 +
      (x : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι).2 j ^ 2) / 2 + c j = y (i (u j)))
    (hv : y ∈ (facetPolyhedron i u c).extremePoints ℝ) :
    IsSmoothVertex i u c y ↔ ∀ θ ∈ (facetTorusHom i u (2 * π)).ker, θ +ᵥ x = x → θ = 0 := by
  have := hi.finiteDimensional
  simp_rw [vadd_eq_self_iff_of_forall_eq hy]
  rw [isSmoothVertex_def]
  exact exists_basis_iff_forall_eq_zero_of_mem_ker_facetTorusHom hi (by positivity)
    (mem_extremePoints_facetPolyhedron_iff_span_eq_top.1 hv).2

/-- **Freeness on the level.** For a bounded polyhedron `Δ`, every vertex of `Δ` is smooth exactly
when the kernel torus acts freely on the level: the only element of the kernel torus fixing a
point of the level is zero. -/
theorem forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self (hi : IsIntegralLattice i)
    (hb : Bornology.IsBounded (facetPolyhedron i u c)) :
    (∀ y ∈ (facetPolyhedron i u c).extremePoints ℝ, IsSmoothVertex i u c y) ↔
      ∀ θ ∈ (facetTorusHom i u (2 * π)).ker, ∀ x : delzantLevel i u c, θ +ᵥ x = x → θ = 0 := by
  have := hi.finiteDimensional
  have hc := isCompact_facetPolyhedron_of_isBounded hb
  refine ⟨fun hv θ hθ x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · -- The facets active at the moment value of `x` are active at a smooth vertex.
    obtain ⟨y, hy⟩ := mem_delzantLevel_iff.1 x.property
    obtain ⟨v, hv', hsub⟩ :=
      exists_mem_extremePoints_activeSet_subset hc (mem_facetPolyhedron_of_forall_eq c hy)
    exact eq_zero_of_mem_ker_facetTorusHom hi (isSmoothVertex_def.1 (hv v hv')) hθ fun j hj ↦
      (vadd_eq_self_iff_of_forall_eq hy θ).1 hx j fun h ↦ hj (hsub h)
  · -- Every point of `Δ` is the moment value of a point of the level.
    obtain ⟨x, hx, hxy⟩ : y ∈ {y : StrongDual ℝ V | ∃ x ∈ delzantLevel i u c,
        ∀ j, (x.1 j ^ 2 + x.2 j ^ 2) / 2 + c j = y (i (u j))} := by
      rw [setOf_exists_mem_delzantLevel]
      exact extremePoints_subset hy
    exact (isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self hi (x := ⟨x, hx⟩) hxy hy).2 fun θ hθ ↦
      h θ hθ ⟨x, hx⟩

/-- **Delzant polytopes are those with free kernel torus.** A facet presentation is Delzant
exactly when its polyhedron is bounded, each constraint is the only active one at some point, and
the kernel torus acts freely on the level. -/
theorem isDelzant_iff_forall_eq_zero_of_vadd_eq_self (hi : IsIntegralLattice i) :
    IsDelzant i u c ↔ Bornology.IsBounded (facetPolyhedron i u c) ∧
      (∀ j, ∃ y ∈ facetPolyhedron i u c, activeSet (facetPairing i u) c y = {j}) ∧
      ∀ θ ∈ (facetTorusHom i u (2 * π)).ker, ∀ x : delzantLevel i u c, θ +ᵥ x = x → θ = 0 :=
  ⟨fun h ↦ ⟨h.isBounded, h.irredundant,
      (forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self hi h.isBounded).1 h.isSmoothVertex⟩,
    fun ⟨hb, hirr, h⟩ ↦
      ⟨hb, (forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self hi hb).2 h, hirr⟩⟩

/-! ### Labelled facet presentations -/

section Label

variable {m : ι → ℕ}

/-- **The smoothness criterion for labelled polytopes.** Let `Δ` be bounded, with every facet
meeting it. The kernel torus of the labelled normals `m j • u j`, with support constants
`m j * c j`, acts freely on its level exactly when every label is one and every vertex of `Δ` is
smooth. -/
theorem forall_eq_zero_of_vadd_eq_self_nsmul_iff (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0)
    (hb : Bornology.IsBounded (facetPolyhedron i u c))
    (hj : ∀ j, ∃ y ∈ facetPolyhedron i u c, j ∈ activeSet (facetPairing i u) c y) :
    (∀ θ ∈ (facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker,
        ∀ x : delzantLevel i (fun j ↦ m j • u j) (fun j ↦ m j * c j), θ +ᵥ x = x → θ = 0) ↔
      (∀ j, m j = 1) ∧ ∀ y ∈ (facetPolyhedron i u c).extremePoints ℝ, IsSmoothVertex i u c y := by
  have := hi.finiteDimensional
  rw [← forall_isSmoothVertex_iff_forall_eq_zero_of_vadd_eq_self hi
    (by rwa [facetPolyhedron_nsmul hm]), facetPolyhedron_nsmul hm]
  simp_rw [isSmoothVertex_nsmul_iff hm]
  refine ⟨fun h ↦ ⟨fun j ↦ ?_, fun y hy ↦ (h y hy).2⟩, fun h y hy ↦ ⟨fun j _ ↦ h.1 j, h.2 y hy⟩⟩
  -- The facet `j` meets `Δ`, so it is active at some vertex.
  obtain ⟨y, hy, hjy⟩ := hj j
  obtain ⟨v, hv, hjv⟩ :=
    exists_mem_extremePoints_mem_activeSet (isCompact_facetPolyhedron_of_isBounded hb) hy hjy
  exact (h v hv).1 j hjv

/-- **Unit labels on a Delzant polytope.** For a Delzant polytope, the kernel torus of the
labelled normals `m j • u j`, with support constants `m j * c j`, acts freely on its level exactly
when every label is one. -/
theorem IsDelzant.forall_eq_zero_of_vadd_eq_self_nsmul_iff (hΔ : IsDelzant i u c)
    (hi : IsIntegralLattice i) (hm : ∀ j, m j ≠ 0) :
    (∀ θ ∈ (facetTorusHom i (fun j ↦ m j • u j) (2 * π)).ker,
        ∀ x : delzantLevel i (fun j ↦ m j • u j) (fun j ↦ m j * c j), θ +ᵥ x = x → θ = 0) ↔
      ∀ j, m j = 1 := by
  rw [Toric.forall_eq_zero_of_vadd_eq_self_nsmul_iff hi hm hΔ.isBounded fun j ↦
    let ⟨y, hy, hjy⟩ := hΔ.irredundant j; ⟨y, hy, hjy ▸ mem_singleton j⟩]
  exact and_iff_left hΔ.isSmoothVertex

/-- **The doubled interval.** The normals `2, -2` with support constants `0, -2a` cut out the same
interval `[0, a]` as the normals `1, -1` with support constants `0, -a`, but the kernel torus of
the doubled normals does not act freely on its level. -/
theorem not_forall_eq_zero_of_vadd_eq_self_interval_two {a : ℝ} (ha : 0 < a) :
    ¬∀ θ ∈ (facetTorusHom (Int.castAddHom ℝ) ![2, -2] (2 * π)).ker,
      ∀ x : delzantLevel (Int.castAddHom ℝ) ![2, -2] ![0, -(2 * a)], θ +ᵥ x = x → θ = 0 := by
  have hu : (![2, -2] : Fin 2 → ℤ) = fun j ↦ (![2, 2] : Fin 2 → ℕ) j • ![1, -1] j := by
    ext j; fin_cases j <;> simp
  have hc : (![0, -(2 * a)] : Fin 2 → ℝ) = fun j ↦ ((![2, 2] : Fin 2 → ℕ) j : ℝ) * ![0, -a] j := by
    ext j; fin_cases j <;> simp
  have hi : IsIntegralLattice (Int.castAddHom ℝ) :=
    isIntegralLattice_of_basis (Module.Basis.singleton Unit ℤ) (Module.Basis.singleton Unit ℝ)
      fun _ ↦ by simp
  rw [hu, hc, (isDelzant_interval ha).forall_eq_zero_of_vadd_eq_self_nsmul_iff hi fun j ↦ by
    fin_cases j <;> simp]
  exact fun h ↦ absurd (h 0) (by simp)

end Label

end TauCeti.Toric
