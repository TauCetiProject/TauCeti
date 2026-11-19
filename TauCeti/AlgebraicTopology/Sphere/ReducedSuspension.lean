/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.CubeQuotient
public import TauCeti.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopPair.Quotient

/-!
# The reduced suspension of a sphere is a sphere

Let `Sⁿ` be the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`, pointed at its north pole
`e_last` (`TauCeti.sphereNorthPole`), and let `n ≥ 1`. The reduced suspension of `Sⁿ` is the
pointed quotient

`ΣSⁿ = (Sⁿ × I) / (Sⁿ × ∂I ∪ {e_last} × I)`

of the cylinder on `Sⁿ`, written here as the pointed quotient `TopPair.ordinaryPairQuotient` of
the pair `(Sⁿ × I, Sⁿ × ∂I ∪ {e_last} × I)`. This file identifies it with the sphere `Sⁿ⁺¹`
(`TauCeti.sphereReducedSuspensionHomeomorph`), the interval coordinate becoming the last
coordinate of the cube.

The identification is read off the cube maps `q : Iⁿ → Sⁿ` (`TauCeti.cubeToSphere`), which
collapse exactly the boundary of the cube to the north pole. Appending the interval coordinate
last identifies `Iⁿ × I` with `Iⁿ⁺¹`, and the cube map of `Iⁿ⁺¹` is constant on `∂Iⁿ × I`, so it
descends along `q × id` to the **suspension map**

`σ : Sⁿ × I → Sⁿ⁺¹`, `σ (q y, t) = q (y, t)`

(`TauCeti.sphereSuspensionMap`, `TauCeti.sphereSuspensionMap_cubeToSphere`). A point
`(y, t)` lies on the boundary of `Iⁿ⁺¹` exactly when `y ∈ ∂Iⁿ` or `t ∈ ∂I`
(`Cube.snoc_mem_boundary_iff`), so `σ` collapses exactly the locus
`Sⁿ × ∂I ∪ {e_last} × I` to the north pole of `Sⁿ⁺¹`
(`TauCeti.sphereSuspensionMap_eq_sphereNorthPole_iff`), it identifies no other points
(`TauCeti.sphereSuspensionMap_eq_sphereSuspensionMap_iff`), and it is surjective. The cylinder
is compact and the sphere is Hausdorff, so the map induced by `σ` on the pointed quotient is a
homeomorphism (`TopPair.ordinaryPairQuotientHomeomorph`). It is the only map from the reduced
suspension that reads the cube maps this way (`TauCeti.eq_sphereReducedSuspensionHomeomorph`):
the composite

`Iⁿ × I → Sⁿ × I → ΣSⁿ → Sⁿ⁺¹`

is the cube map of `Iⁿ⁺¹`, with the interval coordinate last
(`TauCeti.sphereReducedSuspensionHomeomorph_π` and `TauCeti.sphereSuspensionMap_cubeToSphere`).

Through this homeomorphism, maps out of `Sⁿ⁺¹` are maps out of the reduced suspension of `Sⁿ`,
as needed to compare the loop space of `Sⁿ⁺¹` with the James construction on `Sⁿ`, whose
homology is the tensor algebra on the reduced homology of `Sⁿ` (Bott–Samelson).

## Main declarations

* `TauCeti.sphereSuspensionMap`: the suspension map `Sⁿ × I → Sⁿ⁺¹`, characterized on the cube by
  `TauCeti.sphereSuspensionMap_cubeToSphere`, with its fibres
  `TauCeti.sphereSuspensionMap_eq_sphereNorthPole_iff` and
  `TauCeti.sphereSuspensionMap_eq_sphereSuspensionMap_iff`.
* `TauCeti.sphereReducedSuspensionHomeomorph`: the homeomorphism `ΣSⁿ ≃ₜ Sⁿ⁺¹`, with
  `TauCeti.sphereReducedSuspensionHomeomorph_π` and
  `TauCeti.sphereReducedSuspensionHomeomorph_basepoint`.
* `TauCeti.eq_sphereReducedSuspensionHomeomorph`: it is the only map from `ΣSⁿ` reading the cube
  maps with the interval coordinate last.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0 (the reduced suspension and `ΣSⁿ = Sⁿ⁺¹`) and Section 4.1 (`Iⁿ / ∂Iⁿ = Sⁿ`).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter III.
-/

public section

noncomputable section

open CategoryTheory Metric Set Topology
open scoped unitInterval

namespace TauCeti

variable {n : ℕ}

/-! ### Appending the interval coordinate -/

variable (n) in
/-- The cube map of `Iⁿ⁺¹` read on `I × Iⁿ`, the interval coordinate appended last. -/
private def cubeSuspensionAux :
    C(I × I^(Fin n), sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1) :=
  (cubeToSphere (n + 1)).comp
    ⟨fun p ↦ Fin.snoc (α := fun _ ↦ I) p.2 p.1,
      Continuous.finSnoc (A := fun _ ↦ I) continuous_snd continuous_fst⟩

private lemma cubeSuspensionAux_apply (t : I) (y : I^(Fin n)) :
    cubeSuspensionAux n (t, y) = cubeToSphere (n + 1) (Fin.snoc y t) :=
  (rfl)

/-- At each time, the cube map of `Iⁿ⁺¹` is constant on `∂Iⁿ × I`, the north pole. -/
private lemma cubeSuspensionAux_boundary (t : I) (y : I^(Fin n))
    (hy : y ∈ Cube.boundary (Fin n)) (z : I^(Fin n)) (hz : z ∈ Cube.boundary (Fin n)) :
    cubeSuspensionAux n (t, y) = cubeSuspensionAux n (t, z) := by
  rw [cubeSuspensionAux_apply, cubeSuspensionAux_apply, cubeToSphere_eq_cubeToSphere_iff]
  exact Or.inr
    ⟨Cube.snoc_mem_boundary_iff.2 (Or.inl hy), Cube.snoc_mem_boundary_iff.2 (Or.inl hz)⟩

/-! ### The suspension map -/

variable (n) in
/-- The **suspension map** `σ : Sⁿ × I → Sⁿ⁺¹`, the map through which the cube map of `Iⁿ⁺¹`
factors along `q × id : Iⁿ × I → Sⁿ × I`: it sends `(q y, t)` to the image of the cube point
`(y, t)`, the interval coordinate last (`TauCeti.sphereSuspensionMap_cubeToSphere`). -/
def sphereSuspensionMap [NeZero n] :
    C(sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I,
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1) :=
  (liftProdCubeToSphere (cubeSuspensionAux n) cubeSuspensionAux_boundary).comp
    ContinuousMap.prodSwap

/-- The suspension map sends `(q y, t)` to the cube map of `Iⁿ⁺¹` at `(y, t)`. -/
@[simp]
theorem sphereSuspensionMap_cubeToSphere [NeZero n] (y : I^(Fin n)) (t : I) :
    sphereSuspensionMap n (cubeToSphere n y, t) = cubeToSphere (n + 1) (Fin.snoc y t) := by
  rw [sphereSuspensionMap, ContinuousMap.comp_apply, ContinuousMap.prodSwap_apply]
  exact (liftProdCubeToSphere_apply _ _ t y).trans (cubeSuspensionAux_apply t y)

/-- The suspension map collapses exactly the locus `Sⁿ × ∂I ∪ {e_last} × I`, to the north
pole. -/
theorem sphereSuspensionMap_eq_sphereNorthPole_iff [NeZero n]
    {p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I} :
    sphereSuspensionMap n p = sphereNorthPole (n + 1) ↔
      p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1 := by
  obtain ⟨x, t⟩ := p
  obtain ⟨y, rfl⟩ := cubeToSphere_surjective n x
  simp only [sphereSuspensionMap_cubeToSphere, cubeToSphere_eq_sphereNorthPole_iff,
    Cube.snoc_mem_boundary_iff]

/-- The suspension map identifies two points exactly when they are equal or both lie on the
locus `Sⁿ × ∂I ∪ {e_last} × I`. -/
theorem sphereSuspensionMap_eq_sphereSuspensionMap_iff [NeZero n]
    {p p' : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I} :
    sphereSuspensionMap n p = sphereSuspensionMap n p' ↔
      p = p' ∨ (p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1) ∧
        (p'.1 = sphereNorthPole n ∨ p'.2 = 0 ∨ p'.2 = 1) := by
  rw [← sphereSuspensionMap_eq_sphereNorthPole_iff, ← sphereSuspensionMap_eq_sphereNorthPole_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, t⟩ := p
    obtain ⟨x', t'⟩ := p'
    obtain ⟨y, rfl⟩ := cubeToSphere_surjective n x
    obtain ⟨y', rfl⟩ := cubeToSphere_surjective n x'
    have h' := h
    rw [sphereSuspensionMap_cubeToSphere, sphereSuspensionMap_cubeToSphere,
      cubeToSphere_eq_cubeToSphere_iff] at h'
    rcases h' with h' | ⟨hb, -⟩
    · obtain ⟨rfl, rfl⟩ := Fin.snoc_inj.1 h'
      exact Or.inl rfl
    · have hn : sphereSuspensionMap n (cubeToSphere n y, t) = sphereNorthPole (n + 1) := by
        rwa [sphereSuspensionMap_cubeToSphere, cubeToSphere_eq_sphereNorthPole_iff]
      exact Or.inr ⟨hn, h ▸ hn⟩
  · rintro (rfl | ⟨h, h'⟩)
    · rfl
    · rw [h, h']

/-- The suspension map collapses the segment over the north pole. -/
@[simp]
theorem sphereSuspensionMap_sphereNorthPole [NeZero n] (t : I) :
    sphereSuspensionMap n (sphereNorthPole n, t) = sphereNorthPole (n + 1) :=
  sphereSuspensionMap_eq_sphereNorthPole_iff.2 (Or.inl rfl)

/-- The suspension map collapses the bottom of the cylinder. -/
@[simp]
theorem sphereSuspensionMap_zero [NeZero n] (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereSuspensionMap n (x, 0) = sphereNorthPole (n + 1) :=
  sphereSuspensionMap_eq_sphereNorthPole_iff.2 (Or.inr (Or.inl rfl))

/-- The suspension map collapses the top of the cylinder. -/
@[simp]
theorem sphereSuspensionMap_one [NeZero n] (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereSuspensionMap n (x, 1) = sphereNorthPole (n + 1) :=
  sphereSuspensionMap_eq_sphereNorthPole_iff.2 (Or.inr (Or.inr rfl))

/-- The suspension map is surjective. -/
theorem sphereSuspensionMap_surjective [NeZero n] :
    Function.Surjective (sphereSuspensionMap n) := by
  intro z
  obtain ⟨w, rfl⟩ := cubeToSphere_surjective (n + 1) z
  refine ⟨(cubeToSphere n (Fin.init w), w (Fin.last n)), ?_⟩
  rw [sphereSuspensionMap_cubeToSphere, Fin.snoc_init_self]

/-! ### The reduced suspension -/

variable (n) in
/-- **The reduced suspension of `Sⁿ` is `Sⁿ⁺¹`.** The pointed quotient
`ΣSⁿ = (Sⁿ × I) / (Sⁿ × ∂I ∪ {e_last} × I)` is homeomorphic to `Sⁿ⁺¹` by the map induced by the
suspension map `TauCeti.sphereSuspensionMap`, which sends the class of `(q y, t)` to the cube
map of `Iⁿ⁺¹` at `(y, t)`, the interval coordinate last, and the basepoint to the north pole. -/
def sphereReducedSuspensionHomeomorph [NeZero n] :
    (TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
      {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1}).ordinaryPairQuotient ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1 :=
  TopPair.ordinaryPairQuotientHomeomorph
    (TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
      {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1})
    (Y := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1))
    (TopCat.ofHom (sphereSuspensionMap n)) (sphereNorthPole (n + 1))
    (fun _ ↦ by
      rw [TopPair.range_ofSubset_map]
      exact sphereSuspensionMap_eq_sphereNorthPole_iff)
    (fun _ _ hp h ↦ by
      rw [TopPair.range_ofSubset_map] at hp
      exact (sphereSuspensionMap_eq_sphereSuspensionMap_iff.1 h).resolve_right
        fun h' ↦ hp h'.1)
    (fun z _ ↦ sphereSuspensionMap_surjective z)

/-- The homeomorphism `ΣSⁿ ≃ₜ Sⁿ⁺¹` sends the class of a point of the cylinder to its image under
the suspension map. -/
@[simp]
theorem sphereReducedSuspensionHomeomorph_π [NeZero n]
    (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I) :
    sphereReducedSuspensionHomeomorph n
        ((TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
          {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1}).ordinaryPairQuotientπ p) =
      sphereSuspensionMap n p :=
  TopPair.ordinaryPairQuotientHomeomorph_π
    (TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
      {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1})
    (f := TopCat.ofHom (sphereSuspensionMap n)) _ _ _ p

/-- The homeomorphism `ΣSⁿ ≃ₜ Sⁿ⁺¹` sends the basepoint to the north pole. -/
@[simp]
theorem sphereReducedSuspensionHomeomorph_basepoint [NeZero n] :
    sphereReducedSuspensionHomeomorph n
        (TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
          {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1}).ordinaryPairQuotientBasepoint =
      sphereNorthPole (n + 1) :=
  TopPair.ordinaryPairQuotientHomeomorph_basepoint _ _ _ _

/-- **Uniqueness.** A function on `ΣSⁿ` that reads the cube maps with the interval coordinate last,
sending the class of `(q y, t)` to the cube map of `Iⁿ⁺¹` at `(y, t)`, is
`TauCeti.sphereReducedSuspensionHomeomorph`. -/
theorem eq_sphereReducedSuspensionHomeomorph [NeZero n]
    (g : (TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
      {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1}).ordinaryPairQuotient →
        sphere (0 : EuclideanSpace ℝ (Fin (n + 1 + 1))) 1)
    (hg : ∀ (y : I^(Fin n)) (t : I),
      g ((TopPair.ofSubset (X := TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 × I))
        {p | p.1 = sphereNorthPole n ∨ p.2 = 0 ∨ p.2 = 1}).ordinaryPairQuotientπ
          (cubeToSphere n y, t)) = cubeToSphere (n + 1) (Fin.snoc y t)) :
    g = sphereReducedSuspensionHomeomorph n := by
  funext z
  rcases TopPair.exists_ordinaryPairQuotientπ_or_eq_basepoint _ z with ⟨⟨x, t⟩, rfl⟩ | rfl
  · obtain ⟨y, rfl⟩ := cubeToSphere_surjective n x
    rw [hg, sphereReducedSuspensionHomeomorph_π, sphereSuspensionMap_cubeToSphere]
  · -- The basepoint is the class of any point at time `0`.
    rw [← (TopPair.ordinaryPairQuotientπ_eq_basepoint_iff _ (cubeToSphere n 0, 0)).2
      (by rw [TopPair.range_ofSubset_map]; exact Or.inr (Or.inl rfl)), hg,
      sphereReducedSuspensionHomeomorph_π, sphereSuspensionMap_cubeToSphere]

end TauCeti
