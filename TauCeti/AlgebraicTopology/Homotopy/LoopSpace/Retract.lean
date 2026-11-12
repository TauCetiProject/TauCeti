/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.PointedMap
public import TauCeti.Geometry.Sphere.LinearIsometry
public import TauCeti.AlgebraicTopology.Singular.Homotopy.Invariance
public import TauCeti.Topology.PathSpace.Moore.Homotopy

/-!
# Double loops of a homotopy retract

If a pointed map `s : (X, x) → (Q, q)` has a pointed left homotopy inverse `r`, that is,
`r ∘ s ≃ id` relative to `x`, then the map `Ω²s` of Moore double loop spaces is injective on
singular homology in every degree and with any coefficients: by homotopy invariance of the Moore
loop functor (`TauCeti.MooreLoopSpace.homotopicRel_comp_map_id`), `Ω²r ∘ Ω²s` is homotopic to
the identity (`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`).

The case of interest is a sphere. Let `s : Sⁿ⁺² → Q` and `c : Q → Sⁿ⁺²` be maps such that
`c ∘ s` has degree `±1`, that is, induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ) ≅ ℤ`; no base point
condition is imposed on either map. Rotations `a`, `b` of the sphere move a base point `x` of the
source and the image of `s x` to the north pole, making `δ = b ∘ c ∘ s ∘ a` a pointed self-map of
degree `±1`. By Hopf's theorem for pointed self-maps of the sphere, `δ ∘ δ ≃ id`
(`ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap`), so
`a ∘ δ ∘ b ∘ c` is a pointed left homotopy inverse of `s` at `x`, and
`(Ω²s)_* : H_*(Ω²Sⁿ⁺²) → H_*(Ω²Q)` is injective at every base point
(`TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`).

This is the homotopy-theoretic part of Lemma 7.6 of Barraud, Damian, Humilière and Oancea. There
`s` embeds `Sᵏ` in a closed manifold `Q`, meeting transversely and in a single point a closed
submanifold `Y` with trivial normal bundle, and `c` is the Pontryagin–Thom collapse of `Q` onto the
fibre sphere of a tubular neighbourhood `Y × Dᵏ`, so that `c ∘ s` has degree one
(`TauCeti.IsFramedTube.injective_singularHomologyMap_map_map`).

## Main results

* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_homotopicRel`: the double loops
  of a map with a pointed left homotopy inverse are injective on singular homology.
* `TauCeti.MooreLoopSpace.injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap`:
  the double loops of a map `s : Sⁿ⁺² → Q` are injective on singular homology at every base point
  when some `c : Q → Sⁿ⁺²` makes `c ∘ s` of degree `±1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Lemma 7.6.
-/

public section

open Metric

namespace TauCeti.MooreLoopSpace

universe u

/-- **Double loops of a homotopy retract.** If a pointed map `s : (X, x) → (Q, q)` has a pointed
left inverse `r` up to homotopy relative to `x`, then `Ω²s : Ω²X → Ω²Q`, on Moore double loop
spaces, is injective on singular homology in every degree and with any coefficients. -/
theorem injective_singularHomologyMap_map_map_of_homotopicRel {X Q : Type u} [TopologicalSpace X]
    [TopologicalSpace Q] {x : X} {q : Q} {s : C(X, Q)} {r : C(Q, X)} (hs : s x = q) (hr : r q = x)
    (h : (r.comp s).HomotopicRel (ContinuousMap.id X) {x}) (k : Type u) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (map (map s hs : C(MooreLoopSpace X x, MooreLoopSpace Q q)) (map_one (map s hs)) :
        C(MooreLoopSpace (MooreLoopSpace X x) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) :=
  -- `Ω²r ∘ Ω²s` is homotopic to the identity, so `(Ω²s)_*` has a left inverse.
  ContinuousMap.injective_singularHomologyMap_of_homotopic_comp_id k m
    (homotopicRel_comp_map_id (homotopicRel_comp_map_id h hs hr) (map_one (map s hs))
      (map_one (map r hr))).homotopic

/-- **Double loops of a sphere mapping with degree `±1` onto a sphere.** Let `s : Sⁿ⁺² → Q` and
`c : Q → Sⁿ⁺²` be maps such that `c ∘ s` induces a surjection on `Hₙ₊₂(Sⁿ⁺²; ℤ)`. Then, at every
base point `x` of the sphere, `Ω²s : Ω²Sⁿ⁺² → Ω²Q`, on Moore double loop spaces, is injective on
singular homology in every degree and with any coefficients. Neither `s` nor `c` need preserve a
chosen base point. -/
theorem injective_singularHomologyMap_map_map_of_surjective_singularHomologyMap {Q : Type}
    [TopologicalSpace Q] {n : ℕ} {x : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1} {q : Q}
    {s : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, Q)}
    {c : C(Q, sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1)} (hs : s x = q)
    (h : Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp s)))
    (k : Type) [Ring k] (m : ℕ) :
    Function.Injective (ContinuousMap.singularHomologyMap k m
      (map (map s hs : C(MooreLoopSpace _ x, MooreLoopSpace Q q)) (map_one (map s hs)) :
        C(MooreLoopSpace (MooreLoopSpace _ x) 1, MooreLoopSpace (MooreLoopSpace Q q) 1))) := by
  -- Rotations `a` and `b` of the sphere move the base points to the north pole `N`: `a N = x`
  -- and `b (c q) = N`.
  have hrot (y z : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) :
      ∃ e : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1 ≃ₜ
        sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1, e y = z := by
    obtain ⟨e, he⟩ := MulAction.exists_smul_eq (EuclideanSpace ℝ (Fin (n + 3)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (n + 3))) y z
    exact ⟨e.unitSphereIsometryEquiv.toHomeomorph, by simpa using he⟩
  obtain ⟨a, ha⟩ := hrot (sphereNorthPole (n + 2)) x
  obtain ⟨b, hb⟩ := hrot (c q) (sphereNorthPole (n + 2))
  -- Homeomorphisms are surjective on homology.
  have hsurj (e : sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) :
      Function.Surjective (ContinuousMap.singularHomologyMap ℤ (n + 2)
        (e : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
          sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1))) :=
    Function.RightInverse.surjective (g := ContinuousMap.singularHomologyMap ℤ (n + 2)
      (e.symm : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
        sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1))) fun y ↦ by
        rw [← ContinuousMap.singularHomologyMap_comp, Homeomorph.toContinuousMap_comp_symm,
          ContinuousMap.singularHomologyMap_id]
  let A : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := a
  let A' : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := a.symm
  let B : C(sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1,
    sphere (0 : EuclideanSpace ℝ (Fin (n + 3))) 1) := b
  -- The pointed self-map `δ = b ∘ c ∘ s ∘ a` of `(Sⁿ⁺², N)` has degree `±1`, so `δ ∘ δ ≃ id`.
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = B.comp ((c.comp s).comp A) := ⟨_, rfl⟩
  have hδ : δ (sphereNorthPole (n + 2)) = sphereNorthPole (n + 2) := by
    simp [hδdef, A, B, ha, hs, hb]
  have hδδ := ContinuousMap.homotopicRel_comp_self_id_of_surjective_singularHomologyMap hδ
    (by
      have hcomp : ⇑(ContinuousMap.singularHomologyMap ℤ (n + 2) δ) =
          ContinuousMap.singularHomologyMap ℤ (n + 2) B ∘
            ContinuousMap.singularHomologyMap ℤ (n + 2) (c.comp s) ∘
              ContinuousMap.singularHomologyMap ℤ (n + 2) A := by
        funext y
        simp only [hδdef, Function.comp_apply, ContinuousMap.singularHomologyMap_comp]
      rw [hcomp]
      exact (hsurj b).comp (h.comp (hsurj a)))
  -- Then `r = a ∘ δ ∘ b ∘ c` is a pointed left homotopy inverse of `s`: `r ∘ s = a ∘ δ² ∘ a⁻¹`.
  refine injective_singularHomologyMap_map_map_of_homotopicRel hs
    (r := A.comp (δ.comp (B.comp c))) (by
      have hB : B (c q) = sphereNorthPole (n + 2) := by simp [B, hb]
      simp only [ContinuousMap.comp_apply]
      rw [hB, hδ]
      exact ha) ?_ k m
  have hr : (A.comp (δ.comp (B.comp c))).comp s = A.comp ((δ.comp δ).comp A') := by
    ext1 y
    simp [hδdef, A, A', B]
  have hpre : A' ⁻¹' {sphereNorthPole (n + 2)} = {x} := by
    ext y
    simp [A', ← ha, a.symm_apply_eq]
  have hid : A.comp ((ContinuousMap.id _).comp A') = ContinuousMap.id _ := by
    ext1 y
    simp [A, A']
  simpa only [hr, hpre, hid] using (hδδ.precomp A').comp_continuousMap A

end TauCeti.MooreLoopSpace
