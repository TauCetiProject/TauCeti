/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Relative.Compression
public import TauCeti.Topology.CWComplex.Classical.Compression
public import TauCeti.Topology.Homotopy.Extension.Cube

/-!
# Maps of disk pairs and relative homotopy groups

The relative homotopy set `π_{n+1}(Y, B, b) = TauCeti.RelHomotopyGroup (Fin n) _` is built from
relative cubes: maps `I × Iⁿ → Y` sending the face `{0} × Iⁿ` into `B` and the rest of the
boundary of the cube to `b`. The cells of a CW complex are instead attached along maps of pairs
`(Dⁿ⁺¹, Sⁿ) → (Y, B)` that need not be constant on any part of the sphere. This file connects the
two, and so states the compression lemma in its usual form (Hatcher, Lemma 4.6): if
`π_n(Y, B, b) = 0` for every `b ∈ B` and every `n` such that a relative CW complex `(C, D)` has
`n`-cells, then every map `(C, D) → (Y, B)` is homotopic relative to `D` to a map into `B`
(`TauCeti.exists_homotopicRel_range_subset_of_relHomotopyGroup`).

* A map of pairs `g : (I × Iⁿ, ∂(I × Iⁿ)) → (Y, B)` is homotopic, through maps of pairs, to a
  relative cube (`TauCeti.exists_homotopicWith_relGenLoop`). The open box
  `{1} × Iⁿ ∪ I × ∂Iⁿ` contracts to the centre of its top face; along the face `{0} × Iⁿ`, whose
  boundary lies in the open box, this contraction extends to a homotopy into `B` because `∂Iⁿ`
  has the homotopy extension property in `Iⁿ`. The resulting homotopy of `g` on the boundary of
  the cube extends over the cube because that boundary has the homotopy extension property too
  (`TauCeti.hasHomotopyExtensionProperty_prodBoundary`).
* If `π_{n+1}(Y, B, b)` is trivial for every `b ∈ B`, every map of pairs
  `(Dⁿ⁺¹, Sⁿ) → (Y, B)` is homotopic relative to `Sⁿ` to a map into `B`
  (`TauCeti.exists_homotopicRel_range_subset_of_subsingleton`). Here `Dⁿ⁺¹` and `Sⁿ` are the closed
  unit ball and the unit sphere of the sup norm on `Fin (n + 1) → ℝ`, the domains of the
  characteristic maps of `Topology.RelCWComplex`; they are the cube `I × Iⁿ` and its boundary. By
  the previous item and the triviality of the resulting relative cube, the map is homotopic through
  maps of pairs to a constant map with value in `B`, and sweeping that homotopy across the ball
  (`ContinuousMap.HomotopicWith.exists_homotopicRel_range_subset`) gives a homotopy relative to the
  sphere.

The hypothesis of the compression lemma for `0`-cells is that every point of `Y` is joined by a
path to a point of `B`, which is what `π_0(Y, B, b) = 0` means; relative homotopy sets are only
defined here in positive degrees.

## Main declarations

* `TauCeti.exists_homotopicWith_relGenLoop`: a map of pairs out of the cube `I × Iⁿ` is homotopic
  through maps of pairs to a relative cube.
* `TauCeti.exists_homotopyWith_relGenLoop_of_openBox`: the same, by a homotopy that follows a
  prescribed contraction of the open box `{1} × Iⁿ ∪ I × ∂Iⁿ`, so that maps sharing a face of the
  cube can be deformed compatibly.
* `TauCeti.exists_homotopicRel_range_subset_of_subsingleton`: maps of disk pairs compress into `B`
  when the relative homotopy sets vanish.
* `TauCeti.exists_homotopicRel_range_subset_of_relHomotopyGroup`: **the compression lemma**, with
  its hypotheses on relative homotopy sets.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 4.1, Lemma 4.6 (the compression lemma) and the compression criterion preceding
  Theorem 4.3.
-/

public section

noncomputable section

universe u v

open Metric Set Topology Topology.RelCWComplex
open scoped unitInterval

namespace TauCeti

/-! ### Deforming a map of pairs into a relative cube -/

variable {N : Type v} [Finite N] {Y : TopCat.{u}} {B : Set Y}

/-- Let `R` be a deformation of the open box `{1} × I^N ∪ I × ∂I^N` of `I × I^N` inside the
boundary of the cube, starting at the identity. A map of pairs
`g : (I × I^N, ∂(I × I^N)) → (Y, B)`, restricted to the boundary of the cube, is homotopic through
maps into `B` to a map that agrees with `g ∘ R 1` on the open box, by a homotopy that is `g ∘ R t`
on the open box at every time `t`. -/
private theorem exists_boundaryHomotopy (R : I → I × (I^N) → I × (I^N))
    (hR : Continuous fun q : I × (I × I^N) ↦ R q.1 q.2) (hR₀ : ∀ z, R 0 z = z)
    (hRJ : ∀ {z : I × I^N}, (z.1 = 1 ∨ z.2 ∈ Cube.boundary N) → ∀ t, R t z ∈ Cube.prodBoundary N)
    (g : C(I × I^N, Y)) (hg : MapsTo g (Cube.prodBoundary N) B) :
    ∃ h : C(I × Cube.prodBoundary N, Y), (∀ z, h (0, z) = g z) ∧ (∀ t z, h (t, z) ∈ B) ∧
      ∀ t (z : Cube.prodBoundary N), ((z : I × I^N).1 = 1 ∨ (z : I × I^N).2 ∈ Cube.boundary N) →
        h (t, z) = g (R t z) := by
  classical
  -- On the open box, `h` is `g` composed with the deformation `R`. On the face `{0} × I^N`, where
  -- the deformation is already prescribed on the boundary, it is the extension `K` with values in
  -- `B` provided by the homotopy extension property of `∂I^N`.
  have hbd := hasHomotopyExtensionProperty_cubeBoundary (N := N)
  obtain ⟨K, hK₀, hK⟩ := hbd.exists_extension_of_isClosed hbd.isClosed
    (⟨fun y ↦ ⟨g (0, y), hg (Cube.mk_zero_mem_prodBoundary y)⟩, by fun_prop⟩ : C(I^N, B))
    ⟨fun q ↦ ⟨g (R q.1 (0, q.2)), hg (hRJ (.inr q.2.2) _)⟩,
      (g.continuous.comp (hR.comp (continuous_fst.prodMk (continuous_const.prodMk
        (continuous_subtype_val.comp continuous_snd))))).subtype_mk _⟩
    fun a ↦ by simp [hR₀]
  let h : I × (I × I^N) → Y := fun q ↦
    if q.2.1 = 0 then (K (q.1, q.2.2) : Y) else g (R q.1 q.2)
  let S : Set (I × (I × I^N)) := {q | q.2.1 = 1 ∨ q.2.2 ∈ Cube.boundary N}
  have hS : EqOn h (fun q ↦ g (R q.1 q.2)) S := by
    rintro ⟨t, s, y⟩ hq
    by_cases hs : s = 0
    · subst hs
      have hy : y ∈ Cube.boundary N := hq.resolve_left fun h ↦ zero_ne_one' I h
      simpa [h] using congrArg Subtype.val (hK t ⟨y, hy⟩)
    · simp [h, hs]
  -- The two pieces are closed and `h` is continuous on each of them.
  have hcont : ContinuousOn h ({q | q.2.1 = 0} ∪ S) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_eq (by fun_prop) continuous_const)
      ((isClosed_eq (by fun_prop) continuous_const).union
        (hbd.isClosed.preimage (by fun_prop)))
    · refine (continuous_subtype_val.comp (K.continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))).continuousOn.congr ?_
      intro q hq
      simp [h, show q.2.1 = 0 from hq]
    · exact (g.continuous.comp hR).continuousOn.congr hS
  have hmem (q : I × Cube.prodBoundary N) : (q.1, (q.2 : I × I^N)) ∈ {q | q.2.1 = 0} ∪ S := by
    rcases Cube.mem_prodBoundary_iff.1 q.2.2 with (hs | hs) | hy
    exacts [.inl hs, .inr (.inl hs), .inr (.inr hy)]
  have hS' {z : I × I^N} (hz : z ∈ Cube.prodBoundary N) (hs : z.1 ≠ 0) :
      z.1 = 1 ∨ z.2 ∈ Cube.boundary N :=
    (Cube.mem_prodBoundary_iff.1 hz).imp_left (·.resolve_left hs)
  refine ⟨⟨fun q ↦ h (q.1, q.2), hcont.comp_continuous (by fun_prop) hmem⟩, fun z ↦ ?_,
    fun t z ↦ ?_, fun t z hz ↦ hS (show (t, (z : I × I^N)) ∈ S from hz)⟩
  · by_cases hz : (z : I × I^N).1 = 0
    · simp only [ContinuousMap.coe_mk, h, hz, ite_true, hK₀]
      exact congrArg g (Prod.ext hz.symm rfl)
    · simp [h, hz, hR₀]
  · by_cases hs : (z : I × I^N).1 = 0
    · simp only [ContinuousMap.coe_mk, h, hs, ite_true]
      exact (K (t, (z : I × I^N).2)).2
    · rw [ContinuousMap.coe_mk, hS (show (t, (z : I × I^N)) ∈ S from hS' z.2 hs)]
      exact hg (hRJ (hS' z.2 hs) t)

/-- **A map of pairs is homotopic to a relative cube along a contraction of the open box.** Let
`R` be a deformation of the open box `{1} × I^N ∪ I × ∂I^N` of `I × I^N` inside the boundary of the
cube, starting at the identity and ending at the constant map to a point `v`. Every map of pairs
`g : (I × I^N, ∂(I × I^N)) → (Y, B)` is homotopic, through maps of pairs, to a relative cube at
`g v`, by a homotopy that is `g ∘ R t` on the open box at every time `t`. -/
theorem exists_homotopyWith_relGenLoop_of_openBox (R : I → I × (I^N) → I × (I^N))
    (hR : Continuous fun q : I × (I × I^N) ↦ R q.1 q.2) (hR₀ : ∀ z, R 0 z = z)
    (hRJ : ∀ {z : I × I^N}, (z.1 = 1 ∨ z.2 ∈ Cube.boundary N) → ∀ t, R t z ∈ Cube.prodBoundary N)
    {v : I × I^N} (hR₁ : ∀ {z : I × I^N}, (z.1 = 1 ∨ z.2 ∈ Cube.boundary N) → R 1 z = v)
    (g : C(I × I^N, Y)) (hg : MapsTo g (Cube.prodBoundary N) B) :
    ∃ b : B, (b : Y) = g v ∧ ∃ p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩,
      ∃ G : g.HomotopyWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B,
        ∀ t {z : I × I^N}, (z.1 = 1 ∨ z.2 ∈ Cube.boundary N) →
          G.toContinuousMap (t, z) = g (R t z) := by
  -- Extend the homotopy of `g` on the boundary of the cube over the whole cube.
  obtain ⟨h, h₀, hB, hJ⟩ := exists_boundaryHomotopy R hR hR₀ hRJ g hg
  have hbd := hasHomotopyExtensionProperty_prodBoundary (N := N)
  obtain ⟨G, hG₀, hG⟩ := hbd.exists_extension_of_isClosed hbd.isClosed g h h₀
  have hGJ (t : I) {z : I × I^N} (hz : z.1 = 1 ∨ z.2 ∈ Cube.boundary N) : G (t, z) = g (R t z) :=
    (hG t ⟨z, Cube.mk_mem_prodBoundary hz⟩).trans (hJ t ⟨z, _⟩ hz)
  -- At time `1` the extension is a relative cube.
  have hface (t : I^N) : G (1, (0, t)) ∈ range (TopPair.ofSubset B).map := by
    rw [TopPair.range_ofSubset_map, hG 1 ⟨(0, t), Cube.mk_zero_mem_prodBoundary t⟩]
    exact hB 1 _
  let c : C(I × I^N, Y) := ⟨fun z ↦ G (1, z), G.continuous.comp (continuous_const.prodMk
    continuous_id)⟩
  have hv : g v ∈ B := by
    simpa only [hR₁ (z := (1, fun _ ↦ 0)) (.inl rfl)] using
      hg (hRJ (z := (1, fun _ ↦ 0)) (.inl rfl) 1)
  refine ⟨⟨g v, hv⟩, rfl, RelGenLoop.mk c hface fun s t hst ↦
      (hGJ 1 hst).trans (congrArg g (hR₁ hst)),
    { toFun := G
      map_zero_left := hG₀
      map_one_left z := (DFunLike.congr_fun
        (RelGenLoop.coe_mk (X := ⟨TopPair.ofSubset B, ⟨g v, hv⟩⟩) c hface _) z).symm
      prop' t z hz := (hG t ⟨z, hz⟩).symm ▸ hB t ⟨z, hz⟩ }, fun t z hz ↦ hGJ t hz⟩

/-- **A map of pairs `(I × I^N, ∂(I × I^N)) → (Y, B)` is homotopic, through maps of pairs, to a
relative cube.** Its basepoint `b ∈ B` is the value of the given map at the centre of the face
`{1} × I^N`. -/
theorem exists_homotopicWith_relGenLoop (g : C(I × I^N, Y))
    (hg : MapsTo g (Cube.prodBoundary N) B) :
    ∃ b : B, (b : Y) = g (1, cubeCenter) ∧ ∃ p : RelGenLoop N ⟨TopPair.ofSubset B, b⟩,
      g.HomotopicWith p.1 fun f ↦ MapsTo f (Cube.prodBoundary N) B :=
  let ⟨b, hb, p, G, _⟩ := exists_homotopyWith_relGenLoop_of_openBox openBoxContraction
    continuous_openBoxContraction openBoxContraction_zero
    (fun hz t ↦ openBoxContraction_mem_prodBoundary hz t) (fun _ ↦ openBoxContraction_one _) g hg
  ⟨b, hb, p, ⟨G⟩⟩

/-! ### Compressing maps of disk pairs -/

/-- **Compressing a map of disk pairs.** Let `B ⊆ Y` be such that the relative homotopy set
`π_{n+1}(Y, B, b)` is trivial for every `b ∈ B`. Then every map from the closed unit ball of the
sup norm on `Fin (n + 1) → ℝ` to `Y` sending the unit sphere into `B` is homotopic, relative to the
unit sphere, to a map with values in `B`. -/
theorem exists_homotopicRel_range_subset_of_subsingleton {n : ℕ}
    (h : ∀ b : B, Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset B, b⟩))
    (g : C(closedBall (0 : Fin (n + 1) → ℝ) 1, Y))
    (hg : MapsTo g {x | (x : Fin (n + 1) → ℝ) ∈ sphere 0 1} B) :
    ∃ g' : C(closedBall (0 : Fin (n + 1) → ℝ) 1, Y),
      g.HomotopicRel g' {x | (x : Fin (n + 1) → ℝ) ∈ sphere 0 1} ∧ range g' ⊆ B := by
  -- Read `g` on the cube `I × I^(Fin n)` and deform it, through maps of pairs, to a relative cube.
  -- That relative cube is trivial, so it is homotopic through relative cubes to the constant cube.
  -- Back on the ball, `g` is homotopic through maps of pairs to a constant map with value in `B`.
  let e := closedBallHomeomorphProd n
  obtain ⟨b, -, p, ⟨G⟩⟩ := exists_homotopicWith_relGenLoop
    (g.comp (e.symm : C(I × I^(Fin n), _)))
    fun z hz ↦ hg ((closedBallHomeomorphProd_mem_prodBoundary_iff _).1 (by simpa [e] using hz))
  obtain ⟨F⟩ := RelGenLoop.homotopic_iff.1 (RelHomotopyGroup.mk_eq_mk.1
    (Subsingleton.elim (RelHomotopyGroup.mk p) (RelHomotopyGroup.mk RelGenLoop.const)))
  let H := G.trans
    { toHomotopy := F.toHomotopy
      prop' t := (RelGenLoop.mapsTo_prodBoundary (F.prop t)).mono_right
        TopPair.range_ofSubset_map.subset }
  refine ContinuousMap.HomotopicWith.exists_homotopicRel_range_subset
    (g₁ := ContinuousMap.const _ (b : Y))
    ⟨{ toFun q := H.toContinuousMap (q.1, e q.2)
       continuous_toFun := H.toContinuousMap.continuous.comp
         (continuous_fst.prodMk (e.continuous.comp continuous_snd))
       map_zero_left x := (H.apply_zero (e x)).trans (by simp [e])
       map_one_left x := (H.apply_one (e x)).trans (RelGenLoop.const_apply (e x))
       prop' t x hx := H.prop t ((closedBallHomeomorphProd_mem_prodBoundary_iff x).2 hx) }⟩ ?_
  rintro _ ⟨_, rfl⟩
  exact b.2

/-! ### The compression lemma -/

/-- **The compression lemma** in terms of relative homotopy groups (Hatcher, Lemma 4.6). Let `C`
be a relative CW complex with base `D`, and let `B ⊆ Y`. Suppose that every point of `Y` is joined
by a path to a point of `B` if `C` has `0`-cells, and that the relative homotopy set
`π_{n+1}(Y, B, b)` is trivial for every `b ∈ B` if `C` has `(n + 1)`-cells. Then every map
`f : C → Y` sending `D` into `B` is homotopic, relative to `D`, to a map into `B`. -/
theorem exists_homotopicRel_range_subset_of_relHomotopyGroup
    {X : Type*} [TopologicalSpace X] [T2Space X] {C D : Set X} [RelCWComplex C D]
    (h₀ : Nonempty (cell C 0) → ∀ y : Y, ∃ b ∈ B, Joined y b)
    (h : ∀ n, Nonempty (cell C (n + 1)) → ∀ b : B,
      Subsingleton (RelHomotopyGroup (Fin n) ⟨TopPair.ofSubset B, b⟩))
    (f : C(C, Y)) (hf : MapsTo f {x : C | (x : X) ∈ D} B) :
    ∃ g : C(C, Y), f.HomotopicRel g {x : C | (x : X) ∈ D} ∧ range g ⊆ B := by
  refine exists_homotopicRel_range_subset (fun n hn g hg ↦ ?_) f hf
  rcases n with _ | n
  · -- The closed unit ball of `Fin 0 → ℝ` is a point, and its unit sphere is empty.
    have hS (x : closedBall (0 : Fin 0 → ℝ) 1) : (x : Fin 0 → ℝ) ∉ sphere 0 1 := fun hx ↦ by
      rw [mem_sphere_zero_iff_norm, Subsingleton.elim (x : Fin 0 → ℝ) 0, norm_zero] at hx
      exact zero_ne_one hx
    obtain ⟨b, hb, ⟨γ⟩⟩ := h₀ hn (g ⟨0, mem_closedBall_self zero_le_one⟩)
    refine ⟨ContinuousMap.const _ b,
      ⟨{ toFun q := γ q.1
         map_zero_left x := by rw [γ.source]; exact congrArg g (Subsingleton.elim _ _)
         map_one_left _ := γ.target
         prop' _ x hx := absurd hx (hS x) }⟩, ?_⟩
    rintro _ ⟨_, rfl⟩
    exact hb
  · exact exists_homotopicRel_range_subset_of_subsingleton (h n hn) g hg

end TauCeti
