/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.Geometry.Manifold.Morse.Cell.Homology
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic

/-!
# The cells of the height function on the sphere

The height function `h x = ⟪x, v⟫` on the unit sphere `Sⁿ` of an `(n + 1)`-dimensional real inner
product space has two critical points, the south pole `-v` of index `0` and the north pole `v` of
index `n`. Milnor's cell attachment theorem therefore builds `Sⁿ` from a `0`-cell by attaching one
`n`-cell. This file proves the resulting statements about the homology of the sublevels of the
height.

* Every sublevel `{h ≤ a}` with `-1 ≤ a < 1` is contractible
  (`TauCeti.contractibleSpace_sublevel_sphereHeight`). It misses the north pole, and stereographic
  projection from the north pole carries it onto a closed ball about the origin. So, up to
  homotopy, the lower sublevel is the `0`-cell at the south pole; in particular it is path
  connected.
* For `-1 < a < 1 < b`, the relative homology of the sublevel pair `({h ≤ b}, {h ≤ a})` is one
  copy of the coefficients in degree `n` and vanishes in every other degree
  (`TauCeti.nonempty_singularHomology_sublevelPair_sphereHeight_iso` and
  `TauCeti.isZero_singularHomology_sublevelPair_sphereHeight`): the band contains the single
  critical point `v`, of index `n`.
* For `-1 ≤ a < 1` and `a ≤ b`, the quotient map `Hₖ₊₁({h ≤ b}) ⟶ Hₖ₊₁({h ≤ b}, {h ≤ a})` is
  an isomorphism (`TauCeti.isIso_singularHomologyπ_sublevelPair_sphereHeight`), since the lower
  sublevel is contractible. With the previous item, for `-1 < a < 1 < b` and `n ≥ 1` the homology
  `Hₙ({h ≤ b})` is one copy of the coefficients, carried by the cell at the north pole. For
  `b ≥ 1` the subspace `{h ≤ b}` is the whole sphere as a set, so this is the cell-structure
  reading of `Hₙ(Sⁿ)`, and of `H₁(S¹; ℤ) ≅ ℤ` for the circle with integer coefficients; the
  identification of the homology of `{h ≤ b}` with that of `Sⁿ` is not formalized here. The
  homology of spheres itself is computed by the Mayer–Vietoris sequence in
  `TauCeti.reducedSingularHomologySphereIso`.
* Consequently, the connecting morphism `Hₖ₊₁({h ≤ b}, {h ≤ a}) ⟶ Hₖ({h ≤ a})` vanishes
  (`TauCeti.singularHomologyδ_sublevelPair_sphereHeight_eq_zero`): the top cell is a cycle. For
  the circle, `n = 1`, the cell at the maximum is made of two descending arcs, whose ends are the
  two points of the attaching sphere `S⁰`; the vanishing of `H₁({h ≤ b}, {h ≤ a}) ⟶ H₀({h ≤ a})`
  says that both ends attach to the same component of the lower sublevel, the one of the minimum.
  This is the opposite of the double well `(x² - 1)²` on `ℝ`, whose two attaching points lie in
  different components of the lower sublevel.

## Main results

* `TauCeti.contractibleSpace_sublevel_sphereHeight`: the lower sublevels of the height are
  contractible.
* `TauCeti.nonempty_singularHomology_sublevelPair_sphereHeight_iso`,
  `TauCeti.isZero_singularHomology_sublevelPair_sphereHeight`: the relative homology of the band
  across the maximum.
* `TauCeti.isIso_singularHomologyπ_sublevelPair_sphereHeight`: the homology of an upper sublevel
  maps isomorphically to the relative homology of the band across the maximum.
* `TauCeti.singularHomologyδ_sublevelPair_sphereHeight_eq_zero`: the top cell is a cycle.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §3, Theorems 3.1, 3.2 and 3.5.
-/

public section

open CategoryTheory Limits Module Set Metric
open scoped Manifold InnerProductSpace RealInnerProductSpace

universe u v w

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The lower sublevels of the height are contractible.** For `-1 ≤ a < 1`, the sublevel
`{x | ⟪x, v⟫ ≤ a}` of the unit sphere is contractible: it misses the north pole `v`, and the
stereographic projection from `v` carries it onto a closed ball about the origin. -/
theorem contractibleSpace_sublevel_sphereHeight (v : sphere (0 : E) 1) {a : ℝ} (ha : -1 ≤ a)
    (ha' : a < 1) : ContractibleSpace {x | sphereHeight v x ≤ a} := by
  set e := stereographic (norm_eq_of_mem_sphere v)
  set s := {x | sphereHeight v x ≤ a}
  have hs : s ⊆ e.source := by
    intro x hx hxv
    rw [mem_singleton_iff] at hxv
    simp only [s, mem_ofPred_eq, hxv, Subtype.coe_eta, sphereHeight_self] at hx
    linarith
  have himage : e '' s = {w | -stereographicHeight w ≤ a} := by
    rw [e.image_eq_target_inter_inv_preimage hs]
    ext w
    simp only [e, s, stereographic_target, univ_inter, mem_preimage, mem_ofPred_eq,
      sphereHeight_stereographic_symm_apply]
  -- The image is star-convex about the origin, since the height decreases with `‖w‖`.
  have hstar : StarConvex ℝ 0 (e '' s) := by
    rw [himage]
    intro w hw b c hb hc hbc
    simp only [mem_ofPred_eq, smul_zero, zero_add] at hw ⊢
    have hc1 : c ≤ 1 := by linarith
    have : ‖c • w‖ ≤ ‖w‖ := by
      rw [norm_smul, Real.norm_of_nonneg hc]
      exact mul_le_of_le_one_left (norm_nonneg w) hc1
    linarith [stereographicHeight_le_stereographicHeight this]
  have hne : (e '' s).Nonempty := ⟨0, by
    rw [himage, mem_ofPred_eq, stereographicHeight_apply]
    norm_num
    linarith⟩
  have := hstar.contractibleSpace hne
  exact (e.homeomorphOfImageSubsetSource hs rfl).contractibleSpace

/-- The subspace `{h ≤ a}` of the sublevel pair of the height is contractible for
`-1 ≤ a < 1`. -/
private theorem contractibleSpace_sublevelPair_snd_sphereHeight (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 ≤ a) (ha' : a < 1) (hab : a ≤ b) :
    ContractibleSpace (sublevelPair (sphereHeight v) hab).snd :=
  -- The subspace of `sublevelPair` is `TopCat.of {x | sphereHeight v x ≤ a}` by definition.
  contractibleSpace_sublevel_sphereHeight v ha ha'

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

variable {A : Type v} [Category.{w} A] [Abelian A] [HasCoproducts.{u} A] (R : A)

/-- For `-1 < a < 1 < b`, the north pole `v` is the only critical point of the height whose value
lies in `[a, b]`, so the band `{a ≤ h ≤ b}` crosses the single critical level `1`. -/
private theorem sphereHeight_eq_one_of_mem_criticalPoints (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 < a) {x : sphere (0 : E) 1} (hx : x ∈ criticalPoints (𝓡 n) (sphereHeight v))
    (hxab : sphereHeight v x ∈ Icc a b) : sphereHeight v x = 1 := by
  rw [criticalPoints_sphereHeight, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact sphereHeight_self x
  · rw [sphereHeight_neg_self] at hxab
    linarith [hxab.1]

/-- For `-1 < a < 1 < b`, the relative homology of the sublevel pair `({h ≤ b}, {h ≤ a})` of the
height in degree `k` is free on the critical points of level `1` and Morse index `k`; the only
such point, when `k = n`, is the north pole. -/
private theorem nonempty_singularHomology_sublevelPair_sphereHeight_iso_sigma
    (v : sphere (0 : E) 1) {a b : ℝ} (ha : -1 < a) (ha' : a < 1) (hb : 1 < b) (k : ℕ) :
    Nonempty ((sublevelPair (sphereHeight v) (ha'.trans hb).le).singularHomology R k ≅
      ∐ fun _ : {p : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1}) //
        manifoldMorseIndex (𝓡 n) (sphereHeight v) p = k} ↦ R) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hf := isMorse_sphereHeight (n := n) v
  exact hf.nonempty_singularHomology_sublevelPair_iso_sigma ha' hb
    (isClosed_Icc.preimage hf.contMDiff.continuous).isCompact
    (fun x hx hxab ↦ sphereHeight_eq_one_of_mem_criticalPoints v ha hx hxab) R k

/-- **The band across the maximum of the height is an `n`-cell.** For `-1 < a < 1 < b`, the
relative homology `Hₙ({h ≤ b}, {h ≤ a})` of the sublevel pair of the height on `Sⁿ` is one copy of
the coefficients: the band contains the single critical point `v`, of index `n`. -/
theorem nonempty_singularHomology_sublevelPair_sphereHeight_iso (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 < a) (ha' : a < 1) (hb : 1 < b) :
    Nonempty ((sublevelPair (sphereHeight v) (ha'.trans hb).le).singularHomology R n ≅ R) := by
  obtain ⟨e⟩ :=
    nonempty_singularHomology_sublevelPair_sphereHeight_iso_sigma (n := n) R v ha ha' hb n
  let p : {p : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1}) //
      manifoldMorseIndex (𝓡 n) (sphereHeight v) p = n} :=
    ⟨⟨v, by simp, sphereHeight_self v⟩, manifoldMorseIndex_sphereHeight_self v⟩
  have : Unique {p : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1}) //
      manifoldMorseIndex (𝓡 n) (sphereHeight v) p = n} :=
    { default := p
      uniq q := Subtype.ext <| Subtype.ext <| sphereHeight_eq_one_iff.1 q.1.2.2 }
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- For `-1 < a < 1 < b`, the relative homology `Hₖ({h ≤ b}, {h ≤ a})` of the sublevel pair of the
height on `Sⁿ` vanishes in every degree `k ≠ n`. -/
theorem isZero_singularHomology_sublevelPair_sphereHeight (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 < a) (ha' : a < 1) (hb : 1 < b) {k : ℕ} (hk : k ≠ n) :
    IsZero ((sublevelPair (sphereHeight v) (ha'.trans hb).le).singularHomology R k) := by
  obtain ⟨e⟩ :=
    nonempty_singularHomology_sublevelPair_sphereHeight_iso_sigma (n := n) R v ha ha' hb k
  have : IsEmpty {p : ↥(criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1}) //
      manifoldMorseIndex (𝓡 n) (sphereHeight v) p = k} := ⟨fun q ↦ by
    have hq := q.2
    rw [sphereHeight_eq_one_iff.1 q.1.2.2, manifoldMorseIndex_sphereHeight_self] at hq
    exact hk hq.symm⟩
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun q ↦ isEmptyElim q)).of_iso e

/-- **The homology of an upper sublevel is carried by the top cell of the height.** For
`-1 ≤ a < 1` and `a ≤ b`, the quotient map `Hₖ₊₁({h ≤ b}) ⟶ Hₖ₊₁({h ≤ b}, {h ≤ a})` is an
isomorphism, since the lower sublevel is contractible. The source is the homology of the subspace
`{h ≤ b}`, which is the whole sphere as a set when `b ≥ 1`; its identification with the homology of
`Sⁿ` is not stated here. For `a > -1`, `b > 1` and `k + 1 = n` the target is one copy of the
coefficients (`TauCeti.nonempty_singularHomology_sublevelPair_sphereHeight_iso`). -/
theorem isIso_singularHomologyπ_sublevelPair_sphereHeight (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 ≤ a) (ha' : a < 1) (hab : a ≤ b) (k : ℕ) :
    IsIso ((sublevelPair (sphereHeight v) hab).singularHomologyπ R (k + 1)) := by
  have := contractibleSpace_sublevelPair_snd_sphereHeight v ha ha' hab
  exact TopPair.isIso_singularHomologyπ_of_contractibleSpace _ R k

/-- **The top cell of the height is a cycle.** For `-1 ≤ a < 1` and `a ≤ b`, the connecting
morphism `Hₖ₊₁({h ≤ b}, {h ≤ a}) ⟶ Hₖ({h ≤ a})` of the sublevel pair of the height vanishes. On the
circle, in degree `0`, this says that the two ends of the cell at the maximum attach to the same
component of the lower sublevel. -/
theorem singularHomologyδ_sublevelPair_sphereHeight_eq_zero (v : sphere (0 : E) 1) {a b : ℝ}
    (ha : -1 ≤ a) (ha' : a < 1) (hab : a ≤ b) (k : ℕ) :
    (sublevelPair (sphereHeight v) hab).singularHomologyδ R (k + 1) k = 0 := by
  have := contractibleSpace_sublevelPair_snd_sphereHeight v ha ha' hab
  exact TopPair.singularHomologyδ_eq_zero_of_contractibleSpace _ R k

end TauCeti
