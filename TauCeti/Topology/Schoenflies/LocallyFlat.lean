/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Brown
public import TauCeti.Topology.Schoenflies.Standard
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension
import TauCeti.Topology.Circle.Schoenflies
import TauCeti.Topology.ConnectedComponents

/-!
# The generalized Schoenflies theorem for locally flat spheres

Combining M. Brown's bicollaring theorem (`TauCeti.IsLocallyFlat.isBicollared_of_finrank_eq`) with
his generalized Schoenflies theorem
(`TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range` for `m ≥ 2`,
`TauCeti.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one` for `m = 1`,
and the zero-dimensional degenerate case `m = 0`) yields the **locally flat generalized Schoenflies
theorem** in every dimension `m ≥ 0`: let `σ : S(E) → S(F)` be a codimension-one locally flat
embedding between unit spheres of real normed spaces (`finrank ℝ F = finrank ℝ E + 1`). Then the
complement of `range σ` in `S(F)` has two connected components, and the closure of each component
is homeomorphic to the closed unit ball of `E` by a homeomorphism inverting `σ` on `range σ` and
sending `range σ` onto the boundary sphere `S(E)`. Equivalently, `σ` extends across each side to a
closed embedding `closedBall (0 : E) 1 → S(F)` carrying `ball (0 : E) 1` onto that complementary
component.

Two unifications happen along the way:

* On the `IsBicollar` layer, `TauCeti.Topology.Schoenflies.Disc` assumes `1 < finrank ℝ E` and an
  inner product on `F`, whereas `TauCeti.Topology.Circle.Schoenflies` treats `finrank ℝ E = 1` for
  any real normed space `F`. Transporting the ambient sphere to a Euclidean sphere via
  `TauCeti.sphereHomeomorphOfFinrankEq` removes the inner-product assumption for `1 < finrank ℝ E`
  and combines `m = 0`, `m = 1`, and `m ≥ 2` into a single statement for all real normed spaces
  `E`, `F` with `finrank ℝ F = finrank ℝ E + 1`.
* When `F` is a real inner product space, gluing the two complementary discs along `range σ` via
  `TauCeti.exists_homeomorph_sphere_of_union_closedBall_orthogonal` gives an ambient
  self-homeomorphism of `S(F)` straightening `σ` to `TauCeti.equatorInclusion` and carrying a
  chosen complementary closure onto the closed positive hemisphere, in every dimension `m ≥ 0`
  (including `finrank ℝ E = 1`, where collar sides can twist between the two points of `S⁰` even
  though the two complementary arcs still form a standard hemisphere pair).

Finally, `TauCeti.isBicollared_equatorInclusion` and `TauCeti.isLocallyFlat_equatorInclusion` show
that the standard equatorial inclusion `S((ℝ ∙ p)ᗮ) → S(F)` is itself bicollared and locally flat,
using `TauCeti.latitudeHomeomorphComplPair` as an explicit global bicollar onto `S(F) \ {p, -p}`.

## Main results

* `TauCeti.isBicollared_equatorInclusion` and `TauCeti.isLocallyFlat_equatorInclusion`: the
  equatorial sphere around a unit vector `p` in a real inner product space is bicollared and
  locally flat.
* `TauCeti.exists_connectedComponentIn_compl_range_sphere_eq_union`: the complement of an embedded
  codimension-one sphere splits into the connected component of any chosen exterior point and one
  disjoint second component.
* `TauCeti.IsBicollar.closure_connectedComponentIn_compl_range_of_finrank_eq`,
  `TauCeti.IsBicollar.frontier_connectedComponentIn_compl_range_of_finrank_eq`, and
  `TauCeti.IsBicollar.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq`:
  Brown's generalized Schoenflies theorem for bicollared spheres in unit spheres of arbitrary real
  normed spaces in every dimension `m ≥ 0`.
* `TauCeti.IsBicollar.exists_isClosedEmbedding_closedBall` and
  `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_closedBall`: closed-ball extension form of the
  Schoenflies theorem on either side of `range σ`.
* `TauCeti.IsLocallyFlat.exists_homeomorph_closure_connectedComponentIn_compl_range` and
  `TauCeti.IsLocallyFlat.exists_homeomorph_sphere_eq_equatorInclusion`: the locally flat
  generalized Schoenflies theorem and ambient equatorial straightening in every dimension `m ≥ 0`.

## References

* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
-/

public section

open Function Metric Module Set Topology
open scoped RealInnerProductSpace

namespace TauCeti

/-! ### Equatorial spheres are bicollared and locally flat -/

section Equator

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **The equatorial inclusion is globally bicollared.** In any real inner product space `F`, the
equatorial sphere `S((ℝ ∙ p)ᗮ) → S(F)` around a unit vector `p` admits a global bicollar. -/
theorem isBicollared_equatorInclusion (p : sphere (0 : F) 1) :
    IsBicollared (equatorInclusion (r := 1) (p : F)) := by
  have hball : ball (0 : ℝ) 1 = Ioo (-1 : ℝ) 1 := by
    ext t
    simp [abs_lt]
  let ρ : ℝ ≃ₜ Ioo (-1 : ℝ) 1 := Homeomorph.unitBall.trans (Homeomorph.setCongr hball)
  have hopen : IsOpen (({p, -p} : Set (sphere (0 : F) 1))ᶜ) :=
    ((Set.finite_singleton (-p)).insert p).isClosed.isOpen_compl
  let e := ((Homeomorph.refl _).prodCongr ρ).trans (latitudeHomeomorphComplPair p)
  refine isBicollared_iff.2 ⟨Subtype.val ∘ e,
    hopen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding, fun u ↦ ?_⟩
  have hρ0 : (ρ 0 : ℝ) = 0 := Homeomorph.coe_unitBall_apply_zero
  have he : ((Subtype.val ∘ e) (u, 0) : F) = (latitude p u (ρ 0) : F) := by simp [e]
  apply Subtype.ext
  rw [he, hρ0, coe_latitude_of_mem p u ⟨by norm_num, by norm_num⟩]
  simp [coe_equatorInclusion_apply]

/-- **The equatorial inclusion is locally flat.** When the equatorial sphere `S((ℝ ∙ p)ᗮ)` is
charted on a model space `H`, `TauCeti.equatorInclusion (p : F)` is locally flat with
one-dimensional complementary model `ℝ`. -/
theorem isLocallyFlat_equatorInclusion (p : sphere (0 : F) 1) {H : Type*} [TopologicalSpace H]
    [ChartedSpace H (sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)] :
    IsLocallyFlat H ℝ (equatorInclusion (r := 1) (p : F)) :=
  (isBicollared_equatorInclusion p).isLocallyFlat

end Equator

/-! ### Complementary components of an embedded sphere -/

section Complement

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **The two complementary components of an embedded sphere.** For a continuous injection
`σ : S(E) → S(F)` with `finrank ℝ F = finrank ℝ E + 1` and a point `y ∉ range σ`, there is a
point `w ∉ range σ` in the opposite complementary component: the components of `y` and `w` in
`(range σ)ᶜ` are disjoint and cover `(range σ)ᶜ`. -/
theorem exists_connectedComponentIn_compl_range_sphere_eq_union
    (hEF : finrank ℝ F = finrank ℝ E + 1) (hc : Continuous σ) (hi : Injective σ)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ w ∉ range σ,
      Disjoint (connectedComponentIn (range σ)ᶜ y) (connectedComponentIn (range σ)ᶜ w) ∧
      (range σ)ᶜ = connectedComponentIn (range σ)ᶜ y ∪ connectedComponentIn (range σ)ᶜ w := by
  have hcard := natCard_connectedComponents_sphere_compl_range_eq_two hEF hc hi
  obtain ⟨c, hcne, hcall⟩ :=
    (Nat.card_eq_two_iff' ((⟨y, hy⟩ : ↥(range σ)ᶜ) : ConnectedComponents ↥(range σ)ᶜ)).1 hcard
  obtain ⟨⟨w, hw⟩, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨w, hw, disjoint_left.2 fun z hzy hzw ↦ hcne ?_, ?_⟩
  · rw [ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq]
    exact (connectedComponentIn_eq hzw).trans (connectedComponentIn_eq hzy).symm
  · refine Subset.antisymm (fun z hz ↦ ?_)
      (union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _))
    by_cases hzy :
        ((⟨z, hz⟩ : ↥(range σ)ᶜ) : ConnectedComponents ↥(range σ)ᶜ) =
          ((⟨y, hy⟩ : ↥(range σ)ᶜ) : ConnectedComponents ↥(range σ)ᶜ)
    · rw [ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq] at hzy
      exact Or.inl (hzy ▸ mem_connectedComponentIn hz)
    · have hzw := hcall _ hzy
      rw [ConnectedComponents.coe_eq_coe_iff_connectedComponentIn_eq] at hzw
      exact Or.inr (hzw ▸ mem_connectedComponentIn hz)

/-- When `finrank ℝ E = 0` and `finrank ℝ F = 1`, `S(E)` is empty and `S(F)` is finite discrete, so
`range σ = ∅` and every complementary component in `S(F)` is a singleton `{y}`. -/
private lemma connectedComponentIn_compl_range_of_finrank_eq_zero
    (hEF : finrank ℝ F = finrank ℝ E + 1) (h0 : finrank ℝ E = 0) (hi : Injective σ)
    (y : sphere (0 : F) 1) :
    range σ = ∅ ∧ connectedComponentIn (range σ)ᶜ y = {y} := by
  have : FiniteDimensional ℝ E := finiteDimensional_of_injective_sphere hEF hi
  have : Subsingleton E := finrank_zero_iff.1 h0
  have : IsEmpty (sphere (0 : E) 1) :=
    isEmpty_coe_sort.2 (sphere_eq_empty_of_subsingleton one_ne_zero)
  have hrange : range σ = ∅ := range_eq_empty σ
  have : Finite (sphere (0 : F) 1) := finite_sphere_of_finrank_eq_one (by omega) 0 1
  have : DiscreteTopology (sphere (0 : F) 1) := Finite.instDiscreteTopology
  refine ⟨hrange, ?_⟩
  rw [hrange, compl_empty, connectedComponentIn_univ]
  exact connectedComponent_eq_singleton y

/-- Degenerate `finrank ℝ E = 0` case of the generalized Schoenflies theorem: `{y}` and
`closedBall (0 : E) 1 = {0}` are both singletons. -/
private lemma exists_homeomorph_closure_of_finrank_eq_zero
    (hEF : finrank ℝ F = finrank ℝ E + 1) (h0 : finrank ℝ E = 0) (hi : Injective σ)
    (y : sphere (0 : F) 1) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  obtain ⟨hrange, hcomp⟩ := connectedComponentIn_compl_range_of_finrank_eq_zero hEF h0 hi y
  have : FiniteDimensional ℝ E := finiteDimensional_of_injective_sphere hEF hi
  have : Subsingleton E := finrank_zero_iff.1 h0
  have hE_emp : sphere (0 : E) 1 = ∅ := sphere_eq_empty_of_subsingleton one_ne_zero
  have : IsEmpty (sphere (0 : E) 1) := isEmpty_coe_sort.2 hE_emp
  have : Unique (closure (connectedComponentIn (range σ)ᶜ y)) :=
    ⟨⟨y, subset_closure (hcomp ▸ rfl)⟩, fun ⟨z, hz⟩ ↦ Subtype.ext <| by simpa [hcomp] using hz⟩
  have : Unique (closedBall (0 : E) 1) :=
    ⟨⟨0, mem_closedBall_self zero_le_one⟩, fun z ↦ Subtype.ext (Subsingleton.elim _ _)⟩
  exact ⟨Homeomorph.homeomorphOfUnique _ _, fun _ x ↦ isEmptyElim x,
    fun _ ↦ by simp [hE_emp, hrange]⟩

end Complement

/-! ### Unified bicollared Schoenflies theorem in all dimensions -/

namespace IsBicollar

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {σ : sphere (0 : E) 1 → sphere (0 : F) 1} {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}

/-- **The closure of a complementary domain of a bicollared sphere (`m ≥ 0`).** Whenever
`finrank ℝ F = finrank ℝ E + 1`, the closure of each connected component of `(range σ)ᶜ` is that
component together with `range σ`. -/
theorem closure_connectedComponentIn_compl_range_of_finrank_eq (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · obtain ⟨hrange, hcomp⟩ :=
      connectedComponentIn_compl_range_of_finrank_eq_zero hEF h0 hb.injective y
    rw [hcomp, hrange, closure_singleton, union_empty]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | hgt
    · exact closure_connectedComponentIn_compl_range_of_finrank_eq_one hEF h1.symm hb.injective hy
    · exact hb.closure_connectedComponentIn_compl_range hEF hgt hy

/-- **The frontier of a complementary domain of a bicollared sphere (`m ≥ 0`).** Whenever
`finrank ℝ F = finrank ℝ E + 1`, each connected component of `(range σ)ᶜ` has frontier `range σ`. -/
theorem frontier_connectedComponentIn_compl_range_of_finrank_eq (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · obtain ⟨hrange, hcomp⟩ :=
      connectedComponentIn_compl_range_of_finrank_eq_zero hEF h0 hb.injective y
    have : Finite (sphere (0 : F) 1) := finite_sphere_of_finrank_eq_one (by omega) 0 1
    have : DiscreteTopology (sphere (0 : F) 1) := Finite.instDiscreteTopology
    rw [hcomp, hrange, IsClopen.frontier_eq ⟨isClosed_discrete _, isOpen_discrete _⟩]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | hgt
    · exact frontier_connectedComponentIn_compl_range_of_finrank_eq_one hEF h1.symm hb.injective hy
    · exact hb.frontier_connectedComponentIn_compl_range hEF hgt hy

/-- **Brown's generalized Schoenflies theorem in all dimensions (`m ≥ 0`) and arbitrary real normed
spaces.** Let `σ : S(E) → S(F)` admit a bicollar `b`, where `finrank ℝ F = finrank ℝ E + 1`. Then
for every `y ∉ range σ`, the closure of the connected component of `y` in `(range σ)ᶜ` is
homeomorphic to `closedBall (0 : E) 1` by a homeomorphism inverting `σ` on `range σ` and sending
`range σ` onto `sphere (0 : E) 1`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ := by
  rcases Nat.eq_zero_or_pos (finrank ℝ E) with h0 | hpos
  · exact exists_homeomorph_closure_of_finrank_eq_zero hEF h0 hb.injective y
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | hgt
    · exact exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq_one
        hEF h1.symm hb.injective hy
    · -- Transport `S(F)` to a Euclidean sphere so `InnerProductSpace` is available for `m ≥ 2`.
      have : FiniteDimensional ℝ F := .of_finrank_pos (by omega)
      let G := EuclideanSpace ℝ (Fin (finrank ℝ E + 1))
      let Φ : sphere (0 : F) 1 ≃ₜ sphere (0 : G) 1 :=
        sphereHomeomorphOfFinrankEq (by simp [G, hEF])
      have hyΦ : Φ y ∉ range (Φ ∘ σ) := by
        rw [range_comp, Φ.injective.mem_set_image]
        exact hy
      have hbΦ := hb.isOpenEmbedding_comp Φ.isOpenEmbedding
      obtain ⟨hG, hhG_inv, hhG_sph⟩ :=
        hbΦ.exists_homeomorph_closure_connectedComponentIn_compl_range (by simp [G]) hgt hyΦ
      have hclΦ : closure (connectedComponentIn (range (Φ ∘ σ))ᶜ (Φ y)) =
          Φ '' closure (connectedComponentIn (range σ)ᶜ y) := by
        rw [range_comp, ← image_compl_eq Φ.bijective, ← Φ.image_connectedComponentIn hy,
          Φ.image_closure]
      let Ψ : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ
          closure (connectedComponentIn (range (Φ ∘ σ))ᶜ (Φ y)) :=
        Φ.subtype fun z ↦ (hclΦ ▸ Φ.injective.mem_set_image).symm
      refine ⟨Ψ.trans hG, fun z x hzx ↦ hhG_inv (Ψ z) x (by simp [Ψ, hzx]), fun z ↦ ?_⟩
      exact (hhG_sph (Ψ z)).trans <| by
        rw [Homeomorph.subtype_apply_coe, range_comp]
        exact Φ.injective.mem_set_image

/-- **Closed-ball extension form of Brown's generalized Schoenflies theorem (`m ≥ 0`).** For each
complementary point `y ∉ range σ`, `σ` extends to a closed embedding
`g : closedBall (0 : E) 1 → S(F)` whose image is `closure (connectedComponentIn (range σ)ᶜ y)` and
which carries `ball (0 : E) 1` onto `connectedComponentIn (range σ)ᶜ y`. -/
theorem exists_isClosedEmbedding_closedBall (hb : IsBicollar σ b)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ g : closedBall (0 : E) 1 → sphere (0 : F) 1, IsClosedEmbedding g ∧
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = σ x) ∧
      range g = closure (connectedComponentIn (range σ)ᶜ y) ∧
      (∀ z : closedBall (0 : E) 1,
        (z : E) ∈ ball (0 : E) 1 ↔ g z ∈ connectedComponentIn (range σ)ᶜ y) := by
  obtain ⟨h, hh_inv, hh_sph⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy
  have hcl := hb.closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy
  let g : closedBall (0 : E) 1 → sphere (0 : F) 1 := Subtype.val ∘ h.symm
  refine ⟨g, isClosed_closure.isClosedEmbedding_subtypeVal.comp h.symm.isClosedEmbedding,
    fun x ↦ ?_, by simp [g], fun z ↦ ?_⟩
  · have hxmem : σ x ∈ closure (connectedComponentIn (range σ)ᶜ y) :=
      hcl ▸ Or.inr (mem_range_self x)
    have hxeq : h ⟨σ x, hxmem⟩ = ⟨x, sphere_subset_closedBall x.2⟩ :=
      Subtype.ext (hh_inv ⟨σ x, hxmem⟩ x rfl)
    simpa [g] using congrArg (Subtype.val ∘ h.symm) hxeq.symm
  · have hz_norm : (z : E) ∈ ball (0 : E) 1 ↔ (z : E) ∉ sphere (0 : E) 1 := by
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm]
      exact (mem_closedBall_zero_iff.1 z.2).lt_iff_ne
    have hdisj : Disjoint (connectedComponentIn (range σ)ᶜ y) (range σ) :=
      subset_compl_iff_disjoint_right.1 (connectedComponentIn_subset _ _)
    rw [hz_norm, ← not_iff_not, not_not]
    have hmem : g z ∈ connectedComponentIn (range σ)ᶜ y ∪ range σ := hcl ▸ (h.symm z).2
    have hiff := hh_sph (h.symm z)
    rw [h.apply_symm_apply] at hiff
    rw [hiff]
    exact ⟨fun hr ↦ hdisj.notMem_of_mem_right hr, fun hn ↦ hmem.resolve_left hn⟩

/-- **Ambient equatorial straightening in all dimensions (`m ≥ 0`).** In a real inner product space
`F` with `finrank ℝ F = finrank ℝ E + 1`, for any pole `p : sphere (0 : F) 1`, any homeomorphism
`e : S(E) ≃ₜ S((ℝ ∙ p)ᗮ)`, and any chosen exterior point `y ∉ range σ`, there is an ambient
homeomorphism `h : S(F) ≃ₜ S(F)` straightening `σ` to `equatorInclusion (p : F) ∘ e` and carrying
`closure (connectedComponentIn (range σ)ᶜ y)` onto the closed hemisphere `{z | 0 ≤ ⟪z, p⟫}` (and
the opposite complementary closure onto `{z | ⟪z, p⟫ ≤ 0}`). -/
theorem exists_homeomorph_sphere_eq_equatorInclusion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {σ : sphere (0 : E) 1 → sphere (0 : F) 1} {b : sphere (0 : E) 1 × ℝ → sphere (0 : F) 1}
    (hb : IsBicollar σ b) (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ z, 0 ≤ ⟪(h z : F), (p : F)⟫ ↔
        z ∈ closure (connectedComponentIn (range σ)ᶜ y)) ∧
      (∀ z, ⟪(h z : F), (p : F)⟫ < 0 ↔
        z ∉ closure (connectedComponentIn (range σ)ᶜ y)) := by
  obtain ⟨w, hw, hUV, hcompl⟩ :=
    exists_connectedComponentIn_compl_range_sphere_eq_union hEF hb.continuous hb.injective hy
  let U := connectedComponentIn (range σ)ᶜ y
  let V := connectedComponentIn (range σ)ᶜ w
  let A := closure U
  let C := closure V
  have hA : A = U ∪ range σ := hb.closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy
  have hC : C = V ∪ range σ := hb.closure_connectedComponentIn_compl_range_of_finrank_eq hEF hw
  have hAC : A ∪ C = univ := by
    rw [hA, hC, ← union_union_distrib_right, ← hcompl, compl_union_self]
  have hinter : A ∩ C = range σ := by
    rw [hA, hC, ← inter_union_distrib_right, hUV.inter_eq, empty_union]
  let B : closedBall (0 : E) 1 ≃ₜ closedBall (0 : (ℝ ∙ (p : F))ᗮ) 1 :=
    e.radialExtension.subtype fun z ↦ by simp
  have hB (z : closedBall (0 : E) 1) : ‖(B z : (ℝ ∙ (p : F))ᗮ)‖ = 1 ↔ ‖(z : E)‖ = 1 := by
    simp [B]
  obtain ⟨eA, heA, hnA⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy
  obtain ⟨eC, -, hnC⟩ :=
    hb.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq hEF hw
  obtain ⟨h, hhA, hhpos, -⟩ := exists_homeomorph_sphere_of_union_closedBall_orthogonal p
    isClosed_closure isClosed_closure hAC (eA.trans B) (eC.trans B)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnA]
      simpa only [mem_inter_iff, A, C, z.2, true_and] using Set.ext_iff.1 hinter z)
    (fun z ↦ by
      rw [Homeomorph.trans_apply, hB, ← mem_sphere_zero_iff_norm, hnC]
      simpa only [mem_inter_iff, A, C, z.2, and_true] using Set.ext_iff.1 hinter z)
  refine ⟨h, fun x ↦ ?_, hhpos, fun z ↦ not_le.symm.trans (hhpos z).not⟩
  have hxA : σ x ∈ A := hA ▸ Or.inr (mem_range_self x)
  rw [hhA ⟨σ x, hxA⟩]
  have he : (B (eA ⟨σ x, hxA⟩) : (ℝ ∙ (p : F))ᗮ) = e x := by
    simpa only [B, Homeomorph.subtype_apply_coe, heA ⟨σ x, hxA⟩ x rfl] using
      e.radialExtension_coe_sphere x
  apply Subtype.ext
  simp [Homeomorph.trans_apply, coe_hemisphereHomeomorph_symm_apply,
    coe_equatorInclusion_apply, he, norm_eq_of_mem_sphere]

end IsBicollar

/-! ### The locally flat generalized Schoenflies theorem -/

namespace IsLocallyFlat

variable {H E F : Type*} [TopologicalSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {σ : sphere (0 : E) 1 → sphere (0 : F) 1}

/-- **The closure of a complementary domain of a locally flat sphere (`m ≥ 0`).** -/
theorem closure_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    closure (connectedComponentIn (range σ)ᶜ y) = connectedComponentIn (range σ)ᶜ y ∪ range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy

/-- **The frontier of a complementary domain of a locally flat sphere (`m ≥ 0`).** -/
theorem frontier_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    frontier (connectedComponentIn (range σ)ᶜ y) = range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.frontier_connectedComponentIn_compl_range_of_finrank_eq hEF hy

/-- **The locally flat generalized Schoenflies theorem (`m ≥ 0`).** Every codimension-one locally
flat sphere `σ : S(E) → S(F)` (`finrank ℝ F = finrank ℝ E + 1`) bounds a closed `m`-ball on each
side: for every `y ∉ range σ`, `closure (connectedComponentIn (range σ)ᶜ y)` is homeomorphic to
`closedBall (0 : E) 1` by a homeomorphism inverting `σ` on `range σ` and sending `range σ` onto
`sphere (0 : E) 1`. -/
theorem exists_homeomorph_closure_connectedComponentIn_compl_range (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : closure (connectedComponentIn (range σ)ᶜ y) ≃ₜ closedBall (0 : E) 1,
      (∀ (z : closure (connectedComponentIn (range σ)ᶜ y)) x,
        (z : sphere (0 : F) 1) = σ x → (h z : E) = x) ∧
      ∀ z, (h z : E) ∈ sphere (0 : E) 1 ↔ (z : sphere (0 : F) 1) ∈ range σ :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_homeomorph_closure_connectedComponentIn_compl_range_of_finrank_eq hEF hy

/-- **Closed-ball extension form of the locally flat generalized Schoenflies theorem (`m ≥ 0`).**
For every `y ∉ range σ`, `σ` extends to a closed embedding `g : closedBall (0 : E) 1 → S(F)` with
range `closure (connectedComponentIn (range σ)ᶜ y)` carrying `ball (0 : E) 1` onto
`connectedComponentIn (range σ)ᶜ y`. -/
theorem exists_isClosedEmbedding_closedBall (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1) {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ g : closedBall (0 : E) 1 → sphere (0 : F) 1, IsClosedEmbedding g ∧
      (∀ x : sphere (0 : E) 1, g ⟨x, sphere_subset_closedBall x.2⟩ = σ x) ∧
      range g = closure (connectedComponentIn (range σ)ᶜ y) ∧
      (∀ z : closedBall (0 : E) 1,
        (z : E) ∈ ball (0 : E) 1 ↔ g z ∈ connectedComponentIn (range σ)ᶜ y) :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_isClosedEmbedding_closedBall hEF hy

/-- **Ambient equatorial straightening for locally flat spheres (`m ≥ 0`).** In a real inner
product space `F` with `finrank ℝ F = finrank ℝ E + 1`, every locally flat sphere
`σ : S(E) → S(F)` is carried to the equator `equatorInclusion (p : F) ∘ e` by an ambient
self-homeomorphism of `S(F)` sending `closure (connectedComponentIn (range σ)ᶜ y)` onto the closed
hemisphere `{z | 0 ≤ ⟪z, p⟫}`. -/
theorem exists_homeomorph_sphere_eq_equatorInclusion
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {σ : sphere (0 : E) 1 → sphere (0 : F) 1} (hf : IsLocallyFlat H ℝ σ)
    (hEF : finrank ℝ F = finrank ℝ E + 1)
    (p : sphere (0 : F) 1) (e : sphere (0 : E) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : F))ᗮ) 1)
    {y : sphere (0 : F) 1} (hy : y ∉ range σ) :
    ∃ h : sphere (0 : F) 1 ≃ₜ sphere (0 : F) 1,
      (∀ x, h (σ x) = equatorInclusion (p : F) (e x)) ∧
      (∀ z, 0 ≤ ⟪(h z : F), (p : F)⟫ ↔
        z ∈ closure (connectedComponentIn (range σ)ᶜ y)) ∧
      (∀ z, ⟪(h z : F), (p : F)⟫ < 0 ↔
        z ∉ closure (connectedComponentIn (range σ)ᶜ y)) :=
  let ⟨_, hb⟩ := isBicollared_iff.1 (hf.isBicollared_of_finrank_eq hEF)
  hb.exists_homeomorph_sphere_eq_equatorInclusion hEF p e hy

end IsLocallyFlat

end TauCeti
