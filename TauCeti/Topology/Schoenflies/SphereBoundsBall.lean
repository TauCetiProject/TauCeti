/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Irreducible
public import TauCeti.Topology.Schoenflies.NormedSpace
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.AlgebraicTopology.Disk
import TauCeti.AlgebraicTopology.Singular.InvarianceOfDomain
import TauCeti.AlgebraicTopology.Sphere.Contractible
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# Alexander's theorem and 3-manifold irreducibility instances

Every closed locally flat 2-sphere in the 3-sphere `S³` separates `S³` into two connected
components and bounds an embedded closed 3-ball on **each** side; in particular `S³` satisfies the
tame irreducibility predicate `TauCeti.IsSphereBoundsBall`. Likewise, every closed locally flat
2-sphere in a 3-dimensional real normed space `E` bounds its filled hull as an embedded closed
3-ball.

More generally, a local bicollar of `TopCat.sphere n` into a real normed space `E` or into the unit
sphere `S(F)` of a real normed space `F` already forces `E` (resp. `F`) to be finite-dimensional of
dimension `n + 1` (resp. `n + 2`), by Riesz's compact-ball theorem and Brouwer's invariance of
dimension (`Topology.IsOpenEmbedding.finrank_eq`). Consequently the closed-disk extension theorems
and `TauCeti.IsSphereBoundsBall` hold without any auxiliary dimension hypotheses on `E` or `F`: for
`finrank ℝ F = 4` (`S(F) ≅ S³`, non-vacuously witnessed by `TauCeti.isLocallyFlat_equatorInclusion`)
this is **Alexander's theorem**, while for `finrank ℝ F ≠ 4` no locally flat `(ℝ², ℝ)`-embedding of
`S²` into `S(F)` exists.

Historically, J. W. Alexander proved the piecewise-linear 3-sphere theorem in 1924, while his
horned sphere showed that local flatness cannot be dropped in the topological category; M. Brown's
bicollaring and generalized Schoenflies theorems yield the locally flat topological form in every
dimension.

As a contrasting reducibility witness, a product `X × S²` of any nonempty 1-manifold `X` (such as
`Circle × S²` or `ℝ × S²`) does **not** satisfy `TauCeti.IsSphereBoundsBall`: a fiber `{x₀} × S²`
is a closed locally flat 2-sphere whose extension across `𝔻³` would contract `S²` via second-factor
projection.

## Main results

* `TauCeti.IsLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere` and
  `TauCeti.IsLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere_sphere`: a locally
  bicollared `n`-sphere in `E` (resp. `S(F)`) forces `FiniteDimensional ℝ E ∧ finrank ℝ E = n + 1`
  (resp. `FiniteDimensional ℝ F ∧ finrank ℝ F = n + 2`).
* `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_disk_sphere`: a locally flat `n`-sphere
  `TopCat.sphere n → S(F)` extends across `TopCat.disk (n + 1)` to a closed embedding onto the
  closure of either complementary component.
* `TauCeti.isSphereBoundsBall_sphere` and `TauCeti.isSphereBoundsBall_topCatSphere`:
  **Alexander's theorem** — `S(F)` (in particular `S³`) and `TopCat.sphere n` (in particular
  `TopCat.sphere 3`) satisfy `TauCeti.IsSphereBoundsBall`.
* `TauCeti.IsLocallyFlat.exists_isClosedEmbedding_disk_filledHull` and
  `TauCeti.isSphereBoundsBall_normedSpace`: closed-disk filling of `filledHull` and
  `TauCeti.IsSphereBoundsBall` for real normed spaces (in particular `ℝ³`).
* `TauCeti.isBicollared_prodMkRight_of_finrank_eq_one`,
  `TauCeti.not_isSphereBoundsBall_prod_sphere`,
  `TauCeti.not_isSphereBoundsBall_circle_prod_sphere`, and
  `TauCeti.not_isSphereBoundsBall_real_prod_sphere`: `X × S²` fails `TauCeti.IsSphereBoundsBall`
  for every nonempty 1-manifold `X` (in particular `S¹ × S²` and `ℝ × S²`).

## References

* J. W. Alexander, *On the subdivision of 3-space by a polyhedron*, Proc. Nat. Acad. Sci. U.S.A.
  10 (1924), 6–8.
* M. Brown, *A proof of the generalized Schoenflies theorem*, Bull. Amer. Math. Soc. 66 (1960),
  74–76.
* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* A. Hatcher, *Notes on Basic 3-Manifold Topology*, Theorem 1.1.
-/

public section

open CategoryTheory Filter Function Metric Module Set Topology

namespace TauCeti

universe u v

/-! ### Dimension forcing from local bicollars -/

/-- An open embedding from a finite-dimensional real normed space `G` into a real normed space `E`
forces `E` to be finite-dimensional of the same `finrank` as `G`. -/
private lemma finiteDimensional_and_finrank_eq_of_isOpenEmbedding {G E : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : G → E} (hψ : IsOpenEmbedding ψ) :
    FiniteDimensional ℝ E ∧ finrank ℝ E = finrank ℝ G := by
  have hK : IsCompact (ψ '' closedBall 0 1) := (isCompact_closedBall 0 1).image hψ.continuous
  have hnhds : ψ '' closedBall 0 1 ∈ 𝓝 (ψ 0) :=
    Filter.mem_of_superset
      ((hψ.isOpenMap _ isOpen_ball).mem_nhds ⟨0, mem_ball_self one_pos, rfl⟩)
      (image_mono ball_subset_closedBall)
  obtain ⟨r, hr₀, hrK⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hnhds
  have : FiniteDimensional ℝ E :=
    .of_isCompact_closedBall ℝ hr₀ (hK.of_isClosed_subset isClosed_closedBall hrK)
  exact ⟨‹_›, hψ.finrank_eq IsOpenEmbedding.id⟩

/-- Around any point `x₀` of an open set `U` in a manifold `M` charted on a real normed space `H`,
reparametrizing an open chart ball by `OpenPartialHomeomorph.univBall` gives an open embedding
`H → U` sending `0` to `x₀`. -/
private lemma exists_isOpenEmbedding_of_isOpen_mem {M H : Type*} [TopologicalSpace M]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ChartedSpace H M]
    {U : Set M} (hU : IsOpen U) {x₀ : M} (hx₀ : x₀ ∈ U) :
    ∃ κ : H → U, IsOpenEmbedding κ ∧ (κ 0 : M) = x₀ := by
  let φ := chartAt H x₀
  have hxφ : x₀ ∈ φ.source := mem_chart_source H x₀
  have hV : IsOpen (φ.target ∩ φ.symm ⁻¹' U) :=
    φ.continuousOn_symm.isOpen_inter_preimage φ.open_target hU
  have hxV : φ x₀ ∈ φ.target ∩ φ.symm ⁻¹' U :=
    ⟨φ.map_source hxφ, by simpa [φ.left_inv hxφ] using hx₀⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV (φ x₀) hxV
  let ψH := OpenPartialHomeomorph.univBall (φ x₀) ε
  have hψ_mem (v : H) : ψH v ∈ φ.target ∩ φ.symm ⁻¹' U :=
    hball (OpenPartialHomeomorph.univBall_target (φ x₀) hε ▸ ψH.map_source (by simp [ψH]))
  let g : H → φ.symm.source := fun v ↦ ⟨ψH v, φ.symm_source ▸ (hψ_mem v).1⟩
  have hg : IsOpenEmbedding g :=
    (φ.symm.open_source.isOpenEmbedding_subtypeVal.of_comp_iff g).1
      (ψH.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _))
  let κM : H → M := φ.symm.source.domRestrict φ.symm ∘ g
  have hκM : IsOpenEmbedding κM := φ.symm.isOpenEmbedding_restrict.comp hg
  let κ : H → U := fun v ↦ ⟨κM v, (hψ_mem v).2⟩
  refine ⟨κ, (hU.isOpenEmbedding_subtypeVal.of_comp_iff κ).1 hκM, ?_⟩
  change φ.symm (ψH 0) = x₀
  rw [OpenPartialHomeomorph.univBall_apply_zero, φ.left_inv hxφ]

/-- Any locally bicollared map out of `TopCat.sphere n` yields an open embedding of
`EuclideanSpace ℝ (Fin n) × ℝ` into the target. -/
private lemma exists_isOpenEmbedding_prod_of_topCatSphere {Y : Type v} [TopologicalSpace Y]
    {n : ℕ} {f : TopCat.sphere.{u} n → Y} (hf : IsLocallyBicollared f) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) × ℝ → Y, IsOpenEmbedding ψ := by
  let V := EuclideanSpace ℝ (Fin (n + 1))
  have : Fact (finrank ℝ V = n + 1) := ⟨by simp [V]⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp [V])
  obtain ⟨x₀⟩ : Nonempty (sphere (0 : V) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  let eS : TopCat.sphere.{u} n ≃ₜ sphere (0 : V) 1 := Homeomorph.ulift
  obtain ⟨U, hU, hx₀, hbic⟩ := isLocallyBicollared_iff.1 (hf.comp_homeomorph eS.symm) x₀
  obtain ⟨b, hb⟩ := isBicollared_iff.1 hbic
  obtain ⟨κ, hκ, -⟩ :=
    exists_isOpenEmbedding_of_isOpen_mem (H := EuclideanSpace ℝ (Fin n)) hU hx₀
  exact ⟨b ∘ Prod.map κ id, hb.isOpenEmbedding.comp (hκ.prodMap IsOpenEmbedding.id)⟩

/-- **A locally bicollared `n`-sphere in a real normed space `E` forces `dim E = n + 1`.** -/
theorem IsLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {f : TopCat.sphere.{u} n → E} (hf : IsLocallyBicollared f) :
    FiniteDimensional ℝ E ∧ finrank ℝ E = n + 1 := by
  obtain ⟨ψ, hψ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere hf
  obtain ⟨hfd, hdim⟩ := finiteDimensional_and_finrank_eq_of_isOpenEmbedding hψ
  exact ⟨hfd, hdim.trans (by simp [Module.finrank_prod])⟩

/-- **A locally bicollared `n`-sphere in `S(F)` forces `dim F = n + 2`.** -/
theorem IsLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere_sphere
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ}
    {f : TopCat.sphere.{u} n → sphere (0 : F) 1} (hf : IsLocallyBicollared f) :
    FiniteDimensional ℝ F ∧ finrank ℝ F = n + 2 := by
  obtain ⟨ψ, hψ⟩ := exists_isOpenEmbedding_prod_of_topCatSphere hf
  let ρ₀ := OpenPartialHomeomorph.univBall (1 : ℝ) (1 / 2)
  have hρ_pos (t : ℝ) : 0 < ρ₀ t := by
    have ht : dist (ρ₀ t) 1 < 1 / 2 := mem_ball.1 <|
      OpenPartialHomeomorph.univBall_target (1 : ℝ) (by positivity : (0 : ℝ) < 1 / 2) ▸
        ρ₀.map_source (by simp [ρ₀])
    linarith [(abs_lt.1 (Real.dist_eq (ρ₀ t) 1 ▸ ht)).1]
  let ρ : ℝ → Ioi (0 : ℝ) := fun t ↦ ⟨ρ₀ t, hρ_pos t⟩
  have hρ : IsOpenEmbedding ρ :=
    (isOpen_Ioi.isOpenEmbedding_subtypeVal.of_comp_iff ρ).1
      (ρ₀.isOpenEmbedding (OpenPartialHomeomorph.univBall_source _ _))
  let Φ : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ → F :=
    Subtype.val ∘ (homeomorphUnitSphereProd F).symm ∘ Prod.map ψ ρ
  have hΦ : IsOpenEmbedding Φ :=
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp <|
      (homeomorphUnitSphereProd F).symm.isOpenEmbedding.comp (hψ.prodMap hρ)
  obtain ⟨hfd, hdim⟩ := finiteDimensional_and_finrank_eq_of_isOpenEmbedding hΦ
  exact ⟨hfd, hdim.trans (by simp [Module.finrank_prod])⟩

/-! ### Disk extensions and Alexander's theorem on `S³` -/

/-- **Two-sided closed-disk extension for locally flat spheres in `S(F)`.** Let `F` be a real
normed space and let `f : C((TopCat.sphere n : TopCat.{u}), sphere (0 : F) 1)` be locally flat. For
every exterior point `y ∉ range f`, `f` extends across `TopCat.disk (n + 1)` to a closed embedding
whose image is `closure (connectedComponentIn (range f)ᶜ y)`. -/
theorem IsLocallyFlat.exists_isClosedEmbedding_disk_sphere
    {F : Type v} {H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    {n : ℕ} {f : C((TopCat.sphere n : TopCat.{u}), sphere (0 : F) 1)} (hf : IsLocallyFlat H ℝ f)
    {y : sphere (0 : F) 1} (hy : y ∉ range f) :
    ∃ g : C((TopCat.disk (n + 1) : TopCat.{u}), sphere (0 : F) 1),
      IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion (n + 1)).hom = f ∧
      range g = closure (connectedComponentIn (range f)ᶜ y) := by
  obtain ⟨_, hF⟩ := hf.isLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere_sphere
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let eS : (TopCat.sphere n : TopCat.{u}) ≃ₜ sphere (0 : E) 1 := Homeomorph.ulift
  let eD : (TopCat.disk (n + 1) : TopCat.{u}) ≃ₜ closedBall (0 : E) 1 := Homeomorph.ulift
  let σ : sphere (0 : E) 1 → sphere (0 : F) 1 := f ∘ eS.symm
  have hrange : range σ = range f := eS.symm.surjective.range_comp f
  have hfσ : IsLocallyFlat H ℝ σ := hf.comp_homeomorph eS.symm
  obtain ⟨g₀, hg₀_emb, hg₀_bdry, hg₀_range, -⟩ :=
    hfσ.exists_isClosedEmbedding_closedBall (by simp [E, hF]) (hrange.symm ▸ hy)
  refine ⟨⟨g₀ ∘ eD, hg₀_emb.continuous.comp eD.continuous⟩,
    hg₀_emb.comp eD.isClosedEmbedding, ContinuousMap.ext fun s ↦ ?_, ?_⟩
  · change g₀ (eD ((TopCat.diskBoundaryInclusion (n + 1)).hom s)) = f s
    have hs : eD ((TopCat.diskBoundaryInclusion (n + 1)).hom s) =
        ⟨(eS s : E), sphere_subset_closedBall (eS s).2⟩ := Subtype.ext rfl
    rw [hs, hg₀_bdry (eS s)]
    exact congrArg f (eS.symm_apply_apply s)
  · change range (g₀ ∘ eD) = closure (connectedComponentIn (range f)ᶜ y)
    rw [eD.surjective.range_comp, hg₀_range, hrange]

/-- **Alexander's theorem:** for any real normed space `F`, the unit sphere `sphere (0 : F) 1`
satisfies `TauCeti.IsSphereBoundsBall`. When `finrank ℝ F = 4` (`S(F) ≅ S³`, witnessed
non-vacuously by `TauCeti.isLocallyFlat_equatorInclusion`), every closed locally flat embedded
2-sphere bounds an embedded 3-ball on each side; when `finrank ℝ F ≠ 4`, no locally flat
`(ℝ², ℝ)`-embedding of `S²` into `S(F)` exists. -/
theorem isSphereBoundsBall_sphere (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    IsSphereBoundsBall (sphere (0 : F) 1) := by
  rw [isSphereBoundsBall_iff]
  intro f hf_emb hf_flat
  obtain ⟨_, hF⟩ :=
    hf_flat.isLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere_sphere
  have hne : (range f)ᶜ.Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    let eS : (TopCat.sphere 2 : TopCat.{u}) ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      Homeomorph.ulift
    let σ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → sphere (0 : F) 1 := f ∘ eS.symm
    have hcard := natCard_connectedComponents_sphere_compl_range_eq_two
      (E := EuclideanSpace ℝ (Fin 3)) (by simp [hF])
      (f.continuous.comp eS.symm.continuous) (hf_emb.injective.comp eS.symm.injective)
    have hσ_empty : (range σ)ᶜ = ∅ := by
      rwa [show σ = f ∘ eS.symm from rfl, eS.symm.surjective.range_comp]
    have : IsEmpty ↥(range σ)ᶜ := isEmpty_coe_sort.2 hσ_empty
    have : IsEmpty (ConnectedComponents ↥(range σ)ᶜ) :=
      ⟨fun c ↦ let ⟨x, _⟩ := ConnectedComponents.surjective_coe c; isEmptyElim x⟩
    simp at hcard
  obtain ⟨y, hy⟩ := hne
  obtain ⟨g, hg_emb, hg_bdry, -⟩ := hf_flat.exists_isClosedEmbedding_disk_sphere hy
  exact ⟨g, hg_emb, hg_bdry⟩

/-- **Alexander's theorem (`TopCat.sphere` form):** Mathlib's universe-polymorphic `n`-sphere
`TopCat.sphere n` (in particular the 3-sphere `TopCat.sphere 3`) satisfies
`TauCeti.IsSphereBoundsBall`. -/
theorem isSphereBoundsBall_topCatSphere (n : ℕ) :
    IsSphereBoundsBall (TopCat.sphere.{u} n) :=
  Homeomorph.ulift.symm.isSphereBoundsBall (isSphereBoundsBall_sphere _)

/-! ### Disk extensions and irreducibility of real normed spaces -/

/-- **Closed-disk extension in real normed spaces.** Every locally flat `n`-sphere
`f : C((TopCat.sphere n : TopCat.{u}), E)` in a real normed space `E` extends across
`TopCat.disk (n + 1)` to a closed embedding whose image is `filledHull (range f)`. -/
theorem IsLocallyFlat.exists_isClosedEmbedding_disk_filledHull
    {E : Type v} {H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {n : ℕ} {f : C((TopCat.sphere n : TopCat.{u}), E)} (hf : IsLocallyFlat H ℝ f) :
    ∃ g : C((TopCat.disk (n + 1) : TopCat.{u}), E),
      IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion (n + 1)).hom = f ∧
      range g = filledHull (range f) := by
  obtain ⟨hfd, hE⟩ := hf.isLocallyBicollared.finiteDimensional_and_finrank_eq_of_topCatSphere
  let V := EuclideanSpace ℝ (Fin (n + 1))
  let L : V ≃L[ℝ] E :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq (by simp [V, hE])).some
  let eS : (TopCat.sphere n : TopCat.{u}) ≃ₜ sphere (0 : E) 1 :=
    Homeomorph.ulift.trans (L.unitBallHomeomorph.subtype fun x ↦ by simp)
  let eD : (TopCat.disk (n + 1) : TopCat.{u}) ≃ₜ closedBall (0 : E) 1 :=
    Homeomorph.ulift.trans (L.unitBallHomeomorph.subtype fun x ↦ by simp)
  let f₀ : sphere (0 : E) 1 → E := f ∘ eS.symm
  have hrange : range f₀ = range f := eS.symm.surjective.range_comp f
  have hf₀ : IsLocallyFlat H ℝ f₀ := hf.comp_homeomorph eS.symm
  obtain ⟨g₀, hg₀_emb, hg₀_bdry, hg₀_range, -⟩ :=
    hf₀.exists_isClosedEmbedding_closedBall_filledHull
  refine ⟨⟨g₀ ∘ eD, hg₀_emb.continuous.comp eD.continuous⟩,
    hg₀_emb.comp eD.isClosedEmbedding, ContinuousMap.ext fun s ↦ ?_, ?_⟩
  · change g₀ (eD ((TopCat.diskBoundaryInclusion (n + 1)).hom s)) = f s
    have hs : eD ((TopCat.diskBoundaryInclusion (n + 1)).hom s) =
        ⟨(eS s : E), sphere_subset_closedBall (eS s).2⟩ := Subtype.ext rfl
    rw [hs, hg₀_bdry (eS s)]
    exact congrArg f (eS.symm_apply_apply s)
  · change range (g₀ ∘ eD) = filledHull (range f)
    rw [eD.surjective.range_comp, hg₀_range, hrange]

/-- **Every real normed space satisfies `TauCeti.IsSphereBoundsBall`.** When `finrank ℝ E = 3`
(`E ≅ ℝ³`), every closed locally flat embedded 2-sphere bounds `filledHull (range f)` as an embedded
3-ball; when `finrank ℝ E ≠ 3`, no locally flat `(ℝ², ℝ)`-embedding of `S²` into `E` exists. -/
theorem isSphereBoundsBall_normedSpace (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsSphereBoundsBall E := by
  rw [isSphereBoundsBall_iff]
  intro f _ hf_flat
  obtain ⟨g, hg_emb, hg_bdry, -⟩ := hf_flat.exists_isClosedEmbedding_disk_filledHull
  exact ⟨g, hg_emb, hg_bdry⟩

/-! ### Reducibility of `X × S²` (`S¹ × S²` and `ℝ × S²`) -/

/-- **A point fiber in a product with a 1-manifold is globally bicollared.** For any `x₀ : X` in a
topological space `X` charted on a one-dimensional real normed space `H` (`finrank ℝ H = 1`) and
any topological space `Y`, the fiber inclusion `Prod.mk x₀ : Y → X × Y` admits a global bicollar. -/
theorem isBicollared_prodMkRight_of_finrank_eq_one {X Y H : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ChartedSpace H X]
    (hH : finrank ℝ H = 1) (x₀ : X) :
    IsBicollared (Prod.mk x₀ : Y → X × Y) := by
  have : FiniteDimensional ℝ H := .of_finrank_pos (by omega)
  let L : ℝ ≃L[ℝ] H :=
    (FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
      ((Module.finrank_self ℝ).trans hH.symm)).some
  obtain ⟨κU, hκU, hκU0⟩ := exists_isOpenEmbedding_of_isOpen_mem (H := H) isOpen_univ (mem_univ x₀)
  let κ : ℝ → X := Subtype.val ∘ κU ∘ L
  have hκ : IsOpenEmbedding κ :=
    isOpen_univ.isOpenEmbedding_subtypeVal.comp (hκU.comp L.toHomeomorph.isOpenEmbedding)
  have hκ0 : κ 0 = x₀ := by simp [κ, hκU0]
  refine isBicollared_iff.2 ⟨fun q ↦ (κ q.2, q.1), ?_, fun y ↦ by simp [hκ0]⟩
  exact (Homeomorph.prodComm Y X).isOpenEmbedding.comp (IsOpenEmbedding.id.prodMap hκ)

/-- **Products of nonempty 1-manifolds with 2-spheres are reducible.** For any nonempty space `X`
charted on a 1-dimensional real normed space `H` and any 3-dimensional real normed space `E`,
`X × sphere (0 : E) 1` does not satisfy `TauCeti.IsSphereBoundsBall`: a fiber `{x₀} × S(E)` is a
closed locally flat 2-sphere that cannot bound a 3-ball because `S(E)` is not contractible. -/
theorem not_isSphereBoundsBall_prod_sphere {X E : Type u} {H : Type*}
    [TopologicalSpace X] [Nonempty X]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [ChartedSpace H X] (hH : finrank ℝ H = 1)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : finrank ℝ E = 3) :
    ¬ IsSphereBoundsBall (X × sphere (0 : E) 1) := by
  intro h
  have : T1Space X := ChartedSpace.t1Space H X
  have : FiniteDimensional ℝ E := .of_finrank_pos (by omega)
  have : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let x₀ : X := Classical.arbitrary X
  let S₀ := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
  let eE : S₀ ≃ₜ sphere (0 : E) 1 := sphereHomeomorphOfFinrankEq (by simp [hE])
  let eU : TopCat.diskBoundary.{u} 3 ≃ₜ S₀ := Homeomorph.ulift
  let f : C((TopCat.sphere 2 : TopCat.{u}), X × sphere (0 : E) 1) :=
    ⟨Prod.mk x₀ ∘ eE ∘ eU, by fun_prop⟩
  have hf_emb : IsClosedEmbedding f :=
    (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight x₀)
      (isClosedMap_prodMk_left x₀)).comp (eE.isClosedEmbedding.comp eU.isClosedEmbedding)
  have hf_flat : IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f := by
    have hb : IsBicollared (Prod.mk x₀ ∘ eE : S₀ → X × sphere (0 : E) 1) :=
      (isBicollared_prodMkRight_of_finrank_eq_one hH x₀).comp_homeomorph eE
    exact hb.isLocallyFlat.comp_homeomorph eU
  obtain ⟨g, -, hg_bdry⟩ := (isSphereBoundsBall_iff _).1 h f hf_emb hf_flat
  let r : C(X × sphere (0 : E) 1, TopCat.diskBoundary.{u} 3) :=
    ⟨eU.symm ∘ eE.symm ∘ Prod.snd, by fun_prop⟩
  have hext : TopCat.diskBoundaryInclusion 3 ≫ TopCat.ofHom (r.comp g) =
      𝟙 (TopCat.diskBoundary.{u} 3) := by
    ext s
    have hs : g ((TopCat.diskBoundaryInclusion 3).hom s) = f s :=
      ContinuousMap.congr_fun hg_bdry s
    change eU.symm (eE.symm (g ((TopCat.diskBoundaryInclusion 3).hom s)).2) = s
    rw [hs]
    exact (congrArg eU.symm (eE.symm_apply_apply (eU s))).trans (eU.symm_apply_apply s)
  have hnull : (ContinuousMap.id (TopCat.diskBoundary.{u} 3)).Nullhomotopic :=
    (TopCat.Hom.nullhomotopic_iff_exists_diskBoundaryInclusion_comp_eq
      (𝟙 (TopCat.diskBoundary.{u} 3))).2 ⟨TopCat.ofHom (r.comp g), hext⟩
  have : ContractibleSpace (TopCat.diskBoundary.{u} 3) :=
    (contractible_iff_id_nullhomotopic _).2 hnull
  have : ContractibleSpace S₀ := eU.symm.contractibleSpace
  exact not_contractibleSpace_sphere ‹ContractibleSpace S₀›

/-- **`S¹ × S²` is reducible:** `Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` does not satisfy
`TauCeti.IsSphereBoundsBall`. -/
theorem not_isSphereBoundsBall_circle_prod_sphere :
    ¬ IsSphereBoundsBall (Circle × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  not_isSphereBoundsBall_prod_sphere (H := EuclideanSpace ℝ (Fin 1)) (by simp) (by simp)

/-- **`ℝ × S²` does not satisfy `TauCeti.IsSphereBoundsBall`.** -/
theorem not_isSphereBoundsBall_real_prod_sphere :
    ¬ IsSphereBoundsBall (ℝ × sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  not_isSphereBoundsBall_prod_sphere (H := ℝ) (by simp) (by simp)

end TauCeti
