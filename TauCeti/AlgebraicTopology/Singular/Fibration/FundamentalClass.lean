/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Trivialization
public import TauCeti.AlgebraicTopology.Singular.Fibration.LocalHomology
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.IsFundamentalClass

/-!
# The shriek map of a point sends fundamental classes to fundamental classes

Let `p : E ⟶ B` be a Serre fibration over a `T₁` space, and let `e : B → V` be a chart at `b` to a
real normed space of finite dimension `r`. The shriek map of the inclusion of `b` is the
localization at the fibre followed by the identification of local homology along the fibre
(`TauCeti.TopCat.singularHomologyComplFiberIso`),

`j_! : Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)`, `F = p⁻¹(b)`.

This file shows that when `p` is trivial over a chart ball about `b`, with fibre a `T₁` space,
`j_!` sends fundamental classes of `E` to fundamental classes of `F`
(`TauCeti.IsFundamentalClass.singularHomologyComplFiberIso_hom_fiberLocalization`), in the sense
of `TauCeti.IsFundamentalClass`: classes whose image in the local homology at every point
generates it. For a fibre bundle of closed manifolds this is the identity `j_![E] = [F]` of
Barraud, Damian, Humilière and Oancea, which turns the nonvanishing of `σ_*[F]` into a criterion
for `σ_*[E]` to live over the fundamental class of the base.

## The argument

Fix `y ∈ F`. The point is that `j_!` is compatible with restriction to `y`: the shriek map
followed by `Hₙ(F) → Hₙ(F, F ∖ {y})` is the restriction `Hₙ₊ᵣ(E, E ∖ F) → Hₙ₊ᵣ(E, E ∖ {y})`
followed by an isomorphism. A fundamental class of `E` restricts to a generator of
`Hₙ₊ᵣ(E, E ∖ {y})`, so its image under `j_!` restricts to a generator of `Hₙ(F, F ∖ {y})`.

After excision onto the part of `E` over the chart ball, the fibration is a product `K × Y → K`
over a ball `K` about `0`. Let `A = K × (Y ∖ {y})`, an open set since `Y` is `T₁`. Then
`E ∖ {y}` is the union of `A` and of the part of `E` over `K ∖ {0}`, and the computation of
`Hₙ₊ᵣ(E, E ∖ F)` by relative Mayer–Vietoris sequences
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`) runs relative to `A` as well
(`TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso`), compatibly with it
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso_hom_comp_singularHomologyπ`). The acyclicity
it needs relative to `A` holds because moving along straight lines in `K` keeps the coordinate in
`Y`. Its value `Hₙ(E, A)` is `Hₙ(F, F ∖ {y})`, since the retraction of `E` onto the fibre keeping
the coordinate in `Y` is a homotopy inverse of the inclusion of pairs.

## Main results

* `TauCeti.IsFundamentalClass.singularHomologyComplFiberIso_hom_fiberLocalization`: the shriek
  map of a point sends fundamental classes of the total space to fundamental classes of the
  fibre.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Remark 2.10 and Corollary 2.13).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, local homology and fundamental classes.
-/

public section

noncomputable section

open CategoryTheory Limits Module Metric Set Topology
open scoped unitInterval

universe u

namespace TauCeti

namespace TopCat

/-! ### The local homology of a trivial fibration at a point of a fibre -/

namespace TrivialDisk

variable {V : Type u} [NormedAddCommGroup V] {K : Set V}
  {E : _root_.TopCat.{u}} {p : E ⟶ _root_.TopCat.of K} {Y : Type u} [TopologicalSpace Y]
  (φ : E ≃ₜ K × Y) (hφ : ∀ e, (φ e).1 = p e) (x : E)

/-- The points of `E` whose coordinate in `Y` differs from that of `x`. -/
private abbrev offSlice : Set E :=
  {e | (φ e).2 ≠ (φ x).2}

private lemma isOpen_offSlice [T1Space Y] : IsOpen (offSlice φ x) :=
  isClosed_singleton.isOpen_compl.preimage (continuous_snd.comp φ.continuous)

include hφ in
/-- Two points over the same point of `K` with the same coordinate in `Y` are equal. -/
private lemma eq_of_snd_eq {e e' : E} (hp : p e = p e') (h : (φ e).2 = (φ e').2) : e = e' :=
  φ.injective (Prod.ext ((hφ e).trans (hp.trans (hφ e').symm)) h)

include hφ in
/-- Over `0`, the complement of `x` is the union of `offSlice φ x` and the part over `K ∖ {0}`. -/
private lemma offSlice_union (hx : (p x : V) = 0) :
    offSlice φ x ∪ p ⁻¹' {k : K | (k : V) ≠ 0} = {x}ᶜ := by
  ext e
  simp only [mem_union, mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_singleton_iff]
  refine ⟨?_, fun he ↦ ?_⟩
  · rintro (h | h) rfl
    exacts [h rfl, h hx]
  · by_contra! h
    exact he (eq_of_snd_eq φ hφ (Subtype.ext (h.2.trans hx.symm)) h.1)

variable (p) in
/-- The fibre of `p` over `0`. -/
private abbrev fiber : Set E :=
  p ⁻¹' {k : K | (k : V) = 0}

variable (p) in
/-- The inclusion of the fibre of `p` over `0`. -/
private abbrev fiberIncl : _root_.TopCat.of (fiber p) ⟶ E :=
  (TopPair.ofSubset (fiber p)).map

include hφ in
/-- The fibre minus a point `x₀` lies in `offSlice φ x₀`. -/
private lemma mapsTo_fiber (x₀ : fiber p) :
    MapsTo (fiberIncl p) ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))
      (offSlice φ x₀.1) := fun f hf h ↦
  hf (Subtype.ext (eq_of_snd_eq φ hφ (Subtype.ext (f.2.trans x₀.2.symm)) h))

/-- The retraction of `E` onto the fibre over `0` which keeps the coordinate in `Y`. -/
private def retraction (h₀ : (0 : V) ∈ K) : E ⟶ _root_.TopCat.of (fiber p) :=
  _root_.TopCat.ofHom
    { toFun e := ⟨φ.symm (⟨0, h₀⟩, (φ e).2), by
        simp only [mem_preimage, mem_ofPred_eq, ← hφ, Homeomorph.apply_symm_apply]⟩
      continuous_toFun := by fun_prop }

include hφ in
private lemma mapsTo_retraction (h₀ : (0 : V) ∈ K) (x₀ : fiber p) :
    MapsTo (retraction φ hφ h₀) (offSlice φ x₀.1) ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p))) :=
  fun e he h ↦ he (by
    have h' := congrArg (fun f : fiber p ↦ (φ f).2) h
    simpa [retraction] using h')

variable [NormedSpace ℝ V] (R : Type u) [Ring R]

include hφ in
/-- `E` is acyclic modulo `offSlice φ x` and the part over the complement in `K` of a closed
half-subspace: moving along straight lines in `K` towards a point of that complement, and keeping
the coordinate in `Y`, deforms `E` into it. -/
private lemma isZero_offSlice (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (W : Submodule ℝ V)
    (ψ : V →ₗ[ℝ] ℝ) (v : V) (hv : v ∈ W) (hψv : ψ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset
      (offSlice φ x ∪ p ⁻¹' {k : K | ¬((k : V) ∈ W ∧ ψ k ≤ 0)})).singularHomology
        (ModuleCat.of R R) n) := by
  -- A neighbourhood of `0` is absorbent, so it contains a positive multiple `c` of `v`.
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t • v ∈ K :=
    ((absorbent_nhds_zero hK₀).eventually_nhdsNE_zero v).filter_mono
      (nhdsWithin_mono _ fun _ h ↦ ne_of_gt h)
  obtain ⟨t, htK, ht : 0 < t⟩ := (hev.and self_mem_nhdsWithin).exists
  have hψc : 0 < ψ (t • v) := by simpa [hψv] using ht
  have hS := starConvex_compl_setOf_mem_and_nonpos (W.smul_mem t hv) hψc
  have hcS : t • v ∉ {y | y ∈ W ∧ ψ y ≤ 0} := fun h ↦ (not_le.2 hψc) h.2
  let B := offSlice φ x ∪ p ⁻¹' {k : K | ¬((k : V) ∈ W ∧ ψ k ≤ 0)}
  let c : K := ⟨t • v, htK⟩
  -- The straight line from `p e` to `c` in `K`, with the coordinate of `e` in `Y`.
  let G : C(I × E, E) :=
    { toFun q := φ.symm (⟨AffineMap.lineMap (p q.2 : V) (c : V) (q.1 : ℝ),
        hK.lineMap_mem (p q.2).2 c.2 q.1.2⟩, (φ q.2).2)
      continuous_toFun := by fun_prop }
  have hGp : ∀ q, (p (G q) : V) = AffineMap.lineMap (p q.2 : V) (c : V) (q.1 : ℝ) := fun q ↦ by
    rw [← hφ]
    simp [G]
  have hGY : ∀ q, (φ (G q)).2 = (φ q.2).2 := fun q ↦ by simp [G]
  let ρ : E ⟶ E := _root_.TopCat.ofHom ⟨fun e ↦ G (1, e), by fun_prop⟩
  have hρ : ∀ e, ρ e ∈ B := fun e ↦ Or.inr <| by
    simp only [ρ, _root_.TopCat.hom_ofHom, ContinuousMap.coe_mk, mem_preimage, mem_ofPred_eq,
      hGp, Icc.coe_one, AffineMap.lineMap_apply_one]
    exact hcS
  let H : (_root_.TopCat.Hom.hom (𝟙 E)).Homotopy ρ.hom :=
    { toContinuousMap := G
      map_zero_left e := eq_of_snd_eq φ hφ (Subtype.ext ((hGp (0, e)).trans (by simp)))
        (by simpa using hGY (0, e))
      map_one_left _ := rfl }
  have hH := TopPair.ofSubsetHomotopy (B := B) (B' := B) H fun τ e he ↦ by
    rcases he with he | he
    · refine Or.inl ?_
      -- `H` is the homotopy with underlying map `G`; read the goal through `G` to use `hGY`.
      change (φ (G (τ, e))).2 ≠ (φ x).2
      rw [hGY]
      exact he
    · refine Or.inr ?_
      simp only [mem_preimage, mem_ofPred_eq] at he ⊢
      rw [show H (τ, e) = G (τ, e) from rfl, hGp, AffineMap.lineMap_apply_module, add_comm]
      exact hS he τ.2.1 (sub_nonneg.2 τ.2.2) (add_sub_cancel _ _)
  refine TopPair.isZero_singularHomology_of_homotopy (P := TopPair.ofSubset B)
    (f := TopPair.ofSubsetMap ρ fun e _ ↦ hρ e) ?_
    (_root_.TopCat.ofHom ⟨fun e ↦ ⟨ρ e, hρ e⟩, by fun_prop⟩) ?_ (ModuleCat.of R R) n
  · rw [← TopPair.ofSubsetMap_id (B := B) fun _ hx ↦ hx]
    exact hH
  · ext e
    exact (TopPair.ofSubsetMap_fst_apply _ _ e).symm

/-- **The pair of the fibre minus a point.** The inclusion of `(F, F ∖ {x₀})`, for `F` the fibre
over `0`, into `(E, offSlice φ x₀)` induces isomorphisms on relative homology: the retraction
keeping the coordinate in `Y` is an inverse up to the homotopy moving along straight lines in
`K`. -/
private def fiberPairIso (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (x₀ : fiber p) (n : ℕ) :
    (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomology
        (ModuleCat.of R R) n ≅
      (TopPair.ofSubset (offSlice φ x₀.1)).singularHomology (ModuleCat.of R R) n where
  hom := TopPair.singularHomologyMap (TopPair.ofSubsetMap (fiberIncl p) (mapsTo_fiber φ hφ x₀)) _ n
  inv := TopPair.singularHomologyMap
    (TopPair.ofSubsetMap (retraction φ hφ h₀) (mapsTo_retraction φ hφ h₀ x₀)) _ n
  hom_inv_id := by
    have hιr : fiberIncl p ≫ retraction φ hφ h₀ = 𝟙 _ := by
      ext f
      refine eq_of_snd_eq φ hφ (Subtype.ext ?_) ?_
      · simp only [retraction, ← hφ]
        simpa [hφ] using f.2.symm
      · simp [retraction]
    rw [← TopPair.singularHomologyMap_comp, ← TopPair.singularHomologyMap_id]
    congr 1
    refine TopPair.hom_ext_of_fst _ ?_
    rw [TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst, TopPair.ofSubsetMap_fst, TopPair.Hom.fst_id]
    exact hιr
  inv_hom_id := by
    -- Move along straight lines in `K` from the retraction to the identity.
    let G : (_root_.TopCat.Hom.hom (retraction φ hφ h₀ ≫ fiberIncl p)).Homotopy
        (_root_.TopCat.Hom.hom (𝟙 E)) :=
      { toFun q := φ.symm (⟨AffineMap.lineMap (0 : V) (p q.2 : V) (q.1 : ℝ),
          hK.lineMap_mem h₀ (p q.2).2 q.1.2⟩, (φ q.2).2)
        continuous_toFun := by fun_prop
        map_zero_left e := by simp [retraction]
        map_one_left e := eq_of_snd_eq φ hφ (Subtype.ext (by simp [← hφ])) (by simp) }
    rw [← TopPair.singularHomologyMap_comp, ← TopPair.ofSubsetMap_comp _ _ _ _
      ((mapsTo_fiber φ hφ x₀).comp (mapsTo_retraction φ hφ h₀ x₀)),
      ← TopPair.singularHomologyMap_id, ← TopPair.ofSubsetMap_id (B := offSlice φ x₀.1)
        fun e he ↦ he]
    refine TopPair.Homotopy.congr_singularHomologyMap (TopPair.ofSubsetHomotopy G ?_) _ n
    intro τ e he
    -- The homotopy is `φ.symm` applied to a pair whose coordinate in `Y` is that of `e`.
    change (φ (φ.symm (_, (φ e).2))).2 ≠ (φ x₀.1).2
    rwa [Homeomorph.apply_symm_apply]

omit [NormedSpace ℝ V] in
/-- Away from the fibre over `0`, a point avoids every point of that fibre. -/
private lemma mapsTo_compl_singleton (x₀ : fiber p) :
    MapsTo (𝟙 E) (p ⁻¹' {k : K | (k : V) ≠ 0}) ({x₀.1}ᶜ : Set E) := by
  rintro e he (rfl : e = x₀.1)
  exact he x₀.2

variable [FiniteDimensional ℝ V]

include hφ in
/-- **The local homology of a trivial fibration at a point of the fibre over `0`.** Let `K` be a
convex neighbourhood of `0` in a finite-dimensional real normed space of dimension `r`, and let
`p : E ⟶ K` be a Serre fibration which is trivial, through `φ : E ≃ₜ K × Y` with `Y` a `T₁`
space. For a point `x₀` of the fibre `F` over `0`, the shriek map
`Hₘ(E, E ∖ F) ≅ Hₙ(F)` followed by `Hₙ(F) ⟶ Hₙ(F, F ∖ {x₀})` factors as the restriction
`Hₘ(E, E ∖ F) ⟶ Hₘ(E, E ∖ {x₀})` followed by an isomorphism, for `m = n + r`. -/
private theorem exists_iso_comp_singularHomologyMap [T1Space Y] (hp : serreFibrations p)
    (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (x₀ : fiber p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    ∃ ψ : (TopPair.ofSubset ({x₀.1}ᶜ : Set E)).singularHomology (ModuleCat.of R R) m ≅
        (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomology
          (ModuleCat.of R R) n,
      (singularHomologyPreimageNeZeroIso R hp hK hK₀ n m h).hom ≫
          (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomologyπ
            (ModuleCat.of R R) n =
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_singleton x₀))
          (ModuleCat.of R R) m ≫ ψ.hom := by
  have hA := isOpen_offSlice φ x₀.1
  have hA' := isZero_offSlice φ hφ x₀.1 R hK hK₀
  -- `E ∖ {x₀}` is `offSlice φ x₀` together with the part of `E` over `K ∖ {0}`.
  let setIso : TopPair.ofSubset ({x₀.1}ᶜ : Set E) ≅
      TopPair.ofSubset (offSlice φ x₀.1 ∪ p ⁻¹' {k : K | (k : V) ≠ 0}) :=
    TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
      rw [offSlice_union φ hφ x₀.1 x₀.2]
      rfl
  refine ⟨asIso (TopPair.singularHomologyMap setIso.hom _ m) ≪≫
    singularHomologyPreimageNeZeroRelIso R hA hA' n m h ≪≫
      (fiberPairIso φ hφ R hK (mem_of_mem_nhds hK₀) x₀ n).symm, ?_⟩
  have hcompat := singularHomologyPreimageNeZeroIso_hom_comp_singularHomologyπ R hA hA' hp hK hK₀
    n m h
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (fiberIncl p) (mapsTo_fiber φ hφ x₀)) (ModuleCat.of R R) n
  rw [TopPair.ofSubsetMap_fst] at hπ
  have hincl : TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_singleton x₀) ≫ setIso.hom =
      TopPair.ofSubsetMap (𝟙 E) fun _ ↦ Or.inr := by
    simp only [setIso, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
  rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv,
    ← TopPair.singularHomologyMap_comp, hincl]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hπ.symm).trans hcompat)

end TrivialDisk

/-! ### Fibre bundles over a chart -/

section Chart

open TrivialDisk

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} (R : Type u) [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : serreFibrations p)
  {Y : Type u} [TopologicalSpace Y] (T : Bundle.Trivialization Y p)
  (hT : e.chartBall b ε ⊆ T.baseSet)

/-- Over `OpenPartialHomeomorph.chartBall e b ε`, a trivialization of `p` identifies the part of
`E` with the product of the ball of radius `ε` about `0` and the fibre. -/
private def chartBallTrivialization :
    p ⁻¹' e.chartBall b ε ≃ₜ ball (0 : V) ε × Y :=
  (T.preimageHomeomorph hT).trans ((e.chartBallHomeomorph hε).prodCongr (Homeomorph.refl Y))

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] in
private lemma chartBallTrivialization_fst (z : p ⁻¹' e.chartBall b ε) :
    (chartBallTrivialization e hε T hT z).1 = e.chartBallProj hε p z :=
  Subtype.ext (by
    rw [OpenPartialHomeomorph.coe_chartBallProj_apply]
    simp [chartBallTrivialization, T.preimageHomeomorph_apply])

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] in
/-- The complement of the fibre over `b` lies in the complement of each of its points. -/
private lemma mapsTo_compl_fiber (y : p ⁻¹' {b}) :
    MapsTo (𝟙 E) (p ⁻¹' {b})ᶜ ({y.1}ᶜ : Set E) :=
  fun _ hz ↦ compl_subset_compl.2 (singleton_subset_iff.2 y.2) hz

variable (y : p ⁻¹' {b})

/-- The point of the fibre over `0` of `OpenPartialHomeomorph.chartBallProj e hε p` corresponding
to the point `y` of the fibre over `b`. -/
private abbrev fiberPoint : fiber (e.chartBallProj hε p) :=
  (e.chartBallProjFiberHomeomorph hb hε p hε₀).symm y

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] in
private lemma coe_fiberPoint : ((fiberPoint e hb hε hε₀ y).1 : E) = y.1 :=
  e.coe_chartBallProjFiberHomeomorph_symm_apply hb hε p hε₀ y

/-- The pair `(U, U ∖ {y})` for `U` the part of `E` over the chart ball, read in `U`. -/
private def pointPairIso :
    TopPair.interPair (X := E) (p ⁻¹' e.chartBall b ε) ({y.1}ᶜ : Set E) ≅
      TopPair.ofSubset ({(fiberPoint e hb hε hε₀ y).1}ᶜ :
        Set (_root_.TopCat.of (p ⁻¹' e.chartBall b ε))) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ by
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, ← coe_fiberPoint e hb hε hε₀ y]
    exact Subtype.ext_iff.symm.not

/-- The fibre over `0` minus the point corresponding to `y` is the fibre over `b` minus `y`. -/
private def fiberPointPairIso :
    TopPair.ofSubset ({fiberPoint e hb hε hε₀ y}ᶜ :
        Set (_root_.TopCat.of (fiber (e.chartBallProj hε p)))) ≅
      TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' {b}))) :=
  TopPair.ofSubsetIso (e.chartBallProjFiberHomeomorph hb hε p hε₀) fun z ↦ by
    simp only [mem_compl_iff, mem_singleton_iff, fiberPoint]
    exact (Homeomorph.eq_symm_apply _).not

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] in
private lemma fst_fiberPointPairIso_hom :
    TopPair.Hom.fst (fiberPointPairIso e hb hε hε₀ y).hom =
      _root_.TopCat.ofHom (e.chartBallProjFiberHomeomorph hb hε p hε₀) := by
  simp only [fiberPointPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst _ _

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [T1Space B] in
/-- Excision onto the part of `E` over the chart ball commutes with restriction to `y`. -/
private lemma excisionMap_comp_ofSubsetMap :
    TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ ≫
        TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_fiber y) =
      (e.chartBallComplFiberPairIso hb hε p).hom ≫
        TopPair.ofSubsetMap (𝟙 _) (mapsTo_compl_singleton (fiberPoint e hb hε hε₀ y)) ≫
        (pointPairIso e hb hε hε₀ y).inv ≫
        TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) ({y.1}ᶜ : Set E) := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext z
  simp only [pointPairIso, OpenPartialHomeomorph.chartBallComplFiberPairIso_hom,
    TopPair.ofSubsetIso_inv, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  -- Every map involved is an inclusion or an identity of the underlying spaces; `erw` sees
  -- through the bundled forms of these maps, which `rw` does not unfold.
  erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply, TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply]
  rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
include hb hε₀ in
/-- Excision onto the part of `E` over the chart ball, at the point `y`. -/
private lemma isIso_singularHomologyMap_excisionMap_compl_singleton (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) ({y.1}ᶜ : Set E))
        (ModuleCat.of R R) m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_closure_subset (ModuleCat.of R R)
    ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    ((closure_minimal (singleton_subset_iff.2 y.2)
      (isClosed_singleton.preimage p.hom.continuous)).trans
      (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)))) m

include hp hT in
/-- **Local homology along the shriek map.** For a Serre fibration `p : E ⟶ B` over a `T₁` space,
trivial over a chart ball about `b` with fibre a `T₁` space, and a point `y` of the fibre
`F = p⁻¹(b)`, the shriek map `Hₘ(E, E ∖ F) ≅ Hₙ(F)` followed by `Hₙ(F) ⟶ Hₙ(F, F ∖ {y})` is the
restriction `Hₘ(E, E ∖ F) ⟶ Hₘ(E, E ∖ {y})` followed by an isomorphism, for `m = n + dim V`. -/
private theorem exists_iso_singularHomologyComplFiberIso_hom_comp [T1Space Y] (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    ∃ Ψ : (TopPair.ofSubset ({y.1}ᶜ : Set E)).singularHomology (ModuleCat.of R R) m ≅
        (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' {b})))).singularHomology
          (ModuleCat.of R R) n,
      (singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom ≫
          (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' {b})))).singularHomologyπ
            (ModuleCat.of R R) n =
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E)
          (mapsTo_compl_fiber y)) (ModuleCat.of R R) m ≫ Ψ.hom := by
  -- Over the chart ball the fibration is trivial, so its local homology at the point of the fibre
  -- over `0` corresponding to `y` is computed by `exists_iso_comp_singularHomologyMap`.
  obtain ⟨ψ, hψ⟩ := exists_iso_comp_singularHomologyMap (chartBallTrivialization e hε T hT)
    (chartBallTrivialization_fst e hε T hT) R (e.mem_serreFibrations_chartBallProj hε hp)
    (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) (fiberPoint e hb hε hε₀ y) n m h
  have := isIso_singularHomologyMap_excisionMap_compl_singleton R e hb hε₀ y m
  have := TopPair.isIso_singularHomologyMap_excisionMap_of_isClosed_subset (ModuleCat.of R R)
    (X := E) ((e.isOpen_chartBall b ε).preimage p.hom.continuous)
    (isClosed_singleton.preimage p.hom.continuous)
    (preimage_mono (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀))) m
  refine ⟨(asIso (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) ({y.1}ᶜ : Set E))
      (ModuleCat.of R R) m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (pointPairIso e hb hε hε₀ y) m ≪≫ ψ ≪≫
      TopPair.singularHomologyMapIso _ (fiberPointPairIso e hb hε hε₀ y) n, ?_⟩
  -- On the fibres, the restriction to `y` is the restriction to the corresponding point over `0`.
  have hfib := TopPair.singularHomologyπ_naturality (fiberPointPairIso e hb hε hε₀ y).hom
    (ModuleCat.of R R) n
  rw [fst_fiberPointPairIso_hom] at hfib
  -- After excision onto the chart ball, both sides are computed over the chart ball.
  have hright := excisionMap_comp_ofSubsetMap e hb hε hε₀ y
  apply_fun (TopPair.singularHomologyMap · (ModuleCat.of R R) m) at hright
  simp only [TopPair.singularHomologyMap_comp] at hright
  rw [← cancel_epi (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := E) (p ⁻¹' e.chartBall b ε) (p ⁻¹' {b})ᶜ) (ModuleCat.of R R) m)]
  refine (singularHomologyMap_excisionMap_comp_singularHomologyComplFiberIso_hom_assoc R e hb hε
    hε₀ hp n m h _).trans (Eq.trans (b := TopPair.singularHomologyMap
      (e.chartBallComplFiberPairIso hb hε p).hom (ModuleCat.of R R) m ≫
      (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _)
        (mapsTo_compl_singleton (fiberPoint e hb hε hε₀ y))) (ModuleCat.of R R) m ≫ ψ.hom) ≫
      TopPair.singularHomologyMap (fiberPointPairIso e hb hε hε₀ y).hom (ModuleCat.of R R) n) ?_ ?_)
  · exact congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hfib).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hψ)))
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, TopPair.singularHomologyMapIso,
      reassoc_of% hright, Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← TopPair.singularHomologyMap_comp_assoc (f := (pointPairIso e hb hε hε₀ y).inv),
      Iso.inv_hom_id, TopPair.singularHomologyMap_id, Category.id_comp]
end Chart

end TopCat

/-! ### The shriek map on fundamental classes -/

section FundamentalClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type u} [Ring R]
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : TopCat.serreFibrations p)
  {Y : Type u} [TopologicalSpace Y] [T1Space Y] (T : Bundle.Trivialization Y p)
  (hT : e.chartBall b ε ⊆ T.baseSet)

include hT in
/-- **The shriek map of a point sends fundamental classes to fundamental classes.** Let
`p : E ⟶ B` be a Serre fibration over a `T₁` space, trivial over the chart ball
`OpenPartialHomeomorph.chartBall e b ε` of a chart `e` of dimension `r` at `b`, with fibre a `T₁`
space. If `μ ∈ Hₙ₊ᵣ(E; R)` is a fundamental class of `E`, then its image under the shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ F) ≅ Hₙ(F)` of the inclusion of `b` is a fundamental class of the
fibre `F = p⁻¹(b)`. For a fibre bundle of closed manifolds this is the identity `j_![E] = [F]` of
Barraud–Damian–Humilière–Oancea (their Remark 2.10), up to the orientation conventions which
`TauCeti.IsFundamentalClass` leaves free. -/
theorem IsFundamentalClass.singularHomologyComplFiberIso_hom_fiberLocalization {n m : ℕ}
    (h : n + finrank ℝ V = m)
    {μ : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass (M := p ⁻¹' {b})
      ((TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom μ)) := by
  refine (isFundamentalClass_iff _).2 fun y ↦ ?_
  obtain ⟨Ψ, hΨ⟩ := TopCat.exists_iso_singularHomologyComplFiberIso_hom_comp R e hb hε hε₀ hp T hT
    y n m h
  -- Restricting to `y` before or after the shriek map differ by the isomorphism `Ψ`.
  have hy : singularHomologyToLocalHomology (ModuleCat.of R R) y n
      ((TopCat.singularHomologyComplFiberIso R e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom μ)) =
      Ψ.hom.hom (singularHomologyToLocalHomology (ModuleCat.of R R) y.1 m μ) := by
    rw [singularHomologyToLocalHomology_eq, singularHomologyToLocalHomology_eq,
      ← TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id _
        (TopCat.mapsTo_compl_fiber y)]
    exact congrArg (fun f ↦ f.hom ((fiberLocalization (ModuleCat.of R R) p b m).hom μ)) hΨ
  rw [hy, ← Set.image_singleton, Submodule.span_image, (isFundamentalClass_iff _).1 hμ y.1,
    Submodule.map_top, LinearMap.range_eq_top]
  exact fun z ↦ ⟨Ψ.inv.hom z, by simp⟩

end FundamentalClass

end TauCeti
