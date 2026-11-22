/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
Barraud, Damian, Humilière and Oancea up to a unit: a fundamental class is determined only up to
the orientation conventions that `TauCeti.IsFundamentalClass` leaves free, and the oriented,
sign-exact identity is not proved here.

The point is a special case. For a closed subset `Z ⊆ B` with a normal coordinate `ν : W → K`
(a Serre fibration on an open neighbourhood `W` of `Z`, onto a convex neighbourhood `K` of `0` in a
real normed space of finite dimension `r`, with zero set `Z`), the shriek map of the inclusion of
`Z` is `Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))`
(`TauCeti.TopCat.singularHomologyComplPreimageIso`). When `p` is trivial over `W` compatibly with
`ν`, it sends fundamental classes of `E` to fundamental classes of `p⁻¹(Z)`
(`TauCeti.IsFundamentalClass.singularHomologyComplPreimageIso_hom_singularHomologyπ`). A point
with a chart is the case `Z = {b}`; the core of a framed tube is another
(`TauCeti.IsFundamentalClass.singularHomologyComplPreimageCoreIso_hom_singularHomologyπ`, in
`TauCeti.AlgebraicTopology.Singular.Fibration.FramedTube`).

Without local triviality, the file also shows that `j_! μ` generates `Hₙ(F; N)` for a fundamental
class `μ` of `E` with coefficients in a module `N` over a commutative ring `k`, provided `Hₙ(F; N)`
and the local homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at one point `y ∈ F` are both free of rank one
(`TauCeti.IsFundamentalClass.span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top`).
The localization of `μ` at `y` factors through its localization at the fibre, and a linear map
between two copies of `k` reflects generators
(`LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top`). Combined with the naturality
of the shriek map (`TauCeti.livesOverFundamentalClass_homologyMap_iff`), this gives their
Corollary 2.13: for a map `f : E → E'` over `B` to a second Serre fibration, `f_* μ` lives over
the fundamental class at `b` as soon as the restriction of `f` to the fibres does not kill a
generator of `Hₙ(F; N)` (`TauCeti.IsFundamentalClass.livesOverFundamentalClass_homologyMap`).

## The argument

Write `F = p⁻¹(Z)` and fix `y ∈ F`. The point is that `j_!` is compatible with restriction to
`y`: the shriek map followed by `Hₙ(F) → Hₙ(F, F ∖ {y})` is the restriction
`Hₙ₊ᵣ(E, E ∖ F) → Hₙ₊ᵣ(E, E ∖ {y})` followed by an isomorphism
`Hₙ₊ᵣ(E, E ∖ {y}) ≅ Hₙ(F, F ∖ {y})` (`TauCeti.TopCat.singularHomologyComplSingletonPreimageIso`,
`TauCeti.TopCat.singularHomologyComplPreimageIso_hom_comp_singularHomologyπ`). A fundamental class
of `E` restricts to a generator of `Hₙ₊ᵣ(E, E ∖ {y})`, so its image under `j_!` restricts to a
generator of `Hₙ(F, F ∖ {y})`.

After excision onto `p⁻¹(W)`, the fibration followed by `ν` is a product `K × Y → K` over the
convex neighbourhood `K` of `0`. Let `A = K × (Y ∖ {y})`, an open set since `Y` is `T₁`. Then
`E ∖ {y}` is the union of `A` and of the part of `E` over `K ∖ {0}`, and the computation of
`Hₙ₊ᵣ(E, E ∖ F)` by relative Mayer–Vietoris sequences
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso`) runs relative to `A` as well
(`TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso`), compatibly with it
(`TauCeti.TopCat.singularHomologyPreimageNeZeroIso_hom_comp_homologyMap_comp_singularHomologyπ`).
The acyclicity it needs relative to `A` holds because moving along straight lines in `K`
keeps the coordinate in `Y`. Its value `Hₙ(E, A)` is `Hₙ(F, F ∖ {y})`, since the retraction of
`E` onto the fibre keeping the coordinate in `Y` is a homotopy inverse of the inclusion of pairs.

## Main definitions and results

* `TauCeti.TopCat.singularHomologyComplSingletonPreimageIso`: for a point `y` of `p⁻¹(Z)`, the
  isomorphism `Hₙ₊ᵣ(E, E ∖ {y}) ≅ Hₙ(p⁻¹(Z), p⁻¹(Z) ∖ {y})`.
* `TauCeti.TopCat.singularHomologyComplPreimageIso_hom_comp_singularHomologyπ`: the local homology
  along `p⁻¹(Z)` commutes with restriction to `y`.
* `TauCeti.IsFundamentalClass.singularHomologyComplPreimageIso_hom_singularHomologyπ`: the shriek
  map of the zero set of a normal coordinate sends fundamental classes of the total space to
  fundamental classes of its preimage.
* `TauCeti.TopCat.singularHomologyComplSingletonFiberIso`: for a point `y` of the fibre `F`, the
  isomorphism `Hₙ₊ᵣ(E, E ∖ {y}) ≅ Hₙ(F, F ∖ {y})`.
* `TauCeti.TopCat.singularHomologyComplFiberIso_hom_comp_singularHomologyπ`: the shriek map
  followed by `Hₙ(F) → Hₙ(F, F ∖ {y})` is the restriction `Hₙ₊ᵣ(E, E ∖ F) → Hₙ₊ᵣ(E, E ∖ {y})`
  followed by `TauCeti.TopCat.singularHomologyComplSingletonFiberIso`.
* `TauCeti.IsFundamentalClass.singularHomologyComplFiberIso_hom_fiberLocalization`: the shriek
  map of a point sends fundamental classes of the total space to fundamental classes of the
  fibre.
* `TauCeti.IsFundamentalClass.span_fiberLocalization_eq_top`: the localization at the fibre of a
  fundamental class generates the local homology along the fibre.
* `TauCeti.IsFundamentalClass.span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top`:
  the shriek of a fundamental class generates the top homology of the fibre.
* `TauCeti.IsFundamentalClass.livesOverFundamentalClass_homologyMap`: the image of a fundamental
  class under a map of fibrations that is nonzero on the fibres lives over the fundamental class.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Remark 2.10, Proposition 2.12
  and Corollary 2.13) and §6.4.2 (Proposition 6.15).
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
      (offSlice φ x₀.val) := fun f hf h ↦
  hf (Subtype.ext (eq_of_snd_eq φ hφ (Subtype.ext (f.property.trans x₀.property.symm)) h))

/-- The retraction of `E` onto the fibre over `0` which keeps the coordinate in `Y`. -/
private def retraction (h₀ : (0 : V) ∈ K) : E ⟶ _root_.TopCat.of (fiber p) :=
  _root_.TopCat.ofHom
    { toFun e := ⟨φ.symm (⟨0, h₀⟩, (φ e).2), by
        simp only [mem_preimage, mem_ofPred_eq, ← hφ, Homeomorph.apply_symm_apply]⟩
      continuous_toFun := by fun_prop }

include hφ in
private lemma mapsTo_retraction (h₀ : (0 : V) ∈ K) (x₀ : fiber p) :
    MapsTo (retraction φ hφ h₀) (offSlice φ x₀.val) ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p))) :=
  fun e he h ↦ he (by
    have h' := congrArg (fun f : fiber p ↦ (φ f).2) h
    simpa [retraction] using h')

variable [NormedSpace ℝ V] {R : Type*} [Ring R] (M : ModuleCat.{u} R)

include hφ in
/-- `E` is acyclic modulo `offSlice φ x` and the part over the complement in `K` of a closed
half-subspace: moving along straight lines in `K` towards a point of that complement, and keeping
the coordinate in `Y`, deforms `E` into it. -/
private lemma isZero_offSlice (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (W : Submodule ℝ V)
    (ψ : V →ₗ[ℝ] ℝ) (v : V) (hv : v ∈ W) (hψv : ψ v = 1) (n : ℕ) :
    IsZero ((TopPair.ofSubset
      (offSlice φ x ∪ p ⁻¹' {k : K | ¬((k : V) ∈ W ∧ ψ k ≤ 0)})).singularHomology
        M n) := by
  obtain ⟨c₀, hc₀K, hcS, hS⟩ :=
    exists_mem_starConvex_compl_setOf_mem_and_nonpos hK₀ hv (hψv ▸ one_pos)
  let B := offSlice φ x ∪ p ⁻¹' {k : K | ¬((k : V) ∈ W ∧ ψ k ≤ 0)}
  let c : K := ⟨c₀, hc₀K⟩
  -- The straight line from `p e` to `c` in `K`, with the coordinate of `e` in `Y`.
  let G : C(I × E, E) :=
    { toFun q := φ.symm (⟨AffineMap.lineMap (p q.2 : V) (c : V) (q.1 : ℝ),
        hK.lineMap_mem (p q.2).property c.property q.1.property⟩, (φ q.2).2)
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
  -- `H` is the homotopy with underlying map `G`, so `hGp` and `hGY` describe it.
  have hHG : ∀ q, H q = G q := fun _ ↦ rfl
  exact TopPair.isZero_singularHomology_ofSubset_of_homotopy H (fun τ e he ↦ by
    rcases he with he | he
    · refine Or.inl ?_
      simp only [mem_ofPred_eq, hHG, hGY]
      exact he
    · refine Or.inr ?_
      simp only [mem_preimage, mem_ofPred_eq] at he ⊢
      rw [hHG, hGp, AffineMap.lineMap_apply_module, add_comm]
      exact hS he τ.property.1 (sub_nonneg.2 τ.property.2) (add_sub_cancel _ _)) hρ M n

/-- **The pair of the fibre minus a point.** The inclusion of `(F, F ∖ {x₀})`, for `F` the fibre
over `0`, into `(E, offSlice φ x₀)` induces isomorphisms on relative homology: the retraction
keeping the coordinate in `Y` is an inverse up to the homotopy moving along straight lines in
`K`. -/
private def fiberPairIso (hK : Convex ℝ K) (h₀ : (0 : V) ∈ K) (x₀ : fiber p) (n : ℕ) :
    (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomology
        M n ≅
      (TopPair.ofSubset (offSlice φ x₀.val)).singularHomology M n where
  hom := TopPair.singularHomologyMap (TopPair.ofSubsetMap (fiberIncl p) (mapsTo_fiber φ hφ x₀)) _ n
  inv := TopPair.singularHomologyMap
    (TopPair.ofSubsetMap (retraction φ hφ h₀) (mapsTo_retraction φ hφ h₀ x₀)) _ n
  hom_inv_id := by
    have hιr : fiberIncl p ≫ retraction φ hφ h₀ = 𝟙 _ := by
      ext f
      refine eq_of_snd_eq φ hφ (Subtype.ext ?_) ?_
      · simp only [retraction, ← hφ]
        simpa [hφ] using f.property.symm
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
          hK.lineMap_mem h₀ (p q.2).property q.1.property⟩, (φ q.2).2)
        continuous_toFun := by fun_prop
        map_zero_left e := by simp [retraction]
        map_one_left e := eq_of_snd_eq φ hφ (Subtype.ext (by simp [← hφ])) (by simp) }
    -- `G q` is `φ.symm` applied to a pair whose coordinate in `Y` is that of `q.2`.
    have hGY : ∀ q, (φ (G q)).2 = (φ q.2).2 := fun q ↦
      (congrArg Prod.snd (φ.apply_symm_apply (_, (φ q.2).2)) :)
    rw [← TopPair.singularHomologyMap_comp, ← TopPair.ofSubsetMap_comp _ _ _ _
      ((mapsTo_fiber φ hφ x₀).comp (mapsTo_retraction φ hφ h₀ x₀)),
      ← TopPair.singularHomologyMap_id, ← TopPair.ofSubsetMap_id (B := offSlice φ x₀.val)
        fun e he ↦ he]
    refine TopPair.Homotopy.congr_singularHomologyMap (TopPair.ofSubsetHomotopy G ?_) _ n
    intro τ e he
    simp only [mem_ofPred_eq, hGY]
    exact he

omit [NormedSpace ℝ V] in
/-- Away from the fibre over `0`, a point avoids every point of that fibre. -/
private lemma mapsTo_compl_singleton (x₀ : fiber p) :
    MapsTo (𝟙 E) (p ⁻¹' {k : K | (k : V) ≠ 0}) ({x₀.val}ᶜ : Set E) := by
  rintro e he (rfl : e = x₀.val)
  exact he x₀.property

variable [FiniteDimensional ℝ V]

include hφ in
/-- `E ∖ {x₀}`, for `x₀` in the fibre over `0`, is `offSlice φ x₀` together with the part of `E`
over `K ∖ {0}`. -/
private def complSingletonPairIso (x₀ : fiber p) :
    TopPair.ofSubset ({x₀.val}ᶜ : Set E) ≅
      TopPair.ofSubset (offSlice φ x₀.val ∪ p ⁻¹' {k : K | (k : V) ≠ 0}) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun e ↦ by
    rw [offSlice_union φ hφ x₀.val x₀.property]
    rfl

/-- **The local homology of a trivial fibration at a point of the fibre over `0`.** Let `K` be a
convex neighbourhood of `0` in a finite-dimensional real normed space of dimension `r`, and let
`p : E ⟶ K` be trivial, through `φ : E ≃ₜ K × Y` with `Y` a `T₁` space. For a point `x₀` of the
fibre `F` over `0`, `Hₘ(E, E ∖ {x₀}) ≅ Hₙ(F, F ∖ {x₀})` for `m = n + r`: relative to
`offSlice φ x₀`, which with the part of `E` over `K ∖ {0}` makes up `E ∖ {x₀}`, the computation
of `TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso` gives `Hₙ(E, offSlice φ x₀)`, which is
`Hₙ(F, F ∖ {x₀})` (`fiberPairIso`). -/
private def complSingletonIso [T1Space Y] (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (x₀ : fiber p) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset ({x₀.val}ᶜ : Set E)).singularHomology M m ≅
      (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomology
        M n :=
  TopPair.singularHomologyMapIso _ (complSingletonPairIso φ hφ x₀) m ≪≫
    singularHomologyPreimageNeZeroRelIso M (isOpen_offSlice φ x₀.val)
      (isZero_offSlice φ hφ x₀.val M hK hK₀) n m h ≪≫
    (fiberPairIso φ hφ M hK (mem_of_mem_nhds hK₀) x₀ n).symm

/-- For a trivial fibration `p : E ⟶ K` as in `complSingletonIso`, which is moreover a Serre
fibration, and a point `x₀` of the fibre `F` over `0`, the shriek map `Hₘ(E, E ∖ F) ≅ Hₙ(F)`
followed by `Hₙ(F) ⟶ Hₙ(F, F ∖ {x₀})` is the restriction `Hₘ(E, E ∖ F) ⟶ Hₘ(E, E ∖ {x₀})`
followed by `complSingletonIso`. -/
private theorem singularHomologyPreimageNeZeroIso_hom_comp_singularHomologyπ [T1Space Y]
    (hp : serreFibrations p) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (x₀ : fiber p) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (singularHomologyPreimageNeZeroIso M hp hK hK₀ n m h).hom ≫
        (TopPair.ofSubset ({x₀}ᶜ : Set (_root_.TopCat.of (fiber p)))).singularHomologyπ
          M n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_singleton x₀))
          M m ≫ (complSingletonIso φ hφ M hK hK₀ x₀ n m h).hom := by
  have hcompat := singularHomologyPreimageNeZeroIso_hom_comp_homologyMap_comp_singularHomologyπ M
    (isOpen_offSlice φ x₀.val) (isZero_offSlice φ hφ x₀.val M hK hK₀) hp hK hK₀ n m h
  have hπ := TopPair.singularHomologyπ_naturality
    (TopPair.ofSubsetMap (fiberIncl p) (mapsTo_fiber φ hφ x₀)) M n
  rw [TopPair.ofSubsetMap_fst] at hπ
  have hincl : TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_singleton x₀) ≫
      (complSingletonPairIso φ hφ x₀).hom = TopPair.ofSubsetMap (𝟙 E) fun _ ↦ Or.inr := by
    simp only [complSingletonPairIso, TopPair.ofSubsetIso_hom]
    exact TopPair.ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ _ rfl
  simp only [complSingletonIso, TopPair.singularHomologyMapIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, Iso.eq_comp_inv,
    ← TopPair.singularHomologyMap_comp, hincl]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hπ.symm).trans hcompat)

end TrivialDisk

/-! ### Restriction to a point along the zero set of a normal coordinate -/

section NormalCoordinate

open TrivialDisk

variable {V : Type u} [NormedAddCommGroup V] {K : Set V} {E B : _root_.TopCat.{u}} {p : E ⟶ B}
  {W Z : Set B} {ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K}
  (hZ : ∀ w : W, (ν w : V) = 0 ↔ (w : B) ∈ Z) (hZW : Z ⊆ W)

/-- The complement of `p⁻¹(Z)` lies in the complement of each of its points. -/
private lemma mapsTo_compl_preimage (y : p ⁻¹' Z) :
    MapsTo (𝟙 E) (p ⁻¹' Z)ᶜ ({y.val}ᶜ : Set E) :=
  fun _ hz ↦ compl_subset_compl.2 (singleton_subset_iff.2 y.property) hz

/-- The point of the fibre over `0` of `TauCeti.TopCat.normalCoordinateProj` corresponding to the
point `y` of `p⁻¹(Z)`. -/
private abbrev preimagePoint (y : p ⁻¹' Z) : fiber (normalCoordinateProj p ν) :=
  (normalCoordinateProjFiberHomeomorph hZ hZW).symm y

private lemma coe_preimagePoint (y : p ⁻¹' Z) :
    ((preimagePoint hZ hZW y).val : E) = y.val :=
  coe_normalCoordinateProjFiberHomeomorph_symm_apply _ _ y

/-- The pair `(p⁻¹(W), p⁻¹(W) ∖ {y})`, read in `p⁻¹(W)`. -/
private def pointPairIso (y : p ⁻¹' Z) :
    TopPair.interPair (X := E) (p ⁻¹' W) ({y.val}ᶜ : Set E) ≅
      TopPair.ofSubset ({(preimagePoint hZ hZW y).val}ᶜ :
        Set (_root_.TopCat.of (p ⁻¹' W))) :=
  TopPair.ofSubsetIso (Homeomorph.refl _) fun z ↦ by
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, ← coe_preimagePoint hZ hZW y]
    exact Subtype.ext_iff.symm.not

/-- The fibre over `0` minus the point corresponding to `y` is `p⁻¹(Z)` minus `y`. -/
private def preimagePointPairIso (y : p ⁻¹' Z) :
    TopPair.ofSubset ({preimagePoint hZ hZW y}ᶜ :
        Set (_root_.TopCat.of (fiber (normalCoordinateProj p ν)))) ≅
      TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' Z))) :=
  TopPair.ofSubsetIso (normalCoordinateProjFiberHomeomorph hZ hZW) fun z ↦ by
    simp only [mem_compl_iff, mem_singleton_iff, preimagePoint]
    exact (Homeomorph.eq_symm_apply _).not

private lemma fst_preimagePointPairIso_hom (y : p ⁻¹' Z) :
    TopPair.Hom.fst (preimagePointPairIso hZ hZW y).hom =
      _root_.TopCat.ofHom (normalCoordinateProjFiberHomeomorph (p := p) hZ hZW) := by
  simp only [preimagePointPairIso, TopPair.ofSubsetIso_hom]
  exact TopPair.ofSubsetMap_fst _ _

/-- Excision onto `p⁻¹(W)` commutes with restriction to `y`. -/
private lemma excisionMap_comp_ofSubsetMap (y : p ⁻¹' Z) :
    TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ ≫
        TopPair.ofSubsetMap (𝟙 E) (mapsTo_compl_preimage y) =
      (normalCoordinateComplPairIso (p := p) hZ).hom ≫
        TopPair.ofSubsetMap (𝟙 _) (mapsTo_compl_singleton (preimagePoint hZ hZW y)) ≫
        (pointPairIso hZ hZW y).inv ≫
        TopPair.excisionMap (X := E) (p ⁻¹' W) ({y.val}ᶜ : Set E) := by
  refine TopPair.hom_ext_of_fst _ ?_
  ext z
  simp only [pointPairIso, normalCoordinateComplPairIso_hom,
    TopPair.ofSubsetIso_inv, TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
  -- Every map involved is an inclusion or an identity of the underlying spaces; `erw` sees
  -- through the bundled forms of these maps, which `rw` does not unfold.
  erw [TopPair.ofSubsetMap_fst_apply, TopPair.ofSubsetMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply, TopPair.excisionMap_fst_apply, TopPair.excisionMap_fst_apply,
    TopPair.ofSubsetMap_fst_apply]
  rfl

variable {R : Type*} [Ring R] (M : ModuleCat.{u} R) (hW : IsOpen W) (hZc : IsClosed Z)

include hW hZc hZW in
/-- Excision onto `p⁻¹(W)`, at a point `y` of `p⁻¹(Z)`. -/
private lemma isIso_singularHomologyMap_excisionMap_compl_singleton (y : p ⁻¹' Z) (m : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (TopPair.excisionMap (X := E) (p ⁻¹' W) ({y.val}ᶜ : Set E)) M m) :=
  TopPair.isIso_singularHomologyMap_excisionMap_of_closure_subset M
    (hW.preimage p.hom.continuous)
    ((closure_minimal (singleton_subset_iff.2 y.property)
      (hZc.preimage p.hom.continuous)).trans (preimage_mono hZW)) m

variable [NormedSpace ℝ V] [FiniteDimensional ℝ V] {Y : Type u} [TopologicalSpace Y] [T1Space Y]
  (φ : p ⁻¹' W ≃ₜ K × Y) (hφ : ∀ z, (φ z).1 = normalCoordinateProj p ν z)

/-- **Local homology at a point along the zero set of a normal coordinate.** Let `p : E ⟶ B` be a
map, `Z ⊆ B` closed and `ν : W → K` a normal coordinate of `Z` on an open neighbourhood `W`, onto a
convex neighbourhood `K` of `0` in a real normed space of finite dimension `r`. Suppose that over
`W` the map `p` is trivial compatibly with `ν`: `φ : p⁻¹(W) ≃ₜ K × Y`, with `Y` a `T₁` space, has
first coordinate `ν ∘ p`. Then for a point `y` of `p⁻¹(Z)`,
`Hₘ(E, E ∖ {y}) ≅ Hₙ(p⁻¹(Z), p⁻¹(Z) ∖ {y})` for `m = n + r`. After excision onto `p⁻¹(W)`, which
is a product with `K`, it is computed by relative Mayer–Vietoris sequences
(`TauCeti.TopCat.singularHomologyPreimageNeZeroRelIso`). When `p` and `ν` are Serre fibrations, it
relates the local homology along `p⁻¹(Z)` with restriction to `y`
(`TauCeti.TopCat.singularHomologyComplPreimageIso_hom_comp_singularHomologyπ`). -/
def singularHomologyComplSingletonPreimageIso (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V))
    (y : p ⁻¹' Z) (n m : ℕ) (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset ({y.val}ᶜ : Set E)).singularHomology M m ≅
      (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' Z)))).singularHomology M n :=
  haveI := isIso_singularHomologyMap_excisionMap_compl_singleton hZW M hW hZc y m
  (asIso (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := E) (p ⁻¹' W) ({y.val}ᶜ : Set E)) M m)).symm ≪≫
    TopPair.singularHomologyMapIso _ (pointPairIso hZ hZW y) m ≪≫
    complSingletonIso φ hφ M hK hK₀ (preimagePoint hZ hZW y) n m h ≪≫
    TopPair.singularHomologyMapIso _ (preimagePointPairIso hZ hZW y) n

/-- **The local homology along the zero set of a normal coordinate commutes with restriction to a
point.** In the situation of `TauCeti.TopCat.singularHomologyComplSingletonPreimageIso`, with `p`
and `ν` Serre fibrations, the isomorphism `Hₘ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` of
`TauCeti.TopCat.singularHomologyComplPreimageIso` followed by
`Hₙ(p⁻¹(Z)) ⟶ Hₙ(p⁻¹(Z), p⁻¹(Z) ∖ {y})` is the restriction
`Hₘ(E, E ∖ p⁻¹(Z)) ⟶ Hₘ(E, E ∖ {y})` followed by
`TauCeti.TopCat.singularHomologyComplSingletonPreimageIso`, for `m = n + dim V`. -/
theorem singularHomologyComplPreimageIso_hom_comp_singularHomologyπ (hp : serreFibrations p)
    (hν : serreFibrations ν) (hK : Convex ℝ K) (hK₀ : K ∈ 𝓝 (0 : V)) (y : p ⁻¹' Z) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (singularHomologyComplPreimageIso hZ M hW hZc hZW hp hν hK hK₀ n m h).hom ≫
        (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' Z)))).singularHomologyπ M n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E)
          fun _ hz ↦ compl_subset_compl.2 (singleton_subset_iff.2 y.property) hz) M m ≫
        (singularHomologyComplSingletonPreimageIso hZ hZW M hW hZc φ hφ hK hK₀ y n m h).hom := by
  -- Over `W` the fibration is trivial, so its local homology at the point of the fibre over `0`
  -- corresponding to `y` is computed by `complSingletonIso`.
  have hψ := TrivialDisk.singularHomologyPreimageNeZeroIso_hom_comp_singularHomologyπ φ hφ M
    (mem_serreFibrations_normalCoordinateProj hp hν) hK hK₀ (preimagePoint hZ hZW y) n m h
  -- On the fibres, the restriction to `y` is the restriction to the corresponding point over `0`.
  have hfib := TopPair.singularHomologyπ_naturality (preimagePointPairIso hZ hZW y).hom M n
  rw [fst_preimagePointPairIso_hom] at hfib
  -- Excision onto `p⁻¹(W)` commutes with restriction to `y`.
  have hexc := congrArg (TopPair.singularHomologyMap · M m)
    (excisionMap_comp_ofSubsetMap hZ hZW y)
  simp only [TopPair.singularHomologyMap_comp] at hexc
  have := isIso_singularHomologyMap_excisionMap_preimage (p := p) M hW hZc hZW m
  rw [← cancel_epi (TopPair.singularHomologyMap
    (TopPair.excisionMap (X := E) (p ⁻¹' W) (p ⁻¹' Z)ᶜ) M m)]
  calc _ = _ := singularHomologyMap_excisionMap_comp_singularHomologyComplPreimageIso_hom_assoc
        hZ M hW hZc hZW hp hν hK hK₀ n m h _
    -- Over `W`: the square of `complSingletonIso`, then the identification of fibres.
    _ = TopPair.singularHomologyMap (normalCoordinateComplPairIso (p := p) hZ).hom M m ≫
          (TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _)
            (mapsTo_compl_singleton (preimagePoint hZ hZW y))) M m ≫
            (complSingletonIso φ hφ M hK hK₀ (preimagePoint hZ hZW y) n m h).hom) ≫
          TopPair.singularHomologyMap (preimagePointPairIso hZ hZW y).hom M n :=
      congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) hfib).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hψ)))
    -- Back in `E`, through the excision square at `y`.
    _ = _ := by
      simp only [singularHomologyComplSingletonPreimageIso, Iso.trans_hom, Iso.symm_hom,
        asIso_inv, TopPair.singularHomologyMapIso, reassoc_of% hexc, Category.assoc,
        IsIso.hom_inv_id_assoc]
      rw [← TopPair.singularHomologyMap_comp_assoc (f := (pointPairIso hZ hZW y).inv),
        Iso.inv_hom_id, TopPair.singularHomologyMap_id, Category.id_comp]

end NormalCoordinate

/-! ### Fibre bundles over a chart -/

section Chart

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {R : Type*} [Ring R] (M : ModuleCat.{u} R)
  (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {ε : ℝ} (hε : ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε) (hp : serreFibrations p)
  {Y : Type u} [TopologicalSpace Y] (T : Bundle.Trivialization Y p)
  (hT : e.chartBall b ε ⊆ T.baseSet)

/-- **Local homology along the shriek map.** For a map `p : E ⟶ B` over a `T₁` space, trivial over
a chart ball about `b` with fibre a `T₁` space, and a point `y` of the fibre `F = p⁻¹(b)`,
`Hₘ(E, E ∖ {y}) ≅ Hₙ(F, F ∖ {y})` for `m = n + dim V`. It is
`TauCeti.TopCat.singularHomologyComplSingletonPreimageIso` for the normal coordinate `x ↦ e x - e b`
of `b` on `OpenPartialHomeomorph.chartBall e b ε`. When `p` is a Serre fibration, it relates the
shriek map `TauCeti.TopCat.singularHomologyComplFiberIso` with restriction to `y`
(`TauCeti.TopCat.singularHomologyComplFiberIso_hom_comp_singularHomologyπ`). -/
def singularHomologyComplSingletonFiberIso [T1Space Y] (y : p ⁻¹' {b}) (n m : ℕ)
    (h : n + finrank ℝ V = m) :
    (TopPair.ofSubset ({y.val}ᶜ : Set E)).singularHomology M m ≅
      (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' {b})))).singularHomology
        M n :=
  singularHomologyComplSingletonPreimageIso (e.isoOfHomeo_chartBallHomeomorph_hom_eq_zero_iff hε hb)
    (singleton_subset_iff.2 (e.mem_chartBall_self hb hε₀)) M (e.isOpen_chartBall b ε)
    isClosed_singleton (e.chartBallTrivialization hε T hT)
    (e.chartBallTrivialization_apply_fst hε T hT) (convex_ball 0 ε) (ball_mem_nhds 0 hε₀) y n m h

include hp in
/-- **The shriek map commutes with restriction to a point of the fibre.** For a Serre fibration
`p : E ⟶ B` over a `T₁` space, trivial over a chart ball about `b` with fibre a `T₁` space, and a
point `y` of the fibre `F = p⁻¹(b)`, the shriek map `Hₘ(E, E ∖ F) ≅ Hₙ(F)` followed by
`Hₙ(F) ⟶ Hₙ(F, F ∖ {y})` is the restriction `Hₘ(E, E ∖ F) ⟶ Hₘ(E, E ∖ {y})` followed by
`TauCeti.TopCat.singularHomologyComplSingletonFiberIso`, for `m = n + dim V`. -/
theorem singularHomologyComplFiberIso_hom_comp_singularHomologyπ [T1Space Y] (y : p ⁻¹' {b})
    (n m : ℕ) (h : n + finrank ℝ V = m) :
    (singularHomologyComplFiberIso M e hb hε hε₀ hp n m h).hom ≫
        (TopPair.ofSubset ({y}ᶜ : Set (_root_.TopCat.of (p ⁻¹' {b})))).singularHomologyπ
          M n =
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 E)
          fun _ hz ↦ compl_subset_compl.2 (singleton_subset_iff.2 y.property) hz) M m ≫
        (singularHomologyComplSingletonFiberIso M e hb hε hε₀ T hT y n m h).hom := by
  rw [singularHomologyComplFiberIso_def]
  exact singularHomologyComplPreimageIso_hom_comp_singularHomologyπ _ _ M _ _
    (e.chartBallTrivialization hε T hT) (e.chartBallTrivialization_apply_fst hε T hT) hp _ _ _ y
    n m h

end Chart

end TopCat

/-! ### The shriek map on fundamental classes -/

section FundamentalClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {K : Set V} {E B : _root_.TopCat.{u}} {p : E ⟶ B} {W Z : Set B}
  {ν : _root_.TopCat.of W ⟶ _root_.TopCat.of K} (hZ : ∀ w : W, (ν w : V) = 0 ↔ (w : B) ∈ Z)
  {R : Type u} [Ring R] (hW : IsOpen W) (hZc : IsClosed Z) (hZW : Z ⊆ W)
  {Y : Type u} [TopologicalSpace Y] [T1Space Y]

/-- **The shriek map of the zero set of a normal coordinate sends fundamental classes to
fundamental classes.** Let `p : E ⟶ B` be a Serre fibration, `Z ⊆ B` closed and `ν : W → K` a
Serre fibration on an open neighbourhood `W` of `Z`, onto a convex neighbourhood `K` of `0` in a
real normed space of finite dimension `r`, with zero set `Z`. Suppose that `p` is trivial over `W`
compatibly with `ν`: `φ : p⁻¹(W) ≃ₜ K × Y`, with `Y` a `T₁` space, has first coordinate `ν ∘ p`.
If `μ ∈ Hₙ₊ᵣ(E; R)` is a fundamental class of `E`, then its image under the shriek map
`j_! : Hₙ₊ᵣ(E) → Hₙ₊ᵣ(E, E ∖ p⁻¹(Z)) ≅ Hₙ(p⁻¹(Z))` of the inclusion of `Z`
(`TauCeti.TopCat.singularHomologyComplPreimageIso`) is a fundamental class of `p⁻¹(Z)`. -/
theorem IsFundamentalClass.singularHomologyComplPreimageIso_hom_singularHomologyπ
    (φ : p ⁻¹' W ≃ₜ K × Y) (hφ : ∀ z, (φ z).1 = TopCat.normalCoordinateProj p ν z)
    (hp : TopCat.serreFibrations p) (hν : TopCat.serreFibrations ν) (hK : Convex ℝ K)
    (hK₀ : K ∈ 𝓝 (0 : V)) {n m : ℕ} (h : n + finrank ℝ V = m)
    {μ : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) m : ModuleCat.{u} R)}
    (hμ : IsFundamentalClass μ) :
    IsFundamentalClass (M := p ⁻¹' Z)
      ((TopCat.singularHomologyComplPreimageIso hZ (ModuleCat.of R R) hW hZc hZW hp hν hK hK₀ n m
          h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom μ)) := by
  refine (isFundamentalClass_iff _).2 fun y ↦ ?_
  let Ψ := TopCat.singularHomologyComplSingletonPreimageIso hZ hZW (ModuleCat.of R R) hW hZc φ hφ
    hK hK₀ y n m h
  -- Restricting to `y` before or after the shriek map differ by the isomorphism `Ψ`.
  have hy : singularHomologyToLocalHomology (ModuleCat.of R R) y n
      ((TopCat.singularHomologyComplPreimageIso hZ (ModuleCat.of R R) hW hZc hZW hp hν hK hK₀ n m
          h).hom.hom
        (((TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom μ)) =
      Ψ.hom.hom (singularHomologyToLocalHomology (ModuleCat.of R R) y.val m μ) := by
    refine (singularHomologyToLocalHomology_eq_singularHomologyπ _ y _).trans ?_
    rw [singularHomologyToLocalHomology_eq_singularHomologyπ _ y.val,
      ← TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id _
        (TopCat.mapsTo_compl_preimage y)]
    exact congrArg
      (fun f ↦ f.hom (((TopPair.ofSubset (p ⁻¹' Z)ᶜ).singularHomologyπ (ModuleCat.of R R) m).hom μ))
      (TopCat.singularHomologyComplPreimageIso_hom_comp_singularHomologyπ hZ hZW
        (ModuleCat.of R R) hW hZc φ hφ hp hν hK hK₀ y n m h)
  rw [hy, ← Set.image_singleton, Submodule.span_image, (isFundamentalClass_iff _).1 hμ y.val,
    Submodule.map_top, LinearMap.range_eq_top]
  exact fun z ↦ ⟨Ψ.inv.hom z, by simp⟩

end FundamentalClass

section FundamentalClassChart

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
      ((TopCat.singularHomologyComplFiberIso (ModuleCat.of R R) e hb hε hε₀ hp n m h).hom.hom
        ((fiberLocalization (ModuleCat.of R R) p b m).hom μ)) := by
  rw [TopCat.singularHomologyComplFiberIso_def]
  exact IsFundamentalClass.singularHomologyComplPreimageIso_hom_singularHomologyπ _ _ _ _
    (e.chartBallTrivialization hε T hT) (e.chartBallTrivialization_apply_fst hε T hT) hp _ _ _ h hμ

end FundamentalClassChart

/-! ### Fundamental classes whose shriek generates, without local triviality -/

namespace IsFundamentalClass

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {E B : _root_.TopCat.{u}} [T1Space B] {p : E ⟶ B} {k : Type u} [CommRing k]
  {N : ModuleCat.{u} k} (e : OpenPartialHomeomorph B V) {b : B} (hb : b ∈ e.source)
  {n m : ℕ} (h : n + finrank ℝ V = m)
  {μ : ((_root_.TopCat.toSSet.obj E).homology N m : ModuleCat.{u} k)} {y : E} (hy : p y = b)

include hb h hy in
/-- **The localization at the fibre of a fundamental class generates.** Let `p : E ⟶ B` be a Serre
fibration over a `T₁` space, with a chart `e` of dimension `r` at `b`, and let `μ ∈ Hₙ₊ᵣ(E; N)` be a
fundamental class. If the homology `Hₙ(p⁻¹(b); N)` of the fibre and the local homology
`Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the commutative ring `k`,
then the localization of `μ` at the fibre generates `Hₙ₊ᵣ(E, E ∖ p⁻¹(b); N)`. -/
theorem span_fiberLocalization_eq_top
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hμ : IsFundamentalClass μ) :
    Submodule.span k {(fiberLocalization N p b m).hom μ} = ⊤ := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  have hyF : ({y} : Set E) ⊆ p ⁻¹' {b} := singleton_subset_iff.2 hy
  -- The localization along the fibre is a copy of `k`, through the homology of the fibre.
  let eF : (localHomology N (p ⁻¹' {b}) m : ModuleCat.{u} k) ≃ₗ[k] k :=
    (TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).toLinearEquiv.trans ψ
  refine LinearMap.span_singleton_eq_top_of_span_singleton_apply_eq_top
    (localHomologyRestriction N hyF m).hom eF φ ?_
  -- Restricting the localization at the fibre to `y` gives the localization at `y`.
  have hres : (localHomologyRestriction N hyF m).hom ((fiberLocalization N p b m).hom μ) =
      singularHomologyToLocalHomology N y m μ := by
    rw [singularHomologyToLocalHomology_eq_singularHomologyπ]
    exact singularHomologyπ_localHomologyRestriction_apply N hyF m μ
  rw [hres]
  exact (isFundamentalClass_iff μ).1 hμ y

include hy in
/-- **The shriek of a fundamental class generates the homology of the fibre.** Let `p : E ⟶ B` be
a Serre fibration over a `T₁` space, with a chart `e` of dimension `r` at `b`, and let
`μ ∈ Hₙ₊ᵣ(E; N)` be a fundamental class. If the homology `Hₙ(p⁻¹(b); N)` of the fibre and the
local homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the
commutative ring `k`, then the image `j_! μ` of `μ` under the shriek map
`Hₙ₊ᵣ(E; N) → Hₙ₊ᵣ(E, E ∖ p⁻¹(b); N) ≅ Hₙ(p⁻¹(b); N)` generates `Hₙ(p⁻¹(b); N)`. For closed
oriented manifolds this is `j_! [E] = ±[p⁻¹(b)]`. -/
theorem span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top {ε : ℝ}
    (hε : Metric.ball (e b) ε ⊆ e.target) (hε₀ : 0 < ε)
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hμ : IsFundamentalClass μ) :
    Submodule.span k
        {(TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).hom.hom
          ((fiberLocalization N p b m).hom μ)} = ⊤ := by
  rw [← (TopCat.singularHomologyComplFiberIso N e hb hε hε₀ hp n m h).toLinearEquiv_apply,
    LinearEquiv.span_singleton_apply_eq_top_iff]
  exact span_fiberLocalization_eq_top e hb h hy φ ψ hp hμ

include hb h hy in
/-- **The image of a fundamental class under a map of fibrations** (Barraud–Damian–Humilière–Oancea,
Corollary 2.13). Let `p : E ⟶ B` and `p' : E' ⟶ B` be Serre fibrations over a `T₁` space, with a
chart `e` of dimension `r` at `b`, and let `f : E ⟶ E'` be a map over `B`. Let `μ ∈ Hₙ₊ᵣ(E; N)` be
a fundamental class, and suppose that the homology `Hₙ(p⁻¹(b); N)` of the fibre and the local
homology `Hₙ₊ᵣ(E, E ∖ {y}; N)` at a point `y` of the fibre are both isomorphic to the commutative
ring `k`. If the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` does not kill a generator `ν` of
`Hₙ(p⁻¹(b); N)`, for instance a fundamental class of the fibre, then `f_* μ` lives over the
fundamental class at `b`. -/
theorem livesOverFundamentalClass_homologyMap {E' : _root_.TopCat.{u}} {p' : E' ⟶ B}
    {f : E ⟶ E'} (hf : f ≫ p' = p)
    (φ : (localHomology N ({y} : Set E) m : ModuleCat.{u} k) ≃ₗ[k] k)
    (ψ : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k) ≃ₗ[k] k)
    (hp : TopCat.serreFibrations p) (hp' : TopCat.serreFibrations p') (hμ : IsFundamentalClass μ)
    {ν : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).obj
      (_root_.TopCat.of (p ⁻¹' {b})) : ModuleCat.{u} k)} (hν : Submodule.span k {ν} = ⊤)
    (hfν : (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} k) n).obj N).map
      (f.preimageMap hf {b})).hom ν ≠ 0) :
    LivesOverFundamentalClass N p' b
      ((SSet.homologyMap (_root_.TopCat.toSSet.map f) N m).hom μ) := by
  obtain ⟨ε, hε₀, hε⟩ := Metric.isOpen_iff.1 e.open_target (e b) (e.map_source hb)
  rw [livesOverFundamentalClass_homologyMap_iff e hb hε hε₀ hp hp' hf h μ]
  -- The shriek of `μ` is a unit multiple of `ν`.
  obtain ⟨u, hu⟩ := ψ.exists_units_smul_eq_of_span_singleton_eq_top hν
    (span_singularHomologyComplFiberIso_hom_fiberLocalization_eq_top e hb h hy hε hε₀ φ ψ hp hμ)
  rw [← hu, map_smul]
  exact fun h0 ↦ hfν (u.isUnit.smul_eq_zero.1 h0)

end IsFundamentalClass

end TauCeti
