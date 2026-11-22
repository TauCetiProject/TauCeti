/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.AlgebraicTopology.Singular.Twisted.Functoriality

/-!
# Classes with local coefficients living over the fundamental class

Let `p : E → M` be a map to a manifold, for instance the projection of a fibration, let `b ∈ M`,
and let `K` be a local coefficient system on `E`. A class `α ∈ Hₖ(E; K)` **lives over the
fundamental class** of `M` at `b` if its **localization at the fibre**

`Hₖ(E; K) → Hₖ(E, E ∖ p⁻¹(b); K)`

(`TauCeti.LocalCoefficientSystem.fiberLocalization`) is nonzero
(`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass`). This is the form of Definition 2.3 of
Barraud, Damian, Humilière and Oancea that applies over a base `M` which is not orientable. Such a
base has no integral fundamental class, only the twisted class `[M]_or ∈ Hₙ(M; or_M)`
(`TauCeti.Manifold.OrientationCover.twistedFundamentalClass`), so the total space carries the
pulled-back coefficients `K = p*or_M`. For a Serre fibration and a pulled-back system the relative
group is the shifted homology of the fibre, by the twisted shriek map of the inclusion of `b`
(`TauCeti.TopCat.livesOverFundamentalClass_iff_twistedHomologyComplFiberIso_hom_ne_zero`). As for
constant coefficients (`TauCeti.LivesOverFundamentalClass`), the relative group is used in the
definition because it does not depend on a chart at `b`.

* **Naturality** (the topological form of the source's Proposition 2.12, with coefficients). A map
  `σ : E → E'` over `M`, that is with `p' ∘ σ = p`, is a map of pairs
  `(E, E ∖ p⁻¹(b)) → (E', E' ∖ p'⁻¹(b))`, and localization commutes with the maps it induces with
  coefficients `σ*K'` and `K'`
  (`TauCeti.LocalCoefficientSystem.twistedHomologyMap_comp_fiberLocalization`). So if `σ_* α`
  lives over the fundamental class, so does `α`
  (`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass.of_twistedHomologyMap`).
* **Change of coefficients.** Localization commutes with morphisms of local systems
  (`TauCeti.LocalCoefficientSystem.twistedHomologyCoefficientMap_comp_fiberLocalization`). If the
  image of `α` under a morphism lives over the fundamental class, so does `α`
  (`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass.of_twistedHomologyCoefficientMap`), and
  an isomorphism of local systems preserves and reflects living over the fundamental class
  (`TauCeti.LocalCoefficientSystem.livesOverFundamentalClass_twistedHomologyCoefficientMap_iff`).
* **Constant coefficients.** For a constant system with fibre `N`, twisted homology is ordinary
  homology with coefficients in `N`, and under this identification the two notions of living over
  the fundamental class agree
  (`TauCeti.LocalCoefficientSystem.livesOverFundamentalClass_constantFunctor_iff`).

## Main definitions

* `TauCeti.LocalCoefficientSystem.fiberLocalization`: the map `Hₖ(E; K) → Hₖ(E, E ∖ p⁻¹(b); K)`.
* `TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass`: its value at `α` is nonzero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4 (Definition 2.3, Example 2.4,
  Lemma 2.9, Proposition 2.12).
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.H, homology with local coefficients and the orientation local system.
-/

public section

noncomputable section

open CategoryTheory Set

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {E E' : TopCat.{v}} {M : Type*}

section Localization

variable (K : LocalCoefficientSystem.{u, v, max v w} R E)

/-- The **localization at the fibre** of a map `p : E → M` over a point `b`, with coefficients in a
local system `K` on `E`: the map `Hₖ(E; K) → Hₖ(E, E ∖ p⁻¹(b); K)` from the twisted homology of `E`
to its twisted homology relative to the complement of the fibre. A class lives over the
fundamental class of `M` at `b` when its localization is nonzero
(`TauCeti.LocalCoefficientSystem.LivesOverFundamentalClass`). -/
abbrev fiberLocalization (p : E → M) (b : M) (k : ℕ) :
    K.twistedHomology k ⟶ (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomology K k :=
  (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomologyπ K k

/-- **Naturality of the localization at the fibre in the coefficients**: a morphism `η : K ⟶ K'`
of local systems on `E` commutes with the localization at the fibre of `p` over `b`. -/
@[reassoc]
theorem twistedHomologyCoefficientMap_comp_fiberLocalization
    {K K' : LocalCoefficientSystem.{u, v, max v w} R E} (η : K ⟶ K') (p : E → M) (b : M)
    (k : ℕ) :
    twistedHomologyCoefficientMap η k ≫ K'.fiberLocalization p b k =
      K.fiberLocalization p b k ≫
        (TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomologyCoefficientMap η k :=
  ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomologyπ_comp_twistedHomologyCoefficientMap
    η k).symm

/-- The map of pairs `(E, E ∖ p⁻¹(b)) ⟶ (E', E' ∖ p'⁻¹(b))` given by a map `σ : E ⟶ E'` over
`M`, that is with `p' ∘ σ = p`. It is `TopPair.ofSubsetMap σ`, restated here so that its ambient
component is `σ` by definition: the twisted homology of its source then has the coefficients
`σ*K'` of a local system `K'` on `E'`, without a transport along `TopPair.ofSubsetMap_fst`. -/
abbrev fiberComplPairMap (σ : E ⟶ E') {p : E → M} {p' : E' → M} (h : p' ∘ σ = p) (b : M) :
    TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E) ⟶ TopPair.ofSubset ((p' ⁻¹' {b})ᶜ : Set E') :=
  have hσ : MapsTo σ ((p ⁻¹' {b})ᶜ) ((p' ⁻¹' {b})ᶜ) := by
    subst h
    exact fun _ hx ↦ hx
  TopPair.ofHom σ (TopCat.ofHom ⟨hσ.restrict, σ.hom.continuous.restrict hσ⟩)

/-- `TauCeti.LocalCoefficientSystem.fiberComplPairMap` is the map of pairs
`TopPair.ofSubsetMap σ`. -/
theorem fiberComplPairMap_eq_ofSubsetMap (σ : E ⟶ E') {p : E → M} {p' : E' → M} (h : p' ∘ σ = p)
    (b : M) (hσ : MapsTo σ ((p ⁻¹' {b})ᶜ) ((p' ⁻¹' {b})ᶜ)) :
    fiberComplPairMap σ h b = TopPair.ofSubsetMap σ hσ := by
  ext x : 3
  · exact Subtype.ext (TopPair.ofSubsetMap_snd_apply σ hσ x).symm
  · exact (TopPair.ofSubsetMap_fst_apply σ hσ x).symm

/-- **Naturality of the localization at the fibre**: for a map `σ : E ⟶ E'` over `M`, that is
with `p' ∘ σ = p`, and a local system `K'` on `E'`, localizing `σ_* α` at the fibre of `p'` over
`b` is the image under the map of pairs `(E, E ∖ p⁻¹(b)) → (E', E' ∖ p'⁻¹(b))` of the localization
of `α` at the fibre of `p`, with coefficients `σ*K'`. This is the topological form of the
naturality of the shriek map of a point under maps of fibrations
(Barraud–Damian–Humilière–Oancea, Proposition 2.12), with local coefficients. -/
@[reassoc]
theorem twistedHomologyMap_comp_fiberLocalization (σ : E ⟶ E') {p : E → M} {p' : E' → M}
    (h : p' ∘ σ = p) (b : M) (K' : LocalCoefficientSystem.{u, v, max v w} R E') (k : ℕ) :
    twistedHomologyMap σ K' k ≫ K'.fiberLocalization p' b k =
      ((pullback σ.hom).obj K').fiberLocalization p b k ≫
        TopPair.twistedHomologyMap (fiberComplPairMap σ h b) K' k :=
  TopPair.twistedHomologyπ_naturality (fiberComplPairMap σ h b) K' k

end Localization

section LivesOver

variable (K : LocalCoefficientSystem.{u, v, max v w} R E)

/-- A class `α ∈ Hₖ(E; K)` with coefficients in a local system `K` **lives over the fundamental
class** of `M` at `b`, for a map `p : E → M`, if its localization
`Hₖ(E; K) → Hₖ(E, E ∖ p⁻¹(b); K)` at the fibre over `b` is nonzero.

For a Serre fibration over a manifold and a system pulled back from the base, the target is
identified with the homology of the fibre shifted by the dimension
(`TauCeti.TopCat.twistedHomologyComplFiberIso`), and the localization with the twisted shriek map of
the inclusion of `b`. With `K` the pullback of the orientation local system of the base, this is
Definition 2.3 of Barraud–Damian–Humilière–Oancea over a base which need not be orientable. For a
constant system it is `TauCeti.LivesOverFundamentalClass`
(`TauCeti.LocalCoefficientSystem.livesOverFundamentalClass_constantFunctor_iff`). -/
def LivesOverFundamentalClass (p : E → M) (b : M) {k : ℕ} (α : K.twistedHomology k) : Prop :=
  (K.fiberLocalization p b k).hom α ≠ 0

theorem livesOverFundamentalClass_iff (p : E → M) (b : M) {k : ℕ} (α : K.twistedHomology k) :
    K.LivesOverFundamentalClass p b α ↔ (K.fiberLocalization p b k).hom α ≠ 0 :=
  Iff.rfl

/-- Living over the fundamental class only depends on the fibre: for maps `p : E → M` and
`p' : E → M'` with `p⁻¹(b) = p'⁻¹(b')`, a class lives over the fundamental class at `b` for `p`
exactly when it does at `b'` for `p'`. -/
theorem livesOverFundamentalClass_congr {M' : Type*} {p : E → M} {p' : E → M'} {b : M} {b' : M'}
    (h : p ⁻¹' {b} = p' ⁻¹' {b'}) {k : ℕ} (α : K.twistedHomology k) :
    K.LivesOverFundamentalClass p b α ↔ K.LivesOverFundamentalClass p' b' α := by
  rw [livesOverFundamentalClass_iff, livesOverFundamentalClass_iff, fiberLocalization,
    fiberLocalization, h]

/-- The zero class does not live over the fundamental class. -/
@[simp]
theorem not_livesOverFundamentalClass_zero (p : E → M) (b : M) (k : ℕ) :
    ¬K.LivesOverFundamentalClass p b (0 : K.twistedHomology k) :=
  fun h ↦ h (map_zero _)

variable {K} in
/-- A class lives over the fundamental class at `b` if one of its scalar multiples does. -/
theorem LivesOverFundamentalClass.of_smul {p : E → M} {b : M} {k : ℕ} {α : K.twistedHomology k}
    (c : R) (h : K.LivesOverFundamentalClass p b (c • α)) : K.LivesOverFundamentalClass p b α :=
  fun h' ↦ h (by rw [map_smul, h', smul_zero])

variable {K} in
/-- **Classes living over the fundamental class pull back along morphisms of coefficients.** If
the image of `α` under a morphism `η : K ⟶ K'` of local systems lives over the fundamental class at
`b`, then so does `α`. -/
theorem LivesOverFundamentalClass.of_twistedHomologyCoefficientMap
    {K' : LocalCoefficientSystem.{u, v, max v w} R E} (η : K ⟶ K') {p : E → M} {b : M} {k : ℕ}
    {α : K.twistedHomology k}
    (h : K'.LivesOverFundamentalClass p b ((twistedHomologyCoefficientMap η k).hom α)) :
    K.LivesOverFundamentalClass p b α := by
  intro h'
  apply h
  rw [← ModuleCat.comp_apply, twistedHomologyCoefficientMap_comp_fiberLocalization,
    ModuleCat.comp_apply, h', map_zero]

variable {K} in
/-- **Living over the fundamental class is invariant under isomorphisms of coefficients**: for an
isomorphism `e : K ≅ K'` of local systems on `E`, the image of `α` under `e` lives over the
fundamental class at `b` exactly when `α` does. -/
theorem livesOverFundamentalClass_twistedHomologyCoefficientMap_iff
    {K' : LocalCoefficientSystem.{u, v, max v w} R E} (e : K ≅ K') {p : E → M} {b : M} {k : ℕ}
    (α : K.twistedHomology k) :
    K'.LivesOverFundamentalClass p b ((twistedHomologyCoefficientMap e.hom k).hom α) ↔
      K.LivesOverFundamentalClass p b α := by
  rw [livesOverFundamentalClass_iff, livesOverFundamentalClass_iff, ← ModuleCat.comp_apply,
    twistedHomologyCoefficientMap_comp_fiberLocalization, ModuleCat.comp_apply]
  let P := TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)
  exact not_congr (Iso.toLinearEquiv
    ⟨P.twistedHomologyCoefficientMap e.hom k, P.twistedHomologyCoefficientMap e.inv k,
      P.twistedHomologyCoefficientMap_hom_inv_id e k,
      P.twistedHomologyCoefficientMap_inv_hom_id e k⟩).map_eq_zero_iff

/-- **Classes living over the fundamental class pull back along maps over the base.** If
`σ : E ⟶ E'` satisfies `p' ∘ σ = p`, `K'` is a local system on `E'` and `σ_* α` lives over the
fundamental class at `b` for `p'`, then `α`, with coefficients `σ*K'`, lives over the fundamental
class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_twistedHomologyMap (σ : E ⟶ E') {p : E → M} {p' : E' → M}
    (h : p' ∘ σ = p) {b : M} {K' : LocalCoefficientSystem.{u, v, max v w} R E'} {k : ℕ}
    {α : ((pullback σ.hom).obj K').twistedHomology k}
    (hα : K'.LivesOverFundamentalClass p' b ((twistedHomologyMap σ K' k).hom α)) :
    ((pullback σ.hom).obj K').LivesOverFundamentalClass p b α := by
  intro h'
  apply hα
  -- The relative group of `E'` is stated on the ambient space of a pair, which is `E'` only up to
  -- unfolding, so the naturality square is applied as a term rather than by rewriting.
  exact (congrArg (fun φ ↦ φ.hom α) (twistedHomologyMap_comp_fiberLocalization σ h b K' k)).trans
    ((congrArg (TopPair.twistedHomologyMap (fiberComplPairMap σ h b) K' k).hom h').trans
      (map_zero _))

/-- If the image `p_* α ∈ Hₖ(M; L)` of a class `α ∈ Hₖ(E; p*L)` lives over the fundamental class
at `b` for the identity of `M`, then `α` lives over the fundamental class at `b` for `p`. -/
theorem LivesOverFundamentalClass.of_twistedHomologyMap_proj {B : TopCat.{v}} (p : E ⟶ B)
    {b : B} {L : LocalCoefficientSystem.{u, v, max v w} R B} {k : ℕ}
    {α : ((pullback p.hom).obj L).twistedHomology k}
    (hα : L.LivesOverFundamentalClass id b ((twistedHomologyMap p L k).hom α)) :
    ((pullback p.hom).obj L).LivesOverFundamentalClass p b α :=
  .of_twistedHomologyMap p (Function.id_comp _) hα

end LivesOver

section Constant

variable {E : TopCat.{v}} {M : Type v}

/-- **With constant coefficients, living over the fundamental class is the untwisted notion.** For
the constant local system with fibre `N` on `E`, a class `α` of twisted homology lives over the
fundamental class at `b` exactly when its image in ordinary homology with coefficients in `N`
(`TauCeti.LocalCoefficientSystem.twistedHomologyConstantIso`) does, in the sense of
`TauCeti.LivesOverFundamentalClass`. -/
theorem livesOverFundamentalClass_constantFunctor_iff (N : ModuleCat.{v} R) (p : E → M) (b : M)
    {k : ℕ} (α : ((constantFunctor E).obj N).twistedHomology k) :
    ((constantFunctor E).obj N).LivesOverFundamentalClass p b α ↔
      TauCeti.LivesOverFundamentalClass N p b ((twistedHomologyConstantIso E N k).hom.hom α) := by
  have h := congrArg (fun φ ↦ φ.hom α)
    ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomologyπ_comp_twistedHomologyConstantIso_hom
      N k)
  -- The untwisted localization is stated on `TopCat.of E`, which is `E` only up to unfolding, so
  -- the two sides are compared as terms rather than by rewriting.
  exact ((TopPair.ofSubset ((p ⁻¹' {b})ᶜ : Set E)).twistedHomologyConstantIso N
    k).toLinearEquiv.map_ne_zero_iff.symm.trans <| (Iff.of_eq (congrArg (· ≠ 0) h)).trans
      (TauCeti.livesOverFundamentalClass_iff N p b _).symm

end Constant

end TauCeti.LocalCoefficientSystem
