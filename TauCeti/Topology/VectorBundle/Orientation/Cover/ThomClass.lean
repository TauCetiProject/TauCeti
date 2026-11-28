/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Basic

/-!
# The Thom class of a bundle pulled back to its orientation cover

Let `E → B` be a real vector bundle of rank `r`, let `B' → B` be its orientation double cover
(`TauCeti.VectorBundleOrientationCover`), whose points are the pairs of a point `b` of `B` and an
orientation of `E_b`, and let `σ` be its deck involution, reversing the orientation
(`TauCeti.VectorBundleOrientationCover.deck`). The pull-back `E'` of `E` to `B'` is oriented by the
tautological orientation (`TauCeti.VectorBundleOrientationCover.tautologicalOrientation`). The
lift `δ` of `σ` to the Thom pair `(E', E'₀)`
(`TauCeti.VectorBundleOrientationCover.deckThomPairMap`) pulls the Thom class `U` of the
tautological orientation back to `-U`, so the homology Thom map `Φ(x) = π_*(x ⌢ U)` anticommutes
with the two involutions, `Φ ∘ δ_* = -σ_* ∘ Φ`
(`TauCeti.VectorBundleOrientationCover.singularHomologyMap_deckThomPairMap_comp_homologyThomMap`);
these are in `TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Basic`.

This file records that with coefficients in a field `K`, when `g`
generates `Hʳ(F, F ∖ {0}; K)`, `Φ` carries the classes of `Hₚ₊ᵣ(E', E'₀; K)` fixed by `δ_*` onto
the classes of `Hₚ(B'; K)` negated by `σ_*`
(`TauCeti.VectorBundleOrientationCover.map_ker_singularHomologyMap_deckThomPairMap_sub_one`). The
resulting isomorphism is `TauCeti.VectorBundleOrientationCover.homologyThomMapDeckEquiv`.

## Main results

* `TauCeti.VectorBundleOrientationCover.map_ker_singularHomologyMap_deckThomPairMap_sub_one`:
  over a field, `Φ` carries the `δ_*`-invariant classes onto the `σ_*`-anti-invariant classes.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (orientations and the orientation double cover) and §10 (the Thom class of
  an oriented bundle and the Thom isomorphism).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 3.H (the orientation
  double cover and homology with local coefficients) and Section 4.D (the Thom isomorphism).
-/

public section

noncomputable section

open Bundle CategoryTheory Module AlgebraicTopology

universe w

namespace TauCeti.VectorBundleOrientationCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {ι : Type}

variable [Fintype ι] [FiniteDimensional ℝ F] (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι)

section Field

variable {K : Type w} [Field K]
  {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology (ModuleCat.of K K) K
    (ModuleCat.of K K) (finrank ℝ F)}

/-- The homology Thom map of the tautological orientation is bijective with coefficients in a
field. -/
private theorem bijective_homologyThomMap_tautologicalOrientation
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective
      (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom :=
  bijective_homologyThomMap p m h
    ((tautologicalOrientation (F := F) (E := E) (ι := ι)).isThomClass_thomClassOfModel hι ω hg)

/-- **The Thom isomorphism carries deck-invariant classes to deck-anti-invariant classes.** With
coefficients in a field `K`, the homology Thom map of the tautological orientation carries the
classes of `Hₘ(E', E'₀; K)` fixed by the lifted deck involution `δ` onto the classes of
`Hₚ(B'; K)` negated by the deck involution, `m = r + p`. -/
theorem map_ker_singularHomologyMap_deckThomPairMap_sub_one
    (hg : Submodule.span K {g} = ⊤) {p m : ℕ} (h : finrank ℝ F + p = m) :
    (LinearMap.ker ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom -
        1)).map
      (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
        (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom =
    LinearMap.ker ((((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(VectorBundleOrientationCover F E ι,
          VectorBundleOrientationCover F E ι)))).hom + 1) := by
  set T := (homologyThomMap F ((projection : C(VectorBundleOrientationCover F E ι, B)) *ᵖ E)
    (ModuleCat.of K K) _ p m h (tautologicalOrientation.thomClassOfModel hι ω g)).hom
  have hc (x) :
      T ((TopPair.singularHomologyMap (deckThomPairMap F E ι) (ModuleCat.of K K) m).hom x) =
      -(((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
        (TopCat.ofHom (deck (F := F) (E := E) (ι := ι) : C(VectorBundleOrientationCover F E ι,
          VectorBundleOrientationCover F E ι)))).hom (T x) :=
    congr($(singularHomologyMap_deckThomPairMap_comp_homologyThomMap hι ω g
      (ModuleCat.of K K) h).hom x)
  have hT := bijective_homologyThomMap_tautologicalOrientation (E := E) hι ω hg h
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply,
    one_apply_eq_self, sub_eq_zero, add_eq_zero_iff_eq_neg]
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact neg_eq_iff_eq_neg.1 ((hx ▸ hc x).symm)
  · obtain ⟨x, rfl⟩ := hT.2 y
    exact ⟨x, hT.1 ((hc x).trans (neg_eq_iff_eq_neg.2 hy)), rfl⟩

end Field

end TauCeti.VectorBundleOrientationCover
