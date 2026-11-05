/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Basic
import TauCeti.Algebra.Module.Equiv.SpanSingleton

/-!
# Thom classes of oriented vector bundles

Let `E → B` be a real vector bundle with model fibre `F` of finite dimension `r`, and let `o` be
an orientation of `E` (`TauCeti.VectorBundleOrientation`). Fix an orientation `ω` of `F` and a
class `g ∈ Hʳ(F, F ∖ {0}; R, M)`. A linear trivialization `e` whose base set contains `b`
identifies the fibre pair `(E_b, E_b ∖ {0})` with `(F, F ∖ {0})`, and so reads `g` as a class of
the fibre pair. Two trivializations read `g` as classes differing by the sign of the determinant
of their coordinate change at `b`
(`Bundle.Trivialization.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`), and this sign
is `+1` exactly when they read the orientation `o b` as the same orientation of `F`. So the class
read off along any trivialization carrying `o b` to `ω`, or the negative of the class read off
along one carrying `o b` to `-ω`, is a class of the fibre pair that depends only on `o b`.

Over a compact base these fibre classes glue to a class of the Thom pair `(E, E₀)`
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`):
near each point the orientation reads as a constant orientation of `F` in the preferred
trivialization, so the local
classes over the trivializing sets obtained by pulling back `±g` agree on every fibre where two of
the sets meet, and the Mayer–Vietoris gluing over finite trivializing covers
(`TauCeti.exists_singularCohomology_thomPairOver_biUnion`) assembles them. When `g` generates
`Hʳ(F, F ∖ {0})` the glued class is a Thom class. In particular **every oriented real vector bundle
over a compact base has a Thom class with coefficients in any commutative ring**, integral
coefficients included (`TauCeti.VectorBundleOrientation.exists_isThomClass`). Without an
orientation the existence is established (`TauCeti.exists_isThomClass_of_compactSpace`) for
coefficient rings with a single unit, such as `ZMod 2`. For an oriented plane bundle the Euler
class of this Thom class (`TauCeti.eulerClass`) is the Euler class in `H²(B; ℤ)`.

A top-degree class over a compact base is determined by its fibre restrictions
(`TauCeti.singularCohomology_thomPair_ext_of_compactSpace`), so the prescribed restrictions give
uniqueness. The resulting named class `TauCeti.VectorBundleOrientation.thomClass o hι ω g`
is normalized by both `ω` and `g`; no preferred model-fibre generator is fixed here.

## Main results

* `TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`:
  over a compact base, there is a unique class of `Hʳ(E, E₀)` restricting on every fibre to the
  class read off from `g` along trivializations carrying the orientation of the fibre to `ω`,
  and to its negative along those carrying it to `-ω`.
* `TauCeti.VectorBundleOrientation.exists_isThomClass`: an oriented real vector bundle over a
  compact base has a Thom class with coefficients in any commutative ring.

* `TauCeti.VectorBundleOrientation.thomClass`: the normalized class, with fibre restrictions
  `singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq` and
  `singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg`.
  The theorem `eq_thomClass_of_forall` characterizes it.
* `TauCeti.VectorBundleOrientation.isThomClass_thomClass`: normalization by a generator gives a
  Thom class.
* In `Bundle.Trivialization`, the lemmas
  `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq`,
  `singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg` and
  `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg` describe
  the effect of equal or opposite orientation readings in every degree.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the Thom class of an oriented
  bundle, glued over a finite trivializing cover).
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Filter Module Set
open scoped Topology

universe w

namespace Bundle.Trivialization

open TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B}
  (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet)
  {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K} [Module.Projective K R']

variable {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  {o : Orientation ℝ (E b) ι}

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as the same
orientation of the model fibre pull back every class of `Hⁿ(F, F ∖ {0})` to the same class of the
fibre pair. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq
    (h : e'.mapOrientation ι hb' o = e.mapOrientation ι hb o) {n : ℕ}
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_iff_det_pos _ _ hι] at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : 0 < (e.coordChangeL ℝ e' b : F →L[ℝ] F).det := h
  rw [e.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul e' hb hb', sign_pos hd,
    SignType.coe_one, one_smul]

include hι in
/-- Two linear trivializations reading an orientation of the fibre over `b` as opposite
orientations of the model fibre pull back every class of `Hⁿ(F, F ∖ {0})` to opposite classes of
the fibre pair. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg
    (h : e'.mapOrientation ι hb' o = -e.mapOrientation ι hb o) {n : ℕ}
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g =
      -TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g := by
  rw [mapOrientation_eq_map_coordChangeL e e' hb hb', Orientation.map_eq_neg_iff_det_neg _ _ hι]
    at h
  -- `ContinuousLinearMap.det` is by definition the determinant of the underlying linear map.
  have hd : (e.coordChangeL ℝ e' b : F →L[ℝ] F).det < 0 := h
  rw [e.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul e' hb hb', sign_neg hd,
    SignType.coe_neg_one, neg_one_smul]

include hι in
/-- Pulling back `g` along a linear trivialization that reads an orientation of the fibre over `b`
as `ω`, or `-g` along one that reads it as `-ω`, gives a class of the fibre pair that does not
depend on the trivialization. -/
theorem singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg
    {ω : Orientation ℝ F ι} {n : ℕ}
    {g g₁ g₂ : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M' n}
    (h₁ : e.mapOrientation ι hb o = ω ∧ g₁ = g ∨ e.mapOrientation ι hb o = -ω ∧ g₁ = -g)
    (h₂ : e'.mapOrientation ι hb' o = ω ∧ g₂ = g ∨ e'.mapOrientation ι hb' o = -ω ∧ g₂ = -g) :
    TopPair.singularCohomologyMap (e'.continuousLinearEquivAt ℝ b hb').complZeroPairIso.hom n g₂ =
      TopPair.singularCohomologyMap
        (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom n g₁ := by
  rcases h₁ with ⟨h₁, rfl⟩ | ⟨h₁, rfl⟩ <;> rcases h₂ with ⟨h₂, rfl⟩ | ⟨h₂, rfl⟩
  · exact e.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e' hb hb' hι
      (h₂.trans h₁.symm) _
  · rw [map_neg, e.singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e' hb
      hb' hι (by rw [h₁, h₂]), neg_neg]
  · rw [map_neg, e.singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg e' hb
      hb' hι (by rw [h₁, h₂]; exact (neg_neg ω).symm)]
  · exact e.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq e' hb hb' hι
      (h₂.trans h₁.symm) _

end Bundle.Trivialization

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {ι : Type*} [Fintype ι] {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
  [Module.Projective K R']

open scoped Classical in
/-- The class of the fibre pair `(E_b, E_b ∖ {0})` read off from `g` along a linear trivialization
`e`, with the sign `+1` if `e` carries the orientation `x` of `E_b` to `ω` and `-1` otherwise. -/
private def orientedFiberClass (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F))
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (x : Orientation ℝ (E b) ι) :
    (TopPair.ofSubset (X := TopCat.of (E b)) ({0}ᶜ : Set (E b))).singularCohomology R' K M'
      (finrank ℝ F) :=
  if e.mapOrientation ι hb x = ω then
    TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g
  else -TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g

/-- The oriented fibre class does not depend on the trivialization, by the signed transition
lemma for equal or opposite orientation readings. -/
private theorem orientedFiberClass_eq (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F))
    (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) (x : Orientation ℝ (E b) ι) :
    orientedFiberClass ω g e' hb' x = orientedFiberClass ω g e hb x := by
  classical
  simp only [orientedFiberClass, ← map_neg, ← apply_ite]
  apply e.singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg
    (g := g) e' hb hb' hι
  all_goals
    split_ifs with h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr ⟨(Orientation.eq_or_eq_neg _ ω hι).resolve_left h, rfl⟩

variable [VectorBundle ℝ F E]

/-- **The fibre classes of an oriented bundle glue over a compact base.** Let `o` be an orientation
of a real vector bundle `E` over a compact base, with fibres of dimension `r = card ι`, `ω` an
orientation of the model fibre `F` and `g ∈ Hʳ(F, F ∖ {0}; R, M)`, with `R` projective. There is a
class of `Hʳ(E, E₀; R, M)` whose restriction to the fibre pair `(E_b, E_b ∖ {0})` is the pull-back
of `g` along every linear trivialization carrying the orientation `o b` of `E_b` to `ω`, and the
negative of that pull-back along every linear trivialization carrying `o b` to `-ω`. -/
private theorem exists_singularCohomology_thomPair_fiber [CompactSpace B]
    (hι : Fintype.card ι = finrank ℝ F) (o : VectorBundleOrientation F E ι) (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) :
    ∃ u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F),
      (∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        e.mapOrientation ι hb (o b) = ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
      ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        e.mapOrientation ι hb (o b) = -ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            -TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g := by
  classical
  let e (c : B) := trivializationAt F E c
  have hc (c : B) : c ∈ (e c).baseSet := mem_baseSet_trivializationAt F E c
  -- Near each point `c`, an open set inside the base set of `e c` on which `o` reads as the
  -- constant orientation `(e c).mapOrientation ι (hc c) (o c)` of `F`.
  have hW (c : B) : ∃ t : Set B, IsOpen t ∧ c ∈ t ∧ t ⊆ (e c).baseSet ∧
      ∀ x (hx : x ∈ (e c).baseSet), x ∈ t →
        (e c).mapOrientation ι hx (o x) = (e c).mapOrientation ι (hc c) (o c) := by
    obtain ⟨t, ht, hto, hct⟩ := eventually_nhds_iff.1
      ((o.eventually_mapOrientation_eq hι (e c) (hc c)).and
        ((e c).open_baseSet.mem_nhds (hc c)))
    exact ⟨t, hto, hct, fun x hx ↦ (ht x hx).2, fun x hx hxt ↦ (ht x hxt).1 hx⟩
  choose W hWo hcW hWe hWo' using hW
  -- Over `W c`, the local class pulled back from `±g`, the sign chosen by the reading at `c`.
  choose u hu using fun c ↦ (e c).exists_singularCohomology_thomPairOver_fiber ℝ (hWe c)
    (if (e c).mapOrientation ι (hc c) (o c) = ω then g else -g)
  -- On the fibre over `x ∈ W c`, the local class is the oriented fibre class of `o x`.
  have hux (c x : B) (hx : x ∈ W c) :
      TopPair.singularCohomologyMap (fiberThomPairOverMap F E hx) _ (u c) =
        orientedFiberClass ω g (e c) (hWe c hx) (o x) := by
    rw [hu c x hx, orientedFiberClass, hWo' c x (hWe c hx) hx]
    split_ifs <;> simp
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun b _ ↦ mem_iUnion.2 ⟨b, hcW b⟩
  obtain ⟨y, hy⟩ := exists_singularCohomology_thomPairOver_biUnion t (fun c _ ↦ hWo c)
    (fun c _ ↦ ⟨e c, inferInstance, hWe c⟩) u fun c _ c' _ b hbc hbc' ↦ by
      rw [hux c b hbc, hux c' b hbc', orientedFiberClass_eq hι ω g (e c) (e c')]
  let v := TopPair.singularCohomologyMap ((thomPairOverUnivIso F E).inv ≫ thomPairOverMap F E ht)
    _ y
  -- On every fibre, `v` restricts to the oriented fibre class.
  have hv (e' : Trivialization F (π F E)) [e'.IsLinear ℝ] (b : B) (hb : b ∈ e'.baseSet) :
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ v =
        orientedFiberClass ω g e' hb (o b) := by
    obtain ⟨c, hct, hbc⟩ := mem_iUnion₂.1 (ht (mem_univ b))
    -- The fibre over `b` factors through the Thom pair over the trivializing set `W c`.
    rw [← TopPair.singularCohomologyMap_comp_apply,
      fiberThomPairMap_comp_thomPairOverUnivIso_inv_comp_thomPairOverMap F E ht
        (Finset.subset_set_biUnion_of_mem (f := W) hct) hbc,
      TopPair.singularCohomologyMap_comp_apply,
      hy c hct, hux c b hbc, orientedFiberClass_eq hι ω g (e c) e']
  refine ⟨v, fun e' _ b hb h ↦ ?_, fun e' _ b hb h ↦ ?_⟩
  · simp [hv e' b hb, orientedFiberClass, h]
  · simp [hv e' b hb, orientedFiberClass, h, (Module.Ray.ne_neg_self ω).symm]

section CompactBase

variable [CompactSpace B]

/-- **The Thom class of an oriented vector bundle over a compact base.** Let `o` be an orientation
of the real vector bundle `E` of rank `r = card ι` over a compact base, `ω` an orientation of the
model fibre `F` and `g` a class of `Hʳ(F, F ∖ {0}; R, M)`, `R` projective. There is a unique class
`u ∈ Hʳ(E, E₀; R, M)` such that for every linear trivialization `e` and every point `b` of its base
set, the restriction of `u` to the fibre pair `(E_b, E_b ∖ {0})` is the pull-back of `g` along the
isomorphism `(E_b, E_b ∖ {0}) ≅ (F, F ∖ {0})` given by `e` if `e` reads `o b` as `ω`, and the
pull-back of `-g` if `e` reads `o b` as `-ω`. -/
theorem existsUnique_singularCohomology_thomPair_of_compactSpace
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
    [Module.Projective K R']
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) :
    ∃! u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F),
      ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        (e.mapOrientation ι hb (o b) = ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
        (e.mapOrientation ι hb (o b) = -ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            -TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) := by
  obtain ⟨u, hu₁, hu₂⟩ := exists_singularCohomology_thomPair_fiber hι o ω g
  refine ⟨u, fun e _ b hb ↦ ⟨hu₁ e b hb, hu₂ e b hb⟩, fun v hv ↦ ?_⟩
  refine singularCohomology_thomPair_ext_of_compactSpace fun b ↦ ?_
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι with h | h
  · rw [(hv e b hb).1 h, hu₁ e b hb h]
  · rw [(hv e b hb).2 h, hu₂ e b hb h]

section ThomClass

variable (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι) {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
  [Module.Projective K R']
  (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
    (finrank ℝ F))

/-- **The Thom class of an oriented vector bundle over a compact base**, normalized by an
orientation `ω` of the model fibre `F` and a class `g ∈ Hʳ(F, F ∖ {0}; R, M)`: the unique class of
`Hʳ(E, E₀; R, M)` whose restriction to the fibre pair over a point `b` of the base set of a linear
trivialization `e` is the pull-back of `g` along `e` if `e` reads `o b` as `ω`, and of `-g` if `e`
reads `o b` as `-ω`
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_of_compactSpace`). When
`g` generates `Hʳ(F, F ∖ {0}; K, K) ≅ K` it is a Thom class
(`TauCeti.VectorBundleOrientation.isThomClass_thomClass`). -/
def thomClass : (thomPair F E).singularCohomology R' K M' (finrank ℝ F) :=
  (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose

variable {hι ω g}

/-- Over a point where a linear trivialization `e` reads the orientation as `ω`, the restriction
of the Thom class `thomClass o hι ω g` to the fibre pair is the pull-back of `g` along `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hι ω g) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  ((o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec
    e b hb).1 h

/-- Over a point where a linear trivialization `e` reads the orientation as `-ω`, the restriction
of the Thom class `thomClass o hι ω g` to the fibre pair is the pull-back of `-g` along `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = -ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hι ω g) =
      -TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  ((o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec
    e b hb).2 h

/-- A class of `Hʳ(E, E₀; R, M)` whose fibre restrictions are those prescribed by `o`, `ω` and `g`
is the Thom class `thomClass o hι ω g`. -/
theorem eq_thomClass_of_forall {u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)}
    (hu : ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
      (e.mapOrientation ι hb (o b) = ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
      (e.mapOrientation ι hb (o b) = -ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          -TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g)) :
    u = o.thomClass hι ω g :=
  (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).unique hu
    (o.existsUnique_singularCohomology_thomPair_of_compactSpace hι ω g).exists.choose_spec

end ThomClass

/-- **The Thom class of an oriented bundle normalized by a generator is a Thom class**: if `g`
generates `Hʳ(F, F ∖ {0}; K, K) ≅ K`, then `thomClass o hι ω g` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K, K)` on every fibre. -/
theorem isThomClass_thomClass (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) : IsThomClass F E (o.thomClass hι ω g) := by
  refine isThomClass_iff.2 ⟨inferInstance, fun b ↦ ?_⟩
  let e := trivializationAt F E b
  have hb : b ∈ e.baseSet := mem_baseSet_trivializationAt F E b
  -- The pull-back of `g` along the isomorphism of fibre pairs given by `e` generates.
  have hge : Submodule.span K
      {TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (finrank ℝ F) g} = ⊤ := by
    let L := ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
      (finrank ℝ F)).mapIso (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.op).toLinearEquiv
    exact L.span_singleton_apply_eq_top_iff.2 hg
  rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι with h | h
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq e hb h]
    exact hge
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClass_of_mapOrientation_eq_neg e hb h,
      ← Set.neg_singleton, Submodule.span_neg]
    exact hge

end CompactBase

/-- **An oriented real vector bundle over a compact base has a Thom class** with coefficients in
any commutative ring `K`, in particular with integral coefficients: a class of
`Hʳ(E, E₀; K, K)`, `r = dim F`, restricting to a generator of `Hʳ(E_b, E_b ∖ {0}; K, K) ≅ K` on
every fibre. -/
theorem exists_isThomClass [CompactSpace B] (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (K : Type w) [CommRing K] :
    ∃ u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F),
      IsThomClass F E u := by
  classical
  -- A generator `g` of the local cohomology `Hʳ(F, F ∖ {0}; K) ≅ K`.
  obtain ⟨g, hg⟩ := exists_span_singularCohomology_complSingleton_eq_top (k := K)
    (OpenPartialHomeomorph.refl F) (mem_univ 0)
  -- An orientation of the model fibre, from a basis indexed by `ι`.
  let ω : Orientation ℝ F ι :=
    ((Module.finBasisOfFinrankEq ℝ F hι.symm).reindex (Fintype.equivFin ι).symm).orientation
  exact ⟨_, o.isThomClass_thomClass hι ω hg⟩

end TauCeti.VectorBundleOrientation
