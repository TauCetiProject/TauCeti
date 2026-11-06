/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Local.Orientation
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
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

These fibre classes glue to a class of the Thom pair `(E, E₀)` over an arbitrary base, and the
glued class is unique
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_fiber`): near each
point the orientation reads as a constant orientation of `F` in the preferred trivialization, so
the local classes over the trivializing sets obtained by pulling back `±g` agree on every fibre
where two of the sets meet, and the gluing over arbitrary trivializing covers
(`TauCeti.existsUnique_singularCohomology_thomPair_of_iUnion_eq_univ`) assembles them uniquely.
The glued class is `TauCeti.VectorBundleOrientation.thomClassOfModel`. When `g` generates
`Hʳ(F, F ∖ {0})` it is a Thom class, the Thom class compatible with `o`. In particular **every
oriented real vector bundle has a Thom class with coefficients in any commutative ring**, integral
coefficients included (`TauCeti.VectorBundleOrientation.exists_isThomClass`). Without an
orientation the existence and uniqueness are established
(`TauCeti.existsUnique_isThomClass_of_subsingleton_units`) for coefficient rings with a single
unit, such as `ZMod 2`. For an oriented plane bundle the Euler class of this Thom class
(`TauCeti.eulerClass`) is the Euler class in `H²(B; ℤ)`.

For a bundle of positive rank `n + 1` with integral coefficients, the generators of the fibre
pairs can be named directly: an orientation of `F` selects a generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)`
(`Orientation.localCohomologyClass`), and its pull-back along the isomorphism of fibre pairs given
by a linear trivialization does not depend on the trivialization
(`Orientation.singularCohomologyMap_localCohomologyClass_map_eq`). The *Thom class* of the oriented
bundle (`TauCeti.VectorBundleOrientation.thomClass`) is the class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)` restricting
to these generators on all fibres. It is characterized by its restrictions to the fibres
(`TauCeti.VectorBundleOrientation.eq_thomClass_iff`), it is a Thom class in the sense of
`TauCeti.IsThomClass` (`TauCeti.VectorBundleOrientation.isThomClass_thomClass`), and the opposite
orientation has the opposite Thom class (`TauCeti.VectorBundleOrientation.thomClass_neg`). It lives
in degree `n + 1`, the degree in which the fibre generators are indexed; `TauCeti.IsThomClass` is
stated in degree `finrank ℝ F`, so `isThomClass_thomClass` transports it along
`finrank ℝ F = n + 1`. Integral coefficients are `ULift ℤ`, as for the fibre generators.

## Main definitions

* `TauCeti.VectorBundleOrientation.thomClassOfModel`: the class normalized by an orientation `ω`
  of the model fibre and a class `g ∈ Hʳ(F, F ∖ {0})`.
* `TauCeti.VectorBundleOrientation.thomClass`: the integral Thom class of an oriented real vector
  bundle of positive rank.

## Main results

* In `Bundle.Trivialization`, the lemmas
  `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq`,
  `singularCohomologyMap_complZeroPairIso_hom_eq_neg_of_mapOrientation_eq_neg` and
  `singularCohomologyMap_complZeroPairIso_hom_eq_of_mapOrientation_eq_or_eq_neg` describe
  the effect of equal or opposite orientation readings in every degree.
* `TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_fiber`: there is a
  unique class of `Hʳ(E, E₀)` restricting on every fibre to the class read off from `g` along
  trivializations carrying the orientation of the fibre to `ω`, and to its negative along those
  carrying it to `-ω`.
* `TauCeti.VectorBundleOrientation.thomClassOfModel`: this class, with fibre restrictions
  `singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq` and
  `singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq_neg`;
  `eq_thomClassOfModel_of_forall` characterizes it, and `isThomClass_thomClassOfModel` shows that
  normalization by a generator gives a Thom class.
* `TauCeti.VectorBundleOrientation.exists_isThomClass`: an oriented real vector bundle has a Thom
  class with coefficients in any commutative ring.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_thomClass`: the integral
  Thom class restricts on each fibre to the generator selected by the fibre orientation, read in
  any linear trivialization.
* `TauCeti.VectorBundleOrientation.eq_thomClass_iff`: this property characterizes it.
* `TauCeti.VectorBundleOrientation.thomClass_neg`: reversing the orientation negates it.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_pullbackThomPairMap_thomClass`: it is
  natural under pullback of bundles.
* `TauCeti.VectorBundleOrientation.singularCohomologyMap_negThomPairMap_thomClass`: in odd rank,
  fibrewise negation carries it to the Thom class of the opposite orientation.
* `TauCeti.VectorBundleOrientation.isThomClass_thomClass`: it is a Thom class.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Lemma 10.3 and the proof of Theorem 10.4 (the Thom class of an oriented
  bundle, glued over finite trivializing covers and then over directed unions).
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

section ExistsThomClass

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

omit [Module.Projective K R'] in
/-- A class of `Hʳ(E, E₀)` restricts on every fibre to the class read off from `g` along
trivializations carrying the fibre orientation to `ω`, and to its negative along those carrying it
to `-ω`, exactly when it restricts to the oriented fibre class along every trivialization. -/
private theorem fiber_eq_and_fiber_eq_neg_iff (hι : Fintype.card ι = finrank ℝ F)
    (o : VectorBundleOrientation F E ι) (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F))
    (u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)) :
    ((∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        e.mapOrientation ι hb (o b) = ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
      ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        e.mapOrientation ι hb (o b) = -ω →
          TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
            -TopPair.singularCohomologyMap
              (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ↔
      ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          orientedFiberClass ω g e hb (o b) := by
  refine ⟨fun ⟨h₁, h₂⟩ e _ b hb ↦ ?_, fun h ↦ ⟨fun e _ b hb hω ↦ ?_, fun e _ b hb hω ↦ ?_⟩⟩
  · rcases Orientation.eq_or_eq_neg (e.mapOrientation ι hb (o b)) ω hι with hω | hω
    · simp [orientedFiberClass, hω, h₁ e b hb hω]
    · simp [orientedFiberClass, hω, h₂ e b hb hω, (Module.Ray.ne_neg_self ω).symm]
  · simp [h e b hb, orientedFiberClass, hω]
  · simp [h e b hb, orientedFiberClass, hω, (Module.Ray.ne_neg_self ω).symm]

/-- **The fibre classes of an oriented bundle glue uniquely.** Let `o` be an orientation of a real
vector bundle `E`, with fibres of dimension `r = card ι`, `ω` an orientation of the model fibre `F`
and `g ∈ Hʳ(F, F ∖ {0}; R, M)`, with `R` projective. There is a unique class of `Hʳ(E, E₀; R, M)`
whose restriction to the fibre pair `(E_b, E_b ∖ {0})` is the pull-back of `g` along every linear
trivialization carrying the orientation `o b` of `E_b` to `ω`, and the negative of that pull-back
along every linear trivialization carrying `o b` to `-ω`. The base is arbitrary. -/
theorem existsUnique_singularCohomology_thomPair_fiber
    (hι : Fintype.card ι = finrank ℝ F) (o : VectorBundleOrientation F E ι) (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F)) :
    ∃! u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F),
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
  -- The local classes agree on overlaps, so they glue to a unique class over the whole base.
  obtain ⟨v, hv, -⟩ := existsUnique_singularCohomology_thomPair_of_iUnion_eq_univ W R' M'
    (iUnion_eq_univ_iff.2 fun c ↦ ⟨c, hcW c⟩) hWo (fun c ↦ ⟨e c, inferInstance, hWe c⟩) u
    fun c c' b hbc hbc' ↦ by
      rw [hux c b hbc, hux c' b hbc', orientedFiberClass_eq hι ω g (e c) (e c')]
  have hv' (e' : Trivialization F (π F E)) [e'.IsLinear ℝ] (b : B) (hb : b ∈ e'.baseSet) :
      TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ v =
        orientedFiberClass ω g e' hb (o b) := by
    rw [hv b b (hcW b), hux b b (hcW b), orientedFiberClass_eq hι ω g (e b) e']
  refine ⟨v, (fiber_eq_and_fiber_eq_neg_iff hι o ω g v).2 hv', fun w hw ↦
    singularCohomology_thomPair_ext fun b ↦ ?_⟩
  rw [(fiber_eq_and_fiber_eq_neg_iff hι o ω g w).1 hw (e b) b (hc b), hv' (e b) b (hc b)]

section ThomClass

variable (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
  (ω : Orientation ℝ F ι) {K : Type*} [CommRing K] {R' M' : ModuleCat.{w} K}
  [Module.Projective K R']
  (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
    (finrank ℝ F))

/-- **The Thom class of an oriented vector bundle**, normalized by an
orientation `ω` of the model fibre `F` and a class `g ∈ Hʳ(F, F ∖ {0}; R, M)`: the unique class of
`Hʳ(E, E₀; R, M)` whose restriction to the fibre pair over a point `b` of the base set of a linear
trivialization `e` is the pull-back of `g` along `e` if `e` reads `o b` as `ω`, and of `-g` if `e`
reads `o b` as `-ω`
(`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_fiber`). When
`g` generates `Hʳ(F, F ∖ {0}; K, K) ≅ K` it is a Thom class
(`TauCeti.VectorBundleOrientation.isThomClass_thomClassOfModel`). -/
def thomClassOfModel : (thomPair F E).singularCohomology R' K M' (finrank ℝ F) :=
  (existsUnique_singularCohomology_thomPair_fiber hι o ω g).exists.choose

variable {hι ω g}

/-- Over a point where a linear trivialization `e` reads the orientation as `ω`, the restriction
of the Thom class `thomClassOfModel o hι ω g` to the fibre pair is the pull-back of `g` along
  `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClassOfModel hι ω g) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  (existsUnique_singularCohomology_thomPair_fiber hι o ω g).exists.choose_spec.1 e b hb h

/-- Over a point where a linear trivialization `e` reads the orientation as `-ω`, the restriction
of the Thom class `thomClassOfModel o hι ω g` to the fibre pair is the pull-back of `-g` along
  `e`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq_neg
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (h : e.mapOrientation ι hb (o b) = -ω) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClassOfModel hι ω g) =
      -TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g :=
  (existsUnique_singularCohomology_thomPair_fiber hι o ω g).exists.choose_spec.2 e b hb h

/-- A class of `Hʳ(E, E₀; R, M)` whose fibre restrictions are those prescribed by `o`, `ω` and `g`
is the Thom class `thomClassOfModel o hι ω g`. -/
theorem eq_thomClassOfModel_of_forall {u : (thomPair F E).singularCohomology R' K M' (finrank ℝ F)}
    (hu : ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B) (hb : b ∈ e.baseSet),
      (e.mapOrientation ι hb (o b) = ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g) ∧
      (e.mapOrientation ι hb (o b) = -ω →
        TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
          -TopPair.singularCohomologyMap
            (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom _ g)) :
    u = o.thomClassOfModel hι ω g :=
  (existsUnique_singularCohomology_thomPair_fiber hι o ω g).unique
    ⟨fun e _ b hb h ↦ (hu e b hb).1 h, fun e _ b hb h ↦ (hu e b hb).2 h⟩
    (existsUnique_singularCohomology_thomPair_fiber hι o ω g).exists.choose_spec

end ThomClass

/-- **The Thom class of an oriented bundle normalized by a generator is a Thom class**: if `g`
generates `Hʳ(F, F ∖ {0}; K, K) ≅ K`, then `thomClassOfModel o hι ω g` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K, K)` on every fibre. -/
theorem isThomClass_thomClassOfModel (o : VectorBundleOrientation F E ι)
    (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι) {K : Type w} [CommRing K]
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) : IsThomClass F E (o.thomClassOfModel hι ω g) := by
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
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq e hb h]
    exact hge
  · rw [o.singularCohomologyMap_fiberThomPairMap_thomClassOfModel_of_mapOrientation_eq_neg e hb h,
      ← Set.neg_singleton, Submodule.span_neg]
    exact hge

/-- **An oriented real vector bundle has a Thom class** with coefficients in any commutative ring
`K`, in particular with integral coefficients: a class of `Hʳ(E, E₀; K, K)`, `r = dim F`,
restricting to a generator of `Hʳ(E_b, E_b ∖ {0}; K, K) ≅ K` on every fibre. The base is arbitrary.
The class compatible with the orientation is unique by
`TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_fiber`. -/
theorem exists_isThomClass (hι : Fintype.card ι = finrank ℝ F)
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
  exact ⟨_, o.isThomClass_thomClassOfModel hι ω hg⟩

end ExistsThomClass

section ThomClass

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)

/-- A class of `Hⁿ⁺¹(E, E₀; ℤ)` restricting on every fibre to the generator selected by the fibre
orientation, read in the trivialization at that point. -/
private theorem exists_thomClass :
    ∃ x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1),
      ∀ b, TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ x =
        TopPair.singularCohomologyMap ((trivializationAt F E b).continuousLinearEquivAt ℝ b
          (FiberBundle.mem_baseSet_trivializationAt' b)).complZeroPairIso.hom (n + 1)
          (((trivializationAt F E b).mapOrientation (Fin (n + 1))
            (FiberBundle.mem_baseSet_trivializationAt' b) (o b)).localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  refine (hF ▸ exists_singularCohomology_thomPair_fiber (F := F) (E := E)
    (R := ModuleCat.of ℤ (ULift.{w} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{w} ℤ))) _
    fun c ↦ ?_
  -- Near `c` the fibre orientations read in the trivialization `e` at `c` are a single
  -- orientation `ω` of `F`; pull back the generator it selects along `e`.
  let e := trivializationAt F E c
  have hc : c ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' c
  obtain ⟨t, ht, hto, hct⟩ := eventually_nhds_iff.1 (o.eventually_mapOrientation_eq' c)
  obtain ⟨u, hu⟩ := e.exists_singularCohomology_thomPairOver_fiber ℝ (W := t ∩ e.baseSet)
    inter_subset_right ((e.mapOrientation (Fin (n + 1)) hc (o c)).localCohomologyClass hF)
  refine ⟨t ∩ e.baseSet, hto.inter e.open_baseSet, ⟨hct, hc⟩,
    ⟨e, inferInstance, inter_subset_right⟩, u, fun b hb ↦ ?_⟩
  have hω : e.mapOrientation (Fin (n + 1)) hb.2 (o b) = e.mapOrientation (Fin (n + 1)) hc (o c) :=
    ht b hb.1 hb.2
  rw [hu b hb, ← hω, Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply]
  exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq (o b) _ _ hF

/-- **The integral Thom class of an oriented vector bundle.** For an orientation `o` of a real
vector bundle `E` over an arbitrary base, with model fibre `F` of dimension `n + 1`, this is the
class `U ∈ Hⁿ⁺¹(E, E₀; ℤ)` whose restriction to the fibre pair `(E_b, E_b ∖ {0})` over every
point `b` is the generator of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` selected by the orientation `o b`: the
pull-back, along any linear trivialization at `b`, of the generator of `Hⁿ⁺¹(F, F ∖ {0}; ℤ)`
selected by `o b` read in that trivialization
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_fiberThomPairMap_thomClass`). This
property determines it (`TauCeti.VectorBundleOrientation.eq_thomClass_iff`). -/
def thomClass :
    (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1) :=
  (exists_thomClass o hF).choose

/-- The Thom class of an oriented bundle restricts on the fibre pair over every point `b` to the
generator of `Hⁿ⁺¹(E_b, E_b ∖ {0}; ℤ)` selected by the orientation of `E_b`, read in any linear
trivialization `e` at `b`. -/
theorem singularCohomologyMap_fiberThomPairMap_thomClass (e : Trivialization F (π F E))
    [e.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet) :
    TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ (o.thomClass hF) =
      TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
        (n + 1) ((e.mapOrientation (Fin (n + 1)) hb (o b)).localCohomologyClass hF) :=
  ((exists_thomClass o hF).choose_spec b).trans <| by
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply]
    exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq (o b) _ _ hF

/-- **Uniqueness of the Thom class.** A class of `Hⁿ⁺¹(E, E₀; ℤ)` is the Thom class of the oriented
bundle exactly when it restricts on every fibre to the generator selected by the fibre
orientation, read in a linear trivialization at that point. -/
theorem eq_thomClass_iff
    (u : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)) :
    u = o.thomClass hF ↔ ∀ (e : Trivialization F (π F E)) [e.IsLinear ℝ] (b : B)
      (hb : b ∈ e.baseSet), TopPair.singularCohomologyMap (fiberThomPairMap F E b) _ u =
        TopPair.singularCohomologyMap (e.continuousLinearEquivAt ℝ b hb).complZeroPairIso.hom
          (n + 1) ((e.mapOrientation (Fin (n + 1)) hb (o b)).localCohomologyClass hF) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  refine ⟨fun h e _ b hb ↦ h ▸ o.singularCohomologyMap_fiberThomPairMap_thomClass hF e hb,
    fun h ↦ (hF ▸ fun u v ↦ singularCohomology_thomPair_ext (F := F) (E := E)
      (R := ModuleCat.of ℤ (ULift.{w} ℤ)) (k := ℤ) (M := ModuleCat.of ℤ (ULift.{w} ℤ)) (x := u)
      (y := v)) u _ fun b ↦ ?_⟩
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [h _ b hb, o.singularCohomologyMap_fiberThomPairMap_thomClass hF _ hb]

/-- Reversing the orientation negates the Thom class. -/
@[simp]
theorem thomClass_neg : (-o).thomClass hF = -o.thomClass hF := by
  symm
  refine (eq_thomClass_iff (-o) hF _).2 fun e _ b hb ↦ ?_
  rw [map_neg, o.singularCohomologyMap_fiberThomPairMap_thomClass hF e hb, neg_apply,
    Trivialization.mapOrientation_neg, Orientation.localCohomologyClass_neg, map_neg]

/-- **Naturality of the Thom class.** Pulling the Thom class of an oriented bundle `E` back along
the map of Thom pairs `(f*E, (f*E)₀) ⟶ (E, E₀)` covering a continuous map `f : B' → B` gives the
Thom class of the pulled-back orientation of `f*E`. -/
theorem singularCohomologyMap_pullbackThomPairMap_thomClass {B' : Type w} [TopologicalSpace B']
    (f : C(B', B)) :
    TopPair.singularCohomologyMap (pullbackThomPairMap F E f) (n + 1) (o.thomClass hF) =
      (o.pullback f).thomClass hF := by
  refine ((eq_thomClass_iff (o.pullback f) hF _).2 fun e _ b' hb' ↦ ?_)
  -- Restricted to the fibre over `b'`, the pulled-back class is the Thom class of `E` on the fibre
  -- over `f b'`, read in the preferred trivialization at `f b'`; the reading does not depend on
  -- the trivialization.
  -- Term-mode steps: the zero of the fibres of `f*E` enters the Thom pair of `f*E` through
  -- `pullbackThomPairMap` and through the vector bundle structure of `f*E` as two instances that
  -- agree only up to unfolding, so `rw` cannot match the composite.
  refine (TopPair.singularCohomologyMap_comp_apply _ _ _ _).symm.trans <|
    (congrArg (fun φ ↦ TopPair.singularCohomologyMap φ (n + 1) (o.thomClass hF))
      (fiberThomPairMap_comp_pullbackThomPairMap F E f b')).trans ?_
  refine (o.singularCohomologyMap_fiberThomPairMap_thomClass hF (trivializationAt F E (f b'))
    (FiberBundle.mem_baseSet_trivializationAt' (f b'))).trans ?_
  rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply, pullback_apply]
  exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq (o (f b')) _ _ hF

/-- **Fibrewise negation in odd rank reverses the Thom class.** For an oriented bundle of odd rank
`n + 1`, pulling the Thom class back along `v ↦ -v` gives the Thom class of the opposite
orientation. -/
theorem singularCohomologyMap_negThomPairMap_thomClass (hn : Even n) :
    TopPair.singularCohomologyMap (negThomPairMap F E) (n + 1) (o.thomClass hF) =
      (-o).thomClass hF := by
  refine ((eq_thomClass_iff (-o) hF _).2 fun e _ b hb ↦ ?_)
  let t := e.continuousLinearEquivAt ℝ b hb
  -- On the fibre over `b`, negation is `t⁻¹ ∘ (x ↦ -x) ∘ t`.
  have hφ : fiberThomPairMap F E b ≫ negThomPairMap F E =
      t.complZeroPairIso.hom ≫ (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom ≫
        t.complZeroPairIso.inv ≫ fiberThomPairMap F E b := by
    refine TopPair.hom_ext_of_fst _ (TopCat.ext fun (x : E b) ↦ ?_)
    have h₁ : TopPair.Hom.fst t.complZeroPairIso.inv
        (TopPair.Hom.fst (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom
          (TopPair.Hom.fst t.complZeroPairIso.hom x)) = (-1 : ℝ) • x := by
      have h : t.symm (-t x) = (-1 : ℝ) • x := by
        simpa using t.symm_apply_apply ((-1 : ℝ) • x)
      simp only [ContinuousLinearEquiv.complZeroPairIso_hom_fst_apply,
        ContinuousLinearEquiv.complZeroPairIso_inv_fst_apply, ContinuousLinearEquiv.neg_apply]
      exact h
    -- The ambient map of a composite of maps of pairs is the composite of the ambient maps. After
    -- `TopPair.Hom.fst_comp`, `ConcreteCategory.comp_apply` and `ContinuousMap.comp_apply` do not
    -- fire: the intermediate objects are `TopPair.ofSubset` carriers that agree with the types of
    -- the composed maps only after unfolding. So `change` states the iterated applications.
    change TopPair.Hom.fst (negThomPairMap F E) (TopPair.Hom.fst (fiberThomPairMap F E b) x) =
      TopPair.Hom.fst (fiberThomPairMap F E b) (TopPair.Hom.fst t.complZeroPairIso.inv
        (TopPair.Hom.fst (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom
          (TopPair.Hom.fst t.complZeroPairIso.hom x)))
    rw [h₁]
    exact (congrArg _ (fiberThomPairMap_fst_apply F E b x)).trans
      ((negThomPairMap_fst_apply F E _).trans (fiberThomPairMap_fst_apply F E b _).symm)
  rw [← TopPair.singularCohomologyMap_comp_apply, hφ]
  simp only [TopPair.singularCohomologyMap_comp_apply]
  -- Restriction: on the fibre over `b`, the Thom class is the generator selected through `t`.
  rw [o.singularCohomologyMap_fiberThomPairMap_thomClass hF e hb]
  -- The inverse of `t` cancels against `t`.
  rw [← TopPair.singularCohomologyMap_comp_apply t.complZeroPairIso.inv, Iso.inv_hom_id,
    TopPair.singularCohomologyMap_id, ModuleCat.id_apply]
  -- Antipodal action: `x ↦ -x` acts by the sign of `det (-1) = (-1) ^ (n + 1) = -1`.
  have hdet : ((ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) : F →L[ℝ] F).det = -1 := by
    have hneg : (((ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) : F →L[ℝ] F) : F →ₗ[ℝ] F) =
        (-1 : ℝ) • LinearMap.id := by
      ext; simp
    rw [ContinuousLinearMap.det, hneg, LinearMap.det_smul, LinearMap.det_id, mul_one, hF,
      hn.add_one.neg_one_pow]
  have : FiniteDimensional ℝ F := .of_finrank_eq_succ hF
  have hf : Set.MapsTo ((ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) : F →L[ℝ] F) ({0}ᶜ : Set F)
      {0}ᶜ :=
    (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).mapsTo_compl_zero
  have hneg : (ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F).complZeroPairIso.hom =
      TopPair.ofSubsetMap
        (TopCat.ofHom (((ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) : F →L[ℝ] F) : C(F, F))) hf :=
    ContinuousLinearEquiv.complZeroPairIso_hom _
  -- The determinant-sign action, stated with the `ℤ`-linear structure used by the Thom class.
  have hact : TopPair.singularCohomologyMap (R := ModuleCat.of ℤ (ULift.{w} ℤ)) (k := ℤ)
      (M := ModuleCat.of ℤ (ULift.{w} ℤ))
      (TopPair.ofSubsetMap
        (TopCat.ofHom (((ContinuousLinearEquiv.neg ℝ : F ≃L[ℝ] F) : F →L[ℝ] F) : C(F, F))) hf)
      (n + 1) = -𝟙 _ := by
    refine (singularCohomologyMap_continuousLinearMap_compl_zero
      (ModuleCat.of ℤ (ULift.{w} ℤ)) (ModuleCat.of ℤ (ULift.{w} ℤ)) _ hf (n + 1)).trans ?_
    simp [hdet]
    -- The two sides differ only in the `ℤ`-linear structure on the hom groups used to negate.
    rfl
  rw [hneg, hact]
  -- Sign cleanup: the generator selected by the opposite orientation is the negative one.
  simp [t, Trivialization.mapOrientation_neg, Orientation.localCohomologyClass_neg]

/-- **The Thom class of an oriented bundle is a Thom class**: transported to the degree
`finrank ℝ F = n + 1`, it restricts to a generator of the integral cohomology of every fibre
pair. -/
theorem isThomClass_thomClass :
    IsThomClass F E (hF ▸ o.thomClass hF :
      (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
  have := FiniteDimensional.of_finrank_eq_succ hF
  -- Transport along `finrank ℝ F = d` commutes with the fibre restrictions.
  have key {d : ℕ} (hd : finrank ℝ F = d)
      (x : (thomPair F E).singularCohomology (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
        (ModuleCat.of ℤ (ULift.{w} ℤ)) d)
      (hx : ∀ b, Submodule.span ℤ
        {(TopPair.singularCohomologyMap (fiberThomPairMap F E b) d x)} = ⊤) :
      IsThomClass F E (hd ▸ x : (thomPair F E).singularCohomology
        (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ (ModuleCat.of ℤ (ULift.{w} ℤ)) (finrank ℝ F)) := by
    subst hd
    exact isThomClass_iff.2 ⟨inferInstance, hx⟩
  refine key hF _ fun b ↦ ?_
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) b
  rw [o.singularCohomologyMap_fiberThomPairMap_thomClass hF _ hb]
  -- An isomorphism of pairs induces a linear isomorphism in cohomology, carrying generators to
  -- generators.
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of ℤ (ULift.{w} ℤ)) ℤ
    (ModuleCat.of ℤ (ULift.{w} ℤ)) (n + 1)).mapIso
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (Orientation.span_localCohomologyClass _ _)

end ThomClass

end TauCeti.VectorBundleOrientation
