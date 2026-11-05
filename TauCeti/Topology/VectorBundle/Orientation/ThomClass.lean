/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
When `g` generates `Hʳ(F, F ∖ {0})` the glued class is a Thom class, the Thom class compatible
with `o`. In particular **every oriented real vector bundle has a Thom class with coefficients in
any commutative ring**, integral coefficients included
(`TauCeti.VectorBundleOrientation.exists_isThomClass`). Without an orientation the existence and
uniqueness are established (`TauCeti.existsUnique_isThomClass_of_subsingleton_units`) for
coefficient rings with a single unit, such as `ZMod 2`. For an oriented plane bundle the Euler
class of this Thom class (`TauCeti.eulerClass`) is the Euler class in `H²(B; ℤ)`.

## Main results

* `TauCeti.VectorBundleOrientation.existsUnique_singularCohomology_thomPair_fiber`: there is a
  unique class of `Hʳ(E, E₀)` restricting on every fibre to the class read off from `g` along
  trivializations carrying the orientation of the fibre to `ω`, and to its negative along those
  carrying it to `-ω`.
* `TauCeti.VectorBundleOrientation.exists_isThomClass`: an oriented real vector bundle has a Thom
  class with coefficients in any commutative ring.

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

/-- The oriented fibre class does not depend on the trivialization: by
`Bundle.Trivialization.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`, changing the
trivialization multiplies the unsigned class by the sign of the determinant of the coordinate
change, which is also the sign relating the two readings of `x`. -/
private theorem orientedFiberClass_eq (hι : Fintype.card ι = finrank ℝ F) (ω : Orientation ℝ F ι)
    (g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
      (finrank ℝ F))
    (e e' : Trivialization F (π F E)) [e.IsLinear ℝ] [e'.IsLinear ℝ] {b : B} (hb : b ∈ e.baseSet)
    (hb' : b ∈ e'.baseSet) (x : Orientation ℝ (E b) ι) :
    orientedFiberClass ω g e' hb' x = orientedFiberClass ω g e hb x := by
  have hx := e.mapOrientation_eq_map_coordChangeL e' hb hb' x
  have hdet : LinearMap.det ((e.coordChangeL ℝ e' b).toLinearEquiv : F →ₗ[ℝ] F) ≠ 0 :=
    (LinearEquiv.isUnit_det' _).ne_zero
  have hω := Orientation.eq_or_eq_neg (e.mapOrientation ι hb x) ω hι
  unfold orientedFiberClass
  rw [e.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul e' hb hb', hx]
  rcases hdet.lt_or_gt with hneg | hpos
  · -- An orientation-reversing coordinate change negates both the class and the reading of `x`.
    have hsign : SignType.sign (e.coordChangeL ℝ e' b : F →L[ℝ] F).det = -1 := sign_neg hneg
    rw [(Orientation.map_eq_neg_iff_det_neg _ _ hι).2 hneg, hsign]
    rcases hω with h | h <;> simp [h, (Module.Ray.ne_neg_self ω).symm]
  · -- An orientation-preserving coordinate change fixes both.
    have hsign : SignType.sign (e.coordChangeL ℝ e' b : F →L[ℝ] F).det = 1 := sign_pos hpos
    rw [(Orientation.map_eq_iff_det_pos _ _ hι).2 hpos, hsign]
    simp

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
  obtain ⟨u, ⟨hu₁, hu₂⟩, -⟩ := existsUnique_singularCohomology_thomPair_fiber hι o ω g
  refine ⟨u, isThomClass_iff.2 ⟨inferInstance, fun b ↦ ?_⟩⟩
  have hb := mem_baseSet_trivializationAt F E b
  -- The pull-back along an isomorphism of pairs of a generator generates.
  let φ := (TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      ((trivializationAt F E b).continuousLinearEquivAt ℝ b hb).complZeroPairIso.op
  have hgen : Submodule.span K {φ.toLinearEquiv g} = ⊤ :=
    φ.toLinearEquiv.span_singleton_apply_eq_top_iff.2 hg
  rcases Orientation.eq_or_eq_neg ((trivializationAt F E b).mapOrientation ι hb (o b)) ω hι
    with h | h
  · rwa [hu₁ _ b hb h]
  · rwa [hu₂ _ b hb h, ← Set.neg_singleton, Submodule.span_neg]

end TauCeti.VectorBundleOrientation
