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
(`TauCeti.VectorBundleOrientation.exists_singularCohomology_thomPair_fiber`): near each point the
orientation reads as a constant orientation of `F` in the preferred trivialization, so the local
classes over the trivializing sets obtained by pulling back `±g` agree on every fibre where two of
the sets meet, and the Mayer–Vietoris gluing over finite trivializing covers
(`TauCeti.exists_singularCohomology_thomPairOver_biUnion`) assembles them. When `g` generates
`Hʳ(F, F ∖ {0})` the glued class is a Thom class. In particular **every oriented real vector bundle
over a compact base has a Thom class with coefficients in any commutative ring**, integral
coefficients included (`TauCeti.VectorBundleOrientation.exists_isThomClass`). Without an
orientation the existence is established (`TauCeti.exists_isThomClass_of_compactSpace`) for
coefficient rings with a single unit, such as `ZMod 2`. For an oriented plane bundle the Euler
class of this Thom class (`TauCeti.eulerClass`) is the Euler class in `H²(B; ℤ)`.

## Main results

* `TauCeti.VectorBundleOrientation.exists_singularCohomology_thomPair_fiber`: over a compact base,
  there is a class of `Hʳ(E, E₀)` restricting on every fibre to the class read off from `g` along
  trivializations carrying the orientation of the fibre to `ω`, and to its negative along those
  carrying it to `-ω`.
* `TauCeti.VectorBundleOrientation.exists_isThomClass`: an oriented real vector bundle over a
  compact base has a Thom class with coefficients in any commutative ring.

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

/-- **The fibre classes of an oriented bundle glue over a compact base.** Let `o` be an orientation
of a real vector bundle `E` over a compact base, with fibres of dimension `r = card ι`, `ω` an
orientation of the model fibre `F` and `g ∈ Hʳ(F, F ∖ {0}; R, M)`, with `R` projective. There is a
class of `Hʳ(E, E₀; R, M)` whose restriction to the fibre pair `(E_b, E_b ∖ {0})` is the pull-back
of `g` along every linear trivialization carrying the orientation `o b` of `E_b` to `ω`, and the
negative of that pull-back along every linear trivialization carrying `o b` to `-ω`. -/
theorem exists_singularCohomology_thomPair_fiber [CompactSpace B]
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
    have hfib : fiberThomPairMap F E b ≫ (thomPairOverUnivIso F E).inv ≫ thomPairOverMap F E ht =
        fiberThomPairOverMap F E hbc ≫
          thomPairOverMap F E (Finset.subset_set_biUnion_of_mem (f := W) hct) := by
      rw [← fiberThomPairOverMap_comp_thomPairOverUnivIso_hom, Category.assoc,
        Iso.hom_inv_id_assoc, fiberThomPairOverMap_comp_thomPairOverMap,
        fiberThomPairOverMap_comp_thomPairOverMap]
    rw [← TopPair.singularCohomologyMap_comp_apply, hfib, TopPair.singularCohomologyMap_comp_apply,
      hy c hct, hux c b hbc, orientedFiberClass_eq hι ω g (e c) e']
  refine ⟨v, fun e' _ b hb h ↦ ?_, fun e' _ b hb h ↦ ?_⟩
  · simp [hv e' b hb, orientedFiberClass, h]
  · simp [hv e' b hb, orientedFiberClass, h, (Module.Ray.ne_neg_self ω).symm]

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
  obtain ⟨u, hu₁, hu₂⟩ := exists_singularCohomology_thomPair_fiber hι o ω g
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
