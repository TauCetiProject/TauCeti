/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Comap
public import TauCeti.Topology.VectorBundle.Orientation.EulerClass
public import TauCeti.Topology.VectorBundle.Thom.FiberwiseEquiv

/-!
# Thom and Euler classes of isomorphic oriented bundles

Let `E' → B'` and `E → B` be real vector bundles of rank `n + 1`, with model fibres `F'` and `F`
and orientations `o'` and `o`, and let `φ b' : E'_{b'} ≃ E_{g b'}` be a fibrewise isomorphism over a
continuous map `g : B' → B` (with continuous total-space map). If `φ` is orientation preserving,
that is, `φ b'` carries `o' b'` to `o (g b')` for every `b'`, then the map of Thom pairs
`(E', E'₀) ⟶ (E, E₀)` of `φ` (`TauCeti.thomPairMapOfFiberwise`) pulls the integral Thom class of
`(E, o)` back to the Thom class of `(E', o')`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass`), and the
Euler class of `(E', o')` is the pull-back along `g` of the Euler class of `(E, o)`
(`TauCeti.VectorBundleOrientation.eulerClass_eq_singularCohomologyMap_of_fiberwise`). If `φ` is
orientation reversing, carrying every `o' b'` to `-o (g b')`, both acquire a sign.

Over the identity of the base this says that **isomorphic oriented bundles have the same Euler
class** (`TauCeti.VectorBundleOrientation.eulerClass_eq_of_fiberwise`), and the opposite one when
the isomorphism reverses the orientations
(`TauCeti.VectorBundleOrientation.eulerClass_eq_neg_of_fiberwise`).

Every fibrewise isomorphism `φ` is orientation preserving for the orientation `φ^* o` of `E'`
transported from `o` (`TauCeti.VectorBundleOrientation.comap`), so with that orientation the
statements need no hypothesis on `φ`: the map of Thom pairs of `φ` pulls the Thom class of `(E, o)`
back to that of `(E', φ^* o)`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClass_comap`),
and `e(E', φ^* o) = g^* e(E, o)` (`TauCeti.VectorBundleOrientation.eulerClass_comap`), which over
the identity of the base reads `e(E', φ^* o) = e(E, o)`
(`TauCeti.VectorBundleOrientation.eulerClass_comap_id`).

The proof compares fibre restrictions: on the fibre over `b'` the pulled-back class is the
generator selected by `o (g b')`, pulled back along `φ b'` followed by a linear trivialization at
`g b'`, and the generator selected by an orientation does not depend on the linear isomorphism with
the model fibre used to read it (`Orientation.singularCohomologyMap_localCohomologyClass_map_eq`).
The characterization `TauCeti.VectorBundleOrientation.eq_thomClass_iff` then identifies it with the
Thom class of `o'`.

The same holds, in every rank and with arbitrary coefficients, for the Thom class
`TauCeti.VectorBundleOrientation.thomClassOfModel` normalized by an orientation `ω` and a class
`c ∈ Hʳ(F, F ∖ {0})` of the common model fibre `F` of `E` and `E'`: an orientation-preserving `φ`
pulls the class of `o` back to the class of `o'`
(`TauCeti.VectorBundleOrientation.singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel`),
and an orientation-reversing one to its negative (in the same namespace,
`singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel_of_map_eq_neg`).
Here the fibre over `b'` is read along `φ b'` followed by a trivialization of `E` at `g b'`, which
differs from a trivialization of `E'` at `b'` by an automorphism of `F` acting on `c` by the sign of
its determinant
(`ContinuousLinearEquiv.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9, Property 9.1 (naturality of the Euler class under orientation-preserving
  bundle maps) and Property 9.4 (orientation reversal).
-/

public section

noncomputable section

open Bundle CategoryTheory Module

universe w

namespace TauCeti.VectorBundleOrientation

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {n : ℕ} (o : VectorBundleOrientation F E (Fin (n + 1))) (hF : finrank ℝ F = n + 1)

section BaseMap

variable {B' : Type w} [TopologicalSpace B'] {F' : Type w} [NormedAddCommGroup F']
  [NormedSpace ℝ F'] {E' : B' → Type w} [TopologicalSpace (TotalSpace F' E')]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)]
  [FiberBundle F' E'] [VectorBundle ℝ F' E']
  (o' : VectorBundleOrientation F' E' (Fin (n + 1))) (hF' : finrank ℝ F' = n + 1) {g : C(B', B)}
  {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))

include hφ

/-- **Naturality of the Thom class under orientation-preserving bundle maps.** For a fibrewise
isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `o (g b')` for
every `b'`, the map of Thom pairs of `φ` pulls the Thom class of `(E, o)` back to the Thom class of
`(E', o')`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_thomClass
    (ho : ∀ b', Orientation.map (Fin (n + 1)) (φ b').toLinearEquiv (o' b') = o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) (n + 1) (o.thomClass hF) =
      o'.thomClass hF' := by
  refine (eq_thomClass_iff o' hF' _).2 fun e' _ b' hb' ↦ ?_
  -- On the fibre over `b'`, the pulled-back class is the generator selected by `o (g b')`, pulled
  -- back along `φ b'` followed by the preferred trivialization at `g b'`.
  have hb := FiberBundle.mem_baseSet_trivializationAt' (F := F) (E := E) (g b')
  rw [← TopPair.singularCohomologyMap_comp_apply, fiberThomPairMap_comp_thomPairMapOfFiberwise,
    TopPair.singularCohomologyMap_comp_apply,
    o.singularCohomologyMap_fiberThomPairMap_thomClass hF _ hb,
    ← TopPair.singularCohomologyMap_comp_apply, ← Iso.trans_hom,
    ← ContinuousLinearEquiv.complZeroPairIso_trans, Trivialization.mapOrientation_apply,
    Trivialization.mapOrientation_apply, ← ho, ← Orientation.map_trans]
  -- The generator selected by `o' b'` does not depend on the linear isomorphism `E'_{b'} ≃ F`
  -- used to read it.
  exact Orientation.singularCohomologyMap_localCohomologyClass_map_eq (o' b') _ _ hF hF'

/-- **Orientation-reversing bundle maps negate the Thom class.** For a fibrewise isomorphism
`φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `-o (g b')` for every `b'`,
the map of Thom pairs of `φ` pulls the Thom class of `(E, o)` back to the negative of the Thom class
of `(E', o')`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_thomClass_of_map_eq_neg
    (ho : ∀ b', Orientation.map (Fin (n + 1)) (φ b').toLinearEquiv (o' b') = -o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) (n + 1) (o.thomClass hF) =
      -o'.thomClass hF' := by
  have h := (-o).singularCohomologyMap_thomPairMapOfFiberwise_thomClass hF o' hF' hφ ho
  rw [thomClass_neg, map_neg] at h
  exact neg_eq_iff_eq_neg.1 h

/-- **Naturality of the Euler class under orientation-preserving bundle maps.** For a fibrewise
isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `o (g b')` for
every `b'`, the Euler class of `(E', o')` is the pull-back along `g` of the Euler class of
`(E, o)`. -/
theorem eulerClass_eq_singularCohomologyMap_of_fiberwise
    (ho : ∀ b', Orientation.map (Fin (n + 1)) (φ b').toLinearEquiv (o' b') = o (g b')) :
    o'.eulerClass hF' =
      TopCat.singularCohomologyMap (TopCat.ofHom g) (n + 1) (o.eulerClass hF) := by
  rw [eulerClass_def, eulerClass_def,
    ← o.singularCohomologyMap_thomPairMapOfFiberwise_thomClass hF o' hF' hφ ho]
  exact ConcreteCategory.congr_hom (eulerClass_thomPairMapOfFiberwise hφ (n + 1)) (o.thomClass hF)

/-- **Orientation-reversing bundle maps negate the Euler class.** For a fibrewise isomorphism
`φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `-o (g b')` for every `b'`,
the Euler class of `(E', o')` is the negative of the pull-back along `g` of the Euler class of
`(E, o)`. -/
theorem eulerClass_eq_neg_singularCohomologyMap_of_fiberwise
    (ho : ∀ b', Orientation.map (Fin (n + 1)) (φ b').toLinearEquiv (o' b') = -o (g b')) :
    o'.eulerClass hF' =
      -TopCat.singularCohomologyMap (TopCat.ofHom g) (n + 1) (o.eulerClass hF) := by
  rw [← map_neg, ← eulerClass_neg]
  exact (-o).eulerClass_eq_singularCohomologyMap_of_fiberwise hF o' hF' hφ ho

/-- **The Thom class of a transported orientation.** For a fibrewise isomorphism
`φ b' : E'_{b'} ≃ E_{g b'}` over `g`, the map of Thom pairs of `φ` pulls the Thom class of `(E, o)`
back to the Thom class of `E'` with the transported orientation `φ^* o`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_thomClass_comap :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) (n + 1) (o.thomClass hF) =
      (o.comap ((Fintype.card_fin _).trans hF'.symm) hφ).thomClass hF' :=
  o.singularCohomologyMap_thomPairMapOfFiberwise_thomClass hF _ hF' hφ (map_comap_apply _ o hφ)

/-- **Naturality of the Euler class under bundle maps, with the transported orientation.** For a
fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g`, the Euler class of `E'` with the
transported orientation `φ^* o` is the pull-back along `g` of the Euler class of `(E, o)`. -/
theorem eulerClass_comap :
    (o.comap ((Fintype.card_fin _).trans hF'.symm) hφ).eulerClass hF' =
      TopCat.singularCohomologyMap (TopCat.ofHom g) (n + 1) (o.eulerClass hF) :=
  o.eulerClass_eq_singularCohomologyMap_of_fiberwise hF _ hF' hφ (map_comap_apply _ o hφ)

end BaseMap

section Isomorphism

variable {F' : Type w} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {E' : B → Type w}
  [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)]
  [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E'] [VectorBundle ℝ F' E']
  (o' : VectorBundleOrientation F' E' (Fin (n + 1))) (hF' : finrank ℝ F' = n + 1)
  {φ : ∀ b, E' b ≃L[ℝ] E b}
  (hφ : Continuous fun v : TotalSpace F' E' ↦ TotalSpace.mk' F v.proj (φ v.proj v.snd))

include hφ

/-- **Isomorphic oriented bundles have the same Euler class.** For an isomorphism of real vector
bundles `φ b : E'_b ≃ E_b` over the same base carrying the orientation `o' b` to `o b` for every
`b`, the Euler classes of `(E', o')` and `(E, o)` agree. -/
theorem eulerClass_eq_of_fiberwise
    (ho : ∀ b, Orientation.map (Fin (n + 1)) (φ b).toLinearEquiv (o' b) = o b) :
    o'.eulerClass hF' = o.eulerClass hF :=
  (o.eulerClass_eq_singularCohomologyMap_of_fiberwise hF o' hF' (g := ContinuousMap.id B) hφ
    ho).trans
    (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_id _ (n + 1)) _)

/-- **Orientation-reversing isomorphisms negate the Euler class.** For an isomorphism of real
vector bundles `φ b : E'_b ≃ E_b` over the same base carrying the orientation `o' b` to `-o b` for
every `b`, the Euler class of `(E', o')` is the negative of that of `(E, o)`. -/
theorem eulerClass_eq_neg_of_fiberwise
    (ho : ∀ b, Orientation.map (Fin (n + 1)) (φ b).toLinearEquiv (o' b) = -o b) :
    o'.eulerClass hF' = -o.eulerClass hF := by
  rw [← eulerClass_neg]
  exact (-o).eulerClass_eq_of_fiberwise hF o' hF' hφ ho

/-- **Isomorphic bundles with the transported orientation have the same Euler class.** For an
isomorphism of real vector bundles `φ b : E'_b ≃ E_b` over the same base, the Euler class of `E'`
with the transported orientation `φ^* o` is that of `(E, o)`. -/
theorem eulerClass_comap_id :
    (o.comap (g := ContinuousMap.id B) ((Fintype.card_fin _).trans hF'.symm) hφ).eulerClass hF' =
      o.eulerClass hF :=
  o.eulerClass_eq_of_fiberwise hF _ hF' hφ (map_comap_apply (g := ContinuousMap.id B) _ o hφ)

end Isomorphism

section ThomClassOfModel

variable [FiniteDimensional ℝ F] {ι : Type*} [Fintype ι] (hι : Fintype.card ι = finrank ℝ F)
  {B' : Type w} [TopologicalSpace B'] {E' : B' → Type w} [TopologicalSpace (TotalSpace F E')]
  [∀ b, AddCommMonoid (E' b)] [∀ b, Module ℝ (E' b)] [∀ b, TopologicalSpace (E' b)]
  [FiberBundle F E'] [VectorBundle ℝ F E'] (o : VectorBundleOrientation F E ι)
  (o' : VectorBundleOrientation F E' ι) (ω : Orientation ℝ F ι) {K : Type*} [CommRing K]
  {R' M' : ModuleCat.{w} K} [Module.Projective K R']
  (c : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology R' K M'
    (finrank ℝ F))
  {g : C(B', B)} {φ : ∀ b', E' b' ≃L[ℝ] E (g b')}
  (hφ : Continuous fun v : TotalSpace F E' ↦ TotalSpace.mk' F (g v.proj) (φ v.proj v.snd))

include hφ

/-- **Naturality of the normalized Thom class under orientation-preserving bundle maps.** For a
fibrewise isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to
`o (g b')` for every `b'`, the map of Thom pairs of `φ` pulls the class `thomClassOfModel o hι ω c`
back to `thomClassOfModel o' hι ω c`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel
    (ho : ∀ b', Orientation.map ι (φ b').toLinearEquiv (o' b') = o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) _ (o.thomClassOfModel hι ω c) =
      o'.thomClassOfModel hι ω c := by
  refine eq_thomClassOfModel_of_forall_exists o' hι ω c fun b' ↦ ?_
  let e := trivializationAt F E (g b')
  have hb : g b' ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  let e' := trivializationAt F E' b'
  have hb' : b' ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' _
  -- Over `b'` the pulled-back class is read along `L = φ b' ≫ e`, which differs from the chart
  -- `e'` by the automorphism `A = e'⁻¹ ≫ L` of `F`.
  let L := (φ b').trans (e.continuousLinearEquivAt ℝ (g b') hb)
  let A := (e'.continuousLinearEquivAt ℝ b' hb').symm.trans L
  obtain ⟨c₁, hc₁, hU⟩ :=
    o.exists_singularCohomologyMap_fiberThomPairMap_thomClassOfModel hι ω c e hb
  have hr : e.mapOrientation ι hb (o (g b')) =
      Orientation.map ι A.toLinearEquiv (e'.mapOrientation ι hb' (o' b')) := by
    have hL : (e'.linearEquivAt ℝ b' hb').trans A.toLinearEquiv =
        (φ b').toLinearEquiv.trans (e.linearEquivAt ℝ (g b') hb) := by
      ext v
      simp [A, L, e'.symm_apply_apply_mk hb']
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply, ← ho,
      ← Orientation.map_trans, ← Orientation.map_trans, hL]
  refine ⟨e', inferInstance, hb', (SignType.sign (A : F →L[ℝ] F).det : ℤ) • c₁, ?_, ?_⟩
  · have hdet : (A : F →L[ℝ] F).det ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
    rcases hdet.lt_or_gt with hneg | hpos
    · rw [((e'.mapOrientation ι hb' (o' b')).map_eq_neg_iff_det_neg _ hι).2 hneg] at hr
      rw [sign_neg hneg, SignType.coe_neg_one, neg_one_smul]
      rw [hr] at hc₁
      rcases hc₁ with ⟨h, rfl⟩ | ⟨h, rfl⟩
      · exact Or.inr ⟨by rw [← h]; exact (neg_neg (G := Orientation ℝ F ι) _).symm, rfl⟩
      · exact Or.inl ⟨neg_injective h, neg_neg c⟩
    · rw [((e'.mapOrientation ι hb' (o' b')).map_eq_iff_det_pos _ hι).2 hpos] at hr
      rw [sign_pos hpos, SignType.coe_one, one_smul, ← hr]
      exact hc₁
  · rw [← TopPair.singularCohomologyMap_comp_apply, fiberThomPairMap_comp_thomPairMapOfFiberwise,
      TopPair.singularCohomologyMap_comp_apply, hU, ← TopPair.singularCohomologyMap_comp_apply,
      ← Iso.trans_hom, ← ContinuousLinearEquiv.complZeroPairIso_trans,
      ContinuousLinearEquiv.singularCohomologyMap_complZeroPairIso_hom_eq_sign_det_smul
        (e'.continuousLinearEquivAt ℝ b' hb') L, map_zsmul]

/-- **Orientation-reversing bundle maps negate the normalized Thom class.** For a fibrewise
isomorphism `φ b' : E'_{b'} ≃ E_{g b'}` over `g` carrying the orientation `o' b'` to `-o (g b')` for
every `b'`, the map of Thom pairs of `φ` pulls the class `thomClassOfModel o hι ω c` back to the
negative of `thomClassOfModel o' hι ω c`. -/
theorem singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel_of_map_eq_neg
    (ho : ∀ b', Orientation.map ι (φ b').toLinearEquiv (o' b') = -o (g b')) :
    TopPair.singularCohomologyMap (thomPairMapOfFiberwise hφ) _ (o.thomClassOfModel hι ω c) =
      -o'.thomClassOfModel hι ω c := by
  have h := (-o).singularCohomologyMap_thomPairMapOfFiberwise_thomClassOfModel hι o' ω c hφ
    fun b' ↦ (ho b').trans (neg_apply o (g b')).symm
  rw [thomClassOfModel_neg, map_neg] at h
  exact neg_eq_iff_eq_neg.1 h

end ThomClassOfModel

end TauCeti.VectorBundleOrientation
