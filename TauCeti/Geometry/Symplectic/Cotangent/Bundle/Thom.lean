/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ConcreteCategory.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Orientation
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.Codisc
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.SphereBundle.Basic
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.Orientation.Cover.Descent

/-!
# The Thom isomorphism of the unit codisc bundle

Let `M` be a Riemannian manifold of dimension `n`, with cotangent bundle `T*M`, unit codisc bundle
`D*M = {‖p‖ ≤ 1}` and unit cosphere bundle `S*M = {‖p‖ = 1}`
(`TauCeti.CotangentBundle.codiscBundle`, `TauCeti.CotangentBundle.cosphereBundle`). This file
computes the relative homology of the pair `(D*M, S*M)` (`TauCeti.CotangentBundle.codiscPair`):
it is the homology of `M`, shifted up by `n`,

`Hₚ₊ₙ(D*M, S*M) ≅ Hₚ(M)`,

with the coefficients twisted by the orientation local system of `T*M` when `M` is not
orientable. These are the Thom isomorphisms of the cotangent bundle, read on its unit disc and
sphere bundles. In symplectic topology `D*M` is the standard Liouville domain with boundary `S*M`,
and the inverse of this isomorphism is the shriek map `π_!` of the projection `D*M → M`, through
which classes of `M` are compared with classes of domains of `T*M` and with the zero-energy part
of symplectic homology.

The norm of covectors is a continuous fibre gauge on `T*M`
(`TauCeti.CotangentBundle.isFiberGauge_norm_snd`), whose disc and sphere bundles are `D*M` and
`S*M` (`TauCeti.CotangentBundle.codiscPair_eq_gaugeDiscSpherePair`). So the inclusion of
`(D*M, S*M)` into the Thom pair `(T*M, T*M ∖ 0)` of the cotangent bundle
(`TauCeti.CotangentBundle.codiscPairMap`) induces isomorphisms on relative singular homology with
any coefficients (`TauCeti.CotangentBundle.isIso_singularHomologyMap_codiscPairMap`), by radial
rescaling (`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`). Composing with the Thom
isomorphisms of the vector bundle `T*M`:

* for a Thom class `u` of `T*M` with coefficients in a commutative ring `K`,
  `Hₘ(D*M, S*M; K) ≅ Hₚ(M; K)` for `n + p = m`, over any base
  (`TauCeti.CotangentBundle.codiscPairSingularHomologyIso`, from `TauCeti.homologyThomIso`);
* with no orientation, when `2 = 0` in `K`, for instance `K = ZMod 2`
  (`TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_of_two_eq_zero`);
* for an oriented manifold, over every commutative ring, `ℤ` included
  (`TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_of_orientation`). The Riesz
  isomorphisms `p ↦ p♯` of the metric (`Riemannian.Tensor.rieszDual`) form a continuous bundle
  isomorphism `T*M ≃ TM` (`TauCeti.CotangentBundle.continuous_rieszDual`), along which an
  orientation of `M` transports to an orientation of `T*M`
  (`TauCeti.CotangentBundle.orientation`), and this has a Thom class;
* for a compact manifold, orientable or not, over every commutative ring,
  `Hₚ₊ₙ(D*M, S*M; K) ≅ Hₚ(M; o(T*M) ⊗ K)` with coefficients in the orientation local system of
  `T*M` (`TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_twistedHomology`),
  from the twisted Thom isomorphism over a compact base
  (`nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace`, in the namespace
  `TauCeti.VectorBundleOrientationCover`).
  The twist cannot be dropped in general: for the real projective plane `H₂(ℝP²; o ⊗ ℤ) ≅ ℤ`,
  while `H₂(ℝP²; ℤ) = 0`.

## Main definitions

* `TauCeti.CotangentBundle.codiscPair`: the pair `(D*M, S*M)`.
* `TauCeti.CotangentBundle.codiscPairMap`: its inclusion into the Thom pair of `T*M`.
* `TauCeti.CotangentBundle.codiscPairSingularHomologyIso`: `Hₘ(D*M, S*M; K) ≅ Hₚ(M; K)` from a
  Thom class of `T*M`.

## Main results

* `TauCeti.CotangentBundle.isFiberGauge_norm_snd`: the norm of covectors is a fibre gauge.
* `TauCeti.CotangentBundle.isIso_singularHomologyMap_codiscPairMap`: `(D*M, S*M)` and the Thom pair
  of `T*M` have the same relative homology.
* `TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_of_two_eq_zero`,
  `TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_of_orientation`,
  `TauCeti.CotangentBundle.nonempty_singularHomology_codiscPair_iso_twistedHomology`: the Thom
  isomorphism of the codisc bundle in characteristic two, for oriented manifolds, and with
  orientation-twisted coefficients over a compact manifold.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), Theorem 10.4 and §12.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4 (the zero-energy part of symplectic
  homology) and Proposition 5.9.
-/

public section

noncomputable section

open AlgebraicTopology Bundle CategoryTheory Limits Module
open scoped Manifold

universe u

namespace TauCeti

namespace CotangentBundle

section Pair

variable {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]

variable (I M) in
/-- The pair `(D*M, S*M)` of the unit codisc bundle and the unit cosphere bundle of a Riemannian
manifold. -/
abbrev codiscPair : TopPair.{u} :=
  TopPair.ofInclusion (X := TopCat.of (CotangentBundle I M))
    (cosphereBundle_subset_codiscBundle (I := I) (M := M))

variable (I M) in
/-- The inclusion of the pair `(D*M, S*M)` into the Thom pair `(T*M, T*M ∖ 0)` of the cotangent
bundle. -/
def codiscPairMap :
    codiscPair I M ⟶ thomPair (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) :=
  TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (TopCat.ofHom (ContinuousMap.inclusion fun _ hz ↦
      mem_zeroSectionCompl.2 (snd_ne_zero_of_mem_cosphereBundle hz)))
    (by ext; rfl)

/-- The inclusion of `(D*M, S*M)` into the Thom pair is the inclusion of `D*M` into `T*M`. -/
@[simp]
theorem codiscPairMap_fst_apply (z : codiscBundle I M) :
    TopPair.Hom.fst (codiscPairMap I M) z = z.val :=
  (rfl)

/-- The inclusion of `(D*M, S*M)` into the Thom pair maps `S*M` into `T*M ∖ 0` by inclusion. -/
@[simp]
theorem codiscPairMap_snd_apply (z : cosphereBundle I M) :
    (TopPair.Hom.snd (codiscPairMap I M) z).val = z.val :=
  (rfl)

variable (I M) in
/-- The pair `(D*M, S*M)` is the disc-sphere pair of the norm of covectors. -/
theorem codiscPair_eq_gaugeDiscSpherePair :
    codiscPair I M = gaugeDiscSpherePair fun z : CotangentBundle I M ↦ ‖z.snd‖ :=
  TopPair.ofInclusion_congr _ _ (by ext; simp) (by ext; simp)

variable [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

/-- The norm of covectors is a fibre gauge on the cotangent bundle: it is continuous, positively
homogeneous on each cotangent space and positive off the zero section. Its disc and sphere bundles
are `D*M` and `S*M`. -/
theorem isFiberGauge_norm_snd : IsFiberGauge fun z : CotangentBundle I M ↦ ‖z.snd‖ :=
  isFiberGauge_norm (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
    continuous_norm_snd

/-- The inclusion of `(D*M, S*M)` into the Thom pair is the inclusion of the disc-sphere pair of the
norm of covectors, once the two pairs are identified. -/
theorem codiscPairMap_eq_eqToHom_comp :
    codiscPairMap I M = eqToHom (codiscPair_eq_gaugeDiscSpherePair I M) ≫
      gaugeDiscSpherePairMap isFiberGauge_norm_snd :=
  TopPair.hom_ext_of_fst _ (by
    ext z
    simp only [TopPair.Hom.fst_comp, MorphismProperty.Comma.eqToHom_right, TopCat.hom_comp,
      ContinuousMap.comp_apply]
    refine (codiscPairMap_fst_apply z).trans (.trans ?_ (gaugeDiscSpherePairMap_fst_apply _ _).symm)
    -- Transport along the identification of the pairs does not move the underlying covector.
    exact (Subtype.heq_iff_coe_eq fun _ ↦ mem_codiscBundle.trans
      (mem_gaugeDiscBundle (ρ := fun z : CotangentBundle I M ↦ ‖z.snd‖)).symm).1
        (eqToHom_apply_heq (congrArg (fun P : TopPair.{u} ↦ P.fst)
          (codiscPair_eq_gaugeDiscSpherePair I M)) z).symm)

/-- **The codisc bundle pair has the relative homology of the Thom pair.** The inclusion of
`(D*M, S*M)` into the Thom pair `(T*M, T*M ∖ 0)` of the cotangent bundle induces isomorphisms on
relative singular homology, with coefficients in any abelian category with coproducts. -/
theorem isIso_singularHomologyMap_codiscPairMap {C : Type*} [Category C] [HasCoproducts.{u} C]
    [Abelian C] (R : C) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (codiscPairMap I M) R n) := by
  rw [codiscPairMap_eq_eqToHom_comp, TopPair.singularHomologyMap_comp,
    TopPair.singularHomologyMap_eqToHom]
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap (isFiberGauge_norm_snd (I := I) (M := M))
    R n
  infer_instance

variable (I M) in
/-- **The Thom isomorphism of the codisc bundle.** For a Thom class `u` of the cotangent bundle
of a Riemannian manifold of dimension `n`, with coefficients in a commutative ring `K`, the relative
homology of `(D*M, S*M)` is the homology of `M` shifted by `n`: `Hₘ(D*M, S*M; K) ≅ Hₚ(M; K)` for
`n + p = m`. It is the inclusion into the Thom pair of `T*M` followed by the homology Thom
isomorphism `x ↦ π_*(x ⌢ u)`. -/
def codiscPairSingularHomologyIso (K : Type u) [CommRing K] (p m : ℕ)
    (h : finrank ℝ E + p = m)
    (u : (thomPair (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (E →L[ℝ] ℝ)))
    (hu : IsThomClass (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) u) :
    (codiscPair I M).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj (TopCat.of M) :=
  have := isIso_singularHomologyMap_codiscPairMap (I := I) (M := M) (ModuleCat.of K K) m
  asIso (TopPair.singularHomologyMap (codiscPairMap I M) (ModuleCat.of K K) m) ≪≫
    homologyThomIso _ _ p m (by rw [ContinuousLinearMap.dual_finrank_eq, h]) u hu

/-- The Thom isomorphism of the codisc bundle is induced by the inclusion into the Thom pair of
`T*M` followed by the homology Thom map `x ↦ π_*(x ⌢ u)`. -/
@[simp]
theorem codiscPairSingularHomologyIso_hom (K : Type u) [CommRing K] (p m : ℕ)
    (h : finrank ℝ E + p = m)
    (u : (thomPair (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ (E →L[ℝ] ℝ)))
    (hu : IsThomClass (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) u) :
    (codiscPairSingularHomologyIso I M K p m h u hu).hom =
      TopPair.singularHomologyMap (codiscPairMap I M) (ModuleCat.of K K) m ≫
        homologyThomMap (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) (ModuleCat.of K K)
          (finrank ℝ (E →L[ℝ] ℝ)) p m (by rw [ContinuousLinearMap.dual_finrank_eq, h]) u := by
  simp [codiscPairSingularHomologyIso]

/-- **The Thom isomorphism of the codisc bundle in characteristic two.** For a Riemannian manifold
of dimension `n`, orientable or not, and a commutative ring `K` in which `2 = 0`, such as
`ZMod 2`, `Hₚ₊ₙ(D*M, S*M; K) ≅ Hₚ(M; K)` in every degree `p`. -/
theorem nonempty_singularHomology_codiscPair_iso_of_two_eq_zero (K : Type u) [CommRing K]
    (h2 : (2 : K) = 0) (p : ℕ) :
    Nonempty ((codiscPair I M).singularHomology (ModuleCat.of K K) (finrank ℝ E + p) ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of M)) :=
  let ⟨u, hu⟩ := exists_isThomClass_of_two_eq_zero
    (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) K h2
  ⟨codiscPairSingularHomologyIso I M K p _ rfl u hu⟩

end Pair

/-! ### Oriented manifolds -/

section Orientation

variable {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M]
  [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] {ι : Type*} [Fintype ι]

/-- **The Thom isomorphism of the codisc bundle of an oriented manifold.** For an oriented
Riemannian manifold of dimension `n` and every commutative ring `K`, `ℤ` included,
`Hₚ₊ₙ(D*M, S*M; K) ≅ Hₚ(M; K)` in every degree `p`. -/
theorem nonempty_singularHomology_codiscPair_iso_of_orientation
    (hι : Fintype.card ι = finrank ℝ E)
    (o : VectorBundleOrientation E (TangentSpace I : M → Type u) ι) (K : Type u) [CommRing K]
    (p : ℕ) :
    Nonempty ((codiscPair I M).singularHomology (ModuleCat.of K K) (finrank ℝ E + p) ≅
      ((singularHomologyFunctor (ModuleCat.{u} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of M)) :=
  let ⟨u, hu⟩ := (orientation I hι o).exists_isThomClass
    (by rw [ContinuousLinearMap.dual_finrank_eq, hι]) K
  ⟨codiscPairSingularHomologyIso I M K p _ rfl u hu⟩

end Orientation

/-! ### Orientation-twisted coefficients -/

section Twisted

variable {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type u} [TopologicalSpace M]
  [ChartedSpace H M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)] [CompactSpace M]
  {ι : Type} [Fintype ι]

/-- **The Thom isomorphism of the codisc bundle with orientation-twisted coefficients.** For a
compact Riemannian manifold of dimension `n`, orientable or not, and every commutative ring `K`,
`ℤ` included, `Hₚ₊ₙ(D*M, S*M; K) ≅ Hₚ(M; o(T*M) ⊗ K)` in every degree `p`, with coefficients in the
orientation local system `o(T*M)` of the cotangent bundle. -/
theorem nonempty_singularHomology_codiscPair_iso_twistedHomology
    (hι : Fintype.card ι = finrank ℝ (E →L[ℝ] ℝ)) (K : Type u) [CommRing K] (p : ℕ) :
    Nonempty ((codiscPair I M).singularHomology (ModuleCat.of K K) (finrank ℝ E + p) ≅
      LocalCoefficientSystem.twistedHomology
        (VectorBundleOrientationCover.signLocalSystem (E →L[ℝ] ℝ)
          (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) K hι) p) := by
  have := isIso_singularHomologyMap_codiscPairMap (I := I) (M := M) (ModuleCat.of K K)
    (finrank ℝ E + p)
  obtain ⟨e⟩ := open VectorBundleOrientationCover in
    nonempty_singularHomology_thomPair_iso_twistedHomology_of_compactSpace
      (F := E →L[ℝ] ℝ) (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) hι K p
  rw [ContinuousLinearMap.dual_finrank_eq, Nat.add_comm] at e
  exact ⟨asIso (TopPair.singularHomologyMap (codiscPairMap I M) (ModuleCat.of K K) _) ≪≫ e⟩

end Twisted

end CotangentBundle

end TauCeti
