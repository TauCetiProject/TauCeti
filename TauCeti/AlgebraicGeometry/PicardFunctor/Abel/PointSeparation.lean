/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.Genus.BaseChange
public import TauCeti.AlgebraicGeometry.Geometrically.FunctionField
public import TauCeti.AlgebraicGeometry.LineBundle.LocalRing
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Jacobi
public import TauCeti.AlgebraicGeometry.RationalPoint.IdealSheaf
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PointSeparation

/-!
# The Abel–Jacobi map separates field-valued points in positive genus

Let `f : X ⟶ S` be a smooth proper geometrically connected morphism of relative dimension one
with a section `x₀`, and let `ξ : Spec K ⟶ S` be a point with values in a field `K`. If the fibre
`X_ξ = Spec K ×_S X` has positive genus, then the Abel–Jacobi map
`x ↦ 𝒪(Γₓ - x₀)` (`TauCeti.AlgebraicGeometry.abelJacobiMap`) is injective on the `K`-points of
`X` over `ξ`. Over a field `k` this says that for a smooth proper geometrically connected curve
`X` of genus `g ≥ 1` with a rational point, the Abel–Jacobi map is injective on `K`-points for
every field extension `K / k`, in particular on geometric points.

The proof works on the fibre `X_ξ`, a smooth proper integral curve over `K` with `K`
algebraically closed in its function field. There the graph of a `K`-point `x` is the closed
point `p` it hits, and its ideal sheaf is `𝒪(-p)`
(`AlgebraicGeometry.Scheme.Hom.kerSheafIsoNegPoint`).
Since `Pic(Spec K)` is trivial, equal Abel–Jacobi classes make the two points linearly equivalent
as Weil divisors. Linearly equivalent rational points on a curve of positive genus are equal
(`TauCeti.AlgebraicGeometry.SchemeWeilDivisor.eq_of_linearlyEquivalent_ofPoint_of_genus_pos`), and
a section of `X_ξ ⟶ Spec K` is determined by its underlying point.

This is the injectivity on geometric points in the statement that the Abel–Jacobi map of a curve
of positive genus is a closed immersion. Neither the Jacobian scheme nor the injectivity of the
Abel–Jacobi map on tangent vectors is treated here.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.eq_of_mk_toInvertibleSheaf_eq_of_genus_pos`: two rational points
  of a smooth proper curve of positive genus whose ideal sheaves are isomorphic coincide;
* `TauCeti.AlgebraicGeometry.abelJacobiMap_app_injective_of_nontrivial_cohomology`: the
  Abel–Jacobi map is injective on the points of `X` with values in a field over which the fibre
  has nonzero `H¹(X_ξ, 𝒪)`;
* `TauCeti.AlgebraicGeometry.abelJacobiMap_app_injective_of_genus_pos`: for a curve of positive
  genus over a field `k`, the Abel–Jacobi map is injective on `K`-points for every field
  extension `K / k`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1: on a curve of positive genus
  distinct points are not linearly equivalent.
* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Section 2: the canonical map `Q ↦ 𝒪(Q - P)` from a curve of positive
  genus to its Jacobian is a closed immersion.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {K : Type u} [Field K] {Y : Scheme.{u}} [Y.Over (Spec (.of K))] [IsIntegral Y]
  [IsProper (Y ↘ Spec (.of K))] [SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K))]

/-- **Rational points of a curve of positive genus are separated by their ideal sheaves.** Let
`Y` be a smooth proper integral curve over a field `K`, with `K` algebraically closed in the
function field `K(Y)` and with positive genus. If two rational points `s` and `t` have isomorphic
ideal line bundles `𝒪(-s) ≅ 𝒪(-t)`, then `s = t`. -/
theorem eq_of_mk_toInvertibleSheaf_eq_of_genus_pos
    [FiniteDimensional K (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 1)]
    (hk : IsIntegrallyClosedIn K Y.functionField) (hg : 0 < Y.genus K)
    {s t : Spec (.of K) ⟶ Y} (hs : s ≫ (Y ↘ Spec (.of K)) = 𝟙 (Spec (.of K)))
    (ht : t ≫ (Y ↘ Spec (.of K)) = 𝟙 (Spec (.of K))) (hIs : s.ker.IsEffectiveCartier)
    (hIt : t.ker.IsEffectiveCartier)
    (h : LineBundleClass.mk hIs.toInvertibleSheaf = LineBundleClass.mk hIt.toInvertibleSheaf) :
    s = t := by
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of K))
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of K))
  have : CompactSpace Y := (quasiCompact_iff_compactSpace (Y ↘ Spec (.of K))).mp inferInstance
  have : IsNoetherian Y := {}
  have : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y) :=
    isRegularLocalRing_stalk_of_smooth (Y ↘ Spec (.of K))
  have : ∀ y : CodimensionOnePoint Y, IsDiscreteValuationRing (Y.presheaf.stalk (y : Y)) :=
    fun y ↦ inferInstance
  have := isClosedImmersion_of_comp_eq_id s hs
  have := isClosedImmersion_of_comp_eq_id t ht
  have hdim : topologicalKrullDim Y = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (Y ↘ Spec (.of K))
  have hX : ∀ y : Y, coheight y ≤ 1 := fun y ↦ by
    exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim y).trans hdim.le
  have : Fact (∀ y : Y, coheight y ≤ 1) := ⟨hX⟩
  let x : CodimensionOnePoint Y := ⟨_, coheight_eq_of_isClosed_of_smoothOfRelativeDimension
    (Y ↘ Spec (.of K)) (isClosed_singleton_of_section hs)⟩
  let y : CodimensionOnePoint Y := ⟨_, coheight_eq_of_isClosed_of_smoothOfRelativeDimension
    (Y ↘ Spec (.of K)) (isClosed_singleton_of_section ht)⟩
  -- The ideal line bundle of a rational point is the divisor line bundle of `-p`.
  have hclass (r : Spec (.of K) ⟶ Y) [IsClosedImmersion r] (p : CodimensionOnePoint Y)
      (hp : (p : Y) = r (IsLocalRing.closedPoint K)) (hIr : r.ker.IsEffectiveCartier) :
      SchemeWeilDivisor.toLineBundleClass hX (-WeilDivisor.ofPoint p) =
        LineBundleClass.mk hIr.toInvertibleSheaf :=
    (SchemeWeilDivisor.toLineBundleClass_eq_mk_iff hX).mpr
      ⟨eqToIso (SchemeWeilDivisor.toInvertibleSheaf_obj hX _) ≪≫
        (kerSheafIsoNegPoint r hp hX).symm ≪≫ eqToIso hIr.toInvertibleSheaf_obj.symm⟩
  have hlin := (SchemeWeilDivisor.toLineBundleClass_eq_iff hX).mp
    ((hclass s x rfl hIs).trans (h.trans (hclass t y rfl hIt).symm))
  rw [WeilDivisor.OrderSystem.linearlyEquivalent_iff, neg_sub_neg,
    ← WeilDivisor.OrderSystem.linearlyEquivalent_iff] at hlin
  have hxy : x = y := SchemeWeilDivisor.eq_of_linearlyEquivalent_ofPoint_of_genus_pos K hk hg
    (residueDegree_eq_one_of_section hs _) hlin.symm
  have : IsIso ((Y ↘ Spec (.of K)).residueFieldMap (s (IsLocalRing.closedPoint K))) :=
    isIso_residueFieldMap_of_section hs _
  exact hom_ext_of_isIso_residueFieldMap (f := Y ↘ Spec (.of K)) (hs.trans ht.symm)
    (congrArg Subtype.val hxy)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [SmoothOfRelativeDimension 1 f]
  [GeometricallyConnected f] {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- **The Abel–Jacobi map separates the points of a field-valued fibre of positive genus.** Let
`f : X ⟶ S` be a smooth proper geometrically connected morphism of relative dimension one with a
section `x₀`, and let `ξ : Spec K ⟶ S` be a point with values in a field. If the first cohomology
`H¹(X_ξ, 𝒪)` of the fibre `X_ξ = Spec K ×_S X` is nonzero, that is, if `X_ξ` has positive genus,
then two `K`-points of `X` over `ξ` with the same class `𝒪(Γₓ - x₀)` in `Pic(X_ξ) / Pic(Spec K)`
are equal. -/
theorem abelJacobiMap_app_injective_of_nontrivial_cohomology {K : Type u} [Field K]
    (ξ : Spec (.of K) ⟶ S)
    (hg : Nontrivial (Scheme.Modules.Cohomology (InvertibleSheaf.trivial (pullback ξ f)).obj 1)) :
    Function.Injective ((abelJacobiMap f hx₀).app (Opposite.op (Over.mk ξ))) := by
  rintro ⟨x⟩ ⟨y⟩ hxy
  rw [abelJacobiMap_app_apply, abelJacobiMap_app_apply, div_left_inj, abelMap_app_apply,
    abelMap_app_apply] at hxy
  -- Line bundles on `Spec K` are trivial, so the quotient by `Pic(Spec K)` is injective.
  obtain ⟨c, hc⟩ := QuotientGroup.eq.mp hxy
  rw [Subsingleton.elim (α := LineBundleClass (Spec (.of K))) c 1, map_one, eq_comm,
    inv_mul_eq_one, inv_inj] at hc
  -- The fibre `X_ξ` is a smooth proper integral curve over `K` with exact constants.
  let _ : (pullback ξ f).Over (Spec (.of K)) := ⟨pullback.fst ξ f⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (pullback ξ f ↘ Spec (.of K)) := inferInstanceAs (IsProper (pullback.fst ξ f))
  have : SmoothOfRelativeDimension 1 (pullback ξ f ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.fst ξ f))
  have : GeometricallyIntegral (pullback ξ f ↘ Spec (.of K)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst ξ f))
  have : IsIntegral (pullback ξ f) :=
    GeometricallyIntegral.geometrically_isIntegral ξ _ _ (IsPullback.of_hasPullback ξ f).flip
  have := finiteDimensional_cohomology_one_trivial_of_smooth K (pullback ξ f)
  have hpos : 0 < (pullback ξ f).genus K := by
    rw [Scheme.genus_def]
    exact Module.finrank_pos
  -- The divisor class only depends on the ideal sheaf, here the ideal sheaf of the graph.
  have hmk {I J : (pullback ξ f).IdealSheafData} (hIJ : I = J) (hI : I.IsEffectiveCartier)
      (hJ : J.IsEffectiveCartier) :
      LineBundleClass.mk hI.toInvertibleSheaf = LineBundleClass.mk hJ.toInvertibleSheaf := by
    subst hIJ
    rfl
  have hst := Scheme.Hom.eq_of_mk_toInvertibleSheaf_eq_of_genus_pos
    (isIntegrallyClosedIn_functionField_of_geometricallyIntegral (k := K)) hpos
    (graphSection_fst x) (graphSection_fst y)
    ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
      (ker_graphSection_mem_relativeEffectiveCartierSubfunctor_obj x)).isEffectiveCartier
    ((mem_relativeEffectiveCartierSubfunctor_obj_iff f).mp
      (ker_graphSection_mem_relativeEffectiveCartierSubfunctor_obj y)).isEffectiveCartier
    ((hmk (graphDivisor_app_apply_val x).symm _ _).trans
      (hc.trans (hmk (graphDivisor_app_apply_val y) _ _)))
  exact congrArg ULift.up (ker_graphSection_inj.mp (congrArg Scheme.Hom.ker hst))

/-- **The Abel–Jacobi map of a curve of positive genus separates points over every field
extension.** Let `X` be a smooth proper geometrically connected curve of genus `g ≥ 1` over a
field `k`, with a rational point `x₀`. For every field extension `K / k`, two `K`-points of `X`
with the same class `𝒪(Γₓ - x₀)` in `Pic(X_K) / Pic(Spec K)` are equal. Taking `K`
algebraically closed, the Abel–Jacobi map is injective on geometric points. -/
theorem abelJacobiMap_app_injective_of_genus_pos {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [GeometricallyConnected (X ↘ Spec (.of k))]
    [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
    {x₀ : Spec (.of k) ⟶ X} (hx₀ : x₀ ≫ (X ↘ Spec (.of k)) = 𝟙 (Spec (.of k)))
    (hg : 0 < X.genus k) (K : Type u) [Field K] [Algebra k K] :
    Function.Injective ((abelJacobiMap (X ↘ Spec (.of k)) hx₀).app
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) := by
  let ξ := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let _ : (pullback ξ (X ↘ Spec (.of k))).Over (Spec (.of K)) :=
    ⟨pullback.fst ξ (X ↘ Spec (.of k))⟩
  have : ConnectedSpace X :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := X ↘ Spec (.of k))
  -- The genus does not change under extension of the base field.
  have H : IsPullback (pullback.snd ξ (X ↘ Spec (.of k)))
      (pullback ξ (X ↘ Spec (.of k)) ↘ Spec (.of K)) (X ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (IsPullback.of_hasPullback ξ (X ↘ Spec (.of k))).flip
  have h := finrank_cohomology_one_trivial_eq_of_isPullback_of_smooth H
  rw [Scheme.genus_def, ← h] at hg
  exact abelJacobiMap_app_injective_of_nontrivial_cohomology _ hx₀ ξ
    (Module.nontrivial_of_finrank_pos hg)

end TauCeti.AlgebraicGeometry
