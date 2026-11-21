/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Effective
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.PicZero
import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.FieldPoint

/-!
# Field-valued surjectivity of the Abel maps

On a smooth proper geometrically connected curve, every line bundle of degree `d ≥ g` is
`𝒪(D)` for an effective Cartier divisor of degree `d`. Applying this on the field-valued
fibres of a family identifies actual preimages under the Abel map of the divisor functor.
The normalized degree-`d` Abel map is consequently surjective onto the degree-zero Picard
presheaf at every field-valued point whose fibre has genus at most `d`.

The field need not be algebraically closed or perfect. These assertions concern the relative
Picard presheaf, whose value at a field is the Picard group of the fibre. They do not assert
surjectivity on arbitrary test schemes or representability of either functor.

## References

* J. S. Milne, *Jacobian Varieties*, Section 5 (surjectivity of the Abel maps).
* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Theorem 1.3 (Riemann–Roch).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry
open Module (finrank)

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]
  {k : Type u} [Field k] (g : Spec (.of k) ⟶ S)

/-- Every relative Picard class over a field with degree `d ≥ g(X_k)` at a field-valued
point `ξ` of `Spec k` has an Abel preimage represented by an effective Cartier divisor of
rank `d` on `X_k`. -/
theorem exists_abelMap_app_eq_of_genus_le (d : ℕ)
    (hd : letI : (pullback g f).Over (Spec (.of k)) := ⟨pullback.fst g f⟩
      finrank k (Scheme.Modules.Cohomology
        (InvertibleSheaf.trivial (pullback g f)).obj 1) ≤ d)
    {Ω : Type u} [Field Ω] {ξ : Spec (.of Ω) ⟶ Spec (.of k)}
    (c : (relativePicardPresheaf f).obj (op (Over.mk g)))
    (hc : relativePicardFiberDegree f ξ c = d) :
    ∃ D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj (op (Over.mk g)),
      (abelMap f).app (op (Over.mk g)) (ULift.up D.1) = c := by
  let _ : (pullback g f).Over (Spec (.of k)) := ⟨pullback.fst g f⟩
  have := SmoothOfRelativeDimension.smooth 1 f
  have : IsProper (pullback g f ↘ Spec (.of k)) :=
    inferInstanceAs (IsProper (pullback.fst g f))
  have : SmoothOfRelativeDimension 1 (pullback g f ↘ Spec (.of k)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.fst g f))
  have : GeometricallyIntegral (pullback g f ↘ Spec (.of k)) :=
    inferInstanceAs (GeometricallyIntegral (pullback.fst g f))
  have : IsIntegral (pullback g f) :=
    GeometricallyIntegral.isIntegral_of_subsingleton (pullback g f ↘ Spec (.of k))
  have : RelativeDimensionLE 1 (pullback g f ↘ Spec (.of k)) :=
    inferInstanceAs (RelativeDimensionLE 1 (pullback.fst g f))
  have := finiteDimensional_cohomology_one_trivial_of_smooth k (pullback g f)
  have : Subsingleton (LineBundleClass (op (Over.mk g)).unop.left) :=
    inferInstanceAs (Subsingleton (LineBundleClass (Spec (.of k))))
  obtain ⟨L, hL⟩ := LineBundleClass.mk_surjective (X := pullback g f)
    (relativePicardPresheafObjMulEquiv f (op (Over.mk g)) c)
  have hquot : (QuotientGroup.mk (LineBundleClass.mk L) :
      (relativePicardPresheaf f).obj (op (Over.mk g))) = c := by
    apply (relativePicardPresheafObjMulEquiv f (op (Over.mk g))).injective
    rw [relativePicardPresheafObjMulEquiv_mk, hL]
  have hdeg : L.eulerDegree k = d := by
    rw [← hquot, relativePicardFiberDegree_mk_eq_eulerDegree f g,
      LineBundleClass.eulerDegree_mk] at hc
    exact hc
  obtain ⟨I, hI, hclass, hdegree⟩ :=
    L.exists_isEffectiveCartier_eulerDegree_eq_of_genus_le k (by rw [hdeg]; exact_mod_cast hd)
  have hrel : I.IsRelativeEffectiveCartier (pullback.fst g f) :=
    (Scheme.IdealSheafData.isRelativeEffectiveCartier_iff_isEffectiveCartier _ _).mpr hI
  have hrank : (I.subschemeι ≫ pullback.fst g f).finrank = fun _ ↦ d := by
    ext t
    have ht : t = default := Subsingleton.elim _ _
    rw [ht]
    exact_mod_cast hdegree.symm.trans hdeg
  refine ⟨⟨⟨I, (mem_relativeEffectiveCartierSubfunctor_obj_iff f).mpr hrel⟩,
    (mem_relativeEffectiveCartierDegreeSubfunctor_obj_iff f).mpr hrank⟩, ?_⟩
  apply (relativePicardPresheafObjMulEquiv f (op (Over.mk g))).injective
  rw [abelMap_app_apply, relativePicardPresheafObjMulEquiv_mk, hclass, inv_inv, hL]

/-- If `d` is at least the genus of a field-valued fibre, the normalized degree-`d` Abel map
is surjective onto `Pic⁰` at that field. The section is used only for normalization; neither
algebraic closedness nor perfectness of the field is assumed. -/
theorem abelJacobiMapOfDegreeToPicZero_app_surjective_of_genus_le {x₀ : S ⟶ X}
    (hx₀ : x₀ ≫ f = 𝟙 S) (d : ℕ)
    (hd : letI : (pullback g f).Over (Spec (.of k)) := ⟨pullback.fst g f⟩
      finrank k (Scheme.Modules.Cohomology
        (InvertibleSheaf.trivial (pullback g f)).obj 1) ≤ d) :
    Function.Surjective ((abelJacobiMapOfDegreeToPicZero f hx₀ d).app (op (Over.mk g))) := by
  rintro ⟨c, hc⟩
  -- Keep multiplication in the group-valued presheaf, rather than its forgotten carrier.
  let c₀ : (relativePicardPresheaf f).obj (op (Over.mk g)) := c
  let ξ := Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hc₀ : relativePicardFiberDegree f ξ c₀ = 0 :=
    (mem_relativePicardDegreeZeroSubfunctor_obj_iff f).mp hc (AlgebraicClosure k) ξ
  let B := (graphDivisor f).app (op (Over.mk g)) (basePoint hx₀ (Over.mk g))
  have hpow : (abelMap f).app (op (Over.mk g)) (ULift.up B) ^ d =
      (abelMap f).app (op (Over.mk g)) (ULift.up (B ^ d)) := by
    simp only [← abelMapMonoidHom_apply, map_pow]
  let b : (relativePicardPresheaf f).obj (op (Over.mk g)) :=
    (abelMap f).app (op (Over.mk g)) (ULift.up B)
  have hdeg : relativePicardFiberDegree f ξ (c₀ * b ^ d) = d := by
    rw [relativePicardFiberDegree_mul_of_smooth, hc₀, hpow,
      relativePicardFiberDegree_abelMap_app_of_mem f ξ
        (graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj
          f hx₀ d (op (Over.mk g))), zero_add]
  obtain ⟨D, hD⟩ := exists_abelMap_app_eq_of_genus_le f g d hd _ hdeg
  refine ⟨ULift.up D, Subtype.ext ?_⟩
  rw [abelJacobiMapOfDegreeToPicZero_app_apply_val, abelJacobiMapOfDegree_app_apply, hD]
  exact mul_div_cancel_right _ _

end

end TauCeti.AlgebraicGeometry
