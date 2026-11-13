/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.BaseChange
public import TauCeti.AlgebraicGeometry.Cohomology.Trivial
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms
public import TauCeti.AlgebraicGeometry.LineBundle.Functoriality
public import TauCeti.AlgebraicGeometry.LineBundle.Hom
public import TauCeti.AlgebraicGeometry.Modules.Dual
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Line bundles under extension of the base field

Let `X` be an integral scheme universally closed and quasi-separated over a field `k`
(for instance a proper integral scheme), and let `K / k` be a field extension, with
`X_K = X ×_k K`. Pulling line bundles back along `X_K ⟶ X` is injective on line-bundle classes
(`TauCeti.AlgebraicGeometry.LineBundleClass.pullback_injective`): a line bundle on `X` that
becomes trivial over `K` is already trivial over `k`.

Flat base change in degree zero gives nonzero global sections of both the line bundle and
its dual. Their composition is a nonzero global function, hence a unit because `Γ(X, 𝒪_X)` is
a field. The resulting isomorphism trivializes the line bundle. No dimension bound or
cohomological finiteness assumption is needed.

The scheme need not be smooth, geometrically integral or have a rational point, and `X_K` need
not be reduced or irreducible. Without universal closedness the statement fails: the Picard group
of the affine real conic `x² + y² = 1` has order two, while its base change to `ℂ` is `𝔾_m`,
whose Picard group is trivial.

This gives the injectivity of `Pic(X)` into the `k`-points of the relative Picard sheaf,
in particular for curves without rational points.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3 (flat base change).
* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.2.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Module TensorProduct

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (.of k)} {fY : Y ⟶ Spec (.of K)} {g : Y ⟶ X}
  (H : IsPullback g fY fX (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  [IsIntegral X] [UniversallyClosed fX] [QuasiSeparated fX]

include H in
private theorem exists_nonzero_unitHom_of_pullback_eq_one (L : InvertibleSheaf X)
    (hL : pullback g (mk L) = 1) : ∃ s : 𝟙_ X.Modules ⟶ L.obj, s ≠ 0 := by
  let : X.Over (Spec (.of k)) := ⟨fX⟩
  let : Y.Over (Spec (.of K)) := ⟨fY⟩
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace fX
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated fX
  have hg : Surjective g := MorphismProperty.of_isPullback H.flip inferInstance
  have : Nonempty Y := ⟨Classical.choose (hg.surj (Classical.arbitrary X))⟩
  obtain ⟨e⟩ := mk_eq_one_iff.mp (by rwa [pullback_mk] at hL)
  have : Nontrivial (Scheme.Modules.Cohomology (InvertibleSheaf.trivial Y).obj 0) :=
    Module.nontrivial_of_finrank_pos (R := Γ(Y, ⊤)) (by simp)
  let eL := linearEquivTensorCohomologyZeroPullback (R := k) (R' := K)
    (X := X) (Y := Y) H L.obj
  let eT := Scheme.Modules.cohomologyBaseLinearEquivOfIso K
    (e ≪≫ (InvertibleSheaf.trivialObjIsoUnit Y).symm) 0
  have : Nontrivial (K ⊗[k] Scheme.Modules.Cohomology L.obj 0) :=
    (eL.trans eT).toEquiv.nontrivial
  have : Nontrivial (Scheme.Modules.Cohomology L.obj 0) := by
    by_contra h
    have := not_nontrivial_iff_subsingleton.mp h
    exact not_subsingleton (K ⊗[k] Scheme.Modules.Cohomology L.obj 0) inferInstance
  obtain ⟨x, hx⟩ := exists_ne (0 : Scheme.Modules.Cohomology L.obj 0)
  refine ⟨L.obj.unitHomEquivTop.symm (Scheme.Modules.cohomologyZeroEquiv L.obj x), ?_⟩
  intro hz
  have := congrArg L.obj.unitHomEquivTop hz
  simp only [Equiv.apply_symm_apply, Scheme.Modules.unitHomEquivTop_zero] at this
  exact hx (by simpa using this)

include H in
/-- **Line-bundle classes are detected after any extension of the base field.** Let `X` be
integral, universally closed and quasi-separated over `k` (for instance proper), and let
`X_K = X ×_k K`. A line bundle on `X` whose pullback to `X_K` is trivial is trivial.
No dimension, smoothness, geometric integrality, rational-point or cohomological finiteness
assumption is needed. -/
theorem pullback_injective : Function.Injective (pullback g) := by
  suffices key : ∀ a : LineBundleClass X, pullback g a = 1 → a = 1 by
    intro a b hab
    exact mul_inv_eq_one.mp (key _ (by rw [pullback_mul, pullback_inv, hab, mul_inv_cancel]))
  intro a ha
  obtain ⟨L, rfl⟩ := mk_surjective a
  let _ : TauCeti.SheafOfModules.IsInvertible (R := X.ringCatSheaf) L.obj := L.property
  have : L.obj.IsLocallyFree := TauCeti.SheafOfModules.IsInvertible.isLocallyFree L.obj
  have : _root_.SheafOfModules.IsFiniteType.{u, u, u}
      (R := X.ringCatSheaf) L.obj := by
    obtain ⟨q, hq⟩ := L.property.exists_isInvertible
    refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
    refine { isFiniteType := fun i ↦ ?_ }
    have := hq.basisSubsingleton i
    exact ⟨Finite.of_subsingleton⟩
  obtain ⟨s, hs⟩ := exists_nonzero_unitHom_of_pullback_eq_one H L ha
  have hdual : pullback g (mk L.dual) = 1 := by
    rw [← inv_mk, pullback_inv, ha, inv_one]
  obtain ⟨t, ht⟩ := exists_nonzero_unitHom_of_pullback_eq_one H L.dual hdual
  let eD : L.dual.obj ≅ (ihom L.obj).obj (𝟙_ X.Modules) :=
    eqToIso (InvertibleSheaf.dual_obj L)
  let β : L.dual.obj ⟶ 𝟙_ X.Modules :=
    eD.hom ≫ (Scheme.Modules.dualHomUnitEquiv L.obj).symm s
  have hβ : β ≠ 0 := by
    intro hz
    apply hs
    have hz' : (Scheme.Modules.dualHomUnitEquiv L.obj).symm s = 0 := by
      apply (cancel_epi eD.hom).mp
      simpa only [β, comp_zero] using hz
    have := congrArg (Scheme.Modules.dualHomUnitEquiv L.obj) hz'
    simpa only [β, Equiv.apply_symm_apply, Scheme.Modules.dualHomUnitEquiv_zero] using this
  have : Mono β := L.dual.mono_of_ne_zero_to_unit β hβ
  have hcomp : t ≫ β ≠ 0 := by
    intro hz
    apply ht
    exact (cancel_mono β).mp (hz.trans (zero_comp).symm)
  have hfield := isField_of_universallyClosed k fX
  let r := (Scheme.Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)).symm (End.of (t ≫ β))
  have hr : r ≠ 0 := by
    intro hz
    apply hcomp
    have := congrArg (Scheme.Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)) hz
    simpa only [r, RingEquiv.apply_symm_apply, map_zero, End.ext_iff, End.zero_asHom] using this
  have hu : IsUnit (End.of (t ≫ β)) := by
    rw [← (Scheme.Modules.globalSectionsActionRingEquiv (𝟙_ X.Modules)).apply_symm_apply
      (End.of (t ≫ β))]
    let _ := hfield.toField
    exact (isUnit_iff_ne_zero.mpr hr).map _
  have : IsIso (t ≫ β) := (isUnit_iff_isIso _).mp hu
  have : Epi β := epi_of_epi t β
  have : IsIso β := isIso_of_mono_of_epi β
  have : mk L.dual = 1 := mk_eq_one_iff.mpr ⟨asIso β⟩
  simpa only [← inv_mk, inv_eq_one] using this

end

end TauCeti.AlgebraicGeometry.LineBundleClass
