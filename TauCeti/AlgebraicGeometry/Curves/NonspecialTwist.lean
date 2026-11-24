/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.LineBundle.Pullback
public import TauCeti.AlgebraicGeometry.LineBundle.TensorProduct
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
import TauCeti.AlgebraicGeometry.Curves.Cohomology.Basic
import TauCeti.AlgebraicGeometry.Curves.HighDegree
import TauCeti.AlgebraicGeometry.LineBundle.PointSubtraction
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.EulerCharacteristic
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
import TauCeti.AlgebraicGeometry.LineBundle.BaseChange
import TauCeti.AlgebraicGeometry.LineBundle.GroundFieldSection
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RationalPoint
import TauCeti.AlgebraicGeometry.RationalPoint.Basic
import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero

/-!
# Ground-field twists with one section and vanishing first cohomology

On a smooth proper geometrically connected curve over a separably closed field, a line bundle
after any field extension can be twisted by a line bundle from the original curve to have one
global section and vanishing first cohomology. The one-step theorem
`exists_groundField_twist_step` lowers any positive section dimension by one while preserving
vanishing first cohomology.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open Module (finrank)
open AlgebraicGeometry.Scheme.Modules MonoidalClosed
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry.InvertibleSheaf

universe u

noncomputable section

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [GeometricallyConnected (X ↘ Spec (.of k))]

private theorem exists_eulerDegree_eq_nat (n : ℕ) :
    ∃ M : InvertibleSheaf X, M.eulerDegree k = n := by
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  obtain ⟨hI, hDVR, hcoheight, -, -⟩ := high_degree_hypotheses_of_smooth (k := k) (X := X)
  have := hI
  have := hDVR
  have : Fact (∀ x : X, Order.coheight x ≤ 1) := ⟨hcoheight⟩
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have : X.IsCurveOver k := { topologicalKrullDim_eq_one := hdim }
  have : IsNoetherian X := Scheme.IsCurveOver.isNoetherian k X
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  obtain ⟨⟨p, hp⟩⟩ := (Scheme.Hom.denseRange_rationalSections (X ↘ Spec (.of k))).nonempty
  let x : CodimensionOnePoint X :=
    ⟨p (IsLocalRing.closedPoint k), Scheme.IsCurveOver.coheight_section_eq_one k hp⟩
  obtain ⟨a, ha⟩ := SchemeWeilDivisor.eulerDegreeHom_surjective k (x₀ := x)
    (residueDegree_eq_one_of_section hp (IsLocalRing.closedPoint k)) (n : ℤ)
  obtain ⟨M, hM⟩ := LineBundleClass.mk_surjective a.toMul
  rw [LineBundleClass.eulerDegreeHom_apply, ← hM, LineBundleClass.eulerDegree_mk] at ha
  exact ⟨M, ha⟩

private theorem exists_positive_nonspecial_twist (K : Type u) [Field K] [Algebra k K]
    (L : InvertibleSheaf
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k)))) :
    let _ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨Limits.pullback.fst _ _⟩
    ∃ M : InvertibleSheaf X,
      0 < finrank K (Scheme.Modules.Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) ∧
      Subsingleton (Scheme.Modules.Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 1) := by
  let f := X ↘ Spec (.of k)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := Limits.pullback g f
  let _ : Y.Over (Spec (.of K)) := ⟨Limits.pullback.fst g f⟩
  have : IsProper (Y ↘ Spec (.of K)) := inferInstanceAs (IsProper (Limits.pullback.fst g f))
  have : SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.fst g f))
  have : GeometricallyConnected (Y ↘ Spec (.of K)) :=
    inferInstanceAs (GeometricallyConnected (Limits.pullback.fst g f))
  have := SmoothOfRelativeDimension.smooth 1 (Y ↘ Spec (.of K))
  have : IsIntegral Y := GeometricallyIntegral.isIntegral_of_subsingleton (Y ↘ Spec (.of K))
  let genus := finrank K (Scheme.Modules.Cohomology (trivial Y).obj 1)
  obtain ⟨M, hM⟩ := exists_eulerDegree_eq_nat (k := k) (X := X)
    (2 * (genus : ℤ) - L.eulerDegree K).toNat
  let N := tensorProduct L ((pullback (Limits.pullback.snd g f)).obj M)
  have hdegree : N.eulerDegree K = L.eulerDegree K + M.eulerDegree k := by
    dsimp only [N]
    rw [← LineBundleClass.eulerDegree_mk]
    rw [LineBundleClass.mk_tensorProduct, LineBundleClass.eulerDegree_mul_of_smooth,
      LineBundleClass.eulerDegree_mk, LineBundleClass.eulerDegree_mk,
      eulerDegree_pullback (IsPullback.of_hasPullback g f).flip]
  have hlarge : 2 * (genus : ℤ) ≤ N.eulerDegree K := by
    rw [hdegree, hM]
    omega
  have hcanonical : 2 * (genus : ℤ) - 2 < N.eulerDegree K := by omega
  have hzero : (finrank K (Scheme.Modules.Cohomology N.obj 0) : ℤ) =
      N.eulerDegree K + 1 - (genus : ℤ) :=
    finrank_cohomology_zero_eq_eulerDegree_add_one_sub_genus_of_smooth N hcanonical
  refine ⟨M, ?_,
    subsingleton_cohomology_one_of_smooth_of_two_mul_genus_sub_two_lt_eulerDegree N hcanonical⟩
  have hpos : 0 < finrank K (Scheme.Modules.Cohomology N.obj 0) := by omega
  exact hpos

omit [IsProper (X ↘ Spec (.of k))] in
omit [GeometricallyConnected (X ↘ Spec (.of k))] in
/-- On a smooth curve, a positive nonspecial twist by a ground-field line bundle can
be replaced by one with one fewer independent global section, while preserving vanishing
first cohomology. Separatedness, connectedness and properness are not required. -/
theorem exists_groundField_twist_step
    (K : Type u) [Field K] [Algebra k K]
    (L : InvertibleSheaf
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k))))
    (M : InvertibleSheaf X) :
    let _ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨Limits.pullback.fst _ _⟩
    0 < finrank K (Cohomology
      (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) →
    Subsingleton (Cohomology
      (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 1) →
    ∃ M' : InvertibleSheaf X,
      finrank K (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M')).obj 0) + 1 =
        finrank K (Cohomology
          (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) ∧
      Subsingleton (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M')).obj 1) := by
  let f := X ↘ Spec (.of k)
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := Limits.pullback g f
  let c : Y ⟶ X := Limits.pullback.snd g f
  let _ : Y.Over (Spec (.of K)) := ⟨Limits.pullback.fst g f⟩
  have : SmoothOfRelativeDimension 1 (Y ↘ Spec (.of K)) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (Limits.pullback.fst g f))
  have : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let N := tensorProduct L ((pullback c).obj M)
  dsimp only
  intro hpos hvan
  have : FiniteDimensional K (Cohomology N.obj 0) := Module.finite_of_finrank_pos hpos
  have := SmoothOfRelativeDimension.smooth 1 f
  obtain ⟨φ, p, hpφ⟩ := exists_groundField_section_avoiding_image (X := X) K N
    (Module.nontrivial_of_finrank_pos hpos)
  have := _root_.AlgebraicGeometry.isClosedImmersion_of_comp_eq_id f p.val p.property
  let q := baseChangeSection f p.val p.property (Over.mk g)
  have hq : q ≫ (Y ↘ Spec (.of K)) = 𝟙 _ := baseChangeSection_fst f p.val p.property _
  have := _root_.AlgebraicGeometry.isClosedImmersion_of_comp_eq_id (Y ↘ Spec (.of K)) q hq
  have : SmoothOfRelativeDimension 1 ((⊤ : X.Opens).ι ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have : SmoothOfRelativeDimension 1 ((⊤ : Y.Opens).ι ≫ (Y ↘ Spec (.of K))) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) _)
  have hI := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_comp_eq_id
    (f := f) p.val p.property ⊤ (Set.subset_univ _)).isEffectiveCartier
  have hJ := (Scheme.Hom.isRelativeEffectiveCartier_ker_of_comp_eq_id
    (f := Y ↘ Spec (.of K)) q hq ⊤ (Set.subset_univ _)).isEffectiveCartier
  have hker : q.ker = p.val.ker.comap c :=
    (IsPullback.of_hasPullback g f).flip.ker_eq_comap_of_comp_eq_id p.property hq
      (baseChangeSection_snd f p.val p.property _)
  have hpull : LineBundleClass.pullback c (LineBundleClass.mk hI.toInvertibleSheaf) =
      LineBundleClass.mk hJ.toInvertibleSheaf := by
    rw [hI.pullback_mk_toInvertibleSheaf (hI.comap c), LineBundleClass.mk_eq_mk_iff]
    exact ⟨eqToIso ((hI.comap c).toInvertibleSheaf_obj.trans
      ((congrArg Scheme.IdealSheafData.sheaf hker.symm).trans hJ.toInvertibleSheaf_obj.symm))⟩
  let M' := tensorProduct M hI.toInvertibleSheaf
  have hclass : LineBundleClass.mk (tensorProduct L ((pullback c).obj M')) =
      LineBundleClass.mk (tensorProduct N hJ.toInvertibleSheaf) := by
    simp only [M', N, LineBundleClass.mk_tensorProduct, ← LineBundleClass.pullback_mk,
      LineBundleClass.pullback_mul, hpull, mul_assoc]
  obtain ⟨comparison⟩ := LineBundleClass.mk_eq_mk_iff.mp hclass
  let e : (tensorProduct L ((pullback c).obj M')).obj ≅ N.obj ⊗ q.ker.sheaf :=
    comparison ≪≫ tensorProductObjIso N hJ.toInvertibleSheaf ≪≫
      whiskerLeftIso N.obj (eqToIso hJ.toInvertibleSheaf_obj)
  have hdrop := finrank_cohomology_zero_tensor_ker_add_one_and_subsingleton
    K N q hq φ hpφ hvan
  refine ⟨M', ?_, ?_⟩
  · rw [finrank_cohomology_congr K e 0]
    exact hdrop.1
  · exact (cohomologyBaseLinearEquivOfIso K e 1).toEquiv.subsingleton_congr.mpr hdrop.2

/-- After any field extension of a separably closed ground field, a line bundle on a smooth
proper geometrically connected curve has a twist defined over the ground field with exactly
one independent global section and vanishing first cohomology. -/
theorem exists_groundField_nonspecial_twist (K : Type u) [Field K] [Algebra k K]
    (L : InvertibleSheaf
      (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (X ↘ Spec (.of k)))) :
    let _ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨Limits.pullback.fst _ _⟩
    ∃ M : InvertibleSheaf X,
      finrank K (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) = 1 ∧
      Subsingleton (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 1) := by
  let _ : (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (X ↘ Spec (.of k))).Over (Spec (.of K)) := ⟨Limits.pullback.fst _ _⟩
  have hreduce (n : ℕ) : ∀ M : InvertibleSheaf X,
      finrank K (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) = n + 1 →
      Subsingleton (Cohomology
        (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 1) →
      ∃ M' : InvertibleSheaf X,
        finrank K (Cohomology
          (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M')).obj 0) = 1 ∧
        Subsingleton (Cohomology
          (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M')).obj 1) := by
    induction n with
    | zero => exact fun M hM hvan ↦ ⟨M, hM, hvan⟩
    | succ n ih =>
      intro M hM hvan
      obtain ⟨M', hstep, hvan'⟩ := exists_groundField_twist_step K L M (by omega) hvan
      exact ih M' (by omega) hvan'
  obtain ⟨M, hpos, hvan⟩ := exists_positive_nonspecial_twist K L
  refine hreduce
    (finrank K (Cohomology
      (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0) - 1) M ?_ hvan
  exact (Nat.sub_add_cancel (by omega : 1 ≤ finrank K (Cohomology
    (tensorProduct L ((pullback (Limits.pullback.snd _ _)).obj M)).obj 0))).symm

end

end TauCeti.AlgebraicGeometry.InvertibleSheaf
