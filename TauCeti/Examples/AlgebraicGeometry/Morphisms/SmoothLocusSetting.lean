/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Dense
public import Mathlib.Algebra.DualNumber
import TauCeti.RingTheory.Smooth.SeparablePoint

/-!
# Checks for the setting of Nash blowups

The setting of the Nash blowup is a reduced scheme `X` locally of finite type over a field `k`
whose smooth locus is dense; by
`AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_iff_geometricallyReduced` this says that `X` is
geometrically reduced.

* For an inseparable finite field extension `K / k`, such as `k(t ^ (1 / p))` over `𝔽_p(t)`, the
  scheme `Spec K` is reduced (a field), but its smooth locus over `k` is empty, so it is not
  geometrically reduced and is excluded by the setting.
* `Spec k[ε]/(ε²)` is not reduced, so it is excluded; its reduction `Spec k` is smooth over `k`,
  so its smooth locus is everything.
-/

public section

open AlgebraicGeometry CategoryTheory

universe u

namespace TauCeti.SmoothLocusSettingExample

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- A field extension `K / k` with `Spec K ⟶ Spec k` smooth is separable: the residue field at a
maximal ideal of a smooth `k`-algebra can be chosen separable, and `K` has only `⊥`. -/
private theorem isSeparable_of_smooth
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K)))] : Algebra.IsSeparable k K := by
  have : Algebra.Smooth k K :=
    RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff (P := @Smooth) |>.mp ‹_›)
  obtain ⟨m, hm, -, hsep⟩ := TauCeti.Algebra.Smooth.exists_isMaximal_isSeparable k K
  obtain rfl : m = ⊥ := Ideal.eq_bot_of_prime m
  exact AlgEquiv.Algebra.isSeparable (AlgEquiv.quotientBot k K)

variable [Module.Finite k K]

/-- `Spec K ⟶ Spec k` is locally of finite presentation for a finite extension `K / k`. -/
instance locallyOfFinitePresentation_specMap :
    LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finitePresentation_algebraMap.mpr
    (Algebra.FinitePresentation.of_finiteType.mp inferInstance))

/-- **Check.** For an inseparable finite field extension `K / k`, the smooth locus of `Spec K` over
`k` is empty. -/
theorem smoothLocus_eq_bot (hK : ¬ Algebra.IsSeparable k K) :
    (Spec.map (CommRingCat.ofHom (algebraMap k K))).smoothLocus = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ hK ?_
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    refine Scheme.Hom.smoothLocus_eq_top_iff.mp (eq_top_iff.mpr fun y _ ↦ ?_)
    rwa [Subsingleton.elim y x]
  exact isSeparable_of_smooth k K

/-- **Check.** For an inseparable finite field extension `K / k`, the reduced scheme `Spec K` is not
geometrically reduced over `k`: its smooth locus is empty, hence not dense. -/
theorem not_geometricallyReduced (hK : ¬ Algebra.IsSeparable k K) :
    ¬ GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  rw [← Scheme.Hom.dense_smoothLocus_iff_geometricallyReduced, smoothLocus_eq_bot k K hK]
  simp

end TauCeti.SmoothLocusSettingExample

namespace TauCeti.SmoothLocusSettingExample

variable (k : Type u) [Field k]

-- **Check.** `Spec k[ε]/(ε²)` is not reduced: `ε` is a nonzero nilpotent.
example : ¬ IsReduced (Spec (.of (DualNumber k))) := fun h ↦ by
  have : _root_.IsReduced (DualNumber k) := (affine_isReduced_iff (.of (DualNumber k))).mp h
  have h0 := congrArg TrivSqZeroExt.snd (IsReduced.eq_zero (DualNumber.eps : DualNumber k)
    ⟨2, by simp [pow_two]⟩)
  simp at h0

-- **Check.** The reduction `Spec k` of `Spec k[ε]/(ε²)` has smooth locus everything over `k`.
example : (Spec.map (𝟙 (CommRingCat.of k))).smoothLocus = ⊤ :=
  Scheme.Hom.smoothLocus_eq_top _

end TauCeti.SmoothLocusSettingExample
