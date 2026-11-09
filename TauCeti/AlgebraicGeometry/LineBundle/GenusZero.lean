/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Effective
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero

/-!
# Line bundles on curves of genus zero

On a proper regular integral curve of genus zero with constant global functions, degree
classifies line bundles up to isomorphism. No rational point is needed for injectivity:
Riemann–Roch makes a degree-zero line bundle effective, and positivity of residue degrees
forces its effective divisor to be zero. A degree-one line bundle identifies the Picard
group with `ℤ`; a rational point supplies such a bundle. Without one the image of degree
may be a proper subgroup of `ℤ`.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter IV, Section 1 (Riemann–Roch).
-/

public section

open CategoryTheory AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry.LineBundleClass

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsIntegral X] [IsProper (X ↘ Spec (.of k))]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]
  [FiniteDimensional k (Scheme.Modules.Cohomology (InvertibleSheaf.trivial X).obj 1)]
  (hdim : ∀ x : X, coheight x ≤ 1)
  (hφ : Function.Surjective (Scheme.Modules.baseRingToGlobalSections k X))
  (hg : X.genus k = 0)

include hdim hφ hg in
/-- On a proper regular integral curve of genus zero with constant global functions, the only
line-bundle class of degree zero is the trivial class. This does not require a rational point.
Use this explicitly: simplification unfolds the genus hypothesis, so this is not a simp rule. -/
theorem eulerDegree_eq_zero_iff_of_genus_eq_zero (a : LineBundleClass X) :
    eulerDegree k a = 0 ↔ a = 1 := by
  refine ⟨fun ha ↦ ?_, fun h ↦ h ▸ eulerDegree_one k⟩
  obtain ⟨L, rfl⟩ := mk_surjective a
  rw [eulerDegree_mk] at ha
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  obtain ⟨D, hD, -, hdeg, hclass⟩ :=
    InvertibleSheaf.exists_nonneg_iso_sheaf_of_genus_le_eulerDegree hdim hφ L
      (by simp only [← Scheme.genus_def, hg, ha, Nat.cast_zero, le_refl])
  have hzero : WeilDivisor.weightedDegree
      (fun x : CodimensionOnePoint X ↦ ((X ↘ Spec (.of k)).residueDegree x : ℤ)) D = 0 := by
    rw [WeilDivisor.weightedDegree_apply, ← SchemeWeilDivisor.relativeDegree_apply]
    exact hdeg.trans ha
  have hD0 : D = 0 := by
    apply (WeilDivisor.weightedDegree_eq_zero_iff_of_pos_on_support hD ?_).mp hzero
    intro x _
    exact_mod_cast Nat.pos_of_ne_zero
      (Scheme.Hom.residueDegree_ne_zero_of_isClosed (X ↘ Spec (.of k))
        (isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hdim x.2))
  simpa only [hD0, SchemeWeilDivisor.toLineBundleClass_zero] using hclass.symm

include hdim hφ hg in
/-- Degree is injective on line-bundle classes of a proper regular integral genus-zero curve
with constant global functions, even when the curve has no rational point. -/
theorem eulerDegree_injective_of_genus_eq_zero :
    Function.Injective (eulerDegree k : LineBundleClass X → ℤ) := by
  intro a b hab
  have : IsNoetherian X := isNoetherian_of_finiteType (X ↘ Spec (.of k))
  have h : eulerDegree k (a * b⁻¹) = 0 := by
    rw [eulerDegree_mul k hdim, eulerDegree_inv k hdim, hab, add_neg_cancel]
  exact mul_inv_eq_one.mp ((eulerDegree_eq_zero_iff_of_genus_eq_zero hdim hφ hg _).mp h)

variable [IsNoetherian X] [hX : Fact (∀ x : X, coheight x ≤ 1)]

include hφ hg in
/-- The degree homomorphism on the Picard group is injective for a proper regular integral
curve of genus zero with constant global functions. -/
theorem eulerDegreeHom_injective_of_genus_eq_zero :
    Function.Injective (eulerDegreeHom k X) := fun _ _ h ↦
  Additive.toMul.injective (eulerDegree_injective_of_genus_eq_zero hX.out hφ hg
    (by simpa only [eulerDegreeHom_apply] using h))

include hφ hg in
/-- The degree-zero Picard group of a proper regular integral genus-zero curve with constant
global functions is trivial, without any rational-point hypothesis. -/
theorem picZero_eq_bot_of_genus_eq_zero : picZero k X = ⊥ :=
  (picZero_eq_ker k X).trans ((AddMonoidHom.ker_eq_bot_iff _).mpr
    (eulerDegreeHom_injective_of_genus_eq_zero hφ hg))

/-- Degree identifies the Picard group of a proper regular integral genus-zero curve with
constant global functions with `ℤ`, provided it has a line-bundle class `a` of degree one.
A rational point supplies such a class via its divisor. -/
noncomputable def picardDegreeEquivOfGenusZero
    (a : LineBundleClass X) (ha : eulerDegree k a = 1) :
    Additive (LineBundleClass X) ≃+ ℤ :=
  AddEquiv.ofBijective (eulerDegreeHom k X) ⟨
    eulerDegreeHom_injective_of_genus_eq_zero hφ hg,
    fun n ↦ ⟨Additive.ofMul (a ^ n), by
      simp only [eulerDegreeHom_apply, toMul_ofMul, eulerDegree_zpow k, ha, mul_one]⟩⟩

/-- The genus-zero Picard-group identification evaluates to Euler-characteristic degree. -/
@[simp]
lemma picardDegreeEquivOfGenusZero_apply (a : LineBundleClass X)
    (ha : eulerDegree k a = 1) (b : Additive (LineBundleClass X)) :
    picardDegreeEquivOfGenusZero hφ hg a ha b = eulerDegree k b.toMul :=
  eulerDegreeHom_apply k b

/-- The inverse genus-zero Picard-group identification sends `n` to the `n`th tensor power
of the chosen degree-one line-bundle class. -/
@[simp]
lemma picardDegreeEquivOfGenusZero_symm_apply (a : LineBundleClass X)
    (ha : eulerDegree k a = 1) (n : ℤ) :
    (picardDegreeEquivOfGenusZero hφ hg a ha).symm n = Additive.ofMul (a ^ n) := by
  apply (picardDegreeEquivOfGenusZero hφ hg a ha).injective
  simp [eulerDegree_zpow k, ha]

end TauCeti.AlgebraicGeometry.LineBundleClass
