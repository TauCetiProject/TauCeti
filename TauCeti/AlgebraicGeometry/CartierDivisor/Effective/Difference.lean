/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.CartierDivisor.Effective.Basic
public import TauCeti.AlgebraicGeometry.CartierDivisor.Picard
public import TauCeti.AlgebraicGeometry.Scheme.GenericPoint
public import TauCeti.Topology.KrullDimension.Basic

/-!
# Cartier divisors on curves are differences of effective divisors

Let `X` be an integral scheme whose underlying space is Noetherian and all of whose points have
codimension at most one, for instance a proper integral curve over a field, possibly singular.
Every Cartier divisor `D` on `X` is a difference `E - F` of effective Cartier divisors, so every
line bundle on `X` is `𝒪_X(E) ⊗ 𝒪_X(F)⁻¹` with `E` and `F` effective.

The proof chooses, near each point, an affine open `A` on which `D` has an equation `g`, and
writes `g = a / b` with `a` and `b` regular on `A`. The function `b` is the equation on `A` of an
effective Cartier divisor `G`, which is trivial away from the zero locus of `b`. That zero locus is
a locally closed set of points other than the generic point. On a scheme of dimension at most one
such points are closed, so the zero locus is closed in `X`
(`TauCeti.AlgebraicGeometry.Scheme.isClosed_of_isLocallyClosed_of_genericPoint_notMem`). Hence
the divisor `G` can be glued from the equation `b` on `A` and the zero divisor on the complement
of the zero locus
(`TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_restrict_eq_and_restrict_eq_zero`).
The divisor `D + G` has the regular equation `a` on `A`. Finitely many such opens cover `X`, and
adding the corresponding divisors `G` to `D` makes it effective.

Without the dimension hypothesis the zero locus of `b` need not be closed in `X`.

This is the input that reduces additivity of the degree `deg L = χ(L) - χ(𝒪_X)` on a singular
proper curve to twisting by effective Cartier divisors.

## Main results

* `TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_isEffective_restrict_eq`: a nonzero
  rational function which is regular on an open subset `V` is the equation on `V` of an effective
  Cartier divisor.
* `TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_isEffective_sub_eq`: every Cartier
  divisor is a difference of two effective Cartier divisors.
* `TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.closure_effectiveSubmonoid_eq_top`: the effective
  Cartier divisors generate the group of Cartier divisors.
* `TauCeti.AlgebraicGeometry.Scheme.CartierDivisor.exists_isEffective_toLineBundleClass_mul_inv_eq`:
  every line-bundle class is `[𝒪_X(E)] [𝒪_X(F)]⁻¹` with `E` and `F` effective.

## References

* The Stacks Project, Section 33.44, *Degrees on curves*
  ([Tag 0AYQ](https://stacks.math.columbia.edu/tag/0AYQ)), where the degree of an invertible
  module on a proper curve is computed by writing it in terms of effective Cartier divisors.
* Q. Liu, *Algebraic Geometry and Arithmetic Curves*, Section 7.1, on Cartier divisors and
  invertible sheaves.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
  (hX : ∀ x : X, Order.coheight x ≤ 1)
include hX

/-- **The divisor of zeros of a regular function.** On an integral scheme whose underlying space
is Noetherian and all of whose points have codimension at most one, a nonzero rational function
`f` which is regular on an open subset `V`, the image of `b ∈ Γ(X, V)`, is the equation on `V` of
an effective Cartier divisor. -/
theorem exists_isEffective_restrict_eq {V : X.Opens} [Nonempty V] (b : Γ(X, V))
    (f : X.functionFieldˣ) (hf : X.germToFunctionField V b = f) :
    ∃ G : CartierDivisor X, G.IsEffective ∧ G |_ V = rationalUnitClass X V (Additive.ofMul f) := by
  have hb : genericPoint X ∈ X.basicOpen b := by
    by_contra h
    have hb0 : b = 0 := (basicOpen_eq_bot_iff b).mp (Scheme.eq_bot_of_genericPoint_notMem h)
    exact f.ne_zero (by rw [← hf, hb0, map_zero])
  have : Nonempty (X.basicOpen b) := ⟨⟨_, hb⟩⟩
  -- The zero locus `V ∖ D(b)` is closed in `X`, so its complement `W` is open.
  have hdim : topologicalKrullDim X ≤ 1 := by
    rw [TauCeti.topologicalKrullDim_eq_iSup_coheight]
    exact iSup_le fun x ↦ by exact_mod_cast hX x
  have hZ : IsClosed ((V : Set X) \ X.basicOpen b) :=
    Scheme.isClosed_of_isLocallyClosed_of_genericPoint_notMem hdim
      ⟨V, (X.basicOpen b)ᶜ, V.isOpen, (X.basicOpen b).isOpen.isClosed_compl, Set.sdiff_eq _ _⟩
      fun h ↦ h.2 hb
  let W : X.Opens := ⟨((V : Set X) \ X.basicOpen b)ᶜ, hZ.isOpen_compl⟩
  have hVW : V ⊔ W = ⊤ := top_unique fun x _ ↦ by
    by_cases hx : x ∈ V
    · exact Or.inl hx
    · exact Or.inr fun h ↦ hx h.1
  have hle : V ⊓ W ≤ X.basicOpen b := fun x hx ↦ by
    by_contra h
    exact hx.2 ⟨hx.1, h⟩
  have : Nonempty (V ⊓ W : X.Opens) := ⟨⟨_, X.basicOpen_le b hb, fun h ↦ h.2 hb⟩⟩
  -- On the basic open set `D(b)` the function `b` is a unit, so its class vanishes there.
  have hzero : rationalUnitClass X (X.basicOpen b) (Additive.ofMul f) = 0 := by
    have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le b)).op b) :=
      X.toRingedSpace.isUnit_res_basicOpen b
    convert rationalUnitClass_germToFunctionField_eq_zero X (X.basicOpen b) hu.unit using 2
    refine congrArg Additive.ofMul (Units.ext ?_)
    rw [← hf, Units.coe_map, IsUnit.unit_spec]
    exact (X.presheaf.germ_res_apply _ _ _ b).symm
  obtain ⟨G, hGV, hGW⟩ := exists_restrict_eq_and_restrict_eq_zero hVW f
    (by
      rw [← rationalUnitClass_restrict X hle, hzero]
      simp only [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, map_zero])
  refine ⟨G, isEffective_iff_exists.mpr fun x ↦ ?_, hGV⟩
  by_cases hx : x ∈ V
  · refine ⟨f, isLocalEquationAt_of_rationalUnitClass_eq hGV.symm hx, ?_⟩
    rw [← hf, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx]
    exact RingHom.mem_range_self _ _
  · have hxW : x ∈ W := fun h ↦ hx h.1
    have : Nonempty W := ⟨⟨x, hxW⟩⟩
    refine ⟨1, isLocalEquationAt_of_rationalUnitClass_eq (V := W) ?_ hxW, Subring.one_mem _⟩
    rw [hGW, ofMul_one, map_zero]

/-- Near every point, a Cartier divisor `D` becomes effective after adding an effective divisor:
there are an open neighbourhood `A` of `x` and an effective `G` such that `D + G` has a regular
local equation at every point of `A`. -/
private lemma exists_add_isLocalEquationAt_mem_range (D : CartierDivisor X) (x : X) :
    ∃ A : X.Opens, x ∈ A ∧ ∃ G : CartierDivisor X, G.IsEffective ∧ ∀ y ∈ A,
      ∃ f : X.functionFieldˣ, (D + G).IsLocalEquationAt y f ∧
        (f : X.functionField) ∈ (algebraMap (X.presheaf.stalk y) X.functionField).range := by
  obtain ⟨V, -, hxV, g, hg⟩ := D.exists_localEquation_le ⊤ (Opens.mem_top x)
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have : Nonempty A := ⟨⟨x, hxA⟩⟩
  have hgA := rationalUnitClass_eq_of_le (fun _ hy ↦ hAV hy) hg
  have := functionField_isFractionRing_of_isAffineOpen X A hA
  -- Write the equation `g` of `D` on the affine open `A` as a fraction `a / b`.
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, A)) (g : X.functionField)
  have hb0 : X.germToFunctionField A b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨G, hG, hGA⟩ := exists_isEffective_restrict_eq hX b (Units.mk0 _ hb0) rfl
  refine ⟨A, hxA, G, hG, fun y hy ↦ ⟨g * Units.mk0 _ hb0,
    (isLocalEquationAt_of_rationalUnitClass_eq hgA hy).mul
      (isLocalEquationAt_of_rationalUnitClass_eq hGA.symm hy), ?_⟩⟩
  have hga : (g : X.functionField) * X.germToFunctionField A b = X.germToFunctionField A a := by
    rw [RingHom.algebraMap_toAlgebra] at hab
    rw [← hab, div_mul_cancel₀ _ hb0]
  rw [Units.val_mul, Units.val_mk0, hga, ← Scheme.algebraMap_germ_eq_germToFunctionField X hy]
  exact RingHom.mem_range_self _ _

/-- **Cartier divisors on curves are differences of effective divisors.** On an integral scheme
whose underlying space is Noetherian and all of whose points have codimension at most one, for
instance a proper integral curve over a field, every Cartier divisor is `E - F` with `E` and `F`
effective. -/
theorem exists_isEffective_sub_eq (D : CartierDivisor X) :
    ∃ E F : CartierDivisor X, E.IsEffective ∧ F.IsEffective ∧ E - F = D := by
  choose A hxA G hG hloc using exists_add_isLocalEquationAt_mem_range hX D
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (A x : Set X))
    (fun x ↦ (A x).isOpen) fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxA x⟩
  have hsum (t : Finset X) : (∑ z ∈ t, G z).IsEffective :=
    (mem_effectiveSubmonoid _).mp <|
      (effectiveSubmonoid X).sum_mem fun z _ ↦ (mem_effectiveSubmonoid _).mpr (hG z)
  refine ⟨D + ∑ z ∈ s, G z, ∑ z ∈ s, G z, isEffective_iff_exists.mpr fun y ↦ ?_, hsum s,
    add_sub_cancel_right _ _⟩
  classical
  obtain ⟨x, hxs, hy⟩ : ∃ x ∈ s, y ∈ A x := by simpa using hs (Set.mem_univ y)
  obtain ⟨f, hf, hfr⟩ := hloc x y hy
  obtain ⟨e, he, her⟩ := isEffective_iff_exists.mp (hsum (s.erase x)) y
  refine ⟨f * e, ?_, Subring.mul_mem _ hfr her⟩
  rw [← Finset.add_sum_erase s G hxs, ← add_assoc]
  exact hf.mul he

/-- On an integral scheme whose underlying space is Noetherian and all of whose points have
codimension at most one, the effective Cartier divisors generate the group of Cartier divisors. -/
theorem closure_effectiveSubmonoid_eq_top :
    AddSubgroup.closure (effectiveSubmonoid X : Set (CartierDivisor X)) = ⊤ := by
  refine eq_top_iff.mpr fun D _ ↦ ?_
  obtain ⟨E, F, hE, hF, rfl⟩ := exists_isEffective_sub_eq hX D
  exact sub_mem (AddSubgroup.subset_closure ((mem_effectiveSubmonoid E).mpr hE))
    (AddSubgroup.subset_closure ((mem_effectiveSubmonoid F).mpr hF))

/-- **Line bundles on curves come from effective divisors.** On an integral scheme whose
underlying space is Noetherian and all of whose points have codimension at most one, every
line-bundle class is the class of `𝒪_X(E) ⊗ 𝒪_X(F)⁻¹` for effective Cartier divisors `E` and
`F`. -/
theorem exists_isEffective_toLineBundleClass_mul_inv_eq (a : LineBundleClass X) :
    ∃ E F : CartierDivisor X, E.IsEffective ∧ F.IsEffective ∧
      E.toLineBundleClass * F.toLineBundleClass⁻¹ = a := by
  obtain ⟨D, rfl⟩ := toLineBundleClass_surjective a
  obtain ⟨E, F, hE, hF, rfl⟩ := exists_isEffective_sub_eq hX D
  exact ⟨E, F, hE, hF, by rw [sub_eq_add_neg, toLineBundleClass_add, toLineBundleClass_neg]⟩

end Scheme.CartierDivisor

end

end AlgebraicGeometry

end TauCeti
