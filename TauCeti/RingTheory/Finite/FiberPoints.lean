/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Points of a finite algebra over a rational point

Let `f : A →ₐ[k] B` be the coordinate map of a morphism of affine `k`-schemes
`Spec B → Spec A`, and let `y : A →ₐ[k] k` be a `k`-point of `Spec A`. A point
`x : B →ₐ[k] Ω` lies over `y` when `x.comp f = (Algebra.ofId k Ω).comp y`. These points are
exactly the points of the fiber algebra `B ⧸ (ker y) B`, the coordinate ring of the
scheme-theoretic fiber `Spec B ×_{Spec A} Spec k` (`AlgHom.fiberPointsEquiv`).

When `f` is finite the fiber is a finite `k`-scheme, and points over `y` are algebraic:

* every value of a point over `y` is integral over `k`, already when `f` is only integral;
* the image of a point over `y` is a finite `k`-algebra, so for fields `k` and `Ω` it is a finite
  field extension of `k` (a residue field of the fiber) embedded in `Ω`;
* over a field `k` and for a domain `Ω`, there are finitely many points over `y`, at most the
  `k`-dimension of the fiber algebra.

No algebraic closure of `k` is assumed to embed in `Ω`; for instance `Ω = k` is allowed.
Finiteness of `f`, rather than finite type, is essential: for `f` the inclusion `k → k[t]` and the
rational number field `k = ℚ`, evaluation of `t` at a transcendental element of `ℚ_ℓ` is a point
over the unique point of `Spec ℚ` whose value is not algebraic.

Applied to a finite map of conjugacy quotients of affine groups, they show that a point of the
source quotient whose image is rational is algebraic, as in Kisin–Zhou's comparison of Frobenius
conjugacy classes.

## Main declarations

* `AlgHom.comp_eq_ofId_comp_iff_map_ker_le`: a point lies over `y` iff its kernel contains the
  fiber ideal.
* `AlgHom.fiberPointsEquiv`: points over `y` are the points of the fiber algebra.
* `AlgHom.isIntegral_apply_of_comp_eq`: values of points over `y` are integral over `k` when
  `f` is integral.
* `AlgHom.Finite.finite_quotient_map_ker`: the fiber algebra of a finite map is a finite
  `k`-module.
* `AlgHom.Finite.finite_range_of_comp_eq`: the image of a point over `y` is a finite `k`-module.
* `AlgHom.Finite.finite_setOf_comp_eq`, `AlgHom.Finite.ncard_setOf_comp_eq_le`: over a field,
  a finite map has finitely many points with values in a domain over `y`, at most the dimension
  of the fiber algebra.

## References

* M. Kisin, R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945v2, §5.3.2 and §5.3.6.
-/

public section

open Module

namespace AlgHom

section CommRing

variable {k A B Ω : Type*} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing Ω] [Algebra k Ω]

/-- A point `x` of `B` lies over the `k`-point `y` of `A` along `f` exactly when its kernel
contains the fiber ideal `(ker y) B`. -/
theorem comp_eq_ofId_comp_iff_map_ker_le {f : A →ₐ[k] B} {y : A →ₐ[k] k} {x : B →ₐ[k] Ω} :
    x.comp f = (Algebra.ofId k Ω).comp y ↔ (RingHom.ker y).map f ≤ RingHom.ker x := by
  rw [Ideal.map_le_iff_le_comap]
  refine ⟨fun h a ha ↦ ?_, fun h ↦ AlgHom.ext fun a ↦ ?_⟩
  · simpa [RingHom.mem_ker.mp ha] using DFunLike.congr_fun h a
  · have hmem : a - algebraMap k A (y a) ∈ RingHom.ker y := by
      simp [RingHom.mem_ker]
    simpa [sub_eq_zero] using RingHom.mem_ker.mp (h hmem)

/-- The points of `B` lying over the `k`-point `y` of `A` along `f` are the points of the fiber
algebra `B ⧸ (ker y) B`, the coordinate ring of the scheme-theoretic fiber of `Spec B → Spec A`
over `y`. -/
noncomputable def fiberPointsEquiv (f : A →ₐ[k] B) (y : A →ₐ[k] k) :
    {x : B →ₐ[k] Ω // x.comp f = (Algebra.ofId k Ω).comp y} ≃
      (B ⧸ (RingHom.ker y).map f →ₐ[k] Ω) where
  toFun x := Ideal.Quotient.liftₐ _ x.1 fun _ hb ↦
    RingHom.mem_ker.mp (comp_eq_ofId_comp_iff_map_ker_le.mp x.2 hb)
  invFun g := ⟨g.comp (Ideal.Quotient.mkₐ k _), comp_eq_ofId_comp_iff_map_ker_le.mpr fun b hb ↦ by
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem.mpr hb]⟩
  left_inv x := Subtype.ext (Ideal.Quotient.liftₐ_comp _ _ _)
  right_inv g := Ideal.Quotient.algHom_ext k (Ideal.Quotient.liftₐ_comp _ _ _)

@[simp]
theorem fiberPointsEquiv_apply_mk (f : A →ₐ[k] B) (y : A →ₐ[k] k)
    (x : {x : B →ₐ[k] Ω // x.comp f = (Algebra.ofId k Ω).comp y}) (b : B) :
    fiberPointsEquiv f y x (Ideal.Quotient.mk _ b) = x.1 b := by
  simp only [fiberPointsEquiv, Equiv.coe_fn_mk, Ideal.Quotient.liftₐ_apply]
  exact Ideal.Quotient.lift_mk _ _ _

@[simp]
theorem coe_fiberPointsEquiv_symm_apply (f : A →ₐ[k] B) (y : A →ₐ[k] k)
    (g : B ⧸ (RingHom.ker y).map f →ₐ[k] Ω) :
    ((fiberPointsEquiv f y).symm g : B →ₐ[k] Ω) = g.comp (Ideal.Quotient.mkₐ k _) :=
  (rfl)

/-- If `f` is integral, every value of a point lying over a `k`-point of `A` along `f` is
integral over `k`: points over a rational point are algebraic. -/
theorem isIntegral_apply_of_comp_eq {f : A →ₐ[k] B} {y : A →ₐ[k] k} (x : B →ₐ[k] Ω)
    (hf : f.toRingHom.IsIntegral) (h : x.comp f = (Algebra.ofId k Ω).comp y) (b : B) :
    IsIntegral k (x b) := by
  have hcomp : x.toRingHom.comp f.toRingHom = (algebraMap k Ω).comp y.toRingHom :=
    RingHom.ext fun a ↦ DFunLike.congr_fun h a
  have hb := (hf b).map x.toRingHom
  rw [hcomp] at hb
  simpa [IsIntegral] using RingHom.isIntegralElem.of_comp y.toRingHom (algebraMap k Ω) hb

namespace Finite

/-- If `f` is finite, a surjective point `x` of `B` lying over a `k`-point of `A` exhibits its
target as a finite `k`-module. -/
theorem finite_of_surjective_of_comp_eq {f : A →ₐ[k] B} {y : A →ₐ[k] k} {x : B →ₐ[k] Ω}
    (hf : f.Finite) (hx : Function.Surjective x) (h : x.comp f = (Algebra.ofId k Ω).comp y) :
    Module.Finite k Ω := by
  have hxf : (x.comp f).Finite := (AlgHom.Finite.of_surjective x hx).comp hf
  rw [h] at hxf
  have hofId := AlgHom.Finite.of_comp_finite hxf
  rw [AlgHom.Finite, AlgHom.toRingHom_eq_coe, Algebra.toRingHom_ofId] at hofId
  exact RingHom.finite_algebraMap.mp hofId

/-- The fiber algebra `B ⧸ (ker y) B` of a finite map `f` over a `k`-point `y` is a finite
`k`-module: the fiber is a finite `k`-scheme. -/
theorem finite_quotient_map_ker {f : A →ₐ[k] B} (hf : f.Finite) (y : A →ₐ[k] k) :
    Module.Finite k (B ⧸ (RingHom.ker y).map f) :=
  hf.finite_of_surjective_of_comp_eq (Ideal.Quotient.mkₐ_surjective k _)
    (comp_eq_ofId_comp_iff_map_ker_le.mpr (Ideal.Quotient.mkₐ_ker k _).ge)

/-- If `f` is finite, the image of a point lying over a `k`-point of `A` along `f` is a finite
`k`-module. For fields `k` and `Ω` it is a finite field extension of `k`, a residue field of the
fiber, through which the point factors. -/
theorem finite_range_of_comp_eq {f : A →ₐ[k] B} {y : A →ₐ[k] k} {x : B →ₐ[k] Ω}
    (hf : f.Finite) (h : x.comp f = (Algebra.ofId k Ω).comp y) : Module.Finite k x.range :=
  hf.finite_of_surjective_of_comp_eq x.rangeRestrict_surjective <| AlgHom.ext fun a ↦
    Subtype.ext (by simpa using DFunLike.congr_fun h a)

end Finite

end CommRing

namespace Finite

variable {k A B Ω : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
  [CommRing Ω] [IsDomain Ω] [Algebra k Ω]

/-- Over a field `k`, a finite map `f` has only finitely many points with values in a domain
lying over a given `k`-point of `A`. -/
theorem finite_setOf_comp_eq {f : A →ₐ[k] B} (hf : f.Finite) (y : A →ₐ[k] k) :
    {x : B →ₐ[k] Ω | x.comp f = (Algebra.ofId k Ω).comp y}.Finite := by
  have := hf.finite_quotient_map_ker y
  exact Set.finite_coe_iff.mp (_root_.Finite.of_equiv _ (fiberPointsEquiv f y).symm)

/-- Over a field `k`, the number of points with values in a domain lying over a `k`-point `y` of
`A` along a finite map `f` is at most the `k`-dimension of the fiber algebra `B ⧸ (ker y) B`. -/
theorem ncard_setOf_comp_eq_le {f : A →ₐ[k] B} (hf : f.Finite) (y : A →ₐ[k] k) :
    {x : B →ₐ[k] Ω | x.comp f = (Algebra.ofId k Ω).comp y}.ncard ≤
      finrank k (B ⧸ (RingHom.ker y).map f) := by
  have := hf.finite_quotient_map_ker y
  rw [← Nat.card_coe_set_eq]
  exact (Nat.card_congr (fiberPointsEquiv f y)).trans_le (card_algHom_le_finrank k _ Ω)

end Finite

end AlgHom
