/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Sphere
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.FiniteDimensional
import TauCeti.LinearAlgebra.Exact

/-!
# Divisor cohomology of point twists on the Riemann sphere

For a point `x` of the Riemann sphere `ℙ¹ = OnePoint ℂ` and an integer `n`, write `𝒪(n)` for the
divisor sheaf of `n • [x]`. Stepping through the six-term point-twist sequence from
`h⁰(𝒪) = 1` and `h¹(𝒪) = 0`, we compute

`h⁰(𝒪(n)) = max(n + 1, 0)` and `h¹(𝒪(n)) = max(-n - 1, 0)`,

so `h⁰ - h¹ = n + 1` for every `n`. In particular `𝒪(-1)` has `(h⁰, h¹) = (0, 0)` and `𝒪(-2)`
has `(h⁰, h¹) = (0, 1)`. Only point twists of a single point are treated; no general
Riemann–Roch theorem is asserted.

At a twist of `-[x]` the newly permitted coefficient of a constant section is its value: in the
constant trivialization the coefficient map `H⁰(𝒪) → ℂ` of the sequence for `𝒪(-[x]) → 𝒪` is
the identity. On `ℙ¹` that sequence has dimensions `0 → 0 → 1 → 1 → 0 → 0`.

The canonical divisor `-2[∞]` (`TauCeti.RiemannSurface.isCanonicalDivisor_neg_two_infty`) is
the case `n = -2`, so `h⁰(K) = h¹(𝒪)`, and every canonical divisor of `ℙ¹` has degree
`2 h¹(𝒪) - 2`.

## Main results

* `TauCeti.RiemannSurface.pointTwistGlobalCoefficient_neg_ofPoint_eq_of_forall_eq`: the
  coefficient of a constant section at a twist of `-[x]` is its value, on any complex curve.
* `TauCeti.RiemannSurface.finiteDimensional_divisorCechCohomology_one_zsmul_ofPoint_sphere`:
  `H¹(𝒪(n))` is finite-dimensional.
* `TauCeti.RiemannSurface.finrank_zsmul_ofPoint_euler_characteristic_sphere`:
  `h⁰(𝒪(n)) - h¹(𝒪(n)) = n + 1`.
* `TauCeti.RiemannSurface.finrank_divisorSheaf_zsmul_ofPoint_sphere` and
  `TauCeti.RiemannSurface.finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere`: the closed
  dimension formulas.
* `TauCeti.RiemannSurface.finrank_pointTwist_neg_ofPoint_sphere` and
  `TauCeti.RiemannSurface.pointTwistGlobalCoefficient_neg_ofPoint_bijective_sphere`: the
  six-term sequence of `𝒪(-[x]) → 𝒪`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §§16-17.
-/

public noncomputable section

open CategoryTheory Limits OnePoint Opposite TopologicalSpace
open TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

section Constant

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Evaluation in the constant trivialization.** At a twist of `-[x]`, the newly permitted
coefficient of a global section of `𝒪(-[x] + [x])` with constant value `c` is `c`. -/
theorem pointTwistGlobalCoefficient_neg_ofPoint_eq_of_forall_eq (x : X) (c : ℂ)
    (f : (divisorSheaf (-WeilDivisor.ofPoint x + WeilDivisor.ofPoint x)).obj.obj (op ⊤))
    (hf : ∀ y, (divisorSheafSectionsEquiv _ ⊤ f).1 y = c) :
    pointTwistGlobalCoefficient (-WeilDivisor.ofPoint x) x f = c := by
  have hext : Subtype.val.extend (divisorSheafSectionsEquiv _ ⊤ f).1 (0 : X → ℂ) =
      fun _ ↦ c := by
    funext y
    exact (Subtype.val_injective.extend_apply _ _ (⟨y, trivial⟩ : (⊤ : Opens X))).trans (hf _)
  have hgerm : (divisorSections.toChartGerm _ ⊤ ⟨x, trivial⟩
      (divisorSheafSectionsEquiv _ ⊤ f) : meromorphicGerms ℂ (chartAt ℂ x x)) =
      algebraMap ℂ _ c := by
    rw [← meromorphicGerms.mk_const]
    apply Subtype.ext
    rw [divisorSections.coe_toChartGerm, hext, meromorphicGerms.coe_mk]
    rfl
  rw [pointTwistGlobalCoefficient_apply, divisorSections.pointTwistCoefficient_apply,
    meromorphicGerms.coeff_apply]
  simp only [hgerm]
  have he : -(-(-WeilDivisor.ofPoint x) x - 1) - 1 = (-1 : ℤ) := by
    have h₁ : (WeilDivisor.ofPoint x) x = 1 := WeilDivisor.coeff_ofPoint_self x
    simp [h₁]
  rw [he, mul_comm, ← Algebra.smul_def, map_smul, zpow_neg_one,
    meromorphicGerms.residue_coordinate_inv, smul_eq_mul, mul_one]

variable [IsManifold 𝓘(ℂ) 1 X]

/-- Every scalar is the coefficient of a constant global section at a twist of `-[x]`. -/
theorem pointTwistGlobalCoefficient_neg_ofPoint_surjective (x : X) :
    Function.Surjective (pointTwistGlobalCoefficient (-WeilDivisor.ofPoint x) x) := fun c ↦
  ⟨(divisorSheafSectionsEquiv _ ⊤).symm ⟨(fun _ : X ↦ c) ∘ Subtype.val,
      comp_val_mem_divisorSections fun _ _ ↦
        (isDivisorSectionAt_iff_of_eq_zero (by simp)).2 contMDiffAt_const⟩,
    pointTwistGlobalCoefficient_neg_ofPoint_eq_of_forall_eq x c _ fun _ ↦ by
      rw [LinearEquiv.apply_symm_apply]
      rfl⟩

end Constant

/-- The structure sheaf of the Riemann sphere has one-dimensional global sections:
`h⁰(𝒪) = 1` on `ℙ¹`. -/
theorem finrank_divisorSheaf_zero_sphere :
    Module.finrank ℂ ((divisorSheaf (0 : WeilDivisor (OnePoint ℂ))).obj.obj (op ⊤)) = 1 := by
  exact (((sheafToPresheaf _ _).mapIso (divisorSheafZeroIso (OnePoint ℂ))).app
    (op ⊤)).toLinearEquiv.finrank_eq.trans
      (holomorphicStructureSheafModules.finrank_globalSections 𝓘(ℂ) (OnePoint ℂ))

section Sphere

variable (x : OnePoint ℂ)

private theorem zsmul_ofPoint_add_one (n : ℤ) :
    (n + 1) • WeilDivisor.ofPoint x = n • WeilDivisor.ofPoint x + WeilDivisor.ofPoint x := by
  rw [add_zsmul, one_zsmul]

/-- The first cohomology of `𝒪(n • [x])` on `ℙ¹` is finite-dimensional, stepping from
`h¹(𝒪) = 0` through point twists in both directions. -/
instance finiteDimensional_divisorCechCohomology_one_zsmul_ofPoint_sphere (n : ℤ) :
    FiniteDimensional ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) := by
  induction n using Int.induction_on with
  | zero =>
    rw [zero_zsmul]
    have := ModuleCat.isZero_iff_subsingleton.1 isZero_divisorCechCohomology_zero_one_sphere
    infer_instance
  | succ i ih =>
    rw [zsmul_ofPoint_add_one]
    exact (finiteDimensional_divisorCechCohomology_one_add_point_iff _ x).2 ih
  | pred i ih =>
    refine (finiteDimensional_divisorCechCohomology_one_add_point_iff _ x).1 ?_
    rwa [← zsmul_ofPoint_add_one, sub_add_cancel]

/-- **Riemann–Roch for point twists on `ℙ¹`.** `h⁰(𝒪(n • [x])) - h¹(𝒪(n • [x])) = n + 1`. -/
theorem finrank_zsmul_ofPoint_euler_characteristic_sphere (n : ℤ) :
    (Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) : ℤ) -
      Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = n + 1 := by
  induction n using Int.induction_on with
  | zero =>
    rw [zero_zsmul, finrank_divisorSheaf_zero_sphere, finrank_divisorCechCohomology_zero_one_sphere]
    norm_num
  | succ i ih =>
    rw [zsmul_ofPoint_add_one, finrank_pointTwist_euler_characteristic, ih]
  | pred i ih =>
    have h := finrank_pointTwist_euler_characteristic ((-i - 1 : ℤ) • WeilDivisor.ofPoint x) x
    rw [← zsmul_ofPoint_add_one, sub_add_cancel, ih] at h
    omega

/-- `h¹(𝒪(n • [x])) = 0` on `ℙ¹` for `n ≥ 0`: the point-twist maps on `H¹` are surjective. -/
theorem finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere_of_nonneg {n : ℤ} (hn : 0 ≤ n) :
    Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = 0 := by
  lift n to ℕ using hn
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_zsmul]
    exact finrank_divisorCechCohomology_zero_one_sphere
  | succ m ih =>
    rw [Nat.cast_succ, zsmul_ofPoint_add_one]
    have h := LinearMap.finrank_range_le
      (pointTwistCohomologyMap ((m : ℤ) • WeilDivisor.ofPoint x) x 1)
    rw [LinearMap.range_eq_top.2 (pointTwistCohomologyMap_one_surjective _ x), finrank_top,
      ih] at h
    omega

/-- `h⁰(𝒪(-[x])) = 0` on `ℙ¹`: the coefficient map on the constants `H⁰(𝒪) = ℂ` is
evaluation, which is injective. -/
theorem finrank_divisorSheaf_neg_ofPoint_sphere :
    Module.finrank ℂ ((divisorSheaf (-WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 0 := by
  let f := ((divisorSheafMapOfLE (WeilDivisor.le_add_ofPoint (-WeilDivisor.ofPoint x) x)).hom.app
    (op ⊤)).hom
  have hf : Function.Injective f := divisorSheafMapOfLE_app_injective _ ⊤
  have h₀ := f.finrank_eq_finrank_range_add_finrank_range_of_exact
    (pointTwistGlobalCoefficient _ x) (exact_pointTwist_globalSections_coefficient _ x)
  rw [LinearMap.finrank_range_of_inj hf,
    LinearMap.range_eq_top.2 (pointTwistGlobalCoefficient_neg_ofPoint_surjective x), finrank_top,
    Module.finrank_self] at h₀
  have hmid : Module.finrank ℂ
      ((divisorSheaf (-WeilDivisor.ofPoint x + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 1 := by
    rw [neg_add_cancel]
    exact finrank_divisorSheaf_zero_sphere
  omega

/-- `h⁰(𝒪(n • [x])) = 0` on `ℙ¹` for `n < 0`. -/
theorem finrank_divisorSheaf_zsmul_ofPoint_sphere_of_neg {n : ℤ} (hn : n < 0) :
    Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 0 := by
  have hle : n • WeilDivisor.ofPoint x ≤ -WeilDivisor.ofPoint x := by
    intro y
    by_cases hy : y = x
    · subst hy
      have h₁ : (WeilDivisor.ofPoint y) y = 1 := WeilDivisor.coeff_ofPoint_self y
      simp only [Finsupp.smul_apply, Finsupp.coe_neg, Pi.neg_apply, h₁, smul_eq_mul]
      omega
    · have h₀ : (WeilDivisor.ofPoint x) y = 0 := WeilDivisor.coeff_ofPoint_of_ne hy
      simp [h₀]
  have h := LinearMap.finrank_le_finrank_of_injective
    (f := ((divisorSheafMapOfLE hle).hom.app (op ⊤)).hom) (divisorSheafMapOfLE_app_injective _ ⊤)
  rw [finrank_divisorSheaf_neg_ofPoint_sphere] at h
  omega

/-- **The dimension of `H⁰` of a point twist on `ℙ¹`.** `h⁰(𝒪(n • [x])) = max(n + 1, 0)`. -/
theorem finrank_divisorSheaf_zsmul_ofPoint_sphere (n : ℤ) :
    Module.finrank ℂ ((divisorSheaf (n • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) =
      (n + 1).toNat := by
  have h := finrank_zsmul_ofPoint_euler_characteristic_sphere x n
  rcases le_or_gt 0 n with hn | hn
  · rw [finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere_of_nonneg x hn] at h
    omega
  · rw [finrank_divisorSheaf_zsmul_ofPoint_sphere_of_neg x hn]
    omega

/-- **The dimension of `H¹` of a point twist on `ℙ¹`.** `h¹(𝒪(n • [x])) = max(-n - 1, 0)`. -/
theorem finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere (n : ℤ) :
    Module.finrank ℂ (divisorCechCohomology (n • WeilDivisor.ofPoint x) 1) = (-n - 1).toNat := by
  have h := finrank_zsmul_ofPoint_euler_characteristic_sphere x n
  rw [finrank_divisorSheaf_zsmul_ofPoint_sphere] at h
  omega

/-- `𝒪(-1)` on `ℙ¹` has `(h⁰, h¹) = (0, 0)`. -/
theorem finrank_neg_one_zsmul_ofPoint_sphere :
    Module.finrank ℂ ((divisorSheaf ((-1 : ℤ) • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 0 ∧
      Module.finrank ℂ (divisorCechCohomology ((-1 : ℤ) • WeilDivisor.ofPoint x) 1) = 0 :=
  ⟨finrank_divisorSheaf_zsmul_ofPoint_sphere x _,
    finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere x _⟩

/-- `𝒪(-2)` on `ℙ¹` has `(h⁰, h¹) = (0, 1)`, so its Euler characteristic is `-1 = -2 + 1`. -/
theorem finrank_neg_two_zsmul_ofPoint_sphere :
    Module.finrank ℂ ((divisorSheaf ((-2 : ℤ) • WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 0 ∧
      Module.finrank ℂ (divisorCechCohomology ((-2 : ℤ) • WeilDivisor.ofPoint x) 1) = 1 :=
  ⟨finrank_divisorSheaf_zsmul_ofPoint_sphere x _,
    finrank_divisorCechCohomology_one_zsmul_ofPoint_sphere x _⟩

/-- **The point-twist sequence of `𝒪(-[x]) → 𝒪` on `ℙ¹`.** In the six-term sequence
`0 → H⁰(𝒪(-[x])) → H⁰(𝒪) → ℂ → H¹(𝒪(-[x])) → H¹(𝒪) → 0` the dimensions of the four
cohomology groups are `0`, `1`, `0` and `0`. -/
theorem finrank_pointTwist_neg_ofPoint_sphere :
    Module.finrank ℂ ((divisorSheaf (-WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 0 ∧
      Module.finrank ℂ
        ((divisorSheaf (-WeilDivisor.ofPoint x + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) = 1 ∧
      Module.finrank ℂ (divisorCechCohomology (-WeilDivisor.ofPoint x) 1) = 0 ∧
      Module.finrank ℂ
        (divisorCechCohomology (-WeilDivisor.ofPoint x + WeilDivisor.ofPoint x) 1) = 0 := by
  refine ⟨finrank_divisorSheaf_neg_ofPoint_sphere x, ?_, ?_, ?_⟩
  · rw [neg_add_cancel]
    exact finrank_divisorSheaf_zero_sphere
  · rw [← neg_one_zsmul]
    exact (finrank_neg_one_zsmul_ofPoint_sphere x).2
  · rw [neg_add_cancel]
    exact finrank_divisorCechCohomology_zero_one_sphere

/-- In the sequence of `𝒪(-[x]) → 𝒪` on `ℙ¹`, the coefficient map `H⁰(𝒪) → ℂ` is bijective; by
`pointTwistGlobalCoefficient_neg_ofPoint_eq_of_forall_eq` it is evaluation of constants. -/
theorem pointTwistGlobalCoefficient_neg_ofPoint_bijective_sphere :
    Function.Bijective (pointTwistGlobalCoefficient (-WeilDivisor.ofPoint x) x) := by
  have h := (finrank_pointTwist_neg_ofPoint_sphere x).2.1
  have : FiniteDimensional ℂ
      ((divisorSheaf (-WeilDivisor.ofPoint x + WeilDivisor.ofPoint x)).obj.obj (op ⊤)) :=
    Module.finite_of_finrank_eq_succ h
  have hs := pointTwistGlobalCoefficient_neg_ofPoint_surjective x
  refine ⟨?_, hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [h, Module.finrank_self])).2 hs

end Sphere

/-- On `ℙ¹` the canonical divisor `-2[∞]` (`isCanonicalDivisor_neg_two_infty`) has
`h⁰(K) = h¹(𝒪)`, both being zero. -/
theorem finrank_divisorSheaf_neg_two_infty_eq_finrank_divisorCechCohomology_zero_one :
    Module.finrank ℂ
        ((divisorSheaf ((-2 : ℤ) • WeilDivisor.ofPoint (∞ : OnePoint ℂ))).obj.obj (op ⊤)) =
      Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor (OnePoint ℂ)) 1) := by
  rw [(finrank_neg_two_zsmul_ofPoint_sphere ∞).1, finrank_divisorCechCohomology_zero_one_sphere]

/-- Every canonical divisor of `ℙ¹` has degree `2 h¹(𝒪) - 2`, the value `-2` for analytic
genus zero. -/
theorem IsCanonicalDivisor.degree_eq_two_mul_finrank_sub_two_sphere
    {K : WeilDivisor (OnePoint ℂ)} (hK : IsCanonicalDivisor K) :
    WeilDivisor.degree K =
      2 * (Module.finrank ℂ (divisorCechCohomology (0 : WeilDivisor (OnePoint ℂ)) 1) : ℤ) - 2 := by
  rw [hK.degree_eq_neg_two_of_sphere, finrank_divisorCechCohomology_zero_one_sphere]
  norm_num

end TauCeti.RiemannSurface
