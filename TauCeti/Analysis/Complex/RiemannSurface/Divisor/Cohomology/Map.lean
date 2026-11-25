/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Cohomology.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.LinearEquivalence
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.Linear

/-!
# Cohomology maps of divisor inclusions

For divisors `D ≤ E` on a complex curve, the sheaf inclusion `O(D) → O(E)` induces maps
`Hⁿ(O(D)) → Hⁿ(O(E))` on cover-colimit Čech cohomology. These maps are functorial in the
inclusion, and the point-twist cohomology map is the case `E = D + x`.

On a compact Hausdorff complex curve the map on first cohomology is surjective for every
inclusion `D ≤ E`. This follows by adding the points of `E - D` one at a time, since each
point twist is surjective on `H¹` (the point skyscraper has no first Čech cohomology).
Consequently `dim H¹(O(E)) ≤ dim H¹(O(D))`.

## Main definitions and results

* `divisorCechCohomologyMapOfLE`: the map `Hⁿ(O(D)) → Hⁿ(O(E))` induced by `D ≤ E`.
* `divisorCechCohomologyMapOfLE_refl`, `divisorCechCohomologyMapOfLE_comp`: functoriality.
* `pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE`: the point twist is a special case.
* `divisorCechCohomologyMapOfLE_one_surjective`: surjectivity on `H¹`.
* `finrank_divisorCechCohomology_one_le_of_le`: `h¹` is antitone in the divisor.
* `divisorCechCohomologyMeromorphicMul`: the map `Hⁿ(O(D)) → Hⁿ(O(E))` induced by multiplication
  by a meromorphic function, with `divisorCechCohomologyMeromorphicMul_add`, `_sub`,
  `_algebraMap`, `_comp`, `_one`, and its compatibility with the inclusion maps.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §16 and the proof of Theorem 17.6.
-/

public noncomputable section

open CategoryTheory TopologicalSpace
open TauCeti.Topology TauCeti.AlgebraicGeometry
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- The map `Hⁿ(O(D)) → Hⁿ(O(E))` on cover-colimit Čech cohomology induced by the divisor
inclusion `O(D) → O(E)` for `D ≤ E`. -/
def divisorCechCohomologyMapOfLE {D E : WeilDivisor X} (h : D ≤ E) (n : ℕ) :
    divisorCechCohomology D n →ₗ[ℂ] divisorCechCohomology E n :=
  ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map (divisorSheafMapOfLE h).hom).hom

/-- The divisor-inclusion cohomology map is the Čech cohomology functor applied to the native
divisor sheaf inclusion. -/
theorem divisorCechCohomologyMapOfLE_def {D E : WeilDivisor X} (h : D ≤ E) (n : ℕ) :
    divisorCechCohomologyMapOfLE h n =
      ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafMapOfLE h).hom).hom := (rfl)

/-- The cohomology map of the identity inclusion `D ≤ D` is the identity. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_refl (D : WeilDivisor X) (n : ℕ) :
    divisorCechCohomologyMapOfLE (le_refl D) n = LinearMap.id := by
  rw [divisorCechCohomologyMapOfLE_def, divisorSheafMapOfLE_refl]
  exact congrArg ModuleCat.Hom.hom
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_id _)

/-- The cohomology maps of divisor inclusions compose. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_comp {D E F : WeilDivisor X} (hDE : D ≤ E) (hEF : E ≤ F)
    (n : ℕ) :
    divisorCechCohomologyMapOfLE hEF n ∘ₗ divisorCechCohomologyMapOfLE hDE n =
      divisorCechCohomologyMapOfLE (hDE.trans hEF) n := by
  simp only [divisorCechCohomologyMapOfLE_def, ← divisorSheafMapOfLE_comp hDE hEF]
  exact (congrArg ModuleCat.Hom.hom
    ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map_comp _ _)).symm

/-- Pointwise form of `divisorCechCohomologyMapOfLE_comp`. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_comp_apply {D E F : WeilDivisor X} (hDE : D ≤ E)
    (hEF : E ≤ F) (n : ℕ) (c : divisorCechCohomology D n) :
    divisorCechCohomologyMapOfLE hEF n (divisorCechCohomologyMapOfLE hDE n c) =
      divisorCechCohomologyMapOfLE (hDE.trans hEF) n c := by
  rw [← divisorCechCohomologyMapOfLE_comp hDE hEF n, LinearMap.comp_apply]

/-- The point-twist cohomology map is the cohomology map of the inclusion `D ≤ D + x`. -/
theorem pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE (D : WeilDivisor X) (x : X)
    (n : ℕ) :
    pointTwistCohomologyMap D x n =
      divisorCechCohomologyMapOfLE (WeilDivisor.le_add_ofPoint D x) n := by
  rw [pointTwistCohomologyMap_def, divisorCechCohomologyMapOfLE_def]

section Multiplication

variable [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

/-- The map `Hⁿ(O(D)) → Hⁿ(O(E))` on cover-colimit Čech cohomology induced by multiplication by a
meromorphic function `g` whose order is at least `D - E` (`divisorSheafMeromorphicMul`). -/
def divisorCechCohomologyMeromorphicMul {D E : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (n : ℕ) :
    divisorCechCohomology D n →ₗ[ℂ] divisorCechCohomology E n :=
  ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map (divisorSheafMeromorphicMul g hg).hom).hom

/-- The multiplication map on cohomology is the Čech cohomology functor applied to the
multiplication morphism of divisor sheaves. -/
theorem divisorCechCohomologyMeromorphicMul_def {D E : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul g hg n =
      ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) n).map
        (divisorSheafMeromorphicMul g hg).hom).hom := (rfl)

/-- Multiplication by `g₁ - g₂` on cohomology is the difference of the multiplications by `g₁` and
by `g₂`. -/
theorem divisorCechCohomologyMeromorphicMul_sub {D E : WeilDivisor X}
    (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul (g₁ - g₂)
        (fun x ↦ (le_min (hg₁ x) (hg₂ x)).trans ((MeromorphicFunction.order x).map_sub _ _)) n =
      divisorCechCohomologyMeromorphicMul g₁ hg₁ n -
        divisorCechCohomologyMeromorphicMul g₂ hg₂ n := by
  -- `sheafToPresheaf` is additive, and its action on morphisms is `Sheaf.hom` (`ι_map`).
  have hsub : (divisorSheafMeromorphicMul g₁ hg₁ - divisorSheafMeromorphicMul g₂ hg₂).hom =
      (divisorSheafMeromorphicMul g₁ hg₁).hom - (divisorSheafMeromorphicMul g₂ hg₂).hom :=
    (sheafToPresheaf _ _).map_sub
  rw [divisorCechCohomologyMeromorphicMul_def, divisorCechCohomologyMeromorphicMul_def,
    divisorCechCohomologyMeromorphicMul_def, divisorSheafMeromorphicMul_sub g₁ g₂ hg₁ hg₂, hsub,
    Functor.map_sub,
    ModuleCat.hom_sub]

/-- Multiplication by `g₁ + g₂` on cohomology is the sum of the multiplications by `g₁` and by
`g₂`. -/
theorem divisorCechCohomologyMeromorphicMul_add {D E : WeilDivisor X}
    (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul (g₁ + g₂)
        (fun x ↦ (le_min (hg₁ x) (hg₂ x)).trans ((MeromorphicFunction.order x).map_add _ _)) n =
      divisorCechCohomologyMeromorphicMul g₁ hg₁ n +
        divisorCechCohomologyMeromorphicMul g₂ hg₂ n := by
  -- `sheafToPresheaf` is additive, and its action on morphisms is `Sheaf.hom` (`ι_map`).
  have hadd : (divisorSheafMeromorphicMul g₁ hg₁ + divisorSheafMeromorphicMul g₂ hg₂).hom =
      (divisorSheafMeromorphicMul g₁ hg₁).hom + (divisorSheafMeromorphicMul g₂ hg₂).hom :=
    (sheafToPresheaf _ _).map_add
  rw [divisorCechCohomologyMeromorphicMul_def, divisorCechCohomologyMeromorphicMul_def,
    divisorCechCohomologyMeromorphicMul_def, divisorSheafMeromorphicMul_add g₁ g₂ hg₁ hg₂, hadd,
    Functor.map_add, ModuleCat.hom_add]

/-- **Constant multipliers on cohomology.** For `D ≤ E`, multiplication by a constant `c` is `c`
times the inclusion map `Hⁿ(O(D)) → Hⁿ(O(E))`. -/
theorem divisorCechCohomologyMeromorphicMul_algebraMap {D E : WeilDivisor X} (hDE : D ≤ E)
    (c : ℂ) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul (algebraMap ℂ (MeromorphicFunction X) c)
        (sub_le_order_algebraMap hDE c) n = c • divisorCechCohomologyMapOfLE hDE n := by
  rw [divisorCechCohomologyMeromorphicMul_def, divisorSheafMeromorphicMul_algebraMap_hom,
    Functor.map_smul, ModuleCat.hom_smul, divisorCechCohomologyMapOfLE_def]

/-- **Composition on cohomology.** Multiplying by `g₁` and then by `g₂` on cohomology is
multiplication by `g₁ g₂`. -/
@[simp]
theorem divisorCechCohomologyMeromorphicMul_comp {D E F : WeilDivisor X}
    (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((E x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul g₂ hg₂ n ∘ₗ divisorCechCohomologyMeromorphicMul g₁ hg₁ n =
      divisorCechCohomologyMeromorphicMul (g₁ * g₂)
        (fun x ↦ sub_le_order_mul (hg₁ x) (hg₂ x)) n := by
  rw [divisorCechCohomologyMeromorphicMul_def, divisorCechCohomologyMeromorphicMul_def,
    divisorCechCohomologyMeromorphicMul_def, ← ModuleCat.hom_comp, ← Functor.map_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, divisorSheafMeromorphicMul_comp]

/-- Pointwise form of `divisorCechCohomologyMeromorphicMul_comp`. -/
@[simp]
theorem divisorCechCohomologyMeromorphicMul_comp_apply {D E F : WeilDivisor X}
    (g₁ g₂ : MeromorphicFunction X)
    (hg₁ : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₁)
    (hg₂ : ∀ x, ((E x - F x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g₂) (n : ℕ)
    (c : divisorCechCohomology D n) :
    divisorCechCohomologyMeromorphicMul g₂ hg₂ n (divisorCechCohomologyMeromorphicMul g₁ hg₁ n c) =
      divisorCechCohomologyMeromorphicMul (g₁ * g₂)
        (fun x ↦ sub_le_order_mul (hg₁ x) (hg₂ x)) n c := by
  rw [← divisorCechCohomologyMeromorphicMul_comp g₁ g₂ hg₁ hg₂ n, LinearMap.comp_apply]

/-- Multiplication by `g` on cohomology commutes with the inclusion maps in the source. -/
@[simp]
theorem divisorCechCohomologyMeromorphicMul_comp_divisorCechCohomologyMapOfLE
    {D D' E : WeilDivisor X} (hDD' : D ≤ D') (g : MeromorphicFunction X)
    (hg : ∀ x, ((D' x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul g hg n ∘ₗ divisorCechCohomologyMapOfLE hDD' n =
      divisorCechCohomologyMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_right (hDD' x) _)).trans (hg x)) n := by
  rw [divisorCechCohomologyMeromorphicMul_def, divisorCechCohomologyMeromorphicMul_def,
    divisorCechCohomologyMapOfLE_def, ← ModuleCat.hom_comp, ← Functor.map_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, divisorSheafMapOfLE_comp_divisorSheafMeromorphicMul]

/-- Pointwise form of `divisorCechCohomologyMeromorphicMul_comp_divisorCechCohomologyMapOfLE`. -/
@[simp]
theorem divisorCechCohomologyMeromorphicMul_divisorCechCohomologyMapOfLE_apply
    {D D' E : WeilDivisor X} (hDD' : D ≤ D') (g : MeromorphicFunction X)
    (hg : ∀ x, ((D' x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (n : ℕ)
    (c : divisorCechCohomology D n) :
    divisorCechCohomologyMeromorphicMul g hg n (divisorCechCohomologyMapOfLE hDD' n c) =
      divisorCechCohomologyMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_right (hDD' x) _)).trans (hg x)) n c := by
  rw [← divisorCechCohomologyMeromorphicMul_comp_divisorCechCohomologyMapOfLE hDD' g hg n,
    LinearMap.comp_apply]

/-- Multiplication by `g` on cohomology commutes with the inclusion maps in the target. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_comp_divisorCechCohomologyMeromorphicMul
    {D E E' : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (hEE' : E ≤ E')
    (n : ℕ) :
    divisorCechCohomologyMapOfLE hEE' n ∘ₗ divisorCechCohomologyMeromorphicMul g hg n =
      divisorCechCohomologyMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_left (hEE' x) _)).trans (hg x)) n := by
  rw [divisorCechCohomologyMeromorphicMul_def, divisorCechCohomologyMeromorphicMul_def,
    divisorCechCohomologyMapOfLE_def, ← ModuleCat.hom_comp, ← Functor.map_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, divisorSheafMeromorphicMul_comp_divisorSheafMapOfLE]

/-- Pointwise form of `divisorCechCohomologyMapOfLE_comp_divisorCechCohomologyMeromorphicMul`. -/
@[simp]
theorem divisorCechCohomologyMapOfLE_divisorCechCohomologyMeromorphicMul_apply
    {D E E' : WeilDivisor X} (g : MeromorphicFunction X)
    (hg : ∀ x, ((D x - E x : ℤ) : WithTop ℤ) ≤ MeromorphicFunction.order x g) (hEE' : E ≤ E')
    (n : ℕ) (c : divisorCechCohomology D n) :
    divisorCechCohomologyMapOfLE hEE' n (divisorCechCohomologyMeromorphicMul g hg n c) =
      divisorCechCohomologyMeromorphicMul g
        (fun x ↦ (WithTop.coe_le_coe.2 (sub_le_sub_left (hEE' x) _)).trans (hg x)) n c := by
  rw [← divisorCechCohomologyMapOfLE_comp_divisorCechCohomologyMeromorphicMul g hg hEE' n,
    LinearMap.comp_apply]

/-- For `D ≤ E`, multiplication by `1` on cohomology is the inclusion map. -/
@[simp]
theorem divisorCechCohomologyMeromorphicMul_one {D E : WeilDivisor X} (hDE : D ≤ E) (n : ℕ) :
    divisorCechCohomologyMeromorphicMul 1
        (fun x ↦ map_one (algebraMap ℂ (MeromorphicFunction X)) ▸ sub_le_order_algebraMap hDE 1 x)
        n =
      divisorCechCohomologyMapOfLE hDE n := by
  rw [divisorCechCohomologyMeromorphicMul_def, divisorSheafMeromorphicMul_one,
    divisorCechCohomologyMapOfLE_def]

end Multiplication

variable [IsManifold 𝓘(ℂ) 1 X] [CompactSpace X] [T2Space X]

/-- The surjectivity on `H¹` for `D ≤ E`, by induction on the degree of the effective divisor
`E - D`: remove one point of `E - D` at a time, starting from `D`. -/
private theorem divisorCechCohomologyMapOfLE_one_surjective_aux (E : WeilDivisor X) :
    ∀ (k : ℕ) (D : WeilDivisor X) (h : D ≤ E), WeilDivisor.degree (E - D) = k →
      Function.Surjective (divisorCechCohomologyMapOfLE h 1) := by
  intro k
  induction k with
  | zero =>
    intro D h hk
    have hED : E - D = 0 :=
      (WeilDivisor.degree_eq_zero_iff (sub_nonneg.mpr h)).mp (by exact_mod_cast hk)
    obtain rfl : E = D := sub_eq_zero.mp hED
    rw [divisorCechCohomologyMapOfLE_refl]
    exact Function.surjective_id
  | succ k ih =>
    intro D h hk
    have hpos : E - D ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hk
      exact absurd hk (by omega)
    obtain ⟨x, hx⟩ := WeilDivisor.exists_pos_coeff_of_ne_zero (sub_nonneg.mpr h) hpos
    have hD' : D + WeilDivisor.ofPoint x ≤ E := WeilDivisor.add_ofPoint_le_of_coeff_lt h
      (by simpa only [WeilDivisor.coeff_sub, sub_pos] using hx)
    have hk' : WeilDivisor.degree (E - (D + WeilDivisor.ofPoint x)) = k := by
      rw [sub_add_eq_sub_sub, map_sub, WeilDivisor.degree_ofPoint, hk]
      push_cast
      ring
    rw [← divisorCechCohomologyMapOfLE_comp (WeilDivisor.le_add_ofPoint D x) hD',
      LinearMap.coe_comp]
    exact (ih _ hD' hk').comp (by
      rw [← pointTwistCohomologyMap_eq_divisorCechCohomologyMapOfLE]
      exact pointTwistCohomologyMap_one_surjective D x)

/-- On a compact Hausdorff complex curve, the map `H¹(O(D)) → H¹(O(E))` induced by `D ≤ E` is
surjective. Each point twist is surjective on `H¹`, and `O(E)` is reached from `O(D)` by
finitely many point twists. -/
theorem divisorCechCohomologyMapOfLE_one_surjective {D E : WeilDivisor X} (h : D ≤ E) :
    Function.Surjective (divisorCechCohomologyMapOfLE h 1) :=
  divisorCechCohomologyMapOfLE_one_surjective_aux E _ D h
    (Int.toNat_of_nonneg (WeilDivisor.degree_nonneg (sub_nonneg.mpr h))).symm

/-- On a compact Hausdorff complex curve, `h¹(O(E)) ≤ h¹(O(D))` for `D ≤ E`. -/
theorem finrank_divisorCechCohomology_one_le_of_le {D E : WeilDivisor X} (h : D ≤ E) :
    Module.finrank ℂ (divisorCechCohomology E 1) ≤ Module.finrank ℂ (divisorCechCohomology D 1) :=
  LinearMap.finrank_le_finrank_of_surjective (divisorCechCohomologyMapOfLE_one_surjective h)

end TauCeti.RiemannSurface
