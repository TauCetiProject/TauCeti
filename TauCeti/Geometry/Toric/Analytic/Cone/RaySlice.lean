/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Cone.Manifold
public import Mathlib.Analysis.Analytic.Order

/-!
# Transverse slices and character orders in regular toric charts

Varying one ray coordinate and keeping all other mixed coordinates fixed gives a holomorphic
complex line in a regular affine toric chart. On a slice whose other ray coordinates are
nonzero, a character vanishes to the order given by its pairing with the primitive ray
generator. In particular, the dual basis character defining that boundary component has a
simple zero, even when the slice passes through an intersection of boundary components.

The construction uses `coneChartEquiv` and its monomial evaluation formula. The order formula
is the local analytic version of the coefficient of a character in its toric principal divisor.

## References

* W. Fulton, *Introduction to Toric Varieties*, §3.3.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Proposition 4.1.2.
-/

public section

open Function Multiplicative
open scoped ContDiff Manifold

namespace TauCeti.Toric

variable {N V ι : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}
  (hi : IsIntegralLattice i) (hσ : IsToricCone i σ)
  {b : Module.Basis (ToricRay σ ⊕ ι) ℤ N}
  (hb : ∀ ρ, IsPrimitiveGenerator i ρ (b (Sum.inl ρ)))

/-- The complex line obtained by varying the coordinate of `ρ`, keeping the other regular
coordinates of `x` fixed. At parameter zero it meets the coordinate hyperplane of `ρ`. -/
noncomputable def coneChartRaySlice
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) (t : ℂ) :
    AffineSemigroupComplexPoint (dualSemigroup hi σ) := by
  classical
  exact (coneChartEquiv hi hσ hb).symm
    (update (coneChartEquiv hi hσ hb x).1 ρ t, (coneChartEquiv hi hσ hb x).2)

open Classical in
/-- The mixed coordinates of a ray slice differ from those of its base point only at that ray. -/
@[simp]
theorem coneChartEquiv_coneChartRaySlice
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) (t : ℂ) :
    coneChartEquiv hi hσ hb (coneChartRaySlice hi hσ hb x ρ t) =
      (update (coneChartEquiv hi hσ hb x).1 ρ t, (coneChartEquiv hi hσ hb x).2) := by
  classical
  simp [coneChartRaySlice]

/-- A ray slice passes through its base point at the original value of that coordinate. -/
@[simp]
theorem coneChartRaySlice_self
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) :
    coneChartRaySlice hi hσ hb x ρ
      (x (MonoidAlgebra.single (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ))) 1)) = x := by
  classical
  rw [← coneChartEquiv_fst_apply]
  apply (coneChartEquiv hi hσ hb).injective
  rw [coneChartEquiv_coneChartRaySlice, update_eq_self]

/-- Along a ray slice, a monomial is a power of the parameter times the fixed contribution of
all other coordinates. -/
theorem coneChartRaySlice_apply_single
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ)
    (m : dualSemigroup hi σ) (t : ℂ) :
    coneChartRaySlice hi hσ hb x ρ t (MonoidAlgebra.single (ofAdd m) 1) =
      t ^ (regularDualSemigroupEquiv hi hσ hb m).1 ρ *
        (((regularDualSemigroupEquiv hi hσ hb m).1.erase ρ).prod
          fun ρ' n ↦ (coneChartEquiv hi hσ hb x).1 ρ' ^ n) *
        ((regularDualSemigroupEquiv hi hσ hb m).2.prod
          fun j n ↦ (coneChartEquiv hi hσ hb x).2 j ^ n : ℂˣ) := by
  classical
  rw [coneChartRaySlice, coneChartEquiv_symm_apply_single]
  congr 1
  rw [← Finsupp.mul_prod_erase' _ ρ _ (fun _ ↦ pow_zero _)]
  simp only [update_self]
  congr 1
  rw [Finsupp.prod, Finsupp.prod]
  apply Finset.prod_congr rfl
  intro ρ' hρ'
  obtain ⟨hne, -⟩ := Finset.mem_erase.mp (by
    simpa only [Finsupp.support_erase] using hρ')
  simp [hne]

/-- A character's order on a ray slice is its value on the primitive ray generator, provided
its other supported ray coordinates are nonzero. In particular this applies on the open part
of the boundary component. -/
theorem analyticOrderAt_coneChartRaySlice_apply_single
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ)
    (m : dualSemigroup hi σ)
    (hx : ∀ ρ' ∈ (regularDualSemigroupEquiv hi hσ hb m).1.support,
      ρ' ≠ ρ → (coneChartEquiv hi hσ hb x).1 ρ' ≠ 0) :
    analyticOrderAt (fun t ↦ coneChartRaySlice hi hσ hb x ρ t
      (MonoidAlgebra.single (ofAdd m) 1)) 0 =
        ((m : N →+ ℤ) (primitiveGenerator hi hσ ρ)).toNat := by
  classical
  let a := regularDualSemigroupEquiv hi hσ hb m
  let c : ℂ := (a.1.erase ρ).prod (fun ρ' n ↦ (coneChartEquiv hi hσ hb x).1 ρ' ^ n) *
    (a.2.prod fun j n ↦ (coneChartEquiv hi hσ hb x).2 j ^ n : ℂˣ)
  have hc : c ≠ 0 := mul_ne_zero
    (Finsupp.prod_ne_zero_iff.mpr fun ρ' hρ' ↦ by
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp (by
        simpa only [Finsupp.support_erase] using hρ')
      exact pow_ne_zero _ (hx ρ' hmem hne))
    (Units.ne_zero _)
  have heq : (fun t ↦ coneChartRaySlice hi hσ hb x ρ t
      (MonoidAlgebra.single (ofAdd m) 1)) = fun t ↦ t ^ a.1 ρ * c := by
    funext t
    rw [coneChartRaySlice_apply_single, mul_assoc]
  rw [heq]
  -- Apply the factorization criterion to the actual function, including its constant factor.
  have h : analyticOrderAt (fun t : ℂ ↦ t ^ a.1 ρ * c) 0 = (a.1 ρ : ℕ∞) :=
    ((analyticAt_id.pow (a.1 ρ)).mul analyticAt_const).analyticOrderAt_eq_natCast.mpr
      ⟨fun _ ↦ c, analyticAt_const, hc, by simp⟩
  have hexp : ((m : N →+ ℤ) (primitiveGenerator hi hσ ρ)).toNat = a.1 ρ := by
    rw [← (hb ρ).eq_primitiveGenerator hi hσ,
      ← coe_regularDualSemigroupEquiv_fst_apply hi hσ hb m ρ, Int.toNat_natCast]
  rw [hexp]
  exact h

/-- A ray's dual coordinate has order one on its slice, with no restriction on the other
coordinates. Thus this local boundary equation has multiplicity one also at crossings. -/
@[simp]
theorem analyticOrderAt_coneChartRaySlice_dualSemigroupCoord
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) :
    analyticOrderAt (fun t ↦ coneChartRaySlice hi hσ hb x ρ t
      (MonoidAlgebra.single (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ))) 1)) 0 = 1 := by
  classical
  have heq : (fun t ↦ coneChartRaySlice hi hσ hb x ρ t
      (MonoidAlgebra.single (ofAdd (dualSemigroupCoord hi hσ hb (Sum.inl ρ))) 1)) = id := by
    funext t
    rw [← coneChartEquiv_fst_apply]
    simp
  rw [heq, analyticOrderAt_id]

/-- Ray slices are holomorphic for the complex structure of the extending-basis chart. -/
theorem contMDiff_coneChartRaySlice {k l s : ℕ}
    {B : Module.Basis (ToricRay σ ⊕ Fin l) ℤ N}
    (hB : ∀ ρ, IsPrimitiveGenerator i ρ (B (Sum.inl ρ))) (κ : ToricRay σ ≃ Fin k)
    (g : AddGeneratingFamily (dualSemigroup hi σ) s)
    (x : AffineSemigroupComplexPoint (dualSemigroup hi σ)) (ρ : ToricRay σ) (n : ℕ∞ω) :
    letI := affinePointTopology g
    letI := coneChartedSpace hi hσ hB κ g
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, (Fin k → ℂ) × (Fin l → ℂ)) n
      (coneChartRaySlice hi hσ hB x ρ) := by
  classical
  let := affinePointTopology g
  let := coneChartedSpace hi hσ hB κ g
  apply (contMDiff_coneChartAmbient_comp_iff hi hσ hB κ g).mp
  have heq : coneChartAmbient hi hσ hB κ ∘ coneChartRaySlice hi hσ hB x ρ =
      fun t ↦ (fun a ↦ update (coneChartEquiv hi hσ hB x).1 ρ t (κ.symm a),
        fun j ↦ ((coneChartEquiv hi hσ hB x).2 j : ℂ)) := by
    funext t
    ext <;> simp
  rw [heq]
  apply ContDiff.contMDiff
  apply ContDiff.prodMk
  · let := Fintype.ofEquiv (Fin k) κ.symm
    exact contDiff_pi.mpr fun a ↦
      (contDiff_apply ℂ (fun _ : ToricRay σ ↦ ℂ) (κ.symm a)).comp (contDiff_update _ _ ρ)
  · exact contDiff_const

end TauCeti.Toric
