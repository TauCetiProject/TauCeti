/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The top exterior power of a free module plus a projective ideal

Let `I` be a projective ideal of a domain `R`. The module `Rʳ × I` has rank `r + 1`, and its
exterior power in degree `r + 1` is `I` itself:

```text
⋀ʳ⁺¹ (Rʳ × I) ≃ I.
```

The isomorphism sends `v₀ ∧ ⋯ ∧ vᵣ`, with `vₖ = (uₖ, aₖ)`, to the determinant of the square matrix
whose `k`-th row is `(aₖ, uₖ)`; expanding along the first column shows that this determinant lies
in `I`. Its inverse sends `a ∈ I` to `(0, a) ∧ (e₀, 0) ∧ ⋯ ∧ (eᵣ₋₁, 0)`.

Injectivity is the only nonformal point. For a nonzero `c ∈ I`, the inclusion `Rʳ × I → Rʳ⁺¹`
followed by multiplication by `c` back into `Rʳ × I` is multiplication by `c`, so it induces
multiplication by `cʳ⁺¹` on the exterior power, which is injective because the exterior power of
a projective module is projective, hence flat and torsion-free. Projectivity cannot be dropped: for
the maximal ideal `I = (x, y)` of `k[x, y]`, the element `(0, x) ∧ (0, y)` of `⋀² (R × I)` is
nonzero but is killed by the inclusion into `⋀² R²`.

Over a Dedekind domain every finite projective module of rank `r + 1` is `Rʳ × I` for a nonzero
ideal `I` (Steinitz), so this identifies `I` with the top exterior power, the determinant of the
module.

## Main definitions

* `Ideal.exteriorPowerPiProdEquiv`: the isomorphism `⋀ʳ⁺¹ (Rʳ × I) ≃ I`.

## Main results

* `Ideal.coe_exteriorPowerPiProdEquiv_ιMulti`: its value on an exterior product is a determinant.
* `Ideal.exteriorPowerPiProdEquiv_symm_apply`: its inverse sends `a` to
  `(0, a) ∧ (e₀, 0) ∧ ⋯ ∧ (eᵣ₋₁, 0)`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter I, §3, Proposition 3.4 and the determinant discussion before it.
-/

public section

noncomputable section

open exteriorPower

namespace Ideal

variable {R : Type*} [CommRing R] (I : Ideal R) (r : ℕ)

/-- The inclusion `Rʳ × I → Rʳ⁺¹`, `(u, a) ↦ (a, u₀, …, uᵣ₋₁)`. -/
private def consSubtype : (Fin r → R) × I →ₗ[R] Fin (r + 1) → R :=
  (Fin.consLinearEquiv R fun _ : Fin (r + 1) ↦ R).toLinearMap ∘ₗ
    (I.subtype.prodMap LinearMap.id) ∘ₗ (LinearEquiv.prodComm R (Fin r → R) I).toLinearMap

private theorem consSubtype_apply (x : (Fin r → R) × I) :
    consSubtype I r x = Fin.cons (x.2 : R) x.1 := by
  ext i
  simp [consSubtype, Fin.consLinearEquiv_apply, Equiv.toFun_as_coe]

/-- The linear form on `⋀ʳ⁺¹ (Rʳ × I)` sending `v₀ ∧ ⋯ ∧ vᵣ` to the determinant of the rows
`consSubtype (vₖ)`. -/
private def detForm : ⋀[R]^(r + 1) ((Fin r → R) × I) →ₗ[R] R :=
  (Pi.basisFun R (Fin (r + 1))).exteriorPowerTopEquiv.toLinearMap ∘ₗ
    exteriorPower.map (r + 1) (consSubtype I r)

private theorem detForm_ιMulti (v : Fin (r + 1) → (Fin r → R) × I) :
    detForm I r (ιMulti R (r + 1) v) =
      (Matrix.of fun k ↦ (Fin.cons ((v k).2 : R) (v k).1 : Fin (r + 1) → R)).det := by
  rw [detForm, LinearMap.comp_apply, map_apply_ιMulti, LinearEquiv.coe_coe,
    Module.Basis.exteriorPowerTopEquiv_apply_ιMulti, Pi.basisFun_det_apply]
  simp only [Function.comp_def, consSubtype_apply]

/-- The determinant of rows whose first entries lie in `I` lies in `I`. -/
private theorem detForm_ιMulti_mem (v : Fin (r + 1) → (Fin r → R) × I) :
    detForm I r (ιMulti R (r + 1) v) ∈ I := by
  rw [detForm_ιMulti, Matrix.det_succ_column_zero]
  exact I.sum_mem fun k _ ↦ I.mul_mem_right _ (I.mul_mem_left _ (by simp))

/-- The exterior product `(0, a) ∧ (e₀, 0) ∧ ⋯ ∧ (eᵣ₋₁, 0)`. -/
private def wedgeStd (a : I) : ⋀[R]^(r + 1) ((Fin r → R) × I) :=
  ιMulti R (r + 1) (Fin.cons (0, a) fun j ↦ (Pi.single j 1, 0))

private theorem detForm_wedgeStd (a : I) : detForm I r (wedgeStd I r a) = a := by
  set v : Fin (r + 1) → (Fin r → R) × I := Fin.cons (0, a) fun j ↦ (Pi.single j 1, 0)
  have h : (Matrix.of fun k ↦ (Fin.cons ((v k).2 : R) (v k).1 : Fin (r + 1) → R)) =
      Matrix.diagonal (Fin.cons (a : R) fun _ ↦ 1) := by
    ext k l
    induction k using Fin.cases <;> induction l using Fin.cases <;>
      simp [v, Matrix.diagonal, Pi.single_apply, Fin.succ_inj, eq_comm]
  rw [wedgeStd, detForm_ιMulti, h, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

/-- The image of `detForm` is `I`. -/
private theorem detForm_range_eq : LinearMap.range (detForm I r) = I := by
  refine le_antisymm ?_ fun a ha ↦ ⟨wedgeStd I r ⟨a, ha⟩, detForm_wedgeStd I r ⟨a, ha⟩⟩
  rw [LinearMap.range_eq_map, ← ιMulti_span, Submodule.map_span_le]
  rintro _ ⟨v, rfl⟩
  exact detForm_ιMulti_mem I r v

/-- For `c ∈ I`, the map `Rʳ⁺¹ → Rʳ × I`, `x ↦ ((c x₁, …, c xᵣ), c x₀)`, a left inverse of
`consSubtype` up to the factor `c`. -/
private def smulRestrict {c : R} (hc : c ∈ I) : (Fin (r + 1) → R) →ₗ[R] (Fin r → R) × I :=
  (LinearMap.pi fun j ↦ c • LinearMap.proj j.succ).prod
    ((LinearMap.toSpanSingleton R I ⟨c, hc⟩).comp (LinearMap.proj 0))

private theorem smulRestrict_comp_consSubtype {c : R} (hc : c ∈ I) :
    smulRestrict I r hc ∘ₗ consSubtype I r = c • LinearMap.id := by
  refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
  · ext j
    simp [smulRestrict, consSubtype_apply]
  · ext
    simp [smulRestrict, consSubtype_apply, mul_comm]

variable [IsDomain R] [Module.Projective R I]

private theorem map_consSubtype_injective :
    Function.Injective (exteriorPower.map (r + 1) (consSubtype I r)) := by
  rcases eq_or_ne I ⊥ with rfl | hI
  · -- For `I = 0` the inclusion `Rʳ × 0 → Rʳ⁺¹` has the retraction `x ↦ (tail x, 0)`.
    refine map_injective ((LinearMap.pi fun j ↦ LinearMap.proj j.succ).prod 0) ?_
    refine LinearMap.ext fun x ↦ Prod.ext ?_ (Subsingleton.elim _ _)
    ext j
    simp [consSubtype_apply]
  · -- Otherwise the composite with multiplication by `c ∈ I \ {0}` is multiplication by `cʳ⁺¹`,
    -- which is injective on the projective, hence flat, exterior power.
    obtain ⟨c, hcI, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hreg : IsSMulRegular (⋀[R]^(r + 1) ((Fin r → R) × I)) (c ^ (r + 1)) :=
      Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero (pow_ne_zero _ hc0))
    intro w w' h
    have key (y : ⋀[R]^(r + 1) ((Fin r → R) × I)) :
        exteriorPower.map (r + 1) (smulRestrict I r hcI)
          (exteriorPower.map (r + 1) (consSubtype I r) y) = c ^ (r + 1) • y := by
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, smulRestrict_comp_consSubtype,
        map_smul_eq_pow_smul, exteriorPower.map_id, LinearMap.smul_apply, LinearMap.id_apply]
    exact hreg (by
      simpa only [key] using congrArg (exteriorPower.map (r + 1) (smulRestrict I r hcI)) h)

private theorem detForm_injective : Function.Injective (detForm I r) := by
  rw [detForm, LinearMap.coe_comp, LinearEquiv.coe_coe]
  exact (Pi.basisFun R (Fin (r + 1))).exteriorPowerTopEquiv.injective.comp
    (map_consSubtype_injective I r)

/-- **The top exterior power of `Rʳ × I`.** For a projective ideal `I` of a domain `R`, the
exterior power of `Rʳ × I` in degree `r + 1` is isomorphic to `I`. An exterior product
`v₀ ∧ ⋯ ∧ vᵣ`, `vₖ = (uₖ, aₖ)`, goes to the determinant of the matrix with rows `(aₖ, uₖ)`
(`Ideal.coe_exteriorPowerPiProdEquiv_ιMulti`). -/
def exteriorPowerPiProdEquiv : ⋀[R]^(r + 1) ((Fin r → R) × I) ≃ₗ[R] I :=
  (LinearEquiv.ofInjective (detForm I r) (detForm_injective I r)).trans
    (LinearEquiv.ofEq _ _ (detForm_range_eq I r))

private theorem coe_exteriorPowerPiProdEquiv (x : ⋀[R]^(r + 1) ((Fin r → R) × I)) :
    (exteriorPowerPiProdEquiv I r x : R) = detForm I r x := by
  rw [exteriorPowerPiProdEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
    LinearEquiv.ofInjective_apply]

/-- `Ideal.exteriorPowerPiProdEquiv` sends `v₀ ∧ ⋯ ∧ vᵣ`, `vₖ = (uₖ, aₖ)`, to the determinant of
the matrix with rows `(aₖ, uₖ)`. -/
@[simp]
theorem coe_exteriorPowerPiProdEquiv_ιMulti (v : Fin (r + 1) → (Fin r → R) × I) :
    (exteriorPowerPiProdEquiv I r (ιMulti R (r + 1) v) : R) =
      (Matrix.of fun k ↦ (Fin.cons ((v k).2 : R) (v k).1 : Fin (r + 1) → R)).det := by
  rw [coe_exteriorPowerPiProdEquiv, detForm_ιMulti]

/-- The inverse of `Ideal.exteriorPowerPiProdEquiv` sends `a` to
`(0, a) ∧ (e₀, 0) ∧ ⋯ ∧ (eᵣ₋₁, 0)`. -/
@[simp]
theorem exteriorPowerPiProdEquiv_symm_apply (a : I) :
    (exteriorPowerPiProdEquiv I r).symm a =
      ιMulti R (r + 1) (Fin.cons (0, a) fun j ↦ (Pi.single j 1, 0)) := by
  rw [LinearEquiv.symm_apply_eq]
  exact Subtype.ext (by rw [coe_exteriorPowerPiProdEquiv, ← wedgeStd, detForm_wedgeStd])

end Ideal
