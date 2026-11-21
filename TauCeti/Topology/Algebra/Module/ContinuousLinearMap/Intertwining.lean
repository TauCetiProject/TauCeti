/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import TauCeti.LinearAlgebra.End.Aeval
import Mathlib.Algebra.Polynomial.Div
import TauCeti.LinearAlgebra.End.Split

/-!
# Intertwining linear maps

A linear map `T : E →ₗ[R] F` between topological modules, possibly discontinuous, is
intertwined by continuous linear maps `Q` on `F` and `P` on `E` up to a continuous error when
`Q ∘ T - T ∘ P` is continuous. This file shows that such intertwining pairs are closed under
taking products. Exact intertwiners also intertwine polynomial evaluations
(`Function.Semiconj.aeval`), in particular the spectral operators `1 - a • u` and their powers.
Polynomial evaluation with zero constant coefficient commutes with extending an endomorphism
along a continuous linear retract, and for any polynomial with invertible constant coefficient the
retraction and inclusion identify the kernels of the extended and original evaluations; no
complement is needed.

## Main results

* `LinearMap.continuous_comp_sub_comp_of_continuous_sub`: products of maps intertwining `T`
  up to continuous errors again intertwine `T` up to a continuous error.
* `Function.Semiconj.aeval`: a linear intertwiner intertwines every polynomial in the intertwined
  continuous endomorphisms.
* `ContinuousLinearMap.aeval_comp_comp_of_retract`: polynomial evaluation with zero constant
  coefficient commutes with extension along a retract.
* `ContinuousLinearMap.kerAevalEquivOfRetract`: along a retract, the retraction and inclusion
  identify `ker P(i ∘ u ∘ r)` with `ker P(u)` whenever `P.coeff 0` is a unit.
-/

public section

namespace Function.Semiconj

variable {R M N : Type*} [CommRing R]
  [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]
  {f : M →ₗ[R] N} {u : M →L[R] M} {v : N →L[R] N}

/-- A linear intertwiner also intertwines the associated spectral operators. -/
theorem one_sub_smul (hf : Function.Semiconj f u v) (a : R) :
    Function.Semiconj f (1 - a • u : M →L[R] M) (1 - a • v : N →L[R] N) := by
  intro x
  simp only [sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul, hf x]

/-- A linear intertwiner intertwines every power of the associated spectral operators. -/
theorem one_sub_smul_pow (hf : Function.Semiconj f u v) (a : R) (n : ℕ) :
    Function.Semiconj f ((1 - a • u) ^ n : M →L[R] M)
      ((1 - a • v) ^ n : N →L[R] N) := by
  simpa only [FunLike.coe_pow_eq_iterate] using (hf.one_sub_smul a).iterate_right n

end Function.Semiconj

namespace LinearMap

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F] [IsTopologicalAddGroup F]

/-- If continuous linear maps `Q n` on `F` intertwine `T` with continuous linear maps `P n` on
`E` up to continuous errors `Q n ∘ T - T ∘ P n`, then so do the products
`V n = Q 0 ∘ ⋯ ∘ Q (n - 1)` and `U n = P 0 ∘ ⋯ ∘ P (n - 1)`. -/
theorem continuous_comp_sub_comp_of_continuous_sub (T : E →ₗ[R] F) (P : ℕ → E →L[R] E)
    (Q : ℕ → F →L[R] F)
    (hPQ : ∀ n, Continuous ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E)))
    {U : ℕ → E →L[R] E} (hU0 : U 0 = ContinuousLinearMap.id R E)
    (hU : ∀ n, U (n + 1) = (U n).comp (P n)) {V : ℕ → F →L[R] F}
    (hV0 : V 0 = ContinuousLinearMap.id R F) (hV : ∀ n, V (n + 1) = (V n).comp (Q n)) (n : ℕ) :
    Continuous ((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) := by
  induction n with
  | zero =>
    have : (V 0 : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U 0 : E →ₗ[R] E) = 0 := by
      ext
      simp [hV0, hU0]
    rw [this]
    exact continuous_zero
  | succ n ih =>
    have : (V (n + 1) : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U (n + 1) : E →ₗ[R] E) =
        (V n : F →ₗ[R] F) ∘ₗ ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E)) +
          ((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) ∘ₗ (P n : E →ₗ[R] E) := by
      ext
      simp [hV, hU]
    have h₁ : Continuous ((V n : F →ₗ[R] F) ∘ₗ
        ((Q n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (P n : E →ₗ[R] E))) :=
      (V n).continuous.comp (hPQ n)
    have h₂ : Continuous (((V n : F →ₗ[R] F) ∘ₗ T - T ∘ₗ (U n : E →ₗ[R] E)) ∘ₗ
        (P n : E →ₗ[R] E)) :=
      ih.comp (P n).continuous
    rw [this]
    exact h₁.add h₂

end LinearMap

namespace ContinuousLinearMap

variable {R M N : Type*} [CommSemiring R]
  [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

/-- Forgetting continuity commutes with polynomial evaluation. -/
@[simp]
theorem toLinearMap_aeval (u : M →L[R] M) (p : Polynomial R) :
    (Polynomial.aeval u p).toLinearMap = Polynomial.aeval u.toLinearMap p := by
  simpa only [Polynomial.map_id, toLinearMapRingHom_apply] using
    Polynomial.map_aeval_eq_aeval_map (ψ := toLinearMapRingHom)
      (φ := RingHom.id R) (by ext x; rfl) p u

/-- Extending an endomorphism along a retract commutes with evaluating a polynomial whose
constant coefficient is zero. The condition ensures that the polynomial also vanishes on the
kernel of the retraction. -/
theorem aeval_comp_comp_of_retract {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {B : Polynomial R} (hB0 : B.coeff 0 = 0) :
    Polynomial.aeval (i.comp (u.comp r)) B = i.comp ((Polynomial.aeval u B).comp r) := by
  obtain ⟨Q, rfl⟩ := Polynomial.X_dvd_iff.2 hB0
  have hr : u.toLinearMap ∘ₗ r.toLinearMap =
      r.toLinearMap ∘ₗ (i.comp (u.comp r)).toLinearMap := by
    apply LinearMap.ext
    intro y
    have h := DFunLike.congr_fun hri (u (r y))
    simpa using h.symm
  have hQ : (Polynomial.aeval u Q).comp r =
      r.comp (Polynomial.aeval (i.comp (u.comp r)) Q) := by
    apply ContinuousLinearMap.coe_injective
    simpa only [toLinearMap_comp, toLinearMap_aeval] using
      Module.End.aeval_comp_of_comp_eq hr Q
  simp only [map_mul, Polynomial.aeval_X, mul_def, comp_assoc]
  rw [← hQ]

end ContinuousLinearMap

namespace Function.Semiconj

variable {R M N : Type*} [CommSemiring R]
  [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]
  {f : M →ₗ[R] N} {u : M →L[R] M} {v : N →L[R] N}

/-- A linear intertwiner intertwines every polynomial in the intertwined endomorphisms. -/
theorem aeval (hf : Function.Semiconj f u v) (P : Polynomial R) :
    Function.Semiconj f (Polynomial.aeval u P) (Polynomial.aeval v P) := by
  have hP : (Polynomial.aeval v P).toLinearMap.comp f =
      f.comp (Polynomial.aeval u P).toLinearMap := by
    rw [ContinuousLinearMap.toLinearMap_aeval, ContinuousLinearMap.toLinearMap_aeval]
    exact Module.End.aeval_comp_of_comp_eq (LinearMap.ext fun x ↦ (hf x).symm) P
  intro x
  exact (LinearMap.congr_fun hP x).symm

end Function.Semiconj

namespace ContinuousLinearMap

variable {R M N : Type*} [CommSemiring R]
  [TopologicalSpace M] [AddCommGroup M] [Module R M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
  [TopologicalSpace N] [AddCommGroup N] [Module R N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

/-- Along a continuous linear retract `r ∘ i = id`, if a polynomial `P` has invertible constant
coefficient, then `r` and `i` identify `ker P(i ∘ u ∘ r)` with `ker P(u)` as topological
modules. -/
noncomputable def kerAevalEquivOfRetract {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {P : Polynomial R} (hP : IsUnit (P.coeff 0)) :
    LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) : N →ₗ[R] N) ≃L[R]
      LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M) := by
  have hri' : r.toLinearMap.comp i.toLinearMap = LinearMap.id := by
    simpa only [toLinearMap_comp, coe_id] using congrArg toLinearMap hri
  set Q : Polynomial R := hP.unit⁻¹ • P
  have hQ0 : Q.coeff 0 = 1 := by
    simp [Q, Units.smul_def, smul_eq_mul]
  have hQ : Q = Polynomial.X * Q.divX + 1 := by
    simpa [hQ0] using (Polynomial.X_mul_divX_add Q).symm
  have hB := aeval_comp_comp_of_retract hri u (B := Polynomial.X * Q.divX) (by simp)
  have hQu : ((Polynomial.aeval u Q : M →L[R] M) : M →ₗ[R] M) - 1 =
      ((Polynomial.aeval u (Polynomial.X * Q.divX) : M →L[R] M) : M →ₗ[R] M) := by
    apply sub_eq_iff_eq_add.mpr
    conv_lhs => rw [hQ, map_add, map_one, toLinearMap_add, toLinearMap_one]
  have hsplit : ((Polynomial.aeval (i.comp (u.comp r)) Q : N →L[R] N) : N →ₗ[R] N) =
      LinearMap.splitEnd r.toLinearMap i.toLinearMap hri'
        ((Polynomial.aeval u Q : M →L[R] M) : M →ₗ[R] M) := by
    rw [LinearMap.splitEnd_eq_one_add, hQu, ← toLinearMap_comp, ← toLinearMap_comp, ← hB]
    conv_lhs => rw [hQ, map_add, map_one, toLinearMap_add, toLinearMap_one, add_comm]
  have hQ_ker_u :
      LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M) =
        LinearMap.ker ((Polynomial.aeval u Q : M →L[R] M) : M →ₗ[R] M) := by
    ext x
    simp only [Q, Units.smul_def, map_smul, LinearMap.mem_ker, coe_coe, smul_apply,
      (hP.unit⁻¹).isUnit.smul_eq_zero]
  have hQ_ker_v :
      LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) : N →ₗ[R] N) =
        LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) Q : N →L[R] N) : N →ₗ[R] N) := by
    ext x
    simp only [Q, Units.smul_def, map_smul, LinearMap.mem_ker, coe_coe, smul_apply,
      (hP.unit⁻¹).isUnit.smul_eq_zero]
  let e := LinearMap.kerSplitEndEquiv r.toLinearMap i.toLinearMap hri'
    ((Polynomial.aeval u Q : M →L[R] M) : M →ₗ[R] M)
  have hmaps_r : ∀ x ∈ LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) :
      N →ₗ[R] N), r x ∈ LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M) := by
    intro x hx
    rw [hQ_ker_v, hsplit] at hx
    rw [hQ_ker_u]
    simpa only [e, LinearMap.coe_kerSplitEndEquiv_apply, coe_coe] using (e ⟨x, hx⟩).property
  have hmaps_i : ∀ x ∈ LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M),
      i x ∈ LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) : N →ₗ[R] N) := by
    intro x hx
    rw [hQ_ker_u] at hx
    rw [hQ_ker_v, hsplit]
    simpa only [e, LinearMap.coe_kerSplitEndEquiv_symm_apply, coe_coe] using
      (e.symm ⟨x, hx⟩).property
  refine ContinuousLinearEquiv.ofContinuousLinearMap
    ((r.domRestrict _).codRestrict _ fun x ↦ hmaps_r x x.property)
    ((i.domRestrict _).codRestrict _ fun x ↦ hmaps_i x x.property)
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext <| by
      have h1 := congrArg Subtype.val (e.apply_symm_apply ⟨x, hQ_ker_u ▸ x.property⟩)
      dsimp only [e] at h1
      rw [LinearMap.coe_kerSplitEndEquiv_apply, LinearMap.coe_kerSplitEndEquiv_symm_apply] at h1
      exact h1)
    (ContinuousLinearMap.ext fun x ↦ Subtype.ext <| by
      have h2 := congrArg Subtype.val (e.symm_apply_apply ⟨x, hsplit ▸ hQ_ker_v ▸ x.property⟩)
      dsimp only [e] at h2
      rw [LinearMap.coe_kerSplitEndEquiv_symm_apply, LinearMap.coe_kerSplitEndEquiv_apply] at h2
      exact h2)

/-- The forward map of `kerAevalEquivOfRetract` applies the retraction `r`. -/
@[simp]
theorem coe_kerAevalEquivOfRetract_apply {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {P : Polynomial R} (hP : IsUnit (P.coeff 0))
    (x : LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) : N →ₗ[R] N)) :
    (kerAevalEquivOfRetract hri u hP x : M) = r x :=
  (rfl)

/-- The inverse map of `kerAevalEquivOfRetract` applies the inclusion `i`. -/
@[simp]
theorem coe_kerAevalEquivOfRetract_symm_apply {i : M →L[R] N} {r : N →L[R] M}
    (hri : r.comp i = .id R M) (u : M →L[R] M) {P : Polynomial R} (hP : IsUnit (P.coeff 0))
    (x : LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M)) :
    ((kerAevalEquivOfRetract hri u hP).symm x : N) = i x :=
  (rfl)

end ContinuousLinearMap
