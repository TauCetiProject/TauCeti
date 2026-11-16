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
* `ContinuousLinearMap.aeval_comp_comp_of_retract`: polynomial evaluation with zero constant
  coefficient commutes with extension along a retract.
* `ContinuousLinearMap.kerAevalEquivOfRetract`: along a retract, the retraction and inclusion
  identify `ker P(i ∘ u ∘ r)` with `ker P(u)` whenever `P.coeff 0` is a unit.
* `Function.Semiconj.aeval`: a linear intertwiner intertwines every polynomial in the two
  operators.
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

/-- A linear intertwiner intertwines every polynomial in the two operators. -/
theorem aeval (hf : Function.Semiconj f u v) (p : Polynomial R) :
    Function.Semiconj f (Polynomial.aeval u p) (Polynomial.aeval v p) := by
  have hcomp : v.toLinearMap.comp f = f.comp u.toLinearMap := LinearMap.ext fun x ↦ (hf x).symm
  intro x
  have hx := LinearMap.congr_fun (Module.End.aeval_comp_of_comp_eq hcomp p) x
  simpa only [LinearMap.comp_apply, ← ContinuousLinearMap.toLinearMap_aeval,
    ContinuousLinearMap.coe_coe] using hx.symm

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
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hr : Function.Semiconj (r : N →ₗ[R] M) (i.comp (u.comp r)) u := fun y ↦ by simp [hri']
  have hi : Function.Semiconj (i : M →ₗ[R] N) u (i.comp (u.comp r)) := fun x ↦ by simp [hri']
  have hmaps_r : ∀ x ∈ LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) :
      N →ₗ[R] N), r x ∈ LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M) := by
    intro x hx
    rw [LinearMap.mem_ker, coe_coe] at hx ⊢
    simpa only [coe_coe, hx, map_zero] using (hr.aeval P x).symm
  have hmaps_i : ∀ x ∈ LinearMap.ker ((Polynomial.aeval u P : M →L[R] M) : M →ₗ[R] M),
      i x ∈ LinearMap.ker ((Polynomial.aeval (i.comp (u.comp r)) P : N →L[R] N) : N →ₗ[R] N) := by
    intro x hx
    rw [LinearMap.mem_ker, coe_coe] at hx ⊢
    simpa only [coe_coe, hx, map_zero] using (hi.aeval P x).symm
  refine ContinuousLinearEquiv.equivOfInverse
    ((r.domRestrict _).codRestrict _ fun x ↦ hmaps_r x x.2)
    ((i.domRestrict _).codRestrict _ fun x ↦ hmaps_i x x.2) ?_ ?_
  · intro x
    have hx : Polynomial.aeval (i.comp (u.comp r)) P x = 0 := LinearMap.mem_ker.mp x.2
    have hirx : Polynomial.aeval (i.comp (u.comp r)) P (i (r x)) = 0 :=
      LinearMap.mem_ker.mp (hmaps_i (r x) (hmaps_r x x.2))
    have hdiv (y : N) :
        Polynomial.aeval (i.comp (u.comp r)) (Polynomial.X * P.divX) y + P.coeff 0 • y =
          Polynomial.aeval (i.comp (u.comp r)) P y := by
      have h := congrArg (fun f : N →L[R] N ↦ f y)
        (congrArg (Polynomial.aeval (i.comp (u.comp r))) (Polynomial.X_mul_divX_add P))
      simpa only [map_add, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, add_apply,
        smul_apply, one_apply_eq_self] using h
    have hX := aeval_comp_comp_of_retract hri u (B := Polynomial.X * P.divX) (by simp)
    have hXeq : Polynomial.aeval (i.comp (u.comp r)) (Polynomial.X * P.divX) (i (r x)) =
        Polynomial.aeval (i.comp (u.comp r)) (Polynomial.X * P.divX) x := by
      simp [hX, hri']
    have hsmul : P.coeff 0 • i (r x) = P.coeff 0 • (x : N) := by
      apply add_left_cancel (a := Polynomial.aeval (i.comp (u.comp r)) (Polynomial.X * P.divX) x)
      rw [hdiv x, hx, ← hXeq, hdiv (i (r x)), hirx]
    obtain ⟨c, hc⟩ := hP.exists_left_inv
    have hEq : i (r x) = x := by simpa [smul_smul, hc] using congrArg (c • ·) hsmul
    exact Subtype.ext hEq
  · intro x
    exact Subtype.ext (hri' x)

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
