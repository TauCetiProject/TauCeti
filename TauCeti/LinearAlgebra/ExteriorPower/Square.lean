/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# Recognizing a second exterior power and symmetric wedge products of endomorphisms

An alternating bilinear map `ω : M → M → N` induces, by the universal property of the exterior
power, a linear map `⋀²M → N` sending `x ∧ y` to `ω x y`. This file records when that map is an
isomorphism: if `M` has a basis `b` indexed by a linearly ordered type and the values
`ω (b i) (b j)` for `i < j` form a basis of `N`, then `⋀²M ≃ N`.

This is how a module presented by a basis of "brackets" of basis vectors, such as the degree-one
piece of the graded Lie algebra of a free group, is identified with an exterior square without
comparing the index set `{(i, j) | i < j}` with Mathlib's index set of two-element subsets.

Over a field `K` of characteristic not `2`, two endomorphisms `A, B : Module.End K V` also combine
into a *symmetric wedge product* `TauCeti.wedgeEnd A B : Module.End K (⋀[K]^2 V)` sending `u ∧ v`
to `2⁻¹ • (A u ∧ B v + B u ∧ A v)`. The `2⁻¹` normalization gives
`wedgeEnd A A = exteriorPower.map 2 A` and `wedgeEnd id id = id`, which matches the bivector
curvature-operator convention for Kulkarni–Nomizu products on inner product spaces.

## Main definitions

* `LinearMap.IsAlt.exteriorSquareEquiv`: the isomorphism `⋀²M ≃ N` induced by an alternating
  bilinear map carrying the ordered pairs of a basis of `M` to a basis of `N`.
* `TauCeti.wedgeEnd`: the symmetric wedge product of two endomorphisms on `⋀[K]^2 V`.

## Main results

* `LinearMap.IsAlt.exteriorSquareEquiv_ιMulti`: the isomorphism sends `x ∧ y` to `ω x y`.
* `LinearMap.IsAlt.exteriorSquareEquiv_symm_apply`: its inverse sends the basis vector indexed by
  `i < j` to `b i ∧ b j`.
* `exteriorPower.ιMulti_two_add_left`, `exteriorPower.ιMulti_two_add_right`,
  `exteriorPower.ιMulti_two_smul_left`, `exteriorPower.ιMulti_two_smul_right`, and
  `exteriorPower.ιMulti_two_swap`: bilinearity and swap antisymmetry of `u ∧ w`.
* `TauCeti.wedgeEnd_apply_ιMulti`, `TauCeti.wedgeEnd_comm`, `TauCeti.wedgeEnd_self`, and
  `TauCeti.wedgeEnd_id`: evaluation, commutativity, diagonal specialization to
  `exteriorPower.map 2`, and the identity law for `wedgeEnd`.
-/

public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The wedge `u ∧ w` is additive in `u`. -/
theorem ιMulti_two_add_left (u u' w : M) :
    ιMulti R 2 ![u + u', w] = ιMulti R 2 ![u, w] + ιMulti R 2 ![u', w] := by
  simpa only [MultilinearMap.toBilinMap_apply, AlternatingMap.coe_multilinearMap] using
    ((ιMulti R 2).toMultilinearMap.toBilinMap).map_add₂ u u' w

/-- The wedge `u ∧ w` is additive in `w`. -/
theorem ιMulti_two_add_right (u w w' : M) :
    ιMulti R 2 ![u, w + w'] = ιMulti R 2 ![u, w] + ιMulti R 2 ![u, w'] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail, mul_add]

/-- The wedge `u ∧ w` is homogeneous in `w`. -/
theorem ιMulti_two_smul_right (u w : M) (c : R) :
    ιMulti R 2 ![u, c • w] = c • ιMulti R 2 ![u, w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

/-- The wedge `u ∧ w` is homogeneous in `u`. -/
theorem ιMulti_two_smul_left (u w : M) (c : R) :
    ιMulti R 2 ![c • u, w] = c • ιMulti R 2 ![u, w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

/-- Swapping the two factors of a pure wedge `u ∧ w` negates it. -/
theorem ιMulti_two_swap (u w : M) :
    ιMulti R 2 ![w, u] = -ιMulti R 2 ![u, w] := by
  simpa using ((ιMulti R 2).isAlt_toBilinMap.neg u w).symm

end exteriorPower

namespace LinearMap.IsAlt

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [LinearOrder ι] {ω : M →ₗ[R] M →ₗ[R] N}

/-- **Recognizing an exterior square.** Let `ω` be an alternating bilinear map, `b` a basis of `M`
indexed by a linearly ordered type, and `c` a basis of `N` indexed by the pairs `i < j` with
`c (i, j) = ω (b i) (b j)`. Then the linear map `⋀²M → N` induced by `ω`, which sends `x ∧ y` to
`ω x y` (`LinearMap.IsAlt.exteriorSquareEquiv_ιMulti`), is an isomorphism. -/
noncomputable def exteriorSquareEquiv (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) : ⋀[R]^2 M ≃ₗ[R] N :=
  LinearEquiv.ofLinearMap (exteriorPower.alternatingMapLinearEquiv hω.toAlternatingMap)
    (c.constr R fun ij ↦ exteriorPower.ιMulti R 2 ![b ij.1.1, b ij.1.2])
    (c.ext fun ij ↦ by
      simp [Module.Basis.constr_basis, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hc])
    (exteriorPower.linearMap_ext <| b.ext_alternating fun v hv ↦ by
      have hv01 : v 0 ≠ v 1 := hv.ne (by decide)
      have hbv : (fun i ↦ b (v i)) = ![b (v 0), b (v 1)] := by
        ext i
        fin_cases i <;> rfl
      simp only [hbv, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, toAlternatingMap_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.id_apply]
      rcases hv01.lt_or_gt with h | h
      · rw [hc ⟨(v 0, v 1), h⟩, Module.Basis.constr_basis]
      · -- The pair is out of order: swap it, at the cost of a sign on both sides.
        have hswap : ![b (v 0), b (v 1)] = ![b (v 1), b (v 0)] ∘ Equiv.swap 0 1 := by
          ext i
          fin_cases i <;> rfl
        rw [← hω.neg, hc ⟨(v 1, v 0), h⟩, map_neg, Module.Basis.constr_basis, hswap,
          AlternatingMap.map_swap _ _ (by decide)])

/-- The isomorphism induced by `ω` sends `x ∧ y` to `ω x y`. -/
@[simp]
theorem exteriorSquareEquiv_ιMulti (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) (v : Fin 2 → M) :
    hω.exteriorSquareEquiv b c hc (exteriorPower.ιMulti R 2 v) = ω (v 0) (v 1) := by
  simp [exteriorSquareEquiv, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The inverse isomorphism sends the basis vector of `N` indexed by `i < j` to `b i ∧ b j`. -/
@[simp]
theorem exteriorSquareEquiv_symm_apply (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) (ij : {ij : ι × ι // ij.1 < ij.2}) :
    (hω.exteriorSquareEquiv b c hc).symm (c ij) =
      exteriorPower.ιMulti R 2 ![b ij.1.1, b ij.1.2] := by
  simp [exteriorSquareEquiv, Module.Basis.constr_basis]

end LinearMap.IsAlt

namespace TauCeti

section WedgeEnd

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem end_ext_ιMulti {f g : Module.End K (⋀[K]^2 V)}
    (h : ∀ u w, f (exteriorPower.ιMulti K 2 ![u, w]) = g (exteriorPower.ιMulti K 2 ![u, w])) :
    f = g :=
  exteriorPower.linearMap_ext <| AlternatingMap.ext fun v ↦ by
    rw [← FinVec.etaExpand_eq v]; exact h (v 0) (v 1)

private theorem isAlt_wedgeEndAux (A B : Module.End K V) :
    (((exteriorPower.ιMulti K 2).toMultilinearMap.toBilinMap).compl₁₂ A B +
      ((exteriorPower.ιMulti K 2).toMultilinearMap.toBilinMap).compl₁₂ B A).IsAlt := fun u ↦ by
  simp [LinearMap.compl₁₂_apply, exteriorPower.ιMulti_two_swap (B u) (A u)]

private noncomputable def wedgeEndAux (A B : Module.End K V) : Module.End K (⋀[K]^2 V) :=
  (2 : K)⁻¹ • exteriorPower.alternatingMapLinearEquiv (isAlt_wedgeEndAux A B).toAlternatingMap

private theorem wedgeEndAux_ιMulti (A B : Module.End K V) (u v : V) :
    wedgeEndAux A B (exteriorPower.ιMulti K 2 ![u, v]) = (2 : K)⁻¹ •
      (exteriorPower.ιMulti K 2 ![A u, B v] + exteriorPower.ιMulti K 2 ![B u, A v]) := by
  simp [wedgeEndAux, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    LinearMap.IsAlt.toAlternatingMap_apply]

private theorem wedgeEndAux_comm (A B : Module.End K V) : wedgeEndAux A B = wedgeEndAux B A :=
  end_ext_ιMulti fun _ _ ↦ by simp [wedgeEndAux_ιMulti, add_comm]

private theorem wedgeEndAux_add_left (A₁ A₂ B : Module.End K V) :
    wedgeEndAux (A₁ + A₂) B = wedgeEndAux A₁ B + wedgeEndAux A₂ B :=
  end_ext_ιMulti fun _ _ ↦ by
    simp only [LinearMap.add_apply, wedgeEndAux_ιMulti, exteriorPower.ιMulti_two_add_left,
      exteriorPower.ιMulti_two_add_right, smul_add]; abel

private theorem wedgeEndAux_smul_left (c : K) (A B : Module.End K V) :
    wedgeEndAux (c • A) B = c • wedgeEndAux A B :=
  end_ext_ιMulti fun _ _ ↦ by
    simp only [LinearMap.smul_apply, wedgeEndAux_ιMulti, exteriorPower.ιMulti_two_smul_left,
      exteriorPower.ιMulti_two_smul_right, smul_add, smul_comm (2 : K)⁻¹ c]

/-- The symmetric wedge product of two endomorphisms `A, B : Module.End K V` on `⋀[K]^2 V`,
characterized on pure wedges by `wedgeEnd A B (u ∧ v) = 2⁻¹ • (A u ∧ B v + B u ∧ A v)`. -/
noncomputable def wedgeEnd : Module.End K V →ₗ[K] Module.End K V →ₗ[K] Module.End K (⋀[K]^2 V) :=
  LinearMap.mk₂ K wedgeEndAux wedgeEndAux_add_left wedgeEndAux_smul_left
    (fun A B₁ B₂ ↦ by
      rw [wedgeEndAux_comm A, wedgeEndAux_add_left, wedgeEndAux_comm B₁, wedgeEndAux_comm B₂])
    (fun c A B ↦ by rw [wedgeEndAux_comm A, wedgeEndAux_smul_left, wedgeEndAux_comm B])

/-- On a pure wedge `u ∧ v`, `wedgeEnd A B` evaluates to `2⁻¹ • (A u ∧ B v + B u ∧ A v)`. -/
@[simp] theorem wedgeEnd_apply_ιMulti (A B : Module.End K V) (u v : V) :
    wedgeEnd A B (exteriorPower.ιMulti K 2 ![u, v]) = (2 : K)⁻¹ •
      (exteriorPower.ιMulti K 2 ![A u, B v] + exteriorPower.ιMulti K 2 ![B u, A v]) := by
  simp [wedgeEnd, wedgeEndAux_ιMulti]

/-- The symmetric wedge product of endomorphisms is commutative. -/
theorem wedgeEnd_comm (A B : Module.End K V) : wedgeEnd A B = wedgeEnd B A := wedgeEndAux_comm A B

/-- When `2 ≠ 0`, `wedgeEnd A A` equals the induced exterior-square map `exteriorPower.map 2 A`. -/
@[simp] theorem wedgeEnd_self [NeZero (2 : K)] (A : Module.End K V) :
    wedgeEnd A A = exteriorPower.map 2 A :=
  end_ext_ιMulti fun u v ↦ by
    have hAv : ![A u, A v] = A ∘ ![u, v] := by ext i; fin_cases i <;> rfl
    simp [exteriorPower.map_apply_ιMulti, ← two_smul K, smul_smul,
      inv_mul_cancel₀ (NeZero.ne (2 : K)), hAv]

/-- When `2 ≠ 0`, `wedgeEnd id id` is the identity on `⋀[K]^2 V`. -/
theorem wedgeEnd_id [NeZero (2 : K)] :
    wedgeEnd (LinearMap.id : Module.End K V) LinearMap.id = LinearMap.id := by
  rw [wedgeEnd_self, exteriorPower.map_id]

end WedgeEnd

end TauCeti
