/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.UqSl2.ClebschGordan.Basic
public import TauCeti.QuantumGroups.UqSl2.LadderModule.Schur
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# Inverse Clebsch–Gordan maps and Casimir spectral projections

The normalized Clebsch–Gordan inclusions admit module-linear projections back to each
signed ladder summand. Their composites are the spectral projections of the Casimir:
the projection onto channel `j` is the Lagrange polynomial which is one at that channel's
Casimir scalar and zero at the other channel scalars, evaluated on the Casimir action.
Thus each channel is exactly a Casimir eigenspace, and these projections resolve the
identity, commute with every module endomorphism, and are natural with respect to module
maps on the two tensor factors via `LadderModule.schurScalar`. The projections extract
components in the normalized highest-vector and lowering string bases, as needed when
comparing iterated tensor decompositions.

The inclusions and their normalization are those of `clebschGordanInclusion`; no choice of
basis or normalization is made in defining the inverse maps.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter VII, for the
  signed Clebsch–Gordan decomposition.
-/

public noncomputable section

namespace TauCeti.UqSl2

open BialgebraModule LadderModule

variable {q : ℂ} [Fact (q ≠ 0)] {m n : ℕ} {ε δ : ℤˣ}

/-- The inverse Clebsch–Gordan map onto channel `j`, with the normalization of
`clebschGordanInclusion`. -/
def clebschGordanProjection (hq : IsGenericQuantumParameter q) (j : Fin (min m n + 1)) :
    Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ) →ₗ[UqSl2 q]
      LadderModule q (m + n - 2 * j) (ε * δ) :=
  (LinearMap.proj j).comp (clebschGordanEquiv hq).symm.toLinearMap

/-- The projections are the components of the inverse decomposition map. -/
theorem clebschGordanProjection_apply (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
    clebschGordanProjection hq j x = (clebschGordanEquiv hq).symm x j := (rfl)

/-- The inverse map recovers the `j`-th component of a Clebsch–Gordan expansion. -/
@[simp]
theorem clebschGordanProjection_equiv (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1))
    (x : Π i : Fin (min m n + 1), LadderModule q (m + n - 2 * i) (ε * δ)) :
    clebschGordanProjection hq j (clebschGordanEquiv hq x) = x j := by
  simp [clebschGordanProjection_apply]

/-- Projection onto an included channel gives its corresponding single component. -/
theorem clebschGordanProjection_inclusion (hq : IsGenericQuantumParameter q)
    (i j : Fin (min m n + 1)) (x : LadderModule q (m + n - 2 * j) (ε * δ)) :
    clebschGordanProjection hq i (clebschGordanInclusion hq j x) =
      (Pi.single (M := fun k : Fin (min m n + 1) =>
      LadderModule q (m + n - 2 * k) (ε * δ)) j x) i := by
  rw [← clebschGordanEquiv_single hq j x, clebschGordanProjection_equiv]

/-- A channel projection is a left inverse of its normalized inclusion. -/
@[simp]
theorem clebschGordanProjection_inclusion_self (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1)) (x : LadderModule q (m + n - 2 * j) (ε * δ)) :
    clebschGordanProjection hq j (clebschGordanInclusion hq j x) = x := by
  simp [clebschGordanProjection_inclusion]

/-- Different channels are annihilated by the projection. -/
@[simp]
theorem clebschGordanProjection_inclusion_of_ne (hq : IsGenericQuantumParameter q)
    {i j : Fin (min m n + 1)} (hij : i ≠ j)
    (x : LadderModule q (m + n - 2 * j) (ε * δ)) :
    clebschGordanProjection hq i (clebschGordanInclusion hq j x) = 0 := by
  simp [clebschGordanProjection_inclusion, hij.symm]

/-- The normalized channel projections reconstruct every tensor vector. -/
theorem sum_clebschGordanInclusion_projection (hq : IsGenericQuantumParameter q)
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
    ∑ j, clebschGordanInclusion hq j (clebschGordanProjection hq j x) = x := by
  simp only [clebschGordanProjection_apply, ← clebschGordanEquiv_apply,
    LinearEquiv.apply_symm_apply]

/-- The channel endomorphisms resolve the identity as module maps. -/
theorem sum_clebschGordanInclusion_comp_projection (hq : IsGenericQuantumParameter q) :
    ∑ j : Fin (min m n + 1),
      (clebschGordanInclusion (ε := ε) (δ := δ) hq j).comp
        (clebschGordanProjection hq j) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  simpa using sum_clebschGordanInclusion_projection hq x

/-- The channel projection followed by its inclusion is the explicit Casimir spectral
projection: evaluate the corresponding Lagrange basis polynomial on the Casimir action. -/
theorem clebschGordanInclusion_comp_projection_eq_aeval (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1)) :
    ((clebschGordanInclusion (ε := ε) (δ := δ) hq j).comp
      (clebschGordanProjection hq j)).restrictScalars ℂ =
    Polynomial.aeval
      (Algebra.lsmul ℂ ℂ
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) (casimir q))
      (Lagrange.basis Finset.univ
        (fun i : Fin (min m n + 1) =>
          casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) j) := by
  classical
  apply LinearMap.ext
  intro x
  conv_rhs => rw [← sum_clebschGordanInclusion_projection hq x]
  rw [map_sum]
  have heval (i : Fin (min m n + 1)) :
      (Lagrange.basis Finset.univ
        (fun i : Fin (min m n + 1) =>
          casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) j).eval
        (casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) =
        if j = i then 1 else 0 := by
    split_ifs with h
    · subst i
      exact Lagrange.eval_basis_self
        (clebschGordan_casimirScalar_injective hq).injOn (Finset.mem_univ j)
    · exact Lagrange.eval_basis_of_ne (v := fun i : Fin (min m n + 1) =>
        casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) h
        (Finset.mem_univ i)
  have hact (i : Fin (min m n + 1))
      (y : LadderModule q (m + n - 2 * i) (ε * δ)) :
      Polynomial.aeval
        (Algebra.lsmul ℂ ℂ
          (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) (casimir q))
        (Lagrange.basis Finset.univ
          (fun i : Fin (min m n + 1) =>
            casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) j)
        (clebschGordanInclusion hq i y) =
          (if j = i then 1 else 0 : ℂ) • clebschGordanInclusion hq i y := by
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (f := Algebra.lsmul ℂ ℂ
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) (casimir q))
      (casimir_smul_clebschGordanInclusion hq i y), heval]
  simp only [hact, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, LinearMap.restrictScalars_apply, LinearMap.comp_apply]

/-- A channel is exactly the Casimir eigenspace with its highest-weight scalar. -/
theorem range_clebschGordanInclusion_eq_eigenspace (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1)) :
    (LinearMap.range (clebschGordanInclusion (ε := ε) (δ := δ) hq j)).restrictScalars ℂ =
      (Algebra.lsmul ℂ ℂ
        (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ))
        (casimir q)).eigenspace
          (casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (j : ℕ)))) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr (casimir_smul_clebschGordanInclusion hq j y)
  · intro hx
    have hp := congrArg (fun f => f x)
      (clebschGordanInclusion_comp_projection_eq_aeval (ε := ε) (δ := δ) hq j)
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul
      (Module.End.mem_eigenspace_iff.mp hx), Lagrange.eval_basis_self
        (clebschGordan_casimirScalar_injective hq).injOn (Finset.mem_univ j), one_smul] at hp
    exact ⟨clebschGordanProjection hq j x, hp⟩

/-- Channel projection commutes with every module endomorphism of the tensor product. -/
theorem clebschGordanInclusion_projection_naturality (hq : IsGenericQuantumParameter q)
    (j : Fin (min m n + 1))
    (φ : Module.End (UqSl2 q)
      (Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
    clebschGordanInclusion hq j (clebschGordanProjection hq j (φ x)) =
      φ (clebschGordanInclusion hq j (clebschGordanProjection hq j x)) := by
  have hp (y : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
      clebschGordanInclusion hq j (clebschGordanProjection hq j y) =
        Polynomial.aeval (casimir q)
          (Lagrange.basis Finset.univ
            (fun i : Fin (min m n + 1) =>
              casimirScalar q ((ε * δ : ℤˣ) * q ^ (m + n - 2 * (i : ℕ)))) j) • y := by
    have h := congrArg (fun f => f y)
      (clebschGordanInclusion_comp_projection_eq_aeval (ε := ε) (δ := δ) hq j)
    simpa only [Polynomial.aeval_algHom, AlgHom.comp_apply, Algebra.lsmul_apply,
      LinearMap.restrictScalars_apply, LinearMap.comp_apply] using h
  rw [hp, hp, map_smul]

/-- At a generic parameter, the tensor product of endomorphisms of two signed ladder modules acts
by the product of their Schur scalars. -/
theorem tensorMap_apply_eq_schurScalar_smul (hq : IsGenericQuantumParameter q)
    (f : Module.End (UqSl2 q) (LadderModule q m ε))
    (g : Module.End (UqSl2 q) (LadderModule q n δ))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
    tensorMap ℂ (UqSl2 q) f g x = (schurScalar f * schurScalar g) • x := by
  induction x using Tensor.inductionOn with
  | htmul a b =>
    rw [tensorMap_tmul, apply_eq_schurScalar_smul hq f a, apply_eq_schurScalar_smul hq g b,
      ← smul_tmul', tmul_smul, smul_smul, mul_comm]
  | hadd x y hx hy => rw [map_add, hx, hy, smul_add]

/-- Naturality of the Clebsch–Gordan inclusions with respect to `UqSl2 q`-endomorphisms of the two
tensor factors. -/
theorem tensorMap_clebschGordanInclusion (hq : IsGenericQuantumParameter q)
    (f : Module.End (UqSl2 q) (LadderModule q m ε))
    (g : Module.End (UqSl2 q) (LadderModule q n δ))
    (j : Fin (min m n + 1)) (x : LadderModule q (m + n - 2 * j) (ε * δ)) :
    tensorMap ℂ (UqSl2 q) f g (clebschGordanInclusion hq j x) =
      (schurScalar f * schurScalar g) • clebschGordanInclusion hq j x :=
  tensorMap_apply_eq_schurScalar_smul hq f g _

/-- Naturality of the inverse Clebsch–Gordan projections with respect to `UqSl2 q`-endomorphisms
of the two tensor factors. -/
theorem clebschGordanProjection_tensorMap (hq : IsGenericQuantumParameter q)
    (f : Module.End (UqSl2 q) (LadderModule q m ε))
    (g : Module.End (UqSl2 q) (LadderModule q n δ))
    (j : Fin (min m n + 1))
    (x : Tensor ℂ (UqSl2 q) (LadderModule q m ε) (LadderModule q n δ)) :
    clebschGordanProjection hq j (tensorMap ℂ (UqSl2 q) f g x) =
      (schurScalar f * schurScalar g) • clebschGordanProjection hq j x := by
  rw [tensorMap_apply_eq_schurScalar_smul hq f g x, LinearMap.map_smul_of_tower]

/-- Naturality of Clebsch–Gordan inclusions and projections across arbitrary factor intertwiners
`f : L_m^ε → L_{m'}^{ε'}` and `g : L_n^δ → L_{n'}^{δ'}` on the ladder vectors `v_l` (covering both
`l = 0` and the normalized `F`-ladder vectors `0 ≤ l ≤ m + n - 2j`). -/
theorem clebschGordanProjection_tensorMap_inclusion_vec (hq : IsGenericQuantumParameter q)
    {m' n' : ℕ} {ε' δ' : ℤˣ}
    (f : LadderModule q m ε →ₗ[UqSl2 q] LadderModule q m' ε')
    (g : LadderModule q n δ →ₗ[UqSl2 q] LadderModule q n' δ')
    (j : Fin (min m n + 1)) (j' : Fin (min m' n' + 1)) (l : ℤ) :
    clebschGordanProjection hq j'
        (tensorMap ℂ (UqSl2 q) f g (clebschGordanInclusion hq j (vec q _ _ l))) =
      (if (j : ℕ) = (j' : ℕ) then schurScalar f * schurScalar g else 0) • vec q _ _ l := by
  by_cases hm : m = m' ∧ ε = ε'
  · by_cases hn : n = n' ∧ δ = δ'
    · rcases hm with ⟨rfl, rfl⟩
      rcases hn with ⟨rfl, rfl⟩
      rw [tensorMap_clebschGordanInclusion hq f g j, LinearMap.map_smul_of_tower]
      by_cases hj : j = j'
      · subst hj
        simp
      · have hjv : (j : ℕ) ≠ (j' : ℕ) := Fin.val_ne_of_ne hj
        rw [clebschGordanProjection_inclusion_of_ne hq (Ne.symm hj), ite_eq_right hjv,
          smul_zero, zero_smul]
    · have hne : n ≠ n' ∨ δ ≠ δ' := by tauto
      rw [hom_eq_zero_of_ne hq hne g, schurScalar_zero, mul_zero, ite_self, zero_smul,
        tensorMap_zero_right, LinearMap.zero_apply, map_zero]
  · have hne : m ≠ m' ∨ ε ≠ ε' := by tauto
    rw [hom_eq_zero_of_ne hq hne f, schurScalar_zero, zero_mul, ite_self, zero_smul,
      tensorMap_zero_left, LinearMap.zero_apply, map_zero]

end TauCeti.UqSl2
