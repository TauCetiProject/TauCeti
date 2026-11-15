/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Elliptic
public import TauCeti.Geometry.Symplectic.WeightDecomposition

/-!
# Williamson's normal form of a positive definite quadratic Hamiltonian

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `Q` a positive definite
quadratic form on `V`. **Williamson's theorem** for `Q` says that there are a Darboux basis
`b = (q₁, p₁, …, qₙ, pₙ)` of `(V, ω)` and positive numbers `ν₁, …, νₙ`, the *symplectic
eigenvalues* or *frequencies* of `Q`, such that

`Q = ∑ₖ νₖ (xₖ² + yₖ²) / 2`

in the dual coordinates `(x₁, y₁, …, xₙ, yₙ)`, that is `Q = ∑ₖ νₖ Iₖ` for the elliptic blocks
`Iₖ` of `b` (`TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`).
Equivalently, the Hamiltonian endomorphism `A_Q` of `Q` (`TauCeti.SymplecticForm.hamiltonianEnd`),
with the convention `ω (A_Q v) w = polar Q v w`, acts on each plane `span(qₖ, pₖ)` as

`A_Q qₖ = -νₖ pₖ`,  `A_Q pₖ = νₖ qₖ`

(`TauCeti.SymplecticForm.exists_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef`), so that the
eigenvalues of `A_Q` are `±i νₖ` and its flow rotates each plane with angular frequency `νₖ`.
This is the elliptic case of Williamson's normal forms: a positive definite quadratic Hamiltonian
lies in the span of the elliptic blocks of a Darboux basis, which form a nondegenerate family
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`).

The proof constructs a complex structure `J` compatible with `ω` that commutes with `A_Q`
(`TauCeti.SymplecticForm.exists_compatible_isComplexLinearMap_hamiltonianEnd_of_posDef`). It is the
polar normalization `TauCeti.SymplecticForm.polarComplexStructure` of `ω` for the inner product
`polar Q`: in that inner product `ω` is represented by an operator `K`, with `K A_Q = 1`, and the
polar factor `J` of `K` commutes with `K`. Then `A_Q` is a `J`-complex-linear element of
`sp(V, ω)`, so it acts on each complex line of a suitable Darboux basis `(qₖ, J qₖ)` by a complex
number (`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint`). The
symmetry of `polar Q` makes this number purely imaginary, and positivity of `Q` fixes its sign.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6.
-/

public section

open Module

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V) {Q : QuadraticForm ℝ V}

/-- A positive definite quadratic form `Q` on a symplectic vector space `(V, ω)` admits a complex
structure `J` compatible with `ω` that commutes with the Hamiltonian endomorphism `A_Q`. It is the
polar normalization of `ω` for the inner product `polar Q`. -/
theorem exists_compatible_isComplexLinearMap_hamiltonianEnd_of_posDef (hQ : Q.PosDef) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧
      IsComplexLinearMap J J (ω.hamiltonianEnd Q) := by
  -- The inner product `⟪u, v⟫ = polar Q u v` on `V`.
  let core : InnerProductSpace.Core ℝ V :=
    { inner u v := QuadraticMap.polar Q u v
      conj_inner_symm u v := by simp [QuadraticMap.polar_comm]
      re_inner_nonneg v := by
        simpa [QuadraticMap.polar_self] using mul_nonneg zero_le_two (hQ.nonneg v)
      add_left u v w := QuadraticMap.polar_add_left Q u v w
      smul_left u v r := by simp [QuadraticMap.polar_smul_left]
      definite v hv := hQ.anisotropic v (by simpa [QuadraticMap.polar_self] using hv) }
  let := core.toNormedAddCommGroup
  let : InnerProductSpace ℝ V := InnerProductSpace.ofCore core.toCore
  have hinner (u v : V) : inner ℝ u v = QuadraticMap.polar Q u v := (rfl)
  -- With `K` the operator of `ω`, `⟪K u, v⟫ = ω u v`, we have `K (A_Q v) = v`.
  have hKA (v : V) : ω.innerOperator (ω.hamiltonianEnd Q v) = v :=
    ext_inner_right ℝ fun w ↦ by rw [inner_innerOperator_apply, apply_hamiltonianEnd, hinner]
  refine ⟨ω.polarComplexStructure, ω.compatible_polarComplexStructure,
    (isComplexLinearMap_iff_apply _ _ _).2 fun v ↦ ω.innerOperator_injective ?_⟩
  rw [hKA, ← polarComplexStructure_apply_innerOperator, hKA]

/-- **Williamson's theorem, Hamiltonian form.** For a positive definite quadratic form `Q` on a
finite-dimensional symplectic vector space `(V, ω)` there are a Darboux basis
`(q₁, p₁, …, qₙ, pₙ)` and positive frequencies `ν₁, …, νₙ` such that the Hamiltonian endomorphism
of `Q` rotates every plane `span(qₖ, pₖ)`: `A_Q qₖ = -νₖ pₖ` and `A_Q pₖ = νₖ qₖ`. -/
theorem exists_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef (hQ : Q.PosDef) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      (∀ k, 0 < ν k) ∧ ∀ k,
        ω.hamiltonianEnd Q (b (k, 0)) = -ν k • b (k, 1) ∧
        ω.hamiltonianEnd Q (b (k, 1)) = ν k • b (k, 0) := by
  obtain ⟨J, hJ, hAJ⟩ := ω.exists_compatible_isComplexLinearMap_hamiltonianEnd_of_posDef hQ
  obtain ⟨n, b, c, hb, -, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint hJ
    (fun _ : Unit ↦ ω.hamiltonianEnd Q) (fun _ _ h ↦ absurd rfl h)
    (fun _ ↦ ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra Q)
    fun _ ↦ hAJ
  set A := ω.hamiltonianEnd Q
  -- The action of `A_Q` on the plane `span(qₖ, pₖ)` is by the complex number `a + b i` with
  -- `a = polar Q qₖ pₖ = -polar Q pₖ qₖ`, so `a = 0`, and `-b = polar Q qₖ qₖ = 2 Q qₖ > 0`.
  have hre (k : Fin n) : (c () k).re = 0 := by
    have h₁ := ω.apply_hamiltonianEnd Q (b (k, 0)) (b (k, 1))
    have h₂ := ω.apply_hamiltonianEnd Q (b (k, 1)) (b (k, 0))
    rw [(hc () k).1] at h₁
    rw [(hc () k).2, QuadraticMap.polar_comm, ← h₁] at h₂
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hb.apply_fst_snd, hb.apply_snd_snd, hb.apply_snd_fst, hb.apply_fst_fst] at h₂
    simp at h₂
    linarith
  have him (k : Fin n) : -(c () k).im = 2 * Q (b (k, 0)) := by
    have h := ω.apply_hamiltonianEnd Q (b (k, 0)) (b (k, 0))
    rw [(hc () k).1, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hb.apply_fst_fst, hb.apply_snd_fst] at h
    simpa using h
  refine ⟨n, b, fun k ↦ -(c () k).im, hb, fun k ↦ ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · beta_reduce
    rw [him]
    exact mul_pos two_pos (hQ _ (b.ne_zero _))
  · rw [(hc () k).1, hre, zero_smul, zero_add, neg_neg]
  · rw [(hc () k).2, hre, zero_smul, add_zero]

/-- **Williamson's theorem.** A positive definite quadratic form `Q` on a finite-dimensional
symplectic vector space `(V, ω)` is a sum of harmonic oscillators in suitable Darboux
coordinates: there are a Darboux basis `b = (q₁, p₁, …, qₙ, pₙ)` and positive frequencies
`ν₁, …, νₙ` with `Q = ∑ₖ νₖ Iₖ`, where `Iₖ = (xₖ² + yₖ²) / 2` are the elliptic blocks of `b`
(`TauCeti.SymplecticForm.elliptic`). Thus `Q v = ∑ₖ νₖ / 2 (xₖ² + yₖ²)` in the coordinates
`(x₁, y₁, …, xₙ, yₙ)` of `v` (`TauCeti.SymplecticForm.elliptic_apply`), and `Q` lies in the
span of the nondegenerate family `(Iₖ)`
(`TauCeti.SymplecticForm.IsDarbouxBasis.isNondegenerateQuadraticFamily_elliptic`). -/
theorem exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef (hQ : Q.PosDef) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      (∀ k, 0 < ν k) ∧ Q = ∑ k, ν k • elliptic b k := by
  obtain ⟨n, b, ν, hb, hν, hA⟩ := ω.exists_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef hQ
  refine ⟨n, b, ν, hb, hν, ω.hamiltonianEnd_injective (b.ext fun ⟨j, a⟩ ↦ ?_)⟩
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [(hA j).1, hb.hamiltonianEnd_sum_smul_elliptic_apply_fst]
  · rw [(hA j).2, hb.hamiltonianEnd_sum_smul_elliptic_apply_snd]

end TauCeti.SymplecticForm
