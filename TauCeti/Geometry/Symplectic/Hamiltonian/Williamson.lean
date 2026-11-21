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

Williamson's theorem is an instance of a normal form for every element `A ∈ sp(V, ω)` which is
complex linear for a complex structure `J` compatible with `ω`, without any positivity: in a
Darboux basis with `pₖ = J qₖ`, `A` rotates each plane `span(qₖ, pₖ)` with a real angular
frequency `νₖ`, and its quadratic Hamiltonian `½ ω(A v, v)` is `∑ₖ νₖ Iₖ`
(`TauCeti.SymplecticForm.exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic`).
Every frequency contributes two squares of the same sign, so the indices of inertia of this
Hamiltonian are even (`TauCeti.SymplecticForm.even_sigNeg_hamiltonianEndEquiv_symm`,
`TauCeti.SymplecticForm.even_sigPos_hamiltonianEndEquiv_symm`).

The proof constructs a complex structure `J` compatible with `ω` that commutes with `A_Q`
(`TauCeti.SymplecticForm.exists_compatible_isComplexLinearMap_hamiltonianEnd_of_posDef`). It is the
polar normalization `TauCeti.SymplecticForm.polarComplexStructure` of `ω` for the inner product
`polar Q`: in that inner product `ω` is represented by an operator `K`, with `K A_Q = 1`, and the
polar factor `J` of `K` commutes with `K`. Then `A_Q` is a `J`-complex-linear element of
`sp(V, ω)`, so it acts on each complex line of a suitable Darboux basis `(qₖ, J qₖ)` by a complex
number (`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint`). The
symmetry of `polar Q` makes this number purely imaginary
(`TauCeti.SymplecticForm.IsDarbouxBasis.eq_zero_of_hamiltonianEnd_apply_eq`), and positivity of
`Q` fixes its sign. The basis can thus be chosen with `pₖ = J qₖ` for a compatible `J`, on which
`A_Q = -νₖ J`
(`TauCeti.SymplecticForm.exists_compatible_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef`).

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

section ComplexLinear

variable {ω} {J : AlmostComplexStructure V}

/-- **Normal form of a compact element of `sp(V, ω)`.** Let `A ∈ sp(V, ω)` be complex linear for a
complex structure `J` compatible with `ω`. Then there are a Darboux basis `(q₁, p₁, …, qₙ, pₙ)`
with `pₖ = J qₖ` and real numbers `ν₁, …, νₙ` such that `A` rotates every plane `span(qₖ, pₖ)`
with angular frequency `νₖ`, `A qₖ = -νₖ pₖ` and `A pₖ = νₖ qₖ`, and its quadratic Hamiltonian
`v ↦ ½ ω(A v, v)` is `∑ₖ νₖ Iₖ`, for the elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2` of the basis. -/
theorem exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic
    (hJ : ω.Compatible J) (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      (∀ k, b (k, 1) = J (b (k, 0))) ∧
      (∀ k, (A : Module.End ℝ V) (b (k, 0)) = -ν k • b (k, 1) ∧
        (A : Module.End ℝ V) (b (k, 1)) = ν k • b (k, 0)) ∧
      ω.hamiltonianEndEquiv.symm A = ∑ k, ν k • elliptic b k := by
  obtain ⟨n, b, c, hb, hbJ, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint hJ
    (fun _ : Unit ↦ (A : Module.End ℝ V)) (fun _ _ h ↦ absurd rfl h) (fun _ ↦ A.property) fun _ ↦ hA
  -- `A` acts on `span(qₖ, pₖ)` by `a + b i`, and `ω(A qₖ, pₖ) = -ω(qₖ, A pₖ)` reads `a = -a`.
  have hre (k : Fin n) : (c () k).re = 0 := by
    have h : ω ((A : Module.End ℝ V) (b (k, 0))) (b (k, 1)) =
        -ω (b (k, 0)) ((A : Module.End ℝ V) (b (k, 1))) :=
      skewAdjointLieSubalgebra.apply_left A _ _
    rw [(hc () k).1, (hc () k).2] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hb.apply_fst_snd, hb.apply_snd_snd, hb.apply_fst_fst] at h
    simp at h
    linarith
  have hfst (k : Fin n) : (A : Module.End ℝ V) (b (k, 0)) = -(-(c () k).im) • b (k, 1) := by
    rw [(hc () k).1, hre, zero_smul, zero_add, neg_neg]
  have hsnd (k : Fin n) : (A : Module.End ℝ V) (b (k, 1)) = -(c () k).im • b (k, 0) := by
    rw [(hc () k).2, hre, zero_smul, add_zero]
  refine ⟨n, b, fun k ↦ -(c () k).im, hb, hbJ, fun k ↦ ⟨hfst k, hsnd k⟩,
    ω.hamiltonianEndEquiv.symm_apply_eq.2 (Subtype.ext (b.ext fun ⟨j, a⟩ ↦ ?_))⟩
  rw [coe_hamiltonianEndEquiv_apply]
  obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
  · rw [hfst, hb.hamiltonianEnd_sum_smul_elliptic_apply_fst]
  · rw [hsnd, hb.hamiltonianEnd_sum_smul_elliptic_apply_snd]

/-- **The negative index of a compact element of `sp(V, ω)` is even.** If `A ∈ sp(V, ω)` is complex
linear for a complex structure compatible with `ω`, the quadratic Hamiltonian `½ ω(A v, v)` has
even negative index of inertia. -/
theorem even_sigNeg_hamiltonianEndEquiv_symm (hJ : ω.Compatible J)
    (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    Even (sigNeg (ω.hamiltonianEndEquiv.symm A)) := by
  obtain ⟨n, b, ν, -, -, -, h⟩ :=
    exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic hJ A hA
  rw [h, sigNeg_sum_smul_elliptic]
  exact even_two_mul _

/-- **The positive index of a compact element of `sp(V, ω)` is even.** If `A ∈ sp(V, ω)` is complex
linear for a complex structure compatible with `ω`, the quadratic Hamiltonian `½ ω(A v, v)` has
even positive index of inertia. -/
theorem even_sigPos_hamiltonianEndEquiv_symm (hJ : ω.Compatible J)
    (A : skewAdjointLieSubalgebra ω.toBilinForm)
    (hA : IsComplexLinearMap J J (A : Module.End ℝ V)) :
    Even (sigPos (ω.hamiltonianEndEquiv.symm A)) := by
  obtain ⟨n, b, ν, -, -, -, h⟩ :=
    exists_isDarbouxBasis_hamiltonianEndEquiv_symm_eq_sum_smul_elliptic hJ A hA
  rw [h, sigPos_sum_smul_elliptic]
  exact even_two_mul _

end ComplexLinear

variable {ω} in
/-- If the Hamiltonian endomorphism of a quadratic form `R` acts on the plane `span(qₖ, pₖ)` of a
Darboux basis by the complex number `a + c i`, that is `A_R qₖ = a qₖ + c pₖ` and
`A_R pₖ = -c qₖ + a pₖ`, then `a = 0`: the symmetry of `polar R` forces a rotation. -/
theorem IsDarbouxBasis.eq_zero_of_hamiltonianEnd_apply_eq {R : QuadraticForm ℝ V} {n : ℕ}
    {b : Basis (Fin n × Fin 2) ℝ V} (hb : ω.IsDarbouxBasis b)
    {k : Fin n} {a c : ℝ} (h₁ : ω.hamiltonianEnd R (b (k, 0)) = a • b (k, 0) + c • b (k, 1))
    (h₂ : ω.hamiltonianEnd R (b (k, 1)) = -c • b (k, 0) + a • b (k, 1)) : a = 0 := by
  -- `a = ω(A_R qₖ, pₖ) = polar R qₖ pₖ = polar R pₖ qₖ = ω(A_R pₖ, qₖ) = -a`.
  have e₁ := ω.apply_hamiltonianEnd R (b (k, 0)) (b (k, 1))
  have e₂ := ω.apply_hamiltonianEnd R (b (k, 1)) (b (k, 0))
  rw [h₁] at e₁
  rw [h₂, QuadraticMap.polar_comm, ← e₁] at e₂
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hb.apply_fst_snd, hb.apply_snd_snd, hb.apply_snd_fst, hb.apply_fst_fst] at e₂
  simp at e₂
  linarith

variable {ω} in
/-- If the Hamiltonian endomorphism of a quadratic form `R` sends the vector `qₖ` of a Darboux
basis to `a qₖ + c pₖ`, then `c = -2 R(qₖ)`. -/
theorem IsDarbouxBasis.eq_neg_two_mul_of_hamiltonianEnd_apply_eq {R : QuadraticForm ℝ V} {n : ℕ}
    {b : Basis (Fin n × Fin 2) ℝ V} (hb : ω.IsDarbouxBasis b)
    {k : Fin n} {a c : ℝ} (h : ω.hamiltonianEnd R (b (k, 0)) = a • b (k, 0) + c • b (k, 1)) :
    c = -(2 * R (b (k, 0))) := by
  have e := ω.apply_hamiltonianEnd R (b (k, 0)) (b (k, 0))
  rw [h, QuadraticMap.polar_self, nsmul_eq_mul, Nat.cast_ofNat] at e
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hb.apply_fst_fst, hb.apply_snd_fst] at e
  simp at e
  linarith

/-- **Williamson's theorem, with its complex structure.** For a positive definite quadratic form
`Q` on a finite-dimensional symplectic vector space `(V, ω)` there are a complex structure `J`
compatible with `ω`, a Darboux basis `(q₁, p₁, …, qₙ, pₙ)` with `pₖ = J qₖ`, and positive
frequencies `ν₁, …, νₙ` such that the Hamiltonian endomorphism of `Q` rotates every plane
`span(qₖ, pₖ)`: `A_Q qₖ = -νₖ pₖ` and `A_Q pₖ = νₖ qₖ`. Thus `A_Q = -νₖ J` on that plane. -/
theorem exists_compatible_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef (hQ : Q.PosDef) :
    ∃ (J : AlmostComplexStructure V) (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ),
      ω.Compatible J ∧ ω.IsDarbouxBasis b ∧ (∀ k, b (k, 1) = J (b (k, 0))) ∧ (∀ k, 0 < ν k) ∧
        ∀ k, ω.hamiltonianEnd Q (b (k, 0)) = -ν k • b (k, 1) ∧
          ω.hamiltonianEnd Q (b (k, 1)) = ν k • b (k, 0) := by
  obtain ⟨J, hJ, hAJ⟩ := ω.exists_compatible_isComplexLinearMap_hamiltonianEnd_of_posDef hQ
  obtain ⟨n, b, c, hb, hbJ, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint hJ
    (fun _ : Unit ↦ ω.hamiltonianEnd Q) (fun _ _ h ↦ absurd rfl h)
    (fun _ ↦ ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra Q)
    fun _ ↦ hAJ
  -- The action of `A_Q` on the plane `span(qₖ, pₖ)` is by the complex number `a + b i` with
  -- `a = 0` by the symmetry of `polar Q`, and `-b = 2 Q qₖ > 0`.
  have hre (k : Fin n) : (c () k).re = 0 :=
    hb.eq_zero_of_hamiltonianEnd_apply_eq (hc () k).1 (hc () k).2
  have him (k : Fin n) : -(c () k).im = 2 * Q (b (k, 0)) := by
    rw [hb.eq_neg_two_mul_of_hamiltonianEnd_apply_eq (hc () k).1, neg_neg]
  refine ⟨J, n, b, fun k ↦ -(c () k).im, hJ, hb, hbJ, fun k ↦ ?_, fun k ↦ ⟨?_, ?_⟩⟩
  · beta_reduce
    rw [him]
    exact mul_pos two_pos (hQ _ (b.ne_zero _))
  · rw [(hc () k).1, hre, zero_smul, zero_add, neg_neg]
  · rw [(hc () k).2, hre, zero_smul, add_zero]

/-- **Williamson's theorem, Hamiltonian form.** For a positive definite quadratic form `Q` on a
finite-dimensional symplectic vector space `(V, ω)` there are a Darboux basis
`(q₁, p₁, …, qₙ, pₙ)` and positive frequencies `ν₁, …, νₙ` such that the Hamiltonian endomorphism
of `Q` rotates every plane `span(qₖ, pₖ)`: `A_Q qₖ = -νₖ pₖ` and `A_Q pₖ = νₖ qₖ`. -/
theorem exists_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef (hQ : Q.PosDef) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V) (ν : Fin n → ℝ), ω.IsDarbouxBasis b ∧
      (∀ k, 0 < ν k) ∧ ∀ k,
        ω.hamiltonianEnd Q (b (k, 0)) = -ν k • b (k, 1) ∧
        ω.hamiltonianEnd Q (b (k, 1)) = ν k • b (k, 0) := by
  obtain ⟨-, n, b, ν, -, hb, -, hν, hA⟩ :=
    ω.exists_compatible_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef hQ
  exact ⟨n, b, ν, hb, hν, hA⟩

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
  exact ⟨n, b, ν, hb, hν, hb.eq_sum_smul_elliptic_of_hamiltonianEnd_apply_eq hA⟩

end TauCeti.SymplecticForm
