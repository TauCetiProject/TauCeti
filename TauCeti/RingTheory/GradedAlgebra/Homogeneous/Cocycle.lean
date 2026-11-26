/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Coeff
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Generator
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Units

/-!
# Gradings of the free module of rank one as Laurent cocycles

Let `A` be a commutative `R`-algebra graded by `ℤ` through `𝒜`, that is, with an action of the
multiplicative group `𝔾_m` on `Spec A`, the coaction `A → A[T;T⁻¹]` being
`ρ = decomposeLaurent 𝒜 : a ↦ ∑ₙ aₙ Tⁿ`. A `𝔾_m`-linearisation of the trivial line bundle on
`Spec A` is a unit `u = φ(t, x)` of `Γ(𝔾_m × Spec A) = A[T;T⁻¹]` satisfying the cocycle identity
`φ(s t, x) = φ(t, x) φ(s, t · x)` and the unit condition `φ(1, x) = 1`
(Mumford–Fogarty–Kirwan, Chapter 1, §3). Comparing the coefficients of `sᵉ` in the cocycle
identity, it says `ρ(uₑ) * u = uₑ Tᵉ` for every coefficient `uₑ` of `u`; this is
`TauCeti.GradedAlgebra.IsGradingCocycle 𝒜 u`.

Such cocycles are the same as gradings of the `A`-module `A` compatible with `𝒜`:

* a cocycle `u` gives the grading `cocycleGrading 𝒜 u`, whose degree-`n` piece consists of the `m`
  with `ρ(m) * u = m Tⁿ`; it is compatible with `𝒜` and is a direct sum decomposition
  (`isInternal_cocycleGrading`), the component of `m` in degree `n` being the coefficient of `Tⁿ`
  in `ρ(m) * u`;
* a compatible grading `ℳ` gives the cocycle `decomposeLaurent ℳ 1`, the Laurent polynomial of the
  homogeneous components of `1`.

These constructions are inverse to each other (`gradingCocycleEquiv`). The shift `A(d)`, with
degree-`n` piece `𝒜 (n + d)`, corresponds to the cocycle `T (-d)` (`cocycleGrading_T`): the
element `1` of `A(d)` is homogeneous of degree `-d`.

Graded isomorphisms between two such gradings are multiplications by units `v` of `A`, and they
exist exactly when the cocycles are cohomologous: `ρ(v) * u' = v u`
(`exists_linearEquiv_iff_exists_mul_eq`). Two cocycles `T c` and `T c'` are cohomologous exactly
when `c - c'` is the degree of a homogeneous unit (`exists_mul_T_eq_iff`), and, when `Spec A` is
connected, every cocycle is cohomologous to some `T c` (`IsGradingCocycle.exists_mul_eq_T`). So
on a connected spectrum, the cocycles up to cohomology, that is, the `𝔾_m`-linearisations of the
trivial line bundle up to isomorphism, are classified by `ShiftClassGroup 𝒜`.

## Main definitions

* `TauCeti.GradedAlgebra.IsGradingCocycle 𝒜 u`: `u ∈ A[T;T⁻¹]` satisfies the cocycle and unit
  conditions of a `𝔾_m`-linearisation of the trivial line bundle on `Spec A`.
* `TauCeti.GradedAlgebra.cocycleGrading 𝒜 u`: the grading of the `A`-module `A` defined by `u`.
* `TauCeti.GradedAlgebra.gradingCocycleEquiv 𝒜`: cocycles are equivalent to compatible gradings.

## Main results

* `TauCeti.GradedAlgebra.decomposeLaurent_cocycleGrading`: for any decomposition of
  `cocycleGrading 𝒜 u`, the Laurent polynomial of the components of `m` is `ρ(m) * u`.
* `TauCeti.GradedAlgebra.isInternal_cocycleGrading`: a cocycle defines a grading.
* `TauCeti.GradedAlgebra.isGradingCocycle_decomposeLaurent_one` and
  `TauCeti.GradedAlgebra.cocycleGrading_decomposeLaurent_one`: a compatible grading defines a
  cocycle, from which it is recovered.
* `TauCeti.GradedAlgebra.exists_linearEquiv_iff_exists_mul_eq`: graded isomorphisms correspond to
  cohomologous cocycles.
* `TauCeti.GradedAlgebra.IsGradingCocycle.exists_mul_eq_T`: on a connected spectrum every cocycle
  is cohomologous to a monomial `T c`.

## References

* D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*, 3rd ed., Springer (1994),
  Chapter 1, §3.
-/

public section

open DirectSum LaurentPolynomial

namespace TauCeti.GradedAlgebra

noncomputable section

section Semiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The cocycle and unit conditions of a `𝔾_m`-linearisation `u` of the trivial line bundle on
`Spec A`, for the `𝔾_m`-action given by the grading `𝒜`. The first is the coefficient of `sᵉ` in
the cocycle identity `u(s t) = ρₜ(u(s)) u(t)`, with `ρ = decomposeLaurent 𝒜` the coaction; the
second says `u(1) = 1`. -/
structure IsGradingCocycle (u : A[T;T⁻¹]) : Prop where
  /-- The cocycle identity, coefficient by coefficient. -/
  decomposeLaurent_coeff_mul (e : ℤ) : decomposeLaurent 𝒜 (u.coeff e) * u = C (u.coeff e) * T e
  /-- The unit condition: `u` evaluates to `1` at `T = 1`. -/
  eval₂_one : eval₂ (RingHom.id A) 1 u = 1

/-- The grading of the `A`-module `A` defined by `u ∈ A[T;T⁻¹]`: its degree-`n` piece consists of
the `m` with `ρ(m) * u = m Tⁿ`, where `ρ = decomposeLaurent 𝒜`. It is a grading when `u` is a
cocycle (`isInternal_cocycleGrading`). -/
def cocycleGrading (u : A[T;T⁻¹]) (n : ℤ) : Submodule R A where
  carrier := {m | decomposeLaurent 𝒜 m * u = C m * T n}
  zero_mem' := by simp
  add_mem' {m m'} hm hm' := by
    simp only [Set.mem_ofPred_eq, map_add, add_mul] at hm hm' ⊢
    rw [hm, hm']
  smul_mem' r m hm := by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def] at hm ⊢
    rw [decomposeLaurent_mul_of_mem 𝒜 𝒜 (SetLike.algebraMap_mem_graded 𝒜 r), mul_assoc, hm]
    simp [mul_assoc]

@[simp]
theorem mem_cocycleGrading_iff {u : A[T;T⁻¹]} {n : ℤ} {m : A} :
    m ∈ cocycleGrading 𝒜 u n ↔ decomposeLaurent 𝒜 m * u = C m * T n :=
  Iff.rfl

/-- The grading defined by any `u ∈ A[T;T⁻¹]` is compatible with `𝒜`. -/
instance cocycleGrading.gradedSMul (u : A[T;T⁻¹]) : SetLike.GradedSMul 𝒜 (cocycleGrading 𝒜 u) where
  smul_mem {i j a m} ha hm := by
    rw [smul_eq_mul, mem_cocycleGrading_iff, decomposeLaurent_mul_of_mem 𝒜 𝒜 ha, mul_assoc,
      (mem_cocycleGrading_iff 𝒜).mp hm, vadd_eq_add, T_add, map_mul]
    ring

variable {𝒜} in
/-- The coaction twisted by `u` recovers the components of an element of the direct sum of the
pieces of `cocycleGrading 𝒜 u`. -/
private theorem coeff_decomposeLaurent_mul_coe {u : A[T;T⁻¹]} (x : ⨁ n, cocycleGrading 𝒜 u n)
    (n : ℤ) : (decomposeLaurent 𝒜 (DirectSum.coeAddMonoidHom (cocycleGrading 𝒜 u) x) * u).coeff n =
      (x n : A) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of, (mem_cocycleGrading_iff 𝒜).mp y.property,
      ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, DirectSum.of_apply]
    by_cases h : i = n
    · subst h
      simp
    · simp [h]
  | add x y hx hy => simp [add_mul, hx, hy]

/-- For any decomposition of the grading `cocycleGrading 𝒜 u`, the Laurent polynomial of the
components of `m` is the coaction of `m` twisted by `u`. -/
theorem decomposeLaurent_cocycleGrading {u : A[T;T⁻¹]} [Decomposition (cocycleGrading 𝒜 u)]
    (m : A) : decomposeLaurent (cocycleGrading 𝒜 u) m = decomposeLaurent 𝒜 m * u := by
  ext n
  have hm := Decomposition.left_inv (ℳ := cocycleGrading 𝒜 u) m
  rw [Decomposition.decompose'_eq] at hm
  rw [coeff_decomposeLaurent, ← coeff_decomposeLaurent_mul_coe (decompose (cocycleGrading 𝒜 u) m),
    hm]

/-- The Laurent polynomial of the components of `1` for a decomposition of `cocycleGrading 𝒜 u` is
`u` itself. -/
@[simp]
theorem decomposeLaurent_one_cocycleGrading {u : A[T;T⁻¹]} [Decomposition (cocycleGrading 𝒜 u)] :
    decomposeLaurent (cocycleGrading 𝒜 u) 1 = u := by
  rw [decomposeLaurent_cocycleGrading, decomposeLaurent_one, one_mul]

variable {𝒜}

/-- For a cocycle `u`, every coefficient of the coaction of `m` twisted by `u` is homogeneous for
the grading defined by `u`, of the degree of its exponent. -/
theorem IsGradingCocycle.coeff_mem_cocycleGrading {u : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u)
    (m : A) (n : ℤ) : (decomposeLaurent 𝒜 m * u).coeff n ∈ cocycleGrading 𝒜 u n := by
  induction m using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add m m' hm hm' => simpa [add_mul] using add_mem hm hm'
  | @homogeneous d m =>
    -- For `m` homogeneous of degree `d`, the coefficient is `m * u_{n - d}`.
    rw [decomposeLaurent_of_mem 𝒜 m.property, mul_assoc, mul_comm (T d), coeff_C_mul,
      coeff_mul_T, mem_cocycleGrading_iff, decomposeLaurent_mul_of_mem 𝒜 𝒜 m.property, mul_assoc,
      hu.decomposeLaurent_coeff_mul, map_mul]
    calc C (m : A) * T d * (C (u.coeff (n - d)) * T (n - d))
        = C (m : A) * C (u.coeff (n - d)) * (T d * T (n - d)) := by ring
      _ = C (m : A) * C (u.coeff (n - d)) * T n := by rw [← T_add, add_sub_cancel]

/-- The pieces of the grading defined by a cocycle `u` form an internal direct sum. -/
theorem isInternal_cocycleGrading {u : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u) :
    DirectSum.IsInternal (cocycleGrading 𝒜 u) := by
  classical
  refine ⟨fun x y hxy ↦ DFinsupp.ext fun n ↦ Subtype.ext ?_, fun m ↦ ?_⟩
  · rw [← coeff_decomposeLaurent_mul_coe x, ← coeff_decomposeLaurent_mul_coe y, hxy]
  · -- The coefficients of `ρ(m) * u` are homogeneous, and they sum to `m * u(1) = m`.
    set p := decomposeLaurent 𝒜 m * u
    refine ⟨∑ n ∈ p.coeff.support, DirectSum.of _ n ⟨p.coeff n, hu.coeff_mem_cocycleGrading m n⟩,
      ?_⟩
    have hp : eval₂ (RingHom.id A) 1 p = m := by
      rw [map_mul, eval₂_one_decomposeLaurent, hu.eval₂_one, mul_one]
    simp only [map_sum, coeAddMonoidHom_of]
    rwa [eval₂_id_one_eq_sum_coeff] at hp

/-- The decomposition of `A` by the grading defined by a cocycle. -/
abbrev IsGradingCocycle.decomposition {u : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u) :
    Decomposition (cocycleGrading 𝒜 u) :=
  (isInternal_cocycleGrading hu).chooseDecomposition

/-- The component of `m` in degree `n` for the grading defined by a cocycle `u` is the coefficient
of `Tⁿ` in the coaction of `m` twisted by `u`. -/
theorem coe_decompose_cocycleGrading {u : A[T;T⁻¹]} [Decomposition (cocycleGrading 𝒜 u)] (m : A)
    (n : ℤ) : (decompose (cocycleGrading 𝒜 u) m n : A) = (decomposeLaurent 𝒜 m * u).coeff n := by
  rw [← coeff_decomposeLaurent, decomposeLaurent_cocycleGrading]

/-- A cocycle is a unit of `A[T;T⁻¹]`. -/
theorem IsGradingCocycle.isUnit {u : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u) : IsUnit u := by
  let := hu.decomposition
  simpa using isUnit_decomposeLaurent_one 𝒜 (cocycleGrading 𝒜 u)

variable (𝒜)

/-- The Laurent polynomial of the homogeneous components of `1` for a grading `ℳ` of the
`A`-module `A` compatible with `𝒜` is a cocycle. -/
theorem isGradingCocycle_decomposeLaurent_one {σ : Type*} [SetLike σ A] [AddSubmonoidClass σ A]
    (ℳ : ℤ → σ) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ] :
    IsGradingCocycle 𝒜 (decomposeLaurent ℳ 1) where
  decomposeLaurent_coeff_mul e := by
    rw [coeff_decomposeLaurent]
    exact decomposeLaurent_decompose_one_mul 𝒜 ℳ e
  eval₂_one := eval₂_one_decomposeLaurent ℳ 1

/-- A grading `ℳ` of the `A`-module `A` compatible with `𝒜` is recovered from its cocycle. -/
theorem cocycleGrading_decomposeLaurent_one (ℳ : ℤ → Submodule R A) [Decomposition ℳ]
    [SetLike.GradedSMul 𝒜 ℳ] : cocycleGrading 𝒜 (decomposeLaurent ℳ 1) = ℳ := by
  ext n m
  rw [mem_cocycleGrading_iff, ← decomposeLaurent_mul ℳ 𝒜, mul_one,
    decomposeLaurent_eq_C_mul_T_iff]

/-- **Linearisations of the trivial line bundle as gradings.** Cocycles `u ∈ A[T;T⁻¹]` for the
grading `𝒜` correspond to the gradings of the `A`-module `A` compatible with `𝒜`: a cocycle `u`
gives `cocycleGrading 𝒜 u`, and a grading `ℳ` gives the Laurent polynomial of the homogeneous
components of `1`. -/
def gradingCocycleEquiv :
    {u : A[T;T⁻¹] // IsGradingCocycle 𝒜 u} ≃
      {ℳ : ℤ → Submodule R A // DirectSum.IsInternal ℳ ∧ SetLike.GradedSMul 𝒜 ℳ} where
  toFun u := ⟨cocycleGrading 𝒜 u, isInternal_cocycleGrading u.property, inferInstance⟩
  invFun ℳ :=
    letI := ℳ.property.1.chooseDecomposition
    haveI := ℳ.property.2
    ⟨decomposeLaurent ℳ.val 1, isGradingCocycle_decomposeLaurent_one 𝒜 ℳ.val⟩
  left_inv u := by
    let := u.property.decomposition
    exact Subtype.ext (decomposeLaurent_one_cocycleGrading 𝒜)
  right_inv ℳ := by
    let := ℳ.property.1.chooseDecomposition
    have := ℳ.property.2
    exact Subtype.ext (cocycleGrading_decomposeLaurent_one 𝒜 ℳ.val)

/-- The grading attached to a cocycle `u` is `cocycleGrading 𝒜 u`. -/
@[simp]
theorem coe_gradingCocycleEquiv_apply (u : {u : A[T;T⁻¹] // IsGradingCocycle 𝒜 u}) :
    (gradingCocycleEquiv 𝒜 u : ℤ → Submodule R A) = cocycleGrading 𝒜 u :=
  (rfl)

/-- The cocycle attached to a compatible grading `ℳ` is the Laurent polynomial of the homogeneous
components of `1`, for any decomposition of `ℳ`. -/
theorem coe_gradingCocycleEquiv_symm_apply
    (ℳ : {ℳ : ℤ → Submodule R A // DirectSum.IsInternal ℳ ∧ SetLike.GradedSMul 𝒜 ℳ})
    [Decomposition ℳ.val] :
    ((gradingCocycleEquiv 𝒜).symm ℳ : A[T;T⁻¹]) = decomposeLaurent ℳ.val 1 := by
  -- The decomposition chosen in `gradingCocycleEquiv` agrees with the given one.
  simp only [gradingCocycleEquiv, Equiv.coe_fn_symm_mk]
  congr
  exact Subsingleton.elim _ _

/-- Each monomial `T d` is a cocycle. -/
theorem isGradingCocycle_T (d : ℤ) : IsGradingCocycle 𝒜 (T d) where
  decomposeLaurent_coeff_mul e := by
    by_cases h : d = e
    · subst h
      simp
    · simp [h]
  eval₂_one := by simp

/-- The grading defined by the cocycle `T d` is the shift `A(-d)`, whose degree-`n` piece is
`𝒜 (n - d)`. -/
@[simp]
theorem cocycleGrading_T (d n : ℤ) : cocycleGrading 𝒜 (T d) n = 𝒜 (n - d) := by
  ext m
  rw [mem_cocycleGrading_iff, ← decomposeLaurent_eq_C_mul_T_iff 𝒜, mul_T_eq_mul_T_iff]

variable {𝒜}

/-- **Graded isomorphisms and cohomologous cocycles.** For a cocycle `u` and any `u'`, the
gradings defined by `u` and `u'` are isomorphic as graded `A`-modules if and only if `u` and `u'`
are cohomologous: `ρ(v) * u' = v u` for a unit `v` of `A`, the image of `1` under the isomorphism.
-/
theorem exists_linearEquiv_iff_exists_mul_eq {u u' : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u) :
    (∃ φ : A ≃ₗ[A] A, ∀ n x, φ x ∈ cocycleGrading 𝒜 u' n ↔ x ∈ cocycleGrading 𝒜 u n) ↔
      ∃ v : Aˣ, decomposeLaurent 𝒜 v * u' = C (v : A) * u := by
  classical
  let := hu.decomposition
  refine ⟨fun ⟨φ, hφ⟩ ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · -- The isomorphism is multiplication by the unit `φ 1`, which sends each homogeneous
    -- component of `1` for `u` to a homogeneous element of the same degree for `u'`.
    have hφx (x : A) : φ x = x * φ 1 := by rw [← smul_eq_mul, ← φ.map_smul, smul_eq_mul, mul_one]
    have hunit : IsUnit (φ 1) := φ.isUnit_apply_one
    refine ⟨hunit.unit, ?_⟩
    -- Write `1 = ∑ₙ mₙ` with `mₙ` homogeneous of degree `n` for `u`, so that `u = ∑ₙ mₙ Tⁿ`.
    set D := decompose (cocycleGrading 𝒜 u) (1 : A)
    have hcomp (n : ℤ) :
        decomposeLaurent 𝒜 ((D n : A) * φ 1) * u' = C ((D n : A) * φ 1) * T n := by
      rw [← mem_cocycleGrading_iff, ← hφx, hφ]
      exact (D n).property
    have hu1 : u = ∑ n ∈ D.support, C (D n : A) * T n := by
      calc u = decomposeLaurent (cocycleGrading 𝒜 u) (∑ n ∈ D.support, (D n : A)) := by
            rw [sum_support_decompose, decomposeLaurent_one_cocycleGrading]
        _ = ∑ n ∈ D.support, C (D n : A) * T n := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun n _ ↦ decomposeLaurent_of_mem _ (D n).property
    calc decomposeLaurent 𝒜 (hunit.unit : A) * u'
        = decomposeLaurent 𝒜 ((∑ n ∈ D.support, (D n : A)) * φ 1) * u' := by
          rw [sum_support_decompose, one_mul, IsUnit.unit_spec]
      _ = ∑ n ∈ D.support, C ((D n : A) * φ 1) * T n := by
          rw [Finset.sum_mul, map_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun n _ ↦ hcomp n
      _ = C (hunit.unit : A) * u := by
          conv_rhs => rw [hu1]
          rw [Finset.mul_sum, IsUnit.unit_spec]
          exact Finset.sum_congr rfl fun n _ ↦ by rw [map_mul]; ring
  · refine ⟨v.mulRightLinearEquiv A, fun n x ↦ ?_⟩
    have h : decomposeLaurent 𝒜 (x * v) * u' = C (v : A) * (decomposeLaurent 𝒜 x * u) := by
      calc decomposeLaurent 𝒜 (x * v) * u'
          = decomposeLaurent 𝒜 x * (decomposeLaurent 𝒜 v * u') := by
            rw [decomposeLaurent_mul 𝒜 𝒜, mul_assoc]
        _ = C (v : A) * (decomposeLaurent 𝒜 x * u) := by rw [hv, mul_left_comm]
    rw [Units.mulRightLinearEquiv_apply, mem_cocycleGrading_iff, mem_cocycleGrading_iff, h,
      map_mul, mul_comm (C x), mul_assoc, (v.isUnit.map C).mul_right_inj]

variable (𝒜)

/-- The monomial cocycles `T c` and `T c'` are cohomologous exactly when `c - c'` is the degree of
a homogeneous unit of `A`. -/
theorem exists_mul_T_eq_iff {c c' : ℤ} :
    (∃ v : Aˣ, decomposeLaurent 𝒜 v * T c' = C (v : A) * T c) ↔
      c - c' ∈ homogeneousUnitDegrees 𝒜 := by
  simp only [mem_homogeneousUnitDegrees_iff, ← decomposeLaurent_eq_C_mul_T_iff 𝒜,
    mul_T_eq_mul_T_iff]

end Semiring

section Ring

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] [PreconnectedSpace (PrimeSpectrum A)]

/-- On a connected spectrum, every cocycle `u` is cohomologous to a monomial cocycle `T c`: the
grading it defines has a homogeneous generator, a unit `v` of degree `c`. -/
theorem IsGradingCocycle.exists_mul_eq_T {u : A[T;T⁻¹]} (hu : IsGradingCocycle 𝒜 u) :
    ∃ (v : Aˣ) (c : ℤ), decomposeLaurent 𝒜 v * u = C (v : A) * T c := by
  let := hu.decomposition
  obtain ⟨c, v, hv, hmem⟩ := exists_isUnit_mem_of_connected 𝒜 (cocycleGrading 𝒜 u)
  exact ⟨hv.unit, c, by rw [hv.unit_spec]; exact (mem_cocycleGrading_iff 𝒜).mp hmem⟩

end Ring

end

end TauCeti.GradedAlgebra
