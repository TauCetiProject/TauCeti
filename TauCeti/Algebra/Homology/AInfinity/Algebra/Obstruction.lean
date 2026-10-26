/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Gauge

/-!
# Obstructions to removing the higher operations of a minimal `A∞` algebra

Let `m_𝒜` and `m_ℋ` be the suspended Taylor maps of two `A∞` structures `𝒜` and `ℋ` on the same
graded module.  Their difference `D = m_𝒜 - m_ℋ` satisfies the Maurer--Cartan equation

`[m_ℋ, D] + D{D} = 0`

of the Hochschild complex of `ℋ`, because both structures satisfy the brace equation
(`TauCeti.AInfinityAlgebra.hochschildDifferential_taylor_sub_taylor`).  No division is involved,
so this holds over every commutative ring.  Consequently, if `𝒜` and `ℋ` agree on the words of
length at most `e`, the Hochschild differential `[m_ℋ, D]` vanishes on the words of length at most
`2 e`.

This is the cocycle half of Kadeishvili's obstruction theory.  Let `ℋ` be a graded algebra,
presented as a minimal `A∞` algebra without operations above arity two, and let `𝒜` be a minimal
`A∞` structure with the same grading whose Taylor map agrees with that of `ℋ` on the words of
length at most `n`, for some `n ≥ 2`; equivalently `𝒜` has the binary operation of `ℋ` and
`m₃ = ⋯ = mₙ = 0`.  The **obstruction** `𝒜.obstruction ℋ ⟨n + 1, _⟩`, the component of `D` on the
words of length `n + 1`, is then a Hochschild cocycle of `ℋ` of degree one
(`TauCeti.AInfinityAlgebra.hochschildDifferential_obstruction`).  In unsuspended terms it is the
operation `mₙ₊₁` of `𝒜`, of internal degree `1 - n`; the classical obstruction class in
`HH^{n+1, 1-n}(H, H)` is its cohomology class.  This file works with the cocycle itself.

The other half is the killing step.  If the obstruction is a coboundary, `[m_ℋ, φ] = -D` on the
words of length at most `n + 1` for a degree-zero cochain `φ` vanishing on the words of length less
than `n`, then the gauge
transformation of `𝒜` by `φ` agrees with `ℋ` on the words of length at most `n + 1`
(`TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential`): the gauge
transformation adds `[m_𝒜, φ]` to the Taylor map, and `[m_𝒜, φ]` agrees with `[m_ℋ, φ]` there
(`TauCeti.AInfinityAlgebra.hochschildDifferential_eq_add_gerstenhaberBracket`).

## Main definitions

* `TauCeti.AInfinityAlgebra.obstruction`: the component on the words of a fixed length of the
  difference of the Taylor maps of two `A∞` structures.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_apply_eq_of_forall_m_eq`: two `A∞` structures with the same
  grading and the same operations of arity at most `n` have the same Taylor map on the words of
  length at most `n`.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_taylor_sub_taylor`: the Maurer--Cartan
  equation `[m_ℋ, D] = -D{D}` for the difference of two `A∞` structures.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_eq_add_gerstenhaberBracket`: the Hochschild
  differentials of two `A∞` structures differ by the bracket with `D`.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_comp_lengthProj_two`: a graded algebra has its
  Taylor map concentrated on the words of length two.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_comp_lengthProj`: the Hochschild differential
  of a graded algebra raises the arity of a cochain concentrated in one arity by one.
* `TauCeti.AInfinityAlgebra.hochschildDifferential_obstruction`: the first obstruction to the
  formality of a minimal `A∞` structure on a graded algebra is a Hochschild cocycle.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential`: a gauge
  transformation by a cochain bounding the obstruction removes it.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2,
  for braces and the Hochschild differential.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

universe uR uA

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 ℋ : AInfinityAlgebra R A}

/-! ### The difference of two `A∞` structures -/

/-- Two `A∞` structures with the same grading whose operations of positive arity at most `n` agree
have Taylor maps agreeing on the words of length at most `n`. -/
theorem taylor_apply_eq_of_forall_m_eq (hG : 𝒜.grading = ℋ.grading) {n : ℕ}
    (hm : ∀ k, 0 < k → k ≤ n → 𝒜.m k = ℋ.m k) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) :
    𝒜.taylor z = ℋ.taylor z := by
  have h : filtration R A n ≤ LinearMap.eqLocus 𝒜.taylor ℋ.taylor := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c x =>
        rw [map_smul, map_smul, map_smul, taylor_of_tprod, taylor_of_tprod, hG, hm k k.2 hk]
    | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  exact h hz

/-- **The difference of two `A∞` structures is a Maurer--Cartan element** of the Hochschild
complex: for `A∞` structures `𝒜` and `ℋ` on the same graded module, the difference
`D = m_𝒜 - m_ℋ` of their suspended Taylor maps satisfies `[m_ℋ, D] = -D{D}`. -/
theorem hochschildDifferential_taylor_sub_taylor (hG : 𝒜.grading = ℋ.grading) :
    ℋ.hochschildDifferential 1 (𝒜.taylor - ℋ.taylor) =
      -brace (ℋ.grading.shift 1) (𝒜.taylor - ℋ.taylor) (𝒜.taylor - ℋ.taylor) 1 := by
  obtain ⟨D, hD⟩ : ∃ D, 𝒜.taylor = ℋ.taylor + D := ⟨_, (add_sub_cancel ℋ.taylor 𝒜.taylor).symm⟩
  have h := 𝒜.brace_taylor_taylor
  rw [hG, hD, brace_add_left, brace_add_right, brace_add_right, ℋ.brace_taylor_taylor,
    zero_add] at h
  rw [hD, add_sub_cancel_left, hochschildDifferential_eq_brace_sub, negOnePowCast_one,
    neg_one_smul, sub_neg_eq_add]
  exact eq_neg_of_add_eq_zero_left ((add_assoc _ _ _).trans h)

/-- If two `A∞` structures agree on the words of length at most `e`, the Hochschild differential
of the difference of their Taylor maps vanishes on the words of length at most `2 e`. -/
theorem hochschildDifferential_taylor_sub_taylor_apply_eq_zero (hG : 𝒜.grading = ℋ.grading)
    {e : ℕ} (h : ∀ z ∈ filtration R A e, 𝒜.taylor z = ℋ.taylor z) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (2 * e)) :
    ℋ.hochschildDifferential 1 (𝒜.taylor - ℋ.taylor) z = 0 := by
  have hD : ∀ w ∈ filtration R A e, (𝒜.taylor - ℋ.taylor) w = 0 := fun w hw ↦ by
    rw [LinearMap.sub_apply, h w hw, sub_self]
  rw [hochschildDifferential_taylor_sub_taylor hG, LinearMap.neg_apply,
    brace_apply_eq_zero_of_mem_filtration _ _ hD hD (by rwa [← two_mul]), neg_zero]

/-- The Hochschild differentials of two `A∞` structures on the same graded module differ by the
Gerstenhaber bracket with the difference of their Taylor maps:
`[m_𝒜, F] = [m_ℋ, F] + [m_𝒜 - m_ℋ, F]`. -/
theorem hochschildDifferential_eq_add_gerstenhaberBracket (hG : 𝒜.grading = ℋ.grading) (q : ℤ)
    (F : ReducedTensorWords R A →ₗ[R] A) :
    𝒜.hochschildDifferential q F = ℋ.hochschildDifferential q F +
      gerstenhaberBracket (ℋ.grading.shift 1) 1 q (𝒜.taylor - ℋ.taylor) F := by
  rw [hochschildDifferential_def, hochschildDifferential_def, hG, ← gerstenhaberBracket_add_left,
    add_sub_cancel]

/-! ### The obstruction cochain -/

variable (𝒜 ℋ) in
/-- The **obstruction cochain** of `𝒜` relative to `ℋ` in arity `n`: the component on the words of
length `n` of the difference `m_𝒜 - m_ℋ` of the suspended Taylor maps. -/
noncomputable def obstruction (n : {n : ℕ // 0 < n}) : ReducedTensorWords R A →ₗ[R] A :=
  (𝒜.taylor - ℋ.taylor) ∘ₗ lengthProj R A n

variable (𝒜 ℋ) in
/-- Unfold the obstruction cochain as the difference of the Taylor maps after the projection onto
the words of length `n`. -/
theorem obstruction_def (n : {n : ℕ // 0 < n}) :
    𝒜.obstruction ℋ n = (𝒜.taylor - ℋ.taylor) ∘ₗ lengthProj R A n :=
  (rfl)

variable (𝒜 ℋ) in
/-- The obstruction cochain in arity `n` is concentrated on the words of length `n`. -/
@[simp]
theorem obstruction_comp_lengthProj (n : {n : ℕ // 0 < n}) :
    𝒜.obstruction ℋ n ∘ₗ lengthProj R A n = 𝒜.obstruction ℋ n :=
  LinearMap.ext fun z ↦ by
    simp only [obstruction_def, LinearMap.comp_apply, lengthProj_lengthProj]

/-- The obstruction cochain has degree one, like the Taylor maps whose difference it is. -/
theorem isHomogeneous_obstruction (hG : 𝒜.grading = ℋ.grading) (n : {n : ℕ // 0 < n}) :
    LinearMap.IsHomogeneous (𝒜.obstruction ℋ n) (gradedPiece (ℋ.grading.shift 1))
      (ℋ.grading.shift 1).piece 1 := by
  have h𝒜 := 𝒜.taylor_isSuspension.isHomogeneous 𝒜.m_degree
  rw [hG] at h𝒜
  simpa only [obstruction_def, zero_add] using
    (h𝒜.sub (ℋ.taylor_isSuspension.isHomogeneous ℋ.m_degree)).comp
      (isHomogeneous_lengthProj (ℋ.grading.shift 1) n)

/-- If `𝒜` and `ℋ` agree on the words of length at most `n`, the obstruction in arity `n + 1` is
the difference of their Taylor maps on the words of length at most `n + 1`. -/
theorem obstruction_apply_of_mem_filtration {n : ℕ}
    (h : ∀ z ∈ filtration R A n, 𝒜.taylor z = ℋ.taylor z) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (n + 1)) :
    𝒜.obstruction ℋ ⟨n + 1, n.succ_pos⟩ z = 𝒜.taylor z - ℋ.taylor z := by
  rw [obstruction_def, LinearMap.comp_apply,
    apply_lengthProj_of_mem_filtration R A (fun w hw ↦ by
      rw [LinearMap.sub_apply, h w hw, sub_self]) hz, LinearMap.sub_apply]

/-! ### The obstruction is a Hochschild cocycle -/

/-- The Taylor map of a minimal `A∞` algebra without operations above arity two, that is of a
graded algebra, is concentrated on the words of length two. -/
theorem IsMinimal.taylor_comp_lengthProj_two (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) :
    ℋ.taylor ∘ₗ lengthProj R A ⟨2, two_pos⟩ = ℋ.taylor := by
  refine linearMap_ext R A fun ⟨k, hk⟩ x ↦ ?_
  rw [LinearMap.comp_apply]
  by_cases h2 : k = 2
  · subst h2
    rw [lengthProj_of_self]
  rw [lengthProj_of_of_ne R A fun h ↦ h2 (Subtype.mk.inj h), map_zero]
  by_cases h1 : k = 1
  · subst h1
    exact (hℋ.taylor_apply_eq_zero_of_mem_filtration_one _
      (of_mem_filtration R A (k := ⟨1, hk⟩) le_rfl _)).symm
  · exact (LinearMap.congr_fun (ℋ.taylor_comp_of_eq_zero_of_m_eq_zero ⟨k, hk⟩
      (hm k (by omega))) (PiTensorProduct.tprod R x)).symm

/-- **The Hochschild differential of a graded algebra raises arity by one.**  If the Taylor map of
`ℋ` is concentrated on the words of length two, the Hochschild differential of `ℋ` sends a cochain
concentrated on the words of length `n + 1` to one concentrated on the words of length `n + 2`. -/
theorem hochschildDifferential_comp_lengthProj
    (ht : ℋ.taylor ∘ₗ lengthProj R A ⟨2, two_pos⟩ = ℋ.taylor) (q : ℤ) {n : ℕ}
    {F : ReducedTensorWords R A →ₗ[R] A} (hF : F ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩ = F) :
    ℋ.hochschildDifferential q F ∘ₗ lengthProj R A ⟨n + 2, by omega⟩ =
      ℋ.hochschildDifferential q F := by
  have h₁ := lengthProj_comp_gradedCoderiv (ℋ.grading.shift 1) q hF
    (j := ⟨2, two_pos⟩) (m := ⟨n + 2, by omega⟩) (by dsimp only; omega)
  have h₂ := lengthProj_comp_gradedCoderiv (ℋ.grading.shift 1) 1 ht
    (j := ⟨n + 1, n.succ_pos⟩) (m := ⟨n + 2, by omega⟩) rfl
  simp only [hochschildDifferential_eq_brace_sub, brace_def, LinearMap.sub_comp,
    LinearMap.smul_comp, LinearMap.comp_assoc, ← h₁, ← h₂]
  simp only [← LinearMap.comp_assoc, ht, hF]

/-- **The obstruction is a Hochschild cocycle.**  Let `ℋ` be a graded algebra, presented as a
minimal `A∞` algebra without operations above arity two, and let `𝒜` be an `A∞` structure with the
same grading whose Taylor map agrees with that of `ℋ` on the words of length at most `n`, for some
`n ≥ 2`.  Then the obstruction of `𝒜` in arity `n + 1`, the operation `mₙ₊₁` of `𝒜`, is a
Hochschild cocycle of `ℋ`. -/
theorem hochschildDifferential_obstruction (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0)
    (hG : 𝒜.grading = ℋ.grading) {n : ℕ} (hn : 2 ≤ n)
    (h : ∀ z ∈ filtration R A n, 𝒜.taylor z = ℋ.taylor z) :
    ℋ.hochschildDifferential 1 (𝒜.obstruction ℋ ⟨n + 1, n.succ_pos⟩) = 0 := by
  rw [← hochschildDifferential_comp_lengthProj (hℋ.taylor_comp_lengthProj_two hm) 1
    (obstruction_comp_lengthProj 𝒜 ℋ _)]
  refine LinearMap.ext fun z ↦ ?_
  have hz : lengthProj R A ⟨n + 2, by omega⟩ z ∈ filtration R A (n + 2) :=
    lengthProj_mem_filtration R A ⟨n + 2, by omega⟩ z
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  -- On the words of length at most `n + 1` the obstruction is the difference `D` of the Taylor
  -- maps, so on those of length at most `n + 2` its Hochschild differential is that of `D`.
  have hdiff : ∀ w ∈ filtration R A (n + 1),
      (𝒜.obstruction ℋ ⟨n + 1, n.succ_pos⟩ - (𝒜.taylor - ℋ.taylor)) w = 0 := fun w hw ↦ by
    rw [LinearMap.sub_apply, obstruction_apply_of_mem_filtration h hw, LinearMap.sub_apply,
      sub_self]
  rw [← sub_add_cancel (𝒜.obstruction ℋ ⟨n + 1, n.succ_pos⟩) (𝒜.taylor - ℋ.taylor),
    hochschildDifferential_add, LinearMap.add_apply,
    hℋ.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one 1 hdiff hz, zero_add]
  exact hochschildDifferential_taylor_sub_taylor_apply_eq_zero hG h
    (filtration_monotone R A (by omega) hz)

/-! ### Removing the obstruction by a gauge transformation -/

/-- **A gauge transformation removes a bounded obstruction.**  Let `𝒜` be a minimal `A∞`
structure whose Taylor map agrees with that of `ℋ`, which has the same grading, on the words of
length at most `e + 1`, for some `e ≥ 1`.  Let `φ` be a degree-zero cochain vanishing on the words
of length at most `e` whose Hochschild differential for `ℋ` is `m_ℋ - m_𝒜` on the words of length
at most `e + 2`.  Then the gauge transformation of `𝒜` by `φ` agrees with `ℋ` on the words of
length at most `e + 2`. -/
theorem IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential (h𝒜 : 𝒜.IsMinimal)
    (hG : 𝒜.grading = ℋ.grading) {φ : ReducedTensorWords R A →ₗ[R] A}
    (hφ : LinearMap.IsHomogeneous φ (gradedPiece (𝒜.grading.shift 1)) (𝒜.grading.shift 1).piece 0)
    (hφ₁ : φ ∘ₗ ofLetter R A = 0) {e : ℕ} (he : 1 ≤ e)
    (h : ∀ z ∈ filtration R A (e + 1), 𝒜.taylor z = ℋ.taylor z)
    (hφe : ∀ z ∈ filtration R A e, φ z = 0)
    (hδ : ∀ z ∈ filtration R A (e + 2), ℋ.hochschildDifferential 0 φ z = ℋ.taylor z - 𝒜.taylor z)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A (e + 2)) :
    (𝒜.gauge φ hφ hφ₁).taylor z = ℋ.taylor z := by
  have hD : ∀ w ∈ filtration R A (e + 1), (𝒜.taylor - ℋ.taylor) w = 0 := fun w hw ↦ by
    rw [LinearMap.sub_apply, h w hw, sub_self]
  -- The bracket `[m_𝒜 - m_ℋ, φ]` vanishes on the words of length at most `2 e + 1`.
  have hbracket : gerstenhaberBracket (ℋ.grading.shift 1) 1 0 (𝒜.taylor - ℋ.taylor) φ z = 0 := by
    rw [gerstenhaberBracket_def, LinearMap.sub_apply, LinearMap.smul_apply,
      brace_apply_eq_zero_of_mem_filtration _ _ hD hφe (filtration_monotone R A (by omega) hz),
      brace_apply_eq_zero_of_mem_filtration _ _ hφe hD (filtration_monotone R A (by omega) hz),
      smul_zero, sub_zero]
  rw [h𝒜.taylor_gauge_apply_of_mem_filtration hφ hφ₁ hφe (filtration_monotone R A (by omega) hz),
    hochschildDifferential_eq_add_gerstenhaberBracket hG, LinearMap.add_apply, hbracket, add_zero,
    hδ z hz, add_sub_cancel]

end AInfinityAlgebra

end TauCeti
