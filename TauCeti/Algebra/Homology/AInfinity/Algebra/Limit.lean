/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal

/-!
# Limits of stabilising sequences of `A∞` algebra structures

Let `𝒜₀, 𝒜₁, …` be `A∞` structures on `(A, G)` whose suspended Taylor maps *stabilise*: for every
`n`, the Taylor maps of `𝒜ₙ₊₁` and `𝒜ₙ` agree on `filtration R A n`. There is then a unique `A∞`
structure `TauCeti.AInfinityAlgebra.limit` on `(A, G)` whose Taylor map agrees with `(𝒜 n).taylor`
on `filtration R A n` for all `n`. Its bar coderivation agrees with `(𝒜 n).barDifferential` on
`filtration R A n`, and therefore squares to zero everywhere.

Whereas `TauCeti.AInfinityHom.limit` takes the limit of comparison morphisms toward a fixed target
algebra, `TauCeti.AInfinityAlgebra.limit` constructs the limit `A∞` structure itself when arity-wise
gauge transformations modify higher operations inductively, as in unit strictification.

## Main definitions

* `TauCeti.AInfinityAlgebra.limit`: limit of a stabilising sequence of `A∞` structures with a common
  grading.

## Main results

* `TauCeti.AInfinityAlgebra.taylor_limit_apply_of_mem_filtration` and
  `TauCeti.AInfinityAlgebra.barDifferential_limit_apply_of_mem_filtration`: agreement with `𝒜 n` on
  `filtration R A n`.
* `TauCeti.AInfinityAlgebra.m_limit_of_le`, `TauCeti.AInfinityAlgebra.m_limit`, and
  `TauCeti.AInfinityAlgebra.eq_limit`: arity-wise agreement and uniqueness of the limit.
* `TauCeti.AInfinityAlgebra.differential_limit` and `TauCeti.AInfinityAlgebra.isMinimal_limit_iff`:
  the limit inherits the differential and minimality of `𝒜 1`.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003), Ch. 3.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

namespace TauCeti

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

namespace AInfinityAlgebra

open ReducedTensorWords

section Stabilising

variable {G : InternalGrading R A ℤ} {𝒜 : ℕ → AInfinityAlgebra R A}
  (hG : ∀ n, (𝒜 n).grading = G)
  (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 (n + 1)).taylor z = (𝒜 n).taylor z)

include hG h𝒜

private theorem gradedCoderiv_filtrationLimit_taylor_apply_of_mem_filtration {n : ℕ}
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A n) :
    gradedCoderiv (G.shift 1) (filtrationLimit fun k ↦ (𝒜 k).taylor) 1 z =
      (𝒜 n).barDifferential z := by
  rw [(𝒜 n).barDifferential_def, hG n]
  exact gradedCoderiv_apply_eq_of_mem_filtration _ 1
    (fun _ hw ↦ filtrationLimit_apply_of_mem_filtration h𝒜 hw) hz

private theorem isHomogeneous_filtrationLimit_taylor :
    LinearMap.IsHomogeneous (filtrationLimit fun k ↦ (𝒜 k).taylor)
      (gradedPiece (G.shift 1)) (G.shift 1).piece 1 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  have h := (𝒜 n).taylor_isSuspension.isHomogeneous (𝒜 n).m_degree
  rw [hG n] at h
  rw [filtrationLimit_apply_of_mem_filtration h𝒜 hn]
  exact h.map_mem hz

private theorem gradedCoderiv_filtrationLimit_taylor_comp_self :
    gradedCoderiv (G.shift 1) (filtrationLimit fun k ↦ (𝒜 k).taylor) 1 ∘ₗ
      gradedCoderiv (G.shift 1) (filtrationLimit fun k ↦ (𝒜 k).taylor) 1 = 0 :=
  LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R A z
    rw [LinearMap.comp_apply, LinearMap.zero_apply,
      gradedCoderiv_filtrationLimit_taylor_apply_of_mem_filtration hG h𝒜 hn,
      gradedCoderiv_filtrationLimit_taylor_apply_of_mem_filtration hG h𝒜
        ((𝒜 n).barDifferential_mem_filtration hn),
      ← LinearMap.comp_apply, (𝒜 n).barDifferential_sq, LinearMap.zero_apply]

end Stabilising

/-- The **limit** of a stabilising sequence of `A∞` structures `𝒜 n` with common grading `G`, whose
Taylor map agrees with `(𝒜 n).taylor` on `filtration R A n` for every `n`. -/
noncomputable def limit {G : InternalGrading R A ℤ} (𝒜 : ℕ → AInfinityAlgebra R A)
    (hG : ∀ n, (𝒜 n).grading = G)
    (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 (n + 1)).taylor z = (𝒜 n).taylor z) :
    AInfinityAlgebra R A :=
  ofTaylor G (filtrationLimit fun k ↦ (𝒜 k).taylor) (isHomogeneous_filtrationLimit_taylor hG h𝒜)
    (gradedCoderiv_filtrationLimit_taylor_comp_self hG h𝒜)

section Limit

variable {G : InternalGrading R A ℤ} {𝒜 : ℕ → AInfinityAlgebra R A}
  (hG : ∀ n, (𝒜 n).grading = G)
  (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 (n + 1)).taylor z = (𝒜 n).taylor z)

include hG h𝒜

/-- The limit `A∞` structure has the common grading `G`. -/
@[simp]
theorem limit_grading : (limit 𝒜 hG h𝒜).grading = G := by rw [limit, ofTaylor_grading]

/-- On the words of length at most `n`, the Taylor map of the limit is that of `𝒜 n`. -/
theorem taylor_limit_apply_of_mem_filtration {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) : (limit 𝒜 hG h𝒜).taylor z = (𝒜 n).taylor z := by
  rw [limit, ofTaylor_taylor, filtrationLimit_apply_of_mem_filtration h𝒜 hz]

/-- On the words of length at most `n`, the bar differential of the limit is that of `𝒜 n`. -/
theorem barDifferential_limit_apply_of_mem_filtration {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) :
    (limit 𝒜 hG h𝒜).barDifferential z = (𝒜 n).barDifferential z := by
  rw [limit, barDifferential_ofTaylor,
    gradedCoderiv_filtrationLimit_taylor_apply_of_mem_filtration hG h𝒜 hz]

/-- The arity-`k` operation of the limit agrees with that of `𝒜 n` whenever `k ≤ n`. -/
theorem m_limit_of_le {k n : ℕ} (hkn : k ≤ n) : (limit 𝒜 hG h𝒜).m k = (𝒜 n).m k :=
  m_eq_of_taylor_eq_on_filtration ((limit_grading hG h𝒜).trans (hG n).symm) hkn
    fun _ hz ↦ taylor_limit_apply_of_mem_filtration hG h𝒜 hz

/-- The arity-`n` operation of the limit is that of `𝒜 n`. -/
@[simp]
theorem m_limit (n : ℕ) : (limit 𝒜 hG h𝒜).m n = (𝒜 n).m n := m_limit_of_le hG h𝒜 le_rfl

/-- The limit is the unique `A∞` structure with grading `G` whose Taylor map agrees with
`(𝒜 n).taylor` on `filtration R A n` for every `n`. -/
theorem eq_limit {ℋ : AInfinityAlgebra R A} (hℋG : ℋ.grading = G)
    (hℋ : ∀ n, ∀ z ∈ filtration R A n, ℋ.taylor z = (𝒜 n).taylor z) : ℋ = limit 𝒜 hG h𝒜 := by
  have htaylor : ℋ.taylor = (limit 𝒜 hG h𝒜).taylor := LinearMap.ext fun z ↦ by
    obtain ⟨n, hn⟩ := exists_mem_filtration R A z
    rw [hℋ n z hn, taylor_limit_apply_of_mem_filtration hG h𝒜 hn]
  refine ext (hℋG.trans (limit_grading hG h𝒜).symm) ?_
  rw [m_eq_desuspension, m_eq_desuspension, hℋG, limit_grading, htaylor]

/-- The differential of the limit is that of `𝒜 1`. -/
@[simp]
theorem differential_limit : (limit 𝒜 hG h𝒜).differential = (𝒜 1).differential :=
  LinearMap.ext fun _ ↦ by rw [differential_apply, differential_apply, m_limit]

/-- The limit is minimal if and only if `𝒜 1` is minimal. -/
theorem isMinimal_limit_iff : (limit 𝒜 hG h𝒜).IsMinimal ↔ (𝒜 1).IsMinimal := by
  rw [isMinimal_def, isMinimal_def, differential_limit hG h𝒜]

end Limit

end AInfinityAlgebra

end TauCeti
