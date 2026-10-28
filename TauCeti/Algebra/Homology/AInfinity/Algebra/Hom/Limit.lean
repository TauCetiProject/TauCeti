/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.BarDifferential
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Iso

/-!
# Limits of stabilising sequences of `A∞` morphisms

Let `ℋ` and `ℬ` be `A∞` algebras, and let `𝒜₀, 𝒜₁, …` be `A∞` structures on the graded module of
`ℋ` such that `𝒜ₙ` agrees with `ℋ` on the words of length at most `n`.  A sequence of `A∞`
morphisms `fₙ : 𝒜ₙ ⟶ ℬ` *stabilises* when the Taylor components of `fₙ₊₁` and `fₙ` agree on the
words of length at most `n`.  Such a sequence has a limit `f : ℋ ⟶ ℬ`
(`TauCeti.AInfinityHom.limit`), the unique `A∞` morphism whose Taylor components agree with those
of `fₙ` on the words of length at most `n`, for every `n`.  It is a morphism because the component
equation on the words of length at most `n` only involves the operations of `ℋ` and the Taylor
components of `f` on such words, where they are those of `𝒜ₙ` and `fₙ`.

Limits of this kind assemble infinitely many successive gauge transformations, one for each arity,
into a single `A∞` isomorphism, as in Kadeishvili's obstruction theory for intrinsic formality.

## Main definitions

* `TauCeti.AInfinityHom.limit`: the limit of a stabilising sequence of `A∞` morphisms.

## Main results

* `TauCeti.AInfinityHom.taylor_limit_apply_of_mem_filtration` and
  `TauCeti.AInfinityHom.barMap_limit_apply_of_mem_filtration`: on the words of length at most `n`
  the limit agrees with `fₙ`.
* `TauCeti.AInfinityHom.eq_limit`: the limit is the only `A∞` morphism with this property.
* `TauCeti.AInfinityHom.linearPart_limit` and `TauCeti.AInfinityHom.isIso_limit_iff`: the limit
  has the linear part of `f₁`, and it is an isomorphism exactly when `f₁` is.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 3.6.
-/

public section

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

namespace AInfinityHom

open ReducedTensorWords

variable {ℋ : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B} {𝒜 : ℕ → AInfinityAlgebra R A}

/-- The Taylor components of the limit of a sequence of `A∞` morphisms `f n`: on the words of
length `k`, those of `f k`. -/
private noncomputable def limitTaylor (f : ∀ n, AInfinityHom (𝒜 n) ℬ) :
    ReducedTensorWords R A →ₗ[R] B :=
  DirectSum.toModule R _ _ fun k ↦ (f k.1).taylor ∘ₗ of R A k

section Stabilising

variable {f : ∀ n, AInfinityHom (𝒜 n) ℬ}
  (hf : ∀ n, ∀ z ∈ filtration R A n, (f (n + 1)).taylor z = (f n).taylor z)

include hf

/-- In a stabilising sequence, the Taylor components of `f n` agree with those of `f k` on the
words of length at most `k`, for `k ≤ n`. -/
private theorem taylor_apply_eq_of_le {k n : ℕ} (hkn : k ≤ n) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A k) : (f n).taylor z = (f k).taylor z := by
  induction n, hkn using Nat.le_induction with
  | base => rfl
  | succ n hkn ih => rw [hf n z (filtration_monotone R A hkn hz), ih]

/-- The Taylor components of the limit agree with those of `f n` on the words of length at most
`n`. -/
private theorem limitTaylor_apply_of_mem_filtration {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) : limitTaylor f z = (f n).taylor z := by
  have h : filtration R A n ≤ LinearMap.eqLocus (limitTaylor f) (f n).taylor := by
    rw [filtration_le_iff]
    rintro k hk _ ⟨x, rfl⟩
    rw [LinearMap.mem_eqLocus, limitTaylor, toModule_of, LinearMap.comp_apply,
      taylor_apply_eq_of_le hf hk (of_mem_filtration R A le_rfl x)]
  exact h hz

/-- The Taylor expansion of the limit Taylor components agrees with the bar map of `f n` on the
words of length at most `n`. -/
private theorem coalgHom_limitTaylor_apply_of_mem_filtration {n : ℕ}
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A n) :
    coalgHom R (limitTaylor f) z = (f n).barMap z :=
  (isCoalgHom_coalgHom _).apply_eq_of_mem_filtration (f n).isCoalgHom_barMap
    (fun w hw ↦ by
      rw [← LinearMap.comp_apply (letter R B), letter_comp_coalgHom,
        limitTaylor_apply_of_mem_filtration hf hw, taylor_def, LinearMap.comp_apply]) hz

variable (hG : ∀ n, (𝒜 n).grading = ℋ.grading)

include hG

/-- The limit Taylor components have degree zero for the suspended gradings. -/
private theorem isHomogeneous_limitTaylor :
    LinearMap.IsHomogeneous (limitTaylor f) (gradedPiece (ℋ.grading.shift 1))
      (ℬ.grading.shift 1).piece 0 := by
  rw [LinearMap.isHomogeneous_def]
  intro p z hz
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  have h := (f n).isHomogeneous_taylor
  rw [hG n] at h
  rw [limitTaylor_apply_of_mem_filtration hf hn]
  exact h.map_mem hz

variable (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 n).taylor z = ℋ.taylor z)

include h𝒜

/-- The limit Taylor components satisfy the component equation of an `A∞` morphism from `ℋ`: on
the words of length at most `n` it is the component equation of `f n`. -/
private theorem taylor_comp_coalgHom_limitTaylor :
    ℬ.taylor ∘ₗ coalgHom R (limitTaylor f) = limitTaylor f ∘ₗ ℋ.barDifferential := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  have h := LinearMap.congr_fun (f n).taylor_comp_barMap z
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    coalgHom_limitTaylor_apply_of_mem_filtration hf hn, h,
    AInfinityAlgebra.barDifferential_apply_eq_of_mem_filtration (hG n) (h𝒜 n) hn,
    limitTaylor_apply_of_mem_filtration hf (ℋ.barDifferential_mem_filtration hn)]

end Stabilising

/-- The **limit** of a stabilising sequence of `A∞` morphisms.  Let `𝒜 n` be `A∞` structures with
the grading of `ℋ` whose Taylor maps agree with that of `ℋ` on the words of length at most `n`,
and let `f n : 𝒜 n ⟶ ℬ` be `A∞` morphisms such that the Taylor components of `f (n + 1)` and
`f n` agree on the words of length at most `n`.  The limit is the `A∞` morphism `ℋ ⟶ ℬ` whose
Taylor components agree with those of `f n` on the words of length at most `n`, for every `n`. -/
noncomputable def limit (f : ∀ n, AInfinityHom (𝒜 n) ℬ) (hG : ∀ n, (𝒜 n).grading = ℋ.grading)
    (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 n).taylor z = ℋ.taylor z)
    (hf : ∀ n, ∀ z ∈ filtration R A n, (f (n + 1)).taylor z = (f n).taylor z) :
    AInfinityHom ℋ ℬ :=
  ofTaylor (limitTaylor f) (isHomogeneous_limitTaylor hf hG)
    (taylor_comp_coalgHom_limitTaylor hf hG h𝒜)

section Limit

variable {f : ∀ n, AInfinityHom (𝒜 n) ℬ}
  (hf : ∀ n, ∀ z ∈ filtration R A n, (f (n + 1)).taylor z = (f n).taylor z)
  (hG : ∀ n, (𝒜 n).grading = ℋ.grading)
  (h𝒜 : ∀ n, ∀ z ∈ filtration R A n, (𝒜 n).taylor z = ℋ.taylor z)

include hf hG h𝒜

/-- On the words of length at most `n`, the Taylor components of the limit are those of `f n`. -/
theorem taylor_limit_apply_of_mem_filtration {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) : (limit f hG h𝒜 hf).taylor z = (f n).taylor z := by
  rw [limit, taylor_ofTaylor, limitTaylor_apply_of_mem_filtration hf hz]

/-- On the words of length at most `n`, the bar map of the limit is that of `f n`. -/
theorem barMap_limit_apply_of_mem_filtration {n : ℕ} {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A n) : (limit f hG h𝒜 hf).barMap z = (f n).barMap z := by
  rw [limit, barMap_ofTaylor, coalgHom_limitTaylor_apply_of_mem_filtration hf hz]

/-- The limit is the only `A∞` morphism whose Taylor components agree with those of `f n` on the
words of length at most `n`, for every `n`. -/
theorem eq_limit {g : AInfinityHom ℋ ℬ}
    (hg : ∀ n, ∀ z ∈ filtration R A n, g.taylor z = (f n).taylor z) : g = limit f hG h𝒜 hf := by
  refine ext (LinearMap.ext fun z ↦ ?_)
  obtain ⟨n, hn⟩ := exists_mem_filtration R A z
  rw [hg n z hn, taylor_limit_apply_of_mem_filtration hf hG h𝒜 hn]

/-- The linear part of the limit is that of `f 1`. -/
@[simp]
theorem linearPart_limit : (limit f hG h𝒜 hf).linearPart = (f 1).linearPart :=
  LinearMap.ext fun a ↦ by
    rw [linearPart_apply, linearPart_apply,
      taylor_limit_apply_of_mem_filtration hf hG h𝒜 (ofLetter_mem_filtration R A a)]

/-- The limit is an `A∞` isomorphism exactly when `f 1` is. -/
theorem isIso_limit_iff : (limit f hG h𝒜 hf).IsIso ↔ (f 1).IsIso := by
  rw [isIso_iff_linearPart_bijective, isIso_iff_linearPart_bijective,
    linearPart_limit hf hG h𝒜]

end Limit

end AInfinityHom

end TauCeti
