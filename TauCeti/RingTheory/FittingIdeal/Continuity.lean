/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import TauCeti.RingTheory.FittingIdeal.BaseChange
public import TauCeti.RingTheory.Ideal.KrullIntersection

import TauCeti.LinearAlgebra.TensorProduct.Quotient

/-!
# Closed-ideal detection and Fitting continuity

In a Noetherian commutative ring `R`, every ideal is closed in the `J`-adic topology for any ideal
`J` contained in `Ring.jacobson R` (`Ideal.iInf_sup_pow_eq_of_le_jacobson`). Consequently, if
`{Kᵢ}` is any family of ideals cofinal in the powers of `J` (every `J ^ N` contains some `Kᵢ`),
then two ideals of `R` are equal as soon as they have the same image in `R ⧸ Kᵢ` for every `i`
(`Ideal.eq_of_forall_map_quotientMk_eq`).

Combined with arbitrary base change of Fitting ideals (`TauCeti.fittingIdeal_baseChange`), this
gives **closed-ideal Fitting continuity**: if a finite `R`-module `M` has the property that for
every `i` the `k`-th Fitting ideal of `(R ⧸ Kᵢ) ⊗[R] M` (equivalently `M ⧸ Kᵢ M`) agrees with
the image of a fixed ideal `L` of `R`, then `Fitt_k(M) = L`. No statement that Fitting ideals
commute with arbitrary inverse limits is needed or used; the argument only compares images of
closed ideals along finite-level quotients.

We also record the quotient reduction formula
`Fitt_k(M ⧸ I M) = Fitt_k(M) (R ⧸ I)` (`TauCeti.fittingIdeal_quotientSMulTop`) and componentwise
detection along a complete orthogonal family of idempotents
(`TauCeti.fittingIdeal_eq_of_completeOrthogonalIdempotents`) or a finite product of rings
(`TauCeti.fittingIdeal_eq_of_pi`).

## Main results

* `Ideal.eq_iff_forall_map_quotientMk_one_sub_eq`: componentwise ideal equality along a complete
  orthogonal family of idempotents.
* `TauCeti.fittingIdeal_quotientSMulTop`: `Fitt_k(M ⧸ I M) = Fitt_k(M) (R ⧸ I)`.
* `TauCeti.fittingIdeal_eq_of_forall_baseChange_quotient_eq`,
  `TauCeti.fittingIdeal_eq_of_forall_quotientSMulTop_eq`: Fitting continuity along cofinal
  quotient systems over a Noetherian ring.
* `TauCeti.fittingIdeal_eq_of_completeOrthogonalIdempotents`, `TauCeti.fittingIdeal_eq_of_pi`:
  componentwise detection of Fitting ideals over finite product decompositions.

## References

* H. Matsumura, *Commutative Ring Theory*, Theorem 8.10 (Krull's intersection theorem).
* M. Kurihara, *Iwasawa theory and Fitting ideals*, J. Reine Angew. Math. 561 (2003), Lemma 4.2(2).
-/

public section

noncomputable section

open TensorProduct

namespace Ideal

variable {R : Type*} [CommRing R]

/-- Ideals of a ring with a complete orthogonal family of idempotents `e` are equal if and only if
they have equal images in every quotient `R ⧸ (1 - e i)`. -/
theorem eq_iff_forall_map_quotientMk_one_sub_eq {ι : Type*} [Fintype ι] {e : ι → R}
    (he : CompleteOrthogonalIdempotents e) {I L : Ideal R} :
    I = L ↔ ∀ i, I.map (Ideal.Quotient.mk (Ideal.span {1 - e i})) =
      L.map (Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
  refine ⟨fun h _ ↦ congrArg _ h, fun h ↦ ?_⟩
  let φ : R ≃+* ∀ i, R ⧸ Ideal.span {1 - e i} :=
    (AlgEquiv.ofBijective (AlgHom.pi fun _ ↦ Ideal.Quotient.mkₐ R _) he.bijective_pi).toRingEquiv
  refine φ.idealComapOrderIso.symm.injective (Ideal.piOrderIso.injective (funext fun i ↦ ?_))
  -- By definition, `Ideal.piOrderIso` sends an ideal `J` to `i ↦ J.map (Pi.evalRingHom _ i)`.
  have hpi (J : Ideal (∀ i, R ⧸ Ideal.span {1 - e i})) (i : ι) :
      Ideal.piOrderIso J i = J.map (Pi.evalRingHom _ i) := rfl
  have hφx (x : R) : φ x i = Ideal.Quotient.mk (Ideal.span {1 - e i}) x := rfl
  have hmap (J : Ideal R) :
      (J.map φ).map (Pi.evalRingHom _ i) = J.map (Ideal.Quotient.mk (Ideal.span {1 - e i})) := by
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.2 fun x hx ↦ ?_)
    · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro x hx
      simpa only [Ideal.mem_comap, Pi.evalRingHom_apply, hφx] using
        Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span {1 - e i})) hx
    · simpa only [Ideal.mem_comap, Pi.evalRingHom_apply, ← hφx] using
        Ideal.mem_map_of_mem (Pi.evalRingHom _ i) (Ideal.mem_map_of_mem φ hx)
  rw [hpi, hpi, RingEquiv.idealComapOrderIso_symm_apply, RingEquiv.idealComapOrderIso_symm_apply,
    hmap, hmap]
  exact h i

end Ideal

namespace TauCeti

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Quotient base change of Fitting ideals**: `Fitt_k(M ⧸ I M) = Fitt_k(M) (R ⧸ I)`. -/
@[simp]
theorem fittingIdeal_quotientSMulTop (I : Ideal R) (k : ℕ) :
    fittingIdeal (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M))) k =
      (fittingIdeal R M k).map (Ideal.Quotient.mk I) := by
  have h := fittingIdeal_congr (quotTensorEquivQuotSMulQuot (R := R) (M := M) I) k
  rw [← h, fittingIdeal_baseChange, Ideal.Quotient.algebraMap_eq]

/-- **Closed-ideal Fitting continuity (tensor-quotient form).** Over a Noetherian ring `R`, let
`J ≤ Ring.jacobson R` and let `{Kᵢ}` be a family of ideals cofinal in the powers of `J`. If
`Fitt_k((R ⧸ Kᵢ) ⊗[R] M) = L (R ⧸ Kᵢ)` for every `i`, then `Fitt_k(M) = L`. -/
theorem fittingIdeal_eq_of_forall_baseChange_quotient_eq [IsNoetherianRing R] {J : Ideal R}
    (hJ : J ≤ Ring.jacobson R) {ι : Type*} {K : ι → Ideal R}
    (hcof : ∀ N : ℕ, ∃ i : ι, K i ≤ J ^ N) {L : Ideal R} {k : ℕ}
    (h : ∀ i, fittingIdeal (R ⧸ K i) ((R ⧸ K i) ⊗[R] M) k =
      L.map (Ideal.Quotient.mk (K i))) :
    fittingIdeal R M k = L := by
  refine Ideal.eq_of_forall_map_quotientMk_eq hJ hcof fun i ↦ ?_
  simpa only [fittingIdeal_baseChange, Ideal.Quotient.algebraMap_eq] using h i

/-- **Closed-ideal Fitting continuity (module-quotient form).** Over a Noetherian ring `R`, let
`J ≤ Ring.jacobson R` and let `{Kᵢ}` be a family of ideals cofinal in the powers of `J`. If
`Fitt_k(M ⧸ Kᵢ M) = L (R ⧸ Kᵢ)` for every `i`, then `Fitt_k(M) = L`. -/
theorem fittingIdeal_eq_of_forall_quotientSMulTop_eq [IsNoetherianRing R] {J : Ideal R}
    (hJ : J ≤ Ring.jacobson R) {ι : Type*} {K : ι → Ideal R}
    (hcof : ∀ N : ℕ, ∃ i : ι, K i ≤ J ^ N) {L : Ideal R} {k : ℕ}
    (h : ∀ i, fittingIdeal (R ⧸ K i) (M ⧸ (K i • (⊤ : Submodule R M))) k =
      L.map (Ideal.Quotient.mk (K i))) :
    fittingIdeal R M k = L := by
  refine Ideal.eq_of_forall_map_quotientMk_eq hJ hcof fun i ↦ ?_
  simpa only [fittingIdeal_quotientSMulTop] using h i

/-- Specialization of closed-ideal Fitting continuity to a principal ideal `Ideal.span {d}`
(for instance a determinant ideal). -/
theorem fittingIdeal_eq_span_singleton_of_forall_quotientSMulTop_eq [IsNoetherianRing R]
    {J : Ideal R} (hJ : J ≤ Ring.jacobson R) {ι : Type*} {K : ι → Ideal R}
    (hcof : ∀ N : ℕ, ∃ i : ι, K i ≤ J ^ N) {d : R} {k : ℕ}
    (h : ∀ i, fittingIdeal (R ⧸ K i) (M ⧸ (K i • (⊤ : Submodule R M))) k =
      Ideal.span {Ideal.Quotient.mk (K i) d}) :
    fittingIdeal R M k = Ideal.span {d} := by
  refine fittingIdeal_eq_of_forall_quotientSMulTop_eq hJ hcof fun i ↦ ?_
  rw [h i, Ideal.map_span, Set.image_singleton]

/-- Componentwise detection of Fitting ideals along a complete orthogonal family of idempotents. -/
theorem fittingIdeal_eq_of_completeOrthogonalIdempotents {ι : Type*} [Fintype ι] {e : ι → R}
    (he : CompleteOrthogonalIdempotents e) {L : Ideal R} {k : ℕ}
    (h : ∀ i, fittingIdeal (R ⧸ Ideal.span {1 - e i})
        ((R ⧸ Ideal.span {1 - e i}) ⊗[R] M) k =
      L.map (Ideal.Quotient.mk (Ideal.span {1 - e i}))) :
    fittingIdeal R M k = L := by
  refine (Ideal.eq_iff_forall_map_quotientMk_one_sub_eq he).mpr fun i ↦ ?_
  simpa only [fittingIdeal_baseChange, Ideal.Quotient.algebraMap_eq] using h i

/-- Componentwise detection of Fitting ideals over a finite product of rings. -/
theorem fittingIdeal_eq_of_pi {ι : Type*} [Finite ι] {S : ι → Type*} [∀ i, CommRing (S i)]
    {N : Type*} [AddCommGroup N] [Module (∀ i, S i) N] [Module.Finite (∀ i, S i) N]
    {L : Ideal (∀ i, S i)} {k : ℕ}
    (h : ∀ i, letI : Algebra (∀ j, S j) (S i) := (Pi.evalRingHom S i).toAlgebra
      fittingIdeal (S i) (S i ⊗[∀ j, S j] N) k = L.map (Pi.evalRingHom S i)) :
    fittingIdeal (∀ i, S i) N k = L := by
  refine Ideal.piOrderIso.injective (funext fun i ↦ ?_)
  -- By definition, `Ideal.piOrderIso` sends an ideal `J` to `i ↦ J.map (Pi.evalRingHom S i)`.
  have hpi (J : Ideal (∀ i, S i)) (i : ι) : Ideal.piOrderIso J i = J.map (Pi.evalRingHom S i) := rfl
  let : Algebra (∀ j, S j) (S i) := (Pi.evalRingHom S i).toAlgebra
  simpa only [hpi, fittingIdeal_baseChange, RingHom.algebraMap_toAlgebra] using h i

end TauCeti
