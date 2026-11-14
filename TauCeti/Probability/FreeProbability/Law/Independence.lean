/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Distribution.Free
public import TauCeti.Probability.FreeProbability.Law.Basic
import Mathlib.Algebra.Star.BigOperators

/-!
# Realization-independence of scalar laws of freely independent selfadjoint families

Two freely independent families of selfadjoint elements in possibly different C⋆-probability spaces
whose individual scalar laws (`PositiveLinearMap.law`) match have identical individual moments and
therefore the same joint noncommutative distribution (`TauCeti.jointDistribution`). By compact
moment determinacy (`PositiveLinearMap.law_eq_law_iff_forall_apply_pow`), any noncommutative
polynomial whose evaluations on both families are selfadjoint—in particular any finite or binary
sum—has the same scalar law in both spaces.

## Main results

* `TauCeti.IsFreelyIndependentElements.jointDistribution_eq_of_forall_law_eq`: matching scalar laws
  of freely independent selfadjoint families determine the joint distribution.
* `TauCeti.IsFreelyIndependentElements.law_lift_eq_of_forall_law_eq`: matching scalar laws determine
  the scalar law of any selfadjoint polynomial evaluation `FreeAlgebra.lift ℂ a P`.
* `TauCeti.IsFreelyIndependentElements.law_sum_eq_of_forall_law_eq`,
  `TauCeti.IsFreelyIndependentElements.law_add_eq_of_law_eq`,
  `TauCeti.IsFreelyIndependent.law_sum_eq_of_forall_law_eq`: realization-independence of finite and
  binary sum laws for freely independent elements and subalgebras.

## References

* D. V. Voiculescu, K. J. Dykema, A. Nica, *Free Random Variables*, CRM Monograph Ser. 1,
  Amer. Math. Soc. (1992), §3.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 5 and 12.
-/

public section

noncomputable section

open Finset
open scoped ComplexOrder

namespace TauCeti

variable {A B ι : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace IsFreelyIndependentElements

/-- Freely independent families of selfadjoint elements in possibly different C⋆-probability spaces
with matching individual laws have the same joint noncommutative distribution. -/
theorem jointDistribution_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hasa : ∀ i, IsSelfAdjoint (a i)) (hbsa : ∀ i, IsSelfAdjoint (b i))
    (hlaw : ∀ i, φ.law (a i) = ψ.law (b i)) :
    jointDistribution φ.toLinearMap a = jointDistribution ψ.toLinearMap b :=
  ha.jointDistribution_eq_of_forall_pow hb hφ hψ fun i n =>
    (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ ψ (hasa i) (hbsa i)).mp (hlaw i) n

/-- Any noncommutative polynomial `P` whose evaluations on two freely independent selfadjoint
families with matching individual laws are selfadjoint has the same scalar law in both spaces. -/
theorem law_lift_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hasa : ∀ i, IsSelfAdjoint (a i)) (hbsa : ∀ i, IsSelfAdjoint (b i))
    (hlaw : ∀ i, φ.law (a i) = ψ.law (b i))
    (P : FreeAlgebra ℂ ι)
    (hPa : IsSelfAdjoint (FreeAlgebra.lift ℂ a P))
    (hPb : IsSelfAdjoint (FreeAlgebra.lift ℂ b P)) :
    φ.law (FreeAlgebra.lift ℂ a P) = ψ.law (FreeAlgebra.lift ℂ b P) := by
  have hjd := ha.jointDistribution_eq_of_forall_law_eq hb hφ hψ hasa hbsa hlaw
  refine (PositiveLinearMap.law_eq_law_iff_forall_apply_pow φ ψ hPa hPb).mpr fun n => ?_
  have hpow := LinearMap.congr_fun hjd (P ^ n)
  simpa only [jointDistribution_apply, map_pow, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, PositiveLinearMap.coe_toLinearMap] using hpow

/-- Finite sums of freely independent selfadjoint elements depend in law only on the individual laws
of the summands. Only the summands indexed by `s` need be selfadjoint or match in law. -/
theorem law_sum_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : ι → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (s : Finset ι)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hbsa : ∀ i ∈ s, IsSelfAdjoint (b i))
    (hlaw : ∀ i ∈ s, φ.law (a i) = ψ.law (b i)) :
    φ.law (∑ i ∈ s, a i) = ψ.law (∑ i ∈ s, b i) := by
  let a' : s → A := fun i => a i.1
  let b' : s → B := fun i => b i.1
  have ha' : IsFreelyIndependentElements φ.toLinearMap a' := ha.comp Subtype.val_injective
  have hb' : IsFreelyIndependentElements ψ.toLinearMap b' := hb.comp Subtype.val_injective
  let P : FreeAlgebra ℂ s := ∑ i : s, FreeAlgebra.ι ℂ i
  have hPa : FreeAlgebra.lift ℂ a' P = ∑ i ∈ s, a i := by
    simp [P, a', Finset.univ_eq_attach, Finset.sum_attach]
  have hPb : FreeAlgebra.lift ℂ b' P = ∑ i ∈ s, b i := by
    simp [P, b', Finset.univ_eq_attach, Finset.sum_attach]
  rw [← hPa, ← hPb]
  exact ha'.law_lift_eq_of_forall_law_eq hb' hφ hψ
    (fun i => hasa i.1 i.2) (fun i => hbsa i.1 i.2) (fun i => hlaw i.1 i.2) P
    (hPa.symm ▸ isSelfAdjoint_sum s hasa) (hPb.symm ▸ isSelfAdjoint_sum s hbsa)

/-- Binary sums of distinct freely independent selfadjoint elements depend in law only on the two
individual laws. -/
theorem law_add_eq_of_law_eq {κ : Type*} {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {a : ι → A} {b : κ → B}
    (ha : IsFreelyIndependentElements φ.toLinearMap a)
    (hb : IsFreelyIndependentElements ψ.toLinearMap b)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    {i₁ i₂ : ι} {k₁ k₂ : κ} (hi : i₁ ≠ i₂) (hk : k₁ ≠ k₂)
    (ha₁ : IsSelfAdjoint (a i₁)) (ha₂ : IsSelfAdjoint (a i₂))
    (hb₁ : IsSelfAdjoint (b k₁)) (hb₂ : IsSelfAdjoint (b k₂))
    (h₁ : φ.law (a i₁) = ψ.law (b k₁)) (h₂ : φ.law (a i₂) = ψ.law (b k₂)) :
    φ.law (a i₁ + a i₂) = ψ.law (b k₁ + b k₂) := by
  let ea : Bool → ι := fun t => cond t i₁ i₂
  let eb : Bool → κ := fun t => cond t k₁ k₂
  have hea : Function.Injective ea := by
    rintro (_ | _) (_ | _) h <;> simp [ea] at h <;> tauto
  have heb : Function.Injective eb := by
    rintro (_ | _) (_ | _) h <;> simp [eb] at h <;> tauto
  have hsum := (ha.comp hea).law_sum_eq_of_forall_law_eq (hb.comp heb) hφ hψ
    ({true, false} : Finset Bool)
    (by rintro (_ | _) _ <;> assumption)
    (by rintro (_ | _) _ <;> assumption)
    (by rintro (_ | _) _ <;> assumption)
  simpa [ea, eb] using hsum

end IsFreelyIndependentElements

namespace IsFreelyIndependent

/-- Finite sums of selfadjoint elements chosen from freely independent subalgebras depend in law
only on the individual laws of the summands. -/
theorem law_sum_eq_of_forall_law_eq {φ : A →ₚ[ℂ] ℂ} {ψ : B →ₚ[ℂ] ℂ}
    {SA : ι → Subalgebra ℂ A} {SB : ι → Subalgebra ℂ B}
    (hA : IsFreelyIndependent φ.toLinearMap SA)
    (hB : IsFreelyIndependent ψ.toLinearMap SB)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1) (s : Finset ι) {a : ι → A} {b : ι → B}
    (haS : ∀ i ∈ s, a i ∈ SA i) (hbS : ∀ i ∈ s, b i ∈ SB i)
    (hasa : ∀ i ∈ s, IsSelfAdjoint (a i)) (hbsa : ∀ i ∈ s, IsSelfAdjoint (b i))
    (hlaw : ∀ i ∈ s, φ.law (a i) = ψ.law (b i)) :
    φ.law (∑ i ∈ s, a i) = ψ.law (∑ i ∈ s, b i) := by
  have ha' : IsFreelyIndependentElements φ.toLinearMap (fun i : s => a i.1) :=
    (hA.comp Subtype.val_injective).isFreelyIndependentElements fun i => haS i.1 i.2
  have hb' : IsFreelyIndependentElements ψ.toLinearMap (fun i : s => b i.1) :=
    (hB.comp Subtype.val_injective).isFreelyIndependentElements fun i => hbS i.1 i.2
  simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
    ha'.law_sum_eq_of_forall_law_eq hb' hφ hψ univ
      (fun i _ => hasa i.1 i.2) (fun i _ => hbsa i.1 i.2) (fun i _ => hlaw i.1 i.2)

end IsFreelyIndependent

end TauCeti
