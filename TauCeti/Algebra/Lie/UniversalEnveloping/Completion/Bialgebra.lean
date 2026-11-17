/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FilteredAlgebra.Bialgebra
public import TauCeti.Algebra.Lie.UniversalEnveloping.DegreeFiltration
public import TauCeti.Algebra.Lie.Graded.Completion

import TauCeti.LinearAlgebra.TensorProduct.Decomposition

/-!
# Completed bialgebra structure on graded universal enveloping algebras

For a Lie algebra `L` over a commutative ring `R` equipped with a nonnegative `Γ`-grading, the
decreasing total-degree filtration `TauCeti.UniversalEnvelopingAlgebra.degreeFiltration` on `U(L)`
is compatible with the standard cocommutative bialgebra structure:

* Comultiplication preserves every total-degree filtration ideal
  (`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_ideal_le_comap_comul`).
* The counit vanishes on the first degree ideal
  (`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_one_le_ker_counit`), with equality when the
  grading is supported in strictly positive degrees
  (`TauCeti.UniversalEnvelopingAlgebra.degreeFiltration_one_eq_ker_counit`).
* An enveloping element supported in degrees at most `k` whose coproduct is primitive modulo
  filtration order `k + 1` in `U(L) ⊗[R] U(L)` is already primitive in `U(L)`
  (`TauCeti.UniversalEnvelopingAlgebra.isPrimitiveElem_of_mem_tensorProduct_ideal_succ`).

For a positively graded Lie algebra `(d : PositiveDegrees N) (ℒ : N → Submodule R L)`, the finite
nilpotent truncations `d.truncatedLie ℒ k` map compatibly into the finite enveloping quotients,
assembling into a Lie homomorphism `TauCeti.PositiveDegrees.completedLieToU` into the completed
enveloping algebra whose image lies in the first completion ideal and consists of completed
primitive elements.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter II, §6.
* D. Quillen, *Rational homotopy theory*, Ann. of Math. (2) **90** (1969), Appendix A.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra Opposite

section NonnegGrading

variable {Γ R L : Type*} [AddCommMonoid Γ] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : Γ → Submodule R L) (d : Γ →+ ℤ)

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

private def homogeneousTensorSubmodule (p : Γ × Γ) : Submodule R (U ⊗[R] U) :=
  Submodule.map₂ (TensorProduct.mk R U U)
    (homogeneousSubmodule ℒ p.1) (homogeneousSubmodule ℒ p.2)

private theorem tmul_mem_homogeneousTensorSubmodule {i j : Γ} {a b : U}
    (ha : a ∈ homogeneousSubmodule ℒ i) (hb : b ∈ homogeneousSubmodule ℒ j) :
    a ⊗ₜ[R] b ∈ homogeneousTensorSubmodule ℒ (i, j) :=
  Submodule.apply_mem_map₂ (TensorProduct.mk R U U) ha hb

private theorem mul_mem_homogeneousTensorSubmodule {p q : Γ × Γ} {s t : U ⊗[R] U}
    (hs : s ∈ homogeneousTensorSubmodule ℒ p) (ht : t ∈ homogeneousTensorSubmodule ℒ q) :
    s * t ∈ homogeneousTensorSubmodule ℒ (p + q) := by
  have hpq : (p.1 + q.1, p.2 + q.2) = p + q := Prod.ext rfl rfl
  refine (Submodule.map₂_le.mpr fun a₁ ha₁ b₁ hb₁ => ?_ :
      homogeneousTensorSubmodule ℒ p ≤
        (homogeneousTensorSubmodule ℒ (p + q)).comap (LinearMap.mulRight R t)) hs
  refine (Submodule.map₂_le.mpr fun a₂ ha₂ b₂ hb₂ => ?_ :
      homogeneousTensorSubmodule ℒ q ≤
        (homogeneousTensorSubmodule ℒ (p + q)).comap (LinearMap.mulLeft R (a₁ ⊗ₜ[R] b₁))) ht
  simp only [Submodule.mem_comap, LinearMap.mulLeft_apply, TensorProduct.mk_apply,
    Algebra.TensorProduct.tmul_mul_tmul, ← hpq]
  exact tmul_mem_homogeneousTensorSubmodule ℒ
    (SetLike.mul_mem_graded ha₁ ha₂) (SetLike.mul_mem_graded hb₁ hb₂)

private def homogeneousComulSupport (n : Γ) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : Γ × Γ // p.1 + p.2 = n}, homogeneousTensorSubmodule ℒ p.1

private theorem le_homogeneousComulSupport {p : Γ × Γ} {n : Γ} (hp : p.1 + p.2 = n) :
    homogeneousTensorSubmodule ℒ p ≤ homogeneousComulSupport ℒ n :=
  le_iSup (fun q : {q : Γ × Γ // q.1 + q.2 = n} => homogeneousTensorSubmodule ℒ q.1) ⟨p, hp⟩

private theorem mul_mem_homogeneousComulSupport {m n : Γ} {s t : U ⊗[R] U}
    (hs : s ∈ homogeneousComulSupport ℒ m) (ht : t ∈ homogeneousComulSupport ℒ n) :
    s * t ∈ homogeneousComulSupport ℒ (m + n) := by
  refine Submodule.iSup_induction _ (motive := fun s => s * t ∈ _) hs (fun p s hs => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [add_mul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun t => s * t ∈ _) ht (fun q t ht => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [mul_add] using add_mem h₁ h₂)
  refine le_homogeneousComulSupport ℒ ?_ (mul_mem_homogeneousTensorSubmodule ℒ hs ht)
  -- Expose the componentwise addition on `Γ × Γ` before regrouping in `Γ`.
  change (p.1.1 + q.1.1) + (p.1.2 + q.1.2) = m + n
  rw [add_add_add_comm, p.2, q.2]

private theorem comul_prod_mem_homogeneousComulSupport (l : List (Σ i, ℒ i)) :
    Coalgebra.comul (R := R) (l.map (fun x => ι R (x.2 : L))).prod ∈
      homogeneousComulSupport ℒ (l.map Sigma.fst).sum := by
  have h1 := SetLike.one_mem_graded (homogeneousSubmodule ℒ)
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, Bialgebra.comul_one, List.sum_nil]
    exact le_homogeneousComulSupport ℒ (add_zero 0) (tmul_mem_homogeneousTensorSubmodule ℒ h1 h1)
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons, Bialgebra.comul_mul, comul_ι]
    refine mul_mem_homogeneousComulSupport ℒ (add_mem ?_ ?_) ih
    · exact le_homogeneousComulSupport ℒ (add_zero x.1)
        (tmul_mem_homogeneousTensorSubmodule ℒ (ι_mem_homogeneousSubmodule ℒ x.2.property) h1)
    · exact le_homogeneousComulSupport ℒ (zero_add x.1)
        (tmul_mem_homogeneousTensorSubmodule ℒ h1 (ι_mem_homogeneousSubmodule ℒ x.2.property))

private theorem comul_mem_homogeneousComulSupport {n : Γ} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) :
    Coalgebra.comul (R := R) a ∈ homogeneousComulSupport ℒ n :=
  ((homogeneousSubmodule_le_iff ℒ n _).mpr fun l hl =>
    hl ▸ comul_prod_mem_homogeneousComulSupport ℒ l :
      homogeneousSubmodule ℒ n ≤ (homogeneousComulSupport ℒ n).comap (Coalgebra.comul (R := R))) ha

private def lowTensorSupport (k : ℕ) : Submodule R (U ⊗[R] U) :=
  ⨆ p : {p : Γ × Γ // d p.1 + d p.2 ≤ k}, homogeneousTensorSubmodule ℒ p.1

private theorem le_lowTensorSupport {p : Γ × Γ} {k : ℕ} (hp : d p.1 + d p.2 ≤ k) :
    homogeneousTensorSubmodule ℒ p ≤ lowTensorSupport ℒ d k :=
  le_iSup (fun q : {q : Γ × Γ // d q.1 + d q.2 ≤ k} => homogeneousTensorSubmodule ℒ q.1) ⟨p, hp⟩

variable [DecidableEq Γ] [GradedLieAlgebra ℒ]

private theorem isInternal_homogeneousTensorSubmodule :
    _root_.DirectSum.IsInternal (homogeneousTensorSubmodule ℒ) :=
  _root_.DirectSum.IsInternal.tensorProduct (homogeneousSubmodule ℒ) (homogeneousSubmodule ℒ)
    (isInternal_homogeneousSubmodule ℒ) (isInternal_homogeneousSubmodule ℒ)

private theorem degreeFiltration_tensorFiltrationTail_le
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    TauCeti.tensorFiltrationTail
        (fun n => ((degreeFiltration ℒ d hneg).ideal n).restrictScalars R)
        (fun n => ((degreeFiltration ℒ d hneg).ideal n).restrictScalars R) k ≤
      TauCeti.DirectSum.degreeTail (homogeneousTensorSubmodule ℒ)
        (fun p => d p.1 + d p.2) k := by
  refine (TauCeti.tensorFiltrationTail_le_iff _ _).mpr fun i j hij a ha b hb => ?_
  rw [Submodule.restrictScalars_mem, degreeFiltration_ideal,
    TauCeti.GradedAlgebra.mem_degreeIdeal_iff, TauCeti.DirectSum.degreeTail_def] at ha hb
  refine Submodule.iSup_induction _ (motive := fun a => a ⊗ₜ[R] b ∈ _) ha (fun n₁ a ha => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [TensorProduct.add_tmul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun a => a ⊗ₜ[R] b ∈ _) ha (fun hn₁ a ha => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [TensorProduct.add_tmul] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun b => a ⊗ₜ[R] b ∈ _) hb (fun n₂ b hb => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [TensorProduct.tmul_add] using add_mem h₁ h₂)
  refine Submodule.iSup_induction _ (motive := fun b => a ⊗ₜ[R] b ∈ _) hb (fun hn₂ b hb => ?_)
    (by simp) (fun _ _ h₁ h₂ => by simpa [TensorProduct.tmul_add] using add_mem h₁ h₂)
  exact TauCeti.DirectSum.le_degreeTail (homogeneousTensorSubmodule ℒ)
    (fun p => d p.1 + d p.2) (i := (n₁, n₂)) (by dsimp only; omega)
    (tmul_mem_homogeneousTensorSubmodule ℒ ha hb)

private theorem degreeFiltration_tensorProduct_ideal_restrictScalars
    (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).restrictScalars R =
      TauCeti.DirectSum.degreeTail (homogeneousTensorSubmodule ℒ)
        (fun p => d p.1 + d p.2) k := by
  let F := degreeFiltration ℒ d hneg
  refine le_antisymm (fun t ht => degreeFiltration_tensorFiltrationTail_le ℒ d hneg k
    ((F.mem_tensorProduct_ideal_iff R F).mp ht)) ?_
  simp only [TauCeti.DirectSum.degreeTail_def, iSup_le_iff]
  rintro ⟨n₁, n₂⟩ hdeg
  dsimp only at hdeg
  by_cases hn₁ : d n₁ < 0
  · simp [homogeneousTensorSubmodule, homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn₁]
  · by_cases hn₂ : d n₂ < 0
    · simp [homogeneousTensorSubmodule, homogeneousSubmodule_eq_bot_of_degree_neg ℒ d hneg hn₂]
    · refine Submodule.map₂_le.mpr fun a ha b hb => ?_
      dsimp only at ha hb
      exact F.tmul_mem_tensorProduct_ideal R F (a := (d n₁).toNat) (b := (d n₂).toNat) (by omega)
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg ha (by omega))
        (mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d hneg hb (by omega))

/-- Comultiplication on the enveloping algebra of a nonnegatively graded Lie algebra preserves every
total-degree filtration ideal. -/
theorem degreeFiltration_ideal_le_comap_comul (hneg : ∀ n, d n < 0 → ℒ n = ⊥) (k : ℕ) :
    (degreeFiltration ℒ d hneg).ideal k ≤
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal k).comap (Bialgebra.comulAlgHom R U) := by
  rw [degreeFiltration_ideal_le_iff]
  intro n hn a ha
  rw [Ideal.mem_comap, Bialgebra.comulAlgHom_apply, ← Submodule.restrictScalars_mem R,
    degreeFiltration_tensorProduct_ideal_restrictScalars ℒ d hneg k]
  refine Submodule.iSup_induction _ (motive := fun t => t ∈ _)
    (comul_mem_homogeneousComulSupport ℒ ha) (fun p t ht => ?_) (by simp) (fun _ _ => add_mem)
  exact TauCeti.DirectSum.le_degreeTail (homogeneousTensorSubmodule ℒ)
    (fun q => d q.1 + d q.2) (by simpa only [← map_add, p.2] using hn) ht

/-- The first total-degree filtration ideal of a nonnegatively graded enveloping algebra lies in the
kernel of the counit. -/
theorem degreeFiltration_one_le_ker_counit (hneg : ∀ n, d n < 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d hneg).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) :=
  fun _ ha => RingHom.mem_ker.mpr <| (HopfIdeal.mem_augmentation R U).mp <|
    HopfIdeal.mem_toIdeal.mp (degreeFiltration_le_augmentation ℒ d hneg Nat.one_pos ha)

/-- For a strictly positively graded Lie algebra, the kernel of the counit lies in the first
total-degree filtration ideal. -/
theorem ker_counit_le_degreeFiltration_one (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    RingHom.ker (Bialgebra.counitAlgHom R U) ≤
      (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 :=
  fun _ ha => augmentation_le_degreeFiltration_one ℒ d hpos <| HopfIdeal.mem_toIdeal.mpr <|
    (HopfIdeal.mem_augmentation R U).mpr (by simpa using RingHom.mem_ker.mp ha)

/-- For a strictly positively graded Lie algebra, the first total-degree filtration ideal of `U(L)`
is equal to the kernel of the counit. -/
theorem degreeFiltration_one_eq_ker_counit (hpos : ∀ n, d n ≤ 0 → ℒ n = ⊥) :
    (degreeFiltration ℒ d (fun n hn => hpos n hn.le)).ideal 1 =
      RingHom.ker (Bialgebra.counitAlgHom R U) :=
  le_antisymm (degreeFiltration_one_le_ker_counit ℒ d _)
    (ker_counit_le_degreeFiltration_one ℒ d hpos)

private theorem comul_sub_mem_lowTensorSupport {k : ℕ} {b : U}
    (hdeg : ∀ n, (k : ℤ) < d n → (DirectSum.decompose (homogeneousSubmodule ℒ) b n : U) = 0) :
    Coalgebra.comul (R := R) b - (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) ∈ lowTensorSupport ℒ d k := by
  classical
  let H := homogeneousSubmodule ℒ
  have hlin : Coalgebra.comul (R := R) b - (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) =
      ∑ n ∈ (DirectSum.decompose H b).support,
        (Coalgebra.comul (R := R) (DirectSum.decompose H b n : U) -
          ((DirectSum.decompose H b n : U) ⊗ₜ[R] 1 +
            1 ⊗ₜ[R] (DirectSum.decompose H b n : U))) := by
    conv_lhs => rw [← DirectSum.sum_support_decompose H b]
    simp only [map_sum, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      ← Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hlin]
  refine Submodule.sum_mem _ fun n _ => ?_
  by_cases hn : (k : ℤ) < d n
  · simp [H, hdeg n hn]
  · have hnk : d n ≤ k := not_lt.mp hn
    have hmem := (DirectSum.decompose H b n).property
    have hc : Coalgebra.comul (R := R) (DirectSum.decompose H b n : U) ∈
        lowTensorSupport ℒ d k :=
      Submodule.iSup_induction _ (motive := fun t => t ∈ _)
        (comul_mem_homogeneousComulSupport ℒ hmem)
        (fun p _ ht => le_lowTensorSupport ℒ d (by simpa only [← map_add, p.2] using hnk) ht)
        (by simp) (fun _ _ => add_mem)
    exact sub_mem hc (add_mem
      (le_lowTensorSupport ℒ d (p := (n, 0)) (by simpa using hnk)
        (tmul_mem_homogeneousTensorSubmodule ℒ hmem (SetLike.one_mem_graded H)))
      (le_lowTensorSupport ℒ d (p := (0, n)) (by simpa using hnk)
        (tmul_mem_homogeneousTensorSubmodule ℒ (SetLike.one_mem_graded H) hmem)))

private theorem eq_zero_of_mem_degreeTail_of_mem_lowTensorSupport {k : ℕ} {w : U ⊗[R] U}
    (hw_tail : w ∈ TauCeti.DirectSum.degreeTail (homogeneousTensorSubmodule ℒ)
      (fun p => d p.1 + d p.2) (k + 1))
    (hw_low : w ∈ lowTensorSupport ℒ d k) : w = 0 := by
  classical
  let 𝒯 := homogeneousTensorSubmodule ℒ
  let _ : DirectSum.Decomposition 𝒯 :=
    (isInternal_homogeneousTensorSubmodule ℒ).chooseDecomposition
  let d₂ : Γ × Γ → ℤ := fun p => d p.1 + d p.2
  refine (DirectSum.decomposeLinearEquiv 𝒯).injective (_root_.DirectSum.ext fun p => Subtype.ext ?_)
  simp only [DirectSum.decomposeLinearEquiv_apply, DirectSum.decompose_zero,
    _root_.DirectSum.zero_apply, ZeroMemClass.coe_zero]
  by_cases hp : d₂ p ≤ k
  · exact (TauCeti.DirectSum.mem_degreeTail_iff 𝒯 d₂).mp hw_tail p (by omega)
  · exact Submodule.iSup_induction _
      (motive := fun t => (DirectSum.decompose 𝒯 t p : U ⊗[R] U) = 0) hw_low
      (fun q _ ht => DirectSum.decompose_of_mem_ne 𝒯 ht fun hqp =>
        hp (by simpa only [d₂, hqp] using q.2))
      (by simp) (fun _ _ h₁ h₂ => by simp [h₁, h₂])

/-- An enveloping element supported in degrees at most `k` whose coproduct is primitive modulo
filtration order `k + 1` in `U(L) ⊗[R] U(L)` is already primitive in `U(L)`. -/
theorem isPrimitiveElem_of_mem_tensorProduct_ideal_succ (hneg : ∀ n, d n < 0 → ℒ n = ⊥)
    {k : ℕ} {b : U}
    (hdeg : ∀ n, (k : ℤ) < d n → (DirectSum.decompose (homogeneousSubmodule ℒ) b n : U) = 0)
    (hcomul : Coalgebra.comul (R := R) b - (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) ∈
      (((degreeFiltration ℒ d hneg).tensorProduct R
        (degreeFiltration ℒ d hneg)).ideal (k + 1))) :
    Bialgebra.IsPrimitiveElem R b := by
  rw [← Submodule.restrictScalars_mem R,
    degreeFiltration_tensorProduct_ideal_restrictScalars ℒ d hneg (k + 1)] at hcomul
  have hw0 := eq_zero_of_mem_degreeTail_of_mem_lowTensorSupport ℒ d hcomul
    (comul_sub_mem_lowTensorSupport ℒ d hdeg)
  apply Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr
  rw [add_comm]
  exact sub_eq_zero.mp hw0

end NonnegGrading

end TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.PositiveDegrees

open _root_.UniversalEnvelopingAlgebra TauCeti.UniversalEnvelopingAlgebra Opposite

variable {N R L : Type*} [AddCommMonoid N] [CommRing R] [LieRing L] [LieAlgebra R L]
  (d : PositiveDegrees N) (ℒ : N → Submodule R L)
  [DecidableEq N] [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The decreasing total-degree filtration on `U(L)` induced by a positive grading of `L`. -/
noncomputable def envelopingFiltration : TauCeti.AlgFiltration U :=
  degreeFiltration ℒ d.degree (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le)

/-- `envelopingFiltration` is the total-degree filtration associated to `d.degree`. -/
theorem envelopingFiltration_def :
    d.envelopingFiltration ℒ =
      degreeFiltration ℒ d.degree (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le) := (rfl)

/-- A homogeneous enveloping element of degree at least `k` lies in `(d.envelopingFiltration ℒ)`
at order `k`. -/
theorem mem_envelopingFiltration_of_mem_homogeneousSubmodule {n : N} {a : U}
    (ha : a ∈ homogeneousSubmodule ℒ n) {k : ℕ} (hk : (k : ℤ) ≤ d.degree n) :
    a ∈ (d.envelopingFiltration ℒ).ideal k :=
  mem_degreeFiltration_ideal_of_mem_homogeneousSubmodule ℒ d.degree _ ha hk

/-- An enveloping element supported in degrees at most `k` that is primitive modulo
`((d.envelopingFiltration ℒ).tensorProduct R (d.envelopingFiltration ℒ)).ideal (k + 1)` is
primitive in `U(L)`. -/
theorem isPrimitiveElem_of_mem_envelopingFiltration_tensorProduct_succ {k : ℕ} {b : U}
    (hdeg : ∀ n, (k : ℤ) < d.degree n →
      (DirectSum.decompose (homogeneousSubmodule ℒ) b n : U) = 0)
    (hcomul : Coalgebra.comul (R := R) b - (b ⊗ₜ[R] 1 + 1 ⊗ₜ[R] b) ∈
      (((d.envelopingFiltration ℒ).tensorProduct R
        (d.envelopingFiltration ℒ)).ideal (k + 1))) :
    Bialgebra.IsPrimitiveElem R b :=
  isPrimitiveElem_of_mem_tensorProduct_ideal_succ ℒ d.degree _ hdeg hcomul

/-- Comultiplication preserves the positive-degree enveloping filtration at all orders. -/
theorem envelopingFiltration_ideal_le_comap_comul (k : ℕ) :
    (d.envelopingFiltration ℒ).ideal k ≤
      (((d.envelopingFiltration ℒ).tensorProduct R
        (d.envelopingFiltration ℒ)).ideal k).comap (Bialgebra.comulAlgHom R U) :=
  degreeFiltration_ideal_le_comap_comul ℒ d.degree _ k

/-- The first ideal of the positive-degree enveloping filtration lies in the kernel of the
counit. -/
theorem envelopingFiltration_one_le_ker_counit :
    (d.envelopingFiltration ℒ).ideal 1 ≤ RingHom.ker (Bialgebra.counitAlgHom R U) :=
  degreeFiltration_one_le_ker_counit ℒ d.degree _

/-- The kernel of the counit lies in the first ideal of the positive-degree enveloping
filtration. -/
theorem ker_counit_le_envelopingFiltration_one :
    RingHom.ker (Bialgebra.counitAlgHom R U) ≤ (d.envelopingFiltration ℒ).ideal 1 :=
  ker_counit_le_degreeFiltration_one ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)

/-- For a positively graded Lie algebra, the first enveloping filtration ideal is the kernel of the
counit. -/
theorem envelopingFiltration_one_eq_ker_counit :
    (d.envelopingFiltration ℒ).ideal 1 = RingHom.ker (Bialgebra.counitAlgHom R U) :=
  degreeFiltration_one_eq_ker_counit ℒ d.degree (d.eq_bot_of_degree_nonpos ℒ)

/-- Elements of the Lie degree ideal above cutoff `k` map into enveloping filtration order
`k + 1`. -/
theorem ι_mem_envelopingFiltration_of_mem_degreeIdeal {k : ℕ} {x : L}
    (hx : x ∈ d.degreeIdeal ℒ k) : ι R x ∈ (d.envelopingFiltration ℒ).ideal (k + 1) := by
  rw [← LieSubmodule.mem_toSubmodule, d.degreeIdeal_toSubmodule ℒ k, d.degreeSubmodule_def ℒ k]
    at hx
  exact Submodule.iSup_induction _
    (motive := fun x => ι R x ∈ (d.envelopingFiltration ℒ).ideal (k + 1)) hx
    (fun n _ hx => ι_mem_degreeFiltration ℒ d.degree _ hx (by have := n.property; omega))
    (by simp) (fun _ _ h₁ h₂ => by simpa only [map_add] using add_mem h₁ h₂)

/-- The canonical Lie homomorphism from the order-`k` Lie truncation into the order-`(k + 1)`
enveloping algebra quotient. -/
noncomputable def truncatedLieToU (k : ℕ) :
    d.truncatedLie ℒ k →ₗ⁅R⁆ U ⧸ (d.envelopingFiltration ℒ).ideal (k + 1) :=
  LieIdeal.liftQ (d.degreeIdeal ℒ k)
    ((Ideal.Quotient.mkₐ R ((d.envelopingFiltration ℒ).ideal (k + 1))).toLieHom.comp (ι R))
    fun _ hx => by
      simpa [Ideal.Quotient.eq_zero_iff_mem] using
        d.ι_mem_envelopingFiltration_of_mem_degreeIdeal ℒ hx

/-- `truncatedLieToU` sends the class of `x : L` to the quotient class of `ι R x`. -/
@[simp]
theorem truncatedLieToU_mk (k : ℕ) (x : L) :
    d.truncatedLieToU ℒ k (LieSubmodule.Quotient.mk x) =
      Ideal.Quotient.mk ((d.envelopingFiltration ℒ).ideal (k + 1)) (ι R x) := by
  simp [truncatedLieToU]

/-- The finite-order Lie-to-enveloping maps commute with `LieIdeal.factor`. -/
@[simp]
theorem factor_truncatedLieToU {k l : ℕ} (h : k ≤ l) (y : d.truncatedLie ℒ l) :
    Ideal.Quotient.factor
        ((d.envelopingFiltration ℒ).antitone (Nat.add_le_add_right h 1))
        (d.truncatedLieToU ℒ l y) =
      d.truncatedLieToU ℒ k (LieIdeal.factor (d.degreeIdeal_antitone ℒ h) y) := by
  obtain ⟨x, rfl⟩ := (d.degreeIdeal ℒ l).surjective_mkQ y
  simp [LieIdeal.mkQ_apply]

/-- When `ι : L → U(L)` is injective, every finite-order map `truncatedLieToU` is injective. -/
theorem truncatedLieToU_injective (hι : Function.Injective (ι R : L → U)) (k : ℕ) :
    Function.Injective (d.truncatedLieToU ℒ k) := by
  rw [truncatedLieToU, LieIdeal.liftQ_injective_iff]
  intro x hx
  have hx' : ι R x ∈ (d.envelopingFiltration ℒ).ideal (k + 1) := by
    simpa [Ideal.Quotient.eq_zero_iff_mem] using hx
  have htail : x ∈ TauCeti.DirectSum.degreeTail ℒ d.degree (k + 1) := by
    rw [← comap_degreeFiltration_ι ℒ d.degree
      (fun n hn => d.eq_bot_of_degree_nonpos ℒ n hn.le) hι (k + 1)]
    exact hx'
  exact (d.mem_degreeIdeal_iff ℒ).mpr fun n hn =>
    (TauCeti.DirectSum.mem_degreeTail_iff ℒ d.degree).mp htail n (by omega)

private noncomputable def completedLieToUFun (z : d.completedLie ℒ) :
    (d.envelopingFiltration ℒ).completion :=
  ⟨fun k : ℕᵒᵖ => d.truncatedLieToU ℒ k.unop
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k.unop z),
    ((d.envelopingFiltration ℒ).mem_completion_iff _).mpr fun {k l} h => by
      rw [d.factor_truncatedLieToU ℒ h]
      exact congrArg (d.truncatedLieToU ℒ k)
        (LieIdeal.factor_completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) h z)⟩

/-- The canonical Lie homomorphism from the completed positively graded Lie algebra into the
completed universal enveloping algebra. -/
noncomputable def completedLieToU :
    d.completedLie ℒ →ₗ⁅R⁆ (d.envelopingFiltration ℒ).completion where
  toFun := d.completedLieToUFun ℒ
  map_add' x y := (d.envelopingFiltration ℒ).completion_ext fun k => by
    simp [completedLieToUFun, AlgFiltration.projection_apply]
  map_smul' r x := (d.envelopingFiltration ℒ).completion_ext fun k => by
    have hsmul : (d.envelopingFiltration ℒ).projection k (r • d.completedLieToUFun ℒ x) =
        r • (d.envelopingFiltration ℒ).projection k (d.completedLieToUFun ℒ x) := by
      simpa only [AlgFiltration.projectionₐ_apply] using
        map_smul ((d.envelopingFiltration ℒ).projectionₐ (R := R) k) r (d.completedLieToUFun ℒ x)
    rw [RingHom.id_apply, hsmul]
    simp [completedLieToUFun, AlgFiltration.projection_apply]
  map_lie' {x y} := (d.envelopingFiltration ℒ).completion_ext fun k => by
    simp [LieRing.of_associative_ring_bracket, completedLieToUFun, AlgFiltration.projection_apply]

/-- The order-`k` projection of `completedLieToU` is `truncatedLieToU` on the order-`k` Lie
projection. -/
@[simp]
theorem projection_completedLieToU (k : ℕ) (z : d.completedLie ℒ) :
    (d.envelopingFiltration ℒ).projection k (d.completedLieToU ℒ z) =
      d.truncatedLieToU ℒ k
        (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k z) :=
  (d.envelopingFiltration ℒ).projection_apply k _

/-- `completedLieToU` extends the canonical Lie inclusion `ι : L → U(L)` along completions. -/
@[simp]
theorem completedLieToU_toCompletion (x : L) :
    d.completedLieToU ℒ (LieIdeal.toCompletion (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) x) =
      (d.envelopingFiltration ℒ).toCompletion (ι R x) :=
  (d.envelopingFiltration ℒ).completion_ext fun _ => by simp [LieIdeal.mkQ_apply]

/-- Every element in the image of `completedLieToU` lies in the first completion ideal. -/
theorem completedLieToU_mem_completionIdeal_one (z : d.completedLie ℒ) :
    d.completedLieToU ℒ z ∈ (d.envelopingFiltration ℒ).completionIdeal 1 := by
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, projection_completedLieToU,
    Subsingleton.elim
      (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) 0 z) 0, map_zero]

/-- Every element in the image of `completedLieToU` is completed primitive over any commutative
base ring `R`. -/
theorem isCompletedPrimitive_completedLieToU (z : d.completedLie ℒ) :
    (d.envelopingFiltration ℒ).IsCompletedPrimitive R
      (d.envelopingFiltration_ideal_le_comap_comul ℒ)
      (d.envelopingFiltration_one_le_ker_counit ℒ) (d.completedLieToU ℒ z) := by
  refine (d.envelopingFiltration ℒ).isCompletedPrimitive_of_forall_sub_mem R
    (d.envelopingFiltration_ideal_le_comap_comul ℒ)
    (d.envelopingFiltration_one_le_ker_counit ℒ) fun k => ?_
  obtain ⟨x, hx⟩ := (d.degreeIdeal ℒ k).surjective_mkQ
    (LieIdeal.completionProjection (d.degreeIdeal ℒ) (d.degreeIdeal_antitone ℒ) k z)
  refine ⟨(d.envelopingFiltration ℒ).toCompletion (ι R x),
    (d.envelopingFiltration ℒ).isCompletedPrimitive_toCompletion R _ _ (isPrimitiveElem_ι R L x),
    ?_⟩
  rw [AlgFiltration.completionIdeal_succ, RingHom.mem_ker, map_sub, sub_eq_zero,
    projection_completedLieToU, ← hx, LieIdeal.mkQ_apply, truncatedLieToU_mk,
    AlgFiltration.projection_toCompletion]

/-- When `ι : L → U(L)` is injective, `completedLieToU` is injective. -/
theorem completedLieToU_injective (hι : Function.Injective (ι R : L → U)) :
    Function.Injective (d.completedLieToU ℒ) := fun _ _ hxy =>
  LieIdeal.completion_ext _ _ fun k => d.truncatedLieToU_injective ℒ hι k <| by
    simpa only [projection_completedLieToU] using
      congrArg ((d.envelopingFiltration ℒ).projection k) hxy

end TauCeti.PositiveDegrees
