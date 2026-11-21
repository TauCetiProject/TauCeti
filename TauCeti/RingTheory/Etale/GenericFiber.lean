/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Ideal.GoingUp
import TauCeti.FieldTheory.IntermediateField.Adjoin.Transcendental
import TauCeti.RingTheory.LocalRing.ResidueField.Ideal
import TauCeti.RingTheory.Unramified.Localization

/-!
# Generic fibres of reduced algebras over a domain

Let `P` be a ring, a domain with fraction field `FP` for the second statement, and let `B` be a
reduced `P`-algebra.

* If no nonzero element of `P` vanishes on an irreducible component of `Spec B`, then `B` is
  torsion-free over `P`: an element killed by a nonzero scalar vanishes on every component, so it
  is nilpotent.
* If `B` is essentially of finite type over `P`, and at every minimal prime `p` of `B` the residue
  field `κ(p)` is algebraic and formally unramified over `P`, then the generic fibre `FP ⊗[P] B`
  is étale over `FP`, that is, a finite product of finite separable extensions of `FP`.

For the second statement, the primes of `FP ⊗[P] B` are the primes of `B` meeting no nonzero
element of `P`. Algebraicity of the components makes every such prime minimal, since a prime
strictly above a minimal prime `p` contains a nonzero element of `B ⧸ p` algebraic over `P`, and
hence a nonzero element of `P`. At a minimal prime the local ring of the reduced ring `B` is the
residue field, so `FP ⊗[P] B` is unramified over `FP` at every prime.

These are the two hypotheses on `B` in
`TauCeti.Ring.finite_integralClosure_of_isTorsionFree_of_etale`. They are specialized to
`P = R[X]` for a domain `R` with fraction field `K`, where `B` is a `K`-algebra and the image `y`
of `X` in every residue field `κ(p)` at a minimal prime is a separating transcendental element:
`K(y)` is then a fraction field of `R[X]` over which `κ(p)` is separable. This is how
`TauCeti.finite_integralClosure_of_forall_finrank_kaehlerDifferential_eq_one` proves finite
normalization of models of smooth curves over a possibly non-excellent discrete valuation ring.

## Main results

* `TauCeti.isTorsionFree_of_forall_mem_minimalPrimes`: a reduced algebra whose components all
  receive `P` injectively is torsion-free over `P`.
* `TauCeti.etale_tensorProduct_of_forall_mem_minimalPrimes`: the generic fibre of a reduced
  algebra essentially of finite type, algebraic and unramified at its minimal primes, is étale.
* `TauCeti.isTorsionFree_polynomial_of_forall_transcendental` and
  `TauCeti.etale_tensorProduct_polynomial_of_forall_isSeparable`: the case of a coordinate that is
  transcendental, respectively separating, on every component of `B`.

## References

* The Stacks Project, Lemma 55.8.2, https://stacks.math.columbia.edu/tag/0C2T.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {P B : Type*} [CommRing P] [CommRing B] [Algebra P B]

/-- A reduced `P`-algebra `B` is torsion-free as soon as `P` maps injectively to `B ⧸ p` for every
minimal prime `p` of `B`: an element killed by a nonzero scalar vanishes on every irreducible
component of `Spec B`, so it is nilpotent. -/
theorem isTorsionFree_of_forall_mem_minimalPrimes [IsReduced B]
    (h : ∀ p ∈ minimalPrimes B, Function.Injective (algebraMap P (B ⧸ p))) :
    Module.IsTorsionFree P B := by
  cases subsingleton_or_nontrivial P with
  | inl _ =>
    have := Module.subsingleton P B
    exact ⟨fun _ _ _ _ _ ↦ Subsingleton.elim _ _⟩
  | inr _ => ?_
  refine .of_smul_eq_zero fun a b hab ↦ or_iff_not_imp_left.mpr fun ha ↦ ?_
  suffices hb : b ∈ sInf (minimalPrimes B) by
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hb
    exact (mem_nilradical.mp hb).eq_zero
  refine Submodule.mem_sInf.mpr fun p hp ↦ ?_
  have := hp.1.1
  have hmul : algebraMap P (B ⧸ p) a * Ideal.Quotient.mk p b = 0 := by
    rw [IsScalarTower.algebraMap_apply P B (B ⧸ p), Ideal.Quotient.algebraMap_eq, ← map_mul,
      ← Algebra.smul_def, hab, map_zero]
  refine Ideal.Quotient.eq_zero_iff_mem.mp ((mul_eq_zero.mp hmul).resolve_left fun h0 ↦ ha ?_)
  exact h p hp (by rw [h0, map_zero])

/-- A prime of `B` meeting no nonzero element of `P` is minimal, provided `κ(p)` is algebraic
over `P` for every minimal prime `p` of `B`. -/
private lemma mem_minimalPrimes_of_disjoint
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B → Algebra.IsAlgebraic P p.ResidueField)
    (q : Ideal B) [q.IsPrime] (hq : ∀ a : P, a ≠ 0 → algebraMap P B a ∉ q) :
    q ∈ minimalPrimes B := by
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q)
  have := hp.1.1
  suffices q ≤ p from (le_antisymm this hpq) ▸ hp
  intro d hd
  by_contra hdp
  -- The image of `d` in the domain `B ⧸ p` is nonzero and algebraic over `P`.
  have hd0 : Ideal.Quotient.mk p d ≠ 0 := by rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  have := h p hp
  have halg : IsAlgebraic P (Ideal.Quotient.mk p d) :=
    (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom P (B ⧸ p) p.ResidueField)
      p.injective_algebraMap_quotient_residueField).mp (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Ideal.under_ne_bot_of_algebraic_mem hd0 (Ideal.mem_map_of_mem _ hd) halg)
  refine hq a ha0 ((Ideal.mem_quotient_iff_mem hpq).mp ?_)
  rwa [Ideal.mem_comap, IsScalarTower.algebraMap_apply P B (B ⧸ p),
    Ideal.Quotient.algebraMap_eq] at ha

/-- **The generic fibre of an algebra that is unramified at its generic points is étale.** Let `P`
be a domain with fraction field `FP`, and let `B` be a reduced `P`-algebra essentially of finite
type. If at every minimal prime `p` of `B` the residue field `κ(p)` is algebraic and formally
unramified over `P`, then `FP ⊗[P] B` is an étale `FP`-algebra. -/
theorem etale_tensorProduct_of_forall_mem_minimalPrimes (FP : Type*) [Field FP] [Algebra P FP]
    [IsFractionRing P FP] [Algebra.EssFiniteType P B] [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Algebra.IsAlgebraic P p.ResidueField ∧ Algebra.FormallyUnramified P p.ResidueField) :
    Algebra.Etale FP (FP ⊗[P] B) := by
  have := (IsFractionRing.injective P FP).isDomain (algebraMap P FP)
  let : Algebra B (FP ⊗[P] B) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors P)) (FP ⊗[P] B) :=
    IsLocalization.tensorRight FP _
  have : Algebra.FormallyUnramified FP (FP ⊗[P] B) := by
    refine Algebra.formallyUnramified_iff_forall.mpr fun Q ↦
      (Algebra.isUnramifiedAt_localization_iff (S := B) (nonZeroDivisors P) Q.asIdeal).mpr ?_
    -- The prime `Q ∩ B` meets no nonzero element of `P`, which is a unit in `FP ⊗[P] B`.
    have hq : Q.asIdeal.under B ∈ minimalPrimes B := by
      refine mem_minimalPrimes_of_disjoint (fun p _ hp ↦ (h p hp).1) _ fun a ha haQ ↦ ?_
      refine Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ haQ ?_)
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply P FP]
      exact ((IsFractionRing.injective P FP).ne_iff' (map_zero _)).mpr ha |>.isUnit.map _
    have := (h _ hq).2
    exact .of_equiv (AlgEquiv.ofBijective (IsScalarTower.toAlgHom P _ _)
      (Ideal.bijective_algebraMap_residueField_of_mem_minimalPrimes _ hq)).symm
  have : Algebra.FormallyEtale FP (FP ⊗[P] B) := .of_formallyUnramified_of_field FP _
  have := Algebra.FormallyUnramified.finite_of_free FP (FP ⊗[P] B)
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

section Coordinate

open Polynomial IntermediateField

variable {R K B : Type*} [CommRing R] [Field K] [Algebra R K] [CommRing B] [Algebra R B]
  [Algebra K B] [IsScalarTower R K B] [Algebra R[X] B] [IsScalarTower R R[X] B]

/-- For a prime `p` of an `R[X]`-algebra `B`, a polynomial maps to `κ(p)` by evaluation at the
image of `X`. -/
private lemma algebraMap_residueField_eq_aeval (p : Ideal B) [p.IsPrime] (f : R[X]) :
    algebraMap R[X] p.ResidueField f = aeval (algebraMap R[X] p.ResidueField X) f := by
  have : IsScalarTower R R[X] p.ResidueField := .of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R B, IsScalarTower.algebraMap_eq R R[X] B,
      IsScalarTower.algebraMap_eq R[X] B p.ResidueField, RingHom.comp_assoc]
  rw [← IsScalarTower.coe_toAlgHom' R, aeval_algHom_apply, aeval_X_left_apply]

/-- **A coordinate transcendental on every component makes a reduced algebra torsion-free.** Let
`B` be a reduced `R[X]`-algebra. If the image of `X` in the residue field of every minimal prime of
`B` is transcendental over `R`, then `B` is torsion-free over `R[X]`. -/
theorem isTorsionFree_polynomial_of_forall_transcendental [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Transcendental R (algebraMap R[X] p.ResidueField X)) :
    Module.IsTorsionFree R[X] B := by
  refine isTorsionFree_of_forall_mem_minimalPrimes fun p hp ↦ ?_
  have := hp.1.1
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ transcendental_iff.mp (h p hp) f ?_
  rw [← algebraMap_residueField_eq_aeval, IsScalarTower.algebraMap_apply R[X] (B ⧸ p), hf,
    map_zero]

/-- **A separating coordinate makes the generic fibre étale.** Let `R` be a domain with fraction
field `K`, and let `B` be a reduced `R[X]`-algebra which is also a `K`-algebra essentially of finite
type. Suppose that at every minimal prime `p` of `B` the image `y` of `X` in `κ(p)` is
transcendental over `K` and `κ(p)` is separable over `K(y)`. Then the generic fibre of `B` over
`R[X]` is a finite étale algebra over the fraction field of `R[X]`. -/
theorem etale_tensorProduct_polynomial_of_forall_isSeparable [IsFractionRing R K]
    [Algebra.EssFiniteType K B] [IsReduced B]
    (h : ∀ (p : Ideal B) [p.IsPrime], p ∈ minimalPrimes B →
      Transcendental K (algebraMap R[X] p.ResidueField X) ∧
        Algebra.IsSeparable K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField) :
    Algebra.Etale (FractionRing R[X]) (FractionRing R[X] ⊗[R[X]] B) := by
  have := (IsFractionRing.injective R K).isDomain (algebraMap R K)
  have : Algebra.EssFiniteType R K := .of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType R B := .comp R K B
  have : Algebra.EssFiniteType R[X] B := .of_comp R R[X] B
  refine etale_tensorProduct_of_forall_mem_minimalPrimes _ fun p _ hp ↦ ?_
  obtain ⟨hy, -⟩ := h p hp
  -- Factor `R[X] → κ(p)` through `K(y)`, a fraction field of `R[X]` over which `κ(p)` is
  -- separable.
  let := (aeval (R := R) (AdjoinSimple.gen K (algebraMap R[X] p.ResidueField X))).toAlgebra
  have : IsScalarTower R[X] K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField :=
    .of_algebraMap_eq fun f ↦ by
      rw [algebraMap_residueField_eq_aeval]
      exact (aeval_algHom_apply
        ((K⟮algebraMap R[X] p.ResidueField X⟯).val.restrictScalars R) (AdjoinSimple.gen K _) f)
  have := hy.isFractionRing_adjoin_simple (R := R)
  have := (h p hp).2
  have : Algebra.FormallyUnramified K⟮algebraMap R[X] p.ResidueField X⟯ p.ResidueField :=
    .of_isSeparable _ _
  have : Algebra.FormallyUnramified R[X] K⟮algebraMap R[X] p.ResidueField X⟯ :=
    .of_isLocalization (nonZeroDivisors R[X])
  have := IsLocalization.isAlgebraic K⟮algebraMap R[X] p.ResidueField X⟯ (nonZeroDivisors R[X])
  exact ⟨.trans R[X] K⟮algebraMap R[X] p.ResidueField X⟯ _,
    .comp R[X] K⟮algebraMap R[X] p.ResidueField X⟯ _⟩

end Coordinate

end TauCeti
