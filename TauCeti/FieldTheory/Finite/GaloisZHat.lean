/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.FieldTheory.Finite.SepClosedSubfield
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import TauCeti.FieldTheory.Galois.FixedField

/-!
# The absolute Galois group of a finite field is `ℤ̂`

Let `k` be a finite field with `q` elements and `L` an algebraic extension of `k` that is separably
closed, for instance an algebraic closure. The arithmetic Frobenius `x ↦ x ^ q` of `L` generates
`Gal(L/k)` topologically: its fixed field is `k`, so the closure of the subgroup it generates is
the fixing subgroup of `k`. On the fixed field `k_n` of its `n`-th power, of degree `n` over `k`,
it restricts to the Frobenius of `k_n / k`, of order `n`, which detects every finite quotient of
`ℤ`. So the continuous homomorphism `ℤ̂ → Gal(L/k)` sending the generator to Frobenius is
bijective, and `Gal(L/k) ≃ₜ* ℤ̂` with Frobenius going to `zHat.gen`
(`TauCeti.FiniteField.galoisGroupEquivZHat`).

## Main results

* `TauCeti.FiniteField.isGalois_of_isSepClosed`: a separably closed algebraic extension of a perfect
  field is Galois.
* `TauCeti.FiniteField.fixedField_zpowers_frobeniusAlgEquivOfAlgebraic`: the fixed field of
  Frobenius is `k`.
* `TauCeti.FiniteField.topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic`: Frobenius
  generates `Gal(L/k)` topologically.
* `TauCeti.FiniteField.galoisGroupEquivZHat`: `Gal(L/k) ≃ₜ* ℤ̂`, with
  `galoisGroupEquivZHat_apply_frobenius` and `galoisGroupEquivZHat_symm_apply_gen`.
-/

public section

noncomputable section

open IntermediateField

namespace TauCeti.FiniteField

universe u v

/-- A separably closed algebraic extension of a perfect field is Galois. -/
instance (priority := 100) isGalois_of_isSepClosed (k L : Type*) [Field k] [PerfectField k]
    [Field L] [Algebra k L] [Algebra.IsAlgebraic k L] [IsSepClosed L] : IsGalois k L := by
  have : Algebra.IsSeparable k L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : IsSepClosure k L := ⟨inferInstance, inferInstance⟩
  infer_instance

variable (k : Type u) (L : Type v) [Field k] [Fintype k] [Field L] [Algebra k L]
  [Algebra.IsAlgebraic k L]

/-- The fixed field of the arithmetic Frobenius of `L` is `k`. -/
theorem fixedField_zpowers_frobeniusAlgEquivOfAlgebraic :
    fixedField (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)) = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  rw [mem_fixedField_zpowers_iff, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic] at hx
  rw [IntermediateField.mem_bot]
  exact (pow_natCard_eq_self_iff_mem_range_algebraMap x).1 (by rwa [Nat.card_eq_fintype_card])

/-- **Frobenius generates the absolute Galois group of a finite field topologically.** -/
theorem topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic [IsGalois k L] :
    (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)).topologicalClosure =
      ⊤ := by
  rw [← fixingSubgroup_fixedField_eq_topologicalClosure,
    fixedField_zpowers_frobeniusAlgEquivOfAlgebraic, fixingSubgroup_bot]

variable [IsSepClosed L]

/-- The fixed field `k_n` of the `n`-th power of Frobenius, of degree `n` over `k`. -/
abbrev frobeniusLevel (n : ℕ+) : IntermediateField k L :=
  fixedField (Subgroup.zpowers (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L ^ (n : ℕ)))

instance (n : ℕ+) : FiniteDimensional k (frobeniusLevel k L n) := Module.finite_of_finrank_pos
  (by rw [finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero]; exact n.pos)

instance (n : ℕ+) : Finite (frobeniusLevel k L n) := Module.finite_of_finite k

/-- Restricted to `k_n`, Frobenius has order `n`. -/
theorem orderOf_restrictNormalHom_frobeniusAlgEquivOfAlgebraic (n : ℕ+) :
    orderOf (AlgEquiv.restrictNormalHom (frobeniusLevel k L n)
      (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)) = n := by
  have : Fintype (frobeniusLevel k L n) := Fintype.ofFinite _
  have h : AlgEquiv.restrictNormalHom (frobeniusLevel k L n)
      (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) =
      _root_.FiniteField.frobeniusAlgEquivOfAlgebraic k (frobeniusLevel k L n) := by
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      _root_.FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    simp
  rw [h, _root_.FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
    finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero]


/-- The canonical generator generates every finite quotient of the defining copy of `ℤ`. -/
private theorem mem_zpowers_quotientGenerator
    (H : FiniteIndexNormalSubgroup (ULift.{v} (Multiplicative ℤ))) :
    ∀ x : ULift.{v} (Multiplicative ℤ) ⧸ H.toSubgroup,
      x ∈ Subgroup.zpowers (QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1))) := by
  have hf : zpowersHom _ (QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1)) :
      ULift.{v} (Multiplicative ℤ) ⧸ H.toSubgroup) =
      (QuotientGroup.mk' H.toSubgroup).comp MulEquiv.ulift.symm.toMonoidHom :=
    MonoidHom.ext_mint rfl
  rw [← Subgroup.eq_top_iff', ← Subgroup.range_zpowersHom, hf, MonoidHom.range_eq_top]
  exact (QuotientGroup.mk'_surjective _).comp MulEquiv.ulift.symm.surjective

/-- Every finite quotient of `ℤ` is detected by restricting Frobenius to some `k_n`. -/
private theorem exists_finiteQuotient_frobeniusAlgEquivOfAlgebraic :
    ∀ H : FiniteIndexNormalSubgroup (ULift.{v} (Multiplicative ℤ)),
      letI : TopologicalSpace (ULift.{v} (Multiplicative ℤ) ⧸ H.toSubgroup) := ⊥
      ∃ q : Gal(L/k) →ₜ* (ULift.{v} (Multiplicative ℤ) ⧸ H.toSubgroup),
        q (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) =
          QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1)) := by
  intro H
  let Q := ULift.{v} (Multiplicative ℤ) ⧸ H.toSubgroup
  let _ : TopologicalSpace Q := ⊥
  let _ : DiscreteTopology Q := ⟨rfl⟩
  let gQ : Q := QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1))
  let n : ℕ+ := ⟨Nat.card Q, Nat.card_pos⟩
  let E := frobeniusLevel k L n
  let r : Gal(L/k) →ₜ* Gal(E/k) :=
    ⟨AlgEquiv.restrictNormalHom E, InfiniteGalois.restrictNormalHom_continuous E⟩
  have hcardE : Nat.card Gal(E/k) = n := by
    rw [IsGalois.card_aut_eq_finrank]
    exact finrank_fixedField_zpowers_frobeniusAlgEquivOfAlgebraic_pow k L n.ne_zero
  have hgenE : ∀ x : Gal(E/k),
      x ∈ Subgroup.zpowers (r (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)) := by
    rw [← Subgroup.eq_top_iff', ← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, hcardE]
    exact orderOf_restrictNormalHom_frobeniusAlgEquivOfAlgebraic k L n
  let eE : Multiplicative (ZMod n) ≃* Gal(E/k) := zmodMulEquivOfGenerator hgenE hcardE
  let eQ : Multiplicative (ZMod n) ≃* Q :=
    zmodMulEquivOfGenerator (mem_zpowers_quotientGenerator H) rfl
  let e : Gal(E/k) ≃* Q := eE.symm.trans eQ
  let ec : Gal(E/k) →ₜ* Q := ⟨e.toMonoidHom, continuous_of_discreteTopology⟩
  refine ⟨ec.comp r, ?_⟩
  change eQ (eE.symm (r (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L))) = gQ
  rw [zmodMulEquivOfGenerator_symm_apply_generator hgenE hcardE]
  exact zmodMulEquivOfGenerator_apply_ofAdd_one (mem_zpowers_quotientGenerator H) rfl

/-- **The absolute Galois group of a finite field is the profinite integers.** For a finite field
`k` and a separably closed algebraic extension `L`, the continuous multiplicative equivalence
`Gal(L/k) ≃ₜ* ℤ̂` sends the arithmetic Frobenius `x ↦ x ^ q` to `zHat.gen`. -/
def galoisGroupEquivZHat : Gal(L/k) ≃ₜ* zHat.{v} := by
  let f : zHat.{v} →ₜ* Gal(L/k) :=
    zHat.lift (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L)
  have hf : Function.Bijective f :=
    ⟨zHat.lift_injective_of_finite_quotients _
      (exists_finiteQuotient_frobeniusAlgEquivOfAlgebraic k L),
    zHat.lift_surjective _ (topologicalClosure_zpowers_frobeniusAlgEquivOfAlgebraic k L)⟩
  have : T2Space Gal(L/k) := krullTopology_t2
  exact (ContinuousMulEquiv.mk (MulEquiv.ofBijective f.toMonoidHom hf) f.continuous
    (f.continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective f.toMonoidHom hf).toEquiv))).symm

/-- The inverse equivalence sends the canonical generator of `ℤ̂` to the arithmetic Frobenius. -/
@[simp]
theorem galoisGroupEquivZHat_symm_apply_gen :
    (galoisGroupEquivZHat k L).symm zHat.gen =
      _root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  rw [galoisGroupEquivZHat, ContinuousMulEquiv.symm_symm]
  exact zHat.lift_gen _

/-- The equivalence sends the arithmetic Frobenius to the canonical generator of `ℤ̂`. -/
@[simp]
theorem galoisGroupEquivZHat_apply_frobenius :
    galoisGroupEquivZHat k L (_root_.FiniteField.frobeniusAlgEquivOfAlgebraic k L) = zHat.gen := by
  apply (galoisGroupEquivZHat k L).symm.injective
  rw [ContinuousMulEquiv.symm_apply_apply, galoisGroupEquivZHat_symm_apply_gen]

end TauCeti.FiniteField
