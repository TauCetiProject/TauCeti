/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Profinite
public import TauCeti.NumberTheory.LocalField.Unramified.Maximal
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic

import TauCeti.Topology.Algebra.Group.Profinite.ZHat.ZMod

/-!
# The Galois group of the maximal unramified extension

For a nonarchimedean local field `K` and a separably closed extension `Ω`, this file identifies
the Galois group of the maximal unramified extension with the profinite integers:

`Gal(Kᵘʳ/K) ≃ₜ* ℤ̂`.

The isomorphism sends arithmetic Frobenius to the canonical generator `zHat.gen`, and hence each
integral power of `zHat.gen` to the same power of Frobenius; in particular arithmetic Frobenius has
infinite order (`TauCeti.not_isOfFinOrder_maximalUnramifiedFrobenius`), and `Gal(Kᵘʳ/K)` is
commutative.

## Main definition

* `TauCeti.maximalUnramifiedGaloisGroupEquivZHat`: the continuous multiplicative equivalence
  `Gal(Kᵘʳ/K) ≃ₜ* ℤ̂`, carrying arithmetic Frobenius to `zHat.gen`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open CategoryTheory IntermediateField

namespace TauCeti

universe u v w

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] (Ω : Type v) [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

/-- The degree-`f` unramified extension, regarded as an intermediate field of the maximal
unramified extension. -/
private def maximalUnramifiedLevel (f : ℕ) :
    IntermediateField K (maximalUnramifiedExtension K Ω) :=
  (unramifiedExtension K Ω f).comap (maximalUnramifiedExtension K Ω).val

/-- The degree-`f` level inside the maximal unramified extension is canonically equivalent to
the degree-`f` unramified extension inside `Ω`. -/
private def maximalUnramifiedLevelEquiv (f : ℕ) :
    maximalUnramifiedLevel K Ω f ≃ₐ[K] unramifiedExtension K Ω f :=
  let hLM := unramifiedExtension_le_maximalUnramifiedExtension K Ω f
  { toFun := fun x ↦ ⟨(x : maximalUnramifiedExtension K Ω), x.2⟩
    invFun := fun x ↦ ⟨⟨x, hLM x.2⟩, x.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_mul' := fun _ _ ↦ rfl
    commutes' := fun _ ↦ rfl }

private instance (f : ℕ) : IsGalois K (maximalUnramifiedLevel K Ω f) :=
  IsGalois.of_algEquiv (maximalUnramifiedLevelEquiv K Ω f).symm

/-- Restriction of arithmetic Frobenius to the degree-`f` level has order `f`. -/
private theorem orderOf_restrict_maximalUnramifiedFrobenius (f : ℕ) (hf : f ≠ 0) :
    orderOf (AlgEquiv.restrictNormalHom (maximalUnramifiedLevel K Ω f)
      (maximalUnramifiedFrobenius K Ω)) = f := by
  let L := unramifiedExtension K Ω f
  let hLM := unramifiedExtension_le_maximalUnramifiedExtension K Ω f
  let E := maximalUnramifiedLevel K Ω f
  let e := maximalUnramifiedLevelEquiv K Ω f
  let _ := finiteIntermediateFieldValuativeRel K Ω L
  let _ := finiteIntermediateFieldTopology K Ω L
  have := finiteIntermediateField_isNonarchimedeanLocalField K Ω L
  have := finiteIntermediateField_valuativeExtension K Ω L
  have : IsUnramified K L := isUnramified_unramifiedExtension hf
  have heq : AlgEquiv.autCongr e
      (AlgEquiv.restrictNormalHom E (maximalUnramifiedFrobenius K Ω)) =
      frobeniusAlgEquiv (K := K) (L := L) := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    calc
      (((AlgEquiv.autCongr e
          (AlgEquiv.restrictNormalHom E (maximalUnramifiedFrobenius K Ω))) x : L) : Ω) =
          (maximalUnramifiedFrobenius K Ω ⟨(x : Ω), hLM x.2⟩ : Ω) := by
            have hr := AlgEquiv.restrictNormalHom_apply E
              (maximalUnramifiedFrobenius K Ω) (e.symm x)
            exact congrArg (fun y : maximalUnramifiedExtension K Ω ↦ (y : Ω)) hr
      _ = (frobeniusAlgEquiv (K := K) (L := L) x : Ω) :=
        coe_maximalUnramifiedFrobenius_apply_of_mem x.2
  rw [← (AlgEquiv.autCongr e).orderOf_eq, heq, orderOf_frobeniusAlgEquiv,
    IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension hf]

/-- The canonical generator generates every finite quotient of the defining copy of `ℤ`. -/
private theorem mem_zpowers_quotientGenerator
    (H : FiniteIndexNormalSubgroup (ULift.{w} (Multiplicative ℤ))) :
    ∀ x : ULift.{w} (Multiplicative ℤ) ⧸ H.toSubgroup,
      x ∈ Subgroup.zpowers
        (QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1))) := by
  have hf : zpowersHom _ (QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1)) :
      ULift.{w} (Multiplicative ℤ) ⧸ H.toSubgroup) =
      (QuotientGroup.mk' H.toSubgroup).comp MulEquiv.ulift.symm.toMonoidHom :=
    MonoidHom.ext_mint rfl
  rw [← Subgroup.eq_top_iff', ← Subgroup.range_zpowersHom, hf, MonoidHom.range_eq_top]
  exact (QuotientGroup.mk'_surjective _).comp MulEquiv.ulift.symm.surjective

/-- Every finite coordinate of `ℤ̂` is detected by restriction to a finite unramified level. -/
private theorem exists_finiteQuotient_maximalUnramifiedFrobenius :
    ∀ H : FiniteIndexNormalSubgroup (ULift.{max u v} (Multiplicative ℤ)),
      letI : TopologicalSpace
        (ULift.{max u v} (Multiplicative ℤ) ⧸ H.toSubgroup) := ⊥
      ∃ q : Gal(maximalUnramifiedExtension K Ω/K) →ₜ*
          (ULift.{max u v} (Multiplicative ℤ) ⧸ H.toSubgroup),
        q (maximalUnramifiedFrobenius K Ω) =
          QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1)) := by
  intro H
  let Q := ULift.{max u v} (Multiplicative ℤ) ⧸ H.toSubgroup
  let _ : TopologicalSpace Q := ⊥
  let _ : DiscreteTopology Q := ⟨rfl⟩
  let gQ : Q := QuotientGroup.mk (ULift.up (Multiplicative.ofAdd 1))
  let n := Nat.card Q
  have hn : n ≠ 0 := Nat.ne_zero_of_lt Nat.card_pos
  let E := maximalUnramifiedLevel K Ω n
  have := Module.Finite.equiv (maximalUnramifiedLevelEquiv K Ω n).toLinearEquiv.symm
  let r : Gal(maximalUnramifiedExtension K Ω/K) →ₜ* Gal(E/K) :=
    ⟨AlgEquiv.restrictNormalHom E, InfiniteGalois.restrictNormalHom_continuous E⟩
  have hcardE : Nat.card Gal(E/K) = n := by
    rw [IsGalois.card_aut_eq_finrank]
    exact (maximalUnramifiedLevelEquiv K Ω n).toLinearEquiv.finrank_eq.trans
      (finrank_unramifiedExtension hn)
  have hgenE :
      ∀ x : Gal(E/K), x ∈ Subgroup.zpowers (r (maximalUnramifiedFrobenius K Ω)) := by
    rw [← (Subgroup.zpowers (r (maximalUnramifiedFrobenius K Ω))).eq_top_iff']
    rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers]
    -- Expose the restriction map hidden behind the local abbreviation `r`.
    change orderOf (AlgEquiv.restrictNormalHom (maximalUnramifiedLevel K Ω n)
      (maximalUnramifiedFrobenius K Ω)) = Nat.card Gal(E/K)
    rw [orderOf_restrict_maximalUnramifiedFrobenius K Ω n hn, hcardE]
  have hgenQ : ∀ x : Q, x ∈ Subgroup.zpowers gQ :=
    mem_zpowers_quotientGenerator H
  let eE : Multiplicative (ZMod n) ≃* Gal(E/K) :=
    zmodMulEquivOfGenerator hgenE hcardE
  let eQ : Multiplicative (ZMod n) ≃* Q :=
    zmodMulEquivOfGenerator hgenQ rfl
  let e : Gal(E/K) ≃* Q := eE.symm.trans eQ
  let ec : Gal(E/K) →ₜ* Q := ⟨e.toMonoidHom, continuous_of_discreteTopology⟩
  refine ⟨ec.comp r, ?_⟩
  -- Unfold the named equivalences only for this generator computation.
  change e (r (maximalUnramifiedFrobenius K Ω)) = gQ
  change eQ (eE.symm (r (maximalUnramifiedFrobenius K Ω))) = gQ
  rw [zmodMulEquivOfGenerator_symm_apply_generator hgenE hcardE,
    zmodMulEquivOfGenerator_apply_ofAdd_one hgenQ rfl]

/-- The canonical lift from the profinite integers to the Galois group of the maximal unramified
extension is bijective. -/
private theorem maximalUnramifiedFrobeniusLift_bijective :
    Function.Bijective (zHat.lift (maximalUnramifiedFrobenius K Ω) :
      zHat.{max u v} →ₜ* Gal(maximalUnramifiedExtension K Ω/K)) :=
  ⟨zHat.lift_injective_of_finite_quotients _
      (exists_finiteQuotient_maximalUnramifiedFrobenius K Ω),
    zHat.lift_surjective _ topologicalClosure_zpowers_maximalUnramifiedFrobenius⟩

/-- **The Galois group of the maximal unramified extension is the profinite integers.** This
continuous multiplicative equivalence sends arithmetic Frobenius to `zHat.gen`. -/
noncomputable def maximalUnramifiedGaloisGroupEquivZHat :
    Gal(maximalUnramifiedExtension K Ω/K) ≃ₜ* zHat.{max u v} := by
  let f : zHat.{max u v} →ₜ* Gal(maximalUnramifiedExtension K Ω/K) :=
    zHat.lift (maximalUnramifiedFrobenius K Ω)
  have hf := maximalUnramifiedFrobeniusLift_bijective K Ω
  have : T2Space Gal(maximalUnramifiedExtension K Ω/K) := krullTopology_t2
  let e : zHat.{max u v} ≃ₜ* Gal(maximalUnramifiedExtension K Ω/K) :=
    ContinuousMulEquiv.mk (MulEquiv.ofBijective f.toMonoidHom hf) f.continuous
      (f.continuous.continuous_symm_of_equiv_compact_to_t2
        (f := (MulEquiv.ofBijective f.toMonoidHom hf).toEquiv))
  exact e.symm

/-- The inverse isomorphism sends the canonical generator of `ℤ̂` to arithmetic Frobenius. -/
@[simp]
theorem maximalUnramifiedGaloisGroupEquivZHat_symm_apply_gen :
    (maximalUnramifiedGaloisGroupEquivZHat K Ω).symm zHat.gen =
      maximalUnramifiedFrobenius K Ω := by
  rw [maximalUnramifiedGaloisGroupEquivZHat, ContinuousMulEquiv.symm_symm]
  exact zHat.lift_gen _

/-- The isomorphism sends arithmetic Frobenius to the canonical generator of `ℤ̂`. -/
@[simp]
theorem maximalUnramifiedGaloisGroupEquivZHat_apply_frobenius :
    maximalUnramifiedGaloisGroupEquivZHat K Ω (maximalUnramifiedFrobenius K Ω) = zHat.gen := by
  apply (maximalUnramifiedGaloisGroupEquivZHat K Ω).symm.injective
  rw [ContinuousMulEquiv.symm_apply_apply,
    maximalUnramifiedGaloisGroupEquivZHat_symm_apply_gen]

/-- Integral powers of the canonical generator correspond to the same powers of arithmetic
Frobenius. -/
theorem maximalUnramifiedGaloisGroupEquivZHat_symm_apply_ofInt (n : ℤ) :
    (maximalUnramifiedGaloisGroupEquivZHat K Ω).symm
        (zHat.ofInt (Multiplicative.ofAdd n)) =
      maximalUnramifiedFrobenius K Ω ^ n := by
  rw [zHat.ofInt_ofAdd, map_zpow, maximalUnramifiedGaloisGroupEquivZHat_symm_apply_gen]

open scoped IsMulCommutative in
/-- The Galois group of the maximal unramified extension is commutative, being isomorphic to
`ℤ̂`. -/
instance : IsMulCommutative Gal(maximalUnramifiedExtension K Ω/K) :=
  ⟨⟨fun a b ↦ (maximalUnramifiedGaloisGroupEquivZHat K Ω).injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩

/-- **Arithmetic Frobenius has infinite order** in `Gal(Kᵘʳ/K)`, since `ℤ` embeds into `ℤ̂`. -/
theorem not_isOfFinOrder_maximalUnramifiedFrobenius :
    ¬ IsOfFinOrder (maximalUnramifiedFrobenius K Ω) := by
  refine injective_zpow_iff_not_isOfFinOrder.1 fun m n h ↦ ?_
  simp only [← maximalUnramifiedGaloisGroupEquivZHat_symm_apply_ofInt] at h
  exact Multiplicative.ofAdd.injective (zHat.ofInt_injective
    ((maximalUnramifiedGaloisGroupEquivZHat K Ω).symm.injective h))

end TauCeti
