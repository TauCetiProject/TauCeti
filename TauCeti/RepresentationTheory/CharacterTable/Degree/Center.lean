/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Nat.Factorization.PowDvd
public import TauCeti.RepresentationTheory.CharacterTable.Degree.Basic
public import TauCeti.RepresentationTheory.Induction.Restriction
public import TauCeti.RepresentationTheory.Tensor.External

/-!
# The degree of an irreducible character divides the index of a central subgroup

For a finite group `H`, a subgroup `Z` of its centre and an irreducible representation `ρ` of `H`
over an algebraically closed field of characteristic zero, the degree `χ(1) = dim V` divides the
index `|H : Z|`. This sharpens `Representation.finrank_dvd_card`, the case `Z = 1`.

The proof is the tensor-power argument. By Schur's lemma each `z ∈ Z` acts on `V` as a scalar
`λ(z)`. For `m ≥ 1` the `m`-fold external tensor power of `ρ` is an irreducible representation of
`H^m` of dimension `χ(1)^m`, and it is trivial on the central subgroup
`{(z_1, …, z_m) ∈ Z^m : z_1 ⋯ z_m = 1}`, of order `|Z|^(m-1)`. Applying
`Representation.finrank_dvd_card` to the quotient gives `χ(1)^m ∣ |H : Z|^m |Z|` for every `m`,
and comparing the exponents of each prime for `m` large gives `χ(1) ∣ |H : Z|`.

The tensor powers are built one factor at a time: the induction runs over a general finite group
`G` with an irreducible representation `σ`, a central copy `ι(Z)` of `Z` acting through the same
scalars `λ`, and a central subgroup `A` acting trivially, and replaces `(G, σ, A)` by
`(H × G, ρ ⊠ σ, A')` with `A' = {(z, ι(z)⁻¹ a)}`.

## Main statements

* `Representation.finrank_dvd_index_of_le_center` and `FDRep.finrank_dvd_index_of_le_center`:
  the degree of an irreducible representation divides the index of any central subgroup.

## References

See I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 3.12.
-/

public section

open Module (finrank)
open scoped TensorProduct

universe u v

namespace Representation

section Helpers

variable {k : Type*} {H : Type u} {V : Type v} [Field k] [Group H] [AddCommGroup V] [Module k V]

/-- The embedding `(z, a) ↦ (z, ι(z)⁻¹ a)` of `Z × A` into `H × G`, a homomorphism because `ι`
takes central values. -/
private def antidiagonalHom {G : Type*} [Group G] (Z : Subgroup H) (ι : Z →* G)
    (hι : ∀ z, ι z ∈ Subgroup.center G) (A : Subgroup G) : Z × A →* H × G where
  toFun p := ((p.1 : H), (ι p.1)⁻¹ * p.2)
  map_one' := by simp
  map_mul' p q := by
    have hcomm (x : G) : (ι q.1)⁻¹ * x = x * (ι q.1)⁻¹ :=
      (Subgroup.mem_center_iff.mp (inv_mem (hι q.1)) x).symm
    refine Prod.ext (by simp) ?_
    calc (ι (p.1 * q.1))⁻¹ * ((p.2 : G) * q.2)
        = (ι q.1)⁻¹ * ((ι p.1)⁻¹ * p.2) * q.2 := by simp only [map_mul, mul_inv_rev, mul_assoc]
      _ = (ι p.1)⁻¹ * p.2 * (ι q.1)⁻¹ * q.2 := by rw [hcomm]
      _ = (ι p.1)⁻¹ * p.2 * ((ι q.1)⁻¹ * q.2) := by simp only [mul_assoc]

private theorem antidiagonalHom_injective {G : Type*} [Group G] (Z : Subgroup H) (ι : Z →* G)
    (hι : ∀ z, ι z ∈ Subgroup.center G) (A : Subgroup G) :
    Function.Injective (antidiagonalHom Z ι hι A) := fun p q hpq => by
  have h1 : p.1 = q.1 := Subtype.ext (congrArg Prod.fst hpq)
  have h2 : (ι p.1)⁻¹ * p.2 = (ι q.1)⁻¹ * q.2 := congrArg Prod.snd hpq
  rw [h1, mul_right_inj] at h2
  exact Prod.ext h1 (Subtype.ext h2)

private theorem antidiagonalHom_apply {G : Type*} [Group G] (Z : Subgroup H) (ι : Z →* G)
    (hι : ∀ z, ι z ∈ Subgroup.center G) (A : Subgroup G) (p : Z × A) :
    antidiagonalHom Z ι hι A p = ((p.1 : H), (ι p.1)⁻¹ * p.2) :=
  rfl

/-- The image `{(z, ι(z)⁻¹ a)}` is central when `Z` and `A` are. -/
private theorem antidiagonalHom_range_le_center {G : Type*} [Group G] {Z : Subgroup H}
    (hZ : Z ≤ Subgroup.center H) (ι : Z →* G) (hι : ∀ z, ι z ∈ Subgroup.center G)
    {A : Subgroup G} (hA : A ≤ Subgroup.center G) :
    (antidiagonalHom Z ι hι A).range ≤ Subgroup.center (H × G) := by
  rintro _ ⟨p, rfl⟩
  rw [Subgroup.center_prod, Subgroup.mem_prod, antidiagonalHom_apply]
  exact ⟨hZ p.1.property, mul_mem (inv_mem (hι p.1)) (hA p.2.property)⟩

private theorem card_range_antidiagonalHom {G : Type*} [Group G] (Z : Subgroup H) (ι : Z →* G)
    (hι : ∀ z, ι z ∈ Subgroup.center G) (A : Subgroup G) :
    Nat.card (antidiagonalHom Z ι hι A).range = Nat.card Z * Nat.card A := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MonoidHom.ofInjective (antidiagonalHom_injective Z ι hι A)).toEquiv.symm

end Helpers

section Center

variable {k : Type*} {H : Type u} {V : Type v} [Field k] [IsAlgClosed k] [CharZero k] [Group H]
  [AddCommGroup V] [Module k V]

/-- The inductive step of the tensor-power argument, generalised over the group `G` carrying the
running tensor power `σ`, the central copy `ι` of `Z` and the central subgroup `A` acting
trivially. -/
private theorem finrank_mul_pow_dvd_aux (ρ : Representation k H V) [ρ.IsIrreducible]
    [FiniteDimensional k V] (Z : Subgroup H) (hZ : Z ≤ Subgroup.center H) (lam : Z → k)
    (hlam : ∀ (z : Z) v, ρ z v = lam z • v) (m : ℕ) :
    ∀ {G : Type u} [Group G] {W : Type v} [AddCommGroup W] [Module k W]
      (σ : Representation k G W) (_ : σ.IsIrreducible) (ι : Z →* G)
      (_ : ∀ z, ι z ∈ Subgroup.center G) (_ : ∀ (z : Z) w, σ (ι z) w = lam z • w)
      (A : Subgroup G) (_ : A ≤ Subgroup.center G) (_ : ∀ a ∈ A, ∀ w, σ a w = w),
      finrank k W * finrank k V ^ m * (Nat.card A * Nat.card Z ^ m) ∣
        Nat.card G * Nat.card H ^ m := by
  induction m with
  | zero =>
    intro G _ W _ _ σ hσ ι _ _ A hA hAσ
    have : A.Normal := Subgroup.normal_of_le_center hA
    have : IsTrivial (σ.comp A.subtype) := ⟨fun a => LinearMap.ext (hAσ a a.property)⟩
    have : (σ.ofQuotient A).IsIrreducible := (isIrreducible_ofQuotient_iff σ A).mpr hσ
    simpa [A.card_eq_card_quotient_mul_card_subgroup] using
      mul_dvd_mul_right (finrank_dvd_card (σ.ofQuotient A)) (Nat.card A)
  | succ m ih =>
    intro G _ W _ _ σ hσ ι hι hισ A hA hAσ
    have := (inferInstance : ρ.IsIrreducible).nontrivial
    have hinv (z : Z) : lam z⁻¹ * lam z = 1 := by
      rw [← map_mul_of_forall_apply_eq_smul (ρ.comp Z.subtype) hlam, inv_mul_cancel,
        map_one_of_forall_apply_eq_smul (ρ.comp Z.subtype) hlam]
    -- the next tensor power `ρ ⊠ σ` of `H × G`, with `Z` embedded in the first factor and
    -- trivial on the central subgroup `{(z, ι(z)⁻¹ a)}`
    have key := @ih (H × G) _ (V ⊗[k] W) _ _ (ρ.externalTensor σ)
      (isIrreducible_externalTensor ρ σ inferInstance hσ)
      ((MonoidHom.inl H G).comp Z.subtype)
      (fun z => Subgroup.mem_center_iff.mpr fun x => Prod.ext
        (Subgroup.mem_center_iff.mp (hZ z.property) x.1) (by simp))
      (fun z w => by
        induction w using TensorProduct.inductionOn with
        | tmul v w => simp [hlam, TensorProduct.smul_tmul']
        | add x y hx hy => simp_all)
      (antidiagonalHom Z ι hι A).range (antidiagonalHom_range_le_center hZ ι hι hA)
      (by
        rintro _ ⟨p, rfl⟩ w
        induction w using TensorProduct.inductionOn with
        | tmul v w =>
          -- `ι(z)⁻¹` acts on `W` by `λ(z)⁻¹`, cancelling the scalar `λ(z)` of `z` on `V`
          have hσinv : σ (ι p.1)⁻¹ w = lam p.1⁻¹ • w := by rw [← map_inv, hισ]
          simp [antidiagonalHom_apply, hAσ _ p.2.property, hσinv, hlam,
            TensorProduct.smul_tmul', smul_smul, hinv]
        | add x y hx hy => simp_all)
    rw [Module.finrank_tensorProduct, card_range_antidiagonalHom, Nat.card_prod] at key
    calc finrank k W * finrank k V ^ (m + 1) * (Nat.card A * Nat.card Z ^ (m + 1))
        = finrank k V * finrank k W * finrank k V ^ m *
            (Nat.card Z * Nat.card A * Nat.card Z ^ m) := by ring
      _ ∣ Nat.card H * Nat.card G * Nat.card H ^ m := key
      _ = Nat.card G * Nat.card H ^ (m + 1) := by ring

/-- **The degree of an irreducible character divides the index of a central subgroup.**

Over an algebraically closed field of characteristic zero, the dimension of an irreducible
representation of a finite group `H` divides `|H : Z|` for every subgroup `Z` of the centre of
`H`. -/
theorem finrank_dvd_index_of_le_center [Finite H] (ρ : Representation k H V) [ρ.IsIrreducible]
    (Z : Subgroup H) (hZ : Z ≤ Subgroup.center H) : finrank k V ∣ Z.index := by
  have : FiniteDimensional k V := ρ.asModuleEquiv.finiteDimensional
  -- Schur's lemma: a central element acts by a scalar
  have hscal (z : Z) : ∃ c : k, ∀ v, ρ z v = c • v :=
    IsIrreducible.exists_forall_apply_eq_smul (ρ z) fun g v => by
      have hzg : Commute (z : H) g := (Subgroup.mem_center_iff.mp (hZ z.property) g).symm
      rw [← mul_apply_eq_comp, (hzg.map ρ).eq, mul_apply_eq_comp]
  choose lam hlam using hscal
  have hZc : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  refine Nat.dvd_of_forall_pow_dvd_mul_pow hZc fun m => ?_
  have key := finrank_mul_pow_dvd_aux ρ Z hZ lam hlam m ρ inferInstance Z.subtype
    (fun z => hZ z.property) hlam ⊥ bot_le (by simp)
  rw [Subgroup.card_bot, one_mul, ← Z.card_mul_index] at key
  rw [← Nat.mul_dvd_mul_iff_right (pow_pos (Nat.card_pos (α := Z)) m)]
  calc finrank k V ^ (m + 1) * Nat.card Z ^ m
      = finrank k V * finrank k V ^ m * Nat.card Z ^ m := by ring
    _ ∣ Nat.card Z * Z.index * (Nat.card Z * Z.index) ^ m := key
    _ = Nat.card Z * Z.index ^ (m + 1) * Nat.card Z ^ m := by ring

end Center

end Representation

namespace FDRep

variable {k G : Type*} [Field k] [IsAlgClosed k] [CharZero k] [Group G] [Finite G]

/-- **The degree of an irreducible character divides the index of a central subgroup**, for a
bundled finite-dimensional representation. -/
theorem finrank_dvd_index_of_le_center (X : FDRep k G) [Representation.IsIrreducible X.ρ]
    (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G) : finrank k X ∣ Z.index :=
  Representation.finrank_dvd_index_of_le_center X.ρ Z hZ

end FDRep
