/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Degree
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

section Center

variable {k : Type*} {H : Type u} {V : Type v} [Field k] [IsAlgClosed k] [CharZero k] [Group H]
  [AddCommGroup V] [Module k V]

/-- If `d^(m+1)` divides `c * i^(m+1)` for every `m`, with `c ≠ 0`, then `d` divides `i`: for each
prime the exponent in `d` exceeds that in `i` by at most `v_p(c) / (m + 1)`. -/
private theorem dvd_of_forall_pow_dvd_mul_pow {d c i : ℕ} (hd : d ≠ 0) (hc : c ≠ 0)
    (h : ∀ m : ℕ, d ^ (m + 1) ∣ c * i ^ (m + 1)) : d ∣ i := by
  rcases eq_or_ne i 0 with rfl | hi
  · exact dvd_zero d
  rw [← Nat.factorization_le_iff_dvd hd hi]
  intro p
  have hm := (Nat.factorization_le_iff_dvd (pow_ne_zero _ hd)
    (mul_ne_zero hc (pow_ne_zero _ hi))).mpr (h (c.factorization p)) p
  rw [Nat.factorization_mul hc (pow_ne_zero _ hi), Nat.factorization_pow,
    Nat.factorization_pow] at hm
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.add_apply] at hm
  by_contra hlt
  nlinarith [not_le.mp hlt]

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
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    -- the scalars `λ(z)` are multiplicative inverses of `λ(z⁻¹)`
    have hinv (z : Z) : lam z⁻¹ * lam z = 1 := by
      have h1 : ρ ((z : H) * (z⁻¹ : Z)) v₀ = v₀ := by simp
      rw [map_mul, mul_apply_eq_comp, hlam z⁻¹, map_smul, hlam, smul_smul] at h1
      have h2 : (lam z⁻¹ * lam z - 1) • v₀ = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv₀)
    have hcomm (z : Z) (x : G) : (ι z)⁻¹ * x = x * (ι z)⁻¹ :=
      Subgroup.mem_center_iff.mp (inv_mem (hι z)) x |>.symm
    let φ : Z × A →* H × G :=
      { toFun := fun p => ((p.1 : H), (ι p.1)⁻¹ * p.2)
        map_one' := by simp
        map_mul' := fun p q => by
          refine Prod.ext (by simp) ?_
          change (ι (p.1 * q.1))⁻¹ * ((p.2 : G) * q.2) = (ι p.1)⁻¹ * p.2 * ((ι q.1)⁻¹ * q.2)
          calc (ι (p.1 * q.1))⁻¹ * ((p.2 : G) * q.2)
              = (ι q.1)⁻¹ * ((ι p.1)⁻¹ * p.2) * q.2 := by
                simp only [map_mul, mul_inv_rev, mul_assoc]
            _ = (ι p.1)⁻¹ * p.2 * (ι q.1)⁻¹ * q.2 := by rw [hcomm]
            _ = (ι p.1)⁻¹ * p.2 * ((ι q.1)⁻¹ * q.2) := by simp only [mul_assoc] }
    have hφ : Function.Injective φ := fun p q hpq => by
      have h1 : (p.1 : H) = q.1 := congrArg Prod.fst hpq
      have h1' : p.1 = q.1 := Subtype.ext h1
      have h2 : (ι p.1)⁻¹ * p.2 = (ι q.1)⁻¹ * q.2 := congrArg Prod.snd hpq
      rw [h1', mul_right_inj] at h2
      exact Prod.ext h1' (Subtype.ext h2)
    have hcard : Nat.card φ.range = Nat.card Z * Nat.card A := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm
    have key := @ih (H × G) _ (V ⊗[k] W) _ _ (ρ.externalTensor σ)
      (isIrreducible_externalTensor ρ σ inferInstance hσ)
      ((MonoidHom.inl H G).comp Z.subtype)
      (fun z => Subgroup.mem_center_iff.mpr fun x => Prod.ext
        (Subgroup.mem_center_iff.mp (hZ z.property) x.1) (by simp))
      (fun z w => by
        induction w using TensorProduct.inductionOn with
        | tmul v w => simp [hlam, TensorProduct.smul_tmul']
        | add x y hx hy => simp_all)
      φ.range
      (by
        rintro _ ⟨p, rfl⟩
        refine Subgroup.mem_center_iff.mpr fun x => Prod.ext
          (Subgroup.mem_center_iff.mp (hZ p.1.property) x.1) ?_
        exact (Subgroup.mem_center_iff.mp (mul_mem (inv_mem (hι p.1)) (hA p.2.property)) x.2))
      (by
        rintro _ ⟨p, rfl⟩ w
        induction w using TensorProduct.inductionOn with
        | tmul v w =>
          simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, externalTensor_apply,
            TensorProduct.map_tmul, map_mul, mul_apply_eq_comp, hAσ _ p.2.property, ← map_inv,
            hισ, hlam, TensorProduct.smul_tmul, smul_smul]
          rw [mul_comm, hinv, one_smul]
        | add x y hx hy => simp_all)
    rw [Module.finrank_tensorProduct, hcard, Nat.card_prod] at key
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
      rw [← mul_apply_eq_comp, ← map_mul, ← mul_apply_eq_comp, ← map_mul,
        (Subgroup.mem_center_iff.mp (hZ z.property) g).symm]
  choose lam hlam using hscal
  have hd : finrank k V ≠ 0 := (IsIrreducible.finrank_pos (inferInstance : ρ.IsIrreducible)).ne'
  have hZc : Nat.card Z ≠ 0 := Nat.card_pos.ne'
  refine dvd_of_forall_pow_dvd_mul_pow hd hZc fun m => ?_
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
