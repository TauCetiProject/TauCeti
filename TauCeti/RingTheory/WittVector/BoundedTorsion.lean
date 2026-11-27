/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty
public import TauCeti.CategoryTheory.Abelian.SerreClass.BoundedTorsion
public import TauCeti.RingTheory.WittVector.Ideal
public import TauCeti.RingTheory.WittVector.Units

/-!
# Witt vectors of a ring map up to bounded torsion

Let `f : A →+* B` be a map of rings of characteristic `p`. This file determines when
`W(f) : W(A) → W(B)` is an isomorphism up to bounded torsion, that is, when its kernel and its
cokernel are each killed by a nonzero integer. This happens exactly when

* the kernel of `f` is a nil ideal of bounded exponent: `a ^ p ^ c = 0` for all `a ∈ ker f`, and
* a uniform `p`-power of every element of `B` comes from `A`: `b ^ p ^ c ∈ f(A)` for all `b ∈ B`

(`WittVector.isoModSerre_isBoundedTorsion_map_iff`). Both conditions are read off Teichmüller
representatives: in characteristic `p`, the Witt vector `[b] * p ^ c = V^c [b ^ p ^ c]` has
`b ^ p ^ c` as its `c`-th Witt coordinate. In the other direction, `y * p ^ c = V^c (F^c y)` has
Witt coordinates `0` and `y_n ^ p ^ c`, and a Witt vector lies in the image of `W(f)` exactly when
all of its Witt coordinates lie in the image of `f` (`WittVector.mem_range_map_iff`).

In the language of sheaves on a scheme `Y` of characteristic `p`, this is the affine form of the
statement that `WO_{Y,ℚ} → f_* WO_{X,ℚ}` is an isomorphism in the isogeny category, the Serre
quotient by sheaves of bounded torsion, for a finite universal homeomorphism `f : X → Y`. When
`A ⊆ B` are reduced and `B ^ p ^ e ⊆ A`, the map `W(A) → W(B)` is injective and `p ^ e` kills its
cokernel. In the other direction, a map `W(A) → W(B)` that is an isomorphism up to bounded torsion
forces `f` to be injective when `A` is reduced (`WittVector.injective_of_isoModSerre_map`) and
every element of `B` to have a uniform `p`-power in `A`: this is the algebraic step in the
converse, that a proper surjective map along which the rational Witt sheaves agree has
geometrically connected fibres.

## Main results

* `WittVector.forall_mul_p_pow_mem_range_map_iff`: in characteristic `p`, `p ^ c` carries `W(B)`
  into the image of `W(f)` iff `b ^ p ^ c ∈ f(A)` for every `b ∈ B`.
* `WittVector.isoModSerre_isBoundedTorsion_map_iff`: `W(f)` is an isomorphism up to bounded
  torsion iff `ker f` is nil of bounded exponent and a uniform `p`-power of every element of `B`
  lies in `f(A)`.
* `WittVector.injective_of_isoModSerre_map`: if `A` is reduced and `W(f)` is an isomorphism up to
  bounded torsion, then `f` is injective.

## References

* [Y. Gongyo, Y. Nakamura, H. Tanaka, *Rational points on log Fano threefolds over a finite
  field*, J. Eur. Math. Soc. 21 (2019)], Lemma 2.22 and its proof.
* [Y. Nakamura, H. Tanaka, *A Witt Nadel vanishing theorem for threefolds*, Compositio Math. 156
  (2020)], Lemma 2.17 and its proof.
* [A. Chatzistamatiou, K. Rülling, *Hodge–Witt cohomology and Witt-rational singularities*,
  Doc. Math. 17 (2012)], §3.7.
-/

public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.ObjectProperty

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {A B : Type*} [CommRing A] [CommRing B]

local notation "𝕎" => WittVector p

section CharP

variable [CharP B p]

/-- In characteristic `p`, multiplication by `p ^ c` carries `W(B)` into the image of `W(f)`
exactly when `b ^ p ^ c` lies in the image of `f` for every `b ∈ B`. -/
theorem forall_mul_p_pow_mem_range_map_iff {f : A →+* B} {c : ℕ} :
    (∀ y : 𝕎 B, y * (p : 𝕎 B) ^ c ∈ (map f).range) ↔ ∀ b, b ^ p ^ c ∈ f.range := by
  refine ⟨fun h b ↦ ?_, fun h y ↦ (mem_range_map_iff f _).mpr fun n ↦ ?_⟩
  · -- The `c`-th Witt coordinate of `[b] * p ^ c` is `b ^ p ^ c`.
    have := mul_pow_charP_coeff_succ (p := p) (teichmuller p b) (m := 0) (n := c)
    rw [zero_add, teichmuller_coeff_zero] at this
    exact this ▸ (mem_range_map_iff f _).mp (h _) c
  · -- The Witt coordinates of `y * p ^ c` are `0` below `c` and `y_m ^ p ^ c` in degree `m + c`.
    rcases lt_or_ge n c with hn | hn
    · rw [mul_pow_charP_coeff_zero y hn]
      exact ⟨0, map_zero f⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
      rw [mul_pow_charP_coeff_succ]
      exact h _

/-- If `p` does not divide `m`, multiplication by `m` is surjective on `W(B) ⧸ W(f)(W(A))`. -/
private theorem surjective_nsmul_quotient_range_map (f : A →+* B) {m : ℕ} (hm : ¬p ∣ m) :
    Function.Surjective fun y : 𝕎 B ⧸ (map f).range.toAddSubgroup ↦ m • y := by
  obtain ⟨u, hu⟩ := (isUnit_natCast_iff (p := p) (R := B)).mpr hm |>.exists_right_inv
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H y =>
    refine ⟨QuotientAddGroup.mk (u * y), ?_⟩
    dsimp only
    rw [← QuotientAddGroup.mk_nsmul, nsmul_eq_mul, ← mul_assoc, hu, one_mul]

end CharP

/-- If `p` does not divide `m`, multiplication by `m` is surjective on the kernel of `W(f)`. -/
private theorem surjective_nsmul_ker_map [CharP A p] (f : A →+* B) {m : ℕ} (hm : ¬p ∣ m) :
    Function.Surjective fun x : (map (p := p) f).toAddMonoidHom.ker ↦ m • x := by
  obtain ⟨u, hu⟩ := (isUnit_natCast_iff (p := p) (R := A)).mpr hm |>.exists_right_inv
  rintro ⟨x, hx⟩
  refine ⟨⟨u * x, ?_⟩, Subtype.ext ?_⟩
  · simp only [AddMonoidHom.mem_ker, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass,
      map_mul] at hx ⊢
    rw [hx, mul_zero]
  · simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, ← mul_assoc, hu, one_mul]

/-- **Witt vectors of a map up to bounded torsion.** For a map `f : A →+* B` of rings of
characteristic `p`, the map `W(f) : W(A) → W(B)` of abelian groups is an isomorphism modulo the
Serre class of bounded-torsion groups, that is, its kernel and its cokernel are each killed by a
nonzero integer, exactly when the kernel of `f` is a nil ideal of bounded exponent and a uniform
`p`-power of every element of `B` lies in the image of `f`. -/
theorem isoModSerre_isBoundedTorsion_map_iff {A B : Type u} [CommRing A] [CommRing B]
    [CharP A p] [CharP B p] (f : A →+* B) :
    (isBoundedTorsion AddCommGrpCat.{u}).isoModSerre
        (AddCommGrpCat.ofHom (map (p := p) f).toAddMonoidHom) ↔
      (∃ c : ℕ, ∀ a ∈ RingHom.ker f, a ^ p ^ c = 0) ∧ ∃ c : ℕ, ∀ b, b ^ p ^ c ∈ f.range := by
  rw [isoModSerre_iff, monoModSerre_iff, epiModSerre_iff,
    prop_iff_of_iso (isBoundedTorsion _) (AddCommGrpCat.kernelIsoKer _),
    prop_iff_of_iso (isBoundedTorsion _) (AddCommGrpCat.cokernelIsoQuotient _),
    AddCommGrpCat.prop_isBoundedTorsion_iff_exists_pow_nsmul_eq_zero hp.out
      fun m hm ↦ surjective_nsmul_ker_map f (hp.out.coprime_iff_not_dvd.mp hm.symm),
    AddCommGrpCat.prop_isBoundedTorsion_iff_exists_pow_nsmul_eq_zero hp.out
      fun m hm ↦ surjective_nsmul_quotient_range_map f (hp.out.coprime_iff_not_dvd.mp hm.symm)]
  refine and_congr ?_ ?_
  · refine exists_congr fun c ↦ ?_
    rw [← forall_mem_ideal_mul_p_pow_eq_zero_iff, ← ker_map]
    simp only [AddCommGrpCat.hom_ofHom, Subtype.forall, ← Subtype.val_inj, AddSubgroup.coe_nsmul,
      ZeroMemClass.coe_zero, AddMonoidHom.mem_ker, RingHom.mem_ker, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass, nsmul_eq_mul', Nat.cast_pow]
  · refine exists_congr fun c ↦ ?_
    rw [← forall_mul_p_pow_mem_range_map_iff]
    simp only [AddCommGrpCat.hom_ofHom, QuotientAddGroup.mk_surjective.forall,
      ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, nsmul_eq_mul', Nat.cast_pow,
      AddMonoidHom.mem_range, RingHom.mem_range, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_ofClass]

/-- If `A` is reduced and `W(f)` is an isomorphism up to bounded torsion, then `f` is injective:
its kernel is a nil ideal. -/
theorem injective_of_isoModSerre_map {A B : Type u} [CommRing A] [CommRing B] [CharP A p]
    [CharP B p] [IsReduced A] {f : A →+* B}
    (hf : (isBoundedTorsion AddCommGrpCat.{u}).isoModSerre
      (AddCommGrpCat.ofHom (map (p := p) f).toAddMonoidHom)) :
    Function.Injective f := by
  obtain ⟨⟨c, hc⟩, -⟩ := (isoModSerre_isBoundedTorsion_map_iff f).mp hf
  exact (injective_iff_map_eq_zero f).mpr fun a ha ↦ IsReduced.eq_zero a ⟨_, hc a ha⟩

end WittVector
