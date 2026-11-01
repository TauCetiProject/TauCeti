/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.TensorProduct
public import TauCeti.RingTheory.Perfect.FrobeniusRootIdeal

/-!
# Tensor products of perfect rings and `Tor₁` of radical quotients

Let `A` be a perfect ring of prime characteristic `p`, let `I` be a radical ideal of `A` and let
`C` be a perfect `A`-algebra. We show that `I ⊗[A] C → A ⊗[A] C` is injective, that is,
`Tor₁^A(A ⧸ I, C) = 0`. Thus `I ⊗[A] C` maps isomorphically onto the extended ideal `I C`, which
is radical by `Ideal.IsRadical.map`, while `(A ⧸ I) ⊗[A] C` is the reduced quotient `C ⧸ I C` by
`Algebra.TensorProduct.quotIdealMapEquivTensorQuot`. No flatness is involved: `A ⧸ I` is usually
not flat over `A`.

For a Frobenius-root ideal `J_f = √(f)` the statement only needs `C` to be reduced: every element
of `J_f ⊗[A] C` has the form `f ^ (1 / p ^ n) ⊗ c`, and if `f ^ (1 / p ^ n) c = 0` then this
tensor vanishes after rewriting it through the next root `f ^ (1 / p ^ (n + 1))`. For the radical
of a finitely generated ideal, write it as a finite sum of Frobenius-root ideals and use
`Ideal.sup_subtype_rTensor_injective`: the needed identity `I C ∩ J C = (I ⊓ J) C` is
`Ideal.IsRadical.map_inf`. A general radical ideal is the directed union of such radicals.

This is the `Tor₁` part of the Tor independence of perfect rings, which asserts
`Tor_i^A(B, C) = 0` for all `i > 0` and all maps `B ← A → C` of perfect rings, in the case where
`B = A ⧸ I` is a quotient.

The file also shows that `B ⊗[A] C` is perfect whenever `A`, `B` and `C` are perfect
(`Algebra.TensorProduct.perfectRing`): its `p`-th root is `b ⊗ c ↦ b ^ (1 / p) ⊗ c ^ (1 / p)`,
which is well defined because `(a • b) ^ (1 / p) = a ^ (1 / p) • b ^ (1 / p)`. Perfectness of `A`
is needed: over `A = 𝔽_p[t]`, with `B = 𝔽_p[t ^ (1 / p ^ ∞)]` perfect, the element
`t ^ (1 / p) ⊗ 1 - 1 ⊗ t ^ (1 / p)` of `B ⊗[A] B` is nonzero, but its `p`-th power vanishes.

## Main results

* `TauCeti.frobeniusRootIdeal_subtype_rTensor_injective`: `J_f ⊗[A] C → A ⊗[A] C` is injective for
  every reduced `A`-algebra `C`.
* `TauCeti.subtype_rTensor_injective_of_isRadical`: `I ⊗[A] C → A ⊗[A] C` is injective for every
  radical ideal `I` of `A` and every perfect `A`-algebra `C`.
* `Algebra.TensorProduct.perfectRing`: the tensor product of two perfect algebras over a perfect
  ring is perfect.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 3.16 and its proof.
-/

public section

open TensorProduct

namespace TauCeti

variable {A : Type*} [CommRing A] {p : ℕ} [ExpChar A p] [PerfectRing A p] [hp : Fact p.Prime]
  (C : Type*) [CommRing C] [Algebra A C]

/-- **`Tor₁` of `A ⧸ J_f`.** For a Frobenius-root ideal `J_f = √(f)` of a perfect ring `A` and a
reduced `A`-algebra `C`, the map `J_f ⊗[A] C → A ⊗[A] C` is injective. -/
theorem frobeniusRootIdeal_subtype_rTensor_injective [IsReduced C] (f : A) :
    Function.Injective ((frobeniusRootIdeal A p f).subtype.rTensor C) := by
  -- `ρ n` is the `p ^ n`-th root of `f`, as an element of `J_f`.
  let ρ (n : ℕ) : frobeniusRootIdeal A p f :=
    ⟨_, iterateFrobeniusEquiv_symm_mem_frobeniusRootIdeal f n⟩
  have tmul_eq {x : frobeniusRootIdeal A p f} {n : ℕ} {a : A}
      (hx : (x : A) = (iterateFrobeniusEquiv A p n).symm f * a) (c : C) :
      x ⊗ₜ[A] c = ρ n ⊗ₜ (a • c) := by
    rw [← smul_tmul]
    exact congrArg (· ⊗ₜ c) (Subtype.ext (hx.trans (mul_comm _ _)))
  -- Every element of `J_f ⊗[A] C` is of the form `ρ n ⊗ c`.
  have exists_eq (t : frobeniusRootIdeal A p f ⊗[A] C) : ∃ n c, t = ρ n ⊗ₜ c := by
    induction t with
    | tmul x c =>
      obtain ⟨n, a, ha⟩ := mem_frobeniusRootIdeal.mp x.2
      exact ⟨n, a • c, tmul_eq ha c⟩
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨m, c₁, rfl⟩ := h₁
      obtain ⟨n, c₂, rfl⟩ := h₂
      obtain ⟨a₁, ha₁⟩ := iterateFrobeniusEquiv_symm_dvd_of_le (p := p) f (le_max_left m n)
      obtain ⟨a₂, ha₂⟩ := iterateFrobeniusEquiv_symm_dvd_of_le (p := p) f (le_max_right m n)
      refine ⟨max m n, a₁ • c₁ + a₂ • c₂, ?_⟩
      rw [tmul_eq (x := ρ m) ha₁, tmul_eq (x := ρ n) ha₂, tmul_add]
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨n, c, rfl⟩ := exists_eq t
  -- With `s` the image of the `p ^ (n + 1)`-th root of `f`, the hypothesis says `c * s ^ p = 0`.
  set s := algebraMap A C ((iterateFrobeniusEquiv A p (n + 1)).symm f)
  have hρ (m : ℕ) : ((ρ m : frobeniusRootIdeal A p f) : A) = (iterateFrobeniusEquiv A p m).symm f :=
    rfl
  have hc : c * s = 0 := by
    refine mul_eq_zero_of_mul_pow_eq_zero (k := p) ?_
    rw [← map_pow, iterateFrobeniusEquiv_symm_succ_pow, mul_comm, ← Algebra.smul_def]
    simpa [ρ] using congrArg (TensorProduct.lid A C) ht
  -- Rewriting `ρ n = ρ (n + 1) ^ p` as `ρ (n + 1) * ρ (n + 1) ^ (p - 1)` kills the tensor.
  have hρ' : ((ρ n : frobeniusRootIdeal A p f) : A) = (iterateFrobeniusEquiv A p (n + 1)).symm f *
      (iterateFrobeniusEquiv A p (n + 1)).symm f ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, iterateFrobeniusEquiv_symm_succ_pow, hρ]
  have hsc : s ^ (p - 1) * c = 0 := by
    rw [← Nat.succ_pred (Nat.sub_ne_zero_of_lt hp.out.one_lt), pow_succ, mul_assoc, mul_comm s c,
      hc, mul_zero]
  rw [tmul_eq hρ', Algebra.smul_def, map_pow, hsc, tmul_zero]

/-- **`Tor₁` of radical quotients of perfect rings.** For a radical ideal `I` of a perfect ring `A`
and a perfect `A`-algebra `C`, the map `I ⊗[A] C → A ⊗[A] C` is injective, that is,
`Tor₁^A(A ⧸ I, C) = 0`. -/
theorem subtype_rTensor_injective_of_isRadical [ExpChar C p] [PerfectRing C p] {I : Ideal A}
    (hI : I.IsRadical) : Function.Injective (I.subtype.rTensor C) := by
  have := isReduced_of_perfectRing C p
  -- The radical of a finitely generated ideal is a finite sum of Frobenius-root ideals.
  have fg {N : Ideal A} (hN : N.FG) : Function.Injective (N.radical.subtype.rTensor C) := by
    induction N, hN using Submodule.fg_induction with
    | singleton f =>
      rw [← Ideal.span, ← frobeniusRootIdeal_eq_radical (p := p)]
      exact frobeniusRootIdeal_subtype_rTensor_injective C f
    | sup N₁ N₂ _ _ h₁ h₂ =>
      have r₁ := Ideal.radical_isRadical N₁
      have r₂ := Ideal.radical_isRadical N₂
      rw [Ideal.radical_sup, (r₁.sup p r₂).radical]
      refine Ideal.sup_subtype_rTensor_injective h₁ h₂ fun x hx ↦ ?_
      simpa [Ideal.smul_top_eq_map, r₁.map_inf p r₂] using hx
  -- A general radical ideal is the directed union of the radicals of its finitely generated
  -- subideals.
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨N, hN, hNI, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  have hle : Ideal.radical N ≤ I := hI.radical_le_iff.mpr hNI
  rw [← Submodule.inclusion_comp_inclusion Ideal.le_radical hle,
    LinearMap.rTensor_comp_apply] at hx ⊢
  rw [← LinearMap.rTensor_comp_apply, Submodule.subtype_comp_inclusion] at hx
  rw [fg hN (hx.trans (map_zero _).symm), map_zero]

end TauCeti

namespace Algebra.TensorProduct

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C] [Algebra A B]
  [Algebra A C] (p : ℕ) [ExpChar A p] [PerfectRing A p] [ExpChar B p] [PerfectRing B p]
  [ExpChar C p] [PerfectRing C p]

/-- The `p`-th root of `B ⊗[A] C`, `b ⊗ c ↦ b ^ (1 / p) ⊗ c ^ (1 / p)`, as an additive map. -/
private noncomputable def pthRoot : B ⊗[A] C →+ B ⊗[A] C :=
  liftAddHom
    { toFun b :=
        { toFun c := (frobeniusEquiv B p).symm b ⊗ₜ (frobeniusEquiv C p).symm c
          map_zero' := by simp
          map_add' _ _ := by simp [tmul_add] }
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp [add_tmul] }
    fun a b c ↦ by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [TauCeti.frobeniusEquiv_symm_smul, TauCeti.frobeniusEquiv_symm_smul, smul_tmul]

private theorem pthRoot_tmul (b : B) (c : C) :
    pthRoot p (b ⊗ₜ[A] c) = (frobeniusEquiv B p).symm b ⊗ₜ (frobeniusEquiv C p).symm c :=
  rfl

/-- The tensor product of two perfect algebras over a perfect ring is perfect. -/
instance perfectRing : PerfectRing (B ⊗[A] C) p := by
  obtain _ | ⟨hp⟩ := ‹ExpChar A p›
  · exact ⟨by simp only [pow_one]; exact Function.bijective_id⟩
  rcases subsingleton_or_nontrivial (B ⊗[A] C) with _ | _
  · exact ⟨⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun x ↦ ⟨x, Subsingleton.elim _ _⟩⟩⟩
  -- `p = 0` in `B ⊗[A] C`, since it is an `A`-algebra.
  have : CharP (B ⊗[A] C) p := (CharP.charP_iff_prime_eq_zero hp).2 <| by
    rw [← map_natCast (algebraMap A (B ⊗[A] C)), CharP.cast_eq_zero, map_zero]
  have : ExpChar (B ⊗[A] C) p := .prime hp
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨pthRoot p, fun x ↦ ?_, fun x ↦ ?_⟩⟩
  · beta_reduce
    induction x using TensorProduct.inductionOn with
    | tmul b c => rw [tmul_pow, pthRoot_tmul, frobeniusEquiv_symm_pow, frobeniusEquiv_symm_pow]
    | add x y hx hy => rw [add_pow_expChar, map_add, hx, hy]
  · beta_reduce
    induction x using TensorProduct.inductionOn with
    | tmul b c => rw [pthRoot_tmul, tmul_pow, frobeniusEquiv_symm_pow_p, frobeniusEquiv_symm_pow_p]
    | add x y hx hy => rw [map_add, add_pow_expChar, hx, hy]

end Algebra.TensorProduct
