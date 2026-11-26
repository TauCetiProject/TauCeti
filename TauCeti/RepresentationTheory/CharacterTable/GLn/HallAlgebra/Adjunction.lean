/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Mackey
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.GeneralLinearGroup.Basic
import TauCeti.LinearAlgebra.Dimension.Submodule
import TauCeti.LinearAlgebra.GeneralLinearGroup.SubmoduleOrbit

/-!
# The adjoint of the induction product, and cuspidal elements

For class functions `A`, `A′` on all square matrices over a finite field `k`, the inner product
in rank `n` is `⟨A, A′⟩_n = |GL_n(k)|⁻¹ Σ_{g ∈ GL_n(k)} conj (A g) · A′ g`. For `f` and `d`, the
function `∂_{d,f} A : a ↦ ⟨f, δA(a, ·)⟩_d` pairs `f` with the block average of `A`. It is the
adjoint of multiplication by `f` when `f` lives in size `d`, and for cuspidal `f` and `d ≠ 0`,
`∂_{d,f}` is a derivation (it satisfies the Leibniz rule).

## Main definitions

* `TauCeti.HallAlgebra.rankInner n A A′`: the inner product `⟨A, A′⟩_n` over `GL_n(k)`.
* `TauCeti.HallAlgebra.mulAdjoint d f A`: the function `∂_{d,f} A`.

## Main results

* `TauCeti.HallAlgebra.rankInner_mul_eq_sum_mulAdjoint`:
  `⟨A ∗ B, X⟩_n = Σ_{p + q = n} ⟨A, ∂_{q,B} X⟩_p`. The pairs `(g, U)` of an invertible `g` and a
  `g`-invariant subspace `U` are counted by `U` first: the subspaces of one dimension form one
  orbit of `GL_n(k)`, and the stabiliser of `U` is the group of block upper triangular maps for
  `V = U ⊕ Z`, parametrised by its three blocks.
* `TauCeti.HallAlgebra.rankInner_mul_eq_rankInner_mulAdjoint` (adjunction): if `f` vanishes off
  the classes of size `d`, then `⟨f ∗ A′, A⟩_{d+n} = ⟨A′, ∂_{d,f} A⟩_n`.
* `TauCeti.HallAlgebra.mulAdjoint_of_isCuspidal`: for cuspidal `c` and `d ≠ 0`,
  `∂_{d,f} c = ⟨f, c⟩_d · 1`.
* `TauCeti.HallAlgebra.mulAdjoint_mul`: for cuspidal `c` and `d ≠ 0`, `∂_{d,c}` is a derivation,
  by Mackey's formula `TauCeti.HallAlgebra.blockAverage_mul`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* A. V. Zelevinsky, *Representations of finite classical groups: a Hopf algebra approach*,
  Lecture Notes in Math. 869 (1981), §9.
* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.Hall.rankInner`, `New.Hall.skew`, `New.Hall.rankInner_eq_classInner_simClassOf`,
  `New.Hall.rankInner_mul_eq_sum_skew`, `New.Hall.rankInner_mul_eq_rankInner_skew`,
  `New.Hall.mul_apply_of_dim_zero`, `New.Hall.rankInner_mul_of_isCuspidal`,
  `New.Hall.skew_of_isCuspidal` and `New.Hall.skew_mul`; the finite means `New.finMean` of
  `src/Lib/General/Groups/CharacterTheory.lean` are `Mathlib`'s `Finset.expect` here.
-/

public section

open Module TauCeti.SimilarityClass ComplexConjugate
open scoped BigOperators

open Module.End (blockTriangular blockTriangular_apply)
open Submodule (blockUnit blockUnit_apply blockUnit_mem_stabilizer)

namespace TauCeti.HallAlgebra

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- The inner product `⟨A, A′⟩_n`: the mean over `g ∈ GL_n(k)` of `conj (A g) · A′ g`. -/
noncomputable def rankInner (n : ℕ) (F H : HallAlgebra k) : ℂ :=
  𝔼 g : GL (Fin n) k, conj (F (ofEnd (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)))) *
    H (ofEnd (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)))

/-- The inner product `⟨A, A′⟩_n` is the mean over `g ∈ GL_n(k)` of `conj (A g) · A′ g`. -/
theorem rankInner_def (n : ℕ) (F H : HallAlgebra k) :
    rankInner n F H =
      𝔼 g : GL (Fin n) k, conj (F (ofEnd (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k)))) *
        H (ofEnd (Matrix.toLin' (g : Matrix (Fin n) (Fin n) k))) :=
  (rfl)

/-- The function `∂_{d,f} A : a ↦ ⟨f, δA(a, ·)⟩_d`, pairing `f` in rank `d` with the block average
of `A`. -/
noncomputable def mulAdjoint (d : ℕ) (f F : HallAlgebra k) : HallAlgebra k :=
  fun a ↦ rankInner d f (blockAverage F a)

/-- The value of `∂_{d,f} A` at `a` is `⟨f, δA(a, ·)⟩_d`. -/
@[simp]
theorem mulAdjoint_apply (d : ℕ) (f F : HallAlgebra k) (a : SimilarityClass k) :
    mulAdjoint d f F a = rankInner d f (blockAverage F a) :=
  (rfl)

/-- The function `∂_{d,f} 0` is `0`. -/
@[simp]
theorem mulAdjoint_zero (d : ℕ) (f : HallAlgebra k) : mulAdjoint d f 0 = 0 :=
  ext fun _ ↦ by simp [rankInner_def]

/-- The function `∂_{d,f} A` is additive in `A`. -/
@[simp]
theorem mulAdjoint_add (d : ℕ) (f F H : HallAlgebra k) :
    mulAdjoint d f (F + H) = mulAdjoint d f F + mulAdjoint d f H :=
  ext fun _ ↦ by simp [rankInner_def, mul_add, Finset.expect_add_distrib]

/-- The function `∂_{d,f} A` commutes with complex scalars in `A`. -/
@[simp]
theorem mulAdjoint_smul (d : ℕ) (f : HallAlgebra k) (c : ℂ) (F : HallAlgebra k) :
    mulAdjoint d f (c • F) = c • mulAdjoint d f F :=
  ext fun _ ↦ by simp [rankInner_def, Finset.mul_expect, mul_left_comm]

omit [Fintype k] [DecidableEq k] in
/-- The automorphisms of a finite-dimensional space over a finite field form a finite group. -/
private local instance finite_units_end [Finite k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] : Finite (Module.End k V)ˣ :=
  have : Finite (Module.End k V) := Module.finite_of_finite k
  inferInstance

omit [Fintype k] [DecidableEq k] in
/-- A finite-dimensional space over a finite field has finitely many subspaces. -/
private local instance finite_submodule [Finite k] {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] : Finite (Submodule k V) :=
  have : Finite V := Module.finite_of_finite k
  inferInstance

/-! ### Inner products as means over automorphisms -/

section Units

attribute [local instance low] Fintype.ofFinite

variable {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The inner product in rank `dim V` is the mean over the automorphisms of `V`. -/
theorem rankInner_finrank_eq_expect [Fintype (Module.End k V)ˣ] (F H : HallAlgebra k) :
    rankInner (finrank k V) F H =
      𝔼 g : (Module.End k V)ˣ, conj (F (ofEnd (g : Module.End k V))) *
        H (ofEnd (g : Module.End k V)) := by
  -- Conjugate by the coordinates of a basis of `V`.
  let b := (finBasis k V).equivFun
  let E : GL (Fin (finrank k V)) k ≃ (Module.End k V)ˣ :=
    (Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv b.symm)).toEquiv
  have h_class (g : GL (Fin (finrank k V)) k) :
      ofEnd (Matrix.toLin' (g : Matrix (Fin (finrank k V)) (Fin (finrank k V)) k)) =
        ofEnd ((E g : (Module.End k V)ˣ) : Module.End k V) :=
    ofEnd_eq_of_apply_eq b.symm fun x ↦ by simp [E]
  exact Fintype.expect_equiv E _ _ fun g ↦ by rw [h_class]

end Units

/-! ### The stabiliser of a subspace -/

section Stabilizer

open Pointwise MulAction

attribute [local instance low] Fintype.ofFinite

variable {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]

variable {U Z : Submodule k V} (hUZ : IsCompl U Z)

/-- The term of a pair `(g, U)` in the expansion of `⟨A ∗ B, X⟩`. -/
private noncomputable def pairTerm (A B X : HallAlgebra k) (g : (Module.End k V)ˣ)
    {U : Submodule k V} (hU : U ∈ (g : Module.End k V).invtSubmodule) : ℂ :=
  conj (A (ofEnd ((g : Module.End k V).invtRestrict hU))) *
    conj (B (ofEnd ((g : Module.End k V).invtQuot hU))) * X (ofEnd (g : Module.End k V))

omit [Fintype k] [DecidableEq k] in
/-- On the automorphism with blocks `a`, `b`, `x`, the restriction to `U` has the class of `a`, the
map on `V ⧸ U` the class of `b`, and the whole map the class of the block map on `U × Z`. -/
private theorem pairTerm_blockUnit (A B X : HallAlgebra k) (a : (Module.End k U)ˣ)
    (b : (Module.End k Z)ˣ) (x : Z →ₗ[k] U) :
    pairTerm A B X (blockUnit hUZ a b x)
        (Submodule.mem_invtSubmodule_of_mem_stabilizer (blockUnit_mem_stabilizer hUZ a b x)) =
      conj (A (ofEnd (a : Module.End k U))) * conj (B (ofEnd (b : Module.End k Z))) *
        X (ofEnd (blockTriangular (a : Module.End k U) (b : Module.End k Z) x)) := by
  let e := U.prodEquivOfIsCompl Z hUZ
  have h_mem := Submodule.mem_invtSubmodule_of_mem_stabilizer (blockUnit_mem_stabilizer hUZ a b x)
  rw [pairTerm, ofEnd_invtRestrict_eq_of_injective (g := (a : Module.End k U)) U.subtype
      (fun u ↦ by simp [blockUnit_apply]) h_mem U.injective_subtype U.range_subtype,
    ofEnd_invtQuot_eq_of_surjective (g' := (b : Module.End k Z))
      (LinearMap.snd k U Z ∘ₗ e.symm.toLinearMap) (fun v ↦ by simp [e, blockUnit_apply]) h_mem
      ((LinearMap.snd_surjective (R := k) (M := U) (M₂ := Z)).comp e.symm.surjective) ?_,
    ofEnd_eq_of_apply_eq (g' := blockTriangular (a : Module.End k U) (b : Module.End k Z) x)
      e.symm fun v ↦ by simp [e, blockUnit_apply]]
  ext v
  simp [e]

include hUZ in
/-- The mean over the stabiliser of `U` of the term of `(g, U)` is `⟨A, ∂_{q,B} X⟩_p`, with
`p = dim U` and `q = dim Z`. -/
private theorem expect_stabilizer (A B X : HallAlgebra k) :
    𝔼 g : stabilizer (Module.End k V)ˣ U,
        pairTerm A B X g (Submodule.mem_invtSubmodule_of_mem_stabilizer (M := V) (U := U) g.prop) =
      rankInner (finrank k U) A (mulAdjoint (finrank k Z) B X) := by
  have : Finite (Z →ₗ[k] U) := Module.finite_of_finite k
  rw [← Fintype.expect_bijective (Submodule.stabilizerBlockEquiv hUZ)
    (Submodule.stabilizerBlockEquiv hUZ).bijective
    (fun t ↦ conj (A (ofEnd (t.1 : Module.End k U))) * conj (B (ofEnd (t.2.1 : Module.End k Z))) *
      X (ofEnd (blockTriangular (t.1 : Module.End k U) (t.2.1 : Module.End k Z) t.2.2))) _
    fun t ↦ by
      rw [← pairTerm_blockUnit hUZ A B X t.1 t.2.1 t.2.2]
      simp only [Submodule.coe_stabilizerBlockEquiv_apply]]
  simp_rw [rankInner_finrank_eq_expect, mulAdjoint_apply, rankInner_finrank_eq_expect,
    blockAverage_ofEnd, Finset.mul_expect, ← Finset.univ_product_univ, Finset.expect_product,
    mul_assoc]

end Stabilizer

/-! ### Counting the pairs `(g, U)` by `U` -/

section Orbit

open Pointwise MulAction

attribute [local instance low] Fintype.ofFinite

variable {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The sum over the stabiliser of `U` of the term of `(g, U)` is `|Stab(U)|` times
`⟨A, ∂_{q,B} X⟩_p`, with `p = dim U` and `q = dim V - p`. -/
private theorem sum_stabilizer_pairTerm (A B X : HallAlgebra k) (U : Submodule k V) :
    ∑ g : stabilizer (Module.End k V)ˣ U,
        pairTerm A B X g (Submodule.mem_invtSubmodule_of_mem_stabilizer (M := V) (U := U) g.prop) =
      Fintype.card (stabilizer (Module.End k V)ˣ U) *
        rankInner (finrank k U) A (mulAdjoint (finrank k V - finrank k U) B X) := by
  obtain ⟨Z, hZ⟩ := U.exists_isCompl
  have h_dim : finrank k Z = finrank k V - finrank k U := by
    have := Submodule.finrank_add_eq_of_isCompl hZ
    omega
  have h_mean := expect_stabilizer hZ A B X
  rw [Fintype.expect_eq_sum_div_card, h_dim] at h_mean
  rw [← h_mean, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]

/-- `⟨A ∗ B, X⟩` in rank `dim V`, expanded over the dimension `p` of the invariant subspace. -/
private theorem rankInner_mul_finrank (A B X : HallAlgebra k) :
    rankInner (finrank k V) (A * B) X =
      ∑ p ∈ Finset.range (finrank k V + 1),
        rankInner p A (mulAdjoint (finrank k V - p) B X) := by
  classical
  -- The pairs `(g, U)` with `U` invariant under `g`, listed by `U` first.
  let pairs : (Σ U : Submodule k V, stabilizer (Module.End k V)ˣ U) ≃
      Σ g : (Module.End k V)ˣ, (g : Module.End k V).invtSubmodule :=
    { toFun x := ⟨x.2, x.1, Submodule.mem_invtSubmodule_of_mem_stabilizer x.2.prop⟩
      invFun y := ⟨y.2.val, y.1, mem_stabilizer_iff.2 (Submodule.units_smul_eq_of_forall_mem _
        ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 y.2.prop) rfl)⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  have h_exp (g : (Module.End k V)ˣ) :
      conj ((A * B) (ofEnd (g : Module.End k V))) * X (ofEnd (g : Module.End k V)) =
        ∑ W : (g : Module.End k V).invtSubmodule, pairTerm A B X g W.prop := by
    simp [pairTerm, mul_ofEnd_eq_sum, Finset.sum_mul]
  have h_lhs : rankInner (finrank k V) (A * B) X =
      ∑ U : Submodule k V,
        rankInner (finrank k U) A (mulAdjoint (finrank k V - finrank k U) B X) /
          (Finset.univ.filter fun Y : Submodule k V ↦ finrank k Y = finrank k U).card := by
    rw [rankInner_finrank_eq_expect, Fintype.expect_eq_sum_div_card]
    simp_rw [h_exp]
    rw [← Fintype.sum_sigma (fun j : Σ g : (Module.End k V)ˣ, (g : Module.End k V).invtSubmodule ↦
        pairTerm A B X j.1 j.2.prop), ← Fintype.sum_equiv pairs _ _ fun _ ↦ rfl,
      Fintype.sum_sigma, Finset.sum_div]
    refine Finset.sum_congr rfl fun U _ ↦
      (congrArg (· / (Fintype.card (Module.End k V)ˣ : ℂ))
        (sum_stabilizer_pairTerm A B X U)).trans ?_
    -- Orbit-stabiliser: `|GL(V)|` is `|Stab(U)|` times the number of subspaces of dimension
    -- `dim U`.
    have h := U.card_stabilizer_mul_card_finrank_eq
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype (p := fun Y : Submodule k V ↦ finrank k Y = finrank k U)] at h
    rw [mul_comm, mul_div_assoc, ← h, Nat.cast_mul,
      div_mul_cancel_left₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), div_eq_mul_inv]
  -- Group the subspaces by dimension.
  rw [h_lhs, Finset.sum_comp (fun p ↦ rankInner p A (mulAdjoint (finrank k V - p) B X) /
    (Finset.univ.filter fun Y : Submodule k V ↦ finrank k Y = p).card),
    Submodule.image_finrank_eq_range]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have h_ne : (Finset.univ.filter fun Y : Submodule k V ↦ finrank k Y = p).card ≠ 0 := by
    rw [← Submodule.image_finrank_eq_range] at hp
    obtain ⟨U, -, hU⟩ := Finset.mem_image.1 hp
    exact Finset.card_ne_zero.2 ⟨U, by simpa using hU⟩
  rw [nsmul_eq_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 h_ne)]

end Orbit

/-! ### The adjunction and cuspidal elements -/

section Adjunction

/-- `⟨A ∗ B, X⟩_n = Σ_{p + q = n} ⟨A, ∂_{q,B} X⟩_p`. -/
theorem rankInner_mul_eq_sum_mulAdjoint (n : ℕ) (A B X : HallAlgebra k) :
    rankInner n (A * B) X =
      ∑ p ∈ Finset.antidiagonal n, rankInner p.1 A (mulAdjoint p.2 B X) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simpa using rankInner_mul_finrank (V := Fin n → k) A B X

/-- Conjugating the inner product exchanges its arguments. -/
@[simp]
theorem conj_rankInner (n : ℕ) (F H : HallAlgebra k) :
    conj (rankInner n F H) = rankInner n H F := by
  simp [rankInner, map_expect, mul_comm]

/-- The inner product is linear in its second argument. -/
@[simp]
theorem rankInner_smul_right (n : ℕ) (F H : HallAlgebra k) (a : ℂ) :
    rankInner n F (a • H) = a * rankInner n F H := by
  simp [rankInner, Finset.mul_expect, mul_left_comm]

/-- The inner product is additive in its second argument. -/
@[simp]
theorem rankInner_add_right (n : ℕ) (F H H' : HallAlgebra k) :
    rankInner n F (H + H') = rankInner n F H + rankInner n F H' := by
  simp [rankInner, mul_add, Finset.expect_add_distrib]

/-- The inner product commutes with finite sums in its second argument. -/
theorem rankInner_sum_right {ι : Type*} (s : Finset ι) (n : ℕ) (F : HallAlgebra k)
    (H : ι → HallAlgebra k) : rankInner n F (∑ i ∈ s, H i) = ∑ i ∈ s, rankInner n F (H i) := by
  simp [rankInner, Finset.mul_sum, Finset.expect_sum_comm]

/-- The inner product vanishes if its first argument vanishes on the classes of size `n`. -/
theorem rankInner_eq_zero_of_left {n : ℕ} {F : HallAlgebra k}
    (hF : ∀ c : SimilarityClass k, c.dim = n → F c = 0) (H : HallAlgebra k) :
    rankInner n F H = 0 :=
  Finset.expect_eq_zero fun g _ ↦ by rw [hF _ (by simp), map_zero, zero_mul]

/-- The inner product vanishes if its second argument vanishes on the classes of size `n`. -/
theorem rankInner_eq_zero_of_right {n : ℕ} (F : HallAlgebra k) {H : HallAlgebra k}
    (hH : ∀ c : SimilarityClass k, c.dim = n → H c = 0) :
    rankInner n F H = 0 :=
  Finset.expect_eq_zero fun g _ ↦ by rw [hH _ (by simp), mul_zero]

/-- In rank `0` the inner product is the product of the values at the class of size `0`. -/
theorem rankInner_zero (F H : HallAlgebra k) {o : SimilarityClass k} (ho : o.dim = 0) :
    rankInner 0 F H = conj (F o) * H o := by
  have h_class (g : GL (Fin 0) k) : ofEnd (Matrix.toLin' (g : Matrix (Fin 0) (Fin 0) k)) = o :=
    eq_of_dim_eq_zero (by simp) ho
  simp [rankInner, h_class]

/-- **Adjunction.** If `f` vanishes off the classes of size `d`, then
`⟨f ∗ A′, A⟩_{d+n} = ⟨A′, ∂_{d,f} A⟩_n`. -/
theorem rankInner_mul_eq_rankInner_mulAdjoint {d : ℕ} (n : ℕ) {f : HallAlgebra k}
    (hf : ∀ c : SimilarityClass k, c.dim ≠ d → f c = 0) (A' A : HallAlgebra k) :
    rankInner (d + n) (f * A') A = rankInner n A' (mulAdjoint d f A) := by
  -- Only the pair of sizes `(n, d)` survives, as `f` vanishes off size `d`.
  rw [mul_comm, rankInner_mul_eq_sum_mulAdjoint,
    Finset.sum_eq_single (n, d) (fun pq hpq hne ↦ ?_) (by simp [add_comm])]
  obtain ⟨p, q⟩ := pq
  have hq : q ≠ d := by
    rintro rfl
    exact hne (Prod.ext (by simp at hpq; omega) rfl)
  exact rankInner_eq_zero_of_right _ fun a _ ↦
    rankInner_eq_zero_of_left (fun c hc ↦ hf c (hc ▸ hq)) _

variable {c : HallAlgebra k}

/-- For cuspidal `c` and `d ≠ 0`, `∂_{d,f} c` is `⟨f, c⟩_d` times the unit. -/
theorem mulAdjoint_of_isCuspidal (hc : c.IsCuspidal) {d : ℕ} (hd : d ≠ 0) (f : HallAlgebra k) :
    mulAdjoint d f c = rankInner d f c • 1 := by
  ext o
  by_cases ho : o.dim = 0
  · -- At a class of size `0` the block average of `c` is `c`.
    simp [mulAdjoint_apply, blockAverage_eq_self_of_dim_eq_zero c ho, ho]
  · -- At any other class it vanishes on blocks of size `d ≠ 0`.
    rw [mulAdjoint_apply, rankInner_eq_zero_of_right _ fun b hb ↦
      hc.blockAverage_eq_zero ho (hb ▸ hd)]
    simp [ho]

/-- For cuspidal `c` and `d ≠ 0`, the pairing with `c` in rank `d` satisfies the Leibniz rule, the
other factor being evaluated at the class `o` of size `0`. -/
private theorem rankInner_mul_of_isCuspidal (hc : c.IsCuspidal) {d : ℕ} (hd : d ≠ 0)
    (F H : HallAlgebra k) {o : SimilarityClass k} (ho : o.dim = 0) :
    rankInner d c (F * H) = rankInner d c F * H o + F o * rankInner d c H := by
  -- In the expansion of `⟨F ∗ H, c⟩_d` only the sizes `(d, 0)` and `(0, d)` contribute.
  have h_sum : rankInner d (F * H) c =
      rankInner d F (mulAdjoint 0 H c) + rankInner 0 F (mulAdjoint d H c) := by
    rw [rankInner_mul_eq_sum_mulAdjoint, Finset.sum_eq_add (d, 0) (0, d) (by simp [hd]) ?_
      (by simp) (by simp)]
    rintro ⟨p, q⟩ h_mem ⟨h_ne₁, h_ne₂⟩
    have h_add : p + q = d := Finset.mem_antidiagonal.1 h_mem
    have hp : p ≠ 0 := by rintro rfl; exact h_ne₂ (by simp_all)
    have hq : q ≠ 0 := by rintro rfl; exact h_ne₁ (by simp_all)
    -- On classes of size `p ≠ 0`, `∂_{q,H} c` vanishes since `c` is cuspidal and `q ≠ 0`.
    refine rankInner_eq_zero_of_right _ fun a ha ↦ ?_
    rw [mulAdjoint_apply, rankInner_eq_zero_of_right _ fun b hb ↦
      hc.blockAverage_eq_zero (ha ▸ hp) (hb ▸ hq)]
  have h_zero_dim : mulAdjoint 0 H c = conj (H o) • c :=
    ext fun a ↦ by
      rw [mulAdjoint_apply, rankInner_zero _ _ ho, blockAverage_of_dim_eq_zero_right c ho,
        smul_apply]
  have h_d : mulAdjoint d H c o = rankInner d H c := by
    rw [mulAdjoint_apply, blockAverage_eq_self_of_dim_eq_zero c ho]
  rw [← conj_rankInner, h_sum, h_zero_dim, rankInner_zero _ _ ho, h_d]
  simp [rankInner_smul_right, conj_rankInner]
  ring

/-- **Leibniz rule.** For cuspidal `c` and `d ≠ 0`, `∂_{d,c}` is a derivation of the Hall
algebra: `∂_{d,c}(A ∗ A′) = ∂_{d,c} A ∗ A′ + A ∗ ∂_{d,c} A′`. -/
theorem mulAdjoint_mul (hc : c.IsCuspidal) {d : ℕ} (hd : d ≠ 0) (F H : HallAlgebra k) :
    mulAdjoint d c (F * H) = mulAdjoint d c F * H + F * mulAdjoint d c H := by
  refine ext_ofEnd fun _ g ↦ ?_
  have := Fintype.ofFinite g.invtSubmodule
  let o : SimilarityClass k := ofEnd (0 : Module.End k (Fin 0 → k))
  have ho : o.dim = 0 := by simp [o]
  -- By Mackey's formula both sides are sums over the `g`-invariant subspaces `W`.
  have h_mackey : blockAverage (F * H) (ofEnd g) =
      ∑ W : g.invtSubmodule, blockAverage F (ofEnd (g.invtRestrict W.prop)) *
        blockAverage H (ofEnd (g.invtQuot W.prop)) :=
    ext_ofEnd fun _ b ↦ by rw [blockAverage_mul, finsum_eq_sum_of_fintype, finset_sum_apply]
  rw [mulAdjoint_apply, h_mackey, rankInner_sum_right, add_apply, mul_ofEnd_eq_sum,
    mul_ofEnd_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun W _ ↦ ?_
  -- The term of `W` is the Leibniz rule for the block averages at `g|_W` and `g|_{V/W}`.
  rw [rankInner_mul_of_isCuspidal hc hd _ _ ho, mulAdjoint_apply, mulAdjoint_apply,
    blockAverage_of_dim_eq_zero_right _ ho, blockAverage_of_dim_eq_zero_right _ ho]

end Adjunction

end TauCeti.HallAlgebra

