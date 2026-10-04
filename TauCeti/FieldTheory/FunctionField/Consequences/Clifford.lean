/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Union
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Genus

/-!
# Clifford's theorem for divisors of a function field

This file proves Clifford's dimension bound for a divisor `D` of an algebraic function field
over an arbitrary exact field of constants, assuming `0 ≤ deg D ≤ 2g - 2`:

`2 * ℓ(D) ≤ deg D + 2`.

The main input is the dimension inequality

`ℓ(A) + ℓ(B) ≤ 1 + ℓ(A + B)`

when both Riemann–Roch spaces are nonzero.  Its proof replaces `A` and `B` by effective
representatives, chooses a divisor `D₀ ≤ A` of least degree with `L(D₀) = L(A)`, and uses that a
vector space over a field with more than `m` elements is not a union of `m` proper subspaces.
A section of `L(D₀)` can therefore be chosen with the exact pole order prescribed by `D₀` at every
place in the support of `B`, as soon as the constant field has more than `deg B + 1` elements.
Multiplication by that section embeds `L(B) / k` into `L(A + B) / L(A)`.

Over a finite constant field there may be too few constants for this choice.  The inequality is
then proved after a finite constant field extension `F · k' / k'` with enough constants: the
conorm preserves degrees and the dimensions of Riemann–Roch spaces, and `k'` stays exact since
finite fields are perfect.

Applying the inequality to `A = D` and `B = W - D`, for a canonical divisor `W`, and using
Riemann--Roch gives Clifford's theorem.  This is the route of Stichtenoth, *Algebraic Function
Fields and Codes*, 2nd ed., Lemma 1.6.14 and Theorem 1.6.13, whose choice of the section uses an
infinite constant field; the reduction from a finite constant field uses the constant field
extensions of Theorem 3.6.3.

## Main results

* `TauCeti.Divisor.dim_add_dim_le_one_add_dim_add_of_lt_card`: Stichtenoth's dimension
  inequality `ℓ(A) + ℓ(B) ≤ 1 + ℓ(A + B)` when the constant field has more than `deg B + 1`
  elements, in particular when it is infinite.
* `TauCeti.Divisor.dim_add_dim_le_one_add_dim_add`: the dimension inequality over an arbitrary
  exact constant field.
* `TauCeti.Divisor.two_mul_dim_le_degree_add_two`: Clifford's theorem over an arbitrary exact
  constant field.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Lemma 1.6.14, Theorem 1.6.13 and Theorem 3.6.3.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- Among the divisors below an effective divisor `A` with the same Riemann--Roch space, one has
least degree.  Subtracting any place from such a divisor strictly decreases its Riemann--Roch
space. -/
private theorem exists_minimal_riemannRochSpace (hF : IsFunctionField k F)
    {A : Divisor k F} (hA : 0 ≤ A) :
    ∃ D : Divisor k F, D ≤ A ∧ riemannRochSpace D = riemannRochSpace A ∧
      ∀ P : Place k F,
        riemannRochSpace (D - WeilDivisor.ofPoint P) < riemannRochSpace D := by
  classical
  let p : ℕ → Prop := fun n ↦ ∃ D : Divisor k F,
    D ≤ A ∧ riemannRochSpace D = riemannRochSpace A ∧ degree D = n
  have hp : ∃ n, p n := by
    refine ⟨(degree A).toNat, A, le_rfl, rfl, ?_⟩
    exact (Int.toNat_of_nonneg (degree_nonneg hA)).symm
  let n := Nat.find hp
  obtain ⟨D, hDA, hspace, hdegree⟩ := Nat.find_spec hp
  refine ⟨D, hDA, hspace, fun P ↦ ?_⟩
  have hpoint : 0 ≤ WeilDivisor.ofPoint P :=
    WeilDivisor.isEffective_iff_zero_le.mp (WeilDivisor.isEffective_ofPoint P)
  have hle : riemannRochSpace (D - WeilDivisor.ofPoint P) ≤ riemannRochSpace D :=
    riemannRochSpace_mono (sub_le_self D hpoint)
  refine lt_of_le_of_ne hle fun heq ↦ ?_
  have hAne : riemannRochSpace A ≠ ⊥ := by
    intro hbot
    have hone := one_mem_riemannRochSpace_iff.mpr hA
    rw [hbot] at hone
    simp at hone
  have hsubne : riemannRochSpace (D - WeilDivisor.ofPoint P) ≠ ⊥ := by
    rw [heq, hspace]
    exact hAne
  have hnonneg : 0 ≤ degree (D - WeilDivisor.ofPoint P) := by
    by_contra hneg
    exact hsubne (riemannRochSpace_eq_bot_of_degree_neg hF (lt_of_not_ge hneg))
  let m := (degree (D - WeilDivisor.ofPoint P)).toNat
  have hmdegree : degree (D - WeilDivisor.ofPoint P) = m :=
    (Int.toNat_of_nonneg hnonneg).symm
  have hpm : p m := ⟨D - WeilDivisor.ofPoint P,
    (sub_le_self D hpoint).trans hDA, heq.trans hspace, hmdegree⟩
  have hnm : n ≤ m := Nat.find_min' hp hpm
  have hPpos : 0 < (P.degree : ℤ) := by
    exact_mod_cast P.one_le_degree_of_isFunctionField hF
  have hm_lt : (m : ℤ) < n := by
    rw [← hmdegree, degree_sub, degree_ofPoint, hdegree]
    omega
  omega

/-- For effective `A` and any divisor `B`, choose a section of a minimal pole bound for `L(A)`
that has the exact allowed order at every place in the support of `B`, provided the constant field
has more than `#supp B + 1` elements. -/
private theorem exists_section_exact_on_support (hF : IsFunctionField k F)
    {A B : Divisor k F} (hA : 0 ≤ A) (hcard : (B.support.card + 1 : ℕ∞) < ENat.card k) :
    ∃ (D : Divisor k F) (z : F), D ≤ A ∧ riemannRochSpace D = riemannRochSpace A ∧
      z ∈ riemannRochSpace D ∧ z ≠ 0 ∧ ∀ P ∈ B.support, P.ord z = -D.coeff P := by
  classical
  obtain ⟨D, hDA, hspace, hminimal⟩ := exists_minimal_riemannRochSpace hF hA
  let U : Option ↑B.support → Submodule k (riemannRochSpace D)
    | none => ⊥
    | some P =>
      (riemannRochSpace (D - WeilDivisor.ofPoint P.1)).submoduleOf (riemannRochSpace D)
  have hU : ∀ P, U P ≠ ⊤ := by
    rintro (_ | P)
    · simp only [U]
      intro hbot
      have hone := one_mem_riemannRochSpace_iff.mpr hA
      rw [← hspace] at hone
      have honebot : (⟨1, hone⟩ : riemannRochSpace D) ∈
          (⊥ : Submodule k (riemannRochSpace D)) := by
        rw [hbot]
        exact Submodule.mem_top
      have hzero : (⟨1, hone⟩ : riemannRochSpace D) = 0 := by
        simp at honebot
      exact one_ne_zero (congrArg Subtype.val hzero)
    · simp only [U]
      intro htop
      exact (hminimal P.1).ne (le_antisymm (hminimal P.1).le
        (Submodule.submoduleOf_eq_top.mp htop))
  obtain ⟨z, hzU⟩ : ∃ z, ∀ P, z ∉ U P := by
    simpa [Set.ssubset_univ_iff, Set.iUnion_eq_univ_iff] using
      Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt Finset.univ U hU (by simpa using hcard)
  have hz0 : (z : F) ≠ 0 := by
    intro hz0
    apply hzU none
    simpa only [U, Submodule.mem_bot] using Subtype.ext hz0
  refine ⟨D, z, hDA, hspace, z.2, hz0, fun P hP ↦ ?_⟩
  apply ord_eq_neg_coeff_of_not_mem_sub_ofPoint z.2
  intro hmem
  apply hzU (some ⟨P, hP⟩)
  simpa only [U, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] using hmem

/-- Stichtenoth's dimension inequality for effective divisors, when the constant field has more
than `deg B + 1` elements.  The general form follows by replacing both divisors by effective
representatives. -/
private theorem dim_add_le_one_add_dim_add_of_effective (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {A B : Divisor k F} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcard : ((degree B).toNat + 1 : ℕ∞) < ENat.card k) :
    dim A + dim B ≤ 1 + dim (A + B) := by
  classical
  have hsupport : (B.support.card + 1 : ℕ∞) < ENat.card k := by
    refine lt_of_le_of_lt ?_ hcard
    have hle : B.support.card ≤ (degree B).toNat := by
      have := card_support_le_degree hF hB
      omega
    gcongr
  obtain ⟨D, z, hDA, hspace, hzD, hz0, hzord⟩ := exists_section_exact_on_support hF hA hsupport
  have hAle : riemannRochSpace A ≤ riemannRochSpace (A + B) :=
    riemannRochSpace_mono (le_add_of_nonneg_right hB)
  let LA : Submodule k (riemannRochSpace (A + B)) :=
    (riemannRochSpace A).submoduleOf (riemannRochSpace (A + B))
  have hDB : D + B ≤ A + B := by
    simpa only [add_comm] using add_le_add_right hDA B
  let mulZ : riemannRochSpace B →ₗ[k] riemannRochSpace (A + B) :=
    { toFun := fun x ↦ ⟨z * x, by
          have hprod : (z : F) * (x : F) ∈ riemannRochSpace (D + B) :=
            mul_mem_riemannRochSpace_add (A := D) (B := B) hzD x.2
          exact riemannRochSpace_mono hDB hprod⟩
      map_add' := fun x y ↦ by
        ext
        simp only [Submodule.coe_add, mul_add]
      map_smul' := fun c x ↦ by
        ext
        simp only [Submodule.coe_smul_of_tower, RingHom.id_apply, Algebra.smul_def]
        ring }
  let T : riemannRochSpace B →ₗ[k] (riemannRochSpace (A + B) ⧸ LA) :=
    LA.mkQ.comp mulZ
  have honeB : (1 : F) ∈ riemannRochSpace B :=
    one_mem_riemannRochSpace_iff.mpr hB
  let oneB : riemannRochSpace B := ⟨1, honeB⟩
  have hzA : z ∈ riemannRochSpace A := by rwa [← hspace]
  -- The kernel consists exactly of the constant sections of `L(B)`.  At a pole of a
  -- nonconstant section, the chosen exact order of `z` prevents the product from lying in
  -- `L(D) = L(A)`.
  have hker : T.ker = k ∙ oneB := by
    apply le_antisymm
    · intro x hx
      have hxzero : T x = 0 := LinearMap.mem_ker.mp hx
      have hxprodA : (z : F) * (x : F) ∈ riemannRochSpace A := by
        have hxLA : mulZ x ∈ LA := by
          apply (Submodule.Quotient.mk_eq_zero LA).mp
          simpa only [T, LinearMap.comp_apply, Submodule.mkQ_apply] using hxzero
        simpa only [LA, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, mulZ,
          LinearMap.coe_mk, AddHom.coe_mk] using hxLA
      have hxalg : (x : F) ∈ algebraicClosure k F := by
        apply (Place.mem_algebraicClosure_iff_forall_mem_integers hF).mpr
        intro P
        rw [P.mem_integers_iff_ord_nonneg]
        rcases eq_or_ne (x : F) 0 with hx0 | hx0
        · simp [hx0]
        by_cases hPB : P ∈ B.support
        · have hxprodD : (z : F) * (x : F) ∈ riemannRochSpace D := by
            rwa [hspace]
          have hbound := (mem_riemannRochSpace_iff_neg_le_ord (mul_ne_zero hz0 hx0)).mp
            hxprodD P
          rw [P.ord_mul hz0 hx0, hzord P hPB] at hbound
          omega
        · have hxbound := (mem_riemannRochSpace_iff_neg_le_ord hx0).mp x.2 P
          have hcoeff : B.coeff P = 0 := by
            simpa only [WeilDivisor.mem_support_iff, not_not] using hPB
          rw [hcoeff] at hxbound
          omega
      obtain ⟨c, hc⟩ := (isIntegrallyClosedIn_iff_forall_isAlgebraic.mp hex) (x : F)
        (_root_.mem_algebraicClosure_iff.mp hxalg)
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      simpa only [oneB, Submodule.coe_smul_of_tower, Algebra.smul_def, mul_one] using hc
    · apply Submodule.span_le.mpr
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      have hmul : mulZ oneB ∈ LA := by
        simp only [LA, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply, mulZ,
          LinearMap.coe_mk, AddHom.coe_mk, oneB, mul_one]
        exact hzA
      simpa only [SetLike.mem_coe, LinearMap.mem_ker, T, LinearMap.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hmul
  have honeB0 : oneB ≠ 0 := by
    intro h
    exact one_ne_zero (congrArg Subtype.val h)
  have hkerfinrank : Module.finrank k T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton honeB0
  let _ := finiteDimensional_riemannRochSpace hF B
  let _ := finiteDimensional_riemannRochSpace hF (A + B)
  -- Rank-nullity for `T`, together with the dimension formula for the target quotient, gives
  -- the desired inequality.
  have hrank := LinearMap.finrank_range_add_finrank_ker T
  have hrange : Module.finrank k T.range ≤
      Module.finrank k (riemannRochSpace (A + B) ⧸ LA) :=
    Submodule.finrank_le T.range
  have hquotRank := rank_quotient_riemannRochSpace_add_dim hF
    (D := A) (E := A + B) (le_add_of_nonneg_right hB)
  have hquot : Module.finrank k (riemannRochSpace (A + B) ⧸ LA) + dim A = dim (A + B) := by
    rw [← Module.finrank_eq_rank] at hquotRank
    exact_mod_cast hquotRank
  rw [hkerfinrank, Nat.add_comm] at hrank
  rw [← dim_def B] at hrank
  omega

/-- **Stichtenoth, Lemma 1.6.14**: if `L(A)` and `L(B)` are nonzero and the exact constant field
has more than `deg B + 1` elements, then

`ℓ(A) + ℓ(B) ≤ 1 + ℓ(A + B)`.

The cardinality hypothesis holds for every infinite constant field. -/
theorem dim_add_dim_le_one_add_dim_add_of_lt_card (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {A B : Divisor k F} (hA : 0 < dim A) (hB : 0 < dim B)
    (hcard : ((degree B).toNat + 1 : ℕ∞) < ENat.card k) :
    dim A + dim B ≤ 1 + dim (A + B) := by
  have hAne : riemannRochSpace A ≠ ⊥ :=
    (one_le_dim_iff_riemannRochSpace_ne_bot hF A).mp hA
  have hBne : riemannRochSpace B ≠ ⊥ :=
    (one_le_dim_iff_riemannRochSpace_ne_bot hF B).mp hB
  obtain ⟨A₀, hA₀, hAA₀⟩ := (riemannRochSpace_ne_bot_iff hF).mp hAne
  obtain ⟨B₀, hB₀, hBB₀⟩ := (riemannRochSpace_ne_bot_iff hF).mp hBne
  have h := dim_add_le_one_add_dim_add_of_effective hF hex hA₀ hB₀
    (by rwa [← degree_eq_of_linearlyEquivalent hF hBB₀])
  have hsum := WeilDivisor.OrderSystem.LinearlyEquivalent.add
    (Place.orderSystem hF) hAA₀ hBB₀
  rw [← dim_eq_of_linearlyEquivalent hF hAA₀,
    ← dim_eq_of_linearlyEquivalent hF hBB₀,
    ← dim_eq_of_linearlyEquivalent hF hsum] at h
  exact h

/-- **Stichtenoth, Lemma 1.6.14, over any exact constant field**: if `L(A)` and `L(B)` are
nonzero, then

`ℓ(A) + ℓ(B) ≤ 1 + ℓ(A + B)`. -/
theorem dim_add_dim_le_one_add_dim_add (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {A B : Divisor k F} (hA : 0 < dim A) (hB : 0 < dim B) :
    dim A + dim B ≤ 1 + dim (A + B) := by
  rcases finite_or_infinite k with hk | hk
  · -- pass to a finite constant field extension with more than `deg B + 1` elements, which
    -- preserves degrees and dimensions and keeps the (perfect) constant field exact
    obtain ⟨F', k', hk', hcard, h⟩ :=
      exists_finiteDimensional_lt_card_constantCompositum_eq_top k F ((degree B).toNat + 1)
    have : FiniteDimensional F F' := finiteDimensional_of_constantCompositum_eq_top (k := k) h
    have : Algebra.IsSeparable k k' := Algebra.IsAlgebraic.isSeparable_of_perfectField
    have : PerfectField k' := Algebra.IsAlgebraic.perfectField k
    have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
    have hex' := isIntegrallyClosedIn_of_constantCompositum_eq_top hex h
    have hdim := dim_add_dim_le_one_add_dim_add_of_lt_card hF' hex'
      (A := conorm k' F' A) (B := conorm k' F' B)
      (by rwa [dim_conorm hex h hF']) (by rwa [dim_conorm hex h hF'])
      (by rw [degree_conorm_of_constantCompositum_eq_top hex h]; exact_mod_cast hcard)
    rwa [← map_add, dim_conorm hex h hF', dim_conorm hex h hF', dim_conorm hex h hF'] at hdim
  · exact dim_add_dim_le_one_add_dim_add_of_lt_card hF hex hA hB (by simp)

/-- **Clifford's theorem** (Stichtenoth, Theorem 1.6.13), over an arbitrary exact field of
constants: a divisor of degree between `0` and `2g - 2` satisfies

`2 * ℓ(D) ≤ deg D + 2`.

The bound includes the nonspecial and empty-linear-system edge cases. -/
theorem two_mul_dim_le_degree_add_two (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) {D : Divisor k F}
    (hDnonneg : 0 ≤ degree D) (hDle : degree D ≤ 2 * (genus k F : ℤ) - 2) :
    2 * (dim D : ℤ) ≤ degree D + 2 := by
  obtain ⟨W, hW⟩ := exists_isRiemannRochDivisor hF hex
  have hRR := Divisor.isRiemannRochDivisor_iff.mp hW D
  rcases eq_or_ne (dim D) 0 with hD0 | hD0
  · rw [hD0]
    omega
  rcases eq_or_ne (dim (W - D)) 0 with hWD0 | hWD0
  · rw [hWD0] at hRR
    omega
  have hdim := dim_add_dim_le_one_add_dim_add hF hex (Nat.pos_of_ne_zero hD0)
    (Nat.pos_of_ne_zero hWD0)
  have hsum : D + (W - D) = W := by abel
  rw [hsum, hW.dim_eq hF hex] at hdim
  omega

end Divisor

end TauCeti
