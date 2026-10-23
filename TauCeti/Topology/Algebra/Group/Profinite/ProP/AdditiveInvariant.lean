/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Filtration
public import TauCeti.Topology.Algebra.GroupAction.AdditiveInvariant
public import TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup

/-!
# Additive invariants of finite primary modules

An invariant of finite discrete `p`-primary `G`-modules with values in a left-cancellative
additive monoid that is additive on short exact sequences is determined, for pro-`p` groups,
by its value on the trivial module of order `p`. The coefficient group need not be killed
by `p`, and the value monoid need not be commutative or carry a topology.

The trivial module is supplied in the same universe as the coefficient groups, together with
an additive equivalence to `ZMod p`. In particular, it can be `ULift (ZMod p)`.

## Main results

* `TauCeti.invariant_eq_padicValNat_nsmul_of_isProP`: for a pro-`p` group, an additive invariant
  of a finite `p`-primary module is the natural multiple `padicValNat p (Nat.card M)` of its
  value on the trivial module of order `p`. This applies to natural-number-valued lengths
  and integer-valued Euler characteristics.
-/

public section

universe u v w

namespace TauCeti

variable {p : ℕ} {G : Type v} [Group G] [TopologicalSpace G]
  {R : Type w} [AddLeftCancelMonoid R]

variable
  (I : ∀ (A : Type u) [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction G A] [ContinuousSMul G A] [Finite A],
    (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → R)
  (hExact : ∀ {A B C : Type u}
    [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
    [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
    [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
    (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0)
    (hB : ∀ b : B, ∃ k : ℕ, p ^ k • b = 0)
    (hC : ∀ c : C, ∃ k : ℕ, p ^ k • c = 0)
    (f : A →+ B) (q : B →+ C),
    (∀ (g : G) (a : A), f (g • a) = g • f a) →
    (∀ (g : G) (b : B), q (g • b) = g • q b) →
    Function.Injective f → Function.Surjective q →
    f.range = q.ker → I B hB = I A hA + I C hC)

variable [Fact p.Prime]
  {M P : Type u}
  [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P] [DistribMulAction G P]

include hExact in
/-- An invariant with values in a left-cancellative additive monoid that is additive on
equivariant short exact sequences of finite discrete `p`-primary modules is the natural
multiple of its value on a trivial module of order `p` by the `p`-adic valuation of the
cardinality. The trivial model `P` lies in the same universe as `M`; it is finite and `p`-primary
because it is additively equivalent to `ZMod p`, and its trivial action is continuous, so neither
is assumed. No exponent-`p` assumption on `M` is needed. -/
theorem invariant_eq_padicValNat_nsmul_of_isProP
    (hG : IsProP p G)
    (hM : ∀ m : M, ∃ k : ℕ, p ^ k • m = 0)
    (eP : P ≃+ ZMod p)
    (hPsmul : ∀ (g : G) (x : P), g • x = x) :
    haveI : Finite P := Finite.of_equiv _ eP.symm.toEquiv
    haveI : ContinuousSMul G P := ⟨continuous_snd.congr fun z ↦ (hPsmul z.1 z.2).symm⟩
    I M hM = padicValNat p (Nat.card M) •
      I P (forall_exists_nsmul_eq_zero_of_addEquiv_zmod eP) := by
  have _ : Finite P := Finite.of_equiv _ eP.symm.toEquiv
  have _ : ContinuousSMul G P := ⟨continuous_snd.congr fun z ↦ (hPsmul z.1 z.2).symm⟩
  have hP := forall_exists_nsmul_eq_zero_of_addEquiv_zmod eP
  obtain ⟨N, hN, h0, hmono, htop, _, hfactors⟩ :=
    exists_filtration_with_trivial_factors_of_isProP hG hM
  let _ (i : ℕ) := (N i).restrictDistribMulAction (hN i)
  let _ (i : ℕ) := (N i).restrictDistribMulAction_continuousSMul (hN i)
  have hprim := fun i ↦ (N i).forall_exists_nsmul_eq_zero hM
  let _ : Subsingleton (N 0) := by rw [h0]; infer_instance
  have hzero := invariant_eq_zero_of_subsingleton I hExact (hprim 0)
  -- Each successive factor contributes the same value `I P hP`.
  have hind : ∀ i, i ≤ padicValNat p (Nat.card M) →
      I (N i) (hprim i) = i • I P hP := by
    intro i
    induction i with
    | zero =>
      intro _
      simpa only [zero_nsmul] using hzero
    | succ i ih =>
      intro hi
      have hi' : i < padicValNat p (Nat.card M) :=
        Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
      have hprev := ih (Nat.le_trans (Nat.le_succ i) hi)
      let Q := N (i + 1) ⧸ (N i).addSubgroupOf (N (i + 1))
      let _ : DistribMulAction G Q :=
        (N i).subquotientDistribMulAction (N (i + 1)) (hN i) (hN (i + 1))
      obtain ⟨⟨eQ⟩, htriv⟩ := hfactors i hi'
      let _ : TopologicalSpace Q := ⊥
      let _ : DiscreteTopology Q := ⟨rfl⟩
      let _ : ContinuousSMul G Q :=
        ⟨by simpa only [htriv] using (continuous_snd : Continuous fun z : G × Q ↦ z.2)⟩
      let e : Q ≃+ P := eQ.trans eP.symm
      have hQ := forall_exists_nsmul_eq_zero_of_addEquiv_zmod eQ
      have heq : I Q hQ = I P hP :=
        invariant_eq_of_equiv I hExact hQ hP e
          (by intro g y; rw [htriv, hPsmul])
      have hstep := hExact (hprim i) (hprim (i + 1)) hQ
        (AddSubgroup.inclusion (hmono (Nat.le_succ i)))
        (QuotientAddGroup.mk' ((N i).addSubgroupOf (N (i + 1))))
        (AddSubgroup.restrictDistribMulAction_inclusion_smul (hN i) (hN (i + 1)) _)
        (fun g x ↦ (AddSubgroup.quotientDistribMulAction_smul_mk _ _ g x).symm)
        (AddSubgroup.inclusion_injective _) (QuotientAddGroup.mk'_surjective _)
        (by rw [AddSubgroup.inclusion_range, QuotientAddGroup.ker_mk'])
      rw [hprev, heq] at hstep
      simpa only [succ_nsmul] using hstep
  -- The top term is equivariantly isomorphic to `M`.
  let eTop : N (padicValNat p (Nat.card M)) ≃+ M :=
    (AddEquiv.addSubgroupCongr (htop _ le_rfl)).trans AddSubgroup.topEquiv
  have htopEq := invariant_eq_of_equiv I hExact (hprim _) hM eTop (by
    intro g x
    simp only [eTop, AddEquiv.trans_apply, AddSubgroup.topEquiv_apply,
      AddEquiv.addSubgroupCongr_apply, AddSubgroup.restrictDistribMulAction_coe_smul])
  exact htopEq.symm.trans (hind _ le_rfl)

end TauCeti
