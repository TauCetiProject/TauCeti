/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AbsoluteValue.Action

import TauCeti.Analysis.AbsoluteValue.Nonarchimedean

/-!
# Decomposition and inertia groups of an absolute value

Let a group `G` act on a ring `L` by ring automorphisms (`MulSemiringAction G L`), and so on the
absolute values of `L` by `(σ • w) x = w (σ⁻¹ • x)` (`AbsoluteValue.instMulAction`). No hypothesis
relates `G` to a fixed field, so everything here applies to an abstract Galois group as well as to
`L ≃ₐ[K] L`.

* The *decomposition group* of `w` is Mathlib's `MulAction.stabilizer G w`; no new definition is
  introduced. Its elements are the `σ` with `w (σ • x) = w x` for all `x`
  (`AbsoluteValue.mem_stabilizer_iff_forall_apply_smul_eq`).
* The *inertia group* `AbsoluteValue.inertia G w` is a `Subgroup G` contained in the decomposition
  group. When `w` is nonarchimedean (a finite place) it consists of the `σ` in the decomposition
  group with `w (σ • x - x) < 1` for every `x` with `w x ≤ 1`, that is, the `σ` that act trivially
  on the residue ring of `w`; when `w` is archimedean (an infinite place) it is the whole
  decomposition group. The second convention is the one under which the inertia group of an
  infinite place of a number field is nontrivial exactly when the place ramifies, as for Mathlib's
  `NumberField.InfinitePlace.IsUnramified`. The membership in the decomposition group is part of
  the definition and is not implied by the congruence: an automorphism can preserve the valuation
  ring of `w` and move `w` to an equivalent absolute value.

The inertia group is normal in the decomposition group
(`AbsoluteValue.instNormalInertiaStabilizer`), and conjugating `w` by `g` conjugates it by `g`
(`AbsoluteValue.inertia_smul`).

There is no Frobenius predicate. For an exponent `q` and a nonarchimedean `w`, an element that
induces `x ↦ x ^ q` on the residue ring of `w` is described by the two hypotheses
`σ ∈ MulAction.stabilizer G w` and `∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1`; for `q = 1` they say
that `σ` lies in the inertia group (`AbsoluteValue.mem_inertia_iff_of_isNonarchimedean`). The
lemmas `AbsoluteValue.forall_apply_smul_sub_pow_lt_one_conj`, `..._mul`, `..._pow` and `..._under`
prove, in this form, that the congruence is carried along by conjugation, that elements for `q` and
`q'` multiply to one for `q * q'`, that powers of an element for `q` are elements for powers of
`q`, that multiplying by an element of the inertia group on either side does not change `q`
(`..._mul_of_mem_inertia_right`, `..._mul_of_mem_inertia_left`), and that the congruence passes to
the restriction of `w` to a subring that `G` maps to itself.

## Main definitions

* `AbsoluteValue.inertia G w`: the inertia group of an absolute value `w`.

## Main results

* `AbsoluteValue.inertia_le_stabilizer`, `AbsoluteValue.inertia_eq_stabilizer`: the inertia group
  lies in the decomposition group, and equals it when `w` is archimedean.
* `AbsoluteValue.inertia_smul`, `AbsoluteValue.instNormalInertiaStabilizer`: conjugation and
  normality.
* `AbsoluteValue.stabilizer_le_stabilizer_under`, `AbsoluteValue.inertia_le_inertia_under`: the
  decomposition and inertia groups of `w` lie in those of its restriction to a `G`-stable subring.
* `AbsoluteValue.stabilizer_trivial`: the trivial absolute value is fixed by the whole group.

The inertia group has the same carrier as `AbsoluteValue.inertiaSubgroup` in Jz Pan's
lean-iwasawa (`acmepjz/lean-iwasawa` at `7fffeb8c80fbe13f989f318c23cbb0dcf2230092`, file
`Iwasawalib/NumberTheory/AbsoluteValue/InertiaSubgroup.lean`, Apache 2.0), which is stated there
for the group `K ≃ₐ[F] K`; here it is stated for any group acting by ring automorphisms.

The statements and proofs of `AbsoluteValue.inertia_smul`, `AbsoluteValue.inertia_le_stabilizer`
and `AbsoluteValue.instNormalInertiaStabilizer` follow Mathlib's `Ideal.inertia_smul`,
`Ideal.inertia_le_stabilizer` and the normality instance for `Ideal.inertia` in
`Mathlib/RingTheory/Ideal/Pointwise.lean` (the normality proof is Mathlib's), and
`AbsoluteValue.subgroupOf_inertia` follows Mathlib's `AddSubgroup.subgroupOf_inertia` in
`Mathlib/Algebra/Group/Subgroup/Basic.lean`.

The design (decomposition and inertia groups defined once for finite and infinite places by
working with absolute values) follows the advice of Thomas Browning and Jz Pan on the Lean Zulip,
https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643780662
and
https://leanprover.zulipchat.com/#narrow/channel/658556-Riemann-Hypothesis/topic/Library.20design.20discrepancies.20between.20RH.2FMathlib.2FTauCeti/near/643806146.
The decomposition group as a stabilizer, the inertia group, and the hypothesis shape
`σ ∈ MulAction.stabilizer G w ∧ ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1` restate, for absolute
values, `New.decompGroup`, `New.inertiaGroup` and `New.IsFrob` of the riemann-hypothesis project
(`leanprover-community/riemann-hypothesis` at `c5451bd3ba92480e05c4218f5221bb2900c58706`, file
`src/Lib/ClassField/Places/GaloisDefs.lean`, Apache 2.0), which are stated there for a valuation
subring of a field acted on by an abstract group; that project's issue
https://github.com/leanprover-community/riemann-hypothesis/issues/6836 proposes this restatement.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Ch. I, §9 and Ch. II, §9.
-/

public section

namespace AbsoluteValue

variable {G L S : Type*} [Group G]

/-! ### The decomposition group -/

section Stabilizer

variable [Semiring L] [MulSemiringAction G L] [Semiring S] [PartialOrder S]
  {w : AbsoluteValue L S}

/-- An element of the decomposition group of `w` preserves the values of `w`. -/
theorem apply_smul_of_mem_stabilizer {σ : G} (hσ : σ ∈ MulAction.stabilizer G w) (x : L) :
    w (σ • x) = w x := by
  conv_lhs => rw [← MulAction.mem_stabilizer_iff.mp hσ]
  rw [smul_apply, inv_smul_smul]

/-- The decomposition group of `w` consists of the elements that preserve the values of `w`. -/
theorem mem_stabilizer_iff_forall_apply_smul_eq {σ : G} :
    σ ∈ MulAction.stabilizer G w ↔ ∀ x, w (σ • x) = w x := by
  refine ⟨apply_smul_of_mem_stabilizer, fun h ↦ ext fun x ↦ ?_⟩
  rw [smul_apply, ← h, smul_inv_smul]

/-- Every element of `G` fixes the trivial absolute value. -/
@[simp]
theorem stabilizer_trivial [IsOrderedRing S] [Nontrivial S] [DecidablePred fun x : L ↦ x = 0]
    [NoZeroDivisors L] :
    MulAction.stabilizer G (AbsoluteValue.trivial : AbsoluteValue L S) = ⊤ := by
  refine eq_top_iff.mpr fun σ _ ↦ ?_
  refine MulAction.mem_stabilizer_iff.mpr (ext fun x ↦ ?_)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [smul_apply, trivial_apply hx, trivial_apply ((smul_ne_zero_iff_ne σ⁻¹).mpr hx)]

end Stabilizer

/-! ### The inertia group -/

section Inertia

variable [Ring L] [MulSemiringAction G L] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  {w : AbsoluteValue L S}

/-- If `σ` in the decomposition group of a nonarchimedean `w` induces `x ↦ x ^ q` on the residue
ring and `τ` induces `x ↦ x ^ q'`, then `σ * τ` induces `x ↦ x ^ (q * q')`. -/
theorem forall_apply_smul_sub_pow_lt_one_mul (hw : IsNonarchimedean w) {σ τ : G} {q q' : ℕ}
    (hσ : σ ∈ MulAction.stabilizer G w) (hσq : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1)
    (hτq' : ∀ x, w x ≤ 1 → w (τ • x - x ^ q') < 1) :
    ∀ x, w x ≤ 1 → w ((σ * τ) • x - x ^ (q * q')) < 1 := by
  intro x hx
  have hxq' : w (x ^ q') ≤ 1 := by
    rcases subsingleton_or_nontrivial L with _ | _
    · simp [Subsingleton.elim (x ^ q') 0]
    · rw [w.map_pow]
      exact pow_le_one₀ (w.nonneg x) hx
  calc w ((σ * τ) • x - x ^ (q * q'))
        = w (σ • (τ • x - x ^ q') + (σ • x ^ q' - (x ^ q') ^ q)) := by
          rw [mul_smul, smul_sub, ← pow_mul', sub_add_sub_cancel]
    _ ≤ max (w (σ • (τ • x - x ^ q'))) (w (σ • x ^ q' - (x ^ q') ^ q)) := hw _ _
    _ < 1 := by
          rw [apply_smul_of_mem_stabilizer hσ]
          exact max_lt (hτq' x hx) (hσq _ hxq')

variable (G) in
/-- The *inertia group* of an absolute value `w` on `L`: the elements `σ` of the decomposition
group `MulAction.stabilizer G w` such that, if `w` is nonarchimedean, `w (σ • x - x) < 1` for every
`x` with `w x ≤ 1`. For an archimedean `w` it is the whole decomposition group. -/
def inertia (w : AbsoluteValue L S) : Subgroup G where
  carrier := {σ | σ • w = w ∧ (IsNonarchimedean w → ∀ x, w x ≤ 1 → w (σ • x - x) < 1)}
  one_mem' := ⟨one_smul G w, fun _ _ _ ↦ by simp⟩
  mul_mem' {a b} ha hb := by
    refine ⟨by rw [mul_smul, hb.1, ha.1], fun hw ↦ ?_⟩
    simpa only [pow_one, mul_one] using forall_apply_smul_sub_pow_lt_one_mul (q := 1) (q' := 1) hw
      ha.1 (by simpa only [pow_one] using ha.2 hw) (by simpa only [pow_one] using hb.2 hw)
  inv_mem' {a} ha := by
    refine ⟨inv_smul_eq_iff.mpr ha.1.symm, fun hw x hx ↦ ?_⟩
    rw [← apply_smul_of_mem_stabilizer (MulAction.mem_stabilizer_iff.mpr ha.1), smul_sub,
      smul_inv_smul, ← AbsoluteValue.map_neg, neg_sub]
    exact ha.2 hw x hx

theorem mem_inertia_iff {σ : G} :
    σ ∈ w.inertia G ↔
      σ • w = w ∧ (IsNonarchimedean w → ∀ x, w x ≤ 1 → w (σ • x - x) < 1) :=
  .rfl

/-- The inertia group lies in the decomposition group. -/
theorem inertia_le_stabilizer : w.inertia G ≤ MulAction.stabilizer G w :=
  fun _ hσ ↦ hσ.1

/-- At a nonarchimedean absolute value, the inertia group consists of the elements of the
decomposition group that act trivially modulo `{x | w x < 1}` on `{x | w x ≤ 1}`. -/
theorem mem_inertia_iff_of_isNonarchimedean (hw : IsNonarchimedean w) {σ : G} :
    σ ∈ w.inertia G ↔
      σ ∈ MulAction.stabilizer G w ∧ ∀ x, w x ≤ 1 → w (σ • x - x) < 1 :=
  and_congr_right' ⟨fun h ↦ h hw, fun h _ ↦ h⟩

/-- At an archimedean absolute value, the inertia group is the decomposition group. -/
theorem inertia_eq_stabilizer (hw : ¬ IsNonarchimedean w) :
    w.inertia G = MulAction.stabilizer G w :=
  le_antisymm inertia_le_stabilizer fun _ hσ ↦ ⟨hσ, fun h ↦ absurd h hw⟩

/-- The inertia group of `g • w` is the conjugate by `g` of the inertia group of `w`. -/
theorem mem_inertia_smul_iff {g σ : G} :
    σ ∈ (g • w).inertia G ↔ g⁻¹ * σ * g ∈ w.inertia G := by
  simp only [mem_inertia_iff, isNonarchimedean_smul_iff, smul_apply, mul_smul, inv_smul_eq_iff]
  refine and_congr_right' (imp_congr_right fun _ ↦ ?_)
  rw [← (MulAction.toPerm g).forall_congr_right]
  simp [smul_sub]

/-- The inertia group of `g • w` is the conjugate by `g` of the inertia group of `w`. -/
theorem inertia_smul (g : G) (w : AbsoluteValue L S) :
    (g • w).inertia G = (w.inertia G).map (MulAut.conj g) := by
  ext σ
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, MonoidHom.coe_ofClass,
    MulAut.conj_symm_apply, mem_inertia_smul_iff]

/-- The inertia group of `w` for the action of a subgroup `H` is the inertia group for the action
of `G`, intersected with `H`. -/
@[simp]
theorem subgroupOf_inertia (H : Subgroup G) : (w.inertia G).subgroupOf H = w.inertia H := by
  ext
  exact .rfl

/-- The inertia group is a normal subgroup of the decomposition group. -/
instance instNormalInertiaStabilizer : (w.inertia (MulAction.stabilizer G w)).Normal := by
  simp_rw [Subgroup.normal_iff_map_conj_eq, ← inertia_smul]
  exact fun g ↦ congrArg (inertia _) g.property

end Inertia

/-! ### Elements inducing a power map on the residue ring -/

section Conj

variable [Ring L] [MulSemiringAction G L] [Semiring S] [PartialOrder S] {w : AbsoluteValue L S}

/-- If `σ` satisfies `w (σ • x - x ^ q) < 1` whenever `w x ≤ 1`, then its conjugate `g σ g⁻¹`
satisfies the same congruences for `g • w`. -/
theorem forall_apply_smul_sub_pow_lt_one_conj {σ : G} {q : ℕ}
    (h : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1) (g : G) :
    ∀ x, (g • w) x ≤ 1 → (g • w) ((g * σ * g⁻¹) • x - x ^ q) < 1 := by
  intro x hx
  rw [smul_apply] at hx ⊢
  simpa [mul_smul, smul_sub, smul_pow'] using h (g⁻¹ • x) hx

end Conj

section Inertia

variable [Ring L] [MulSemiringAction G L] [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
  {w : AbsoluteValue L S}

/-- If `σ` in the decomposition group of a nonarchimedean `w` induces `x ↦ x ^ q` on the residue
ring, then `σ ^ n` induces `x ↦ x ^ (q ^ n)`. -/
theorem forall_apply_smul_sub_pow_lt_one_pow (hw : IsNonarchimedean w) {σ : G} {q : ℕ}
    (hσ : σ ∈ MulAction.stabilizer G w) (hσq : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1) (n : ℕ) :
    ∀ x, w x ≤ 1 → w ((σ ^ n) • x - x ^ (q ^ n)) < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ']
    exact forall_apply_smul_sub_pow_lt_one_mul hw hσ hσq ih

/-- An element of the inertia group of a nonarchimedean `w` induces `x ↦ x ^ 1` on the residue
ring. -/
theorem forall_apply_smul_sub_pow_one_lt_one_of_mem_inertia (hw : IsNonarchimedean w) {σ : G}
    (hσ : σ ∈ w.inertia G) : ∀ x, w x ≤ 1 → w (σ • x - x ^ 1) < 1 := by
  simpa only [pow_one] using ((mem_inertia_iff_of_isNonarchimedean hw).mp hσ).2

/-- If `σ` in the decomposition group of a nonarchimedean `w` induces `x ↦ x ^ q` on the residue
ring, then so does `σ * τ` for every `τ` in the inertia group. -/
theorem forall_apply_smul_sub_pow_lt_one_mul_of_mem_inertia_right (hw : IsNonarchimedean w)
    {σ τ : G} {q : ℕ} (hσ : σ ∈ MulAction.stabilizer G w)
    (hσq : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1) (hτ : τ ∈ w.inertia G) :
    ∀ x, w x ≤ 1 → w ((σ * τ) • x - x ^ q) < 1 := by
  simpa only [mul_one] using forall_apply_smul_sub_pow_lt_one_mul hw hσ hσq
    (forall_apply_smul_sub_pow_one_lt_one_of_mem_inertia hw hτ)

/-- If `σ` induces `x ↦ x ^ q` on the residue ring of a nonarchimedean `w`, then so does `τ * σ`
for every `τ` in the inertia group. -/
theorem forall_apply_smul_sub_pow_lt_one_mul_of_mem_inertia_left (hw : IsNonarchimedean w)
    {σ τ : G} {q : ℕ} (hσq : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1) (hτ : τ ∈ w.inertia G) :
    ∀ x, w x ≤ 1 → w ((τ * σ) • x - x ^ q) < 1 := by
  simpa only [one_mul] using forall_apply_smul_sub_pow_lt_one_mul hw (inertia_le_stabilizer hτ)
    (forall_apply_smul_sub_pow_one_lt_one_of_mem_inertia hw hτ) hσq

end Inertia

/-! ### Restriction to a stable subring -/

section under

variable {M : Type*}

/-- The decomposition group of `w` lies in the decomposition group of its restriction to a
`G`-stable subring. -/
theorem stabilizer_le_stabilizer_under [CommSemiring M] [MulSemiringAction G M] [Semiring L]
    [MulSemiringAction G L] [Algebra M L] [FaithfulSMul M L] [SMulDistribClass G M L] [Semiring S]
    [PartialOrder S] {w : AbsoluteValue L S} :
    MulAction.stabilizer G w ≤ MulAction.stabilizer G (w.under M) := fun σ hσ ↦ by
  rw [MulAction.mem_stabilizer_iff, smul_under, MulAction.mem_stabilizer_iff.mp hσ]

/-- If `σ` satisfies `w (σ • x - x ^ q) < 1` whenever `w x ≤ 1`, then it satisfies the same
congruences for the restriction of `w` to a `G`-stable subring. -/
theorem forall_apply_smul_sub_pow_lt_one_under [CommRing M] [MulSemiringAction G M] [Ring L]
    [MulSemiringAction G L] [Algebra M L] [FaithfulSMul M L] [SMulDistribClass G M L] [Semiring S]
    [PartialOrder S] {w : AbsoluteValue L S} {σ : G} {q : ℕ}
    (h : ∀ x, w x ≤ 1 → w (σ • x - x ^ q) < 1) :
    ∀ m : M, w.under M m ≤ 1 → w.under M (σ • m - m ^ q) < 1 := fun m hm ↦ by
  rw [under_apply, map_sub, map_pow, algebraMap.smul'] at *
  exact h _ hm

/-- The inertia group of a real absolute value `w` on a field lies in the inertia group of its
restriction to a `G`-stable subring. -/
theorem inertia_le_inertia_under [CommRing M] [MulSemiringAction G M] {K : Type*} [Field K]
    [MulSemiringAction G K] [Algebra M K] [FaithfulSMul M K] [SMulDistribClass G M K]
    {w : AbsoluteValue K ℝ} :
    w.inertia G ≤ (w.under M).inertia G := fun σ hσ ↦ by
  refine ⟨MulAction.mem_stabilizer_iff.mp (stabilizer_le_stabilizer_under hσ.1), fun hw ↦ ?_⟩
  have hw' : IsNonarchimedean w := (isNonarchimedean_iff_of_liesOver w (w.under M)).mpr hw
  simpa only [pow_one] using forall_apply_smul_sub_pow_lt_one_under (q := 1)
    (by simpa only [pow_one] using hσ.2 hw')

end under

end AbsoluteValue
