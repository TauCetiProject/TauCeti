/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic
public import TauCeti.Topology.Algebra.Group.Subgroup
public import TauCeti.Topology.Algebra.Group.Profinite.Limit
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
import Mathlib.Topology.Separation.Connected

/-!
# Exponentiation of a pro-`p` group by the `p`-adic integers

In a pro-`p` group every finite quotient is killed by a power of `p`, so the integer powers of
an element `a` only depend on the exponent modulo a power of `p` in each finite quotient. The
`p`-adic integers are the inverse limit of those exponent rings, and `hA.padicPow a l` is the
resulting power `a ^ l` for `l : ℤ_[p]`: it is the unique element whose class modulo an open
normal subgroup `U` is `a ^ l.appr n`, for any `n` with `p ^ n` killing the quotient by `U`.

The construction is the limit description of a profinite group applied to the compatible family
of truncated powers, so it needs no completeness or uniform-space input. It extends the integer
powers, is jointly continuous, and turns `ℤ_[p]` into a ring of exponents: it is additive and
multiplicative in the exponent, and it is the unique continuous extension of `k ↦ a ^ k` along
`ℕ ⊆ ℤ_[p]`.

For an abelian pro-`p` group this action makes the group a `ℤ_[p]`-module,
`TauCeti.IsProP.module`, which is the form in which the structure theory of finitely generated
abelian pro-`p` groups is stated.

## Main definitions

* `TauCeti.IsProP.padicPow`: the power `a ^ l` of an element of a pro-`p` group by a `p`-adic
  integer.
* `TauCeti.IsProP.module`: the `ℤ_[p]`-module structure on an abelian pro-`p` group.
* `TauCeti.IsProP.padicPowHomeomorph`: for a unit `u` of `ℤ_[p]`, the power `a ↦ a ^ u` as a
  homeomorphism of the group, with inverse `a ↦ a ^ u⁻¹`.

## Main results

* `TauCeti.IsProP.mk_padicPow`: the defining description of the power in each finite quotient.
* `TauCeti.IsProP.padicPow_natCast`, `TauCeti.IsProP.padicPow_ofNat`,
  `TauCeti.IsProP.padicPow_intCast`: the power extends the natural and integer powers.
* `TauCeti.IsProP.padicPow_add`, `TauCeti.IsProP.padicPow_mul`: the exponent laws; and
  `TauCeti.IsProP.inv_padicPow`, `TauCeti.IsProP.mul_padicPow` in the base, the latter for
  commuting elements.
* `TauCeti.IsProP.continuous_padicPow`: the action `ℤ_[p] × A → A` is jointly continuous.
* `TauCeti.IsProP.eq_padicPow_of_continuous`, `TauCeti.IsProP.map_padicPow`: the power is the
  unique continuous extension of the natural powers, and continuous homomorphisms preserve it.
* `TauCeti.IsProP.padicPow_mem`: a closed subgroup containing `a` contains its `p`-adic powers;
  `TauCeti.IsProP.map_padicPow_eq_one_of_eq_one`: a continuous homomorphism into a `T1` monoid
  trivial on `a` is trivial on its `p`-adic powers.
* `TauCeti.IsProP.eq_zero_of_padicPow_mem`: a closed subgroup containing no `p`-power `a ^ (p ^ k)`
  contains the `p`-adic power `a ^ l` only for `l = 0`.
* `TauCeti.IsProP.conj_padicPow`: the power commutes with conjugation;
  `TauCeti.IsProP.commute_padicPow`: powers of commuting elements commute.
* `TauCeti.IsProP.padicPow_padicPow_inv`, `TauCeti.IsProP.padicPow_left_inj`,
  `TauCeti.IsProP.closedZpowers_padicPow`: a unit exponent `u` is undone by `u⁻¹`, its power map
  is injective, and `a ^ u` generates the same closed subgroup as `a`.
* `TauCeti.IsProP.mk_padicPow_quotient`, `TauCeti.IsProP.ofMul_mk_padicPow_quotient`: modulo a
  closed normal subgroup the power is the power of the class, and it is the scalar action of
  `ℤ_[p]` when the quotient is abelian.
* `TauCeti.IsProP.padicPow_ofAdd_apply_one`: along a continuous additive homomorphism
  `g : ℤ_[p] →+ X`, the `p`-adic power of `ofAdd (g 1)` in `Multiplicative X` is `ofAdd ∘ g`.
* `TauCeti.IsProP.module_smul`, `TauCeti.IsProP.continuousSMul_module`: the module structure
  acts by the `p`-adic power, and is topological.
* `TauCeti.IsProP.smul_padicPow`, `TauCeti.IsProP.smulCommClass_module`: continuous actions
  by group endomorphisms commute with `p`-adic powers and the resulting scalar action.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 4.3.
-/

public section

namespace TauCeti

universe u v

namespace IsProP

section Group

variable {p : ℕ} [hp : Fact p.Prime] {A : Type u} [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A]

/-- The truncation level at which the `p`-adic power is computed in the quotient by `U`. -/
private noncomputable def padicPowIdx (hA : IsProP p A) (U : OpenNormalSubgroup A) : ℕ :=
  (hA.exists_forall_pow_pow_eq_one U).choose

omit hp in
private theorem pow_pow_padicPowIdx_eq_one (hA : IsProP p A) (U : OpenNormalSubgroup A)
    (g : A ⧸ U.toSubgroup) : g ^ p ^ hA.padicPowIdx U = 1 :=
  (hA.exists_forall_pow_pow_eq_one U).choose_spec g

/-- The family of truncated powers of `a`, one in each finite quotient. -/
private noncomputable def padicPowFamily (hA : IsProP p A) (a : A) (l : ℤ_[p])
    (U : OpenNormalSubgroup A) : A ⧸ U.toSubgroup :=
  (a : A ⧸ U.toSubgroup) ^ l.appr (hA.padicPowIdx U)

private theorem padicPow_compat (hA : IsProP p A) (a : A) (l : ℤ_[p]) :
    ∀ (U V : OpenNormalSubgroup A) (_hle : (U : Subgroup A) ≤ V) (g : A),
      QuotientGroup.mk' (U : Subgroup A) g = hA.padicPowFamily a l U →
        QuotientGroup.mk' (V : Subgroup A) g = hA.padicPowFamily a l V := by
  intro U V hUV g hg
  rw [QuotientGroup.mk'_apply, padicPowFamily] at hg ⊢
  -- The class of `g` modulo `V` is the truncation of `a` at the level chosen for `U`.
  have hpush : (g : A ⧸ V.toSubgroup) = (a : A ⧸ V.toSubgroup) ^ l.appr (hA.padicPowIdx U) := by
    have h := congrArg (QuotientGroup.mapOfLE hUV) hg
    rwa [QuotientGroup.mapOfLE_mk, map_pow, QuotientGroup.mapOfLE_mk] at h
  -- That level also kills the quotient by `V`, because `A ⧸ V` is a quotient of `A ⧸ U`.
  have hkill : ∀ h : A ⧸ V.toSubgroup, h ^ p ^ hA.padicPowIdx U = 1 := by
    intro h
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective h
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    refine hUV ?_
    have hb := hA.pow_pow_padicPowIdx_eq_one U (b : A ⧸ U.toSubgroup)
    rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hb
  set m := max (hA.padicPowIdx U) (hA.padicPowIdx V)
  rw [hpush]
  refine (PadicInt.pow_appr_eq_pow_appr (n := m) l (hkill _) (le_max_left _ _)).symm.trans ?_
  exact PadicInt.pow_appr_eq_pow_appr (n := m) l
    (hA.pow_pow_padicPowIdx_eq_one V _) (le_max_right _ _)

variable [TotallyDisconnectedSpace A]

/-- **The `p`-adic power of an element of a pro-`p` group.** For `l : ℤ_[p]` the element
`hA.padicPow a l` is the unique element of `A` whose class in each finite quotient is the
corresponding truncated power of the class of `a`; see `TauCeti.IsProP.mk_padicPow`. -/
noncomputable def padicPow (hA : IsProP p A) (a : A) (l : ℤ_[p]) : A :=
  (existsUnique_forall_mk_eq (hA.padicPowFamily a l) (hA.padicPow_compat a l)).choose

private theorem mk_padicPow_padicPowIdx (hA : IsProP p A) (a : A) (l : ℤ_[p])
    (U : OpenNormalSubgroup A) :
    ((hA.padicPow a l : A) : A ⧸ U.toSubgroup)
      = (a : A ⧸ U.toSubgroup) ^ l.appr (hA.padicPowIdx U) :=
  (existsUnique_forall_mk_eq (hA.padicPowFamily a l) (hA.padicPow_compat a l)).choose_spec.1 U

/-- **The defining description of the `p`-adic power.** In the quotient by an open normal
subgroup where the image of `a` is killed by `p ^ n`, the `p`-adic power of `a` by `l` is the
ordinary power of `a` by the truncation `l.appr n`. -/
theorem mk_padicPow (hA : IsProP p A) (a : A) (l : ℤ_[p]) {U : OpenNormalSubgroup A} {n : ℕ}
    (hn : (a : A ⧸ U.toSubgroup) ^ p ^ n = 1) :
    ((hA.padicPow a l : A) : A ⧸ U.toSubgroup) = (a : A ⧸ U.toSubgroup) ^ l.appr n := by
  rw [hA.mk_padicPow_padicPowIdx a l U]
  refine (PadicInt.pow_appr_eq_pow_appr (n := max (hA.padicPowIdx U) n) l
    (hA.pow_pow_padicPowIdx_eq_one U _) (le_max_left _ _)).symm.trans ?_
  exact PadicInt.pow_appr_eq_pow_appr (n := max (hA.padicPowIdx U) n) l hn
    (le_max_right _ _)

/-- The `p`-adic power extends the natural-number powers. -/
@[simp]
theorem padicPow_natCast (hA : IsProP p A) (a : A) (k : ℕ) :
    hA.padicPow a (k : ℤ_[p]) = a ^ k := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [hA.mk_padicPow a _ (hn _), QuotientGroup.mk_pow]
  exact pow_eq_pow_of_modEq (PadicInt.appr_natCast_modEq k n) (hn _)

/-- The `p`-adic power by a numeral is the corresponding natural power. -/
@[simp]
theorem padicPow_ofNat (hA : IsProP p A) (a : A) (n : ℕ) [n.AtLeastTwo] :
    hA.padicPow a ofNat(n) = a ^ OfNat.ofNat n := by
  simpa using hA.padicPow_natCast a (OfNat.ofNat n)

/-- The `p`-adic power by `0` is trivial. -/
@[simp]
theorem padicPow_zero (hA : IsProP p A) (a : A) : hA.padicPow a 0 = 1 := by
  simpa using hA.padicPow_natCast a 0

/-- The `p`-adic power by `1` is the element itself. -/
@[simp]
theorem padicPow_one (hA : IsProP p A) (a : A) : hA.padicPow a 1 = a := by
  simpa using hA.padicPow_natCast a 1

/-- The `p`-adic power is additive in the exponent. -/
@[simp]
theorem padicPow_add (hA : IsProP p A) (a : A) (l l' : ℤ_[p]) :
    hA.padicPow a (l + l') = hA.padicPow a l * hA.padicPow a l' := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [QuotientGroup.mk_mul, hA.mk_padicPow a (l + l') (hn _),
    hA.mk_padicPow a l (hn _), hA.mk_padicPow a l' (hn _), ← pow_add]
  exact pow_eq_pow_of_modEq (PadicInt.appr_add_modEq l l' n) (hn _)

/-- Iterating the `p`-adic power multiplies the exponents. -/
@[simp]
theorem padicPow_mul (hA : IsProP p A) (a : A) (l l' : ℤ_[p]) :
    hA.padicPow a (l * l') = hA.padicPow (hA.padicPow a l) l' := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [hA.mk_padicPow a (l * l') (hn _),
    hA.mk_padicPow (hA.padicPow a l) l' (hn _), hA.mk_padicPow a l (hn _), ← pow_mul]
  exact pow_eq_pow_of_modEq (PadicInt.appr_mul_modEq l l' n) (hn _)

/-- Every `p`-adic power of `1` is `1`. -/
@[simp]
theorem one_padicPow (hA : IsProP p A) (l : ℤ_[p]) : hA.padicPow (1 : A) l = 1 := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [hA.mk_padicPow 1 l (hn _)]
  simp

/-- The `p`-adic power of an inverse is the inverse of the `p`-adic power. -/
@[simp]
theorem inv_padicPow (hA : IsProP p A) (a : A) (l : ℤ_[p]) :
    hA.padicPow a⁻¹ l = (hA.padicPow a l)⁻¹ := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [QuotientGroup.mk_inv, hA.mk_padicPow a⁻¹ l (hn _), hA.mk_padicPow a l (hn _),
    QuotientGroup.mk_inv, inv_pow]

/-- Negating the exponent inverts the `p`-adic power. -/
@[simp]
theorem padicPow_neg (hA : IsProP p A) (a : A) (l : ℤ_[p]) :
    hA.padicPow a (-l) = (hA.padicPow a l)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hA.padicPow_add, neg_add_cancel, hA.padicPow_zero])

/-- The `p`-adic power extends the integer powers. -/
@[simp]
theorem padicPow_intCast (hA : IsProP p A) (a : A) (k : ℤ) :
    hA.padicPow a (k : ℤ_[p]) = a ^ k := by
  rcases k with n | n
  · simp
  · have hcast : ((Int.negSucc n : ℤ) : ℤ_[p]) = -((n + 1 : ℕ) : ℤ_[p]) := by push_cast; ring
    rw [hcast, hA.padicPow_neg, hA.padicPow_natCast, zpow_negSucc]

/-- **The `p`-adic power is jointly continuous** as an action `ℤ_[p] × A → A`. -/
theorem continuous_padicPow (hA : IsProP p A) :
    Continuous fun q : ℤ_[p] × A ↦ hA.padicPow q.2 q.1 := by
  refine continuous_iff_forall_continuous_mk.mpr fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  -- Modulo `U` the power only depends on the exponent modulo `p ^ n` and on the class of the
  -- base, so it factors through a map on a discrete space.
  have hfun : (fun q : ℤ_[p] × A ↦ ((hA.padicPow q.2 q.1 : A) : A ⧸ U.toSubgroup))
      = (fun cg : ZMod (p ^ n) × (A ⧸ U.toSubgroup) ↦ cg.2 ^ cg.1.val) ∘
        fun q : ℤ_[p] × A ↦ (PadicInt.toZModPow n q.1, (q.2 : A ⧸ U.toSubgroup)) := by
    funext q
    simpa [PadicInt.val_toZModPow_eq_appr] using hA.mk_padicPow q.2 q.1 (hn _)
  rw [hfun]
  exact continuous_of_discreteTopology.comp
    (((PadicInt.continuous_toZModPow n).comp continuous_fst).prodMk
      (QuotientGroup.continuous_mk.comp continuous_snd))

/-- **The `p`-adic power is the unique continuous extension of the natural powers** along the
dense inclusion of `ℕ` in `ℤ_[p]`. -/
theorem eq_padicPow_of_continuous (hA : IsProP p A) {a : A} {f : ℤ_[p] → A} (hf : Continuous f)
    (hnat : ∀ k : ℕ, f (k : ℤ_[p]) = a ^ k) (l : ℤ_[p]) : f l = hA.padicPow a l := by
  have hcont : Continuous fun l : ℤ_[p] ↦ hA.padicPow a l :=
    hA.continuous_padicPow.comp (continuous_id.prodMk continuous_const)
  exact congrFun (PadicInt.denseRange_natCast.equalizer hf hcont
    (funext fun k ↦ by simp [hnat k])) l

/-- A closed subgroup containing `a` contains every `p`-adic power of `a`. -/
theorem padicPow_mem (hA : IsProP p A) {H : Subgroup A} (hH : IsClosed (H : Set A)) {a : A}
    (ha : a ∈ H) (l : ℤ_[p]) : hA.padicPow a l ∈ H := by
  -- The exponents `l` with `a ^ l ∈ H` form a closed set containing the dense subset `ℕ`.
  have hclosed : IsClosed {l : ℤ_[p] | hA.padicPow a l ∈ H} :=
    hH.preimage (hA.continuous_padicPow.comp (continuous_id.prodMk continuous_const))
  have hnat : Set.range (Nat.cast : ℕ → ℤ_[p]) ⊆ {l : ℤ_[p] | hA.padicPow a l ∈ H} := by
    rintro _ ⟨k, rfl⟩
    simpa using H.pow_mem ha k
  exact hclosed.closure_subset_iff.mpr hnat
    ((PadicInt.denseRange_natCast (p := p)).closure_range ▸ Set.mem_univ l)

/-- A continuous homomorphism into a `T1` monoid that is trivial on `a` is trivial on every `p`-adic
power of `a`. -/
theorem map_padicPow_eq_one_of_eq_one {B : Type*} [Monoid B] [TopologicalSpace B] [T1Space B]
    (hA : IsProP p A) (f : A →ₜ* B) {a : A} (ha : f a = 1) (l : ℤ_[p]) :
    f (hA.padicPow a l) = 1 :=
  hA.padicPow_mem f.isClosed_ker (MonoidHom.mem_ker.mpr ha) l

/-- **A `p`-adic power lying in a closed subgroup has exponent `0` unless a `p`-power of the base
does.** If the closed subgroup `H` contains `a ^ l` but no `a ^ (p ^ k)`, then `l = 0`: a nonzero
`l` is `u pᵛ` with `u` a unit, and then `a ^ (pᵛ) = (a ^ l) ^ (u⁻¹)` lies in `H`. -/
theorem eq_zero_of_padicPow_mem (hA : IsProP p A) {H : Subgroup A} (hH : IsClosed (H : Set A))
    {a : A} (ha : ∀ k : ℕ, a ^ p ^ k ∉ H) {l : ℤ_[p]} (hl : hA.padicPow a l ∈ H) : l = 0 := by
  by_contra hne
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[p]ˣ, l = u * (p : ℤ_[p]) ^ l.valuation :=
    ⟨_, PadicInt.unitCoeff_spec hne⟩
  obtain ⟨v, hv⟩ : ∃ v : ℕ, l.valuation = v := ⟨_, rfl⟩
  rw [hv] at hu
  refine ha v ?_
  -- `pᵛ = l · u⁻¹`, so `a ^ (pᵛ)` is a `p`-adic power of `a ^ l ∈ H`.
  have hpv : (p : ℤ_[p]) ^ v = l * ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) := by
    rw [hu, mul_comm (u : ℤ_[p]), mul_assoc, Units.mul_inv, mul_one]
  rw [← hA.padicPow_natCast, Nat.cast_pow, hpv, hA.padicPow_mul]
  exact hA.padicPow_mem hH hl _

/-- Continuous homomorphisms between pro-`p` groups preserve the `p`-adic power. -/
theorem map_padicPow {B : Type v} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [TotallyDisconnectedSpace B] (hA : IsProP p A) (hB : IsProP p B)
    (f : A →* B) (hf : Continuous f) (a : A) (l : ℤ_[p]) :
    f (hA.padicPow a l) = hB.padicPow (f a) l := by
  apply hB.eq_padicPow_of_continuous
    (hf.comp (hA.continuous_padicPow.comp (continuous_id.prodMk continuous_const)))
  intro k
  simp

/-- A continuous action by group endomorphisms commutes with `p`-adic powers. -/
@[simp]
theorem smul_padicPow {Γ : Type*} [Monoid Γ] [MulDistribMulAction Γ A]
    [ContinuousConstSMul Γ A] (hA : IsProP p A) (γ : Γ) (a : A) (l : ℤ_[p]) :
    γ • hA.padicPow a l = hA.padicPow (γ • a) l :=
  hA.map_padicPow hA (MulDistribMulAction.toMonoidHom A γ) (continuous_const_smul γ) a l

/-- The `p`-adic power is multiplicative on commuting base elements. -/
@[simp]
theorem mul_padicPow (hA : IsProP p A) (a b : A) (hab : Commute a b) (l : ℤ_[p]) :
    hA.padicPow (a * b) l = hA.padicPow a l * hA.padicPow b l := by
  refine eq_of_forall_mk_eq fun U ↦ ?_
  obtain ⟨n, hn⟩ := hA.exists_forall_pow_pow_eq_one U
  rw [QuotientGroup.mk_mul, hA.mk_padicPow (a * b) l (hn _),
    hA.mk_padicPow a l (hn _), hA.mk_padicPow b l (hn _), QuotientGroup.mk_mul]
  exact (hab.map (QuotientGroup.mk' U.toSubgroup)).mul_pow (l.appr n)

/-- The `p`-adic power commutes with conjugation: `(g * a * g⁻¹) ^ l = g * a ^ l * g⁻¹`. -/
@[simp]
theorem conj_padicPow (hA : IsProP p A) (g a : A) (l : ℤ_[p]) :
    hA.padicPow (g * a * g⁻¹) l = g * hA.padicPow a l * g⁻¹ :=
  -- `map_padicPow` is stated for the monoid hom underlying `MulAut.conj g`; `MulAut.conj_apply`
  -- unfolds its application to `g * _ * g⁻¹`.
  by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
    (hA.map_padicPow hA (MulAut.conj g).toMonoidHom (IsTopologicalGroup.continuous_conj g) a l).symm

/-- A `p`-adic power of an element commuting with `b` commutes with `b`. -/
theorem commute_padicPow_left (hA : IsProP p A) {a b : A} (h : Commute a b) (l : ℤ_[p]) :
    Commute (hA.padicPow a l) b := by
  have hconj : b * a * b⁻¹ = a := by rw [← h.eq, mul_inv_cancel_right]
  have hl := hA.conj_padicPow b a l
  rw [hconj] at hl
  exact (mul_inv_eq_iff_eq_mul.mp hl.symm).symm

/-- An element commuting with `b` commutes with every `p`-adic power of `b`. -/
theorem commute_padicPow_right (hA : IsProP p A) {a b : A} (h : Commute a b) (l : ℤ_[p]) :
    Commute a (hA.padicPow b l) :=
  (hA.commute_padicPow_left h.symm l).symm

/-- `p`-adic powers of commuting elements commute. -/
theorem commute_padicPow (hA : IsProP p A) {a b : A} (h : Commute a b) (l l' : ℤ_[p]) :
    Commute (hA.padicPow a l) (hA.padicPow b l') :=
  hA.commute_padicPow_right (hA.commute_padicPow_left h l) l'

/-- A `p`-adic power of `a` lies in the closed cyclic subgroup generated by `a`. -/
theorem padicPow_mem_closedZpowers (hA : IsProP p A) (a : A) (l : ℤ_[p]) :
    hA.padicPow a l ∈ closedZpowers a :=
  hA.padicPow_mem (isClosed_closedZpowers a) (mem_closedZpowers a) l

/-- The closed cyclic subgroup generated by a `p`-adic power of `a` lies in the one generated by
`a`. -/
theorem closedZpowers_padicPow_le (hA : IsProP p A) (a : A) (l : ℤ_[p]) :
    closedZpowers (hA.padicPow a l) ≤ closedZpowers a :=
  (closedZpowers_le (isClosed_closedZpowers a)).mpr (hA.padicPow_mem_closedZpowers a l)

/-! ### Unit exponents -/

/-- Raising to a unit `u` of `ℤ_[p]` and then to its inverse is the identity. -/
@[simp]
theorem padicPow_padicPow_inv (hA : IsProP p A) (a : A) (u : ℤ_[p]ˣ) :
    hA.padicPow (hA.padicPow a u) ↑u⁻¹ = a := by
  rw [← hA.padicPow_mul, Units.mul_inv, hA.padicPow_one]

/-- Raising to the inverse of a unit `u` of `ℤ_[p]` and then to `u` is the identity. -/
@[simp]
theorem padicPow_inv_padicPow (hA : IsProP p A) (a : A) (u : ℤ_[p]ˣ) :
    hA.padicPow (hA.padicPow a ↑u⁻¹) u = a := by
  rw [← hA.padicPow_mul, Units.inv_mul, hA.padicPow_one]

/-- **The `p`-adic power by a unit is a homeomorphism.** For a unit `u` of `ℤ_[p]` the map
`a ↦ a ^ u` is a homeomorphism of `A`, with inverse `a ↦ a ^ u⁻¹`. -/
noncomputable def padicPowHomeomorph (hA : IsProP p A) (u : ℤ_[p]ˣ) : A ≃ₜ A where
  toFun a := hA.padicPow a u
  invFun a := hA.padicPow a ↑u⁻¹
  left_inv a := hA.padicPow_padicPow_inv a u
  right_inv a := hA.padicPow_inv_padicPow a u
  continuous_toFun := hA.continuous_padicPow.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := hA.continuous_padicPow.comp (continuous_const.prodMk continuous_id)

/-- The homeomorphism `TauCeti.IsProP.padicPowHomeomorph u` is the `p`-adic power by `u`. -/
@[simp]
theorem padicPowHomeomorph_apply (hA : IsProP p A) (u : ℤ_[p]ˣ) (a : A) :
    hA.padicPowHomeomorph u a = hA.padicPow a u :=
  (rfl)

/-- The inverse of the `p`-adic power by `u` is the `p`-adic power by `u⁻¹`. -/
@[simp]
theorem padicPowHomeomorph_symm (hA : IsProP p A) (u : ℤ_[p]ˣ) :
    (hA.padicPowHomeomorph u).symm = hA.padicPowHomeomorph u⁻¹ :=
  Homeomorph.ext fun a ↦ (hA.padicPowHomeomorph u).symm_apply_eq.mpr <| by
    rw [padicPowHomeomorph_apply, padicPowHomeomorph_apply, padicPow_inv_padicPow]

/-- **The `p`-adic power by a unit is injective.** This can fail for non-units: when `A` has
an element of order `p`, the power by `p` identifies it with `1`. -/
theorem padicPow_left_injective (hA : IsProP p A) (u : ℤ_[p]ˣ) :
    Function.Injective fun a : A ↦ hA.padicPow a u :=
  (hA.padicPowHomeomorph u).injective

/-- Two elements with the same `p`-adic power by a unit are equal. -/
@[simp]
theorem padicPow_left_inj (hA : IsProP p A) {a b : A} (u : ℤ_[p]ˣ) :
    hA.padicPow a u = hA.padicPow b u ↔ a = b :=
  (hA.padicPow_left_injective u).eq_iff

/-- A unit `p`-adic power of `a` generates the same closed cyclic subgroup as `a`. -/
@[simp]
theorem closedZpowers_padicPow (hA : IsProP p A) (a : A) (u : ℤ_[p]ˣ) :
    closedZpowers (hA.padicPow a u) = closedZpowers a :=
  (hA.closedZpowers_padicPow_le a u).antisymm
    (by simpa using hA.closedZpowers_padicPow_le (hA.padicPow a u) ↑u⁻¹)

/-! ### Quotients -/

/-- **The `p`-adic power passes to quotients**: the class of `a ^ l` modulo a closed normal
subgroup `N` is the `p`-adic power of the class of `a` in the pro-`p` group `A ⧸ N`. -/
@[simp]
theorem mk_padicPow_quotient (hA : IsProP p A) (N : Subgroup A) [N.Normal]
    [IsClosed (N : Set A)] (a : A) (l : ℤ_[p]) :
    ((hA.padicPow a l : A) : A ⧸ N) = (hA.quotient N).padicPow (a : A ⧸ N) l :=
  hA.map_padicPow (hA.quotient N) (QuotientGroup.mk' N) QuotientGroup.continuous_mk a l

/-- **A `p`-adic power relation between the values of a continuous homomorphism holds in the
quotient by its kernel**: if `χ : A →ₜ* B` is a continuous homomorphism of pro-`p` groups with
`χ b = (χ a) ^ l`, then `b = a ^ l` in `A ⧸ ker χ`. -/
theorem mk_eq_padicPow_mk_of_apply_eq_padicPow {B : Type v} [Group B] [TopologicalSpace B]
    [IsTopologicalGroup B] [CompactSpace B] [TotallyDisconnectedSpace B] [T1Space B]
    (hA : IsProP p A) (hB : IsProP p B) (χ : A →ₜ* B) {a b : A} {l : ℤ_[p]}
    (h : χ b = hB.padicPow (χ a) l) :
    haveI := χ.isClosed_ker
    (b : A ⧸ χ.toMonoidHom.ker) =
      (hA.quotient χ.toMonoidHom.ker).padicPow (a : A ⧸ χ.toMonoidHom.ker) l := by
  have := χ.isClosed_ker
  have hcont : Continuous (QuotientGroup.kerLift χ.toMonoidHom) :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr χ.continuous
  refine QuotientGroup.kerLift_injective χ.toMonoidHom ?_
  rw [(hA.quotient _).map_padicPow hB _ hcont, QuotientGroup.kerLift_mk, QuotientGroup.kerLift_mk]
  exact h

end Group

section CommGroup

variable {p : ℕ} [hp : Fact p.Prime] {A : Type u} [CommGroup A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

/-- **An abelian pro-`p` group is a `ℤ_[p]`-module**, with `l` acting as the `p`-adic power
by `l`. The prime is not determined by `A`, so this is a definition rather than an instance;
consumers introduce it with `letI := hA.module`. -/
@[instance_reducible]
noncomputable def module (hA : IsProP p A) : Module ℤ_[p] (Additive A) where
  smul l x := Additive.ofMul (hA.padicPow x.toMul l)
  one_smul x := congrArg Additive.ofMul (hA.padicPow_one x.toMul)
  mul_smul l l' x := congrArg Additive.ofMul
    ((congrArg (hA.padicPow x.toMul) (mul_comm l l')).trans (hA.padicPow_mul x.toMul l' l))
  smul_zero l := congrArg Additive.ofMul (hA.one_padicPow l)
  smul_add l x y := congrArg Additive.ofMul
    (hA.mul_padicPow x.toMul y.toMul (Commute.all _ _) l)
  add_smul l l' x := congrArg Additive.ofMul (hA.padicPow_add x.toMul l l')
  zero_smul x := congrArg Additive.ofMul (hA.padicPow_zero x.toMul)

/-- The scalar action underlying `TauCeti.IsProP.module` is the `p`-adic power. -/
@[simp]
theorem module_smul (hA : IsProP p A) (l : ℤ_[p]) (x : Additive A) :
    letI := hA.module
    l • x = Additive.ofMul (hA.padicPow x.toMul l) :=
  (rfl)

/-- The `ℤ_[p]`-module structure on an abelian pro-`p` group is topological. -/
theorem continuousSMul_module (hA : IsProP p A) :
    letI := hA.module
    ContinuousSMul ℤ_[p] (Additive A) :=
  letI := hA.module
  -- `Additive A` carries the topology of `A`, and the action is `TauCeti.IsProP.padicPow`
  -- by `TauCeti.IsProP.module_smul`.
  ⟨hA.continuous_padicPow⟩

/-- **A continuous action by group endomorphisms is `ℤ_p`-linear**: it commutes with the scalar
action of `TauCeti.IsProP.module`. -/
theorem smulCommClass_module {Γ : Type*} [Monoid Γ] [MulDistribMulAction Γ A]
    [ContinuousConstSMul Γ A] (hA : IsProP p A) :
    letI := hA.module
    SMulCommClass Γ ℤ_[p] (Additive A) :=
  letI := hA.module
  ⟨fun γ l x ↦ by
    simp only [hA.module_smul, ← Additive.ofMul_smul, Additive.toMul_smul, hA.smul_padicPow]⟩

end CommGroup

section AbelianQuotient

variable {p : ℕ} [Fact p.Prime] {A : Type u} [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A] [CompactSpace A] [TotallyDisconnectedSpace A]

open scoped IsMulCommutative in
/-- **In an abelian quotient the `p`-adic power is the scalar action.** If `N` is a closed normal
subgroup of the pro-`p` group `A` with commutative quotient, then the class of `a ^ l` in
`A ⧸ N`, written additively, is `l` times the class of `a` for the `ℤ_[p]`-module structure
`TauCeti.IsProP.module` of the quotient. -/
theorem ofMul_mk_padicPow_quotient (hA : IsProP p A) (N : Subgroup A) [N.Normal]
    [IsClosed (N : Set A)] [IsMulCommutative (A ⧸ N)] (a : A) (l : ℤ_[p]) :
    letI := (hA.quotient N).module
    Additive.ofMul ((hA.padicPow a l : A) : A ⧸ N) = l • Additive.ofMul (a : A ⧸ N) := by
  rw [module_smul, toMul_ofMul, hA.mk_padicPow_quotient]

end AbelianQuotient


section Multiplicative

variable {p : ℕ} [Fact p.Prime] {X : Type u} [AddGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [CompactSpace X] [TotallyDisconnectedSpace X]

/-- Along a continuous additive homomorphism `g : ℤ_[p] →+ X` into an additive group whose
multiplicative type tag is pro-`p`, the `p`-adic power of `ofAdd (g 1)` is `ofAdd ∘ g`: the
exponent acts through `g`. This computes the `p`-adic powers in a product of pro-`p` groups
coordinatewise. -/
theorem padicPow_ofAdd_apply_one (hX : IsProP p (Multiplicative X)) (g : ℤ_[p] →+ X)
    (hg : Continuous g) (l : ℤ_[p]) :
    hX.padicPow (Multiplicative.ofAdd (g 1)) l = Multiplicative.ofAdd (g l) :=
  (hX.eq_padicPow_of_continuous (f := fun l ↦ Multiplicative.ofAdd (g l))
    (continuous_ofAdd.comp hg) (fun k ↦ by rw [← ofAdd_nsmul, ← map_nsmul, nsmul_one]) l).symm

end Multiplicative

end IsProP

end TauCeti
