/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Multiset
public import Mathlib.Data.Multiset.UnionInter
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Topology.Instances.AddCircle.Defs
import TauCeti.Algebra.AddCircle
import TauCeti.Algebra.Group.Coprime

/-!
# Hypergeometric parameter pairs

A hypergeometric family of degree `d` is indexed by two multisets `α`, `β` of `d` classes in
`ℚ/ℤ`, realized as `AddCircle (1 : ℚ)`, with no class common to both. This is the generality in
which Levelt's theorem on the monodromy of the hypergeometric equation, the Beukers–Heckman
invariant form and the finite hypergeometric sums over a single finite field are stated; the
LMFDB's cyclotomic data are the pairs stable under every scaling by a unit.

This file sets up the carrier `TauCeti.Hypergeometric.Parameters` and the operations on it
that the later theory transports invariants along:

* the representatives `rep x ∈ (0, 1]` and `rep0 x ∈ [0, 1)` of a class `x`, with the class of
  `0` represented by `1` and by `0` respectively. The first is the LMFDB's display and the one
  the zigzag of the Hodge vector reads; the second is Beukers–Heckman's normalisation;
* the swap `(α, β) ↦ (β, α)` and the negation `(α, β) ↦ (-α, -β)`, both involutions;
* the shift `(α, β) ↦ (μ + α, μ + β)`, an additive action of `ℚ/ℤ`;
* the common denominator `N`, the least positive integer killing every class of `α + β`, equal
  to the lcm of their additive orders, and `1` exactly for the empty pair;
* the scaling `(α, β) ↦ (uα, uβ)` by an integer `u` prime to `N`, which preserves disjointness,
  the degree and the common denominator, and composes multiplicatively;
* Galois stability: being fixed by every such scaling.

## Main declarations

* `TauCeti.Hypergeometric.rep`, `TauCeti.Hypergeometric.rep0`: the representatives, with
  `coe_rep`, `rep_injective`, `rep_zero`, `rep_eq_iff` and their `rep0` counterparts, and
  `rep_neg`, `rep0_neg` relating them under negation.
* `TauCeti.Hypergeometric.Parameters`: a hypergeometric parameter pair, with its `degree`.
* `TauCeti.Hypergeometric.Parameters.swap`, the `Neg` and `InvolutiveNeg` instances, and the
  `AddAction (AddCircle (1 : ℚ))` instance of shifts.
* `TauCeti.Hypergeometric.Parameters.denominator`, with `denominator_eq_lcm`,
  `denominator_dvd_iff`, `isLeast_denominator` and `denominator_eq_one_iff`.
* `TauCeti.Hypergeometric.Parameters.scale`, with `denominator_scale` and `scale_scale`.
* `TauCeti.Hypergeometric.Parameters.IsGaloisStable`: stability under every such scaling, with
  `isGaloisStable_iff`.

## References

* F. Beukers and G. Heckman, *Monodromy for the hypergeometric function `ₙFₙ₋₁`*, Invent. Math.
  95 (1989), §2–§3.
* F. Beukers, H. Cohen and A. Mellit, *Finite hypergeometric functions*, Pure Appl. Math. Q. 11
  (2015), §1.
* D. P. Roberts and F. Rodriguez-Villegas, *Hypergeometric motives*, Notices Amer. Math. Soc. 69
  (2022), §2.
-/

public section

open Set

namespace TauCeti.Hypergeometric

/-! ### Representatives of classes in `ℚ/ℤ` -/

/-- The representative in `(0, 1]` of a class in `ℚ/ℤ`. The class of `0` is represented by `1`,
as in the LMFDB's display of hypergeometric parameters. -/
noncomputable def rep (x : AddCircle (1 : ℚ)) : ℚ := AddCircle.equivIoc 1 0 x

/-- The representative in `[0, 1)` of a class in `ℚ/ℤ`, Beukers–Heckman's normalisation. -/
noncomputable def rep0 (x : AddCircle (1 : ℚ)) : ℚ := AddCircle.equivIco 1 0 x

variable {x : AddCircle (1 : ℚ)} {q : ℚ}

theorem rep_mem_Ioc (x : AddCircle (1 : ℚ)) : rep x ∈ Ioc (0 : ℚ) 1 := by
  simpa [rep] using (AddCircle.equivIoc 1 0 x).property

theorem rep_pos (x : AddCircle (1 : ℚ)) : 0 < rep x := (rep_mem_Ioc x).1

theorem rep_le_one (x : AddCircle (1 : ℚ)) : rep x ≤ 1 := (rep_mem_Ioc x).2

/-- The representative lifts the class. -/
@[simp]
theorem coe_rep (x : AddCircle (1 : ℚ)) : ((rep x : ℚ) : AddCircle (1 : ℚ)) = x :=
  AddCircle.coe_equivIoc

theorem rep_injective : Function.Injective rep :=
  Function.LeftInverse.injective coe_rep

@[simp]
theorem rep_inj {y : AddCircle (1 : ℚ)} : rep x = rep y ↔ x = y :=
  rep_injective.eq_iff

/-- A rational number is the representative of a class exactly when it lies in `(0, 1]` and
lifts that class. -/
theorem rep_eq_iff : rep x = q ↔ q ∈ Ioc (0 : ℚ) 1 ∧ (q : AddCircle (1 : ℚ)) = x := by
  constructor
  · rintro rfl
    exact ⟨rep_mem_Ioc x, coe_rep x⟩
  · rintro ⟨hq, rfl⟩
    exact AddCircle.equivIoc_coe_of_mem (by simpa using hq)

theorem rep_coe_of_mem (hq : q ∈ Ioc (0 : ℚ) 1) : rep (q : AddCircle (1 : ℚ)) = q :=
  rep_eq_iff.2 ⟨hq, rfl⟩

/-- The class of `0` is represented by `1`. -/
@[simp]
theorem rep_zero : rep 0 = 1 :=
  rep_eq_iff.2 ⟨⟨one_pos, le_rfl⟩, AddCircle.coe_period _⟩

@[simp]
theorem rep_eq_one_iff : rep x = 1 ↔ x = 0 :=
  ⟨fun h ↦ rep_injective (h.trans rep_zero.symm), fun h ↦ h ▸ rep_zero⟩

theorem rep0_mem_Ico (x : AddCircle (1 : ℚ)) : rep0 x ∈ Ico (0 : ℚ) 1 := by
  simpa [rep0] using (AddCircle.equivIco 1 0 x).property

theorem rep0_nonneg (x : AddCircle (1 : ℚ)) : 0 ≤ rep0 x := (rep0_mem_Ico x).1

theorem rep0_lt_one (x : AddCircle (1 : ℚ)) : rep0 x < 1 := (rep0_mem_Ico x).2

/-- The representative in `[0, 1)` lifts the class. -/
@[simp]
theorem coe_rep0 (x : AddCircle (1 : ℚ)) : ((rep0 x : ℚ) : AddCircle (1 : ℚ)) = x :=
  AddCircle.coe_equivIco

theorem rep0_injective : Function.Injective rep0 :=
  Function.LeftInverse.injective coe_rep0

@[simp]
theorem rep0_inj {y : AddCircle (1 : ℚ)} : rep0 x = rep0 y ↔ x = y :=
  rep0_injective.eq_iff

/-- A rational number is the representative in `[0, 1)` of a class exactly when it lies in
`[0, 1)` and lifts that class. -/
theorem rep0_eq_iff : rep0 x = q ↔ q ∈ Ico (0 : ℚ) 1 ∧ (q : AddCircle (1 : ℚ)) = x := by
  constructor
  · rintro rfl
    exact ⟨rep0_mem_Ico x, coe_rep0 x⟩
  · rintro ⟨hq, rfl⟩
    exact AddCircle.equivIco_coe_of_mem (by simpa using hq)

theorem rep0_coe_of_mem (hq : q ∈ Ico (0 : ℚ) 1) : rep0 (q : AddCircle (1 : ℚ)) = q :=
  rep0_eq_iff.2 ⟨hq, rfl⟩

/-- The class of `0` is represented by `0` in `[0, 1)`. -/
@[simp]
theorem rep0_zero : rep0 0 = 0 :=
  rep0_eq_iff.2 ⟨⟨le_rfl, one_pos⟩, AddCircle.coe_zero _⟩

@[simp]
theorem rep0_eq_zero_iff : rep0 x = 0 ↔ x = 0 :=
  ⟨fun h ↦ rep0_injective (h.trans rep0_zero.symm), fun h ↦ h ▸ rep0_zero⟩

/-- Away from the class of `0` the two representatives agree. -/
theorem rep_eq_rep0 (hx : x ≠ 0) : rep x = rep0 x := by
  refine rep_eq_iff.2 ⟨⟨?_, (rep0_lt_one x).le⟩, coe_rep0 x⟩
  exact (rep0_nonneg x).lt_of_ne' (by rwa [Ne, rep0_eq_zero_iff])

/-- Negation reflects the representatives: `rep (-x) = 1 - rep0 x`. -/
theorem rep_neg (x : AddCircle (1 : ℚ)) : rep (-x) = 1 - rep0 x := by
  refine rep_eq_iff.2 ⟨⟨by linarith [rep0_lt_one x], by linarith [rep0_nonneg x]⟩, ?_⟩
  rw [AddCircle.coe_sub, AddCircle.coe_period, coe_rep0, zero_sub]

/-- Negation reflects the representatives: `rep0 (-x) = 1 - rep x`. -/
theorem rep0_neg (x : AddCircle (1 : ℚ)) : rep0 (-x) = 1 - rep x := by
  refine rep0_eq_iff.2 ⟨⟨by linarith [rep_le_one x], by linarith [rep_pos x]⟩, ?_⟩
  rw [AddCircle.coe_sub, AddCircle.coe_period, coe_rep, zero_sub]

/-! ### Parameter pairs -/

/-- A hypergeometric parameter pair: two multisets `α`, `β` of classes in `ℚ/ℤ` of the same
cardinality, with no class in both. The local exponents of the hypergeometric equation at `0`
and `∞` are read off `β` and `α`. -/
@[ext]
structure Parameters where
  /-- The top parameters, giving the local exponents at `∞`. -/
  α : Multiset (AddCircle (1 : ℚ))
  /-- The bottom parameters, giving the local exponents at `0`. -/
  β : Multiset (AddCircle (1 : ℚ))
  card_eq : Multiset.card α = Multiset.card β
  disjoint : Disjoint α β

namespace Parameters

variable (P : Parameters)

/-- The degree `d` of a parameter pair, the common cardinality of `α` and `β`. -/
def degree : ℕ := Multiset.card P.α

@[simp]
theorem card_α : Multiset.card P.α = P.degree := (rfl)

@[simp]
theorem card_β : Multiset.card P.β = P.degree := P.card_eq.symm

theorem degree_eq_zero_iff : P.degree = 0 ↔ P.α = 0 ∧ P.β = 0 := by
  rw [← Multiset.card_eq_zero, ← Multiset.card_eq_zero, card_α, card_β, and_self]

theorem notMem_β_of_mem_α {a : AddCircle (1 : ℚ)} (ha : a ∈ P.α) : a ∉ P.β :=
  Multiset.disjoint_left.1 P.disjoint ha

/-! ### Swap -/

/-- The swap `(α, β) ↦ (β, α)`. -/
def swap : Parameters where
  α := P.β
  β := P.α
  card_eq := P.card_eq.symm
  disjoint := P.disjoint.symm

@[simp]
theorem swap_α : P.swap.α = P.β := (rfl)

@[simp]
theorem swap_β : P.swap.β = P.α := (rfl)

@[simp]
theorem swap_swap : P.swap.swap = P := (rfl)

theorem swap_involutive : Function.Involutive swap := swap_swap

@[simp]
theorem degree_swap : P.swap.degree = P.degree := P.card_β

/-! ### Negation -/

/-- The negation `(α, β) ↦ (-α, -β)`. -/
instance : Neg Parameters where
  neg P :=
    { α := P.α.map Neg.neg
      β := P.β.map Neg.neg
      card_eq := by simp [P.card_eq]
      disjoint := Multiset.disjoint_map_map.2 fun a ha b hb h ↦
        Multiset.disjoint_iff_ne.1 P.disjoint a ha b hb (neg_injective h) }

@[simp]
theorem neg_α : (-P).α = P.α.map Neg.neg := (rfl)

@[simp]
theorem neg_β : (-P).β = P.β.map Neg.neg := (rfl)

instance : InvolutiveNeg Parameters where
  neg_neg P := by ext1 <;> simp [Multiset.map_map]

@[simp]
theorem degree_neg : (-P).degree = P.degree := by
  rw [← card_α, ← card_α]
  simp

@[simp]
theorem swap_neg : (-P).swap = -P.swap := (rfl)

/-! ### Shifts -/

/-- The shift `(α, β) ↦ (μ + α, μ + β)` by a class `μ`. -/
instance : VAdd (AddCircle (1 : ℚ)) Parameters where
  vadd μ P :=
    { α := P.α.map (μ + ·)
      β := P.β.map (μ + ·)
      card_eq := by simp [P.card_eq]
      disjoint := Multiset.disjoint_map_map.2 fun a ha b hb h ↦
        Multiset.disjoint_iff_ne.1 P.disjoint a ha b hb (add_left_cancel h) }

@[simp]
theorem vadd_α (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).α = P.α.map (μ + ·) := (rfl)

@[simp]
theorem vadd_β (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).β = P.β.map (μ + ·) := (rfl)

/-- Shifts form an additive action of `ℚ/ℤ` on parameter pairs. -/
instance : AddAction (AddCircle (1 : ℚ)) Parameters where
  zero_vadd P := by ext1 <;> simp
  add_vadd μ ν P := by ext1 <;> simp [Multiset.map_map, add_assoc]

@[simp]
theorem degree_vadd (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).degree = P.degree := by
  rw [← card_α, ← card_α]
  simp

@[simp]
theorem swap_vadd (μ : AddCircle (1 : ℚ)) : (μ +ᵥ P).swap = μ +ᵥ P.swap := (rfl)

@[simp]
theorem neg_vadd (μ : AddCircle (1 : ℚ)) : -(μ +ᵥ P) = -μ +ᵥ -P := by
  ext1 <;> simp [Multiset.map_map, add_comm]

/-! ### The common denominator -/

/-- The common denominator `N` of a parameter pair: the lcm of the additive orders of the
classes in `α + β`, equivalently the least positive integer killing all of them
(`isLeast_denominator`). -/
noncomputable def denominator : ℕ := ((P.α + P.β).map addOrderOf).lcm

/-- The common denominator is the lcm of the additive orders of the classes in `α + β`. -/
theorem denominator_eq_lcm : P.denominator = ((P.α + P.β).map addOrderOf).lcm := (rfl)

/-- A natural number is a multiple of the common denominator exactly when it kills every class
of the pair. -/
theorem denominator_dvd_iff {n : ℕ} :
    P.denominator ∣ n ↔ ∀ a ∈ P.α + P.β, n • a = 0 := by
  simp only [denominator, Multiset.lcm_dvd, Multiset.forall_mem_map_iff,
    addOrderOf_dvd_iff_nsmul_eq_zero]

theorem addOrderOf_dvd_denominator {a : AddCircle (1 : ℚ)} (ha : a ∈ P.α + P.β) :
    addOrderOf a ∣ P.denominator :=
  addOrderOf_dvd_iff_nsmul_eq_zero.2 (P.denominator_dvd_iff.1 dvd_rfl a ha)

theorem denominator_nsmul_eq_zero {a : AddCircle (1 : ℚ)} (ha : a ∈ P.α + P.β) :
    P.denominator • a = 0 :=
  P.denominator_dvd_iff.1 dvd_rfl a ha

theorem denominator_pos : 0 < P.denominator := by
  refine Nat.pos_of_ne_zero fun h ↦ ?_
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.lcm_eq_zero_iff _ |>.1 h)
  exact (AddCircle.isOfFinAddOrder_rat a).addOrderOf_pos.ne' ha

/-- The common denominator is the least positive integer killing every class of the pair. -/
theorem isLeast_denominator :
    IsLeast {n : ℕ | 0 < n ∧ ∀ a ∈ P.α + P.β, n • a = 0} P.denominator :=
  ⟨⟨P.denominator_pos, P.denominator_dvd_iff.1 dvd_rfl⟩,
    fun _ hn ↦ Nat.le_of_dvd hn.1 (P.denominator_dvd_iff.2 hn.2)⟩

/-- The common denominator is `1` exactly for the empty pair: a nonempty pair has a class in
`α` and a different one in `β`, so not every class is `0`. -/
theorem denominator_eq_one_iff : P.denominator = 1 ↔ P.degree = 0 := by
  constructor
  · intro h
    have h0 : ∀ a ∈ P.α + P.β, a = 0 := fun a ha ↦ by
      simpa [h] using P.denominator_nsmul_eq_zero ha
    by_contra hd
    obtain ⟨a, ha⟩ := (Multiset.card_pos_iff_exists_mem (s := P.α)).1 (by rw [card_α]; omega)
    obtain ⟨b, hb⟩ := (Multiset.card_pos_iff_exists_mem (s := P.β)).1 (by rw [card_β]; omega)
    have ha0 := h0 a (Multiset.mem_add.2 (.inl ha))
    have hb0 := h0 b (Multiset.mem_add.2 (.inr hb))
    exact P.notMem_β_of_mem_α ha (by rwa [ha0, ← hb0])
  · intro h
    obtain ⟨hα, hβ⟩ := P.degree_eq_zero_iff.1 h
    simp [denominator, hα, hβ]

@[simp]
theorem denominator_swap : P.swap.denominator = P.denominator := by
  simp [denominator, add_comm]

@[simp]
theorem denominator_neg : (-P).denominator = P.denominator := by
  simp [denominator, Multiset.map_map]

/-! ### Scaling by units -/

/-- The scaling `(α, β) ↦ (uα, uβ)` by an integer `u` prime to the common denominator. Such a
`u` is injective on the classes of the pair, which keeps the scaled multisets disjoint. -/
def scale {u : ℤ} (hu : IsCoprime u P.denominator) : Parameters where
  α := P.α.map (u • ·)
  β := P.β.map (u • ·)
  card_eq := by simp [P.card_eq]
  disjoint := by
    obtain ⟨v, hv⟩ := hu.exists_zsmul_zsmul_eq_of_zsmul_eq_zero (G := AddCircle (1 : ℚ))
    refine Multiset.disjoint_map_map.2 fun a ha b hb h ↦ ?_
    refine Multiset.disjoint_iff_ne.1 P.disjoint a ha b hb ?_
    have hN {c} (hc : c ∈ P.α + P.β) : (P.denominator : ℤ) • c = 0 := by
      rw [natCast_zsmul, P.denominator_nsmul_eq_zero hc]
    rw [← hv a (hN (Multiset.mem_add.2 (.inl ha))), ← hv b (hN (Multiset.mem_add.2 (.inr hb))), h]

variable {u : ℤ} (hu : IsCoprime u P.denominator)

@[simp]
theorem scale_α : (P.scale hu).α = P.α.map (u • ·) := (rfl)

@[simp]
theorem scale_β : (P.scale hu).β = P.β.map (u • ·) := (rfl)

@[simp]
theorem degree_scale : (P.scale hu).degree = P.degree := by
  rw [← card_α, ← card_α]
  simp

/-- Scaling by a unit preserves the common denominator. -/
@[simp]
theorem denominator_scale : (P.scale hu).denominator = P.denominator := by
  obtain ⟨v, hv⟩ := hu.exists_zsmul_zsmul_eq_of_zsmul_eq_zero (G := AddCircle (1 : ℚ))
  refine Nat.dvd_antisymm ((P.scale hu).denominator_dvd_iff.2 fun a ha ↦ ?_)
    (P.denominator_dvd_iff.2 fun a ha ↦ ?_)
  · obtain ⟨b, hb, rfl⟩ : ∃ b ∈ P.α + P.β, u • b = a := by
      simpa [← Multiset.map_add] using ha
    rw [smul_comm, P.denominator_nsmul_eq_zero hb, smul_zero]
  · have hua : (P.scale hu).denominator • (u • a) = 0 :=
      (P.scale hu).denominator_nsmul_eq_zero <| by
        rw [scale_α, scale_β, ← Multiset.map_add]
        exact Multiset.mem_map_of_mem _ ha
    have hN : P.denominator • (P.scale hu).denominator • a = 0 := by
      rw [smul_comm, P.denominator_nsmul_eq_zero ha, smul_zero]
    rw [← hv _ ((natCast_zsmul _ _).trans hN), smul_comm u, hua, smul_zero]

@[simp]
theorem scale_one : P.scale (u := 1) isCoprime_one_left = P := by
  ext1 <;> simp

@[simp]
theorem scale_neg_one : P.scale (u := -1) isCoprime_one_left.neg_left = -P := by
  ext1 <;> simp

/-- Scaling by `u` and then by `v` is scaling by `v * u`. -/
theorem scale_scale {v : ℤ} (hv : IsCoprime v (P.scale hu).denominator) :
    (P.scale hu).scale hv =
      P.scale (u := v * u) (IsCoprime.mul_left (P.denominator_scale hu ▸ hv) hu) := by
  ext1 <;> simp [Multiset.map_map, mul_zsmul]

@[simp]
theorem swap_scale : (P.scale hu).swap = P.swap.scale (P.denominator_swap ▸ hu) := (rfl)

@[simp]
theorem neg_scale : -(P.scale hu) = (-P).scale (P.denominator_neg ▸ hu) := by
  ext1 <;> simp [Multiset.map_map]

/-! ### Galois stability -/

/-- A parameter pair is *Galois stable* when every scaling by an integer prime to the common
denominator fixes it. The Galois-stable pairs are exactly the pairs of a cyclotomic datum. -/
def IsGaloisStable : Prop :=
  ∀ (u : ℤ) (hu : IsCoprime u P.denominator), P.scale hu = P

theorem isGaloisStable_iff : P.IsGaloisStable ↔
    ∀ u : ℤ, IsCoprime u P.denominator → P.α.map (u • ·) = P.α ∧ P.β.map (u • ·) = P.β := by
  simp only [IsGaloisStable, Parameters.ext_iff, scale_α, scale_β]

@[simp]
theorem isGaloisStable_swap : P.swap.IsGaloisStable ↔ P.IsGaloisStable := by
  simp only [isGaloisStable_iff, swap_α, swap_β, denominator_swap, and_comm]

end Parameters

end TauCeti.Hypergeometric
