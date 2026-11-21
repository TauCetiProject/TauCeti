/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import TauCeti.GroupTheory.FreeGroup.GenEq.Tied

/-!
# Transferring a base of a generalised equation

The elementary transformation ET2 of Makanin's process (Kharlampovich–Myasnikov, §5.1) transfers a
variable base `ψ` contained in a *carrier* base `μ` onto the dual base `Δ(μ)`. It applies when `ψ`
differs from `μ` and `Δ(μ)`, has both end-points `α(ψ), β(ψ)` tied through `μ`, and has every
boundary connection `(p, ψ, r)` tied through `μ` at `p` (`TauCeti.GenEq.IsTransferable`).

In a formally consistent generalised equation `Ω`, the function `tiedBoundary μ` is strictly
increasing on the `μ`-tied boundaries when `ε(μ) = ε(Δμ)` and strictly decreasing on the `μ`-tied
boundaries when `ε(μ) ≠ ε(Δμ)`. Writing `q_l = tiedBoundary μ α(ψ)` and
`q_r = tiedBoundary μ β(ψ)`, the result `Ω′ = Ω.transferBase hΩ h`
keeps the items, constant bases and base indices of `Ω`, leaves every base other than `ψ` at its
place, and moves `ψ` onto `Δ(μ)`:

* when `ε(μ) = ε(Δμ)`, `ψ` spans `[q_l, q_r]` with the same sign `ε(ψ)`;
* when `ε(μ) ≠ ε(Δμ)`, `ψ` spans `[q_r, q_l]` with the opposite sign `¬ ε(ψ)`;
* every boundary connection is relocated by `transferConnection` (when `ψ ≠ Δ(ψ)`, `(p, ψ, r)`
  becomes `(tiedBoundary μ p, ψ, r)` and its dual `(r, Δψ, p)` becomes
  `(r, Δψ, tiedBoundary μ p)`).

This file defines ET2 and establishes its combinatorial invariants: endpoints, signs, item degrees,
constant and free items, open and closed boundaries, closed sections `Σ_Ω`, boundary connections,
ties, and transferability of other bases. For the effect on group solutions, coordinate groups,
graphical solutions, and packaging as a `TauCeti.GenEq.Transformation`, see
`TauCeti.GroupTheory.FreeGroup.GenEq.Elementary.Transfer.Solution`.

## Main definitions

* `TauCeti.GenEq.IsTransferable`: applicability of ET2 to a carrier `μ` and a transfer base `ψ`,
  with a `Decidable` instance.
* `TauCeti.GenEq.transferConnection`: relocation of boundary connections when transferring `ψ`
  along `μ`.
* `TauCeti.GenEq.transferBase`: the generalised equation obtained by transferring `ψ` along `μ`.

## Main results

* `TauCeti.GenEq.baseItems_transferBase_subset_dual`: in the result, `ψ` is contained in `Δ(μ)`.
* `TauCeti.GenEq.closedSections_transferBase`,
  `TauCeti.GenEq.closedSectionOfBase_transferBase_self`: transferring a base preserves constant and
  free items, open and closed boundaries, and the closed sections `Σ_Ω`, while moving `ψ` into the
  closed section of `Δ(μ)`.
* `TauCeti.GenEq.degree_transferBase_add_one`,
  `TauCeti.GenEq.degree_transferBase_eq_degree_add_one`,
  `TauCeti.GenEq.degree_transferBase_eq_degree_iff`: effect of transferring `ψ` on item degrees;
  in particular, transferring `ψ` off an item not in its transferred section lowers that item's
  degree by `1` (lowering degrees in `σ(μ) \ σ(Δμ)` towards `1`).
* `TauCeti.GenEq.isTransferable_transferBase_of_ne`: for `μ' ∉ {ψ, Δ(ψ)}` and `ψ' ≠ ψ`,
  transferability of `ψ'` along `μ'` is preserved and reflected by transferring `ψ` along `μ`.
* `TauCeti.GenEq.card_connections_transferBase`: transferring a base preserves the number of
  boundary connections.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET2.
* O. Kharlampovich, A. Myasnikov, *Effective JSJ decompositions*, Contemp. Math. 378 (2005),
  §5.1, ET2.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §11.3, ET2.
-/

public section

namespace TauCeti

namespace GenEq

variable {A : Type*}

/-! ### Transferability of a base along a carrier -/

section IsTransferable

variable (Ω : GenEq A)

/-- The variable base `ψ` can be transferred along the carrier base `μ` (ET2,
Kharlampovich–Myasnikov, §5.1): `ψ` differs from `μ` and `Δ(μ)`, both end-points of `ψ` are
`μ`-tied (which forces `σ(ψ) ⊆ σ(μ)`), and every boundary connection through `ψ` has its
`ψ`-boundary `μ`-tied. -/
structure IsTransferable (μ ψ : Fin Ω.numBases) : Prop where
  /-- The transfer base is not the carrier. -/
  ne_carrier : ψ ≠ μ
  /-- The transfer base is not the dual of the carrier. -/
  ne_dual_carrier : ψ ≠ Ω.dual μ
  /-- The initial boundary of `ψ` is `μ`-tied. -/
  exists_isTiedTo_left : ∃ q, Ω.IsTiedTo μ (Ω.left ψ) q
  /-- The terminal boundary of `ψ` is `μ`-tied. -/
  exists_isTiedTo_right : ∃ q, Ω.IsTiedTo μ (Ω.right ψ) q
  /-- Every boundary connection through `ψ` has its `ψ`-boundary `μ`-tied. -/
  exists_isTiedTo_of_mem_connections : ∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q

/-- Unfolding `IsTransferable` as a conjunction of its conditions. -/
theorem isTransferable_iff {μ ψ : Fin Ω.numBases} :
    Ω.IsTransferable μ ψ ↔ ψ ≠ μ ∧ ψ ≠ Ω.dual μ ∧
      (∃ q, Ω.IsTiedTo μ (Ω.left ψ) q) ∧ (∃ q, Ω.IsTiedTo μ (Ω.right ψ) q) ∧
      ∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅⟩ => ⟨h₁, h₂, h₃, h₄, h₅⟩⟩

/-- Whether `ψ` can be transferred along `μ` is decidable. -/
instance (μ ψ : Fin Ω.numBases) : Decidable (Ω.IsTransferable μ ψ) :=
  letI : Decidable (∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q) :=
    Finset.decidableDforallFinset
  decidable_of_iff _ Ω.isTransferable_iff.symm

variable {Ω} {μ ψ : Fin Ω.numBases}

/-- The initial boundary of `ψ` is `μ`-tied to `tiedBoundary μ (left ψ)`. -/
theorem IsTransferable.isTiedTo_tiedBoundary_left (h : Ω.IsTransferable μ ψ) :
    Ω.IsTiedTo μ (Ω.left ψ) (Ω.tiedBoundary μ (Ω.left ψ)) :=
  isTiedTo_tiedBoundary_iff.2 h.exists_isTiedTo_left

/-- The terminal boundary of `ψ` is `μ`-tied to `tiedBoundary μ (right ψ)`. -/
theorem IsTransferable.isTiedTo_tiedBoundary_right (h : Ω.IsTransferable μ ψ) :
    Ω.IsTiedTo μ (Ω.right ψ) (Ω.tiedBoundary μ (Ω.right ψ)) :=
  isTiedTo_tiedBoundary_iff.2 h.exists_isTiedTo_right

/-- For every boundary connection `(p, ψ, r)` through `ψ`, `p` is `μ`-tied to `tiedBoundary μ p`. -/
theorem IsTransferable.isTiedTo_tiedBoundary_of_mem_connections (h : Ω.IsTransferable μ ψ)
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (hc : c ∈ Ω.connections) (hcψ : c.2.1 = ψ) :
    Ω.IsTiedTo μ c.1 (Ω.tiedBoundary μ c.1) :=
  isTiedTo_tiedBoundary_iff.2 (h.exists_isTiedTo_of_mem_connections c hc hcψ)

/-- The transfer base starts at or after the start of the carrier. -/
theorem IsTransferable.left_le (h : Ω.IsTransferable μ ψ) : Ω.left μ ≤ Ω.left ψ :=
  h.isTiedTo_tiedBoundary_left.left_le

/-- The transfer base ends at or before the end of the carrier. -/
theorem IsTransferable.right_le (h : Ω.IsTransferable μ ψ) : Ω.right ψ ≤ Ω.right μ :=
  h.isTiedTo_tiedBoundary_right.le_right

/-- A transferable base is contained in its carrier as a section of items. -/
theorem IsTransferable.baseItems_subset (h : Ω.IsTransferable μ ψ) :
    Ω.baseItems ψ ⊆ Ω.baseItems μ :=
  Ω.baseItems_subset_baseItems_iff.2 ⟨h.left_le, h.right_le⟩

/-- The dual of a transferable base is not the carrier. -/
theorem IsTransferable.dual_ne_carrier (h : Ω.IsTransferable μ ψ) : Ω.dual ψ ≠ μ :=
  mt Ω.dual_involutive.eq_iff.1 h.ne_dual_carrier

/-- The dual of a transferable base is not the dual of the carrier. -/
theorem IsTransferable.dual_ne_dual_carrier (h : Ω.IsTransferable μ ψ) : Ω.dual ψ ≠ Ω.dual μ :=
  fun heq => h.ne_carrier (Ω.dual_involutive.injective heq)

/-- A base `ψ` with the same end-points as `μ`, distinct from `μ` and `Δ(μ)`, whose boundary
connections have their `ψ`-boundary `μ`-tied is transferable along `μ`: its end-points are tied as
end-points of `μ`. -/
theorem IsTransferable.of_endpoints_eq (hl : Ω.left ψ = Ω.left μ) (hr : Ω.right ψ = Ω.right μ)
    (hμ : ψ ≠ μ) (hdμ : ψ ≠ Ω.dual μ)
    (hc : ∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q) : Ω.IsTransferable μ ψ where
  ne_carrier := hμ
  ne_dual_carrier := hdμ
  exists_isTiedTo_left := hl ▸ ⟨_, Ω.isTiedTo_left⟩
  exists_isTiedTo_right := hr ▸ ⟨_, Ω.isTiedTo_right⟩
  exists_isTiedTo_of_mem_connections := hc

end IsTransferable

/-! ### Relocation of boundary connections and the transferred equation -/

section TransferBase

variable (Ω : GenEq A)

/-- Relocate a boundary connection triple `c` when transferring `ψ` along `μ`: replace `c.1` by
`tiedBoundary μ c.1` when `c.2.1 = ψ`, and replace `c.2.2` by `tiedBoundary μ c.2.2` when
`c.2.1 = Δ(ψ)`. When `ψ ≠ Δ(ψ)`, a connection `(p, ψ, r)` becomes `(tiedBoundary μ p, ψ, r)`, a
dual connection `(r, Δψ, p)` becomes `(r, Δψ, tiedBoundary μ p)`, and any other triple is
unchanged. -/
def transferConnection (μ ψ : Fin Ω.numBases)
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1) :=
  (if c.2.1 = ψ then Ω.tiedBoundary μ c.1 else c.1,
    c.2.1,
    if c.2.1 = Ω.dual ψ then Ω.tiedBoundary μ c.2.2 else c.2.2)

/-- Explicit formula for `transferConnection`. -/
theorem transferConnection_def (μ ψ : Fin Ω.numBases)
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    Ω.transferConnection μ ψ c =
      (if c.2.1 = ψ then Ω.tiedBoundary μ c.1 else c.1,
        c.2.1,
        if c.2.1 = Ω.dual ψ then Ω.tiedBoundary μ c.2.2 else c.2.2) :=
  (rfl)

variable {Ω} {μ ψ : Fin Ω.numBases}

/-- The first boundary of `transferConnection μ ψ c` is `tiedBoundary μ c.1` when `c.2.1 = ψ`, and
`c.1` otherwise. -/
@[simp]
theorem transferConnection_fst
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.transferConnection μ ψ c).1 = if c.2.1 = ψ then Ω.tiedBoundary μ c.1 else c.1 :=
  (rfl)

/-- Relocating a connection preserves the base index. -/
@[simp]
theorem transferConnection_snd_fst
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.transferConnection μ ψ c).2.1 = c.2.1 :=
  (rfl)

/-- The second boundary of `transferConnection μ ψ c` is `tiedBoundary μ c.2.2` when
`c.2.1 = Δ(ψ)`, and `c.2.2` otherwise. -/
@[simp]
theorem transferConnection_snd_snd
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.transferConnection μ ψ c).2.2 =
      if c.2.1 = Ω.dual ψ then Ω.tiedBoundary μ c.2.2 else c.2.2 :=
  (rfl)

/-- For `ψ ≠ Δ(ψ)`, relocating a connection `c` with `c.2.1 = ψ` replaces its first boundary by
`tiedBoundary μ c.1`. -/
theorem transferConnection_of_eq (hself : ψ ≠ Ω.dual ψ)
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c.2.1 = ψ) :
    Ω.transferConnection μ ψ c = (Ω.tiedBoundary μ c.1, c.2.1, c.2.2) := by
  obtain ⟨p, ν, r⟩ := c
  subst hc
  simp [transferConnection_def, hself]

/-- For `ψ ≠ Δ(ψ)`, relocating a connection `c` with `c.2.1 = Δ(ψ)` replaces its second boundary
by `tiedBoundary μ c.2.2`. -/
theorem transferConnection_of_eq_dual (hself : ψ ≠ Ω.dual ψ)
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c.2.1 = Ω.dual ψ) :
    Ω.transferConnection μ ψ c = (c.1, c.2.1, Ω.tiedBoundary μ c.2.2) := by
  obtain ⟨p, ν, r⟩ := c
  subst hc
  simp [transferConnection_def, hself.symm]

/-- Relocating a connection outside `{ψ, Δ(ψ)}` leaves it unchanged. -/
theorem transferConnection_of_ne
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h₁ : c.2.1 ≠ ψ) (h₂ : c.2.1 ≠ Ω.dual ψ) :
    Ω.transferConnection μ ψ c = c := by
  obtain ⟨p, ν, r⟩ := c
  simp_all [transferConnection_def]

/-- Relocating a connection commutes with passing to the dual connection
`(c.2.2, Δ(c.2.1), c.1)`. -/
theorem transferConnection_dual
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    Ω.transferConnection μ ψ (c.2.2, Ω.dual c.2.1, c.1) =
      ((Ω.transferConnection μ ψ c).2.2, Ω.dual (Ω.transferConnection μ ψ c).2.1,
        (Ω.transferConnection μ ψ c).1) := by
  simp only [transferConnection_def, Ω.dual_involutive.eq_iff, Ω.dual_involutive ψ]

/-- Relocating connections along `μ` is injective on `Ω.connections` when `Ω` is formally
consistent and every connection through `ψ` has its `ψ`-boundary `μ`-tied. -/
theorem IsFormallyConsistent.injOn_transferConnection (hΩ : Ω.IsFormallyConsistent)
    (hc : ∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q) :
    Set.InjOn (Ω.transferConnection μ ψ) Ω.connections := by
  rintro ⟨p₁, ν₁, r₁⟩ hc₁ ⟨p₂, ν₂, r₂⟩ hc₂ heq
  rw [transferConnection_def, transferConnection_def, Prod.mk.injEq, Prod.mk.injEq] at heq
  obtain ⟨hp, rfl, hr⟩ := heq
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · by_cases h₁ : ν₁ = ψ
    · subst ν₁
      simp only [ite_true] at hp
      exact hΩ.injOn_tiedBoundary (hc _ hc₁ rfl) (hc _ hc₂ rfl) hp
    · simpa [h₁] using hp
  · by_cases h₂ : ν₁ = Ω.dual ψ
    · subst ν₁
      simp only [ite_true] at hr
      have hd₁ : (r₁, ψ, p₁) ∈ Ω.connections := by
        simpa [Ω.dual_involutive ψ] using Ω.dual_mem_connections _ hc₁
      have hd₂ : (r₂, ψ, p₂) ∈ Ω.connections := by
        simpa [Ω.dual_involutive ψ] using Ω.dual_mem_connections _ hc₂
      exact hΩ.injOn_tiedBoundary (hc _ hd₁ rfl) (hc _ hd₂ rfl) hr
    · simpa [h₂] using hr

section Consistent

variable (hΩ : Ω.IsFormallyConsistent) (h : Ω.IsTransferable μ ψ)

include hΩ h in
/-- The transferred left end-point of `ψ` strictly precedes its transferred right end-point. -/
private theorem transferLeft_lt_transferRight :
    (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.left ψ)
      else Ω.tiedBoundary μ (Ω.right ψ)) <
    (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.right ψ)
      else Ω.tiedBoundary μ (Ω.left ψ)) := by
  split_ifs with hs
  · exact hΩ.lt_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right (Ω.left_lt_right ψ)
  · exact hΩ.lt_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right (Ω.left_lt_right ψ)

include hΩ h in
/-- For a boundary connection `(p, ψ, r)` through `ψ`, `tiedBoundary μ p` lies strictly between
the transferred end-points of `ψ`. -/
private theorem transferLeft_lt_tiedBoundary_lt_transferRight
    {p r : Fin (Ω.numItems + 1)} (hc : (p, ψ, r) ∈ Ω.connections) :
    (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.left ψ)
      else Ω.tiedBoundary μ (Ω.right ψ)) < Ω.tiedBoundary μ p ∧
    Ω.tiedBoundary μ p <
      (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.right ψ)
        else Ω.tiedBoundary μ (Ω.left ψ)) := by
  obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc
  have hp_tied := h.isTiedTo_tiedBoundary_of_mem_connections hc rfl
  split_ifs with hs
  · exact ⟨hΩ.lt_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left hp_tied hp₁,
      hΩ.lt_of_isTiedTo_of_sign_eq hs hp_tied h.isTiedTo_tiedBoundary_right hp₂⟩
  · exact ⟨hΩ.lt_of_isTiedTo_of_sign_ne hs hp_tied h.isTiedTo_tiedBoundary_right hp₂,
      hΩ.lt_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left hp_tied hp₁⟩

-- Reducible, so that the items and base indices of the result are reducibly those of `Ω`.
/-- **ET2 (Transferring a base).** Transfer the variable base `ψ` along the carrier `μ` onto `Δ(μ)`:
`ψ` moves to `[tiedBoundary μ α(ψ), tiedBoundary μ β(ψ)]` with sign `ε(ψ)` when `ε(μ) = ε(Δμ)`,
and to `[tiedBoundary μ β(ψ), tiedBoundary μ α(ψ)]` with sign `¬ ε(ψ)` otherwise; boundary
connections through `ψ` and `Δ(ψ)` are relocated by `transferConnection`. -/
abbrev transferBase : GenEq A where
  numItems := Ω.numItems
  numBases := Ω.numBases
  left ν := if ν = ψ then
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.left ψ)
      else Ω.tiedBoundary μ (Ω.right ψ)
    else Ω.left ν
  right ν := if ν = ψ then
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.right ψ)
      else Ω.tiedBoundary μ (Ω.left ψ)
    else Ω.right ν
  left_lt_right ν := by
    by_cases hν : ν = ψ
    · simp only [hν, ite_true]
      exact transferLeft_lt_transferRight hΩ h
    · simp only [hν, ite_false]
      exact Ω.left_lt_right ν
  sign ν := if ν = ψ then
      if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.sign ψ else !Ω.sign ψ
    else Ω.sign ν
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases
  connections := Ω.connections.image (Ω.transferConnection μ ψ)
  bounds_of_mem_connections c' hc' := by
    have hfst : ∀ {p ν r}, (p, ν, r) ∈ Ω.connections →
        (if ν = ψ then if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.left ψ)
            else Ω.tiedBoundary μ (Ω.right ψ) else Ω.left ν) <
          (if ν = ψ then Ω.tiedBoundary μ p else p) ∧
        (if ν = ψ then Ω.tiedBoundary μ p else p) <
          (if ν = ψ then if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.right ψ)
            else Ω.tiedBoundary μ (Ω.left ψ) else Ω.right ν) := by
      intro p ν r hc
      by_cases hν : ν = ψ
      · subst hν
        simpa only [ite_true] using transferLeft_lt_tiedBoundary_lt_transferRight hΩ h hc
      · obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc
        simpa only [hν, ite_false] using ⟨hp₁, hp₂⟩
    obtain ⟨⟨p, ν, r⟩, hc, rfl⟩ := Finset.mem_image.1 hc'
    obtain ⟨h₁, h₂⟩ := hfst hc
    obtain ⟨h₃, h₄⟩ := hfst (p := r) (ν := Ω.dual ν) (r := p) (Ω.dual_mem_connections _ hc)
    simp only [Ω.dual_involutive.eq_iff] at h₃ h₄
    simpa only [transferConnection_fst, transferConnection_snd_fst, transferConnection_snd_snd,
      Ω.dual_involutive.eq_iff] using ⟨h₁, h₂, h₃, h₄⟩
  dual_mem_connections c' hc' := by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hc'
    exact Finset.mem_image.2 ⟨(c.2.2, Ω.dual c.2.1, c.1), Ω.dual_mem_connections c hc,
      Ω.transferConnection_dual c⟩

/-- The left end-point of the transferred base `ψ`. -/
theorem left_transferBase_self : (Ω.transferBase hΩ h).left ψ =
    if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.left ψ)
    else Ω.tiedBoundary μ (Ω.right ψ) :=
  ite_eq_left rfl

/-- The left end-point of any base other than `ψ` is unchanged by `transferBase`. -/
theorem left_transferBase_of_ne {ν : Fin Ω.numBases} (hν : ν ≠ ψ) :
    (Ω.transferBase hΩ h).left ν = Ω.left ν :=
  ite_eq_right hν

/-- The right end-point of the transferred base `ψ`. -/
theorem right_transferBase_self : (Ω.transferBase hΩ h).right ψ =
    if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.tiedBoundary μ (Ω.right ψ)
    else Ω.tiedBoundary μ (Ω.left ψ) :=
  ite_eq_left rfl

/-- The right end-point of any base other than `ψ` is unchanged by `transferBase`. -/
theorem right_transferBase_of_ne {ν : Fin Ω.numBases} (hν : ν ≠ ψ) :
    (Ω.transferBase hΩ h).right ν = Ω.right ν :=
  ite_eq_right hν

/-- The sign of the transferred base `ψ`: unchanged when `ε(μ) = ε(Δμ)`, flipped otherwise. -/
theorem sign_transferBase_self : (Ω.transferBase hΩ h).sign ψ =
    if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.sign ψ else !Ω.sign ψ :=
  ite_eq_left rfl

/-- The sign of any base other than `ψ` is unchanged by `transferBase`. -/
theorem sign_transferBase_of_ne {ν : Fin Ω.numBases} (hν : ν ≠ ψ) :
    (Ω.transferBase hΩ h).sign ν = Ω.sign ν :=
  ite_eq_right hν

/-- When `ψ ≠ Δ(ψ)`, after transferring `ψ` along `μ`, `ψ` and `Δ(ψ)` have equal signs if and only
if their original sign agreement matches that of `μ` and `Δ(μ)`. -/
theorem sign_transferBase_eq_sign_dual_iff (hself : ψ ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).sign ψ = (Ω.transferBase hΩ h).sign (Ω.dual ψ) ↔
      (Ω.sign ψ = Ω.sign (Ω.dual ψ) ↔ Ω.sign μ = Ω.sign (Ω.dual μ)) := by
  rw [sign_transferBase_self, sign_transferBase_of_ne hΩ h hself.symm]
  split_ifs with hs
  · simp [hs]
  · cases Ω.sign ψ <;> cases Ω.sign (Ω.dual ψ) <;> simp [hs]

/-- The transferred base `ψ` starts at or after `α(Δμ)`. -/
theorem left_dual_le_left_transferBase :
    Ω.left (Ω.dual μ) ≤ (Ω.transferBase hΩ h).left ψ := by
  rw [left_transferBase_self]
  split_ifs
  exacts [h.isTiedTo_tiedBoundary_left.left_dual_le, h.isTiedTo_tiedBoundary_right.left_dual_le]

/-- The transferred base `ψ` ends at or before `β(Δμ)`. -/
theorem right_transferBase_le_right_dual :
    (Ω.transferBase hΩ h).right ψ ≤ Ω.right (Ω.dual μ) := by
  rw [right_transferBase_self]
  split_ifs
  exacts [h.isTiedTo_tiedBoundary_right.le_right_dual, h.isTiedTo_tiedBoundary_left.le_right_dual]

/-- Sections `[i, j]` only depend on the items, which `transferBase` keeps. -/
@[simp]
theorem sectionItems_transferBase (i j : ℕ) :
    (Ω.transferBase hΩ h).sectionItems i j = Ω.sectionItems i j := by
  ext k
  simp

/-- After transferring `ψ` along `μ`, the section of `ψ` is contained in `Δ(μ)`. -/
theorem baseItems_transferBase_subset_dual :
    (Ω.transferBase hΩ h).baseItems ψ ⊆ Ω.baseItems (Ω.dual μ) := by
  rw [baseItems_def, baseItems_def, sectionItems_transferBase,
    Ω.sectionItems_subset_sectionItems_iff ((Ω.transferBase hΩ h).left_lt_right ψ)
      ((Ω.transferBase hΩ h).right ψ).is_le]
  exact ⟨left_dual_le_left_transferBase hΩ h, right_transferBase_le_right_dual hΩ h⟩

/-- The section of items of any base other than `ψ` is unchanged by `transferBase`. -/
theorem baseItems_transferBase_of_ne {ν : Fin Ω.numBases} (hν : ν ≠ ψ) :
    (Ω.transferBase hΩ h).baseItems ν = Ω.baseItems ν := by
  simp [baseItems_def, hν]

/-- Transferring `ψ` along `μ` inserts `ψ` into the variable bases containing `hₖ` when `hₖ` lies
in the transferred section of `ψ`, and erases `ψ` otherwise. -/
theorem filter_mem_baseItems_transferBase (k : Fin Ω.numItems) :
    ({ν | k ∈ (Ω.transferBase hΩ h).baseItems ν} : Finset (Fin Ω.numBases)) =
      if k ∈ (Ω.transferBase hΩ h).baseItems ψ then
        insert ψ ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases))
      else
        ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases)).erase ψ := by
  ext ν
  split_ifs with hk
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hν : ν = ψ
    · subst ν
      exact ⟨fun _ => Or.inl rfl, fun _ => hk⟩
    · rw [baseItems_transferBase_of_ne hΩ h hν]
      exact ⟨Or.inr, fun h' => h'.resolve_left hν⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hν : ν = ψ
    · subst ν
      exact ⟨fun hmem => absurd hmem hk, fun h' => absurd rfl h'.1⟩
    · rw [baseItems_transferBase_of_ne hΩ h hν]
      exact ⟨fun hmem => ⟨hν, hmem⟩, And.right⟩

/-- If `hₖ` belongs to `ψ` in `Ω` but not in `Ω.transferBase hΩ h`, transferring `ψ` along `μ`
decreases its degree by `1`. -/
theorem degree_transferBase_add_one {k : Fin Ω.numItems} (hkψ : k ∈ Ω.baseItems ψ)
    (hk : k ∉ (Ω.transferBase hΩ h).baseItems ψ) :
    (Ω.transferBase hΩ h).degree k + 1 = Ω.degree k := by
  have hmem : ψ ∈ ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases)) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hkψ⟩
  rw [degree_def, degree_def, filter_mem_baseItems_transferBase hΩ h k, ite_eq_right hk,
    add_right_comm, Finset.card_erase_add_one hmem]

/-- If `hₖ` belongs to `ψ` in `Ω.transferBase hΩ h` but not in `Ω`, transferring `ψ` along `μ`
increases its degree by `1`. -/
theorem degree_transferBase_eq_degree_add_one {k : Fin Ω.numItems} (hkψ : k ∉ Ω.baseItems ψ)
    (hk : k ∈ (Ω.transferBase hΩ h).baseItems ψ) :
    (Ω.transferBase hΩ h).degree k = Ω.degree k + 1 := by
  have hnotMem : ψ ∉ ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases)) :=
    fun hmem => hkψ (Finset.mem_filter.1 hmem).2
  rw [degree_def, degree_def, filter_mem_baseItems_transferBase hΩ h k, ite_eq_left hk,
    Finset.card_insert_of_notMem hnotMem, add_right_comm]

/-- If `hₖ` belongs to `ψ` neither in `Ω` nor in `Ω.transferBase hΩ h`, transferring `ψ` along `μ`
leaves its degree unchanged. -/
theorem degree_transferBase_of_notMem {k : Fin Ω.numItems} (hkψ : k ∉ Ω.baseItems ψ)
    (hk : k ∉ (Ω.transferBase hΩ h).baseItems ψ) :
    (Ω.transferBase hΩ h).degree k = Ω.degree k := by
  have hnotMem : ψ ∉ ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases)) :=
    fun hmem => hkψ (Finset.mem_filter.1 hmem).2
  rw [degree_def, degree_def, filter_mem_baseItems_transferBase hΩ h k, ite_eq_right hk,
    Finset.erase_eq_of_notMem hnotMem]

/-- If `hₖ` belongs to `ψ` both in `Ω` and in `Ω.transferBase hΩ h`, transferring `ψ` along `μ`
leaves its degree unchanged. -/
theorem degree_transferBase_of_mem {k : Fin Ω.numItems} (hkψ : k ∈ Ω.baseItems ψ)
    (hk : k ∈ (Ω.transferBase hΩ h).baseItems ψ) :
    (Ω.transferBase hΩ h).degree k = Ω.degree k := by
  have hmem : ψ ∈ ({ν | k ∈ Ω.baseItems ν} : Finset (Fin Ω.numBases)) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hkψ⟩
  rw [degree_def, degree_def, filter_mem_baseItems_transferBase hΩ h k, ite_eq_left hk,
    Finset.insert_eq_of_mem hmem]

/-- Transferring `ψ` along `μ` preserves the degree of `hₖ` if and only if `hₖ` belongs to the
transferred section of `ψ` exactly when it belongs to `ψ` in `Ω`. -/
theorem degree_transferBase_eq_degree_iff {k : Fin Ω.numItems} :
    (Ω.transferBase hΩ h).degree k = Ω.degree k ↔
      (k ∈ (Ω.transferBase hΩ h).baseItems ψ ↔ k ∈ Ω.baseItems ψ) := by
  by_cases hk : k ∈ (Ω.transferBase hΩ h).baseItems ψ <;> by_cases hkψ : k ∈ Ω.baseItems ψ
  · exact iff_of_true (degree_transferBase_of_mem hΩ h hkψ hk) ⟨fun _ => hkψ, fun _ => hk⟩
  · have hdeg := degree_transferBase_eq_degree_add_one hΩ h hkψ hk
    exact iff_of_false (by omega) (fun hiff => hkψ (hiff.1 hk))
  · have hdeg := degree_transferBase_add_one hΩ h hkψ hk
    exact iff_of_false (by omega) (fun hiff => hk (hiff.2 hkψ))
  · exact iff_of_true (degree_transferBase_of_notMem hΩ h hkψ hk)
      ⟨fun h' => absurd h' hk, fun h' => absurd h' hkψ⟩

/-- Transferring a variable base preserves constant items. -/
@[simp]
theorem isConstantItem_transferBase {k : Fin Ω.numItems} :
    (Ω.transferBase hΩ h).IsConstantItem k ↔ Ω.IsConstantItem k := by
  simp only [isConstantItem_iff]

/-- Transferring a variable base preserves free items: the carrier `μ` and its dual `Δ(μ)` still
cover the old and new sections of `ψ`. -/
@[simp]
theorem isFreeItem_transferBase {k : Fin Ω.numItems} :
    (Ω.transferBase hΩ h).IsFreeItem k ↔ Ω.IsFreeItem k := by
  simp only [isFreeItem_iff, isConstantItem_transferBase]
  refine and_congr_left fun _ => ⟨fun hk ν => ?_, fun hk ν => ?_⟩
  · by_cases hν : ν = ψ
    · subst ν
      exact fun hm => (baseItems_transferBase_of_ne hΩ h h.ne_carrier.symm ▸ hk μ)
        (h.baseItems_subset hm)
    · exact baseItems_transferBase_of_ne hΩ h hν ▸ hk ν
  · by_cases hν : ν = ψ
    · subst ν
      exact fun hm => hk (Ω.dual μ) (baseItems_transferBase_subset_dual hΩ h hm)
    · exact (baseItems_transferBase_of_ne hΩ h hν).symm ▸ hk ν

/-- Transferring a variable base preserves open boundaries: any boundary crossing `ψ` before or
after the transfer also crosses `μ` or `Δ(μ)`. -/
@[simp]
theorem isOpenBoundary_transferBase {i : Fin (Ω.numItems + 1)} :
    (Ω.transferBase hΩ h).IsOpenBoundary i ↔ Ω.IsOpenBoundary i := by
  rw [isOpenBoundary_iff, isOpenBoundary_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨ν, hνc⟩
    rw [crosses_iff] at hνc
    by_cases hν : ν = ψ
    · subst ν
      exact ⟨Ω.dual μ, (crosses_iff _).2 ⟨(left_dual_le_left_transferBase hΩ h).trans_lt hνc.1,
        hνc.2.trans_le (right_transferBase_le_right_dual hΩ h)⟩⟩
    · rw [left_transferBase_of_ne hΩ h hν, right_transferBase_of_ne hΩ h hν] at hνc
      exact ⟨ν, (crosses_iff _).2 hνc⟩
  · rintro ⟨ν, hνc⟩
    rw [crosses_iff] at hνc
    by_cases hν : ν = ψ
    · subst ν
      refine ⟨μ, (crosses_iff _).2 ?_⟩
      rw [left_transferBase_of_ne hΩ h h.ne_carrier.symm,
        right_transferBase_of_ne hΩ h h.ne_carrier.symm]
      exact ⟨h.left_le.trans_lt hνc.1, hνc.2.trans_le h.right_le⟩
    · refine ⟨ν, (crosses_iff _).2 ?_⟩
      rwa [left_transferBase_of_ne hΩ h hν, right_transferBase_of_ne hΩ h hν]

/-- Transferring a variable base preserves closed boundaries. -/
@[simp]
theorem isClosedBoundary_transferBase {i : Fin (Ω.numItems + 1)} :
    (Ω.transferBase hΩ h).IsClosedBoundary i ↔ Ω.IsClosedBoundary i := by
  rw [← not_isOpenBoundary, ← not_isOpenBoundary, isOpenBoundary_transferBase]

/-- Transferring a variable base preserves closed sections. -/
@[simp]
theorem isClosedSection_transferBase {i j : Fin (Ω.numItems + 1)} :
    (Ω.transferBase hΩ h).IsClosedSection i j ↔ Ω.IsClosedSection i j := by
  simp only [isClosedSection_iff, isClosedBoundary_transferBase, isOpenBoundary_transferBase]

/-- Transferring a variable base preserves the set `Σ_Ω` of closed sections. -/
@[simp]
theorem closedSections_transferBase :
    (Ω.transferBase hΩ h).closedSections = Ω.closedSections := by
  ext s
  simp

/-- Transferring a variable base preserves the closed section of every item. -/
@[simp]
theorem closedSectionOfItem_transferBase (k : Fin Ω.numItems) :
    (Ω.transferBase hΩ h).closedSectionOfItem k = Ω.closedSectionOfItem k := by
  rw [closedSectionOfItem_eq_iff, closedSections_transferBase, sectionItems_transferBase]
  exact Ω.closedSectionOfItem_eq_iff.1 rfl

/-- After transferring `ψ` along `μ`, the closed section of `ψ` is the closed section of `Δ(μ)`. -/
@[simp]
theorem closedSectionOfBase_transferBase_self :
    (Ω.transferBase hΩ h).closedSectionOfBase ψ = Ω.closedSectionOfBase (Ω.dual μ) := by
  rw [closedSectionOfBase_eq_iff, closedSections_transferBase, sectionItems_transferBase]
  exact ⟨Ω.closedSectionOfBase_mem_closedSections (Ω.dual μ),
    (baseItems_transferBase_subset_dual hΩ h).trans
      (Ω.baseItems_subset_sectionItems_closedSectionOfBase (Ω.dual μ))⟩

/-- Transferring `ψ` along `μ` preserves the closed section of every variable base other than
`ψ`. -/
theorem closedSectionOfBase_transferBase_of_ne {ν : Fin Ω.numBases} (hν : ν ≠ ψ) :
    (Ω.transferBase hΩ h).closedSectionOfBase ν = Ω.closedSectionOfBase ν := by
  rw [closedSectionOfBase_eq_iff, closedSections_transferBase, sectionItems_transferBase,
    baseItems_transferBase_of_ne hΩ h hν]
  exact Ω.closedSectionOfBase_eq_iff.1 rfl

/-- The boundary connections of `Ω.transferBase hΩ h` are obtained by applying
`transferConnection μ ψ` to the connections of `Ω`. -/
theorem connections_transferBase :
    (Ω.transferBase hΩ h).connections = Ω.connections.image (Ω.transferConnection μ ψ) :=
  (rfl)

/-- Membership in the boundary connections of `Ω.transferBase hΩ h`. -/
theorem mem_connections_transferBase
    {c' : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} :
    c' ∈ (Ω.transferBase hΩ h).connections ↔
      ∃ c ∈ Ω.connections, Ω.transferConnection μ ψ c = c' := by
  rw [connections_transferBase, Finset.mem_image]

/-- Away from `{ψ, Δ(ψ)}`, `transferBase` leaves membership in `connections` unchanged. -/
theorem mem_connections_transferBase_of_ne
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h₁ : c.2.1 ≠ ψ) (h₂ : c.2.1 ≠ Ω.dual ψ) :
    c ∈ (Ω.transferBase hΩ h).connections ↔ c ∈ Ω.connections := by
  rw [mem_connections_transferBase]
  refine ⟨?_, fun hc => ⟨c, hc, transferConnection_of_ne h₁ h₂⟩⟩
  rintro ⟨c₀, hc₀, rfl⟩
  rw [transferConnection_snd_fst] at h₁ h₂
  rwa [transferConnection_of_ne h₁ h₂]

/-- Transferring a base preserves the number of boundary connections. -/
theorem card_connections_transferBase :
    (Ω.transferBase hΩ h).connections.card = Ω.connections.card := by
  rw [connections_transferBase]
  exact Finset.card_image_of_injOn
    (hΩ.injOn_transferConnection h.exists_isTiedTo_of_mem_connections)

/-- Away from `{ψ, Δ(ψ)}`, `transferBase` preserves ties. -/
theorem isTiedTo_transferBase_of_ne {ν : Fin Ω.numBases} {p q : Fin (Ω.numItems + 1)}
    (h₁ : ν ≠ ψ) (h₂ : ν ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).IsTiedTo ν p q ↔ Ω.IsTiedTo ν p q := by
  have hd : Ω.dual ν ≠ ψ := mt Ω.dual_involutive.eq_iff.1 h₂
  simp [isTiedTo_iff, mem_connections_transferBase_of_ne hΩ h (c := (p, ν, q)) h₁ h₂, h₁, hd]

/-- Away from `{ψ, Δ(ψ)}`, `transferBase` leaves `tiedBoundary` unchanged. -/
theorem tiedBoundary_transferBase_of_ne {ν : Fin Ω.numBases} (p : Fin (Ω.numItems + 1))
    (h₁ : ν ≠ ψ) (h₂ : ν ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).tiedBoundary ν p = Ω.tiedBoundary ν p := by
  by_cases hex : ∃ q, Ω.IsTiedTo ν p q
  · have hex' : ∃ q, (Ω.transferBase hΩ h).IsTiedTo ν p q := by
      simpa only [isTiedTo_transferBase_of_ne hΩ h h₁ h₂] using hex
    have ht := (isTiedTo_transferBase_of_ne hΩ h h₁ h₂).1 (isTiedTo_tiedBoundary_iff.2 hex')
    exact (hΩ.tiedBoundary_eq ht).symm
  · have hex' : ¬ ∃ q, (Ω.transferBase hΩ h).IsTiedTo ν p q := by
      simpa only [isTiedTo_transferBase_of_ne hΩ h h₁ h₂] using hex
    rw [tiedBoundary_of_not_exists hex', tiedBoundary_of_not_exists hex]

/-- For any carrier `μ' ∉ {ψ, Δ(ψ)}` and any base `ψ' ≠ ψ`, transferability of `ψ'` along `μ'`
in `Ω.transferBase hΩ h` is equivalent to transferability of `ψ'` along `μ'` in `Ω`. -/
theorem isTransferable_transferBase_of_ne {μ' ψ' : Fin Ω.numBases}
    (hμ'₁ : μ' ≠ ψ) (hμ'₂ : μ' ≠ Ω.dual ψ) (hne : ψ' ≠ ψ) :
    (Ω.transferBase hΩ h).IsTransferable μ' ψ' ↔ Ω.IsTransferable μ' ψ' := by
  have htied : ∀ {p q}, (Ω.transferBase hΩ h).IsTiedTo μ' p q ↔ Ω.IsTiedTo μ' p q :=
    isTiedTo_transferBase_of_ne hΩ h hμ'₁ hμ'₂
  rw [isTransferable_iff, isTransferable_iff, left_transferBase_of_ne hΩ h hne,
    right_transferBase_of_ne hΩ h hne]
  refine and_congr_right fun _ => and_congr_right fun _ =>
    and_congr (exists_congr fun _ => htied) <|
      and_congr (exists_congr fun _ => htied) ?_
  rw [connections_transferBase, Finset.forall_mem_image]
  refine forall₂_congr fun c _ => ?_
  rw [transferConnection_snd_fst]
  refine imp_congr_right fun hc => ?_
  rw [transferConnection_fst, ite_eq_right (hc ▸ hne)]
  exact exists_congr fun _ => htied

end Consistent

/-- Transferring `ψ` along `μ` preserves transferability of any other base `ψ' ≠ ψ` along `μ`. -/
theorem IsTransferable.transferBase {ψ' : Fin Ω.numBases} (h' : Ω.IsTransferable μ ψ')
    (hΩ : Ω.IsFormallyConsistent) (h : Ω.IsTransferable μ ψ) (hne : ψ' ≠ ψ) :
    (Ω.transferBase hΩ h).IsTransferable μ ψ' :=
  (isTransferable_transferBase_of_ne hΩ h h.ne_carrier.symm h.dual_ne_carrier.symm hne).2 h'

end TransferBase

end GenEq

end TauCeti
