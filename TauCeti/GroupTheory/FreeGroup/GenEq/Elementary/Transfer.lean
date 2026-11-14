/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
public import TauCeti.GroupTheory.FreeGroup.GenEq.Tied
public import TauCeti.GroupTheory.FreeGroup.GenEq.Transformation
import Mathlib.Data.Fin.VecNotation

/-!
# Transferring a base of a generalised equation

The elementary transformation ET2 of Makanin's process (Kharlampovich–Myasnikov, §5.1) transfers a
variable base `ψ` contained in a *carrier* base `μ` onto the dual base `Δ(μ)`. It applies when `ψ`
is not its own dual, differs from `μ` and `Δ(μ)`, has both end-points `α(ψ), β(ψ)` tied through
`μ`, and has every boundary connection `(p, ψ, r)` tied through `μ` at `p`
(`TauCeti.GenEq.IsTransferable`).

In a formally consistent generalised equation `Ω`, the function `tiedBoundary μ` is strictly
increasing on the `μ`-tied boundaries when `ε(μ) = ε(Δμ)` and strictly decreasing on the `μ`-tied
boundaries when `ε(μ) ≠ ε(Δμ)`. Writing `q_l = tiedBoundary μ α(ψ)` and
`q_r = tiedBoundary μ β(ψ)`, the result `Ω′ = Ω.transferBase hΩ h`
keeps the items, constant bases and base indices of `Ω`, leaves every base other than `ψ` at its
place, and moves `ψ` onto `Δ(μ)`:

* when `ε(μ) = ε(Δμ)`, `ψ` spans `[q_l, q_r]` with the same sign `ε(ψ)`;
* when `ε(μ) ≠ ε(Δμ)`, `ψ` spans `[q_r, q_l]` with the opposite sign `¬ ε(ψ)`;
* every boundary connection `(p, ψ, r)` is relocated to `(tiedBoundary μ p, ψ, r)`, and its dual
  `(r, Δψ, p)` to `(r, Δψ, tiedBoundary μ p)`.

Because `μ` and `Δ(μ)` are distinct from `ψ` and `Δ(ψ)`, the basic equation of `μ` and all
boundary equations through `μ` belong to both `Ω` and `Ω′`, and identify each segment between
`μ`-tied boundaries with the corresponding segment of `Δ(μ)` (or its inverse). Consequently:

* `Ω*` and `Ω′*` have the same points in every `F(A)`-group
  (`TauCeti.GenEq.V_toSystem_transferBase`), so the identity on the items induces an
  `F(A)`-isomorphism `F_{R(Ω)} → F_{R(Ω′)}` (`TauCeti.GenEq.transferBaseHom`,
  `TauCeti.GenEq.transferBaseHom_bijective`);
* `Ω` and `Ω′` have the exact same graphical solutions, with the same words
  (`TauCeti.GenEq.solutionEquivTransferBase`): unlike the removal of a matched pair (ET3), no
  reducedness condition is lost because the covering bases `μ` and `Δ(μ)` remain in both equations;
* if `Ω` has a solution then `Ω′` is formally consistent
  (`TauCeti.GenEq.isFormallyConsistent_transferBase_of_nonempty_solution`); without a solution,
  flipping the sign of `ψ` across an opposite-sign carrier can place `ψ` over `Δ(ψ)` with opposite
  sign and break formal consistency, as shown in the examples at the end of the file;
* keeping `Ω′` when it is formally consistent packages ET2 as a transformation of `Ω` that
  transfers solutions uniquely (`TauCeti.GenEq.transferBaseTransformation`,
  `TauCeti.GenEq.transfersUniquely_transferBaseTransformation`).

## Main definitions

* `TauCeti.GenEq.IsTransferable`: applicability of ET2 to a carrier `μ` and a transfer base `ψ`,
  with a `Decidable` instance.
* `TauCeti.GenEq.transferConnection`: relocation of boundary connections when transferring `ψ`
  along `μ`.
* `TauCeti.GenEq.transferBase`: the generalised equation obtained by transferring `ψ` along `μ`.
* `TauCeti.GenEq.transferBaseHom`: the `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of coordinate
  groups induced by the identity on the items.
* `TauCeti.GenEq.solutionEquivTransferBase`: equivalence between the graphical solutions of `Ω`
  and those of `Ω.transferBase hΩ h`.
* `TauCeti.GenEq.transferBaseTransformation`: ET2 as a `TauCeti.GenEq.Transformation`.

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
* `TauCeti.GenEq.isTransferable_transferBase_of_ne`: for `ψ' ≠ ψ`, transferability along `μ` is
  preserved and reflected by transferring `ψ` along `μ`.
* `TauCeti.GenEq.card_connections_transferBase`: transferring a base preserves the number of
  boundary connections.
* `TauCeti.GenEq.V_toSystem_transferBase`: ET2 preserves the points of `Ω*` in every `F(A)`-group.
* `TauCeti.GenEq.transferBaseHom_bijective`: `transferBaseHom` is an isomorphism of coordinate
  groups.
* `TauCeti.GenEq.toHom_comp_transferBaseHom_eq_iff`: ET2 transfers solutions uniquely along
  `transferBaseHom`.
* `TauCeti.GenEq.transfersUniquely_transferBaseTransformation`: `transferBaseTransformation`
  transfers solutions uniquely.

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

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars)

variable {A : Type*}

/-! ### Transferability of a base along a carrier -/

section IsTransferable

variable (Ω : GenEq A)

/-- The variable base `ψ` can be transferred along the carrier base `μ` (ET2,
Kharlampovich–Myasnikov, §5.1): `ψ` is not its own dual and differs from `μ` and `Δ(μ)`, both
end-points of `ψ` are `μ`-tied (which forces `σ(ψ) ⊆ σ(μ)`), and every boundary connection through
`ψ` has its `ψ`-boundary `μ`-tied. -/
structure IsTransferable (μ ψ : Fin Ω.numBases) : Prop where
  /-- The transfer base is not its own dual. -/
  ne_dual_self : ψ ≠ Ω.dual ψ
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
    Ω.IsTransferable μ ψ ↔ ψ ≠ Ω.dual ψ ∧ ψ ≠ μ ∧ ψ ≠ Ω.dual μ ∧
      (∃ q, Ω.IsTiedTo μ (Ω.left ψ) q) ∧ (∃ q, Ω.IsTiedTo μ (Ω.right ψ) q) ∧
      ∀ c ∈ Ω.connections, c.2.1 = ψ → ∃ q, Ω.IsTiedTo μ c.1 q :=
  ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
    fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩⟩

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

/-- A base `ψ` with the same end-points as `μ`, distinct from `Δ(ψ)`, `μ` and `Δ(μ)`, and carrying
no boundary connections is transferable along `μ`: its end-points are tied as end-points of `μ`. -/
theorem IsTransferable.of_endpoints_eq (hl : Ω.left ψ = Ω.left μ) (hr : Ω.right ψ = Ω.right μ)
    (hself : ψ ≠ Ω.dual ψ) (hμ : ψ ≠ μ) (hdμ : ψ ≠ Ω.dual μ)
    (hc : ∀ c ∈ Ω.connections, c.2.1 ≠ ψ) : Ω.IsTransferable μ ψ where
  ne_dual_self := hself
  ne_carrier := hμ
  ne_dual_carrier := hdμ
  exists_isTiedTo_left := hl ▸ ⟨_, Ω.isTiedTo_left⟩
  exists_isTiedTo_right := hr ▸ ⟨_, Ω.isTiedTo_right⟩
  exists_isTiedTo_of_mem_connections c hmem hψ := absurd hψ (hc c hmem)

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
    obtain ⟨⟨p, ν, r⟩, hc, rfl⟩ := Finset.mem_image.1 hc'
    by_cases hν : ν = ψ
    · subst hν
      rw [transferConnection_of_eq h.ne_dual_self rfl]
      obtain ⟨-, -, hr₁, hr₂⟩ := Ω.bounds_of_mem_connections _ hc
      obtain ⟨hq₁, hq₂⟩ := transferLeft_lt_tiedBoundary_lt_transferRight hΩ h hc
      simpa [h.ne_dual_self.symm] using ⟨hq₁, hq₂, hr₁, hr₂⟩
    · by_cases hν' : ν = Ω.dual ψ
      · subst hν'
        rw [transferConnection_of_eq_dual h.ne_dual_self rfl]
        obtain ⟨hp₁, hp₂, -, -⟩ := Ω.bounds_of_mem_connections _ hc
        have hc_dual : (r, ψ, p) ∈ Ω.connections := by
          simpa [Ω.dual_involutive ψ] using Ω.dual_mem_connections _ hc
        obtain ⟨hq₁, hq₂⟩ := transferLeft_lt_tiedBoundary_lt_transferRight hΩ h hc_dual
        simpa [h.ne_dual_self.symm, Ω.dual_involutive ψ] using ⟨hp₁, hp₂, hq₁, hq₂⟩
      · rw [transferConnection_of_ne hν hν']
        have hdν : Ω.dual ν ≠ ψ := mt Ω.dual_involutive.eq_iff.1 hν'
        simpa [hν, hdν] using Ω.bounds_of_mem_connections _ hc
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

/-- Membership in the boundary connections of `Ω.transferBase hΩ h`. -/
theorem mem_connections_transferBase
    {c' : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} :
    c' ∈ (Ω.transferBase hΩ h).connections ↔
      ∃ c ∈ Ω.connections, Ω.transferConnection μ ψ c = c' :=
  Finset.mem_image

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
    (Ω.transferBase hΩ h).connections.card = Ω.connections.card :=
  Finset.card_image_of_injOn (hΩ.injOn_transferConnection h.exists_isTiedTo_of_mem_connections)

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

/-- For any base `ψ' ≠ ψ`, transferability along `μ` in `Ω.transferBase hΩ h` is equivalent to
transferability along `μ` in `Ω`. -/
theorem isTransferable_transferBase_of_ne {ψ' : Fin Ω.numBases} (hne : ψ' ≠ ψ) :
    (Ω.transferBase hΩ h).IsTransferable μ ψ' ↔ Ω.IsTransferable μ ψ' := by
  have htied : ∀ {p q}, (Ω.transferBase hΩ h).IsTiedTo μ p q ↔ Ω.IsTiedTo μ p q :=
    isTiedTo_transferBase_of_ne hΩ h h.ne_carrier.symm h.dual_ne_carrier.symm
  rw [isTransferable_iff, isTransferable_iff, left_transferBase_of_ne hΩ h hne,
    right_transferBase_of_ne hΩ h hne]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr (exists_congr fun _ => htied) <|
      and_congr (exists_congr fun _ => htied) ?_
  rw [show (Ω.transferBase hΩ h).connections = Ω.connections.image (Ω.transferConnection μ ψ)
    from rfl, Finset.forall_mem_image]
  refine forall₂_congr fun c _ => ?_
  rw [transferConnection_snd_fst]
  refine imp_congr_right fun hc => ?_
  rw [transferConnection_fst, ite_eq_right (hc ▸ hne)]
  exact exists_congr fun _ => htied

/-! ### Equations and group solutions -/

/-- The segments `h[i, j] ^ ±1` only depend on the items, which `transferBase` keeps. -/
@[simp]
theorem segment_transferBase (i j : ℕ) (s : Bool) :
    (Ω.transferBase hΩ h).segment i j s = Ω.segment i j s := by
  cases s <;> simp only [segment_false, segment_true]

/-- Transferring a variable base keeps the coefficient equations. -/
@[simp]
theorem coeffEquation_transferBase (b : Fin Ω.numItems × (A × Bool)) :
    (Ω.transferBase hΩ h).coeffEquation b = Ω.coeffEquation b :=
  Prod.ext (by simp) (by simp)

/-- The basic equation of any base outside `{ψ, Δ(ψ)}` is unchanged by `transferBase`. -/
theorem basicEquation_transferBase_of_ne {ν : Fin Ω.numBases} (h₁ : ν ≠ ψ) (h₂ : ν ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).basicEquation ν = Ω.basicEquation ν := by
  have hd : Ω.dual ν ≠ ψ := mt Ω.dual_involutive.eq_iff.1 h₂
  exact Prod.ext (by simp [h₁]) (by simp [hd])

/-- The boundary equation of any triple outside `{ψ, Δ(ψ)}` is unchanged by `transferBase`. -/
theorem boundaryEquation_transferBase_of_ne
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)}
    (h₁ : c.2.1 ≠ ψ) (h₂ : c.2.1 ≠ Ω.dual ψ) :
    (Ω.transferBase hΩ h).boundaryEquation c = Ω.boundaryEquation c := by
  have hd : Ω.dual c.2.1 ≠ ψ := mt Ω.dual_involutive.eq_iff.1 h₂
  refine Prod.ext (by simp [h₁]) ?_
  by_cases hs : Ω.sign c.2.1 = Ω.sign (Ω.dual c.2.1) <;>
    simp [boundaryEquation_snd_of_sign_eq, boundaryEquation_snd_of_sign_ne, h₁, hd, hs]

/-- Under any group assignment satisfying the basic and boundary equations of the carrier `μ`, the
transferred segment of `ψ` evaluates to the same group element as the original segment of `ψ`. -/
private theorem lift_mk_segment_transferBase_self {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2)) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).segment
        ((Ω.transferBase hΩ h).left ψ) ((Ω.transferBase hΩ h).right ψ)
        ((Ω.transferBase hΩ h).sign ψ))) =
      FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left ψ) (Ω.right ψ) (Ω.sign ψ))) := by
  rw [segment_transferBase, left_transferBase_self, right_transferBase_self, sign_transferBase_self,
    Ω.lift_mk_segment f _ _ (if Ω.sign μ = Ω.sign (Ω.dual μ) then Ω.sign ψ else !Ω.sign ψ),
    Ω.lift_mk_segment f _ _ (Ω.sign ψ)]
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · simp only [hs, ite_true]
    rw [hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl)]
  · simp only [hs, ite_false]
    rw [hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left
      h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl)]
    cases Ω.sign ψ <;>
      simp only [Bool.not_false, Bool.not_true, Bool.cond_false, Bool.cond_true, inv_inv]

/-- Under any group assignment satisfying the equations of `μ`, every basic equation of
`Ω.transferBase hΩ h` has the exact same side values in the group as the corresponding basic
equation of `Ω`. -/
private theorem lift_mk_basicEquation_transferBase_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    (ν : Fin Ω.numBases) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).basicEquation ν).2) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).2) := by
  have hside : ∀ κ : Fin Ω.numBases,
      FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).segment
          ((Ω.transferBase hΩ h).left κ) ((Ω.transferBase hΩ h).right κ)
          ((Ω.transferBase hΩ h).sign κ))) =
        FreeGroup.lift f (FreeGroup.mk (Ω.segment (Ω.left κ) (Ω.right κ) (Ω.sign κ))) := by
    intro κ
    by_cases hκ : κ = ψ
    · exact hκ ▸ lift_mk_segment_transferBase_self hΩ h f hb hc
    · rw [segment_transferBase, left_transferBase_of_ne hΩ h hκ, right_transferBase_of_ne hΩ h hκ,
        sign_transferBase_of_ne hΩ h hκ]
  simp only [basicEquation_fst, basicEquation_snd]
  rw [hside ν, hside (Ω.dual ν)]

/-- Under any group assignment satisfying the equations of `μ`, the relocated dual connection
`(p, Δψ, tiedBoundary μ r)` has the same right-hand side value in `Ω.transferBase hΩ h` as
`(p, Δψ, r)` in `Ω`. -/
private theorem lift_mk_boundaryEquation_snd_transferConnection_dual {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hb : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hc : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    {p r : Fin (Ω.numItems + 1)} (hc_mem : (p, Ω.dual ψ, r) ∈ Ω.connections) :
    FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
        (p, Ω.dual ψ, Ω.tiedBoundary μ r)).2) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).2) := by
  have hd_mem : (r, ψ, p) ∈ Ω.connections := by
    simpa [Ω.dual_involutive ψ] using Ω.dual_mem_connections _ hc_mem
  have hr_tied := h.isTiedTo_tiedBoundary_of_mem_connections hd_mem rfl
  have hd_ne : Ω.dual ψ ≠ ψ := h.ne_dual_self.symm
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · by_cases hsψ : Ω.sign (Ω.dual ψ) = Ω.sign ψ
    · have hsψ' : (Ω.transferBase hΩ h).sign (Ω.dual ψ) =
          (Ω.transferBase hΩ h).sign (Ω.dual (Ω.dual ψ)) := by
        simp [Ω.dual_involutive ψ, hd_ne, hs, hsψ]
      rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_eq hsψ',
        Ω.boundaryEquation_snd_of_sign_eq (by rwa [Ω.dual_involutive ψ]),
        Ω.dual_involutive ψ, segment_transferBase, left_transferBase_self, ite_eq_left hs]
      exact (hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs h.isTiedTo_tiedBoundary_left hr_tied
        hb (hc _ · rfl) (hc _ · rfl)).symm
    · have hsψ' : (Ω.transferBase hΩ h).sign (Ω.dual ψ) ≠
          (Ω.transferBase hΩ h).sign (Ω.dual (Ω.dual ψ)) := by
        cases h₁ : Ω.sign (Ω.dual ψ) <;> cases h₂ : Ω.sign ψ <;>
          simp_all [Ω.dual_involutive ψ]
      rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_ne hsψ',
        Ω.boundaryEquation_snd_of_sign_ne (by rwa [Ω.dual_involutive ψ]),
        Ω.dual_involutive ψ, segment_transferBase, right_transferBase_self, ite_eq_left hs,
        Ω.lift_mk_segment_false, Ω.lift_mk_segment_false, inv_inj]
      exact (hΩ.lift_mk_segment_eq_of_isTiedTo_of_sign_eq hs hr_tied h.isTiedTo_tiedBoundary_right
        hb (hc _ · rfl) (hc _ · rfl)).symm
  · by_cases hsψ : Ω.sign (Ω.dual ψ) = Ω.sign ψ
    · have hsψ' : (Ω.transferBase hΩ h).sign (Ω.dual ψ) ≠
          (Ω.transferBase hΩ h).sign (Ω.dual (Ω.dual ψ)) := by
        cases h₁ : Ω.sign (Ω.dual ψ) <;> cases h₂ : Ω.sign ψ <;>
          simp_all [Ω.dual_involutive ψ]
      rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_ne hsψ',
        Ω.boundaryEquation_snd_of_sign_eq (by rwa [Ω.dual_involutive ψ]),
        Ω.dual_involutive ψ, segment_transferBase, right_transferBase_self, ite_eq_right hs,
        Ω.lift_mk_segment_false]
      exact (hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs h.isTiedTo_tiedBoundary_left
        hr_tied hb (hc _ · rfl) (hc _ · rfl)).symm
    · have hsψ' : (Ω.transferBase hΩ h).sign (Ω.dual ψ) =
          (Ω.transferBase hΩ h).sign (Ω.dual (Ω.dual ψ)) := by
        cases h₁ : Ω.sign (Ω.dual ψ) <;> cases h₂ : Ω.sign ψ <;>
          simp_all [Ω.dual_involutive ψ]
      rw [(Ω.transferBase hΩ h).boundaryEquation_snd_of_sign_eq hsψ',
        Ω.boundaryEquation_snd_of_sign_ne (by rwa [Ω.dual_involutive ψ]),
        Ω.dual_involutive ψ, segment_transferBase, left_transferBase_self, ite_eq_right hs,
        Ω.lift_mk_segment_false,
        hΩ.lift_mk_segment_eq_inv_of_isTiedTo_of_sign_ne hs hr_tied
          h.isTiedTo_tiedBoundary_right hb (hc _ · rfl) (hc _ · rfl),
        inv_inv]

/-- Under any group assignment satisfying the equations of `μ` and the basic equation of `ψ`, every
relocated connection `transferConnection μ ψ c` holds in `Ω.transferBase hΩ h` if and only if `c`
holds in `Ω`. -/
private theorem lift_mk_boundaryEquation_transferConnection_iff {H : Type*} [Group H]
    (f : Fin Ω.numItems ⊕ A → H)
    (hbμ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2))
    (hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2))
    (hbψ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ψ).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ψ).2))
    {c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)} (hc : c ∈ Ω.connections) :
    FreeGroup.lift f (FreeGroup.mk
        ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ c)).1) =
      FreeGroup.lift f (FreeGroup.mk
        ((Ω.transferBase hΩ h).boundaryEquation (Ω.transferConnection μ ψ c)).2) ↔
    FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) := by
  have hdual : ∀ {p r : Fin (Ω.numItems + 1)}, (p, Ω.dual ψ, r) ∈ Ω.connections →
      (FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
          (Ω.transferConnection μ ψ (p, Ω.dual ψ, r))).1) =
        FreeGroup.lift f (FreeGroup.mk ((Ω.transferBase hΩ h).boundaryEquation
          (Ω.transferConnection μ ψ (p, Ω.dual ψ, r))).2) ↔
      FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation (p, Ω.dual ψ, r)).2)) := by
    intro p r hmem
    rw [transferConnection_of_eq_dual h.ne_dual_self rfl, boundaryEquation_fst,
      segment_transferBase, left_transferBase_of_ne hΩ h h.ne_dual_self.symm,
      ← Ω.boundaryEquation_fst (c := (p, Ω.dual ψ, r)),
      lift_mk_boundaryEquation_snd_transferConnection_dual hΩ h f hbμ hcμ hmem]
  obtain ⟨p, ν, r⟩ := c
  by_cases h₁ : ν = ψ
  · subst ν
    have hc' : Ω.transferConnection μ ψ (p, ψ, r) ∈ (Ω.transferBase hΩ h).connections :=
      Finset.mem_image_of_mem _ hc
    obtain ⟨hp₁', hp₂', hr₁', hr₂'⟩ := (Ω.transferBase hΩ h).bounds_of_mem_connections _ hc'
    obtain ⟨hp₁, hp₂, hr₁, hr₂⟩ := Ω.bounds_of_mem_connections _ hc
    have hbψ' := (lift_mk_basicEquation_transferBase_iff hΩ h f hbμ hcμ ψ).2 hbψ
    rw [transferConnection_of_eq h.ne_dual_self rfl] at hc' hp₁' hp₂' hr₁' hr₂' ⊢
    rw [← (Ω.transferBase hΩ h).lift_mk_boundaryEquation_dual_iff f hp₁'.le hp₂'.le hr₁'.le hr₂'.le
      hbψ', ← transferConnection_of_eq_dual h.ne_dual_self (c := (r, Ω.dual ψ, p)) rfl,
      hdual (Ω.dual_mem_connections _ hc),
      Ω.lift_mk_boundaryEquation_dual_iff f hp₁.le hp₂.le hr₁.le hr₂.le hbψ]
  · by_cases h₂ : ν = Ω.dual ψ
    · subst ν
      exact hdual hc
    · rw [transferConnection_of_ne h₁ h₂, boundaryEquation_transferBase_of_ne hΩ h h₁ h₂]

/-- **ET2 on group solutions.** Transferring a base `ψ` along a carrier `μ` in a formally
consistent generalised equation preserves the points of `Ω*` in every `F(A)`-group. -/
theorem V_toSystem_transferBase {H : Type*} [Group H] (ι : FreeGroup A →* H) :
    V ι (Ω.transferBase hΩ h).toSystem = V ι Ω.toSystem := by
  ext v
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff, (Ω.transferBase hΩ h).forall_mem_equations,
    Ω.forall_mem_equations]
  set f : Fin Ω.numItems ⊕ A → H := Sum.elim v (ι ∘ FreeGroup.of)
  have hμ₁ : μ ≠ ψ := h.ne_carrier.symm
  have hμ₂ : μ ≠ Ω.dual ψ := h.dual_ne_carrier.symm
  refine ⟨fun ⟨hb', hcoeff', hc'⟩ => ?_, fun ⟨hb, hcoeff, hc⟩ => ?_⟩
  · have hbμ : FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation μ).2) := by
      simpa [basicEquation_transferBase_of_ne hΩ h hμ₁ hμ₂] using hb' μ
    have hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
          FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) := by
      intro c hc_mem hc_eq
      have hc'_mem : c ∈ (Ω.transferBase hΩ h).connections :=
        (mem_connections_transferBase_of_ne hΩ h (hc_eq ▸ hμ₁) (hc_eq ▸ hμ₂)).2 hc_mem
      simpa [boundaryEquation_transferBase_of_ne hΩ h (hc_eq ▸ hμ₁) (hc_eq ▸ hμ₂)] using
        hc' c hc'_mem
    have hb : ∀ ν, FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).1) =
        FreeGroup.lift f (FreeGroup.mk (Ω.basicEquation ν).2) :=
      fun ν => (lift_mk_basicEquation_transferBase_iff hΩ h f hbμ hcμ ν).1 (hb' ν)
    refine ⟨hb, fun b hb_mem => by simpa using hcoeff' b hb_mem, fun c hc_mem => ?_⟩
    exact (lift_mk_boundaryEquation_transferConnection_iff hΩ h f hbμ hcμ (hb ψ) hc_mem).1
      (hc' _ (Finset.mem_image_of_mem _ hc_mem))
  · have hcμ : ∀ c ∈ Ω.connections, c.2.1 = μ →
        FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).1) =
          FreeGroup.lift f (FreeGroup.mk (Ω.boundaryEquation c).2) :=
      fun c hc_mem _ => hc c hc_mem
    refine ⟨fun ν => (lift_mk_basicEquation_transferBase_iff hΩ h f (hb μ) hcμ ν).2 (hb ν),
      fun b hb_mem => by simpa using hcoeff b hb_mem, fun c' hc'_mem => ?_⟩
    obtain ⟨c, hc_mem, rfl⟩ := Finset.mem_image.1 hc'_mem
    exact (lift_mk_boundaryEquation_transferConnection_iff hΩ h f (hb μ) hcμ (hb ψ) hc_mem).2
      (hc c hc_mem)

/-- **ET2 on coordinate groups.** The `F(A)`-homomorphism `F_{R(Ω)} → F_{R(Ω′)}` induced by the
identity on the items, where `Ω′ = Ω.transferBase hΩ h`. -/
def transferBaseHom : GHom (CoordGroup.coeff (.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (.id (FreeGroup A)) (Ω.transferBase hΩ h).toSystem) :=
  CoordGroup.homOfVSubset (V_toSystem_transferBase hΩ h _).le

/-- The homomorphism `F_{R(Ω)} → F_{R(Ω′)}` of ET2 is the identity on the words in the items. -/
-- Not `@[simp]`: the reducible `transferBase` in the codomain keeps `simp` from indexing this
-- lemma uninstantiated, so it is used through `rw`.
theorem transferBaseHom_mk (w : GX (FreeGroup A) (Fin Ω.numItems)) :
    transferBaseHom hΩ h (w : Ω.coordGroup) = (w : (Ω.transferBase hΩ h).coordGroup) :=
  CoordGroup.homOfVSubset_mk _ w

/-- **ET2 on coordinate groups.** If `Ω` is formally consistent and `ψ` is transferable along `μ`,
the identity on the items induces an `F(A)`-isomorphism of the coordinate groups of `Ω` and
`Ω.transferBase hΩ h`. -/
theorem transferBaseHom_bijective : Function.Bijective (transferBaseHom hΩ h) :=
  ⟨CoordGroup.homOfVSubset_injective _ (V_toSystem_transferBase hΩ h _).ge,
    CoordGroup.homOfVSubset_surjective _⟩

/-! ### Graphical solutions and the transformation of ET2 -/

namespace Solution

/-- A solution of `Ω` as a solution of `Ω.transferBase hΩ h`, with the same words: the word of the
transferred base `ψ` lies inside `U[α(Δμ), β(Δμ)]`, which is reduced as written. -/
def transferBase (U : Ω.Solution) : (Ω.transferBase hΩ h).Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    (((Ω.transferBase hΩ h).forall_mem_equations_isReduced_iff U.isReduced_word).2 fun ν => by
      rw [segment_transferBase]
      by_cases hν : ν = ψ
      · subst ν
        exact U.isReduced_substituteVars_segment_of_le (Ω.dual μ)
          (left_dual_le_left_transferBase hΩ h) (right_transferBase_le_right_dual hΩ h)
      · rw [left_transferBase_of_ne hΩ h hν, right_transferBase_of_ne hΩ h hν]
        exact U.isReduced_substituteVars_segment ν)
    (funext U.point_apply ▸ (V_toSystem_transferBase hΩ h _).ge U.point_mem_V)

/-- Transferring a base keeps the words of a solution. -/
@[simp]
theorem transferBase_word (U : Ω.Solution) : (U.transferBase hΩ h).word = U.word :=
  Solution.ofMemV_word ..

/-- Transferring a base keeps the point of a solution. -/
@[simp]
theorem transferBase_point (U : Ω.Solution) : (U.transferBase hΩ h).point = U.point := by
  ext
  simp

/-- Transferring a base keeps the positions of the boundaries in the words of a solution. -/
@[simp]
theorem transferBase_prefixLength (U : Ω.Solution) :
    (U.transferBase hΩ h).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- A solution of `Ω.transferBase hΩ h` as a solution of `Ω`, with the same words: `ψ` lies inside
the carrier `μ`, which remains a base of `Ω.transferBase hΩ h`, so `U[α(ψ), β(ψ)]` is reduced as
written. -/
def ofTransferBase (U : (Ω.transferBase hΩ h).Solution) : Ω.Solution :=
  Solution.ofMemV U.word U.isReduced_word U.word_ne_nil
    ((Ω.forall_mem_equations_isReduced_iff U.isReduced_word).2 fun ν => by
      by_cases hν : ν = ψ
      · subst ν
        have hμ' : μ ≠ ψ := h.ne_carrier.symm
        have hseg := U.isReduced_substituteVars_segment_of_le μ
          ((left_transferBase_of_ne hΩ h hμ').symm ▸ h.left_le)
          ((right_transferBase_of_ne hΩ h hμ').symm ▸ h.right_le)
        rwa [segment_transferBase] at hseg
      · have hseg := U.isReduced_substituteVars_segment ν
        rwa [segment_transferBase, left_transferBase_of_ne hΩ h hν,
          right_transferBase_of_ne hΩ h hν] at hseg)
    (funext U.point_apply ▸ (V_toSystem_transferBase hΩ h _).le U.point_mem_V)

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its words. -/
@[simp]
theorem ofTransferBase_word (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).word = U.word :=
  Solution.ofMemV_word ..

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its point. -/
@[simp]
theorem ofTransferBase_point (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).point = U.point := by
  ext
  simp

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` keeps its boundary
positions. -/
@[simp]
theorem ofTransferBase_prefixLength (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).prefixLength = U.prefixLength := by
  ext
  simp [prefixLength_def]

/-- Transferring a solution and reading it back recovers the original solution. -/
@[simp]
theorem ofTransferBase_transferBase (U : Ω.Solution) :
    (U.transferBase hΩ h).ofTransferBase hΩ h = U :=
  Solution.ext (by simp)

/-- Reading a solution of `Ω.transferBase hΩ h` back and transferring it recovers the solution. -/
@[simp]
theorem transferBase_ofTransferBase (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).transferBase hΩ h = U :=
  Solution.ext (by simp)

/-- Reading a solution of `Ω.transferBase hΩ h` back as a solution of `Ω` composes its homomorphism
with `transferBaseHom`. -/
theorem ofTransferBase_toHom (U : (Ω.transferBase hΩ h).Solution) :
    (U.ofTransferBase hΩ h).toHom = U.toHom.comp (transferBaseHom hΩ h) := by
  ext k
  rw [GHom.coe_comp, Function.comp_apply, transferBaseHom_mk]
  simp

end Solution

/-- **ET2 on solutions.** If `Ω` is formally consistent and `ψ` is transferable along `μ`, the
graphical solutions of `Ω` and of `Ω.transferBase hΩ h` are in canonical bijection with identical
item words. -/
def solutionEquivTransferBase : Ω.Solution ≃ (Ω.transferBase hΩ h).Solution where
  toFun U := U.transferBase hΩ h
  invFun U := U.ofTransferBase hΩ h
  left_inv := Solution.ofTransferBase_transferBase hΩ h
  right_inv := Solution.transferBase_ofTransferBase hΩ h

/-- `solutionEquivTransferBase` sends `U` to `U.transferBase hΩ h`. -/
@[simp]
theorem solutionEquivTransferBase_apply (U : Ω.Solution) :
    solutionEquivTransferBase hΩ h U = U.transferBase hΩ h :=
  (rfl)

/-- The inverse of `solutionEquivTransferBase` sends `U` to `U.ofTransferBase hΩ h`. -/
@[simp]
theorem solutionEquivTransferBase_symm_apply (U : (Ω.transferBase hΩ h).Solution) :
    (solutionEquivTransferBase hΩ h).symm U = U.ofTransferBase hΩ h :=
  (rfl)

/-- The homomorphism `F_{R(Ω′)} → F(A)` of `U.transferBase hΩ h` composed with `transferBaseHom`
is the homomorphism of `U`. -/
theorem toHom_comp_transferBaseHom (U : Ω.Solution) :
    (U.transferBase hΩ h).toHom.comp (transferBaseHom hΩ h) = U.toHom := by
  rw [← Solution.ofTransferBase_toHom, Solution.ofTransferBase_transferBase]

/-- If `Ω` has a solution, `Ω.transferBase hΩ h` is formally consistent. -/
theorem isFormallyConsistent_transferBase_of_nonempty_solution (hne : Nonempty Ω.Solution) :
    (Ω.transferBase hΩ h).IsFormallyConsistent :=
  let ⟨U⟩ := hne
  (U.transferBase hΩ h).isFormallyConsistent

-- `@[expose]` so the index type `.ι` and dependent target family `.target` reduce publicly.
/-- **ET2 as a transformation.** The transformation of `Ω` given by transferring `ψ` along `μ`,
keeping `Ω.transferBase hΩ h` as a successor when it is formally consistent. -/
@[expose] def transferBaseTransformation : Transformation Ω :=
  Transformation.ofFamily (κ := Unit) (fun _ => Ω.transferBase hΩ h)
    (fun _ => transferBaseHom hΩ h) (fun _ => (transferBaseHom_bijective hΩ h).2)
    (fun U => ⟨(), U.transferBase hΩ h⟩) (fun U => toHom_comp_transferBaseHom hΩ h U)

/-- `transferBaseTransformation` has at most one successor. -/
instance : Subsingleton (Ω.transferBaseTransformation hΩ h).ι :=
  inferInstanceAs (Subsingleton { _x : Unit // (Ω.transferBase hΩ h).IsFormallyConsistent })

/-- Every successor of `transferBaseTransformation` is `Ω.transferBase hΩ h`. -/
@[simp]
theorem transferBaseTransformation_target (i : (Ω.transferBaseTransformation hΩ h).ι) :
    (Ω.transferBaseTransformation hΩ h).target i = Ω.transferBase hΩ h :=
  (rfl)

/-- Every homomorphism of `transferBaseTransformation` is `transferBaseHom hΩ h`. -/
@[simp]
theorem transferBaseTransformation_hom (i : (Ω.transferBaseTransformation hΩ h).ι) :
    (Ω.transferBaseTransformation hΩ h).hom i = transferBaseHom hΩ h :=
  (rfl)

/-- `transferBaseTransformation` transfers every solution `U` to `U.transferBase hΩ h`. -/
@[simp]
theorem transferBaseTransformation_transfer_snd (U : Ω.Solution) :
    ((Ω.transferBaseTransformation hΩ h).transfer U).2 = U.transferBase hΩ h :=
  (rfl)

/-- **ET2 transfers solutions uniquely.** The solution of `Ω.transferBase hΩ h` whose homomorphism
composed with `transferBaseHom` equals `U.toHom` is `U.transferBase hΩ h`. -/
theorem toHom_comp_transferBaseHom_eq_iff (U : Ω.Solution) (U' : (Ω.transferBase hΩ h).Solution) :
    U'.toHom.comp (transferBaseHom hΩ h) = U.toHom ↔ U' = U.transferBase hΩ h :=
  ⟨fun heq => (Ω.transferBaseTransformation hΩ h).eq_of_toHom_comp_hom_eq
      ⟨(), U'.isFormallyConsistent⟩ (heq.trans (toHom_comp_transferBaseHom hΩ h U).symm),
    fun hU' => hU' ▸ toHom_comp_transferBaseHom hΩ h U⟩

/-- `transferBaseTransformation` transfers every solution of `Ω` uniquely. -/
theorem transfersUniquely_transferBaseTransformation :
    (Ω.transferBaseTransformation hΩ h).TransfersUniquely :=
  Transformation.transfersUniquely_of_subsingleton _

/-- `transferBaseTransformation` has a successor if and only if `Ω.transferBase hΩ h` is formally
consistent. -/
theorem nonempty_ι_transferBaseTransformation_iff :
    Nonempty (Ω.transferBaseTransformation hΩ h).ι ↔ (Ω.transferBase hΩ h).IsFormallyConsistent :=
  ⟨fun ⟨i⟩ => i.2, fun h' => ⟨⟨(), h'⟩⟩⟩

end Consistent

/-- Transferring `ψ` along `μ` preserves transferability of any other base `ψ' ≠ ψ` along `μ`. -/
theorem IsTransferable.transferBase {ψ' : Fin Ω.numBases} (h' : Ω.IsTransferable μ ψ')
    (hΩ : Ω.IsFormallyConsistent) (h : Ω.IsTransferable μ ψ) (hne : ψ' ≠ ψ) :
    (Ω.transferBase hΩ h).IsTransferable μ ψ' :=
  (isTransferable_transferBase_of_ne hΩ h hne).2 h'

end TransferBase

/-! ### Examples -/

section Examples

/-- Six items `h₀, …, h₅`, equal-sign carrier `μ = [0, 3]` and `Δ(μ) = [3, 6]` with boundary
connections `(1, μ, 4)` and `(2, μ, 5)`, and transfer base `ψ = [0, 2]` with `Δ(ψ) = [4, 6]` and
interior boundary connection `(1, ψ, 5)`. -/
private abbrev equalSignExample : GenEq (Fin 2) where
  numItems := 6
  numBases := 4
  left := ![0, 3, 0, 4]
  right := ![3, 6, 2, 6]
  left_lt_right := by decide
  sign := fun _ => true
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 4), (4, 1, 1), (2, 0, 5), (5, 1, 2), (1, 2, 5), (5, 3, 1)}
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- Transferring `ψ = [0, 2]` along the equal-sign carrier `μ = [0, 3]` moves `ψ` to `[3, 5]`,
keeps its sign `+1`, relocates the connection `(1, ψ, 5)` to `(4, ψ, 5)` (and `(5, Δψ, 1)` to
`(5, Δψ, 4)`), and drops the degree of `h₀` from `2` to `1`. -/
example :
    ∃ (hΩ : equalSignExample.IsFormallyConsistent)
      (h : equalSignExample.IsTransferable 0 2),
      let Ω' := equalSignExample.transferBase hΩ h
      Ω'.left 2 = 3 ∧ Ω'.right 2 = 5 ∧ Ω'.sign 2 = true ∧
        (4, 2, 5) ∈ Ω'.connections ∧ (5, 3, 4) ∈ Ω'.connections ∧ Ω'.degree 0 = 1 := by
  have hΩ : equalSignExample.IsFormallyConsistent := by decide
  have h : equalSignExample.IsTransferable 0 2 := by decide
  have ht0 : equalSignExample.tiedBoundary 0 0 = 3 := hΩ.tiedBoundary_eq isTiedTo_left
  have ht1 : equalSignExample.tiedBoundary 0 1 = 4 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have ht2 : equalSignExample.tiedBoundary 0 2 = 5 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have hdeg := degree_transferBase_add_one hΩ h (k := 0)
    (equalSignExample.mem_baseItems.2 (by decide))
    (fun hm => absurd (baseItems_transferBase_subset_dual hΩ h hm)
      (by rw [equalSignExample.mem_baseItems]; decide))
  have hdeg₀ : equalSignExample.degree 0 = 2 := by
    simp only [degree_def, equalSignExample.mem_baseItems]
    decide
  refine ⟨hΩ, h, by simp [ht0], by simp [ht2], rfl, ?_, ?_, by omega⟩
  · exact (mem_connections_transferBase hΩ h).2 ⟨(1, 2, 5), by decide,
      by rw [equalSignExample.transferConnection_of_eq h.ne_dual_self rfl, ht1]⟩
  · exact (mem_connections_transferBase hΩ h).2 ⟨(5, 3, 1), by decide,
      by rw [equalSignExample.transferConnection_of_eq_dual h.ne_dual_self (by decide), ht1]⟩

/-- Five items `h₀, …, h₄`, opposite-sign carrier `μ = [0, 2]` (`+1`) and `Δ(μ) = [2, 4]` (`-1`)
with boundary connection `(1, μ, 3)`, and transfer base `ψ = [0, 1]` (`+1`) with `Δ(ψ) = [4, 5]`
(`+1`). Its equations are `h₀h₁ = (h₂h₃)⁻¹`, `h₀ = h₃⁻¹` and `h₀ = h₄`. -/
private abbrev oppSignExample : GenEq (Fin 2) where
  numItems := 5
  numBases := 4
  left := ![0, 2, 0, 4]
  right := ![2, 4, 1, 5]
  left_lt_right := by decide
  sign := ![true, false, true, true]
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

/-- The graphical solution `(a, b, b⁻¹, a⁻¹, a)` (with `a = 0` and `b = 1`) of `oppSignExample`. -/
private def oppSignSolution : oppSignExample.Solution where
  word := ![[(0, true)], [(1, true)], [(1, false)], [(0, false)], [(0, true)]]
  isReduced_word := by unfold FreeGroup.IsReduced; decide
  word_ne_nil := by decide
  isReduced_subst := (oppSignExample.forall_mem_equations_isReduced_iff
    (by unfold FreeGroup.IsReduced; decide)).2
    (by simp only [segment_true]; unfold FreeGroup.IsReduced; decide)
  subst_eq := (forall_mem_equations _).2
    ⟨by
      simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, basicEquation_fst,
        basicEquation_snd, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.cons_val_succ, Matrix.head_cons, Matrix.tail_cons,
        Fin.isValue, segment_false, segment_true]
      decide,
    fun _ hb => absurd hb (Finset.notMem_empty _),
    by
      simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
        boundaryEquation_fst,
        oppSignExample.boundaryEquation_snd_of_sign_ne (c := (1, 0, 3)) (by decide),
        oppSignExample.boundaryEquation_snd_of_sign_ne (c := (3, 1, 1)) (by decide),
        segment_false, segment_true]
      decide⟩

/-- Transferring `ψ = [0, 1]` along the opposite-sign carrier `μ = [0, 2]` moves `ψ` onto `[3, 4]`
and flips its sign to `-1`, turning `h₀ = h₄` into `h₃⁻¹ = h₄`, and transports the solution
`(a, b, b⁻¹, a⁻¹, a)`. -/
example :
    ∃ (hΩ : oppSignExample.IsFormallyConsistent)
      (h : oppSignExample.IsTransferable 0 2),
      let Ω' := oppSignExample.transferBase hΩ h
      Ω'.left 2 = 3 ∧ Ω'.right 2 = 4 ∧ Ω'.sign 2 = false ∧ Ω'.IsFormallyConsistent ∧
        ∃ U : Ω'.Solution, U.word = ![[(0, true)], [(1, true)], [(1, false)], [(0, false)],
          [(0, true)]] := by
  have hΩ : oppSignExample.IsFormallyConsistent := oppSignSolution.isFormallyConsistent
  have h : oppSignExample.IsTransferable 0 2 := by decide
  have ht0 : oppSignExample.tiedBoundary 0 0 = 4 := hΩ.tiedBoundary_eq isTiedTo_left
  have ht1 : oppSignExample.tiedBoundary 0 1 = 3 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  exact ⟨hΩ, h, by simp [ht1], by simp [ht0], rfl,
    (oppSignSolution.transferBase hΩ h).isFormallyConsistent,
    oppSignSolution.transferBase hΩ h, Solution.transferBase_word hΩ h oppSignSolution⟩

/-- Four items `h₀, …, h₃`, opposite-sign carrier `μ = [0, 2]` (`+1`) and `Δ(μ) = [2, 4]` (`-1`)
with boundary connection `(1, μ, 3)` (`h₀ = h₃⁻¹`), and transfer base `ψ = [0, 1]` (`+1`) with
`Δ(ψ) = [3, 4]` (`+1`) (`h₀ = h₃`). This equation is formally consistent, yet transferring `ψ`
along `μ` places `ψ` at `[3, 4]` with sign `-1` on top of `Δ(ψ) = [3, 4]` (`+1`), breaking formal
consistency and witnessing that `Ω` has no graphical solution. -/
private abbrev inconsistentAfterTransfer : GenEq (Fin 2) where
  numItems := 4
  numBases := 4
  left := ![0, 2, 0, 3]
  right := ![2, 4, 1, 4]
  left_lt_right := by decide
  sign := ![true, false, true, true]
  dual := ![1, 0, 3, 2]
  dual_involutive := by unfold Function.Involutive; decide
  constBases := ∅
  connections := {(1, 0, 3), (3, 1, 1)}
  bounds_of_mem_connections := by decide
  dual_mem_connections := by decide

/-- Formal consistency is not preserved by `transferBase` in general when `Ω` has no solution:
`inconsistentAfterTransfer` is formally consistent, `IsTransferable 0 2` holds, its transferred
equation is not formally consistent, `transferBaseTransformation` has no successors, and
`inconsistentAfterTransfer` has no solution. -/
example :
    ∃ (hΩ : inconsistentAfterTransfer.IsFormallyConsistent)
      (h : inconsistentAfterTransfer.IsTransferable 0 2),
      ¬ (inconsistentAfterTransfer.transferBase hΩ h).IsFormallyConsistent ∧
        IsEmpty (inconsistentAfterTransfer.transferBaseTransformation hΩ h).ι ∧
        IsEmpty inconsistentAfterTransfer.Solution := by
  have hΩ : inconsistentAfterTransfer.IsFormallyConsistent := by decide
  have h : inconsistentAfterTransfer.IsTransferable 0 2 := by decide
  have ht1 : inconsistentAfterTransfer.tiedBoundary 0 1 = 3 :=
    hΩ.tiedBoundary_eq (isTiedTo_of_mem_connections (by decide))
  have hnot : ¬ (inconsistentAfterTransfer.transferBase hΩ h).IsFormallyConsistent := fun hΩ' => by
    have hsign := hΩ'.sign_eq_of_left_eq (μ := 2) (by simp [ht1])
    simp at hsign
  exact ⟨hΩ, h, hnot, ⟨fun i => hnot i.2⟩,
    ⟨fun U => hnot (isFormallyConsistent_transferBase_of_nonempty_solution hΩ h ⟨U⟩)⟩⟩

end Examples

end GenEq

end TauCeti
