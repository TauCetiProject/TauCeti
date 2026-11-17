/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.Combinatorics.Brauer.Generator
import Mathlib.Data.Fintype.EquivFin

/-!
# Framings and skew-symmetric arc products of Brauer diagrams

When a Brauer diagram acts on the tensor power of a module carrying a symmetric bilinear form, an
arc carries no sign: the matrix entry of a diagram `D` at a boundary labelling is `1` when the
labelling is constant on the arcs of `D` and `0` otherwise
(`TauCeti/Combinatorics/Brauer/Labelling.lean`). For an alternating form, exchanging the two
endpoints of an arc negates its weight, and reordering two endpoints introduces a permutation sign;
the two sign changes cancel, so a diagram still has a canonical signed product over its arcs. This
file builds that signed product, the combinatorial counterpart of a Pfaffian term, for any
skew-symmetric matrix `W` on the `2 * k` boundary points `Fin k ⊕ Fin k`.

## Arc framings

Every Brauer diagram `D` on `k` strands is obtained from the identity diagram `permToBrauer 1` by
some permutation `π` of the boundary points `Fin k ⊕ Fin k`: `π` sends the `r`-th identity strand
`(Sum.inl r, Sum.inr r)` to an oriented arc `(π (Sum.inl r), π (Sum.inr r))` of `D`. Such a
permutation is an **arc framing** of `D` (`TauCeti.BrauerDiagram.IsFraming`). Two framings of the
same diagram differ on the right by an element of the centralizer of `Sum.swap`, the
hyperoctahedral group permuting the `k` pairs and reversing individual pairs:

* permuting the `k` pairs by `Equiv.Perm.sumCongr σ σ` has sign `(sign σ)² = 1` and reindexes the
  product over the `k` arcs;
* reversing one pair by `Equiv.swap (Sum.inl r) (Sum.inr r)` has sign `-1` and replaces
  `W x y` by `W y x = -W x y`.

Hence for any skew-symmetric matrix `W` (`∀ x y, W y x = -W x y`), the quantity
`sign π * ∏ r, W (π (Sum.inl r)) (π (Sum.inr r))` depends only on `D`, not on the framing `π`
(`TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`).

## Main definitions

* `TauCeti.BrauerDiagram.IsFraming`: a boundary permutation carrying `permToBrauer 1` to `D`.
* `TauCeti.BrauerDiagram.framing`: a chosen framing of a Brauer diagram.
* `TauCeti.BrauerDiagram.skewArcProd`: the signed product of the entries of a skew-symmetric
  boundary matrix `W` over the arcs of `D`.

## Main results

* `TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`: **framing independence** of the signed arc
  product for skew-symmetric `W`.
* `TauCeti.BrauerDiagram.skewArcProd_permToBrauer`, `TauCeti.BrauerDiagram.skewArcProd_capCup`,
  `TauCeti.BrauerDiagram.skewArcProd_congr` and `TauCeti.BrauerDiagram.skewArcProd_relabel`: values
  of the signed arc product on permutation diagrams, cap-cup diagrams and transported diagrams.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants*, Springer GTM 255
  (2009), §10.1.
-/

public section

namespace TauCeti

variable {k : ℕ}

namespace BrauerDiagram

/-! ### Arc framings of a Brauer diagram -/

/-- An **arc framing** of a Brauer diagram `D` on `k` strands is a permutation `π` of the boundary
points `Fin k ⊕ Fin k` carrying the identity diagram `permToBrauer 1` to `D`, so that the `k`
ordered pairs `(π (Sum.inl r), π (Sum.inr r))` list the `k` arcs of `D`. -/
def IsFraming (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) : Prop :=
  PerfectMatching.congr π (permToBrauer 1) = D

/-- Being a framing means transporting `permToBrauer 1` to `D`. -/
theorem isFraming_def (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) :
    D.IsFraming π ↔ PerfectMatching.congr π (permToBrauer 1) = D := Iff.rfl

/-- **Characterisation of an arc framing**: `π` frames `D` precisely when `D` matches
`π (Sum.inl r)` with `π (Sum.inr r)` for every `r : Fin k`. -/
theorem isFraming_iff (D : BrauerDiagram k) (π : Equiv.Perm (Fin k ⊕ Fin k)) :
    D.IsFraming π ↔ ∀ r : Fin k, D.val (π (Sum.inl r)) = π (Sum.inr r) := by
  refine ⟨fun h r => ?_, fun h => Subtype.ext (Equiv.ext fun x => ?_)⟩
  · rw [← h, PerfectMatching.congr_val_apply_apply, permToBrauer_val_inl, Equiv.Perm.one_apply]
  · rw [PerfectMatching.congr_val_apply]
    rcases hx : π.symm x with r | r
    · rw [permToBrauer_val_inl, Equiv.Perm.one_apply, ← h r, ← hx, π.apply_symm_apply]
    · simp only [permToBrauer_val_inr, Equiv.Perm.one_def, Equiv.refl_symm, Equiv.refl_apply]
      rw [← D.apply_eq_of_apply_eq (h r), ← hx, π.apply_symm_apply]

/-- A framing sends `Sum.inl r` and `Sum.inr r` to partners under `D`. -/
theorem IsFraming.val_inl {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) : D.val (π (Sum.inl r)) = π (Sum.inr r) :=
  (D.isFraming_iff π).mp hπ r

/-- A framing sends `Sum.inr r` and `Sum.inl r` to partners under `D`. -/
theorem IsFraming.val_inr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) : D.val (π (Sum.inr r)) = π (Sum.inl r) :=
  D.apply_eq_of_apply_eq (hπ.val_inl r)

/-- The identity permutation frames the identity diagram. -/
theorem isFraming_permToBrauer_one : (permToBrauer (1 : Equiv.Perm (Fin k))).IsFraming 1 :=
  PerfectMatching.congr_refl _

/-- `Equiv.Perm.sumCongr 1 σ` frames `permToBrauer σ`. -/
theorem isFraming_permToBrauer (σ : Equiv.Perm (Fin k)) :
    (permToBrauer σ).IsFraming (Equiv.Perm.sumCongr 1 σ) := by
  simp [IsFraming, ← relabel_def]

/-- The transposition `Equiv.swap (Sum.inr a) (Sum.inl b)` frames `capCup a b`. -/
theorem isFraming_capCup (a b : Fin k) :
    (capCup a b).IsFraming (Equiv.swap (Sum.inr a) (Sum.inl b)) := by
  rw [isFraming_iff]
  intro r
  rcases eq_or_ne a b with rfl | hab
  · rw [capCup_self]
    rcases eq_or_ne r a with rfl | hra
    · simp [Equiv.Perm.one_def]
    · simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hra, Sum.inr_injective.ne hra]
  · rcases eq_or_ne r b with rfl | hrb
    · simp [hab, Equiv.swap_apply_of_ne_of_ne, Sum.inr_injective.ne hab.symm]
    rcases eq_or_ne r a with rfl | hra
    · simp [hab, Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hab]
    · simp [hra, hrb, Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hrb,
        Sum.inr_injective.ne hra]

/-- Transporting a diagram along `ρ` multiplies its framings on the left by `ρ`. -/
theorem IsFraming.congr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (ρ : Equiv.Perm (Fin k ⊕ Fin k)) :
    IsFraming (PerfectMatching.congr ρ D) (ρ * π) :=
  (PerfectMatching.congr_trans π ρ (permToBrauer 1)).symm.trans (congrArg _ hπ)

/-- Relabelling a diagram multiplies its framings on the left by `Equiv.Perm.sumCongr σ τ`. -/
theorem IsFraming.relabel {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (σ τ : Equiv.Perm (Fin k)) :
    (D.relabel σ τ).IsFraming (Equiv.Perm.sumCongr σ τ * π) := by
  rw [relabel_def]
  exact hπ.congr (Equiv.Perm.sumCongr σ τ)

/-- Reconnecting two arcs multiplies framings on the left by the reconnecting transposition. -/
theorem IsFraming.reconnect {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (x y : Fin k ⊕ Fin k) :
    IsFraming (D.reconnect x y) (Equiv.swap (D.val x) y * π) := by
  have hrec : D.reconnect x y = PerfectMatching.congr (Equiv.swap (D.val x) y) D :=
    Subtype.ext ((PerfectMatching.reconnect_val D x y).trans (PerfectMatching.congr_val _ D).symm)
  rw [hrec]
  exact hπ.congr (Equiv.swap (D.val x) y)

/-- Reversing the orientation of the `r`-th arc in a framing leaves it a framing of `D`. -/
theorem IsFraming.mul_swap_inl_inr {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (r : Fin k) :
    D.IsFraming (π * Equiv.swap (Sum.inl r) (Sum.inr r)) := by
  rw [isFraming_iff]
  intro s
  rcases eq_or_ne s r with rfl | hsr
  · simp [hπ.val_inr s]
  · have h1 : Sum.inl s ≠ (Sum.inl r : Fin k ⊕ Fin k) := Sum.inl_injective.ne hsr
    have h2 : Sum.inr s ≠ (Sum.inr r : Fin k ⊕ Fin k) := Sum.inr_injective.ne hsr
    simp [Equiv.swap_apply_of_ne_of_ne, h1, h2, hπ.val_inl s]

/-- A framing intertwines `D.val` with `Sum.swap`. -/
theorem IsFraming.val_apply {D : BrauerDiagram k} {π : Equiv.Perm (Fin k ⊕ Fin k)}
    (hπ : D.IsFraming π) (x : Fin k ⊕ Fin k) : D.val (π x) = π x.swap := by
  cases x
  · exact hπ.val_inl _
  · exact hπ.val_inr _

/-- **A chosen arc framing of `D`**: enumerate the `k` lower ends of `D` and send `Sum.inl r` to
the `r`-th lower end and `Sum.inr r` to its partner. -/
noncomputable def framing (D : BrauerDiagram k) : Equiv.Perm (Fin k ⊕ Fin k) :=
  let g : Fin k ≃ {x // D.IsLowerEnd x} :=
    (Fintype.equivFinOfCardEq D.card_isLowerEnd).symm
  (g.sumCongr (g.trans D.notLowerEndEquiv.symm)).trans (Equiv.sumCompl D.IsLowerEnd)

/-- `D.framing` frames `D`. -/
theorem isFraming_framing (D : BrauerDiagram k) : D.IsFraming D.framing := by
  rw [isFraming_iff]
  intro r
  simp [framing]

/-- **Orienting one chosen arc in a framing**: for any boundary point `x`, some framing of `D`
lists the arc through `x` in the orientation `(x, D.val x)`. -/
theorem exists_isFraming_apply_eq (D : BrauerDiagram k) (x : Fin k ⊕ Fin k) :
    ∃ (π : Equiv.Perm (Fin k ⊕ Fin k)) (r : Fin k),
      D.IsFraming π ∧ π (Sum.inl r) = x ∧ π (Sum.inr r) = D.val x := by
  set π₀ := D.framing
  have h₀ : D.IsFraming π₀ := D.isFraming_framing
  rcases hx : π₀.symm x with r | r
  · have hxr : π₀ (Sum.inl r) = x := by rw [← hx, π₀.apply_symm_apply]
    exact ⟨π₀, r, h₀, hxr, (hxr ▸ h₀.val_inl r).symm⟩
  · have hxr : π₀ (Sum.inr r) = x := by rw [← hx, π₀.apply_symm_apply]
    refine ⟨π₀ * Equiv.swap (Sum.inl r) (Sum.inr r), r, h₀.mul_swap_inl_inr r, ?_, ?_⟩
    · simp [hxr]
    · simp [← hxr, h₀.val_inr r]

/-- **Orienting two distinct arcs in a framing**: when `x` and `y` lie on distinct arcs of `D`,
some framing of `D` lists the arc at `x` as `(x, D.val x)` at index `r₁` and the arc at `y` as
`(D.val y, y)` at index `r₂ ≠ r₁`. -/
theorem exists_isFraming_apply_pair_eq (D : BrauerDiagram k) {x y : Fin k ⊕ Fin k}
    (hxy : x ≠ y) (hDx : D.val x ≠ y) :
    ∃ (π : Equiv.Perm (Fin k ⊕ Fin k)) (r₁ r₂ : Fin k), r₁ ≠ r₂ ∧ D.IsFraming π ∧
      π (Sum.inl r₁) = x ∧ π (Sum.inr r₁) = D.val x ∧
      π (Sum.inl r₂) = D.val y ∧ π (Sum.inr r₂) = y := by
  obtain ⟨π₁, r₁, hπ₁, hx₁, hx₂⟩ := D.exists_isFraming_apply_eq x
  rcases hy : π₁.symm y with r₂ | r₂
  · have hyr : π₁ (Sum.inl r₂) = y := by rw [← hy, π₁.apply_symm_apply]
    have hr : r₁ ≠ r₂ := fun h => hxy (hx₁.symm.trans (h ▸ hyr))
    refine ⟨π₁ * Equiv.swap (Sum.inl r₂) (Sum.inr r₂), r₁, r₂, hr,
      hπ₁.mul_swap_inl_inr r₂, ?_, ?_, ?_, ?_⟩
    · simp [Equiv.swap_apply_of_ne_of_ne (Sum.inl_injective.ne hr) Sum.inl_ne_inr, hx₁]
    · simp [Equiv.swap_apply_of_ne_of_ne Sum.inr_ne_inl (Sum.inr_injective.ne hr), hx₂]
    · simp [← hyr, hπ₁.val_inl r₂]
    · simp [hyr]
  · have hyr : π₁ (Sum.inr r₂) = y := by rw [← hy, π₁.apply_symm_apply]
    have hr : r₁ ≠ r₂ := fun h => hDx (hx₂.symm.trans (h ▸ hyr))
    exact ⟨π₁, r₁, r₂, hr, hπ₁, hx₁, hx₂, (hyr ▸ hπ₁.val_inr r₂).symm, hyr⟩

/-! ### Skew-symmetric arc products and framing independence -/

section SkewArcProd

variable {R : Type*} [CommRing R]

/-- The raw signed product of `W` along a boundary permutation `π`. -/
private def rawArcProd (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
    (π : Equiv.Perm (Fin k ⊕ Fin k)) : R :=
  ((Equiv.Perm.sign π : ℤ) : R) * ∏ r : Fin k, W (π (Sum.inl r)) (π (Sum.inr r))

/-- Multiplying on the left by `ρ` pulls `W` back along `ρ` and scales by `sign ρ`. -/
private theorem rawArcProd_mul_left (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R)
    (ρ π : Equiv.Perm (Fin k ⊕ Fin k)) :
    rawArcProd W (ρ * π) =
      ((Equiv.Perm.sign ρ : ℤ) : R) * rawArcProd (W.submatrix ρ ρ) π := by
  simp only [rawArcProd, map_mul, Units.val_mul, Int.cast_mul, mul_assoc, Matrix.submatrix_apply,
    Equiv.Perm.mul_apply]

/-- Reversing the `r`-th pair leaves `rawArcProd` unchanged when `W` is skew-symmetric: the `-1`
from `sign` cancels the `-1` from `W y x = -W x y`. -/
private theorem rawArcProd_mul_swap_inl_inr {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R}
    (hW : ∀ x y, W y x = -W x y) (π : Equiv.Perm (Fin k ⊕ Fin k)) (r : Fin k) :
    rawArcProd W (π * Equiv.swap (Sum.inl r) (Sum.inr r)) = rawArcProd W π := by
  rw [rawArcProd, rawArcProd, map_mul, Equiv.Perm.sign_swap Sum.inl_ne_inr]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ r),
    ← Finset.mul_prod_erase Finset.univ (fun s => W (π (Sum.inl s)) (π (Sum.inr s)))
      (Finset.mem_univ r)]
  have hrest : ∏ s ∈ Finset.univ.erase r,
      W ((π * Equiv.swap (Sum.inl r) (Sum.inr r)) (Sum.inl s))
        ((π * Equiv.swap (Sum.inl r) (Sum.inr r)) (Sum.inr s)) =
      ∏ s ∈ Finset.univ.erase r, W (π (Sum.inl s)) (π (Sum.inr s)) := by
    refine Finset.prod_congr rfl fun s hs => ?_
    have hsr : s ≠ r := Finset.ne_of_mem_erase hs
    simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hsr, Sum.inr_injective.ne hsr]
  rw [hrest]
  simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
    hW (π (Sum.inl r)) (π (Sum.inr r)), Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul,
    Int.cast_neg, Int.cast_one]
  ring

/-- A boundary permutation commuting with `Sum.swap` and fixing every pair `{Sum.inl r, Sum.inr r}`
setwise acts by reversing a subset of pairs, so it preserves `rawArcProd`. -/
private theorem rawArcProd_eq_of_subset {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R}
    (hW : ∀ x y, W y x = -W x y) (S : Finset (Fin k)) :
    ∀ χ : Equiv.Perm (Fin k ⊕ Fin k),
      (∀ x, χ x.swap = (χ x).swap) →
      (∀ r, χ (Sum.inl r) = Sum.inl r ∨ χ (Sum.inl r) = Sum.inr r) →
      (∀ r, r ∉ S → χ (Sum.inl r) = Sum.inl r) →
      rawArcProd W χ = rawArcProd W 1 := by
  induction S using Finset.induction_on with
  | empty =>
    intro χ hswap _ hfix
    suffices χ = 1 by rw [this]
    ext x
    rcases x with r | r
    · exact hfix r (Finset.notMem_empty r)
    · simpa [hfix r (Finset.notMem_empty r)] using hswap (Sum.inl r)
  | insert r₀ S _ ih =>
    intro χ hswap hor hfix
    rcases hor r₀ with hr₀_eq | hr₀_eq
    · refine ih χ hswap hor fun r hr => ?_
      rcases eq_or_ne r r₀ with rfl | hne
      · exact hr₀_eq
      · exact hfix r (by simp [hne, hr])
    · rw [← rawArcProd_mul_swap_inl_inr hW χ r₀]
      refine ih (χ * Equiv.swap (Sum.inl r₀) (Sum.inr r₀))
        (fun x => ?_) (fun r => ?_) fun r hr => ?_
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← hswap]
        congr 1
        rcases x with r | r <;> rcases eq_or_ne r r₀ with rfl | hne
        · simp
        · simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hne, Sum.inr_injective.ne hne]
        · simp
        · simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hne, Sum.inr_injective.ne hne]
      · rcases eq_or_ne r r₀ with rfl | hne
        · exact Or.inl (by simpa [hr₀_eq] using hswap (Sum.inl r))
        · simpa [Equiv.swap_apply_of_ne_of_ne (Sum.inl_injective.ne hne) Sum.inl_ne_inr] using hor r
      · rcases eq_or_ne r r₀ with rfl | hne
        · simpa [hr₀_eq] using hswap (Sum.inl r)
        · simpa [Equiv.swap_apply_of_ne_of_ne (Sum.inl_injective.ne hne) Sum.inl_ne_inr] using
            hfix r (by simp [hne, hr])

/-- Every boundary permutation commuting with `Sum.swap` preserves `rawArcProd`: decompose it into
a pair permutation `Equiv.Perm.sumCongr σ σ` and pair reversals. -/
private theorem rawArcProd_eq_of_comm_swap {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R}
    (hW : ∀ x y, W y x = -W x y) {ψ : Equiv.Perm (Fin k ⊕ Fin k)}
    (hswap : ∀ x, ψ x.swap = (ψ x).swap) :
    rawArcProd W ψ = rawArcProd W 1 := by
  let σ : Equiv.Perm (Fin k) := Equiv.ofBijective (fun r => Sum.elim id id (ψ (Sum.inl r)))
    (Finite.injective_iff_bijective.mp fun r₁ r₂ h => by
      rcases h₁ : ψ (Sum.inl r₁) with s₁ | s₁ <;> rcases h₂ : ψ (Sum.inl r₂) with s₂ | s₂ <;>
        simp only [h₁, h₂, Sum.elim_inl, Sum.elim_inr, id_eq] at h <;> subst h
      · exact Sum.inl_injective (ψ.injective (h₁.trans h₂.symm))
      · exact absurd (ψ.injective (h₁.trans (by simpa [h₂] using (hswap (Sum.inl r₂)).symm)))
          Sum.inl_ne_inr
      · exact absurd (ψ.injective (h₂.trans (by simpa [h₁] using (hswap (Sum.inl r₁)).symm)))
          Sum.inl_ne_inr
      · exact Sum.inl_injective (ψ.injective (h₁.trans h₂.symm)))
  let χ : Equiv.Perm (Fin k ⊕ Fin k) := ψ * (Equiv.Perm.sumCongr σ σ)⁻¹
  have hχ_swap (x : Fin k ⊕ Fin k) : χ x.swap = (χ x).swap := by
    rcases x with r | r
    · simpa [χ] using hswap (Sum.inl (σ⁻¹ r))
    · simpa [χ] using hswap (Sum.inr (σ⁻¹ r))
  have hχ_or (r : Fin k) : χ (Sum.inl r) = Sum.inl r ∨ χ (Sum.inl r) = Sum.inr r := by
    have hunproj : Sum.elim id id (χ (Sum.inl r)) = r := σ.apply_symm_apply r
    rcases h : χ (Sum.inl r) with s | s <;> rw [h] at hunproj
    · exact Or.inl (congrArg Sum.inl hunproj)
    · exact Or.inr (congrArg Sum.inr hunproj)
  have hsign : Equiv.Perm.sign (Equiv.Perm.sumCongr σ σ) = 1 := by
    rw [Equiv.Perm.sign_sumCongr, Int.units_mul_self]
  have hprod : rawArcProd W (χ * Equiv.Perm.sumCongr σ σ) = rawArcProd W χ := by
    rw [rawArcProd, rawArcProd, map_mul, hsign, mul_one]
    exact congrArg _ (Equiv.prod_comp σ fun r => W (χ (Sum.inl r)) (χ (Sum.inr r)))
  rw [← inv_mul_cancel_right ψ (Equiv.Perm.sumCongr σ σ), hprod]
  exact rawArcProd_eq_of_subset hW Finset.univ χ hχ_swap hχ_or fun _ hr =>
    absurd (Finset.mem_univ _) hr

/-- **The signed arc product of a Brauer diagram** for a boundary matrix `W`: the product of `W`
over the oriented arcs of `D.framing`, multiplied by `sign D.framing`. When `W` is skew-symmetric,
this is independent of the framing (`TauCeti.BrauerDiagram.skewArcProd_eq_of_isFraming`). -/
noncomputable def skewArcProd (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) : R :=
  ((Equiv.Perm.sign D.framing : ℤ) : R) *
    ∏ r : Fin k, W (D.framing (Sum.inl r)) (D.framing (Sum.inr r))

/-- Defining formula of `TauCeti.BrauerDiagram.skewArcProd` in terms of `D.framing`. -/
theorem skewArcProd_def (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) :
    D.skewArcProd W = ((Equiv.Perm.sign D.framing : ℤ) : R) *
      ∏ r : Fin k, W (D.framing (Sum.inl r)) (D.framing (Sum.inr r)) := (rfl)

/-- `skewArcProd` is `rawArcProd` evaluated at the chosen framing `D.framing`. -/
private theorem skewArcProd_eq_rawArcProd (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) :
    D.skewArcProd W = rawArcProd W D.framing :=
  (rfl)

/-- Applying a ring homomorphism commutes with `TauCeti.BrauerDiagram.skewArcProd`. -/
theorem map_skewArcProd {S : Type*} [CommRing S] (f : R →+* S) (D : BrauerDiagram k)
    (W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R) :
    f (D.skewArcProd W) = D.skewArcProd (W.map f) := by
  simp [skewArcProd]

/-- **Framing independence of the signed arc product**: for a skew-symmetric matrix `W`,
`D.skewArcProd W` can be computed using *any* framing `π` of `D`. -/
theorem skewArcProd_eq_of_isFraming (D : BrauerDiagram k)
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y)
    {π : Equiv.Perm (Fin k ⊕ Fin k)} (hπ : D.IsFraming π) :
    D.skewArcProd W =
      ((Equiv.Perm.sign π : ℤ) : R) * ∏ r : Fin k, W (π (Sum.inl r)) (π (Sum.inr r)) := by
  set ψ := π⁻¹ * D.framing
  have hD : D.framing = π * ψ := by simp [ψ]
  have hcomm (x : Fin k ⊕ Fin k) : ψ x.swap = (ψ x).swap := π.injective <| by
    calc π (ψ x.swap) = D.framing x.swap := by simp [ψ]
      _ = D.val (D.framing x) := (D.isFraming_framing.val_apply x).symm
      _ = D.val (π (ψ x)) := by simp [ψ]
      _ = π (ψ x).swap := hπ.val_apply (ψ x)
  have hW' (x y : Fin k ⊕ Fin k) : W.submatrix π π y x = -W.submatrix π π x y := hW (π x) (π y)
  rw [skewArcProd_eq_rawArcProd, hD, rawArcProd_mul_left, rawArcProd_eq_of_comm_swap hW' hcomm]
  simp [rawArcProd]

/-- On the identity diagram, the signed arc product is `∏ r, W (Sum.inl r) (Sum.inr r)`. -/
theorem skewArcProd_permToBrauer_one {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R}
    (hW : ∀ x y, W y x = -W x y) :
    (permToBrauer (1 : Equiv.Perm (Fin k))).skewArcProd W =
      ∏ r : Fin k, W (Sum.inl r) (Sum.inr r) := by
  rw [skewArcProd_eq_of_isFraming _ hW isFraming_permToBrauer_one]
  simp

/-- **The signed arc product of a permutation diagram**: `sign σ` times the product of the through
weights `W (Sum.inl r) (Sum.inr (σ r))`. -/
theorem skewArcProd_permToBrauer (σ : Equiv.Perm (Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (permToBrauer σ).skewArcProd W =
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ r : Fin k, W (Sum.inl r) (Sum.inr (σ r)) := by
  rw [skewArcProd_eq_of_isFraming _ hW (isFraming_permToBrauer σ), Equiv.Perm.sign_sumCongr,
    map_one, one_mul]
  rfl

/-- **The signed arc product of a cap-cup diagram** at `a ≠ b`: minus the cap weight
`W (Sum.inl a) (Sum.inl b)` times the cup weight `W (Sum.inr a) (Sum.inr b)` times the through
weights off `{a, b}`. -/
theorem skewArcProd_capCup {a b : Fin k} (hab : a ≠ b)
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (capCup a b).skewArcProd W =
      -(W (Sum.inl a) (Sum.inl b) * W (Sum.inr a) (Sum.inr b) *
        ∏ r ∈ (Finset.univ.erase a).erase b, W (Sum.inl r) (Sum.inr r)) := by
  rw [skewArcProd_eq_of_isFraming _ hW (isFraming_capCup a b),
    Equiv.Perm.sign_swap Sum.inr_ne_inl, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
    neg_one_mul]
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    ← Finset.mul_prod_erase (Finset.univ.erase a) _ (Finset.mem_erase.mpr ⟨hab.symm,
      Finset.mem_univ b⟩), ← mul_assoc]
  congr 1
  · simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hab, Sum.inr_injective.ne hab.symm]
  · refine Finset.prod_congr rfl fun r hr => ?_
    have hrb : r ≠ b := (Finset.mem_erase.mp hr).1
    have hra : r ≠ a := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hr)).1
    simp [Equiv.swap_apply_of_ne_of_ne, Sum.inl_injective.ne hrb, Sum.inr_injective.ne hra]

/-- **Transporting a diagram along `ρ`** pulls `W` back along `ρ` and multiplies by `sign ρ`. -/
theorem skewArcProd_congr (D : BrauerDiagram k) (ρ : Equiv.Perm (Fin k ⊕ Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    skewArcProd (PerfectMatching.congr ρ D) W =
      ((Equiv.Perm.sign ρ : ℤ) : R) * D.skewArcProd (W.submatrix ρ ρ) := by
  rw [skewArcProd_eq_of_isFraming _ hW (D.isFraming_framing.congr ρ), skewArcProd]
  simp only [map_mul, Units.val_mul, Int.cast_mul, mul_assoc, Matrix.submatrix_apply,
    Equiv.Perm.mul_apply]

/-- **Relabelling a diagram by `(σ, τ)`** pulls `W` back along `Sum.map σ τ` and multiplies by
`sign σ * sign τ`. -/
theorem skewArcProd_relabel (D : BrauerDiagram k) (σ τ : Equiv.Perm (Fin k))
    {W : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) R} (hW : ∀ x y, W y x = -W x y) :
    (D.relabel σ τ).skewArcProd W =
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) *
        D.skewArcProd (W.submatrix (Sum.map σ τ) (Sum.map σ τ)) := by
  rw [relabel_def, skewArcProd_congr D _ hW, Equiv.Perm.sign_sumCongr, Units.val_mul, Int.cast_mul]
  congr 2

end SkewArcProd

end BrauerDiagram

end TauCeti
