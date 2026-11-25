/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Quotient.Basic
import TauCeti.Order.CompactlyGenerated

/-!
# Finiteness for submodules and quotients

An independent family of submodules whose supremum is finitely generated has only finitely
many nonzero members. This specializes `iSupIndep.finite_ne_bot_of_isCompactElement` using the
equivalence between finite generation and compactness in the lattice of submodules.

`Submodule.toAddSubgroup` is reducible and keeps the carrier set, so `p` and `p.toAddSubgroup`
have the same elements and the same `ℤ`-module structure. Instance search is nevertheless keyed
on the head symbol, so a `Module.Finite ℤ p` instance is never tried against the goal
`Module.Finite ℤ p.toAddSubgroup`. This file records that transfer once, for every `ℤ`-submodule,
rather than at each lattice presented to an API that reads additive subgroups.

For compatible actions of a semiring `A` and a ring `R`, an `R`-submodule `N` and its
quotient being finite over `A` implies that the ambient module is finite over `A`. The
quotient is formed over `R`; the scalar semiring `A` need not be a ring. This is the
scalar-restriction version of Mathlib's `Module.Finite.of_submodule_quotient`.

Finitely generated submodules can be lifted and split: one inside the range of a linear map is
the image of a finitely generated submodule, one inside `B ⊔ C` lies in `B ⊔ C'` for a finitely
generated `C' ≤ C`, and one inside `I • N` lies in `I • W` for a finitely generated `W ≤ N`.

## Main declarations

* `Submodule.finite_iff_fg_restrictScalars`: an `R`-submodule is finite over a compatible scalar
  semiring `A` exactly when its restriction of scalars to `A` is finitely generated.
* `Module.Finite.of_restrictScalars_submodule_quotient`: finiteness of a submodule and quotient
  over a compatible semiring implies finiteness of the ambient module.
* `Module.Finite.of_isCompl`: a complement of a submodule of a finitely generated module is
  finitely generated.
* `iSupIndep.finite_ne_bot_of_fg`: an independent family of submodules with finitely generated
  supremum has finite support.
* `Submodule.FG.exists_fg_map_eq_of_le_range`, `Submodule.FG.exists_fg_le_sup`,
  `Submodule.FG.exists_fg_le_smul`: a finitely generated submodule of a range, a supremum or an
  ideal multiple is controlled by a finitely generated submodule of the relevant piece.
* `TauCeti.instModuleFiniteToAddSubgroup`: a finitely generated `ℤ`-submodule stays finitely
  generated when read as an additive subgroup.
-/

public section

/-- An independent family of submodules spanning a finitely generated submodule has only finitely
many nonzero members. -/
theorem iSupIndep.finite_ne_bot_of_fg {R ι M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {A : ι → Submodule R M} (hAi : iSupIndep A) (hAf : (⨆ i, A i).FG) :
    {i | A i ≠ ⊥}.Finite :=
  hAi.finite_ne_bot_of_isCompactElement ((Submodule.fg_iff_compact _).mp hAf)

namespace TauCeti

/-- A finitely generated `ℤ`-submodule is still finitely generated when read as an additive
subgroup, the two being the same type. -/
instance instModuleFiniteToAddSubgroup {M : Type*} [AddCommGroup M] (p : Submodule ℤ M)
    [Module.Finite ℤ p] : Module.Finite ℤ p.toAddSubgroup :=
  inferInstanceAs (Module.Finite ℤ p)

end TauCeti

/-- An `R`-submodule is a finite module over a compatible scalar semiring `A` exactly when its
restriction of scalars to `A` is finitely generated. -/
theorem Submodule.finite_iff_fg_restrictScalars {A R M : Type*} [Semiring A] [Semiring R]
    [AddCommMonoid M] [Module A M] [Module R M] [SMul A R] [IsScalarTower A R M]
    (N : Submodule R M) : Module.Finite A N ↔ (N.restrictScalars A).FG := by
  rw [← Module.Finite.iff_fg]
  let e := (N.restrictScalarsEquiv A).restrictScalars A
  exact ⟨fun _ ↦ .equiv e.symm, fun _ ↦ .equiv e⟩

/-- If an `R`-submodule and its quotient are finite over a compatible scalar semiring `A`,
then so is the ambient module. The quotient is formed over the ring `R`, so `A` need not
be a ring or commutative. -/
theorem Module.Finite.of_restrictScalars_submodule_quotient
    {A R M : Type*} [Semiring A] [Ring R] [AddCommGroup M]
    [Module A M] [Module R M] [SMul A R] [IsScalarTower A R M]
    (N : Submodule R M) [Module.Finite A N] [Module.Finite A (M ⧸ N)] :
    Module.Finite A M := by
  have : Module.Finite A (N.restrictScalars A) :=
    Module.Finite.equiv ((N.restrictScalarsEquiv A).restrictScalars A).symm
  classical
  -- Lift a finite set of quotient generators; together with the finite kernel they span.
  obtain ⟨s, hs⟩ := Module.finite_def.mp
    (inferInstance : Module.Finite A (M ⧸ N))
  choose lift hlift using N.mkQ_surjective
  let P := Submodule.span A (lift '' (s : Set (M ⧸ N)))
  have hP : P.map (N.mkQ.restrictScalars A) = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp]
    simpa only [Function.comp_def, LinearMap.restrictScalars_apply, hlift,
      Set.image_id'] using hs
  have htop : P ⊔ N.restrictScalars A = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    have hx : N.mkQ x ∈ P.map (N.mkQ.restrictScalars A) := by rw [hP]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [LinearMap.restrictScalars_apply] at hyx
    -- The restricted kernel has the same carrier; quotient equality detects its differences.
    exact Submodule.mem_sup.mpr
      ⟨y, hy, x - y, (Submodule.Quotient.eq N).mp hyx.symm, add_sub_cancel _ _⟩
  refine ⟨?_⟩
  rw [← htop]
  exact (Submodule.fg_span (s.finite_toSet.image lift)).sup
    (Module.Finite.iff_fg.mp inferInstance)

/-- A complement of a submodule of a finitely generated module is finitely generated: it is the
image of the finitely generated module under the projection onto it. -/
theorem Module.Finite.of_isCompl {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] {T T' : Submodule R M} (hcompl : IsCompl T T') : Module.Finite R T :=
  Module.Finite.of_surjective (T.projectionOnto T' hcompl) (T.projectionOnto_surjective hcompl)

namespace Submodule

variable {R M M' : Type*} [AddCommMonoid M] [AddCommMonoid M']

section Semiring

variable [Semiring R] [Module R M] [Module R M']

/-- A finitely generated submodule contained in the range of a linear map is the image of a
finitely generated submodule of the source. -/
theorem FG.exists_fg_map_eq_of_le_range {f : M →ₗ[R] M'} {N' : Submodule R M'} (hN' : N'.FG)
    (h : N' ≤ LinearMap.range f) : ∃ N : Submodule R M, N.FG ∧ N.map f = N' := by
  induction N', hN' using Submodule.fg_induction with
  | singleton y =>
    obtain ⟨x, rfl⟩ := h (mem_span_singleton_self y)
    exact ⟨R ∙ x, fg_span_singleton x, by simp [map_span]⟩
  | sup N₁ N₂ _ _ ih₁ ih₂ =>
    obtain ⟨P₁, hP₁, rfl⟩ := ih₁ (le_sup_left.trans h)
    obtain ⟨P₂, hP₂, rfl⟩ := ih₂ (le_sup_right.trans h)
    exact ⟨P₁ ⊔ P₂, hP₁.sup hP₂, Submodule.map_sup _ _ _⟩

/-- A finitely generated submodule of `B ⊔ C` lies in `B ⊔ C'` for some finitely generated
`C' ≤ C`. -/
theorem FG.exists_fg_le_sup {A B C : Submodule R M} (hA : A.FG) (h : A ≤ B ⊔ C) :
    ∃ C' : Submodule R M, C'.FG ∧ C' ≤ C ∧ A ≤ B ⊔ C' := by
  induction A, hA using Submodule.fg_induction with
  | singleton x =>
    obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup.1 (h (mem_span_singleton_self x))
    refine ⟨R ∙ c, fg_span_singleton c, (span_singleton_le_iff_mem _ _).2 hc, ?_⟩
    rw [span_singleton_le_iff_mem]
    exact add_mem (mem_sup_left hb) (mem_sup_right (mem_span_singleton_self c))
  | sup A₁ A₂ _ _ ih₁ ih₂ =>
    obtain ⟨C₁, hC₁, hC₁C, hA₁⟩ := ih₁ (le_sup_left.trans h)
    obtain ⟨C₂, hC₂, hC₂C, hA₂⟩ := ih₂ (le_sup_right.trans h)
    exact ⟨C₁ ⊔ C₂, hC₁.sup hC₂, sup_le hC₁C hC₂C,
      sup_le (hA₁.trans (sup_le_sup_left le_sup_left _))
        (hA₂.trans (sup_le_sup_left le_sup_right _))⟩

end Semiring

variable [CommSemiring R] [Module R M]

/-- A finitely generated submodule of `I • N` lies in `I • W` for some finitely generated
`W ≤ N`. -/
theorem FG.exists_fg_le_smul {I : Ideal R} {N C : Submodule R M} (hC : C.FG) (h : C ≤ I • N) :
    ∃ W : Submodule R M, W.FG ∧ W ≤ N ∧ C ≤ I • W := by
  induction C, hC using Submodule.fg_induction with
  | singleton x =>
    have hx : x ∈ I • N := h (mem_span_singleton_self x)
    simp only [span_singleton_le_iff_mem]
    clear h
    induction hx using Submodule.smul_induction_on' with
    | smul r hr n hn =>
      exact ⟨R ∙ n, fg_span_singleton n, (span_singleton_le_iff_mem _ _).2 hn,
        smul_mem_smul hr (mem_span_singleton_self n)⟩
    | add x _ y _ hx hy =>
      obtain ⟨W₁, hW₁, hW₁N, hxW⟩ := hx
      obtain ⟨W₂, hW₂, hW₂N, hyW⟩ := hy
      exact ⟨W₁ ⊔ W₂, hW₁.sup hW₂, sup_le hW₁N hW₂N,
        add_mem ((smul_mono_right I le_sup_left : I • W₁ ≤ I • (W₁ ⊔ W₂)) hxW)
          ((smul_mono_right I le_sup_right : I • W₂ ≤ I • (W₁ ⊔ W₂)) hyW)⟩
  | sup C₁ C₂ _ _ ih₁ ih₂ =>
    obtain ⟨W₁, hW₁, hW₁N, hC₁⟩ := ih₁ (le_sup_left.trans h)
    obtain ⟨W₂, hW₂, hW₂N, hC₂⟩ := ih₂ (le_sup_right.trans h)
    exact ⟨W₁ ⊔ W₂, hW₁.sup hW₂, sup_le hW₁N hW₂N, sup_le
      (hC₁.trans (smul_mono_right _ le_sup_left)) (hC₂.trans (smul_mono_right _ le_sup_right))⟩

end Submodule
