/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.NumberTheory.Padics.Complex.GaloisAction
public import TauCeti.RepresentationTheory.Continuous.BanachRep.AlmostIso

/-!
# Almost `ℂ_p`-representations

Let `K` be a field between `ℚ_p` and its algebraic closure `PadicAlgCl p`, and let
`G_K = Gal(PadicAlgCl p / K)` act on `ℂ_p` by the continuous extension of its action on
`PadicAlgCl p`. Following Fontaine, a Banach representation `W` of `G_K` over `ℚ_p` (a
`TauCeti.BanachRep ℚ_[p] G_K`) is an *almost `ℂ_p`-representation* when it is almost isomorphic
to `ℂ_p^d` for some `d`, with `G_K` acting coordinatewise: there are finite-dimensional
`G_K`-stable `ℚ_p`-subspaces `V₂ ⊆ W` and `V₁ ⊆ ℂ_p^d` and an isomorphism `W ⧸ V₂ ≅ ℂ_p^d ⧸ V₁`
of Banach representations (a `TauCeti.BanachRep.AlmostIso`). The integers `d` and
`dim V₂ - dim V₁` are the dimension and the height of the presentation. For a finite extension
`K` of `ℚ_p` Fontaine shows that they depend only on `W`; this file does not use that.

The almost `ℂ_p`-representations form a full subcategory `TauCeti.AlmostCRep p K` of the
Banach representations, closed under isomorphisms and under almost isomorphisms. It contains every
finite-dimensional Banach representation and every `ℂ_p^d`. The basic presentations behave as
Fontaine's height predicts: `ℚ_p` with the trivial action has a presentation of dimension `0` and
height `1`, and the quotient `ℂ_p ⧸ ℚ_p` one of dimension `1` and height `-1`.

## Main definitions

* `TauCeti.padicComplexPow p K d`: the Banach representation `ℂ_p^d` of `G_K`.
* `TauCeti.IsAlmostCRep p K`: the property of being an almost `ℂ_p`-representation.
* `TauCeti.AlmostCRep p K`: the full subcategory of almost `ℂ_p`-representations.

## Main results

* `TauCeti.IsAlmostCRep.of_almostIso`: a Banach representation almost isomorphic to an almost
  `ℂ_p`-representation is one.
* `TauCeti.isAlmostCRep_of_finiteDimensional`: finite-dimensional Banach representations are
  almost `ℂ_p`-representations, with a presentation of dimension `0` and height their dimension.
* `TauCeti.exists_almostIso_padicComplexPow_one_height_eq_neg_one`: `ℂ_p ⧸ ℚ_p` has a
  presentation of dimension `1` and height `-1`.

## References

* J.-M. Fontaine, *Presque `C_p`-représentations*, Documenta Mathematica, Extra Volume Kato
  (2003), 285–385, §1.4.
* P. Colmez and W. Nizioł, *On the cohomology of `p`-adic analytic spaces, II: The
  `C_st`-conjecture* (2025), §2.2.1 and Remark 2.3.
-/

public section

open CategoryTheory Module

namespace TauCeti

open BanachRep

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

/-- **The Banach representation `ℂ_p^d`** of `G_K = Gal(PadicAlgCl p / K)` over `ℚ_p`: the
Galois group acts on each coordinate by the continuous extension of its action on
`PadicAlgCl p`. -/
noncomputable abbrev padicComplexPow (d : ℕ) :
    BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) :=
  BanachRep.of (ContinuousRep.ofDistribMulAction _ ℚ_[p] (Fin d → ℂ_[p]))

/-- The Galois group acts on `ℂ_p^d` coordinatewise. -/
theorem padicComplexPow_ρ_apply (d : ℕ) (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
    (x : Fin d → ℂ_[p]) (i : Fin d) : (padicComplexPow p K d).ρ σ x i = σ • x i :=
  congrFun (ContinuousRep.ofDistribMulAction_apply (A := ℚ_[p]) σ x) i

/-- **Almost `ℂ_p`-representations**: the Banach representations of `G_K` over `ℚ_p` that are
almost isomorphic to `ℂ_p^d` for some `d`. -/
def IsAlmostCRep : ObjectProperty (BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) :=
  fun W => ∃ d : ℕ, Nonempty (AlmostIso W (padicComplexPow p K d))

variable {p K}

theorem isAlmostCRep_iff (W : BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) :
    IsAlmostCRep p K W ↔ ∃ d : ℕ, Nonempty (AlmostIso W (padicComplexPow p K d)) :=
  Iff.rfl

/-- **Almost `ℂ_p`-representations are closed under almost isomorphism.** -/
theorem IsAlmostCRep.of_almostIso {W W' : BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)}
    (e : AlmostIso W W') (h : IsAlmostCRep p K W') : IsAlmostCRep p K W := by
  obtain ⟨d, ⟨f⟩⟩ := h
  exact ⟨d, ⟨e.trans f⟩⟩

instance : (IsAlmostCRep p K).IsClosedUnderIsomorphisms where
  of_iso e h := h.of_almostIso (AlmostIso.ofIso e.symm)

variable (p K) in
/-- `ℂ_p^d` is an almost `ℂ_p`-representation. -/
theorem isAlmostCRep_padicComplexPow (d : ℕ) : IsAlmostCRep p K (padicComplexPow p K d) :=
  ⟨d, ⟨AlmostIso.refl _⟩⟩

instance : FiniteDimensional ℚ_[p] (padicComplexPow p K 0) :=
  inferInstanceAs (FiniteDimensional ℚ_[p] (Fin 0 → ℂ_[p]))

/-- **A finite-dimensional Banach representation `W` has a presentation of dimension `0` and
height `dim W`**: divide out all of `W`. -/
theorem exists_almostIso_padicComplexPow_zero_height_eq
    (W : BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) [FiniteDimensional ℚ_[p] W] :
    ∃ e : AlmostIso W (padicComplexPow p K 0), e.height = finrank ℚ_[p] W :=
  ⟨AlmostIso.ofFiniteDimensional _ _, by simp [Module.finrank_zero_of_subsingleton]⟩

/-- Finite-dimensional Banach representations are almost `ℂ_p`-representations. -/
theorem isAlmostCRep_of_finiteDimensional
    (W : BanachRep.{0} ℚ_[p] (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)) [FiniteDimensional ℚ_[p] W] :
    IsAlmostCRep p K W :=
  ⟨0, ⟨AlmostIso.ofFiniteDimensional _ _⟩⟩

variable (p K) in
/-- `ℚ_p` with the trivial action of `G_K` has a presentation of dimension `0` and height `1`. -/
theorem exists_almostIso_trivial_height_eq_one :
    ∃ e : AlmostIso (BanachRep.of (ContinuousRep.trivial (PadicAlgCl p ≃ₐ[K] PadicAlgCl p)
      ℚ_[p] ℚ_[p])) (padicComplexPow p K 0), e.height = 1 := by
  simpa using exists_almostIso_padicComplexPow_zero_height_eq (K := K)
    (BanachRep.of (ContinuousRep.trivial (PadicAlgCl p ≃ₐ[K] PadicAlgCl p) ℚ_[p] ℚ_[p]))

variable (p K) in
/-- The diagonal line `ℚ_p ⊆ ℂ_p^d` spanned by `(1, …, 1)` is stable under `G_K`, which fixes
`ℚ_p`. -/
theorem padicComplexPow_span_one_invariant (d : ℕ) :
    ∀ (σ : PadicAlgCl p ≃ₐ[K] PadicAlgCl p), ∀ x ∈ ℚ_[p] ∙ (1 : Fin d → ℂ_[p]),
      (padicComplexPow p K d).ρ σ x ∈ ℚ_[p] ∙ (1 : Fin d → ℂ_[p]) := by
  intro σ x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  refine Submodule.mem_span_singleton.mpr ⟨c, funext fun i => ?_⟩
  simp

variable (p K) in
/-- `ℂ_p ⧸ ℚ_p` has a presentation of dimension `1` and height `-1`: it is isomorphic to
`ℂ_p^1 ⧸ ℚ_p` with nothing divided out of it. -/
theorem exists_almostIso_padicComplexPow_one_height_eq_neg_one :
    ∃ e : AlmostIso (quotient (padicComplexPow p K 1) (ℚ_[p] ∙ (1 : Fin 1 → ℂ_[p]))
      (padicComplexPow_span_one_invariant p K 1) (Submodule.isClosed_of_finiteDimensional _))
      (padicComplexPow p K 1), e.height = -1 := by
  refine ⟨(AlmostIso.toQuotient _ _ (padicComplexPow_span_one_invariant p K 1)).symm, ?_⟩
  rw [AlmostIso.height_symm, AlmostIso.height_toQuotient, finrank_span_singleton one_ne_zero,
    Nat.cast_one]

/-- **The category of almost `ℂ_p`-representations** of `G_K`: the full subcategory of the
Banach representations of `G_K` over `ℚ_p` almost isomorphic to some `ℂ_p^d`. -/
abbrev AlmostCRep := (IsAlmostCRep p K).FullSubcategory

end TauCeti
