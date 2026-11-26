/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Length.Endomorphism

/-!
# Colengths of lattices exchanged by two operators

Let `S, B, P` be submodules of a module `M` over a commutative ring, `U, D` endomorphisms of `M`
and `c, d` scalars such that `D(S) ≤ B`, `D(P) ≤ P`, `U (D x) = c • x` on `S ⊓ P` and
`d • x ∈ P → x ∈ P`. Writing `S' = S ⊓ P`, this file proves the exchange bound
`length (S' ⧸ d U(S')) ≤ length (B ⧸ dS) + length (S' ⧸ cS')` in `ℕ∞`, all lengths being
`Module.length`. For submodules `X, Y` of `M` the quotient `X ⧸ Y` is written
`↥X ⧸ Y.comap X.subtype`, that is `X ⧸ (X ⊓ Y)`, which is `X ⧸ Y` when `Y ≤ X`.

Let `B'` be the set of `x ∈ B ⊓ P` with `U x ∈ S'` (all of `B ⊓ P` when `U(B) ≤ S` and
`U(P) ≤ P`). The left side is filtered by the image of `U(B')` and by `S' ⧸ U(B')`. The latter is
a quotient of `S' ⧸ cS'`, since `cs = U(Ds)` with `Ds ∈ B'`. The former is the image of
`B' ⧸ (B' ⊓ dS)` under `U`, because an element `ds` of `B'` with `s ∈ S` has `s ∈ P`, and
`B' ⧸ (B' ⊓ dS)` embeds in `B ⧸ (B ⊓ dS)`. No inclusion `U(B) ≤ S`, `U(P) ≤ P` or `dS ≤ B` is
needed. Over a principal ideal domain with an irreducible `ϖ`, `c = ϖ ^ e`, `d = ϖ ^ b` and `S`
finitely generated and torsion-free, the last term is at most `e * rank S` by the sandwich bound
`TauCeti.length_quotient_le_mul_finrank`.

## Main results

* `TauCeti.length_quotient_smul_map_inf_le_add`: the exchange bound, with scalars `c, d`.
* `TauCeti.length_quotient_pow_smul_map_inf_le_add_mul_finrank`: the exchange bound over a
  principal ideal domain, with `c = ϖ ^ e`, `d = ϖ ^ b` and the last term `e * rank S`.

The subadditivity of colengths used together with it is
`TauCeti.length_quotient_comap_subtype_map_comp_le` and its consequences.
-/

public section

namespace TauCeti

open scoped Pointwise

section Exchange

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The exchange bound.** Let `S, B, P` be submodules of `M`, `U, D` endomorphisms of `M` and
`c, d : R` with `D(S) ≤ B`, `D(P) ≤ P`, `U (D x) = c • x` for `x ∈ S ⊓ P`, and
`d • x ∈ P → x ∈ P` for every `x`. Then, in `ℕ∞`, writing `S' = S ⊓ P`,
`length (S' ⧸ (S' ⊓ d • U(S'))) ≤ length (B ⧸ (B ⊓ d • S)) + length (S' ⧸ c S')`.
No inclusion `U(B) ≤ S`, `U(P) ≤ P` or `d • S ≤ B` is assumed; when they hold, the quotients are
`S' ⧸ d • U(S')` and `B ⧸ d • S`. -/
theorem length_quotient_smul_map_inf_le_add {S B P : Submodule R M} {U D : M →ₗ[R] M} {c d : R}
    (hDS : S.map D ≤ B) (hDP : P.map D ≤ P) (hUD : ∀ x ∈ S ⊓ P, U (D x) = c • x)
    (hP : ∀ x, d • x ∈ P → x ∈ P) :
    Module.length R (↥(S ⊓ P) ⧸ (d • (S ⊓ P).map U).comap (S ⊓ P).subtype) ≤
      Module.length R (↥B ⧸ (d • S).comap B.subtype) +
        Module.length R (↥(S ⊓ P) ⧸ LinearMap.range (LinearMap.lsmul R ↥(S ⊓ P) c)) := by
  -- `B'` is the part of `B ⊓ P` that `U` maps into `S ⊓ P`; it is all of `B ⊓ P` when
  -- `U(B) ≤ S` and `U(P) ≤ P`.
  set B' := B ⊓ P ⊓ (S ⊓ P).comap U
  have hV : ∀ x ∈ B', U x ∈ S ⊓ P := fun _ hx ↦ hx.2
  set W := (d • (S ⊓ P).map U).comap (S ⊓ P).subtype
  set f := W.mkQ ∘ₗ U.restrict hV
  -- `(S ⊓ P) ⧸ d U(S ⊓ P)` is filtered by the range of `f`, the image of `U(B')`, and by
  -- `(S ⊓ P) ⧸ U(B')`.
  rw [length_quotient_eq_length_map_add_length_quotient_sup (LinearMap.range (U.restrict hV)) W,
    ← LinearMap.range_comp]
  refine add_le_add ?_ (length_quotient_anti ?_)
  · -- An element `d • s` of `B'` with `s ∈ S` has `s ∈ P`, so `f` kills it.
    have hK : (d • S).comap B'.subtype ≤ LinearMap.ker f := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
      have hsP : s ∈ P := hP s (hsx ▸ x.property.1.2)
      rw [Submodule.subtype_apply] at hsx
      have hUx : U x = d • U s := by rw [← hsx, map_smul]
      simp only [f, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, W, Submodule.mem_comap, Submodule.subtype_apply,
        LinearMap.coe_restrict_apply, hUx]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_map_of_mem ⟨hs, hsP⟩)
    exact (length_range_le_length_quotient f hK).trans
      (length_quotient_comap_subtype_mono (inf_le_left.trans inf_le_left) _)
  · -- `c • x = U (D x)` with `D x ∈ B'`.
    rintro _ ⟨x, rfl⟩
    have hx : U (D x) = c • x := hUD x x.property
    refine Submodule.mem_sup_right ⟨⟨D x, ⟨hDS ⟨x, x.property.1, rfl⟩,
      hDP ⟨x, x.property.2, rfl⟩⟩, ?_⟩, ?_⟩
    · exact Submodule.mem_comap.2 (hx ▸ (S ⊓ P).smul_mem c x.property)
    · ext
      simp [hx]

variable [IsDomain R] [IsPrincipalIdealRing R] {ϖ : R}

/-- **The exchange bound over a principal ideal domain.** Let `ϖ` be an irreducible element of a
principal ideal domain `R`, `S, B, P` submodules of an `R`-module `M` with `S` finitely generated
and torsion-free, `U, D` endomorphisms of `M` and `b, e : ℕ` with `D(S) ≤ B`, `D(P) ≤ P`,
`U (D x) = ϖ ^ e • x` for `x ∈ S ⊓ P`, and `ϖ • x ∈ P → x ∈ P` for every `x`. Then, in `ℕ∞`,
writing `S' = S ⊓ P`,
`length (S' ⧸ (S' ⊓ ϖ ^ b • U(S'))) ≤ length (B ⧸ (B ⊓ ϖ ^ b • S)) + e * rank S`.
This is `TauCeti.length_quotient_smul_map_inf_le_add` with the last term bounded by the sandwich
bound `TauCeti.length_quotient_le_mul_finrank`, as `rank S' ≤ rank S`. -/
theorem length_quotient_pow_smul_map_inf_le_add_mul_finrank (hϖ : Irreducible ϖ)
    {S B P : Submodule R M} [Module.Finite R S] [Module.IsTorsionFree R S] {U D : M →ₗ[R] M}
    {b e : ℕ} (hDS : S.map D ≤ B) (hDP : P.map D ≤ P) (hUD : ∀ x ∈ S ⊓ P, U (D x) = ϖ ^ e • x)
    (hP : ∀ x, ϖ • x ∈ P → x ∈ P) :
    Module.length R (↥(S ⊓ P) ⧸ (ϖ ^ b • (S ⊓ P).map U).comap (S ⊓ P).subtype) ≤
      Module.length R (↥B ⧸ (ϖ ^ b • S).comap B.subtype) + e * Module.finrank R S := by
  have hPb : ∀ x, ϖ ^ b • x ∈ P → x ∈ P := by
    induction b with
    | zero => simp
    | succ n ih =>
      intro x hx
      rw [pow_succ', mul_smul] at hx
      exact ih x (hP _ hx)
  -- `S ⊓ P` embeds in `S`, so it is finitely generated, torsion-free and of rank at most `rank S`.
  set ι := Submodule.inclusion (inf_le_left : S ⊓ P ≤ S)
  have hι : Function.Injective ι := Submodule.inclusion_injective _
  have : Module.Finite R ↥(S ⊓ P) := Module.Finite.of_injective ι hι
  have : Module.IsTorsionFree R ↥(S ⊓ P) := hι.moduleIsTorsionFree _ fun _ _ ↦ rfl
  refine (length_quotient_smul_map_inf_le_add hDS hDP hUD hPb).trans
    (add_le_add le_rfl ?_)
  refine (length_quotient_le_mul_finrank hϖ (T := LinearMap.range _) fun x ↦ ⟨x, rfl⟩).trans ?_
  gcongr
  exact LinearMap.finrank_le_finrank_of_injective hι

end Exchange

end TauCeti
