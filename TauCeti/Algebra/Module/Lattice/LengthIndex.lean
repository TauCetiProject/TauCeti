/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Lattice
public import TauCeti.RingTheory.Length.Determinant
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.OrderOfVanishing.Noetherian
import TauCeti.Algebra.Module.Submodule.Map
import TauCeti.Algebra.Module.Submodule.Pointwise

/-!
# The length index of two lattices

For submodules `A`, `B` of a module over a ring `R`, `Submodule.lengthIndex A B` is the integer
`length (A / (A ⊓ B)) - length (B / (A ⊓ B))`, each length read through `ENat.toNat`.
For full lattices `A`, `B` in a vector space `V` over the fraction field `K` of a Noetherian domain
`O` of dimension at most one (for instance a discrete valuation ring) both lengths are finite, and
this is the index `idx(A, B)` of the lattices: it may be computed with any full lattice
`D ≤ A ⊓ B` in place of `A ⊓ B`, it equals `length (A / B)` when `B ≤ A`, and it is additive with
no inclusion among the lattices. Below `v(x)` is `WithZero.log (Ring.ordFrac O x)`; when `O` is a
discrete valuation ring this is its normalized valuation, with `v(ϖ) = 1` for a uniformizer `ϖ`
(`Ring.ordFrac_eq_valuation_inv`, `Ring.ordFrac_irreducible`), so the formulas read
`idx(A, gA) = v(det g)` and `idx(A, aA) = v(a) · dim V`. Unlike the `ℤ`-only
`Submodule.IsFullLattice.relIndex_ne_zero`, which counts cardinalities, the index here is
measured by length, so it also serves over a discrete valuation ring with infinite residue field.

## Main definitions

* `Submodule.lengthIndex`: the index `idx(A, B) ∈ ℤ`.

## Main statements

* `Submodule.isFiniteLength_quotient_comap_subtype`: `A ⧸ (A ⊓ D)` has finite length for `A`
  finitely generated and `D` a full lattice.
* `Submodule.lengthIndex_eq_sub`: the index may be computed with any full lattice `D ≤ A ⊓ B`.
* `Submodule.lengthIndex_of_le`, `Submodule.neg_lengthIndex`: `idx(A, B) = length (A / B)` for
  `B ≤ A`, and `idx(B, A) = -idx(A, B)`.
* `Submodule.lengthIndex_add_lengthIndex`: `idx(A, B) + idx(B, C) = idx(A, C)`.
* `Submodule.lengthIndex_mono_left`, `Submodule.lengthIndex_anti_right`: the index increases in its
  first argument and decreases in its second.
* `Submodule.lengthIndex_map`: an injective linear map preserves the index.
* `Submodule.lengthIndex_map_right_self_eq_log_ordFrac_det`: `idx(A, gA) = v(det g)`.
* `Submodule.lengthIndex_smul_right_self`: `idx(A, aA) = v(a) · dim V` for `a ∈ Kˣ`.
* `Submodule.lengthIndex_inv_smul_inf`: `idx(t⁻¹B ⊓ W, B ⊓ W) = v(t) · dim W` for a subspace `W`.
* `Submodule.lengthIndex_inf_mono`, `Submodule.lengthIndex_inf_le`: for `B ≤ A`, the index of
  `B ⊓ P` in `A ⊓ P` increases with the submodule `P` and is at most `idx(A, B)`.
* `Submodule.lengthIndex_inf_le_log_ordFrac_mul_finrank_add`: for every subspace `W` and `t ∈ Kˣ`,
  `idx(A ⊓ W, B ⊓ W) ≤ v(t) · dim W + length ((tA + B) / B)`; with `t = ϖ ^ d` this is
  `Submodule.lengthIndex_inf_le_mul_finrank_add`, the bound of the index on subspaces.

## References

The bound `idx(A ⊓ W, B ⊓ W) ≤ d · dim W + length ((ϖ ^ d A + B) / B)` for every subspace `W` and
every integer `d` is the form in which L. Alpöge's Lean formalization of the Riemann hypothesis for
Dirichlet L-functions (https://github.com/leanprover-community/riemann-hypothesis) uses the index
of two lattices over a discrete valuation ring.
-/

public section

open Module TauCeti
open scoped Pointwise

namespace Submodule

section Ring

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The **index** `idx(A, B)` of two submodules: the length of `A ⧸ (A ⊓ B)` minus the length of
`B ⧸ (A ⊓ B)`, each length read in `ℕ` through `ENat.toNat` (so an infinite length counts as
`0`). For full lattices over a Noetherian domain of dimension at most one both lengths are finite,
and `Submodule.lengthIndex_eq_sub` computes the index with any full lattice `D ≤ A ⊓ B`. -/
noncomputable def lengthIndex (A B : Submodule R M) : ℤ :=
  (length R (A ⧸ B.comap A.subtype)).toNat - (length R (B ⧸ A.comap B.subtype)).toNat

/-- The defining formula of `Submodule.lengthIndex`. -/
theorem lengthIndex_def (A B : Submodule R M) :
    lengthIndex A B = ((length R (A ⧸ B.comap A.subtype)).toNat : ℤ) -
      (length R (B ⧸ A.comap B.subtype)).toNat := by
  rw [lengthIndex]

/-- The index is antisymmetric: `idx(B, A) = -idx(A, B)`. -/
theorem neg_lengthIndex (A B : Submodule R M) : -lengthIndex A B = lengthIndex B A := by
  rw [lengthIndex_def, lengthIndex_def, neg_sub]

/-- For `B ≤ A`, the index of `B` in `A` is the length of `A ⧸ B`. -/
theorem lengthIndex_of_le {A B : Submodule R M} (h : B ≤ A) :
    lengthIndex A B = (length R (A ⧸ B.comap A.subtype)).toNat := by
  rw [lengthIndex_def, comap_subtype_eq_top.2 h,
    length_eq_zero (M := ↥B ⧸ (⊤ : Submodule R B)), ENat.toNat_zero, Nat.cast_zero, sub_zero]

/-- The index of a submodule in itself is `0`. -/
@[simp]
theorem lengthIndex_self (A : Submodule R M) : lengthIndex A A = 0 := by
  rw [lengthIndex_def, sub_self]

/-- The index of a submodule of `A` in `A` is nonnegative. -/
theorem lengthIndex_nonneg {A B : Submodule R M} (h : B ≤ A) : 0 ≤ lengthIndex A B := by
  rw [lengthIndex_of_le h]
  exact Nat.cast_nonneg _

/-- The index of `B` in `A` is at most the length of `A ⧸ (A ⊓ B)`. -/
theorem lengthIndex_le (A B : Submodule R M) :
    lengthIndex A B ≤ (length R (A ⧸ B.comap A.subtype)).toNat := by
  rw [lengthIndex_def]
  exact sub_le_self _ (Nat.cast_nonneg _)

/-- An injective linear map preserves the index: `idx(f(A), f(B)) = idx(A, B)`. -/
theorem lengthIndex_map {f : M →ₗ[R] N} (hf : Function.Injective f) (A B : Submodule R M) :
    lengthIndex (A.map f) (B.map f) = lengthIndex A B := by
  rw [lengthIndex_def, lengthIndex_def, length_quotient_comap_subtype_map hf,
    length_quotient_comap_subtype_map hf]

end Ring

section Lattice

variable {O : Type*} (K : Type*) {V : Type*} [CommRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- `gL` is a full lattice when `det g ≠ 0`, since `g` is then surjective
(`Submodule.isFullLattice_map`). -/
private theorem isFullLattice_map_of_det_ne_zero (L : Submodule O V) [L.IsFullLattice K]
    {g : V →ₗ[K] V} (hg : LinearMap.det g ≠ 0) : (L.map (g.restrictScalars O)).IsFullLattice K :=
  have : Module.Finite K V := Module.Finite.of_isFullLattice L
  isFullLattice_map L g
    ((Module.End.isUnit_iff g).1 ((LinearMap.isUnit_iff_isUnit_det g).2 hg.isUnit)).2

variable [IsNoetherianRing O] [Ring.KrullDimLE 1 O]

/-- For a finitely generated `A` and a full lattice `D`, the quotient `A ⧸ (A ⊓ D)` has finite
length. -/
theorem isFiniteLength_quotient_comap_subtype {A : Submodule O V} (hA : A.FG) (D : Submodule O V)
    [D.IsFullLattice K] : IsFiniteLength O (A ⧸ D.comap A.subtype) := by
  have : IsDomain O := (IsFractionRing.injective O K).isDomain _
  have : Module.Finite O A := Module.Finite.iff_fg.2 hA
  obtain ⟨c, hc, hcD⟩ := IsLattice.exists_ne_zero_forall_smul_mem K D
    (IsFullLattice.span_eq_top (A := K) (M := D)) hA
  refine TauCeti.isFiniteLength_of_nonZeroDivisor_mem_annihilator
    (Module.mem_annihilator.2 fun y ↦ ?_) (mem_nonZeroDivisors_of_ne_zero hc)
  obtain ⟨⟨x, hx⟩, rfl⟩ := Quotient.mk_surjective _ y
  exact (Quotient.mk_eq_zero _).2 (hcD x hx)

/-- For a finitely generated `A` and a full lattice `D`, the length of `A ⧸ (A ⊓ D)` is
finite. -/
theorem length_quotient_comap_subtype_ne_top {A : Submodule O V} (hA : A.FG) (D : Submodule O V)
    [D.IsFullLattice K] : length O (A ⧸ D.comap A.subtype) ≠ ⊤ :=
  length_ne_top_iff.2 (isFiniteLength_quotient_comap_subtype K hA D)

/-- **The index does not depend on the auxiliary lattice.** For full lattices `A`, `B` and any full
lattice `D ≤ A ⊓ B`, `idx(A, B) = length (A ⧸ D) - length (B ⧸ D)`. -/
theorem lengthIndex_eq_sub {A B D : Submodule O V} [A.IsFullLattice K] [B.IsFullLattice K]
    [D.IsFullLattice K] (hDA : D ≤ A) (hDB : D ≤ B) :
    lengthIndex A B = ((length O (A ⧸ D.comap A.subtype)).toNat : ℤ) -
      (length O (B ⧸ D.comap B.subtype)).toNat := by
  have : IsDomain O := (IsFractionRing.injective O K).isDomain _
  have hA := length_quotient_comap_subtype_eq_add (le_inf hDA hDB) (inf_le_left : A ⊓ B ≤ A)
  have hB := length_quotient_comap_subtype_eq_add (le_inf hDA hDB) (inf_le_right : A ⊓ B ≤ B)
  rw [comap_inf, comap_subtype_self, top_inf_eq] at hA
  rw [comap_inf, comap_subtype_self, inf_top_eq] at hB
  have hE := length_quotient_comap_subtype_ne_top K (IsLattice.fg K (A ⊓ B)) D
  rw [lengthIndex_def, hA, hB,
    ENat.toNat_add hE (length_quotient_comap_subtype_ne_top K (IsLattice.fg K A) B),
    ENat.toNat_add hE (length_quotient_comap_subtype_ne_top K (IsLattice.fg K B) A)]
  push_cast
  ring

/-- **Additivity of the index**, with no inclusion among the three full lattices:
`idx(A, B) + idx(B, C) = idx(A, C)`. -/
theorem lengthIndex_add_lengthIndex (A B C : Submodule O V) [A.IsFullLattice K]
    [B.IsFullLattice K] [C.IsFullLattice K] :
    lengthIndex A B + lengthIndex B C = lengthIndex A C := by
  have : IsDomain O := (IsFractionRing.injective O K).isDomain _
  have hA : A ⊓ B ⊓ C ≤ A := inf_le_left.trans inf_le_left
  have hB : A ⊓ B ⊓ C ≤ B := inf_le_left.trans inf_le_right
  rw [lengthIndex_eq_sub K hA hB, lengthIndex_eq_sub K hB inf_le_right,
    lengthIndex_eq_sub K hA inf_le_right]
  ring

/-- Enlarging the first lattice from `A` to `A' ≥ A` adds `length (A' ⧸ A)` to the index. -/
theorem lengthIndex_eq_lengthIndex_add {A A' : Submodule O V} (B : Submodule O V)
    [A.IsFullLattice K] [A'.IsFullLattice K] [B.IsFullLattice K] (h : A ≤ A') :
    lengthIndex A' B = lengthIndex A B + (length O (A' ⧸ A.comap A'.subtype)).toNat := by
  rw [← lengthIndex_add_lengthIndex K A' A B, lengthIndex_of_le h, add_comm]

/-- The index increases in its first argument, for full lattices `A ≤ A'` and any submodule
`B`. -/
theorem lengthIndex_mono_left {A A' : Submodule O V} (B : Submodule O V) [A.IsFullLattice K]
    [A'.IsFullLattice K] (h : A ≤ A') : lengthIndex A B ≤ lengthIndex A' B := by
  -- Filter `A' ⧸ (A ⊓ B)` through `A` and through `A' ⊓ B`, and `B ⧸ (A ⊓ B)` through `A' ⊓ B`.
  have hAB : A ⊓ B ≤ A' ⊓ B := inf_le_inf_right B h
  have hx := length_quotient_comap_subtype_eq_add (inf_le_left : A ⊓ B ≤ A) h
  have hx' := length_quotient_comap_subtype_eq_add hAB (inf_le_left : A' ⊓ B ≤ A')
  have hy := length_quotient_comap_subtype_eq_add hAB (inf_le_right : A' ⊓ B ≤ B)
  have e₁ (X Y Z : Submodule O V) (hZ : Z ≤ Y) : (X ⊓ Y).comap Z.subtype = X.comap Z.subtype := by
    rw [comap_inf, comap_subtype_eq_top.2 hZ, inf_top_eq]
  have e₂ (X Y Z : Submodule O V) (hZ : Z ≤ X) : (X ⊓ Y).comap Z.subtype = Y.comap Z.subtype := by
    rw [comap_inf, comap_subtype_eq_top.2 hZ, top_inf_eq]
  rw [e₂ A B A le_rfl] at hx
  rw [e₁ A B (A' ⊓ B) inf_le_right, e₂ A' B A' le_rfl] at hx'
  rw [e₁ A B B le_rfl, e₁ A B (A' ⊓ B) inf_le_right, e₁ A' B B le_rfl] at hy
  -- The middle term `(A' ⊓ B) ⧸ (A ⊓ B)` embeds in `A' ⧸ A`, which has finite length.
  have hm := length_quotient_comap_subtype_mono (inf_le_left : A' ⊓ B ≤ A') A
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1
    (length_quotient_comap_subtype_ne_top K (IsLattice.fg K A') A)
  rw [← hl] at hx hm
  obtain ⟨m, hm'⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top l) hm)
  rw [← hm'] at hx' hy hm
  rw [lengthIndex_def, lengthIndex_def]
  rw [hx] at hx'
  have hml : m ≤ l := by exact_mod_cast hm
  clear hx hm hm' hl e₁ e₂
  generalize length O (↥A ⧸ B.comap A.subtype) = x at *
  generalize length O (↥A' ⧸ B.comap A'.subtype) = x' at *
  generalize length O (↥B ⧸ A.comap B.subtype) = y at *
  generalize length O (↥B ⧸ A'.comap B.subtype) = y' at *
  -- Now `x + l = m + x'` and `y = m + y'` with `m ≤ l`; check each finite or infinite case.
  subst hy
  induction y' using ENat.recTopCoe <;> induction x using ENat.recTopCoe <;>
    induction x' using ENat.recTopCoe <;>
    simp only [← ENat.natCast_add, top_add, add_top, ENat.toNat_top, ENat.toNat_natCast,
      ENat.natCast_inj, ENat.top_ne_natCast, ENat.natCast_ne_top] at hx' ⊢ <;> omega

/-- The index decreases in its second argument, for any submodule `A` and full lattices
`B ≤ B'`. -/
theorem lengthIndex_anti_right (A : Submodule O V) {B B' : Submodule O V} [B.IsFullLattice K]
    [B'.IsFullLattice K] (h : B ≤ B') : lengthIndex A B' ≤ lengthIndex A B := by
  rw [← neg_lengthIndex B' A, ← neg_lengthIndex B A, neg_le_neg_iff]
  exact lengthIndex_mono_left K A h

/-- For a `K`-linear `φ` with nonzero determinant mapping the full lattice `L` into itself,
`idx(L, φL) = v(det φ)`, with `v = log ∘ Ring.ordFrac O`. -/
private theorem lengthIndex_map_right_self_eq_log_ordFrac_det_of_mapsTo [Nontrivial O]
    (L : Submodule O V) [L.IsFullLattice K] {φ : V →ₗ[K] V} (hφL : ∀ x ∈ L, φ x ∈ L)
    (hφ : LinearMap.det φ ≠ 0) :
    lengthIndex L (L.map (φ.restrictScalars O)) =
      WithZero.log (Ring.ordFrac O (LinearMap.det φ)) := by
  have : IsDomain O := (IsFractionRing.injective O K).isDomain _
  have := isFullLattice_map_of_det_ne_zero K L hφ
  have hle : L.map (φ.restrictScalars O) ≤ L := map_le_iff_le_comap.2 hφL
  have hφL' : ∀ x ∈ L, φ.restrictScalars O x ∈ L := hφL
  have hr : LinearMap.range ((φ.restrictScalars O).restrict hφL') =
      (L.map (φ.restrictScalars O)).comap L.subtype := by
    rw [LinearMap.range_eq_map, LinearMap.map_restrict, map_subtype_top]
  have hn : length O (L ⧸ LinearMap.range ((φ.restrictScalars O).restrict hφL')) =
      (length O (L ⧸ (L.map (φ.restrictScalars O)).comap L.subtype)).toNat := by
    rw [hr, ENat.natCast_toNat (length_quotient_comap_subtype_ne_top K (IsLattice.fg K L) _)]
  rw [lengthIndex_of_le hle, LinearMap.ordFrac_det_eq_coe_of_length_eq φ L (IsLattice.fg K L)
    IsFullLattice.span_eq_top hφL hφ hn]
  exact (WithZero.log_exp _).symm

/-- **The index of a translate is the valuation of the determinant.** For a full lattice `L` and
a `K`-linear `g` with nonzero determinant, `idx(L, gL) = v(det g)`, with
`v = log ∘ Ring.ordFrac O`. -/
theorem lengthIndex_map_right_self_eq_log_ordFrac_det [Nontrivial O] (L : Submodule O V)
    [L.IsFullLattice K] {g : V →ₗ[K] V} (hg : LinearMap.det g ≠ 0) :
    lengthIndex L (L.map (g.restrictScalars O)) =
      WithZero.log (Ring.ordFrac O (LinearMap.det g)) := by
  have : IsDomain O := (IsFractionRing.injective O K).isDomain _
  have : Module.Finite K V := Module.Finite.of_isFullLattice L
  set M := L.map (g.restrictScalars O)
  have : M.IsFullLattice K := isFullLattice_map_of_det_ne_zero K L hg
  obtain ⟨c, hc, hcM⟩ := IsLattice.exists_ne_zero_forall_smul_mem K L
    (IsFullLattice.span_eq_top (A := K) (M := L)) (IsLattice.fg K M)
  -- `ψ` is multiplication by `c`; it maps `M` into itself, and `ψ ∘ g` maps `L` into itself.
  set ψ : V →ₗ[K] V := algebraMap O K c • LinearMap.id
  have hψ : LinearMap.det ψ ≠ 0 := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    exact pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hc)
  have hψM : ∀ x ∈ M, ψ x ∈ M := fun x hx ↦ by simpa [ψ, algebraMap_smul] using M.smul_mem c hx
  have hψgL : ∀ x ∈ L, (ψ ∘ₗ g) x ∈ L := fun x hx ↦ by
    simpa [ψ, algebraMap_smul] using hcM _ (mem_map_of_mem hx)
  have h₁ := lengthIndex_map_right_self_eq_log_ordFrac_det_of_mapsTo K L hψgL
    (by rw [LinearMap.det_comp]; exact mul_ne_zero hψ hg)
  have h₂ := lengthIndex_map_right_self_eq_log_ordFrac_det_of_mapsTo K M hψM hψ
  have := isFullLattice_map_of_det_ne_zero K M hψ
  rw [LinearMap.restrictScalars_comp, map_comp, ← lengthIndex_add_lengthIndex K L M, h₂,
    LinearMap.det_comp, map_mul, WithZero.log_mul (by simpa using hψ) (by simpa using hg)] at h₁
  linarith

/-- **The index of a homothety.** For a full lattice `L` and `a ∈ Kˣ`,
`idx(L, aL) = v(a) · dim V`, with `v = log ∘ Ring.ordFrac O`. -/
theorem lengthIndex_smul_right_self [Nontrivial O] (L : Submodule O V) [L.IsFullLattice K]
    (a : Kˣ) : lengthIndex L (a • L) = WithZero.log (Ring.ordFrac O (a : K)) * finrank K V := by
  have : Module.Finite K V := Module.Finite.of_isFullLattice L
  have h : a • L = L.map (((a : K) • LinearMap.id : V →ₗ[K] V).restrictScalars O) := by
    ext x
    simp [mem_smul_pointwise_iff_exists, Units.smul_def]
  rw [h, lengthIndex_map_right_self_eq_log_ordFrac_det K L (by simp [LinearMap.det_smul]),
    LinearMap.det_smul, LinearMap.det_id, mul_one, map_pow, WithZero.log_pow, nsmul_eq_mul,
    mul_comm]

/-- **Restriction to submodules.** For full lattices `B ≤ A`, the index of `B ⊓ P` in `A ⊓ P`
increases with the submodule `P` (for instance a subspace of `V`, as an `O`-submodule). -/
theorem lengthIndex_inf_mono {A B : Submodule O V} [A.IsFullLattice K] [B.IsFullLattice K]
    (hBA : B ≤ A) {P Q : Submodule O V} (hPQ : P ≤ Q) :
    lengthIndex (A ⊓ P) (B ⊓ P) ≤ lengthIndex (A ⊓ Q) (B ⊓ Q) := by
  -- `(A ⊓ P) ⧸ (B ⊓ P)` embeds in `(A ⊓ Q) ⧸ (B ⊓ Q)`, which embeds in `A ⧸ B`.
  have hc (S : Submodule O V) : (B ⊓ S).comap (A ⊓ S).subtype = B.comap (A ⊓ S).subtype := by
    rw [comap_inf, comap_subtype_eq_top.2 inf_le_right, inf_top_eq]
  have hfin := ne_top_of_le_ne_top (length_quotient_comap_subtype_ne_top K (IsLattice.fg K A) B)
    (length_quotient_comap_subtype_mono (inf_le_left : A ⊓ Q ≤ A) B)
  rw [lengthIndex_of_le (inf_le_inf_right P hBA), lengthIndex_of_le (inf_le_inf_right Q hBA),
    hc, hc]
  exact_mod_cast ENat.toNat_le_toNat
    (length_quotient_comap_subtype_mono (inf_le_inf_left A hPQ) B) hfin

/-- For full lattices `B ≤ A` and any submodule `P`, `idx(A ⊓ P, B ⊓ P) ≤ idx(A, B)`. -/
theorem lengthIndex_inf_le {A B : Submodule O V} [A.IsFullLattice K] [B.IsFullLattice K]
    (hBA : B ≤ A) (P : Submodule O V) : lengthIndex (A ⊓ P) (B ⊓ P) ≤ lengthIndex A B := by
  simpa only [inf_top_eq] using lengthIndex_inf_mono K hBA (le_top : P ≤ ⊤)

/-- The index of the pullbacks of `t⁻¹B` and `B` to a subspace `W` is `v(t) · dim W`. -/
private theorem lengthIndex_comap_inv_smul [Nontrivial O] (B : Submodule O V) [B.IsFullLattice K]
    (W : Submodule K V) (t : Kˣ) :
    lengthIndex ((t⁻¹ • B).comap (W.subtype.restrictScalars O))
        (B.comap (W.subtype.restrictScalars O)) =
      WithZero.log (Ring.ordFrac O (t : K)) * finrank K W := by
  have : ((t⁻¹ • B).comap (W.subtype.restrictScalars O)).IsFullLattice K :=
    isFullLattice_comap (t⁻¹ • B) W.subtype W.injective_subtype
  rw [← smul_inv_smul t B, comap_restrictScalars_units_smul W.subtype t (t⁻¹ • B),
    inv_smul_smul, lengthIndex_smul_right_self K]

/-- **The index of a homothety on a subspace.** For a full lattice `B`, a subspace `W` of `V` and
`t ∈ Kˣ`, `idx(t⁻¹B ⊓ W, B ⊓ W) = v(t) · dim W`, with `v = log ∘ Ring.ordFrac O`. -/
theorem lengthIndex_inv_smul_inf [Nontrivial O] (B : Submodule O V) [B.IsFullLattice K]
    (W : Submodule K V) (t : Kˣ) :
    lengthIndex (t⁻¹ • B ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) =
      WithZero.log (Ring.ordFrac O (t : K)) * finrank K W := by
  rw [inf_restrictScalars_eq_map_comap, inf_restrictScalars_eq_map_comap,
    lengthIndex_map (f := W.subtype.restrictScalars O) W.injective_subtype,
    lengthIndex_comap_inv_smul K B W t]

/-- **The index on subspaces.** For full lattices `A`, `B`, a subspace `W` of `V` and `t ∈ Kˣ`,
`idx(A ⊓ W, B ⊓ W) ≤ v(t) · dim W + length ((tA + B) ⧸ B)`, with `v = log ∘ Ring.ordFrac O`. -/
theorem lengthIndex_inf_le_log_ordFrac_mul_finrank_add [Nontrivial O] {A B : Submodule O V}
    [A.IsFullLattice K] [B.IsFullLattice K] (W : Submodule K V) (t : Kˣ) :
    lengthIndex (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) ≤
      WithZero.log (Ring.ordFrac O (t : K)) * finrank K W +
        (length O (↥(t • A ⊔ B) ⧸ B.comap (t • A ⊔ B).subtype)).toNat := by
  set ι : W →ₗ[O] V := W.subtype.restrictScalars O
  have : (A.comap ι).IsFullLattice K := isFullLattice_comap A W.subtype W.injective_subtype
  have : ((t⁻¹ • B).comap ι).IsFullLattice K :=
    isFullLattice_comap (t⁻¹ • B) W.subtype W.injective_subtype
  -- `(A ⊓ W) ⧸ (A ⊓ t⁻¹B ⊓ W)` embeds in `A ⧸ (A ⊓ t⁻¹B)`, which `t` maps onto `(tA + B) ⧸ B`.
  -- The first embedding is `mapQ` along `ι` restricted to `A ⊓ W → A`.
  set ιA : A.comap ι →ₗ[O] A := ι.restrict fun _ hx ↦ hx
  have hq : ((t⁻¹ • B).comap ι).comap (A.comap ι).subtype =
      ((t⁻¹ • B).comap A.subtype).comap ιA := by
    rw [← comap_comp, ← comap_comp, LinearMap.subtype_comp_restrict, LinearMap.domRestrict]
  have h₁ : length O (↥(A.comap ι) ⧸ ((t⁻¹ • B).comap ι).comap (A.comap ι).subtype) ≤
      length O (A ⧸ (t⁻¹ • B).comap A.subtype) := by
    rw [hq]
    exact length_le_of_injective (mapQ _ _ ιA le_rfl)
      (LinearMap.ker_eq_bot.1 (by rw [ker_mapQ, mkQ_map_self]))
  have h₂ : length O (A ⧸ (t⁻¹ • B).comap A.subtype) =
      length O (↥(t • A ⊔ B) ⧸ B.comap (t • A ⊔ B).subtype) := by
    have hA : A.map (DistribSMul.toLinearMap O V t) = t • A := pointwise_smul_def.symm
    have hB : (t⁻¹ • B).map (DistribSMul.toLinearMap O V t) = B :=
      pointwise_smul_def.symm.trans (smul_inv_smul t B)
    rw [← length_quotient_comap_subtype_map (f := DistribSMul.toLinearMap O V t)
      (MulAction.injective t) A (t⁻¹ • B), hA, hB,
      ← (LinearMap.quotientInfEquivSupQuotient (t • A) B).length_eq, comap_subtype_self,
      top_inf_eq]
  have h₃ : ((length O (↥(A.comap ι) ⧸
      ((t⁻¹ • B).comap ι).comap (A.comap ι).subtype)).toNat : ℤ) ≤
      (length O (↥(t • A ⊔ B) ⧸ B.comap (t • A ⊔ B).subtype)).toNat := by
    rw [← h₂]
    exact_mod_cast ENat.toNat_le_toNat h₁
      (length_quotient_comap_subtype_ne_top K (IsLattice.fg K A) (t⁻¹ • B))
  have : (B.comap ι).IsFullLattice K := isFullLattice_comap B W.subtype W.injective_subtype
  rw [inf_restrictScalars_eq_map_comap, inf_restrictScalars_eq_map_comap,
    lengthIndex_map (f := ι) W.injective_subtype,
    ← lengthIndex_add_lengthIndex K _ ((t⁻¹ • B).comap ι), lengthIndex_comap_inv_smul K B W t]
  linarith [lengthIndex_le (A.comap ι) ((t⁻¹ • B).comap ι)]

end Lattice

section DiscreteValuationRing

variable {O : Type*} (K : Type*) {V : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V]
  [Module K V] [Module O V] [IsScalarTower O K V]

/-- **The index on subspaces over a discrete valuation ring**: for a uniformizer `ϖ` of `O`, an
integer `d` (of either sign), full lattices `A`, `B` and a subspace `W` of `V`,
`idx(A ⊓ W, B ⊓ W) ≤ d · dim W + length ((ϖ ^ d A + B) ⧸ B)`, where `t ∈ Kˣ` is `ϖ ^ d`. -/
theorem lengthIndex_inf_le_mul_finrank_add {A B : Submodule O V} [A.IsFullLattice K]
    [B.IsFullLattice K] (W : Submodule K V) {ϖ : O} (hϖ : Irreducible ϖ) (d : ℤ) {t : Kˣ}
    (ht : (t : K) = algebraMap O K ϖ ^ d) :
    lengthIndex (A ⊓ W.restrictScalars O) (B ⊓ W.restrictScalars O) ≤
      d * finrank K W + (length O (↥(t • A ⊔ B) ⧸ B.comap (t • A ⊔ B).subtype)).toNat := by
  have h := lengthIndex_inf_le_log_ordFrac_mul_finrank_add K (A := A) (B := B) W t
  rwa [ht, map_zpow₀, Ring.ordFrac_irreducible hϖ, WithZero.log_zpow, WithZero.log_exp,
    smul_eq_mul, mul_one] at h
end DiscreteValuationRing

end Submodule
