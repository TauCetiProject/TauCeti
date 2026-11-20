/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Union
public import TauCeti.Geometry.Convex.PolyhedralCochain.Basic
public import Mathlib.LinearAlgebra.Projection

/-!
# Transverse polyhedral cochains

For a vector `n`, `PolyhedralCochain.transversePart n` keeps the oriented cells whose
affine directions do not contain `n`. This operation is well-defined on cochains:
orientation reversal preserves the direction, and every piece of an oriented
subdivision has the direction of the original cell.

Its image, `transverseSubmodule n`, is precisely the cochains admitting a finite
presentation by cells transverse to `n`. It is therefore a module on the existing
cochain carrier, with an injective inclusion, rather than a choice of representatives.
These are the cochains on which negative-ray sweeps can be defined. Coefficient
maps commute with transverse projection and restrict functorially to this module.

The construction uses `PolyhedralCochain.lift` and
`OrientedCell.IsOrientedSubdivision.direction_eq`; its projection and range API uses
Mathlib's `LinearMap.IsIdempotentElem.mem_range_iff`. No lattice condition on `n` is needed.

## Attribution

Adapted from `Mei/Geometry/Convex/PolyhedralCochain/Transverse/Basic.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author: Codex; original copyright: Mei contributors.
-/

public section

noncomputable section

namespace TauCeti.PolyhedralCochain

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {R E : Type*} [Ring R] [AddCommGroup E] [Module R E] {k : ℕ}

open Classical in
/-- Retain the generators transverse to `n`, and discard the tangent generators.
This descends through both orientation reversal and subdivision. -/
def transversePart (n : V) : PolyhedralCochain R h E k →ₗ[R] PolyhedralCochain R h E k :=
  lift (fun σ => if n ∉ (affineSpan ℝ σ.carrier).direction then mk σ else 0)
    (fun σ => by
      by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction <;>
        ext c <;> simp [hn])
    (fun σ Q hQ => by
      by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction
      · simp only [ite_eq_right (not_not.mpr hn)]
        exact (Finset.sum_eq_zero fun τ hτ =>
          ite_eq_right (not_not.mpr (hQ.direction_eq hτ ▸ hn))).symm
      · rw [ite_eq_left hn]
        have he : ∀ τ ∈ Q,
            (if n ∉ (affineSpan ℝ τ.carrier).direction then mk (R := R) (E := E) τ else 0) =
              mk τ := fun τ hτ => ite_eq_left (fun hm => hn (hQ.direction_eq hτ ▸ hm))
        rw [Finset.sum_congr rfl he]
        ext c
        simpa only [LinearMap.sum_apply] using
          mk_eq_sum_of_isOrientedSubdivision (R := R) hQ c)

open Classical in
/-- Transverse projection keeps exactly the transverse generators. -/
@[simp]
theorem transversePart_mk (n : V) (σ : OrientedCell h k) (c : E) :
    transversePart n (mk (R := R) σ c) =
      if n ∉ (affineSpan ℝ σ.carrier).direction then mk σ c else 0 := by
  classical
  simp only [transversePart, lift_mk]
  split_ifs <;> rfl

open Classical in
/-- Transverse projection can be computed by filtering any finite presentation. -/
theorem transversePart_ofFinsupp (n : V) (f : OrientedCell h k →₀ E) :
    transversePart n (ofFinsupp (R := R) f) =
      ofFinsupp (f.filter fun σ => n ∉ (affineSpan ℝ σ.carrier).direction) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp [Finsupp.filter_zero]
  | add f g hf hg => simp [hf, hg]
  | single σ c =>
    by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction <;> simp [hn]

/-- Retaining transverse cells twice has the same effect as retaining them once. -/
@[simp]
theorem transversePart_transversePart (n : V) (C : PolyhedralCochain R h E k) :
    transversePart n (transversePart n C) = transversePart n C := by
  induction C using induction_on with
  | zero => simp
  | add C D hC hD => simp [hC, hD]
  | mk σ c =>
    by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction <;> simp [hn]

/-- Transverse projection is an idempotent linear endomorphism. -/
theorem isIdempotentElem_transversePart (n : V) :
    IsIdempotentElem (transversePart (R := R) (h := h) (E := E) (k := k) n) := by
  apply LinearMap.ext
  exact transversePart_transversePart n

/-- Cochains admitting a presentation by cells transverse to `n`, as a submodule of
the ordinary polyhedral cochains. -/
def transverseSubmodule (n : V) : Submodule R (PolyhedralCochain R h E k) :=
  LinearMap.range (transversePart n)

/-- A cochain is transverse exactly when transverse projection fixes it. -/
@[simp]
theorem mem_transverseSubmodule_iff (n : V) (C : PolyhedralCochain R h E k) :
    C ∈ transverseSubmodule n ↔ transversePart n C = C :=
  LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_transversePart n)

/-- A transverse generator belongs to the transverse submodule. -/
theorem mk_mem_transverseSubmodule (n : V) (σ : OrientedCell h k)
    (hn : n ∉ (affineSpan ℝ σ.carrier).direction) (c : E) :
    mk (R := R) σ c ∈ transverseSubmodule n := by
  rw [mem_transverseSubmodule_iff]
  simp [hn]

/-- Membership means existence of a finite presentation all of whose nonzero cells
are transverse. No condition is imposed on an arbitrary chosen presentation. -/
theorem mem_transverseSubmodule_iff_exists (n : V) (C : PolyhedralCochain R h E k) :
    C ∈ transverseSubmodule n ↔
      ∃ f : OrientedCell h k →₀ E,
        (∀ σ ∈ f.support, n ∉ (affineSpan ℝ σ.carrier).direction) ∧ ofFinsupp f = C := by
  classical
  constructor
  · rintro ⟨D, rfl⟩
    obtain ⟨f, rfl⟩ := ofFinsupp_surjective D
    refine ⟨f.filter (fun σ => n ∉ (affineSpan ℝ σ.carrier).direction), ?_,
      (transversePart_ofFinsupp n f).symm⟩
    intro σ hσ
    exact (Finset.mem_filter.mp hσ).2
  · rintro ⟨f, hf, rfl⟩
    rw [mem_transverseSubmodule_iff, transversePart_ofFinsupp]
    congr 1
    exact (Finsupp.filter_eq_self_iff _ _).mpr fun σ hσ => hf σ (Finsupp.mem_support_iff.mpr hσ)

/-- Every positive-codimension cochain is transverse to some integral direction.
This is a property of the cochain class; no chosen presentation occurs in the
conclusion. -/
theorem exists_mem_transverseSubmodule (C : PolyhedralCochain R h E (k + 1)) :
    ∃ n : N, C ∈ transverseSubmodule (i n) := by
  classical
  have := h.finiteDimensional
  obtain ⟨f, rfl⟩ := ofFinsupp_surjective C
  obtain ⟨n, hn⟩ := i.exists_forall_apply_notMem_of_span_eq_top h.span_range_eq_top
    (fun σ : f.support => (affineSpan ℝ σ.val.carrier).direction) (fun σ he => by
      have hd := σ.val.finrank_direction_add
      rw [he, finrank_top] at hd
      omega)
  exact ⟨n, (mem_transverseSubmodule_iff_exists (i n) _).mpr
    ⟨f, fun σ hσ => hn ⟨σ, hσ⟩, rfl⟩⟩

/-- To prove a property of transverse cochains, it suffices to prove it for zero,
addition, and generators whose cells are transverse. -/
@[elab_as_elim]
theorem transverse_induction_on (n : V) {p : PolyhedralCochain R h E k → Prop}
    (C : PolyhedralCochain R h E k) (hC : C ∈ transverseSubmodule n)
    (zero : p 0) (add : ∀ C D, p C → p D → p (C + D))
    (mk : ∀ (σ : OrientedCell h k), n ∉ (affineSpan ℝ σ.carrier).direction →
      ∀ c : E, p (mk σ c)) : p C := by
  obtain ⟨D, rfl⟩ := hC
  induction D using induction_on with
  | zero => simpa only [map_zero] using zero
  | add C D hC hD => rw [map_add]; exact add _ _ hC hD
  | mk σ c =>
    by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction
    · simpa only [transversePart_mk, ite_eq_right (not_not.mpr hn)] using zero
    · simpa only [transversePart_mk, ite_eq_left hn] using mk σ hn c

/-- Linear maps on transverse cochains are determined by transverse generators. -/
@[ext]
theorem transverse_hom_ext (n : V) {M : Type*} [AddCommGroup M] [Module R M]
    {f g : transverseSubmodule (R := R) (h := h) (E := E) (k := k) n →ₗ[R] M}
    (H : ∀ (σ : OrientedCell h k) (hn : n ∉ (affineSpan ℝ σ.carrier).direction) (c : E),
      f ⟨mk σ c, mk_mem_transverseSubmodule n σ hn c⟩ =
        g ⟨mk σ c, mk_mem_transverseSubmodule n σ hn c⟩) : f = g := by
  apply LinearMap.ext
  intro C
  have he : ∃ hC, f ⟨(C : PolyhedralCochain R h E k), hC⟩ = g ⟨C, hC⟩ := by
    refine transverse_induction_on n
      (p := fun D => ∃ hD : D ∈ transverseSubmodule n, f ⟨D, hD⟩ = g ⟨D, hD⟩)
      (C : PolyhedralCochain R h E k) C.property ?_ ?_ ?_
    · exact ⟨zero_mem _, (map_zero f).trans (map_zero g).symm⟩
    · rintro D D' ⟨hD, heD⟩ ⟨hD', heD'⟩
      refine ⟨add_mem hD hD', ?_⟩
      calc
        f ⟨D + D', add_mem hD hD'⟩ = f ⟨D, hD⟩ + f ⟨D', hD'⟩ := map_add f ⟨D, hD⟩ ⟨D', hD'⟩
        _ = g ⟨D, hD⟩ + g ⟨D', hD'⟩ := congrArg₂ (· + ·) heD heD'
        _ = g ⟨D + D', add_mem hD hD'⟩ := (map_add g ⟨D, hD⟩ ⟨D', hD'⟩).symm
    · exact fun σ hn c => ⟨mk_mem_transverseSubmodule n σ hn c, H σ hn c⟩
  obtain ⟨_, he⟩ := he
  exact he

/-- The zero vector is tangent to every cell, so its transverse part vanishes. -/
@[simp]
theorem transversePart_zero :
    transversePart (R := R) (h := h) (E := E) (k := k) (0 : V) = 0 := by
  ext σ c
  simp

/-- Rescaling a direction by a nonzero real number does not change transversality. -/
@[simp]
theorem transversePart_smul (n : V) {a : ℝ} (ha : a ≠ 0) :
    transversePart (R := R) (h := h) (E := E) (k := k) (a • n) = transversePart n := by
  ext σ c
  by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction
  · have han := (affineSpan ℝ σ.carrier).direction.smul_mem a hn
    simp [hn, han]
  · have han := ((affineSpan ℝ σ.carrier).direction.smul_mem_iff ha).not.mpr hn
    simp [hn, han]

section Coefficients

variable {E' E'' : Type*} [AddCommGroup E'] [Module R E'] [AddCommGroup E''] [Module R E'']

/-- Coefficient maps commute with extracting the transverse cells. -/
theorem map_transversePart (f : E →ₗ[R] E') (n : V) (C : PolyhedralCochain R h E k) :
    map f (transversePart n C) = transversePart n (map f C) := by
  induction C using induction_on with
  | zero => simp
  | add C D hC hD => simp [hC, hD]
  | mk σ c =>
    by_cases hn : n ∈ (affineSpan ℝ σ.carrier).direction <;> simp [hn]

/-- A coefficient map restricts to the modules of transverse cochains. -/
def transverseMap (f : E →ₗ[R] E') (n : V) :
    transverseSubmodule (R := R) (h := h) (k := k) (E := E) n →ₗ[R]
      transverseSubmodule (R := R) (h := h) (k := k) (E := E') n :=
  (map f).restrict fun C hC => by
    rw [mem_transverseSubmodule_iff] at hC ⊢
    rw [← map_transversePart, hC]

@[simp]
theorem coe_transverseMap (f : E →ₗ[R] E') (n : V)
    (C : transverseSubmodule (R := R) (h := h) (k := k) (E := E) n) :
    (transverseMap f n C : PolyhedralCochain R h E' k) =
      map f (C : PolyhedralCochain R h E k) := (rfl)

@[simp]
theorem transverseMap_id (n : V) :
    transverseMap (h := h) (k := k) (LinearMap.id : E →ₗ[R] E) n = LinearMap.id := by
  ext C
  simp

/-- Restriction of coefficient maps to transverse cochains respects composition. -/
theorem transverseMap_comp (g : E' →ₗ[R] E'') (f : E →ₗ[R] E') (n : V) :
    transverseMap (h := h) (k := k) (g ∘ₗ f) n = transverseMap g n ∘ₗ transverseMap f n := by
  ext C
  simp [map_comp]

end Coefficients

end TauCeti.PolyhedralCochain
