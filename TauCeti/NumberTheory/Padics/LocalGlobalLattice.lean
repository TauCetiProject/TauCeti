/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.Algebra.Module.Lattice
public import TauCeti.NumberTheory.Padics.RatCast
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Lattices in a rational vector space are determined by their localizations

Let `V` be a vector space over `ℚ` and `N` a `ℤ`-submodule of `V`. At a prime `p` its
**localization** is the `ℤ_p`-submodule `N_p` of the completed space `V_p = ℚ_p ⊗[ℚ] V` spanned
by the vectors `1 ⊗ v`, `v ∈ N`. When `N` is a full lattice, that is, finitely generated and
spanning `V`, then `N_p` is a full `ℤ_p`-lattice in `V_p`.

This file proves the local–global principle for lattices: a full lattice is determined by its
localizations, and any family of local lattices which is the family of localizations of a fixed
lattice at almost every prime is the family of localizations of exactly one lattice.

* A vector `v ∈ V` lies in the full lattice `N` exactly when `1 ⊗ v ∈ N_p` at every prime `p`
  (`Submodule.mem_iff_forall_one_tmul_mem_padicLocalization`). In the rational basis of a basis of
  `N`, both sides say that the coordinates of `v` are integers, respectively `p`-adic integers at
  every prime. In particular `M ≤ N` exactly when `M_p ≤ N_p` for every `p`.
* Two full lattices have the same localization at almost every prime
  (`Submodule.eventually_padicLocalization_eq`): a nonzero integer `d` multiplies each into the
  other, and `d` is a `p`-adic unit at almost every prime.
* Given a full lattice `N` and full `ℤ_p`-lattices `X_p ⊆ V_p` with `X_p = N_p` for almost every
  `p`, the lattice `M = {v ∈ V | 1 ⊗ v ∈ X_p for every p}` is the unique full lattice with
  `M_p = X_p` at every prime (`Submodule.existsUnique_isLattice_padicLocalization_eq`).

The last statement is what turns a finite adelic point `g = (g_p)` of the orthogonal group of
`V` into a lattice `g L` with `(g L)_p = g_p L_p`, on which the description of the classes in the
genus of an integral lattice by finite adelic double cosets rests.

## Main definitions

* `Submodule.padicLocalization`: the localization `N_p ⊆ ℚ_p ⊗[ℚ] V` of a `ℤ`-submodule `N`.

## Main results

* `Submodule.padicLocalization_le_iff`: `N_p` is the least `ℤ_p`-submodule containing every
  `1 ⊗ v`, `v ∈ N`.
* `Submodule.isLattice_padicLocalization`: the localization of a full lattice is a full
  `ℤ_p`-lattice.
* `Submodule.mem_padicLocalization_iff_repr_mem`: in the scalar extension of the rational basis
  of a basis of `N`, the localization `N_p` consists of the vectors with `p`-adic integral
  coordinates.
* `Submodule.mem_iff_forall_one_tmul_mem_padicLocalization`,
  `Submodule.le_iff_forall_padicLocalization_le`, `Submodule.eq_iff_forall_padicLocalization_eq`:
  a full lattice is determined by its localizations.
* `Submodule.eventually_padicLocalization_eq`: two full lattices have equal localizations at
  almost every prime.
* `Submodule.exists_eq_one_tmul_add_pow_smul`: `N` is dense in `N_p`.
* `Submodule.IsLattice.exists_forall_pow_smul_mem`: a power of `p` multiplies a finitely
  generated `ℤ_p`-submodule into a full `ℤ_p`-lattice.
* `Submodule.existsUnique_isLattice_padicLocalization_eq`: a family of full local lattices
  agreeing almost everywhere with the localizations of a full lattice is the family of
  localizations of a unique full lattice.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms* (1963), §81E, Theorems 81:14 and 81:18.
* M. Kneser, *Quadratische Formen* (2002), §21.
-/

public section

open Module TensorProduct Filter

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

section Localization

variable (N : Submodule ℤ V) (p : ℕ) [Fact p.Prime]

/-- The **localization** `N_p` of a `ℤ`-submodule `N` of a rational vector space `V` at a prime
`p`: the `ℤ_p`-submodule of the completed space `ℚ_p ⊗[ℚ] V` spanned by the vectors `1 ⊗ v` with
`v ∈ N`. -/
noncomputable def padicLocalization : Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V) :=
  span ℤ_[p] ((fun v : V ↦ (1 : ℚ_[p]) ⊗ₜ[ℚ] v) '' N)

/-- The localization `N_p` is the `ℤ_p`-span of the vectors `1 ⊗ v` with `v ∈ N`. -/
theorem padicLocalization_def :
    N.padicLocalization p = span ℤ_[p] ((fun v : V ↦ (1 : ℚ_[p]) ⊗ₜ[ℚ] v) '' N) :=
  (rfl)

variable {N p}

/-- For `v ∈ N`, the vector `1 ⊗ v` lies in the localization `N_p`. -/
theorem one_tmul_mem_padicLocalization {v : V} (hv : v ∈ N) :
    (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ N.padicLocalization p :=
  subset_span ⟨v, hv, rfl⟩

/-- **Universal property of the localization.** `N_p` is contained in a `ℤ_p`-submodule `X` of
`ℚ_p ⊗[ℚ] V` exactly when `X` contains `1 ⊗ v` for every `v ∈ N`. -/
theorem padicLocalization_le_iff {X : Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)} :
    N.padicLocalization p ≤ X ↔ ∀ v ∈ N, (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ X := by
  rw [padicLocalization, span_le, Set.image_subset_iff]
  rfl

/-- Localization is monotone: `M ≤ N` gives `M_p ≤ N_p`. -/
theorem padicLocalization_mono {M : Submodule ℤ V} (h : M ≤ N) :
    M.padicLocalization p ≤ N.padicLocalization p :=
  span_mono (Set.image_mono h)

/-- The localization of the span of a set `s` is the `ℤ_p`-span of the vectors `1 ⊗ v`,
`v ∈ s`. -/
theorem padicLocalization_span (s : Set V) :
    (span ℤ s).padicLocalization p = span ℤ_[p] ((fun v : V ↦ (1 : ℚ_[p]) ⊗ₜ[ℚ] v) '' s) := by
  have h : (fun v : V ↦ (1 : ℚ_[p]) ⊗ₜ[ℚ] v) '' span ℤ s =
      span ℤ ((fun v : V ↦ (1 : ℚ_[p]) ⊗ₜ[ℚ] v) '' s) :=
    (map_coe ((TensorProduct.mk ℚ ℚ_[p] V 1).restrictScalars ℤ) _).symm.trans
      (congrArg SetLike.coe (map_span _ s))
  rw [padicLocalization, h, span_span_of_tower]

variable (N p) in
/-- The localization of a full lattice is a full `ℤ_p`-lattice in `ℚ_p ⊗[ℚ] V`. -/
instance isLattice_padicLocalization [N.IsLattice ℚ] :
    (N.padicLocalization p).IsLattice ℚ_[p] where
  fg := by
    obtain ⟨s, hs⟩ := IsLattice.fg (A := ℚ) (M := N)
    rw [← hs, padicLocalization_span]
    exact fg_def.mpr ⟨_, s.finite_toSet.image _, rfl⟩
  span_eq_top := by
    refine eq_top_iff'.mpr fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => exact add_mem hx hy
    | tmul a v =>
      -- A nonzero integer multiple `n • v` of `v` lies in `N`, and `a ⊗ v = (a / n) • (1 ⊗ n • v)`.
      obtain ⟨n, hn, hv⟩ := IsLattice.exists_ne_zero_smul_mem ℚ N
        (IsLattice.span_eq_top (A := ℚ)) v
      have hn' : (n : ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hn
      have h : a ⊗ₜ[ℚ] v = (a / n) • ((1 : ℚ_[p]) ⊗ₜ[ℚ] (n • v)) := by
        rw [tmul_smul, ← Int.cast_smul_eq_zsmul ℚ_[p], smul_smul, div_mul_cancel₀ a hn',
          smul_tmul', smul_eq_mul, mul_one]
      rw [h]
      exact smul_mem _ _ (subset_span (one_tmul_mem_padicLocalization hv))

section Coordinates

variable [N.IsLattice ℚ] {ι : Type*} (e : Basis ι ℤ N)

/-- The localization of a full lattice `N` is the `ℤ_p`-span of the scalar extension of the
rational basis of a basis of `N`. -/
theorem padicLocalization_eq_span_range :
    N.padicLocalization p = span ℤ_[p] (Set.range ((e.extendOfIsLattice ℚ).baseChange ℚ_[p])) := by
  conv_lhs => rw [← e.span_range_extendOfIsLattice (K := ℚ)]
  rw [padicLocalization_span, ← Set.range_comp]
  congr 2
  ext i
  simp

/-- **The localization in coordinates.** In the scalar extension of the rational basis of a basis
`e` of a full lattice `N`, the localization `N_p` consists of the vectors whose coordinates are
`p`-adic integers. -/
theorem mem_padicLocalization_iff_repr_mem (x : ℚ_[p] ⊗[ℚ] V) :
    x ∈ N.padicLocalization p ↔
      ∀ i, ‖((e.extendOfIsLattice ℚ).baseChange ℚ_[p]).repr x i‖ ≤ 1 := by
  rw [padicLocalization_eq_span_range e, Basis.mem_span_iff_repr_mem]
  refine forall_congr' fun i ↦ ⟨?_, fun h ↦ ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨c, hc⟩
  rw [← hc]
  exact c.norm_le_one

end Coordinates

end Localization

section LocalGlobal

variable {N : Submodule ℤ V} [N.IsLattice ℚ]

/-- **A full lattice is determined by its localizations.** A vector `v` lies in a full lattice `N`
exactly when `1 ⊗ v` lies in the localization `N_p` at every prime `p`. -/
theorem mem_iff_forall_one_tmul_mem_padicLocalization (v : V) :
    v ∈ N ↔ ∀ p : Nat.Primes, (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ N.padicLocalization p := by
  let e := Free.chooseBasis ℤ N
  let b := e.extendOfIsLattice ℚ
  -- Globally, membership is integrality of the rational coordinates of `v` in `b`.
  have hglob : v ∈ N ↔ ∀ i, (b.repr v i).den = 1 := by
    conv_lhs => rw [← e.span_range_extendOfIsLattice (K := ℚ)]
    rw [Basis.mem_span_iff_repr_mem]
    refine forall_congr' fun i ↦ ⟨?_, fun h ↦ ⟨_, (Rat.den_eq_one_iff _).mp h⟩⟩
    rintro ⟨n, hn⟩
    rw [← hn, algebraMap_int_eq, eq_intCast, Rat.den_intCast]
  -- Locally, membership is `p`-adic integrality of the same coordinates.
  have hloc (p : Nat.Primes) : (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ N.padicLocalization p ↔
      ∀ i, ‖((b.repr v i : ℚ) : ℚ_[p])‖ ≤ 1 := by
    rw [mem_padicLocalization_iff_repr_mem e]
    simp [b, Basis.baseChange_repr_tmul, Rat.smul_def]
  simp only [hglob, hloc, forall_comm (α := Nat.Primes),
    Padic.forall_norm_rat_le_one_iff_den_eq_one]

/-- A submodule `M` is contained in a full lattice `N` exactly when every localization of `M` is
contained in the corresponding localization of `N`. -/
theorem le_iff_forall_padicLocalization_le (M : Submodule ℤ V) :
    M ≤ N ↔ ∀ p : Nat.Primes, M.padicLocalization p ≤ N.padicLocalization p :=
  ⟨fun h _ ↦ padicLocalization_mono h, fun h v hv ↦
    (mem_iff_forall_one_tmul_mem_padicLocalization v).mpr fun p ↦
      h p (one_tmul_mem_padicLocalization hv)⟩

/-- Two full lattices are equal exactly when their localizations are equal at every prime. -/
theorem eq_iff_forall_padicLocalization_eq (M : Submodule ℤ V) [M.IsLattice ℚ] :
    M = N ↔ ∀ p : Nat.Primes, M.padicLocalization p = N.padicLocalization p :=
  ⟨fun h _ ↦ h ▸ rfl, fun h ↦ le_antisymm
    ((le_iff_forall_padicLocalization_le M).mpr fun p ↦ (h p).le)
    ((le_iff_forall_padicLocalization_le N).mpr fun p ↦ (h p).ge)⟩

/-- If `M` is finitely generated and `N` is a full lattice, then `M_p ≤ N_p` at almost every
prime: a nonzero integer `r` multiplies `M` into `N`, and `r` is a `p`-adic unit at almost every
prime. -/
theorem eventually_padicLocalization_le {M : Submodule ℤ V} (hM : M.FG) :
    ∀ᶠ p : Nat.Primes in cofinite, M.padicLocalization p ≤ N.padicLocalization p := by
  obtain ⟨r, hr0, hr⟩ :=
    IsLattice.exists_ne_zero_forall_smul_mem ℚ N (IsLattice.span_eq_top (A := ℚ) (M := N)) hM
  filter_upwards [Padic.eventually_norm_rat_eq_one (Int.cast_ne_zero.mpr hr0 : (r : ℚ) ≠ 0)]
    with p hp
  have hu : IsUnit (r : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_def, PadicInt.coe_intCast]
    simpa using hp
  refine padicLocalization_le_iff.mpr fun v hv ↦ ?_
  have h := one_tmul_mem_padicLocalization (p := p) (hr v hv)
  rw [tmul_smul, ← Int.cast_smul_eq_zsmul ℤ_[p]] at h
  exact (smul_mem_iff_of_isUnit _ hu).mp h

/-- **Two full lattices have the same localization at almost every prime.** -/
theorem eventually_padicLocalization_eq (M : Submodule ℤ V) [M.IsLattice ℚ] :
    ∀ᶠ p : Nat.Primes in cofinite, M.padicLocalization p = N.padicLocalization p := by
  filter_upwards [eventually_padicLocalization_le (N := N) (IsLattice.fg (A := ℚ) (M := M)),
    eventually_padicLocalization_le (N := M) (IsLattice.fg (A := ℚ) (M := N))] with p h₁ h₂
  exact le_antisymm h₁ h₂

end LocalGlobal

section Density

variable {N : Submodule ℤ V} {p : ℕ} [Fact p.Prime]

/-- **`N` is dense in its localization.** Every vector of `N_p` is congruent to a vector `1 ⊗ w`,
`w ∈ N`, modulo `p ^ m • N_p`. -/
theorem exists_eq_one_tmul_add_pow_smul {x : ℚ_[p] ⊗[ℚ] V} (hx : x ∈ N.padicLocalization p)
    (m : ℕ) : ∃ w ∈ N, ∃ t ∈ N.padicLocalization p,
      x = (1 : ℚ_[p]) ⊗ₜ[ℚ] w + (p : ℤ_[p]) ^ m • t := by
  induction hx using span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    exact ⟨w, hw, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, t, ht, rfl⟩ := hx
    obtain ⟨w', hw', t', ht', rfl⟩ := hy
    exact ⟨w + w', add_mem hw hw', t + t', add_mem ht ht', by rw [tmul_add, smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨w, hw, t, ht, rfl⟩ := hx
    -- Write `c = a + c' p ^ m` with `a ∈ ℕ`, and move the integer part `a` into `N`.
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec m c)
    refine ⟨PadicInt.appr c m • w, nsmul_mem hw _,
      c' • (1 : ℚ_[p]) ⊗ₜ[ℚ] w + c • t,
      add_mem (smul_mem _ _ (one_tmul_mem_padicLocalization hw)) (smul_mem _ _ ht), ?_⟩
    rw [tmul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[p]]
    generalize (PadicInt.appr c m : ℤ_[p]) = a at hc' ⊢
    obtain rfl : c = a + c' * (p : ℤ_[p]) ^ m := by rw [hc']; ring
    module

end Density

section Existence

/-- **Commensurability over `ℤ_p`.** A power of `p` multiplies a finitely generated
`ℤ_p`-submodule of a `ℚ_p`-vector space into a full `ℤ_p`-lattice. -/
theorem IsLattice.exists_forall_pow_smul_mem (p : ℕ) [Fact p.Prime] {W : Type*} [AddCommGroup W]
    [Module ℚ_[p] W] [Module ℤ_[p] W] [IsScalarTower ℤ_[p] ℚ_[p] W] (Z : Submodule ℤ_[p] W)
    [Z.IsLattice ℚ_[p]] {Y : Submodule ℤ_[p] W} (hY : Y.FG) :
    ∃ k : ℕ, ∀ x ∈ Y, (p : ℤ_[p]) ^ k • x ∈ Z := by
  obtain ⟨k, hk⟩ := IsLattice.exists_maximalIdeal_pow_smul_le ℚ_[p] Z hY
  refine ⟨k, fun x hx ↦ hk (smul_mem_smul ?_ hx)⟩
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k

variable {N : Submodule ℤ V} [N.IsLattice ℚ]

/-- At each prime a power `p ^ k p` multiplies `X p` into `N_p` and `N_p` into `X p`, and `k p`
vanishes at almost every prime. -/
private theorem exists_pow_smul_mem_padicLocalization
    (X : ∀ p : Nat.Primes, Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)) [∀ p, (X p).IsLattice ℚ_[p]]
    (hX : ∀ᶠ p : Nat.Primes in cofinite, X p = N.padicLocalization p) :
    ∃ k : Nat.Primes → ℕ, (∀ᶠ p in cofinite, k p = 0) ∧
      (∀ (p : Nat.Primes) {x}, x ∈ X p → (p : ℤ_[p]) ^ k p • x ∈ N.padicLocalization p) ∧
      ∀ (p : Nat.Primes) {x}, x ∈ N.padicLocalization p → (p : ℤ_[p]) ^ k p • x ∈ X p := by
  classical
  choose k₁ hk₁ using fun p : Nat.Primes ↦ IsLattice.exists_forall_pow_smul_mem p
    (N.padicLocalization p) (IsLattice.fg (A := ℚ_[p]) (M := X p))
  choose k₂ hk₂ using fun p : Nat.Primes ↦ IsLattice.exists_forall_pow_smul_mem p (X p)
    (IsLattice.fg (A := ℚ_[p]) (M := N.padicLocalization p))
  refine ⟨fun p ↦ if X p = N.padicLocalization p then 0 else k₁ p + k₂ p,
    hX.mono fun p h ↦ by simp [h], fun p x hx ↦ ?_, fun p x hx ↦ ?_⟩
  · by_cases h : X p = N.padicLocalization p
    · simpa [h] using h ▸ hx
    · simp only [h, ite_false, add_comm (k₁ p), pow_add, mul_smul]
      exact smul_mem _ _ (hk₁ p x hx)
  · by_cases h : X p = N.padicLocalization p
    · simpa [h] using hx
    · simp only [h, ite_false, pow_add, mul_smul]
      exact smul_mem _ _ (hk₂ p x hx)

omit [N.IsLattice ℚ] in
/-- Away from `p`, the rational number `r = D' p / p ^ k p` is `q ^ k q` times a `q`-adic integer,
so `r • w` stays in `X q` for `w ∈ N`; at `p` it lies in `X p` by hypothesis. -/
private theorem one_tmul_smul_mem {X : ∀ p : Nat.Primes, Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)}
    {k D' : Nat.Primes → ℕ}
    (hkN : ∀ (p : Nat.Primes) {x}, x ∈ N.padicLocalization p → (p : ℤ_[p]) ^ k p • x ∈ X p)
    (hD'q : ∀ {p q : Nat.Primes}, q ≠ p → (q : ℕ) ^ k q ∣ D' p) {p : Nat.Primes} {r : ℚ}
    (hr : r = (D' p : ℚ) / (p : ℚ) ^ k p) {w : V} (hw : w ∈ N)
    (hpX : (1 : ℚ_[p]) ⊗ₜ[ℚ] (r • w) ∈ X p) (q : Nat.Primes) :
    (1 : ℚ_[q]) ⊗ₜ[ℚ] (r • w) ∈ X q := by
  by_cases hqp : q = p
  · subst hqp
    exact hpX
  · obtain ⟨m, hm⟩ := hD'q hqp
    have hpq : ‖(p : ℚ_[q])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr
      ((Nat.coprime_primes q.2 p.2).mpr fun h ↦ hqp (Subtype.ext h))
    have hc : ‖(m : ℚ_[q]) / (p : ℚ_[q]) ^ k p‖ ≤ 1 := by
      rw [norm_div, norm_pow, hpq, one_pow, div_one]
      simpa using Padic.norm_int_le_one (p := q) m
    obtain ⟨c, hc'⟩ : ∃ c : ℤ_[q], (c : ℚ_[q]) = (m : ℚ_[q]) / (p : ℚ_[q]) ^ k p :=
      ⟨⟨_, hc⟩, rfl⟩
    have hrq : (r : ℚ_[q]) = (q : ℚ_[q]) ^ k q * c := by
      rw [hr, hm, hc']
      push_cast
      ring
    have h : (1 : ℚ_[q]) ⊗ₜ[ℚ] (r • w) = (q : ℤ_[q]) ^ k q • c • (1 : ℚ_[q]) ⊗ₜ[ℚ] w := by
      rw [algebra_compatible_smul ℚ_[q] ((q : ℤ_[q]) ^ k q), algebra_compatible_smul ℚ_[q] c,
        PadicInt.algebraMap_apply, PadicInt.algebraMap_apply, tmul_smul,
        ← algebraMap_smul ℚ_[q] r, eq_ratCast, hrq, smul_smul]
      simp
    rw [h]
    exact hkN q (smul_mem _ _ (one_tmul_mem_padicLocalization hw))

omit [N.IsLattice ℚ] in
/-- The local step of `exists_isLattice_padicLocalization_eq`: every `y ∈ X p` has `D' p • y` of
the form `1 ⊗ v + D' p • p ^ k p • t` with `t ∈ N_p` and `v ∈ V` such that `1 ⊗ v ∈ X q` at
every prime `q`. -/
private theorem exists_forall_one_tmul_mem_add
    {X : ∀ p : Nat.Primes, Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)} {k D' : Nat.Primes → ℕ}
    (hkX : ∀ (p : Nat.Primes) {x}, x ∈ X p → (p : ℤ_[p]) ^ k p • x ∈ N.padicLocalization p)
    (hkN : ∀ (p : Nat.Primes) {x}, x ∈ N.padicLocalization p → (p : ℤ_[p]) ^ k p • x ∈ X p)
    (hD'q : ∀ {p q : Nat.Primes}, q ≠ p → (q : ℕ) ^ k q ∣ D' p) {p : Nat.Primes} {y}
    (hy : y ∈ X p) :
    ∃ v : V, (∀ q : Nat.Primes, (1 : ℚ_[q]) ⊗ₜ[ℚ] v ∈ X q) ∧ ∃ t ∈ N.padicLocalization p,
      (D' p : ℤ_[p]) • y = (1 : ℚ_[p]) ⊗ₜ[ℚ] v + (D' p : ℤ_[p]) • (p : ℤ_[p]) ^ k p • t := by
  obtain ⟨w, hw, t, ht, hwt⟩ := exists_eq_one_tmul_add_pow_smul (hkX p hy) (2 * k p)
  obtain ⟨r, hr⟩ : ∃ r : ℚ, r = (D' p : ℚ) / (p : ℚ) ^ k p := ⟨_, rfl⟩
  have hy' : (D' p : ℤ_[p]) • y =
      (1 : ℚ_[p]) ⊗ₜ[ℚ] (r • w) + (D' p : ℤ_[p]) • (p : ℤ_[p]) ^ k p • t := by
    have hrp : (r : ℚ_[p]) * (p : ℚ_[p]) ^ k p = D' p := by
      rw [hr, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Rat.cast_natCast,
        div_mul_cancel₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr p.2.ne_zero))]
    rw [tmul_smul, ← algebraMap_smul ℚ_[p] r, eq_sub_of_add_eq hwt.symm, eq_ratCast]
    simp only [algebra_compatible_smul ℚ_[p] (D' p : ℤ_[p]),
      algebra_compatible_smul ℚ_[p] ((p : ℤ_[p]) ^ k p),
      algebra_compatible_smul ℚ_[p] ((p : ℤ_[p]) ^ (2 * k p)), PadicInt.algebraMap_apply,
      PadicInt.coe_pow, PadicInt.coe_natCast, ← hrp]
    module
  refine ⟨r • w, one_tmul_smul_mem hkN hD'q hr hw ?_, t, ht, hy'⟩
  rw [eq_sub_of_add_eq hy'.symm]
  exact sub_mem (smul_mem _ _ hy) (smul_mem _ _ (hkN p ht))

open scoped Pointwise in
/-- The existence half of `Submodule.existsUnique_isLattice_padicLocalization_eq`: the lattice
`M = {v ∈ V | 1 ⊗ v ∈ X p for every p}` has `M_p = X p` at every prime. -/
private theorem exists_isLattice_padicLocalization_eq
    (X : ∀ p : Nat.Primes, Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)) [∀ p, (X p).IsLattice ℚ_[p]]
    (hX : ∀ᶠ p : Nat.Primes in cofinite, X p = N.padicLocalization p) :
    ∃ M : Submodule ℤ V, M.IsLattice ℚ ∧ ∀ p : Nat.Primes, M.padicLocalization p = X p := by
  obtain ⟨k, hk, hkX, hkN⟩ := exists_pow_smul_mem_padicLocalization X hX
  obtain ⟨D, D', hD0, hD, hD'q, hD'u⟩ := Padic.exists_nat_eq_pow_mul k hk
  have hDsmul (p : Nat.Primes) (x : ℚ_[p] ⊗[ℚ] V) :
      (D : ℤ_[p]) • x = (D' p : ℤ_[p]) • (p : ℤ_[p]) ^ k p • x := by
    rw [hD p, smul_smul, Nat.cast_mul, Nat.cast_pow, mul_comm]
  -- The candidate `M = {v | 1 ⊗ v ∈ X p for every p}` lies between `D • N` and `D⁻¹ • N`.
  let M : Submodule ℤ V :=
    { carrier := {v | ∀ p : Nat.Primes, (1 : ℚ_[p]) ⊗ₜ[ℚ] v ∈ X p}
      add_mem' := fun ha hb p ↦ by simpa only [tmul_add] using add_mem (ha p) (hb p)
      zero_mem' := fun p ↦ by simp
      smul_mem' := fun n v hv p ↦ by simpa only [tmul_smul] using zsmul_mem (hv p) n }
  have hNM {v : V} (hv : v ∈ N) : D • v ∈ M := fun p ↦ by
    rw [tmul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[p], hDsmul]
    exact smul_mem _ _ (hkN p (one_tmul_mem_padicLocalization hv))
  have hMN {v : V} (hv : v ∈ M) : D • v ∈ N := by
    refine (mem_iff_forall_one_tmul_mem_padicLocalization _).mpr fun p ↦ ?_
    rw [tmul_smul, ← Nat.cast_smul_eq_nsmul ℤ_[p], hDsmul]
    exact smul_mem _ _ (hkX p (hv p))
  refine ⟨M, IsLattice.of_nsmul_mem_of_nsmul_mem hD0 (fun v hv ↦ hNM hv) fun v hv ↦ hMN hv,
    fun p ↦ le_antisymm (padicLocalization_le_iff.mpr fun v hv ↦ hv p) fun y hy ↦ ?_⟩
  -- `M_p ⊇ X p`. First, `p ^ k p • N_p ⊆ M_p`, because `D • N ⊆ M` and `D' p` is a unit.
  have hNMp {x} (hx : x ∈ N.padicLocalization p) :
      (p : ℤ_[p]) ^ k p • x ∈ M.padicLocalization p := by
    have hle : N.padicLocalization p ≤
        (M.padicLocalization p).comap (DistribSMul.toLinearMap ℤ_[p] _ (D : ℤ_[p])) :=
      padicLocalization_le_iff.mpr fun v hv ↦ by
        rw [mem_comap, DistribSMul.toLinearMap_apply, Nat.cast_smul_eq_nsmul, ← tmul_smul]
        exact one_tmul_mem_padicLocalization (hNM hv)
    have h := hle hx
    rw [mem_comap, DistribSMul.toLinearMap_apply, hDsmul] at h
    exact (smul_mem_iff_of_isUnit _ (hD'u p)).mp h
  obtain ⟨v, hv, t, ht, hy'⟩ := exists_forall_one_tmul_mem_add hkX hkN hD'q hy
  refine (smul_mem_iff_of_isUnit _ (hD'u p)).mp ?_
  rw [hy']
  exact add_mem (one_tmul_mem_padicLocalization (N := M) hv) (smul_mem _ _ (hNMp ht))

/-- **The local–global correspondence for lattices.** Let `N` be a full lattice in `V` and, for
every prime `p`, let `X p` be a full `ℤ_p`-lattice in `ℚ_p ⊗[ℚ] V`, with `X p = N_p` at almost
every prime. Then exactly one full lattice `M` has `M_p = X p` at every prime. -/
theorem existsUnique_isLattice_padicLocalization_eq
    (X : ∀ p : Nat.Primes, Submodule ℤ_[p] (ℚ_[p] ⊗[ℚ] V)) [∀ p, (X p).IsLattice ℚ_[p]]
    (hX : ∀ᶠ p : Nat.Primes in cofinite, X p = N.padicLocalization p) :
    ∃! M : Submodule ℤ V, M.IsLattice ℚ ∧ ∀ p : Nat.Primes, M.padicLocalization p = X p := by
  refine existsUnique_of_exists_of_unique (exists_isLattice_padicLocalization_eq X hX) ?_
  rintro M M' ⟨hM, hMX⟩ ⟨hM', hM'X⟩
  exact (eq_iff_forall_padicLocalization_eq M).mpr fun p ↦ (hMX p).trans (hM'X p).symm

end Existence

end Submodule
