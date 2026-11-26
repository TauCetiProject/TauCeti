/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Valuation.ValuationRing
public import TauCeti.Algebra.Module.Presentation.Quadratic

import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-!
# Finitely presented modules over a valuation ring

Over a valuation ring `V`, every finitely generated submodule `N` of `V^n` is carried by an
automorphism of `V^n` onto a diagonal submodule `∏ i, (x i)` (the stacked bases theorem), so every
finitely presented `V`-module is a finite product of cyclic modules `V ⧸ (x i)`; it is torsion
exactly when all the `x i` are nonzero. No noetherian or discreteness hypothesis is needed, so
this applies to the ring of integers `O_C` of a complete algebraically closed nonarchimedean field,
where finitely generated ideals are principal although `O_C` is not noetherian.

The proof diagonalizes one row and column at a time. The coordinates of the elements of `N`
generate finitely generated ideals of `V`, which are principal and totally ordered, so there is a
pivot: an element `k₀ ∈ N` and a coordinate `j₀` with `a = k₀ j₀` dividing every coordinate of
every element of `N`. Writing `k₀ = a • u` with `u j₀ = 1`, a transvection followed by a
transposition of coordinates moves `u` to the first basis vector, and then `N` splits as
`(a) × N₂` with `N₂` a finitely generated submodule of `V^(n-1)`.

A finitely presented torsion module is moreover quadratically presented, by a direct argument:
for a surjection `π : V^n → M`, the kernel of `π` is finitely generated and torsion-free, hence flat
and free over the local Bézout domain `V`, and of rank `n` because `M` has rank zero.

## Main results

* `TauCeti.IsQuadraticallyPresented.of_isTorsion`: a finitely presented torsion `V`-module is
  quadratically presented.
* `TauCeti.exists_linearEquiv_map_eq_pi_span_singleton`: a finitely generated submodule of `V^n`
  is diagonal after an automorphism of `V^n`.
* `TauCeti.exists_linearEquiv_pi_quotient_span_singleton`: a finitely presented `V`-module is
  isomorphic to `∏ i : Fin n, V ⧸ (x i)`.
* `TauCeti.exists_linearEquiv_pi_quotient_span_singleton_of_isTorsion`: a finitely presented
  torsion `V`-module is isomorphic to `∏ i : Fin n, V ⧸ (x i)` with all `x i ≠ 0`.

## References

* R. B. Warfield, Jr., *Decomposability of finitely presented modules*, Proc. Amer. Math. Soc.
  25 (1970), 167–172.
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539): torsion-free modules over
  valuation rings are flat.
-/

public section

open Module LinearMap Submodule

namespace TauCeti

variable {V : Type*} [CommRing V] [IsDomain V] [ValuationRing V]

/-- A pivot of a finitely generated submodule `N` of `V^(n+1)`: an element `k₀ ∈ N` and a
coordinate `j₀` such that `k₀ j₀` divides every coordinate of every element of `N`. -/
private theorem exists_pivot {n : ℕ} {N : Submodule V (Fin (n + 1) → V)} (hN : N.FG) :
    ∃ j₀, ∃ k₀ ∈ N, ∀ k ∈ N, ∀ j, k₀ j₀ ∣ k j := by
  classical
  -- The ideals of `j`-th coordinates are totally ordered; take a largest one.
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ
    (fun j ↦ N.map (proj j : (Fin (n + 1) → V) →ₗ[V] V)) Finset.univ_nonempty
  obtain ⟨a, ha⟩ := (IsBezout.isPrincipal_of_FG _ (hN.map (proj j₀))).principal
  obtain ⟨k₀, hk₀, rfl⟩ : a ∈ N.map (proj j₀) := ha ▸ mem_span_singleton_self a
  refine ⟨j₀, k₀, hk₀, fun k hk j ↦ ?_⟩
  have hkj := hj₀ j (Finset.mem_univ j) (mem_map_of_mem (f := proj j) hk)
  rw [ha] at hkj
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hkj
  exact ⟨c, by simpa [mul_comm] using hc.symm⟩

omit [ValuationRing V] in
/-- Moving a pivot to the first coordinate: if `a = k₀ j₀ ≠ 0` divides every coordinate of every
element of `N`, an automorphism of `V^(n+1)` sends `k₀` to `a` times the first basis vector and
keeps the coordinates of the elements of `N` divisible by `a`. -/
private theorem exists_linearEquiv_pivot {n : ℕ} {N : Submodule V (Fin (n + 1) → V)}
    {j₀ : Fin (n + 1)} {k₀ : Fin (n + 1) → V} (ha : k₀ j₀ ≠ 0) (hdvd : ∀ k ∈ N, ∀ j, k₀ j₀ ∣ k j)
    (hk₀ : k₀ ∈ N) :
    ∃ Φ : (Fin (n + 1) → V) ≃ₗ[V] (Fin (n + 1) → V), Pi.single 0 (k₀ j₀) ∈ N.map Φ.toLinearMap ∧
      ∀ k ∈ N.map Φ.toLinearMap, k₀ j₀ ∣ k 0 := by
  classical
  -- Write `k₀ = k₀ j₀ • u`; then `u j₀ = 1`.
  choose u hu using hdvd k₀ hk₀
  have hu₀ : u j₀ = 1 := mul_left_cancel₀ ha (by rw [mul_one, ← hu])
  -- The transvection `y ↦ y + y j₀ • (e_{j₀} - u)` sends `u` to `e_{j₀}`.
  let T : (Fin (n + 1) → V) ≃ₗ[V] (Fin (n + 1) → V) := .ofLinearMap
    (LinearMap.id + (proj j₀).smulRight (Pi.single j₀ 1 - u))
    (LinearMap.id + (proj j₀).smulRight (u - Pi.single j₀ 1))
    (by ext y j; simp [hu₀]; ring) (by ext y j; simp [hu₀]; ring)
  have hT (y : Fin (n + 1) → V) (j) :
      T y j = y j + y j₀ * ((Pi.single j₀ (1 : V) : Fin (n + 1) → V) j - u j) := by
    simp [T]
  -- The transposition of the coordinates `0` and `j₀` then moves `e_{j₀}` to `e_0`.
  let P : (Fin (n + 1) → V) ≃ₗ[V] (Fin (n + 1) → V) :=
    LinearEquiv.funCongrLeft V V (Equiv.swap j₀ 0)
  refine ⟨T.trans P, ⟨k₀, hk₀, ?_⟩, ?_⟩
  · ext j
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, P, LinearEquiv.funCongrLeft_apply,
      funLeft_apply, hT]
    rw [hu (Equiv.swap j₀ 0 j)]
    by_cases hj : j = 0
    · subst hj
      simp [hu₀]
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (by simpa [Equiv.swap_apply_eq_iff] using hj)]
      ring
  · rintro _ ⟨k, hk, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, P, LinearEquiv.funCongrLeft_apply,
      funLeft_apply, hT]
    exact dvd_add (hdvd k hk _) (dvd_mul_of_dvd_left (hdvd k hk j₀) _)

omit [IsDomain V] [ValuationRing V] in
/-- Splitting off the first coordinate: if `N ≤ V^(n+1)` contains `a e_0` and the first coordinate
of each of its elements is divisible by `a`, then `N` consists of the vectors whose first
coordinate is divisible by `a` and whose tail lies in the image `N₂` of `N` under `Fin.tail`. -/
private theorem mem_iff_dvd_and_mem_map_tail {n : ℕ} {N : Submodule V (Fin (n + 1) → V)} {a : V}
    (ha : Pi.single 0 a ∈ N) (hdvd : ∀ k ∈ N, a ∣ k 0) (y : Fin (n + 1) → V) :
    y ∈ N ↔ a ∣ y 0 ∧ funLeft V V Fin.succ y ∈ N.map (funLeft V V Fin.succ) := by
  refine ⟨fun hy ↦ ⟨hdvd y hy, mem_map_of_mem hy⟩, ?_⟩
  rintro ⟨⟨d, hd⟩, ⟨k, hk, hky⟩⟩
  obtain ⟨e, he⟩ := hdvd k hk
  -- `y = k + (d - e) • a e_0`, comparing coordinates.
  have : y = k + (d - e) • Pi.single 0 a := by
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp [hd, he]
      ring
    · simpa using congr_fun hky.symm i
  rw [this]
  exact add_mem hk (smul_mem _ _ ha)

/-- **Stacked bases over a valuation ring.** A finitely generated submodule `N` of `V^n` over a
valuation ring `V` is carried by an automorphism of `V^n` onto the diagonal submodule
`∏ i, (x i)`. -/
theorem exists_linearEquiv_map_eq_pi_span_singleton {n : ℕ} (N : Submodule V (Fin n → V))
    (hN : N.FG) : ∃ (E : (Fin n → V) ≃ₗ[V] (Fin n → V)) (x : Fin n → V),
      N.map E.toLinearMap = Submodule.pi Set.univ fun i ↦ Ideal.span {x i} := by
  induction n with
  | zero => exact ⟨.refl V _, 0, by ext y; simp [Subsingleton.elim y 0]⟩
  | succ n ih =>
    classical
    obtain ⟨j₀, k₀, hk₀, hdvd⟩ := exists_pivot hN
    by_cases ha : k₀ j₀ = 0
    · -- Then every coordinate of every element of `N` vanishes, so `N = 0`.
      refine ⟨.refl V _, 0, ?_⟩
      have hN0 : N = ⊥ := eq_bot_iff.2 fun k hk ↦ (mem_bot V).2 <| funext fun j ↦
        zero_dvd_iff.1 (ha ▸ hdvd k hk j)
      rw [hN0, Submodule.map_bot]
      ext y
      simp only [mem_bot, Submodule.mem_pi, Set.mem_univ, true_implies, Pi.zero_apply,
        Ideal.span_singleton_eq_bot.2 rfl]
      exact funext_iff
    obtain ⟨Φ, hΦ, hΦdvd⟩ := exists_linearEquiv_pivot ha hdvd hk₀
    set N₁ := N.map Φ.toLinearMap
    obtain ⟨E₂, y, hE₂⟩ := ih (N₁.map (funLeft V V Fin.succ)) ((hN.map _).map _)
    -- Apply `E₂` to the tail of a vector, keeping its first coordinate.
    let E₃ : (Fin (n + 1) → V) ≃ₗ[V] (Fin (n + 1) → V) :=
      ((Fin.consLinearEquiv V fun _ ↦ V).symm.trans ((LinearEquiv.refl V V).prodCongr E₂)).trans
        (Fin.consLinearEquiv V fun _ ↦ V)
    refine ⟨Φ.trans E₃, Fin.cons (k₀ j₀) y, ?_⟩
    ext z
    rw [LinearEquiv.coe_trans, Submodule.map_comp, mem_map_equiv,
      mem_iff_dvd_and_mem_map_tail hΦ hΦdvd, mem_pi, Fin.forall_fin_succ]
    simp only [Set.mem_univ, true_implies, Fin.cons_zero, Fin.cons_succ, Ideal.mem_span_singleton]
    refine and_congr (by simp [E₃]) ?_
    have hz : funLeft V V Fin.succ (E₃.symm z) = E₂.symm (funLeft V V Fin.succ z) := by
      have ht : Fin.tail z = funLeft V V Fin.succ z := by
        ext i
        rw [funLeft_apply, Fin.tail_def]
      ext i
      simp [E₃, funLeft_apply, ht]
    rw [hz, ← mem_map_equiv, hE₂]
    simp [mem_pi, Ideal.mem_span_singleton, funLeft_apply]

variable {M : Type*} [AddCommGroup M] [Module V M]

/-- **Finitely presented torsion modules over a valuation ring are quadratically presented**: such
a module is the cokernel of a square matrix. -/
theorem IsQuadraticallyPresented.of_isTorsion [Module.FinitePresentation V M]
    (hM : Module.IsTorsion V M) : IsQuadraticallyPresented V M := by
  -- For a surjection `π : V^n → M`, the kernel of `π` is finitely generated and torsion-free,
  -- hence free over the local Bézout domain `V`, of rank `n` since `M` has rank zero.
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' V M
  have : Module.Finite V (ker π) := .of_fg (Module.FinitePresentation.fg_ker π hπ)
  have : Module.Flat V (ker π) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have : Module.Free V (ker π) := Module.free_of_flat_of_isLocalRing
  have hrank : finrank V (ker π) = n := by
    -- The quotient `V^n ⧸ ker π ≃ M` is torsion, so it has rank zero.
    have hQ : Module.IsTorsion V ((Fin n → V) ⧸ ker π) := fun x ↦ by
      obtain ⟨a, ha⟩ := hM (x := π.quotKerEquivOfSurjective hπ x)
      refine ⟨a, (π.quotKerEquivOfSurjective hπ).injective ?_⟩
      rw [Submonoid.smul_def, map_smul, ← Submonoid.smul_def, ha, map_zero]
    have h := rank_quotient_add_rank_of_isDomain (ker π)
    rw [Module.rank_eq_zero_iff_isTorsion.2 hQ, zero_add, rank_fin_fun] at h
    exact finrank_eq_of_rank_eq h
  exact of_exact (Module.finBasisOfFinrankEq V (ker π) hrank) (Pi.basisFun V (Fin n))
    (exact_subtype_ker_map π) hπ

/-- **Finitely presented modules over a valuation ring are products of cyclic modules**
(Warfield). A finitely presented module `M` over a valuation ring `V` is isomorphic to
`∏ i : Fin n, V ⧸ (x i)` for some `x : Fin n → V`. -/
theorem exists_linearEquiv_pi_quotient_span_singleton [Module.FinitePresentation V M] :
    ∃ (n : ℕ) (x : Fin n → V), Nonempty (M ≃ₗ[V] ((i : Fin n) → V ⧸ Ideal.span {x i})) := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' V M
  obtain ⟨E, x, hE⟩ := exists_linearEquiv_map_eq_pi_span_singleton (ker π)
    (Module.FinitePresentation.fg_ker π hπ)
  exact ⟨n, x, ⟨(π.quotKerEquivOfSurjective hπ).symm.trans <|
    (Submodule.Quotient.equiv _ _ E hE).trans (quotientPi _)⟩⟩

/-- A finitely presented torsion module `M` over a valuation ring `V` is isomorphic to
`∏ i : Fin n, V ⧸ (x i)` for some `x : Fin n → V` with all `x i ≠ 0`. -/
theorem exists_linearEquiv_pi_quotient_span_singleton_of_isTorsion [Module.FinitePresentation V M]
    (hM : Module.IsTorsion V M) : ∃ (n : ℕ) (x : Fin n → V), (∀ i, x i ≠ 0) ∧
      Nonempty (M ≃ₗ[V] ((i : Fin n) → V ⧸ Ideal.span {x i})) := by
  classical
  obtain ⟨n, x, ⟨e⟩⟩ := exists_linearEquiv_pi_quotient_span_singleton (V := V) (M := M)
  refine ⟨n, x, fun i hi ↦ ?_, ⟨e⟩⟩
  -- The class of `1` in the factor `V ⧸ (x i) = V ⧸ 0` is not torsion.
  obtain ⟨⟨a, ha⟩, h⟩ :=
    hM (x := e.symm (Pi.single i (Submodule.Quotient.mk (1 : V) : V ⧸ Ideal.span {x i})))
  rw [Submonoid.mk_smul, ← map_smul, LinearEquiv.map_eq_zero_iff] at h
  have h' := congr_fun h i
  rw [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one, hi, Ideal.span_singleton_eq_bot.2 rfl,
    Ideal.mem_bot] at h'
  exact nonZeroDivisors.ne_zero ha h'

end TauCeti
