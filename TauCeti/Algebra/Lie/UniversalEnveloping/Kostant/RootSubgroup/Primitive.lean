/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import TauCeti.Algebra.Module.Primitive.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Algebra.Lie.Sl2.Straightening
import TauCeti.Algebra.Module.Primitive.Submodule
import TauCeti.LinearAlgebra.Eigenspace.Separation

/-!
# Primitive images of Kostant root operators in `sl₂` triples

Let `M ≤ V` be a Kostant-stable integral lattice with a finite integral basis `b` spanning `V` over
`ℚ`. Whenever two root generators `e i` and `e opp` act on `V` as the raising and lowering elements
of an `sl₂` triple `(H, ρ(e i), ρ(e opp))` whose Cartan operator `H` acts diagonally on `b` with
integral eigenvalues, the integral root operator `kostantRootOperator e h ρ M hM i : M →ₗ[ℤ] M` has
a primitive vector in its image.

This holds for every finite-rank Kostant-stable weight lattice without any restriction on
root-string length or fundamental-weight summands, including adjoint lattices where no primitive
image vector lies in a two-step root string. It provides the lattice-primitivity input for
closed-immersion and parameter-faithfulness theorems on Chevalley root subgroups across all isogeny
types.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_isPrimitive_kostantRootOperator_of_isSl2Triple`:
  integral root-operator primitivity for any finite-rank Kostant-stable weight lattice carrying an
  `sl₂` triple.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§7.2 and 27.1.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open Associative

section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

private theorem exists_pos_weight_of_isSl2Triple
    {V η : Type*} [AddCommGroup V] [Module ℚ V] [Finite η]
    {M : AddSubgroup V} (b : Module.Basis η ℤ M)
    (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {H E F : Module.End ℚ V} (hsl2 : IsSl2Triple H E F)
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V)) :
    ∃ r : η, 0 < wt r := by
  cases nonempty_fintype η
  have hhe : H * E - E * H = 2 • E := hsl2.lie_h_e_nsmul
  have hhf : H * F - F * H = -(2 • F) := hsl2.lie_h_f_nsmul
  have hex_ne : ∃ r : η, wt r ≠ 0 := by
    by_contra! hall
    refine hsl2.h_ne_zero (LinearMap.ext_on_range hspan fun r => ?_)
    simp [hwt r, hall r]
  by_contra! hnonpos
  obtain ⟨r₀, hr₀⟩ := hex_ne
  obtain ⟨j₀, -, hj₀min⟩ := Finset.exists_min_image Finset.univ wt ⟨r₀, Finset.mem_univ r₀⟩
  have hj₀neg : wt j₀ < 0 := lt_of_le_of_ne (le_trans (hj₀min r₀ (Finset.mem_univ r₀))
    (hnonpos r₀)) fun h => hr₀ (le_antisymm (hnonpos r₀) (h ▸ hj₀min r₀ (Finset.mem_univ r₀)))
  have hFj₀ : F (b j₀ : V) = 0 := by
    have heig : H (F (b j₀ : V)) = ((wt j₀ - 2 : ℤ) : ℚ) • F (b j₀ : V) := by
      have hcomm := LinearMap.congr_fun (TauCeti.Sl2.h_mul_f_pow hhf 1) (b j₀ : V)
      push_cast
      simpa [pow_one, mul_apply_eq_comp, sub_apply, hwt j₀, sub_smul,
        ← Nat.cast_smul_eq_nsmul ℚ] using hcomm
    refine H.eq_zero_of_apply_eq_smul_of_span_eq_top hspan hwt heig fun r => ?_
    have := hj₀min r (Finset.mem_univ r)
    exact_mod_cast (by omega : wt r ≠ wt j₀ - 2)
  let K : ℕ := (-wt j₀).toNat
  have hK_eq : (K : ℤ) = -wt j₀ := Int.toNat_of_nonneg (by omega)
  have hsym := hsl2.symm
  have hround : (dividedPower K F) ((dividedPower K E) (b j₀ : V)) = (b j₀ : V) :=
    TauCeti.Sl2.dividedPower_e_apply_dividedPower_f_apply_of_eq_zero
      hsym.lie_e_f hsym.lie_h_e_nsmul hsym.lie_h_f_nsmul hFj₀
      (by rw [LinearMap.neg_apply, hwt j₀, ← neg_smul, ← Int.cast_neg, ← hK_eq, Int.cast_natCast])
  have hw_eig :
      H ((dividedPower K E) (b j₀ : V)) = ((K : ℤ) : ℚ) • (dividedPower K E) (b j₀ : V) := by
    have hcomm := LinearMap.congr_fun (TauCeti.Sl2.h_mul_dividedPower_e hhe K) (b j₀ : V)
    have hwtK : (wt j₀ : ℚ) + (K : ℚ) * 2 = ((K : ℤ) : ℚ) := by
      exact_mod_cast (by omega : wt j₀ + (K : ℤ) * 2 = (K : ℤ))
    simpa [mul_apply_eq_comp, hwt j₀, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← add_smul,
      hwtK] using hcomm
  have hw_zero : (dividedPower K E) (b j₀ : V) = 0 :=
    H.eq_zero_of_apply_eq_smul_of_span_eq_top hspan hwt hw_eig fun r => by
      have := hnonpos r
      exact_mod_cast (by omega : wt r ≠ (K : ℤ))
  rw [hw_zero, map_zero] at hround
  exact (b.ne_zero j₀) (Subtype.ext hround.symm)

private theorem exists_pos_weight_and_apply_eq_zero_of_isSl2Triple
    {V η : Type*} [AddCommGroup V] [Module ℚ V] [Finite η]
    {M : AddSubgroup V} (b : Module.Basis η ℤ M)
    (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {H E F : Module.End ℚ V} (hsl2 : IsSl2Triple H E F)
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V)) :
    ∃ j : η, 0 < wt j ∧ E (b j : V) = 0 := by
  cases nonempty_fintype η
  obtain ⟨r₁, hr₁⟩ := exists_pos_weight_of_isSl2Triple b hspan hsl2 hwt
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image Finset.univ wt ⟨r₁, Finset.mem_univ r₁⟩
  refine ⟨j, lt_of_lt_of_le hr₁ (hjmax r₁ (Finset.mem_univ r₁)), ?_⟩
  have heig : H (E (b j : V)) = ((wt j + 2 : ℤ) : ℚ) • E (b j : V) := by
    have hcomm := LinearMap.congr_fun (TauCeti.Sl2.h_mul_e_pow hsl2.lie_h_e_nsmul 1) (b j : V)
    push_cast
    simpa [pow_one, mul_apply_eq_comp, hwt j, add_smul, ← Nat.cast_smul_eq_nsmul ℚ] using hcomm
  refine H.eq_zero_of_apply_eq_smul_of_span_eq_top hspan hwt heig fun r => ?_
  have := hjmax r (Finset.mem_univ r)
  exact_mod_cast (by omega : wt r ≠ wt j + 2)

private theorem exists_pow_kostantRootOperator_eq_factorial_smul
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V] [Finite η]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M) (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V)) :
    ∃ (j : η) (N : ℕ) (m₀ : M),
      N ≠ 0 ∧ (kostantRootOperator e h ρ M hM i ^ N) m₀ = N.factorial • b j := by
  let E := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  let F := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))
  let op := kostantRootOperator e h ρ M hM i
  obtain ⟨j, hjpos, hEj⟩ := exists_pos_weight_and_apply_eq_zero_of_isSl2Triple b hspan hsl2 hwt
  let N : ℕ := (wt j).toNat
  have hN_eq : (N : ℤ) = wt j := Int.toNat_of_nonneg hjpos.le
  let m₀ : M := ⟨(dividedPower N F) (b j : V),
    dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM opp N (b j).2⟩
  have hcoe_pow (k : ℕ) (x : M) : (((op ^ k) x : M) : V) = (E ^ k) (x : V) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
        coe_kostantRootOperator_apply, ih]
  refine ⟨j, N, m₀, by omega, Subtype.ext ?_⟩
  rw [hcoe_pow, AddSubgroupClass.coe_nsmul]
  have hdiv :
      (E ^ N) (m₀ : V) = N.factorial • ((dividedPower N E) ((dividedPower N F) (b j : V))) := by
    rw [dividedPower_def, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_inv_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N))]
  rw [hdiv, TauCeti.Sl2.dividedPower_e_apply_dividedPower_f_apply_of_eq_zero
    hsl2.lie_e_f hsl2.lie_h_e_nsmul hsl2.lie_h_f_nsmul hEj
    (by rw [hwt j, ← hN_eq, Int.cast_natCast])]

/-- If `e i` and `e opp` act on a Kostant-stable lattice `M` with finite spanning basis `b` as the
raising and lowering elements of an `sl₂` triple `(H, ρ(e i), ρ(e opp))` whose Cartan operator `H`
acts diagonally on `b` with integral eigenvalues, then `kostantRootOperator e h ρ M hM i` has a
primitive vector in its image. -/
theorem exists_isPrimitive_kostantRootOperator_of_isSl2Triple
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V] [Finite η]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M) (hspan : Submodule.span ℚ (Set.range fun r => (b r : V)) = ⊤)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V)) :
    ∃ m : M, IsPrimitive (kostantRootOperator e h ρ M hM i m) := by
  let : Module.Free ℤ M := Module.Free.of_basis b
  obtain ⟨j, N, m₀, hN_ne, hopN⟩ :=
    exists_pow_kostantRootOperator_eq_factorial_smul e h ρ M hM b hspan hsl2 hwt
  set op := kostantRootOperator e h ρ M hM i
  refine op.exists_isPrimitive_apply_iff.mpr ⟨?_, fun p hp => ?_⟩
  · intro hop0
    have hzero : N.factorial • b j = 0 := by
      rw [← hopN, hop0, zero_pow hN_ne, LinearMap.zero_apply]
    have hc := congrArg (b.coord j) hzero
    simp [Nat.factorial_ne_zero N] at hc
  · by_contra! hdiv
    have hpow_div (k : ℕ) : ∃ w : M, (p ^ k) • w = (op ^ k) m₀ := by
      induction k with
      | zero => exact ⟨m₀, by simp⟩
      | succ k ih =>
        obtain ⟨w, hw⟩ := ih
        obtain ⟨u, hu⟩ := hdiv w
        exact ⟨u, by
          rw [pow_succ, mul_smul, hu, ← map_nsmul, hw, pow_succ', mul_apply_eq_comp]⟩
    obtain ⟨w, hw⟩ := hpow_div N
    rw [hopN] at hw
    have hc := congrArg (b.coord j) hw
    simp only [map_nsmul, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, nsmul_eq_mul, mul_one] at hc
    have hdvd : p ^ N ∣ N.factorial :=
      Int.natCast_dvd_natCast.mp ⟨b.coord j w, by exact_mod_cast hc.symm⟩
    have : Fact p.Prime := ⟨hp⟩
    exact absurd ((Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero N)).mp hdvd)
      (not_le_of_gt (multiplicity_factorial_lt_of_ne_zero p hN_ne))

end

end TauCeti.UniversalEnvelopingAlgebra
