/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Pi

/-!
# Additive maps on integer lattices are bounded by the coordinates

Let `a : L →+ (ι → ℤ)` be an injective additive map from an abelian group `L` to the integer
vectors indexed by a finite type `ι`, so that `L` is a lattice with integer coordinates `a P i`.
Every additive map `φ : L →+ K` to a linearly ordered field is then bounded by the `ℓ¹`-norm of
the coordinates: `|φ P| ≤ C * ∑ i, |a P i|` for a constant `C` and all `P`
(`AddMonoidHom.exists_abs_le_mul_sum_abs`), with one constant for any finite family of such maps
(`AddMonoidHom.exists_forall_abs_le_mul_sum_abs`). In particular the sum `∑ i, |a P i|`, which is at
least one for `P ≠ 0`, controls every linear functional on `L` uniformly, including on elements
with arbitrarily large coordinates. When the coordinates are given as a family `aᵢ : L →+ ℤ` and
`K` is archimedean, it follows that for large `N` every nonzero `P` has a coordinate `i` at which
`p_i(P) + N aᵢ(P)` or `q_i(P) - N aᵢ(P)` exceeds `c P`, for any additive maps `p_i`, `q_i` and
`c` (`AddMonoidHom.exists_forall_exists_lt_add_mul_or_lt_sub_mul`).

The proof extends `φ` along `a` to an additive map `ψ : (ι → ℤ) →+ K`, which is possible because
`K` is a divisible abelian group and hence an injective `ℤ`-module (Baer's criterion,
`Module.Baer.of_divisible`). Then `φ P = ∑ i, a P i • ψ (eᵢ)` for the standard basis vectors
`eᵢ`, and `C = ∑ i, |ψ (eᵢ)|` works.

This is the estimate used to compare the first Chern class pairing on the periodic domains of a
Heegaard diagram with the multiplicities of their boundaries along the attaching curves, in the
winding argument for admissibility (`TauCeti.LowDimTopology.Heegaard.Winding`).
-/

public section

namespace AddMonoidHom

/-- An additive map `φ` on an abelian group `L` with injective integer coordinates
`a : L →+ (ι → ℤ)` is bounded by the `ℓ¹`-norm of the coordinates: `|φ P| ≤ C * ∑ i, |a P i|`
for some constant `C` and all `P`. -/
theorem exists_abs_le_mul_sum_abs {L ι K : Type*} [AddCommGroup L] [Fintype ι] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (φ : L →+ K) {a : L →+ (ι → ℤ)}
    (ha : Function.Injective a) :
    ∃ C : K, ∀ P, |φ P| ≤ C * ∑ i, |(a P i : K)| := by
  classical
  obtain ⟨ψ, hψ⟩ := (Module.Baer.of_divisible K).extension_property_addMonoidHom a ha φ
  set e : ι → K := fun i => ψ fun j => if i = j then 1 else 0
  refine ⟨∑ i, |e i|, fun P => ?_⟩
  have hφ : φ P = ∑ i, (a P i : K) * e i := by
    have h := LinearMap.pi_apply_eq_sum_univ ψ.toIntLinearMap (a P)
    simp only [coe_toIntLinearMap, zsmul_eq_mul] at h
    rw [← hψ, coe_comp, Function.comp_apply, h]
  rw [hφ, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun j => |e j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    (abs_nonneg _)

/-- A finite family of additive maps `φ k` on an abelian group `L` with injective integer
coordinates `a : L →+ (ι → ℤ)` is bounded by one multiple of the `ℓ¹`-norm of the coordinates:
`|φ k P| ≤ C * ∑ i, |a P i|` for some constant `C ≥ 0` and all `k` and `P`. -/
theorem exists_forall_abs_le_mul_sum_abs {L ι κ K : Type*} [AddCommGroup L] [Fintype ι]
    [Finite κ] [Field K] [LinearOrder K] [IsStrictOrderedRing K] (φ : κ → L →+ K)
    {a : L →+ (ι → ℤ)} (ha : Function.Injective a) :
    ∃ C : K, 0 ≤ C ∧ ∀ k P, |φ k P| ≤ C * ∑ i, |(a P i : K)| := by
  have := Fintype.ofFinite κ
  choose C hC using fun k => (φ k).exists_abs_le_mul_sum_abs ha
  refine ⟨∑ k, |C k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun k P => (hC k P).trans
    (mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => abs_nonneg _))⟩
  exact (le_abs_self _).trans
    (Finset.single_le_sum (f := fun k => |C k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k))

/-- **The winding estimate.** Let the additive coordinates `aᵢ : L →+ ℤ` detect the elements of
`L`. For additive maps `p_i`, `q_i : L →+ ℤ` and a functional `c : L →+ K`, there is `N₀` such
that for every `N ≥ N₀` each nonzero `P` has an index `i` with `c P < p_i(P) + N aᵢ(P)` or
`c P < q_i(P) - N aᵢ(P)`. -/
theorem exists_forall_exists_lt_add_mul_or_lt_sub_mul {L ι K : Type*} [AddCommGroup L]
    [Finite ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K] {a : ι → L →+ ℤ}
    (ha : ∀ P, (∀ i, a i P = 0) → P = 0) (p q : ι → L →+ ℤ) (c : L →+ K) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ P, P ≠ 0 → ∃ i,
      c P < ((p i P + N * a i P : ℤ) : K) ∨ c P < ((q i P - N * a i P : ℤ) : K) := by
  have := Fintype.ofFinite ι
  have hA : Function.Injective (AddMonoidHom.pi a) :=
    (injective_iff_map_eq_zero _).2 fun P hP => ha P fun i => congr_fun hP i
  -- One constant `M` bounds `|p_i(P)|`, `|q_i(P)|` and `|c P|` by `M` times the `ℓ¹`-norm
  -- `∑ i, |aᵢ(P)|` of the coordinates, uniformly in `P`.
  obtain ⟨M, hM₀, hM⟩ := exists_forall_abs_le_mul_sum_abs
    (fun k : Option (ι ⊕ ι) => k.elim c (Sum.elim
      (fun i => (Int.castAddHom K).comp (p i)) (fun i => (Int.castAddHom K).comp (q i)))) hA
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * M * Fintype.card ι)
  refine ⟨N₀, fun N hN P hP => ?_⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i P ≠ 0 := by
    by_contra! h
    exact hP (ha P h)
  -- At a coordinate `i` where `|aᵢ(P)|` is largest, `∑ j, |aⱼ(P)| ≤ card ι * |aᵢ(P)|`.
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => |a i P|) ⟨i₀, by simp⟩
  set S : K := ∑ j, |(a j P : K)|
  have hai : (1 : K) ≤ |(a i P : K)| := by
    exact_mod_cast (Int.one_le_abs hi₀).trans (hi i₀ (Finset.mem_univ _))
  have hS : S ≤ Fintype.card ι * |(a i P : K)| := by
    simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul Finset.univ
      (fun j => |(a j P : K)|) |(a i P : K)| fun j _ => by exact_mod_cast hi j (Finset.mem_univ _)
  -- The winding term `N |aᵢ(P)|` beats `2 M S`, which bounds the other two terms.
  have hdom : 2 * M * S < N * |(a i P : K)| := by
    have hN' : 2 * M * Fintype.card ι < (N : K) := hN₀.trans_le (by exact_mod_cast hN)
    calc 2 * M * S ≤ 2 * M * Fintype.card ι * |(a i P : K)| := by
          rw [mul_assoc _ (Fintype.card ι : K)]; exact mul_le_mul_of_nonneg_left hS (by positivity)
      _ < N * |(a i P : K)| := mul_lt_mul_of_pos_right hN' (zero_lt_one.trans_le hai)
  have hc : c P ≤ M * S := (le_abs_self _).trans (hM none P)
  have hp := neg_le_of_abs_le (hM (some (.inl i)) P)
  have hq := neg_le_of_abs_le (hM (some (.inr i)) P)
  simp only [Option.elim, Sum.elim_inl, Sum.elim_inr, AddMonoidHom.coe_comp,
    Function.comp_apply, Int.coe_castAddHom, AddMonoidHom.pi_apply] at hp hq
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne (show (a i P : K) ≠ 0 from fun h =>
    (zero_lt_one.trans_le hai).ne' (by rw [h, abs_zero])) with hneg | hpos
  · rw [abs_of_neg hneg] at hdom
    right
    push_cast
    linarith
  · rw [abs_of_pos hpos] at hdom
    left
    push_cast
    linarith

end AddMonoidHom
