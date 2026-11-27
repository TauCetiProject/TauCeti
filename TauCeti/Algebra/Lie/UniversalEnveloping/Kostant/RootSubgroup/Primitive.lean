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
import TauCeti.Algebra.Lie.Sl2.Spectrum
import TauCeti.Algebra.Lie.Sl2.WeightString
import TauCeti.Algebra.Module.Primitive.Submodule

/-!
# Primitive images of Kostant root operators in `sl₂` triples

Let `M ≤ V` be a Kostant-stable integral lattice with an integral basis `b`. Whenever two root
generators `e i` and `e opp` act on `V` as the raising and lowering elements of an `sl₂` triple
`(H, ρ(e i), ρ(e opp))` whose Cartan operator `H` acts diagonally on `b` with bounded integral
eigenvalues that are not all zero, the integral root operator
`kostantRootOperator e h ρ M hM i : M →ₗ[ℤ] M` has a primitive vector in its image.

This holds for every Kostant-stable weight lattice with bounded weights without any restriction on
rank, root-string length, or fundamental-weight summands, including weight lattices inside proper
invariant subspaces and adjoint lattices where no primitive image vector lies in a two-step root
string. It provides the lattice-primitivity input for closed-immersion and parameter-faithfulness
theorems on Chevalley root subgroups across all isogeny types.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.exists_isPrimitive_kostantRootOperator_of_isSl2Triple`:
  integral root-operator primitivity for any Kostant-stable weight lattice with bounded integral
  weights carrying an `sl₂` triple that acts nontrivially on the lattice.

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

/-- Every Kostant root operator preserves the rational span of an integral basis `b` of `M`. -/
private theorem root_apply_mem_span_basis
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M) (k : ι) :
    ∀ x ∈ Submodule.span ℚ (Set.range fun r : η => (b r : V)),
      ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k)) x ∈
        Submodule.span ℚ (Set.range fun r : η => (b r : V)) :=
  (Submodule.span_le (p := (Submodule.span ℚ (Set.range fun r : η => (b r : V))).comap
    (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e k))))).mpr <| by
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, ← coe_kostantRootOperator_apply e h ρ M hM k (b r)]
    have hmem : (kostantRootOperator e h ρ M hM k (b r) : V) ∈
        (Submodule.span ℤ (Set.range b)).map M.subtype.toIntLinearMap :=
      ⟨_, b.span_eq.symm ▸ trivial, rfl⟩
    rw [Submodule.map_span, ← Set.range_comp] at hmem
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hmem

/-- Ambient highest-weight round-trip identity for
`exists_pow_kostantRootOperator_eq_factorial_smul`: produces a positive integer weight `N = wt j`
such that `E ^ N (F ^ N (b j)) = (N! * N!) • b j` by restricting the `sl₂` triple to the rational
span of `b`. -/
private theorem exists_pow_e_pow_f_eq_factorial_smul
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V))
    (hwt_ne : ∃ j, wt j ≠ 0)
    (hbdd_below : BddBelow (Set.range wt)) (hbdd_above : BddAbove (Set.range wt)) :
    ∃ (j : η) (N : ℕ), N ≠ 0 ∧
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) ^ N)
        ((ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp)) ^ N) (b j : V)) =
          ((N.factorial : ℚ) * N.factorial) • (b j : V) := by
  let E := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  let F := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))
  let W : Submodule ℚ V := Submodule.span ℚ (Set.range fun r : η => (b r : V))
  have hEW : ∀ x ∈ W, E x ∈ W := root_apply_mem_span_basis e h ρ M hM b i
  have hFW : ∀ x ∈ W, F x ∈ W := root_apply_mem_span_basis e h ρ M hM b opp
  let 𝒲 := hsl2.lieSubmoduleOfStable W hEW hFW
  let hv : ∀ r, (b r : V) ∈ 𝒲 := fun r =>
    (hsl2.mem_lieSubmoduleOfStable W hEW hFW).mpr (Submodule.subset_span ⟨r, rfl⟩)
  let v : η → 𝒲 := fun r => ⟨(b r : V), hv r⟩
  have hspanW : Submodule.span ℚ (Set.range v) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff 𝒲.toSubmodule hv).mpr
      (hsl2.lieSubmoduleOfStable_toSubmodule W hEW hFW).symm
  have hwtW : ∀ r, ⁅(⟨H, hsl2.h_mem_toLieSubalgebra⟩ : hsl2.toLieSubalgebra ℚ), v r⁆ =
      (wt r : ℚ) • v r := fun r =>
    Subtype.ext <| by
      rw [LieSubmodule.coe_bracket, LieSubalgebra.coe_bracket_of_module, SetLike.val_smul]
      exact hwt r
  obtain ⟨r₀, hr₀⟩ := hwt_ne
  have hhW : LieModule.toEnd ℚ (hsl2.toLieSubalgebra ℚ) 𝒲 ⟨H, hsl2.h_mem_toLieSubalgebra⟩ ≠ 0 := by
    intro hzero
    have hval := congrArg (fun g : Module.End ℚ 𝒲 => g (v r₀)) hzero
    rw [LinearMap.zero_apply, LieModule.toEnd_apply_apply, hwtW r₀] at hval
    exact smul_ne_zero (Int.cast_ne_zero.mpr hr₀)
      (fun h0 => b.ne_zero r₀ (Subtype.ext (congrArg (fun x : 𝒲 => (x : V)) h0))) hval
  obtain ⟨j, hjpos, hP, -⟩ :=
    (hsl2.isSl2Triple_restrict (K := ℚ)).exists_pos_weight_and_hasPrimitiveVectorWith_of_span_eq_top
      hspanW hhW hwtW (hbdd_below.mono (Set.range_comp_subset_range Subtype.val wt))
      (hbdd_above.mono (Set.range_comp_subset_range Subtype.val wt))
  let N : ℕ := (wt j).toNat
  have hN_eq : (N : ℤ) = wt j := Int.toNat_of_nonneg hjpos.le
  have hP_nat :
      (hsl2.isSl2Triple_restrict (K := ℚ)).HasPrimitiveVectorWith (v j) (N : ℚ) := by
    rwa [← Int.cast_natCast, hN_eq]
  have hpow := congrArg Subtype.val (TauCeti.pow_toEnd_e_pow_toEnd_f_self_nat hP_nat)
  have htoEnd (T : Module.End ℚ V) (hT : T ∈ hsl2.toLieSubalgebra ℚ) :
      LieModule.toEnd ℚ (hsl2.toLieSubalgebra ℚ) V ⟨T, hT⟩ = T :=
    LinearMap.ext fun x => by
      rw [LieModule.toEnd_apply_apply, LieSubalgebra.coe_bracket_of_module, Module.End.lie_apply]
  rw [LieSubmodule.coe_toEnd_pow, LieSubmodule.coe_toEnd_pow,
    htoEnd E hsl2.e_mem_toLieSubalgebra, htoEnd F hsl2.f_mem_toLieSubalgebra,
    AddSubmonoidClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_mul] at hpow
  exact ⟨j, N, by omega, by simpa [E, F, v] using hpow⟩

/-- Internal helper for `exists_isPrimitive_kostantRootOperator_of_isSl2Triple`: produces a nonzero
power of `kostantRootOperator` hitting `N! • b j` for a positive-weight primitive basis vector
`b j`. Kept private because its return shape is tailored to the prime-adic factorial argument
below. -/
private theorem exists_pow_kostantRootOperator_eq_factorial_smul
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V))
    (hwt_ne : ∃ j, wt j ≠ 0)
    (hbdd_below : BddBelow (Set.range wt)) (hbdd_above : BddAbove (Set.range wt)) :
    ∃ (j : η) (N : ℕ) (m₀ : M),
      N ≠ 0 ∧ (kostantRootOperator e h ρ M hM i ^ N) m₀ = N.factorial • b j := by
  obtain ⟨j, N, hN_ne, hpow⟩ :=
    exists_pow_e_pow_f_eq_factorial_smul e h ρ M hM b hsl2 hwt hwt_ne hbdd_below hbdd_above
  let F := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))
  let m₀ : M := ⟨(dividedPower N F) (b j : V),
    dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM opp N (b j).property⟩
  refine ⟨j, N, m₀, hN_ne, Subtype.ext ?_⟩
  rw [coe_pow_kostantRootOperator, AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul ℚ]
  simp only [m₀, dividedPower_def, LinearMap.smul_apply]
  rw [map_smul, hpow, ← mul_smul, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero N)), one_mul]

/-- If `e i` and `e opp` act on a Kostant-stable lattice `M` with basis `b` as the raising and
lowering elements of an `sl₂` triple `(H, ρ(e i), ρ(e opp))` whose Cartan operator `H` acts
diagonally on `b` with bounded integral eigenvalues that are not all zero, then
`kostantRootOperator e h ρ M hM i` has a primitive vector in its image. -/
theorem exists_isPrimitive_kostantRootOperator_of_isSl2Triple
    {L ι κ V η : Type*} [LieRing L] [LieAlgebra ℚ L] [AddCommGroup V] [Module ℚ V]
    (e : ι → L) (h : κ → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
    (M : AddSubgroup V) (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
    (b : Module.Basis η ℤ M)
    {i opp : ι} {H : Module.End ℚ V}
    (hsl2 : IsSl2Triple H (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
      (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))))
    {wt : η → ℤ} (hwt : ∀ r, H (b r : V) = (wt r : ℚ) • (b r : V))
    (hwt_ne : ∃ j, wt j ≠ 0)
    (hbdd_below : BddBelow (Set.range wt)) (hbdd_above : BddAbove (Set.range wt)) :
    ∃ m : M, IsPrimitive (kostantRootOperator e h ρ M hM i m) := by
  let : Module.Free ℤ M := Module.Free.of_basis b
  obtain ⟨j, N, m₀, hN_ne, hopN⟩ :=
    exists_pow_kostantRootOperator_eq_factorial_smul e h ρ M hM b hsl2 hwt hwt_ne
      hbdd_below hbdd_above
  set op := kostantRootOperator e h ρ M hM i
  refine op.exists_isPrimitive_apply_iff.mpr fun p hp => ?_
  by_contra! hdiv
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
