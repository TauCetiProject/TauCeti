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
import TauCeti.Algebra.Lie.Sl2.Straightening
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
  let E := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))
  let F := ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e opp))
  let op := kostantRootOperator e h ρ M hM i
  let W : Submodule ℚ V := Submodule.span ℚ (Set.range fun r : η => (b r : V))
  have hmem_W (m : M) : (m : V) ∈ W := by
    have hm : m ∈ Submodule.span ℤ (Set.range b) := b.span_eq.symm ▸ trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨r, rfl⟩ := hx
      exact Submodule.subset_span ⟨r, rfl⟩
    | zero => exact W.zero_mem
    | add _ _ _ _ hx hy => exact W.add_mem hx hy
    | smul c _ _ hx =>
      rw [AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
      exact W.smul_mem _ hx
  have hEW : ∀ x ∈ W, E x ∈ W := fun x hx =>
    (Submodule.span_le (p := W.comap E)).mpr (by
      rintro _ ⟨r, rfl⟩
      change E (b r : V) ∈ W
      rw [← coe_kostantRootOperator_apply e h ρ M hM i (b r)]
      exact hmem_W _) hx
  have hFW : ∀ x ∈ W, F x ∈ W := fun x hx =>
    (Submodule.span_le (p := W.comap F)).mpr (by
      rintro _ ⟨r, rfl⟩
      change F (b r : V) ∈ W
      rw [← coe_kostantRootOperator_apply e h ρ M hM opp (b r)]
      exact hmem_W _) hx
  have hHW : ∀ x ∈ W, H x ∈ W := fun x hx =>
    (Submodule.span_le (p := W.comap H)).mpr (by
      rintro _ ⟨r, rfl⟩
      change H (b r : V) ∈ W
      rw [hwt r]
      exact Submodule.smul_mem W _ (Submodule.subset_span ⟨r, rfl⟩)) hx
  let HW : Module.End ℚ W := H.restrict hHW
  let EW : Module.End ℚ W := E.restrict hEW
  let FW : Module.End ℚ W := F.restrict hFW
  have hsl2W : IsSl2Triple HW EW FW :=
    { h_ne_zero := by
        obtain ⟨r₀, hr₀⟩ := hwt_ne
        intro hzero
        have hval := congrArg (fun f : Module.End ℚ W =>
          (f ⟨(b r₀ : V), Submodule.subset_span ⟨r₀, rfl⟩⟩ : V)) hzero
        simp only [HW, LinearMap.restrict_apply, LinearMap.zero_apply,
          ZeroMemClass.coe_zero, hwt r₀] at hval
        have hb0 : (b r₀ : V) ≠ 0 := fun h0 => b.ne_zero r₀ (Subtype.ext h0)
        exact smul_ne_zero (Int.cast_ne_zero.mpr hr₀) hb0 hval
      lie_e_f := by
        ext ⟨x, hx⟩
        simpa only [HW, EW, FW, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
          LinearMap.comp_apply, LinearMap.restrict_apply, Submodule.coe_sub] using
          congrArg (fun f : Module.End ℚ V => f x) hsl2.lie_e_f
      lie_h_e_nsmul := by
        ext ⟨x, hx⟩
        simpa only [HW, EW, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
          LinearMap.comp_apply, two_smul, LinearMap.add_apply, LinearMap.restrict_apply,
          Submodule.coe_sub, Submodule.coe_add] using
          congrArg (fun f : Module.End ℚ V => f x) hsl2.lie_h_e_nsmul
      lie_h_f_nsmul := by
        ext ⟨x, hx⟩
        simpa only [HW, FW, Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
          LinearMap.comp_apply, two_smul, LinearMap.neg_apply, LinearMap.add_apply,
          LinearMap.restrict_apply, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add] using
          congrArg (fun f : Module.End ℚ V => f x) hsl2.lie_h_f_nsmul }
  let v : η → W := fun r => ⟨(b r : V), Submodule.subset_span ⟨r, rfl⟩⟩
  have hspanW : Submodule.span ℚ (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    have hmap : (Submodule.span ℚ (Set.range v)).map W.subtype = W := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have hx' : x ∈ (Submodule.span ℚ (Set.range v)).map W.subtype := hmap.symm ▸ hx
    obtain ⟨⟨y, hyW⟩, hy, hyx⟩ := Submodule.mem_map.mp hx'
    have : (⟨x, hx⟩ : W) = ⟨y, hyW⟩ := Subtype.ext hyx.symm
    rwa [this]
  have hwtW : ∀ r, ⁅HW, v r⁆ = (wt r : ℚ) • v r := fun r =>
    Subtype.ext (by
      change (HW (v r) : V) = ((wt r : ℚ) • v r : W).val
      simpa only [HW, v, LinearMap.restrict_apply, SetLike.val_smul] using hwt r)
  obtain ⟨j, hjpos, hP⟩ :=
    hsl2W.exists_pos_weight_and_hasPrimitiveVectorWith_of_span_eq_top hspanW
      (fun h0 => hsl2W.h_ne_zero (LinearMap.ext fun x => congrArg (· x) h0))
      hwtW (hbdd_below.mono (Set.range_comp_subset_range Subtype.val wt))
      (hbdd_above.mono (Set.range_comp_subset_range Subtype.val wt))
  have hEj : E (b j : V) = 0 := congrArg Subtype.val hP.lie_e
  let N : ℕ := (wt j).toNat
  have hN_eq : (N : ℤ) = wt j := Int.toNat_of_nonneg hjpos.le
  let m₀ : M := ⟨(dividedPower N F) (b j : V),
    dividedPower_apply_mem_of_kostantForm_apply_mem e h ρ hM opp N (b j).property⟩
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
  rw [hdiv, TauCeti.Sl2.dividedPower_e_apply_dividedPower_f_apply_eq_self_of_eq_zero
    hsl2.lie_e_f hsl2.lie_h_f_nsmul hEj
    (by rw [hwt j, ← hN_eq, Int.cast_natCast])]

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
