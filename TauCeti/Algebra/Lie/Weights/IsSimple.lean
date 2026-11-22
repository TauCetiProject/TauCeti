/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple

/-!
# Split simple Lie algebras: existence of a root and uniqueness of invariant forms

Let `L` be a finite-dimensional simple Lie algebra over a field `K` of characteristic zero, with a
splitting Cartan subalgebra `H`. The root system `LieAlgebra.IsKilling.rootSystem H` is irreducible,
so its weight space `H^*` is nontrivial; since the roots span `H^*`, there is at least one root.

Because each root space is one-dimensional over `K`, every `L`-equivariant endomorphism of `L`
acts as a scalar on a root space, and hence on all of `L` by simplicity. Applying this to the
endomorphism representing an invariant bilinear form against the nondegenerate Killing form shows
that every invariant bilinear form on `L` is a scalar multiple of the Killing form, without
requiring `K` to be algebraically closed.

## Main results

* `TauCeti.LieAlgebra.IsKilling.nonempty_root_of_isSimple`: the type `H.root` of roots is
  nonempty.
* `LieSubalgebra.exists_eq_smul_killingForm_of_isSimple`: **every invariant bilinear form on a split
  finite-dimensional simple Lie algebra over a field of characteristic zero is a scalar multiple of
  the Killing form.**
-/

public section

open LieAlgebra LieAlgebra.IsKilling LieModule

namespace TauCeti.LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- **A simple Lie algebra has a root** with respect to every splitting Cartan subalgebra: its root
system is irreducible, so its weight space `H^*` is nontrivial and spanned by the roots. -/
instance nonempty_root_of_isSimple {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
    [IsTriangularizable K H L] [IsSimple K L] : Nonempty H.root := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := RootPairing.IsIrreducible.nontrivial (P := rootSystem H)
  have hspan := RootPairing.IsRootSystem.span_root_eq_top (P := rootSystem H)
  rw [Set.range_eq_empty, Submodule.span_empty] at hspan
  exact bot_ne_top hspan

end TauCeti.LieAlgebra.IsKilling

namespace LieSubalgebra

open TauCeti.LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

/-- **Every invariant bilinear form on a split finite-dimensional simple Lie algebra is a multiple
of the Killing form**, over any field `K` of characteristic zero (without assuming `K` is
algebraically closed). -/
theorem exists_eq_smul_killingForm_of_isSimple (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
    [IsTriangularizable K H L] [IsSimple K L]
    {Φ : LinearMap.BilinForm K L} (hΦ : Φ.lieInvariant L) :
    ∃ c : K, Φ = c • killingForm K L := by
  let e : L ≃ₗ[K] Module.Dual K L :=
    (killingForm K L).toDual (killingForm_nondegenerate K L)
  let T : L →ₗ[K] L := e.symm.toLinearMap ∘ₗ Φ
  have hT (x y : L) : killingForm K L (T x) y = Φ x y := by
    simp [T, e]
  have hT_lie (z x : L) : T ⁅z, x⁆ = ⁅z, T x⁆ := by
    refine sub_eq_zero.mp <| (killingForm_nondegenerate K L).1 _ fun y ↦ ?_
    rw [map_sub, LinearMap.sub_apply, hT, hΦ z x y,
      LieModule.traceForm_lieInvariant K L L z (T x) y, hT, sub_self]
  let f : L →ₗ⁅K,L⁆ L := { T with map_lie' := fun {z x} ↦ hT_lie z x }
  have hf_apply (x : L) : f x = T x := rfl
  obtain ⟨α⟩ := nonempty_root_of_isSimple (H := H)
  have hα : α.val.IsNonZero := H.isNonZero_coe_root α
  have hdim : Module.finrank K (rootSpace H (α : H → K)) = 1 :=
    finrank_rootSpace_eq_one α.val hα
  have _ : Nontrivial (rootSpace H (α : H → K)) :=
    Module.nontrivial_of_finrank_pos (R := K) (M := rootSpace H (α : H → K))
      (hdim.symm ▸ Nat.zero_lt_one)
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : rootSpace H (α : H → K))
  have hv0' : v ≠ 0 := fun h ↦ hv0 (Subtype.ext h)
  have hTv : T v ∈ rootSpace H (α : H → K) := by
    rw [← hf_apply, ← LieModuleHom.coe_restrictLie (f := f) (L' := H), LieAlgebra.rootSpace]
    exact LieModule.map_genWeightSpace_le (f.restrictLie H) ⟨v, hv, rfl⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hv0 ⟨T v, hTv⟩
  have hTv_eq : T v = c • v := (congrArg Subtype.val hc).symm
  let g : L →ₗ⁅K,L⁆ L := f - c • LieModuleHom.id
  have hg_apply (x : L) : g x = T x - c • x := rfl
  have hker_ne : g.ker ≠ ⊥ := by
    intro hbot
    have hvker : v ∈ g.ker := by
      rw [LieModuleHom.mem_ker, hg_apply, hTv_eq, sub_self]
    rw [hbot, LieSubmodule.mem_bot] at hvker
    exact hv0' hvker
  have hker_top : g.ker = ⊤ := (IsSimple.eq_bot_or_eq_top g.ker).resolve_left hker_ne
  refine ⟨c, LinearMap.ext₂ fun x y ↦ ?_⟩
  have hx : x ∈ g.ker := hker_top.symm ▸ trivial
  rw [LieModuleHom.mem_ker, hg_apply, sub_eq_zero] at hx
  rw [← hT, hx, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply]

end LieSubalgebra
