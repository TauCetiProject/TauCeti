/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
-- Proof-only: equivariant duality and scalar propagation on irreducible modules.
import TauCeti.Algebra.Lie.Dual
import TauCeti.Algebra.Lie.Weights.Central

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
  let e : L ≃ₗ⁅K,L⁆ Module.Dual K L :=
    (killingForm K L).lieModuleEquivDual (killingForm_nondegenerate K L)
      (LieModule.traceForm_lieInvariant K L L)
  let φ : L →ₗ⁅K,L⁆ Module.Dual K L :=
    { toLinearMap := Φ
      map_lie' := fun {z x} ↦ LinearMap.BilinForm.map_lie_of_lieInvariant hΦ z x }
  let f : L →ₗ⁅K,L⁆ L := (e.symm : Module.Dual K L →ₗ⁅K,L⁆ L).comp φ
  have hf_killing (x y : L) : killingForm K L (f x) y = Φ x y :=
    LinearMap.BilinForm.apply_lieModuleEquivDual_symm_apply _ _ _ (φ x) y
  obtain ⟨α⟩ := nonempty_root_of_isSimple (H := H)
  have hdim : Module.finrank K (rootSpace H (α : H → K)) = 1 :=
    finrank_rootSpace_eq_one α.val (H.isNonZero_coe_root α)
  have _ : Nontrivial (rootSpace H (α : H → K)) :=
    Module.nontrivial_of_finrank_pos (R := K) (M := rootSpace H (α : H → K))
      (hdim.symm ▸ Nat.zero_lt_one)
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : rootSpace H (α : H → K))
  have hfv : f v ∈ rootSpace H (α : H → K) := by
    rw [← LieModuleHom.coe_restrictLie (f := f) (L' := H), LieAlgebra.rootSpace]
    exact LieModule.map_genWeightSpace_le (f.restrictLie H) ⟨v, hv, rfl⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hv0 ⟨f v, hfv⟩
  have hfv_eq : f v = c • v := (congrArg Subtype.val hc).symm
  have hall : ∀ x : L, f x = c • x :=
    TauCeti.forall_apply_eq_smul_of_apply_eq_smul K L L f (fun h ↦ hv0 (Subtype.ext h)) hfv_eq
  refine ⟨c, LinearMap.ext₂ fun x y ↦ ?_⟩
  rw [← hf_killing, hall x, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.smul_apply]

end LieSubalgebra
