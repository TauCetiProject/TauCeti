/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MonoidAlgebra.CharGroupRing.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Regular.Pi

/-!
# Character group rings as lattices

For a finite commutative group `G` and a domain `O`, the character group ring `R_Ψ` contains
`#G • (Ψ → O)`. The integral character sums give this containment without dividing by `#G`
or assuming that `O` contains every root of unity. Consequently, if `#G` is nonzero in `O`,
the rank of `R_Ψ` is `#Ψ`. Over a principal ideal domain it is a finite free module.

The additive quotient of the product by `R_Ψ` is finite when `O/(#G)` is finite. This sufficient
coefficient hypothesis is not necessary for every `Ψ`, but cannot be omitted in general:
a principal ideal domain can have infinite residue fields.

## References

* S. Dasgupta, M. Kakde, *On the Brumer–Stark conjecture*, Ann. of Math. 197 (2023), §2.2.
-/

public section

namespace Set.charGroupRing

variable {O G : Type*} [CommRing O] [IsDomain O] [CommGroup G] [Finite G]
variable (Ψ : Set (G →* Oˣ))

/-- Every function on `Ψ`, multiplied by the group order, lies in the character group ring.
Thus `R_Ψ` is a full lattice when the group order is nonzero in `O`. -/
theorem card_smul_mem (y : Ψ → O) :
    (Nat.card G : O) • y ∈ charGroupRing Ψ := by
  classical
  let := Fintype.ofFinite G
  let := Fintype.ofFinite Ψ
  refine mem_iff.mpr ⟨∑ χ : Ψ, y χ •
    TauCeti.subgroupCharSum ((Units.coeHom O).comp χ.1⁻¹) ⊤, ?_⟩
  intro ψ
  simp [map_sum, MonoidHom.charEval_subgroupCharSum_inv_top, Subtype.coe_inj, mul_comm]

/-- A character group ring has rank equal to the number of its characters when the group
order is nonzero in the coefficient domain. No roots-of-unity hypothesis is needed. -/
theorem finrank (hG : (Nat.card G : O) ≠ 0) :
    Module.finrank O (charGroupRing Ψ) = Nat.card Ψ := by
  classical
  let := Fintype.ofFinite Ψ
  have hregular : IsSMulRegular (Ψ → O) (Nat.card G : O) :=
    (isRegular_iff_ne_zero.mpr hG).isSMulRegular
  -- The subalgebra and its underlying submodule have the same subtype and module instances.
  let : Module.Finite O (charGroupRing Ψ).toSubmodule :=
    inferInstanceAs (Module.Finite O (charGroupRing Ψ))
  have hlower := LinearMap.finrank_le_of_isSMulRegular
    (⊤ : Submodule O (Ψ → O)) (charGroupRing Ψ).toSubmodule hregular
    (fun y _ ↦ card_smul_mem Ψ y)
  have hupper := LinearMap.finrank_le_finrank_of_injective
    (f := (charGroupRing Ψ).toSubmodule.subtype) Subtype.val_injective
  rw [finrank_top] at hlower
  simpa [Module.finrank_pi, Nat.card_eq_fintype_card]
    using le_antisymm hupper hlower

/-- The product modulo the character group ring is finite whenever the coefficient ring
modulo the group order is finite. -/
theorem finite_quotient [Finite (O ⧸ Ideal.span {(Nat.card G : O)})] :
    Finite ((Ψ → O) ⧸ (charGroupRing Ψ).toSubmodule) := by
  let I : Ideal O := Ideal.span {(Nat.card G : O)}
  let N : Submodule O (Ψ → O) := ⊤
  have hle : I • N ≤ (charGroupRing Ψ).toSubmodule := by
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y _ N).mp hy
    exact card_smul_mem Ψ z
  let : Finite ((Ψ → O) ⧸ I • N) := Submodule.finite_quotient_smul I
    (Module.Finite.fg_top (R := O) (M := Ψ → O))
  exact Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/-- When the group order is nonzero in the coefficient domain, the non-zero-divisors of the
character group ring are exactly the elements whose character coordinates are all nonzero. -/
theorem mem_nonZeroDivisors_iff (hG : (Nat.card G : O) ≠ 0) (x : charGroupRing Ψ) :
    x ∈ nonZeroDivisors (charGroupRing Ψ) ↔ ∀ ψ : Ψ, (x : Ψ → O) ψ ≠ 0 := by
  classical
  constructor
  · intro hx ψ hψ
    let y : charGroupRing Ψ :=
      ⟨(Nat.card G : O) • Pi.single ψ 1, card_smul_mem Ψ _⟩
    have hxy : x * y = 0 := by
      apply ext
      intro χ
      by_cases h : χ = ψ
      · subst χ
        simp [y, hψ]
      · simp [y, Pi.single_eq_of_ne h]
    have hy := (_root_.mem_nonZeroDivisors_iff_left.mp hx) y hxy
    have hcoord := congrArg (fun z : charGroupRing Ψ ↦ (z : Ψ → O) ψ) hy
    exact hG (by simpa [y] using hcoord)
  · intro hx
    apply mem_nonZeroDivisors_of_injective
      (f := (charGroupRing Ψ).val) Subtype.val_injective
    exact (Pi.isRegular_iff.mpr fun ψ ↦ isRegular_iff_ne_zero.mpr (hx ψ)).mem_nonZeroDivisors

end Set.charGroupRing
