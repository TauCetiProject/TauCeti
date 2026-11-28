/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Semilinear.Algebraic
public import TauCeti.RingTheory.WittVector.Truncated.Basic

/-!
# Algebraic Frobenius modules over truncated Witt vectors

Over the length-`n` Witt vectors of a ring of characteristic `p`, an algebraic Frobenius
module has a bijective Witt-semilinear Frobenius and every element satisfies a monic
relation in its iterates. Both conditions can be checked on the successive quotients
`p^i M / p^{i+1} M` for `i < n`. Multiplication by `p^i` gives a Frobenius-equivariant
surjection from `M / pM` onto each quotient, so the first quotient suffices for the monic
relation condition. That condition can also be checked on the submodule `M[p]` killed by `p`.

The quotients here use the ordinary submodules of scalar multiples. The arguments apply
when the underlying module has `p`-torsion.

## References

* B. Bhatt and J. Lurie, *A Riemann–Hilbert correspondence in positive characteristic*,
  Proposition 9.5.1 and Definition 9.5.2.
-/

public section

open Function
open scoped Pointwise

namespace LinearMap

variable {p n : ℕ} [Fact p.Prime] {R M : Type*} [CommRing R] [CharP R p] [AddCommGroup M]

variable [Module (TruncatedWittVector p n R) M]

local notation "W" => TruncatedWittVector p n R
local notation "φ" => TruncatedWittVector.map (p := p) n (_root_.frobenius R p)

local notation "P" => (fun i : ℕ ↦ (p : W) ^ i • (⊤ : Submodule W M))

/-- Bhatt–Lurie algebraicity for a module over truncated Witt vectors. The Frobenius must be
bijective on the underlying additive group and every vector must satisfy a monic relation. -/
def IsAlgebraicWittFrobenius (F : M →ₛₗ[φ] M) : Prop :=
  Bijective F ∧ F.IsAlgebraic

/-- The bijectivity and monic relation conditions for an algebraic Witt Frobenius. -/
theorem isAlgebraicWittFrobenius_iff (F : M →ₛₗ[φ] M) :
    F.IsAlgebraicWittFrobenius ↔ Bijective F ∧ F.IsAlgebraic := Iff.rfl

/-- The Witt Frobenius induced on the ordinary quotient `p^i M / p^{i+1} M`. -/
noncomputable def wittFrobeniusGraded (F : M →ₛₗ[φ] M) (i : ℕ) :
    (P i ⧸ (P (i + 1)).comap (P i).subtype) →ₛₗ[φ] (P i ⧸ (P (i + 1)).comap (P i).subtype) :=
  F.smulPowGraded (map_natCast φ p) i

/-- The induced Witt Frobenius sends the class of a vector to the class of its Frobenius. -/
@[simp]
theorem wittFrobeniusGraded_mk (F : M →ₛₗ[φ] M) (i : ℕ) (x : P i) :
    F.wittFrobeniusGraded i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨F x, F.mapsTo_smul_top_of_fixed (by simp) x.property⟩ :=
  smulPowGraded_mk F (map_natCast φ p) i x

variable {F : M →ₛₗ[TruncatedWittVector.map (p := p) n (_root_.frobenius R p)] M}

private theorem p_pow_eq_zero : (p : W) ^ n = 0 := by
  rw [← Nat.cast_pow]
  exact CharP.cast_eq_zero W (p ^ n)

private theorem p_pow_smul_top_eq_bot : P n = ⊥ := by
  simp only [p_pow_eq_zero, zero_smul, Submodule.zero_eq_bot]

/-- A bijective Witt Frobenius induces a bijective Frobenius on each successive quotient. -/
theorem bijective_wittFrobeniusGraded (hF : Bijective F) (i : ℕ) :
    Bijective (F.wittFrobeniusGraded i) :=
  bijective_smulPowGraded hF (map_natCast φ p) i

/-- Each successive quotient of an algebraic Witt Frobenius module is algebraic. -/
theorem IsAlgebraicWittFrobenius.wittFrobeniusGraded
    (hF : F.IsAlgebraicWittFrobenius) (i : ℕ) :
    (F.wittFrobeniusGraded i).IsAlgebraicWittFrobenius :=
  ⟨bijective_wittFrobeniusGraded hF.1 i, hF.2.smulPowGraded (map_natCast φ p) i⟩

/-- A Witt-semilinear Frobenius satisfies monic relations precisely when the induced maps on
the successive quotients of the `p`-power filtration do. -/
theorem isAlgebraic_iff_wittFrobeniusGraded :
    F.IsAlgebraic ↔ ∀ i < n, (F.wittFrobeniusGraded i).IsAlgebraic :=
  F.isAlgebraic_iff_smulPowGraded (map_natCast φ p) p_pow_smul_top_eq_bot

/-- Bhatt–Lurie algebraicity is equivalent to algebraic Witt Frobenius on all successive
`p`-power subquotients. -/
theorem isAlgebraicWittFrobenius_iff_wittFrobeniusGraded :
    F.IsAlgebraicWittFrobenius ↔ ∀ i < n, (F.wittFrobeniusGraded i).IsAlgebraicWittFrobenius :=
  ⟨fun h i _ ↦ h.wittFrobeniusGraded i,
    fun h ↦ ⟨bijective_of_smulPowGraded (map_natCast φ p) p_pow_smul_top_eq_bot
      (fun i hi ↦ (h i hi).1), isAlgebraic_iff_wittFrobeniusGraded.mpr fun i hi ↦ (h i hi).2⟩⟩

/-- Witt Frobenius descends to the reduction `M / pM`. -/
noncomputable def wittFrobeniusModP (F : M →ₛₗ[φ] M) :
    (M ⧸ ((p : W) • (⊤ : Submodule W M))) →ₛₗ[φ] (M ⧸ ((p : W) • (⊤ : Submodule W M))) :=
  Submodule.mapQ ((p : W) • (⊤ : Submodule W M)) ((p : W) • ⊤) F
    (F.mapsTo_smul_top_of_fixed (map_natCast φ p))

@[simp]
theorem wittFrobeniusModP_mk (F : M →ₛₗ[φ] M) (x : M) :
    F.wittFrobeniusModP (Submodule.Quotient.mk x) = Submodule.Quotient.mk (F x) := by
  rw [wittFrobeniusModP]
  exact Submodule.mapQ_apply _ _ F x

/-- The monic relation condition over truncated Witt vectors is equivalent to that for the
induced Frobenius on `M / pM`. -/
theorem isAlgebraic_iff_wittFrobeniusModP :
    F.IsAlgebraic ↔ F.wittFrobeniusModP.IsAlgebraic :=
  F.isAlgebraic_iff_mapQ_smul_top (map_natCast φ p) p_pow_smul_top_eq_bot

/-- The restriction of Witt Frobenius to the submodule `M[p]` annihilated by `p`. -/
noncomputable def wittFrobeniusPTorsion (F : M →ₛₗ[φ] M) :=
  F.restrict (F.mapsTo_torsionBy_of_fixed (a := (p : W)) (map_natCast φ p))

@[simp]
theorem coe_wittFrobeniusPTorsion_apply (F : M →ₛₗ[φ] M)
    (x : Submodule.torsionBy W M (p : W)) :
    ↑(F.wittFrobeniusPTorsion x) = F x := by
  rw [wittFrobeniusPTorsion]
  exact coe_restrict_apply (F.mapsTo_torsionBy_of_fixed (map_natCast φ p)) x

/-- The monic relation condition over truncated Witt vectors is equivalent to that for the
restricted Frobenius on the submodule killed by `p`. -/
theorem isAlgebraic_iff_wittFrobeniusPTorsion :
    F.IsAlgebraic ↔ F.wittFrobeniusPTorsion.IsAlgebraic := by
  exact F.isAlgebraic_iff_restrict_torsionBy (map_natCast φ p)
    (fun x ↦ ⟨n, by rw [p_pow_eq_zero, zero_smul]⟩)

end LinearMap
