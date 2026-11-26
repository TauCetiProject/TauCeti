/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.LinearAlgebra.Semilinear.Algebraic
public import TauCeti.RingTheory.WittVector.Truncated.Basic

/-!
# Algebraic Frobenius modules over truncated Witt vectors

Over the length-`n` Witt vectors of a ring of characteristic `p`, an algebraic Frobenius
module has a bijective Witt-semilinear Frobenius and every element satisfies a monic
relation in its iterates. Algebraicity of a bijective Frobenius can be checked on the
successive quotients `p^i M / p^{i+1} M` for `i < n`. Each quotient has bijective Frobenius,
and multiplication by `p^i` gives a Frobenius-equivariant surjection onto it from `M / pM`,
so the first quotient suffices. Alternatively, the monic relation condition can be checked
on the submodule `M[p]` killed by `p`.

The quotients here use the ordinary submodules of scalar multiples. The arguments apply
when the underlying module has `p`-torsion.

## References

* B. Bhatt and J. Lurie, *A Riemann–Hilbert correspondence in positive characteristic*,
  Proposition 9.5.1 and Definition 9.5.2.
-/

public section

open Function Set TauCeti
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
  F.subquotientMap (P i) (P (i + 1)) (F.mapsTo_smul_top_of_fixed (by simp))
    (F.mapsTo_smul_top_of_fixed (by simp))

/-- The induced Witt Frobenius sends the class of a vector to the class of its Frobenius. -/
@[simp]
theorem wittFrobeniusGraded_mk (F : M →ₛₗ[φ] M) (i : ℕ) (x : P i) :
    F.wittFrobeniusGraded i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨F x, F.mapsTo_smul_top_of_fixed (by simp) x.property⟩ := by
  unfold wittFrobeniusGraded
  exact subquotientMap_mk (P i) (P (i + 1)) _ _ x

variable {F : M →ₛₗ[TruncatedWittVector.map (p := p) n (_root_.frobenius R p)] M}

/-- A bijective Witt Frobenius induces a bijective Frobenius on each successive quotient. -/
theorem bijective_wittFrobeniusGraded (hF : Bijective F) (i : ℕ) :
    Bijective (F.wittFrobeniusGraded i) := by
  rw [wittFrobeniusGraded]
  apply bijective_subquotientMap _ _ _ _ (F.surjOn_smul_top_of_fixed hF.2 (by simp))
  intro x _ hx
  obtain ⟨y, hy, hyF⟩ := F.surjOn_smul_top_of_fixed hF.2 (a := (p : W) ^ (i + 1)) (by simp) hx
  exact hF.1 hyF ▸ hy

/-- Each successive quotient of an algebraic Witt Frobenius module is algebraic. -/
theorem IsAlgebraicWittFrobenius.wittFrobeniusGraded
    (hF : F.IsAlgebraicWittFrobenius) (i : ℕ) :
    (F.wittFrobeniusGraded i).IsAlgebraicWittFrobenius :=
  ⟨bijective_wittFrobeniusGraded hF.1 i, hF.2.subquotientMap _ _ _ _⟩

/-- A Witt-semilinear Frobenius satisfies monic relations precisely when the induced maps on
the successive quotients of the `p`-power filtration do. -/
theorem isAlgebraic_iff_wittFrobeniusGraded :
    F.IsAlgebraic ↔ ∀ i < n, (F.wittFrobeniusGraded i).IsAlgebraic := by
  constructor
  · intro h i _
    exact h.subquotientMap _ _ _ _
  · intro h
    have hnil : (p : W) ^ n = 0 := by
      rw [← Nat.cast_pow]
      exact CharP.cast_eq_zero W (p ^ n)
    have hbot : P n = ⊥ := by
      simp only [hnil, zero_smul, Submodule.zero_eq_bot]
    have hdesc : Antitone (P : ℕ → Submodule W M) := fun _ _ hij ↦ by
      simpa only [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] using
        Submodule.pow_smul_top_le (Ideal.span {(p : W)}) M hij
    have h₀ := isAlgebraic_restrict_of_filtration P (fun _ ↦ F.mapsTo_smul_top_of_fixed (by simp))
      hdesc hbot h
    refine h₀.of_surjective (P 0).subtype (fun _ ↦ rfl) fun x ↦ ⟨⟨x, ?_⟩, rfl⟩
    simp

/-- For a bijective Witt Frobenius, Bhatt–Lurie algebraicity is equivalent to algebraicity
of the successive `p`-power subquotients. -/
theorem isAlgebraicWittFrobenius_iff_wittFrobeniusGraded (hF : Bijective F) :
    F.IsAlgebraicWittFrobenius ↔ ∀ i < n, (F.wittFrobeniusGraded i).IsAlgebraicWittFrobenius :=
  ⟨fun h i _ ↦ h.wittFrobeniusGraded i,
    fun h ↦ ⟨hF, isAlgebraic_iff_wittFrobeniusGraded.mpr fun i hi ↦ (h i hi).2⟩⟩

/-- Witt Frobenius descends to the reduction `M / pM`. -/
noncomputable def wittFrobeniusModP (F : M →ₛₗ[φ] M) :
    (M ⧸ ((p : W) • (⊤ : Submodule W M))) →ₛₗ[φ] (M ⧸ ((p : W) • (⊤ : Submodule W M))) :=
  ((p : W) • (⊤ : Submodule W M)).mapQ _ F fun _ hx ↦
    F.mapsTo_smul_top_of_fixed (by simp) hx

@[simp]
theorem wittFrobeniusModP_mk (F : M →ₛₗ[φ] M) (x : M) :
    F.wittFrobeniusModP (Submodule.Quotient.mk x) = Submodule.Quotient.mk (F x) :=
  (rfl)

private theorem smulPowQuotientMap_semiconj (F : M →ₛₗ[φ] M) (i : ℕ) :
    Semiconj (smulPowQuotientMap (p : W) i) F.wittFrobeniusModP (F.wittFrobeniusGraded i) := by
  intro z
  obtain ⟨x, rfl⟩ := ((p : W) • (⊤ : Submodule W M)).mkQ_surjective z
  simp only [Submodule.mkQ_apply, wittFrobeniusModP_mk, smulPowQuotientMap_mk,
    wittFrobeniusGraded_mk]
  congr 1
  exact Subtype.ext (by simp [map_smulₛₗ])

/-- The monic relation condition over truncated Witt vectors is equivalent to that for the
induced Frobenius on `M / pM`. -/
theorem isAlgebraic_iff_wittFrobeniusModP :
    F.IsAlgebraic ↔ F.wittFrobeniusModP.IsAlgebraic := by
  let Q : Submodule W M := (p : W) • ⊤
  refine ⟨fun h ↦ h.of_surjective Q.mkQ (fun x ↦ (wittFrobeniusModP_mk F x).symm)
    Q.mkQ_surjective, ?_⟩
  intro h
  exact isAlgebraic_iff_wittFrobeniusGraded.mpr fun i _ ↦
    h.of_surjective (smulPowQuotientMap (p : W) i) (smulPowQuotientMap_semiconj F i)
      (smulPowQuotientMap_surjective (p : W) i)

/-- The restriction of Witt Frobenius to the submodule `M[p]` annihilated by `p`. -/
noncomputable def wittFrobeniusPTorsion (F : M →ₛₗ[φ] M) :=
  F.restrict (F.mapsTo_ker_smul_of_fixed (a := (p : W)) (map_natCast φ p))

@[simp]
theorem coe_wittFrobeniusPTorsion_apply (F : M →ₛₗ[φ] M)
    (x : ker (DistribSMul.toLinearMap W M (p : W))) :
    ↑(F.wittFrobeniusPTorsion x) = F x :=
  (rfl)

/-- The monic relation condition over truncated Witt vectors is equivalent to that for the
restricted Frobenius on the submodule killed by `p`. -/
theorem isAlgebraic_iff_wittFrobeniusPTorsion :
    F.IsAlgebraic ↔ F.wittFrobeniusPTorsion.IsAlgebraic := by
  refine isAlgebraic_iff_restrict_ker_smul_of_isNilpotent F (map_natCast φ p) ⟨n, ?_⟩
  rw [← Nat.cast_pow]
  exact CharP.cast_eq_zero W (p ^ n)

end LinearMap
