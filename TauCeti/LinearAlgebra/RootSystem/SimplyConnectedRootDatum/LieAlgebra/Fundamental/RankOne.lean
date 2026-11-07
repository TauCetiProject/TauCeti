/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.HighestWeight
public import TauCeti.LinearAlgebra.Submodule.Primitive

/-!
# The integral rank-one string in a fundamental module

For the fundamental module `L(ϖᵢ)`, write `v = v⁺ᵢ` and `w = fᵢ v`. The two vectors form the
standard two-dimensional string for the numbered `sl₂` triple: `eᵢ w = v`, `fᵢ v = w`, and
`eᵢ v = fᵢ w = 0`. This file proves that their integral span is a direct summand of the
fundamental lattice, not merely a rational subrepresentation.

The integral assertion matters for root subgroups over arbitrary coefficient rings: the
coefficient one in this string survives reduction in every characteristic. The split embedding
`fundamentalRankOneEmbedding` supplies integral coordinate functionals recovering both string
coefficients; these can be used to detect the additive parameter in a root exponential.
No assertion that the complementary summand is stable under the Lie algebra is made.

The normalization input is `smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff`.
Applying `eᵢ` and `eᵢ fᵢ` to a vector in the rational string detects its two coefficients, so
that input proves saturation of the integral string. The direct-summand assertion then uses
the torsion-free quotient criterion for finitely generated modules over `ℤ`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 2, Corollary 1 to Theorem 2,
  and Chapter 3 (integral root subgroup actions).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§7 and 27.
-/

public section

namespace TauCeti.DynkinType

variable (t : DynkinType) (ht : t.Valid)

/-- A rational linear combination of the two vectors in the fundamental rank-one string lies
in the fundamental lattice exactly when both coefficients are integers. -/
theorem smul_add_smul_lie_fundamentalModuleGenerator_mem_fundamentalLattice_iff
    (i : Fin t.rank) (q r : ℚ) :
    q • t.fundamentalModuleGenerator ht i +
        r • ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ ∈
      t.fundamentalLattice ht i ↔
    (∃ a : ℤ, (a : ℚ) = q) ∧ ∃ b : ℤ, (b : ℚ) = r := by
  constructor
  · intro hx
    have he : r • t.fundamentalModuleGenerator ht i ∈ t.fundamentalLattice ht i := by
      simpa using t.lie_rootGenerator_mem_fundamentalLattice ht i (.inl i) hx
    have hf : q • ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ ∈
        t.fundamentalLattice ht i := by
      simpa using t.lie_rootGenerator_mem_fundamentalLattice ht i (.inr i) hx
    have hef : q • t.fundamentalModuleGenerator ht i ∈ t.fundamentalLattice ht i := by
      simpa using t.lie_rootGenerator_mem_fundamentalLattice ht i (.inl i) hf
    exact ⟨(t.smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff ht i q).mp hef,
      (t.smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff ht i r).mp he⟩
  · rintro ⟨⟨a, rfl⟩, b, rfl⟩
    simp only [Int.cast_smul_eq_zsmul]
    exact (t.fundamentalLattice ht i).add_mem
      ((t.fundamentalLattice ht i).smul_mem a
        (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i))
      ((t.fundamentalLattice ht i).smul_mem b
        (t.lie_lieBasis_f_fundamentalModuleGenerator_mem_fundamentalLattice ht i))

/-- The integral standard rank-one string inside the fundamental lattice, with coordinates
`(a, b) ↦ a v⁺ᵢ + b fᵢ v⁺ᵢ`. -/
noncomputable def fundamentalRankOneEmbedding (i : Fin t.rank) :
    (ℤ × ℤ) →ₗ[ℤ] t.fundamentalLattice ht i :=
  (LinearMap.fst ℤ ℤ ℤ).smulRight
      ⟨t.fundamentalModuleGenerator ht i,
        t.fundamentalModuleGenerator_mem_fundamentalLattice ht i⟩ +
    (LinearMap.snd ℤ ℤ ℤ).smulRight
      ⟨⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆,
        t.lie_lieBasis_f_fundamentalModuleGenerator_mem_fundamentalLattice ht i⟩

/-- The value of the rank-one embedding in the rational fundamental module. -/
@[simp]
theorem coe_fundamentalRankOneEmbedding (i : Fin t.rank) (a b : ℤ) :
    (t.fundamentalRankOneEmbedding ht i (a, b) : t.fundamentalModule ht i) =
      a • t.fundamentalModuleGenerator ht i +
        b • ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ :=
  (rfl)

/-- The two integral string coefficients are independent. -/
theorem fundamentalRankOneEmbedding_injective (i : Fin t.rank) :
    Function.Injective (t.fundamentalRankOneEmbedding ht i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, b⟩ hx
  have hval := congrArg (fun x : t.fundamentalLattice ht i => (x : t.fundamentalModule ht i)) hx
  simp only [coe_fundamentalRankOneEmbedding, ZeroMemClass.coe_zero] at hval
  have he : b • t.fundamentalModuleGenerator ht i = 0 := by
    simpa using congrArg (fun x => ⁅(t.lieBasis ht).e i, x⁆) hval
  have hb : b = 0 := (smul_eq_zero.mp he).resolve_right
    (t.fundamentalModuleGenerator_ne_zero ht i)
  subst b
  simp only [zero_smul, add_zero] at hval
  have ha : a = 0 := (smul_eq_zero.mp hval).resolve_right
    (t.fundamentalModuleGenerator_ne_zero ht i)
  simp [ha]

/-- The rank-one string is saturated in the fundamental lattice: divisibility in the ambient
lattice cannot introduce fractional string coefficients. -/
theorem mem_range_fundamentalRankOneEmbedding_of_smul_mem (i : Fin t.rank) (c : ℤ)
    (z : t.fundamentalLattice ht i) (hc : c ≠ 0)
    (hz : c • z ∈ (t.fundamentalRankOneEmbedding ht i).range) :
    z ∈ (t.fundamentalRankOneEmbedding ht i).range := by
  obtain ⟨⟨a, b⟩, hab⟩ := hz
  have hval := congrArg (fun x : t.fundamentalLattice ht i => (x : t.fundamentalModule ht i)) hab
  simp only [coe_fundamentalRankOneEmbedding, SetLike.val_smul] at hval
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hzQ : (z : t.fundamentalModule ht i) =
      ((a : ℚ) / c) • t.fundamentalModuleGenerator ht i +
        ((b : ℚ) / c) • ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ := by
    have hvalQ : (a : ℚ) • t.fundamentalModuleGenerator ht i +
        (b : ℚ) • ⁅(t.lieBasis ht).f i, t.fundamentalModuleGenerator ht i⁆ =
          (c : ℚ) • (z : t.fundamentalModule ht i) := by
      simpa only [Int.cast_smul_eq_zsmul] using hval
    have hscaled := congrArg (fun x : t.fundamentalModule ht i => (c : ℚ)⁻¹ • x) hvalQ.symm
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ hcQ, one_smul, div_eq_inv_mul] using hscaled
  have hzmem := z.property
  rw [hzQ] at hzmem
  have hcoeff := (t.smul_add_smul_lie_fundamentalModuleGenerator_mem_fundamentalLattice_iff ht i
    ((a : ℚ) / c) ((b : ℚ) / c)).mp hzmem
  rcases hcoeff with ⟨⟨u, hu⟩, v, hv⟩
  refine ⟨(u, v), Subtype.ext ?_⟩
  rw [coe_fundamentalRankOneEmbedding, hzQ, ← hu, ← hv]
  simp only [Int.cast_smul_eq_zsmul]

/-- The two-dimensional integral string admits a complementary submodule in the fundamental
lattice. The complement is not asserted to be stable under the Lie algebra. -/
theorem exists_isCompl_range_fundamentalRankOneEmbedding (i : Fin t.rank) :
    ∃ N : Submodule ℤ (t.fundamentalLattice ht i),
      IsCompl (t.fundamentalRankOneEmbedding ht i).range N := by
  exact (Submodule.exists_isCompl_iff_isTorsionFree_quotient _).mpr
    ((t.fundamentalRankOneEmbedding ht i).range.isTorsionFree_quotient_of_smul_mem
      (t.mem_range_fundamentalRankOneEmbedding_of_smul_mem ht i))

/-- Integral coordinate functionals recover both coefficients of the standard rank-one string.
In particular the embedding stays injective after extension to every coefficient ring. -/
theorem exists_leftInverse_fundamentalRankOneEmbedding (i : Fin t.rank) :
    ∃ p : t.fundamentalLattice ht i →ₗ[ℤ] ℤ × ℤ,
      Function.LeftInverse p (t.fundamentalRankOneEmbedding ht i) := by
  have hcompl := t.exists_isCompl_range_fundamentalRankOneEmbedding ht i
  rcases hcompl with ⟨N, hN⟩
  refine ⟨LinearMap.linearProjOfIsCompl N (t.fundamentalRankOneEmbedding ht i)
      (t.fundamentalRankOneEmbedding_injective ht i) hN, ?_⟩
  intro x
  exact LinearMap.linearProjOfIsCompl_apply_left N (t.fundamentalRankOneEmbedding ht i)
    (t.fundamentalRankOneEmbedding_injective ht i) hN x

end TauCeti.DynkinType
