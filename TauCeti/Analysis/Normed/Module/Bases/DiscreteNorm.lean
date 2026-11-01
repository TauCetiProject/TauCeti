/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.ResidueBasis
public import TauCeti.Analysis.Normed.Module.Bases.PotentiallyONable

/-!
# Banach modules over discretely normed rings

Let `R` be a complete ultrametric norm-one commutative ring with field residue ring and a
multiplicative pseudo-uniformiser `ϖ` whose norm generates the nonzero scalar norms. Every
complete ultrametric normed `R`-module with contractive scalar action is potentially
orthonormalisable, without a countable-type hypothesis. It is isometrically orthonormalisable
precisely when its norms also lie in `‖ϖ‖ ^ ℤ ∪ {0}`. In particular, both statements apply to
complete discretely normed fields.

The isometric statement is Serre's residue-basis criterion: over the field residue ring every
residue module is free. For potential orthonormalisability, round the module norm upwards to
this discrete value group. The rounded structure retains the original uniformity and topology,
hence also completeness and continuous linear equivalences. No rounding of the scalar norm is
performed.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §1.
-/

public section

namespace TauCeti

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [(unitBallIdeal R).IsMaximal]
  {M : Type*} [NormedAddCommGroup M] [Module R M] [IsBoundedSMul R M]
  [IsUltrametricDist M] [CompleteSpace M]

/-- Over a complete discretely normed ultrametric norm-one commutative ring with field residue
ring, a Banach module is isometrically orthonormalisable exactly when its norms lie in the
scalar value group (or are zero). The fixed-point condition for `zpowCeil` expresses membership
in `‖ϖ‖ ^ ℤ ∪ {0}`. -/
theorem isONable_iff_discrete_norm (ϖ : NormedRing.PseudoUniformizer R)
    (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖) :
    IsONable R M ↔ ∀ m : M, zpowCeil ‖(ϖ.unit : R)‖ ‖m‖ = ‖m‖ := by
  constructor
  · intro h m
    obtain ⟨I, _, _, ⟨e⟩⟩ := (isONable_def R M).1 h
    cases isEmpty_or_nonempty I
    · have he : e m = 0 := by ext i; exact isEmptyElim i
      have hm : ‖m‖ = 0 := by rw [← e.norm_map m, he, norm_zero]
      simp [hm]
    · obtain ⟨i, hi⟩ := (e m).exists_norm_coe_eq_norm
      rw [← e.norm_map m, ← hi]
      exact hR _
  · intro hM
    let := Ideal.Quotient.field (unitBallIdeal R)
    exact (isONable_iff_free_residueModule ϖ hR hM).2 inferInstance

/-- **Serre's potential orthonormalisation theorem.** Every Banach module over a complete
ultrametric norm-one commutative ring with discrete scalar norms and field residue ring is
continuously linearly equivalent to a native model space `C₀(I, R)`. In particular this applies
to complete discretely normed fields. The index type need not be countable. -/
theorem isPotentiallyONable_of_discrete_norm {R : Type*} [NormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] [CompleteSpace R] [(unitBallIdeal R).IsMaximal]
    {E : Type*} [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
    [IsUltrametricDist E] [CompleteSpace E] (ϖ : NormedRing.PseudoUniformizer R)
    (hR : ∀ a : R, zpowCeil ‖(ϖ.unit : R)‖ ‖a‖ = ‖a‖) :
    IsPotentiallyONable R E := by
  rw [isPotentiallyONable_def]
  have hE := fun m : E ↦ zpowCeil_zpowCeil ϖ.norm_pos ϖ.norm_lt_one ‖m‖
  have hu := isUltrametricDist_zpowCeilNormedAddCommGroup
    (M := E) ϖ.norm_pos ϖ.norm_lt_one
  have hs := isBoundedSMul_zpowCeilNormedAddCommGroup
    (M := E) ϖ.norm_pos ϖ.norm_lt_one hR
  let := zpowCeilNormedAddCommGroup (M := E) ϖ.norm_pos ϖ.norm_lt_one
  let := hu
  let := hs
  let := Ideal.Quotient.field (unitBallIdeal R)
  have h : IsONable R E := (isONable_iff_free_residueModule ϖ hR
    (fun m ↦ by simpa only [AddGroupNorm.norm_toNormedAddCommGroupOfUniformity,
      zpowCeilAddGroupNorm_apply] using hE m)).2 inferInstance
  -- The rounded structure retains the original uniformity and topology definitionally.
  -- Thus its continuous linear equivalence also has the original-instance goal's type.
  exact (isPotentiallyONable_def R E).1 h.isPotentiallyONable

end TauCeti
