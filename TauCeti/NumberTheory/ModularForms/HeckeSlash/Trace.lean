/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Hecke slash sums as traces

A double-coset operator is the trace of a translate. The rational cosets used by
`HeckeRing.GL2.heckeSlashSum` and the real cosets used by Mathlib's trace correspond under
extension of scalars. Consequently the two constructions agree, with no extra determinant
factor: both use the arithmetic slash action.

This comparison allows the Petersson adjunction for traces of translates to be applied to
Hecke operators already constructed from rational double cosets.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 5.1 and 5.5.

The proof uses Mathlib's trace construction (`NormTrace.lean`, David Loeffler) and Tau Ceti's
`DoubleCoset.decompQuotientEquivMapOfInjective` to compare the indexing quotients.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

variable {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)} {δ : GL (Fin 2) ℚ}

/-- A finite rational double-coset decomposition gives the finite relative index needed to
trace a translate after extension of scalars to `ℝ`. -/
theorem isFiniteRelIndex_ratCast_conj
    [Finite (DecompQuotient Γ₂ Γ₁ δ⁻¹)] :
    (ConjAct.toConjAct (φ δ)⁻¹ • Γ₁.map φ).IsFiniteRelIndex (Γ₂.map φ) := by
  have hinj := Matrix.GeneralLinearGroup.map_injective (n := Fin 2) (algebraMap ℚ ℝ).injective
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, Subgroup.finiteIndex_iff_finite_quotient]
  have h := (decompQuotientEquivMapOfInjective φ hinj Γ₂ Γ₁ δ⁻¹).finite_iff.mp
    (inferInstance : Finite (DecompQuotient Γ₂ Γ₁ δ⁻¹))
  simpa only [DecompQuotient, map_inv] using h

/-- The rational slash sum equals the trace of the translate by any representative of the
same double coset. This statement needs only slash invariance, and allows different source
and target groups. -/
theorem heckeSlashSum_eq_coe_trace_translate {Δ : Submonoid (GL (Fin 2) ℚ)}
    (k : ℤ) (D : HeckeCoset Δ Γ₁ Γ₂)
    [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
    [Finite (DecompQuotient Γ₂ Γ₁ δ⁻¹)]
    (hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂)
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} (hΓ₁ : Γ₁.map φ = 𝒢) (hΓ₂ : Γ₂.map φ = ℋ)
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒢 k] (f : F) :
    letI : (ConjAct.toConjAct (φ δ)⁻¹ • 𝒢).IsFiniteRelIndex ℋ := by
      rw [← hΓ₁, ← hΓ₂]
      exact isFiniteRelIndex_ratCast_conj
    heckeSlashSum k D f =
      ⇑(SlashInvariantForm.trace ℋ (SlashInvariantForm.translate f (φ δ))) := by
  subst 𝒢 ℋ
  classical
  have hinj := Matrix.GeneralLinearGroup.map_injective (n := Fin 2) (algebraMap ℚ ℝ).injective
  let := isFiniteRelIndex_ratCast_conj (Γ₁ := Γ₁) (Γ₂ := Γ₂) (δ := δ)
  let : Fintype (DecompQuotient Γ₂ Γ₁ δ⁻¹) := Fintype.ofFinite _
  let e : DecompQuotient Γ₂ Γ₁ δ⁻¹ ≃
      (Γ₂.map φ) ⧸ (ConjAct.toConjAct (φ δ)⁻¹ • Γ₁.map φ).subgroupOf (Γ₂.map φ) :=
    QuotientGroup.congrOfMapEq (Subgroup.equivMapOfInjective Γ₂ φ hinj)
      (by simpa only [map_inv] using map_subgroupOf_smul φ hinj Γ₂ Γ₁ δ⁻¹)
  let : Fintype ((Γ₂.map φ) ⧸
      (ConjAct.toConjAct (φ δ)⁻¹ • Γ₁.map φ).subgroupOf (Γ₂.map φ)) := Fintype.ofFinite _
  rw [heckeSlashSum_eq_sum_of_mem_doubleCoset k D hδ f (fun γ hγ ↦ by
    rw [ModularForm.rat_slash]
    exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem φ hγ))]
  rw [SlashInvariantForm.coe_trace, ← e.sum_comp]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  conv_rhs => rw [← Quotient.out_eq q]
  dsimp only [e]
  rw [QuotientGroup.congrOfMapEq_mk, SlashInvariantForm.quotientFunc_mk,
    SlashInvariantForm.coe_translate, ← SlashAction.slash_mul, ModularForm.rat_slash,
    map_mul, map_inv, Subgroup.coe_equivMapOfInjective_apply]

/-- The real conjugate of an integral level has finite relative index whenever its rational
right-coset decomposition is finite. This supplies the instance required by Mathlib's trace. -/
instance isFiniteRelIndex_conj_mapGL {G H : Subgroup SL(2, ℤ)}
    [Finite (DecompQuotient (H.map (mapGL ℚ)) (G.map (mapGL ℚ)) δ⁻¹)] :
    (ConjAct.toConjAct (φ δ)⁻¹ • G.map (mapGL ℝ)).IsFiniteRelIndex (H.map (mapGL ℝ)) := by
  have hφ : (φ).comp (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) = mapGL ℝ :=
    MonoidHom.ext fun g ↦ map_mapGL g
  simpa only [Subgroup.map_map, hφ] using
    (isFiniteRelIndex_ratCast_conj (Γ₁ := G.map (mapGL ℚ))
      (Γ₂ := H.map (mapGL ℚ)) (δ := δ))

/-- The rational double-coset operator on cusp forms is Mathlib's trace of a translate.
The representative `δ` may be chosen anywhere in the double coset. -/
theorem heckeSlashCuspFormEnd_eq_trace_translate {G : Subgroup SL(2, ℤ)}
    [(G.map (mapGL ℝ)).IsArithmetic] {Δ : Submonoid (GL (Fin 2) ℚ)}
    (k : ℤ) (D : HeckeCoset Δ (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
    [Finite (DecompQuotient (G.map (mapGL ℚ)) (G.map (mapGL ℚ))
      (D.out : GL (Fin 2) ℚ)⁻¹)]
    (hD : (D.out : GL (Fin 2) ℚ) ∈ Matrix.GLPos (Fin 2) ℚ)
    [Finite (DecompQuotient (G.map (mapGL ℚ)) (G.map (mapGL ℚ)) δ⁻¹)]
    (hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
    (f : CuspForm (G.map (mapGL ℝ)) k) :
    heckeSlashCuspFormEnd k D hD f =
      CuspForm.trace (G.map (mapGL ℝ)) (CuspForm.translate f (φ δ)) := by
  apply DFunLike.coe_injective
  rw [coe_heckeSlashCuspFormEnd]
  have hφ : (φ).comp (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) = mapGL ℝ :=
    MonoidHom.ext fun g ↦ map_mapGL g
  have hG : (G.map (mapGL ℚ)).map φ = G.map (mapGL ℝ) := by
    rw [Subgroup.map_map, hφ]
  exact heckeSlashSum_eq_coe_trace_translate k D hδ hG hG f

open CongruenceSubgroup HeckeRing.GLn

/-- The operator attached to `Γ₁(N) diag(1,n) Γ₁(N)` is the trace of the translate by
`diag(1,n)`, with no additional normalization factor. The formula holds for every positive
index, including indices divisible by primes in the level. -/
theorem heckeTCuspNat_eq_trace_translate (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeTCuspNat (N := N) k n f = CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
      (CuspForm.translate f (φ (natDiagGL 2 ![1, n]))) := by
  apply DFunLike.coe_injective
  rw [coe_heckeTCuspNat]
  have hφ : (φ).comp (mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ) = mapGL ℝ :=
    MonoidHom.ext fun g ↦ map_mapGL g
  have hG : ((Gamma1 N).map (mapGL ℚ)).map φ = (Gamma1 N).map (mapGL ℝ) := by
    rw [Subgroup.map_map, hφ]
  apply heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) _ hG hG f
  rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
  exact mem_doubleCoset_self _ _ _

end TauCeti
