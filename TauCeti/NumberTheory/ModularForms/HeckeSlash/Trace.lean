/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.NormTrace
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
public import TauCeti.NumberTheory.HeckeRing.StabConjugation
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# Hecke slash sums as traces

A double-coset operator is the trace of a translate. The rational cosets used by
`HeckeRing.GL2.heckeSlashSum` and the real cosets used by Mathlib's trace correspond under
extension of scalars. Consequently the two constructions agree, with no extra determinant
factor: both use the arithmetic slash action.

This comparison allows the Petersson adjunction for traces of translates to be applied to
Hecke operators already constructed from rational double cosets.

The trace of a form depends only on its underlying function and its level, not on the type the
form is packaged in (`TauCeti.SlashInvariantForm.trace_eq_of_coe_eq`). This is what lets a trace
of a translate be compared with another one whose level is equal but not syntactically so, as
happens when the translating matrix is changed by an element normalizing the level. When that
element multiplies on the right, it comes out of the trace as a slash
(`TauCeti.SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer`). The lemma
`CuspForm.coe_trace_translate` records the compatibility of the cusp-form and
modular-form trace constructions.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Sections 5.1 and 5.5.
* David Loeffler, Mathlib's trace construction in `NormTrace.lean`.
-/

public section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane DoubleCoset HeckeRing.GL2
open scoped MatrixGroups ModularForm Pointwise

namespace CuspForm

/-- Coercing the cusp-form trace of a translate to a modular form agrees with tracing the
corresponding translated modular form. -/
theorem coe_trace_translate {k : ℤ} {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    (f : CuspForm 𝒢 k) (x : GL (Fin 2) ℝ)
    [(ConjAct.toConjAct x⁻¹ • 𝒢).IsFiniteRelIndex ℋ] :
    (CuspForm.trace ℋ (CuspForm.translate f x) : ModularForm ℋ k) =
      ModularForm.trace ℋ (ModularForm.translate (f : ModularForm 𝒢 k) x) := by
  rfl

end CuspForm

namespace TauCeti

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

namespace SlashInvariantForm

/-- **The trace sees only the underlying function and the level.** Two slash-invariant forms
with the same underlying function, for levels that are equal (though perhaps not
syntactically), have the same trace. -/
theorem trace_eq_of_coe_eq {k : ℤ} {𝒢₁ 𝒢₂ ℋ : Subgroup (GL (Fin 2) ℝ)} (h : 𝒢₁ = 𝒢₂)
    [𝒢₁.IsFiniteRelIndex ℋ] [𝒢₂.IsFiniteRelIndex ℋ] {F₁ F₂ : Type*} [FunLike F₁ ℍ ℂ]
    [SlashInvariantFormClass F₁ 𝒢₁ k] [FunLike F₂ ℍ ℂ] [SlashInvariantFormClass F₂ 𝒢₂ k]
    {f₁ : F₁} {f₂ : F₂} (hf : ⇑f₁ = ⇑f₂) :
    _root_.SlashInvariantForm.trace ℋ f₁ = _root_.SlashInvariantForm.trace ℋ f₂ := by
  subst h
  ext τ
  simp only [_root_.SlashInvariantForm.coe_trace]
  refine congrFun (Finset.sum_congr rfl fun q _ ↦ ?_) τ
  induction q using Quotient.inductionOn with
  | h r => simp [hf]

/-- **Translating by a normalizing element commutes with the trace.** If `a` normalizes the
level `ℋ`, the trace of the translate of `f` by `x a` is the slash by `a` of the trace of the
translate by `x`. The cosets of the two traces correspond under conjugation by `a`. -/
theorem coe_trace_translate_mul_of_mem_normalizer {k : ℤ} {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)}
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒢 k] (f : F) (x : GL (Fin 2) ℝ)
    {a : GL (Fin 2) ℝ} (ha : a ∈ Subgroup.normalizer (ℋ : Set (GL (Fin 2) ℝ)))
    [(ConjAct.toConjAct x⁻¹ • 𝒢).IsFiniteRelIndex ℋ]
    [(ConjAct.toConjAct (x * a)⁻¹ • 𝒢).IsFiniteRelIndex ℋ] :
    ⇑(_root_.SlashInvariantForm.trace ℋ (_root_.SlashInvariantForm.translate f (x * a))) =
      ⇑(_root_.SlashInvariantForm.trace ℋ (_root_.SlashInvariantForm.translate f x)) ∣[k] a := by
  have hsub : (ConjAct.toConjAct (x * a)⁻¹ • 𝒢).subgroupOf ℋ =
      (ConjAct.toConjAct (a⁻¹ * x⁻¹) • 𝒢).subgroupOf ℋ := by
    rw [_root_.mul_inv_rev]
  let e : ℋ ⧸ (ConjAct.toConjAct (x * a)⁻¹ • 𝒢).subgroupOf ℋ ≃
      ℋ ⧸ (ConjAct.toConjAct x⁻¹ • 𝒢).subgroupOf ℋ :=
    (Subgroup.quotientEquivOfEq hsub).trans
      (decompQuotientEquivMulLeft ℋ 𝒢 x⁻¹ ⟨a⁻¹, Subgroup.inv_mem _ ha⟩)
  rw [SlashInvariantForm.coe_trace, SlashInvariantForm.coe_trace, SlashAction.sum_slash]
  let := Fintype.ofFinite (ℋ ⧸ (ConjAct.toConjAct (x * a)⁻¹ • 𝒢).subgroupOf ℋ)
  let := Fintype.ofFinite (ℋ ⧸ (ConjAct.toConjAct x⁻¹ • 𝒢).subgroupOf ℋ)
  refine Fintype.sum_equiv e _ _ fun q ↦ ?_
  induction q using Quotient.inductionOn with
  | h r =>
    have he : e ⟦r⟧ =
        ⟦⟨a * r * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha r).mp r.2⟩⟧ := by
      dsimp only [e]
      rw [Equiv.trans_apply, Subgroup.quotientEquivOfEq_mk,
        decompQuotientEquivMulLeft_mk]
      rfl
    rw [he]
    rw [SlashInvariantForm.quotientFunc_mk, SlashInvariantForm.quotientFunc_mk,
      SlashInvariantForm.coe_translate, SlashInvariantForm.coe_translate, ← SlashAction.slash_mul,
      ← SlashAction.slash_mul, ← SlashAction.slash_mul]
    congr 1
    simp [mul_assoc]

end SlashInvariantForm

variable {Γ₁ Γ₂ : Subgroup (GL (Fin 2) ℚ)} {δ : GL (Fin 2) ℚ}

/-- A finite rational double-coset decomposition gives the finite relative index needed to
trace a translate after extension of scalars to `ℝ`. -/
theorem isFiniteRelIndex_ratCast_conj
    [Finite (DecompQuotient Γ₂ Γ₁ δ⁻¹)] :
    (ConjAct.toConjAct (φ δ)⁻¹ • Γ₁.map φ).IsFiniteRelIndex (Γ₂.map φ) := by
  have h : (ConjAct.toConjAct δ⁻¹ • Γ₁).IsFiniteRelIndex Γ₂ := by
    rw [Subgroup.isFiniteRelIndex_iff_finiteIndex]
    exact Subgroup.finiteIndex_of_finite_quotient
  have hmap : (ConjAct.toConjAct δ⁻¹ • Γ₁).map φ =
      ConjAct.toConjAct (φ δ)⁻¹ • Γ₁.map φ := by
    -- Express the conjugation action as subgroup maps so `map_map` applies to both sides.
    change (Γ₁.map (MulAut.conj δ⁻¹).toMonoidHom).map φ =
      (Γ₁.map φ).map (MulAut.conj (φ δ)⁻¹).toMonoidHom
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext g
    simp
  simpa only [hmap] using h.map φ

/-- The rational slash sum equals the trace of the translate by any representative of the
same double coset. This statement needs only slash invariance, and allows different source
and target groups. -/
theorem heckeSlashSum_eq_coe_trace_translate {Δ : Submonoid (GL (Fin 2) ℚ)}
    (k : ℤ) (D : HeckeCoset Δ Γ₁ Γ₂)
    [Finite (DecompQuotient Γ₂ Γ₁ (D.out : GL (Fin 2) ℚ)⁻¹)]
    (hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) Γ₁ Γ₂)
    {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} (hΓ₁ : Γ₁.map φ = 𝒢) (hΓ₂ : Γ₂.map φ = ℋ)
    {F : Type*} [FunLike F ℍ ℂ] [SlashInvariantFormClass F 𝒢 k] (f : F) :
    let := finite_decompQuotient_inv_of_mem_doubleCoset hδ
    letI : (ConjAct.toConjAct (φ δ)⁻¹ • 𝒢).IsFiniteRelIndex ℋ := by
      rw [← hΓ₁, ← hΓ₂]
      exact isFiniteRelIndex_ratCast_conj
    heckeSlashSum k D f =
      ⇑(SlashInvariantForm.trace ℋ (SlashInvariantForm.translate f (φ δ))) := by
  subst 𝒢 ℋ
  classical
  let := finite_decompQuotient_inv_of_mem_doubleCoset hδ
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
    (hδ : δ ∈ doubleCoset (D.out : GL (Fin 2) ℚ) (G.map (mapGL ℚ)) (G.map (mapGL ℚ)))
    (f : CuspForm (G.map (mapGL ℝ)) k) :
    let := finite_decompQuotient_inv_of_mem_doubleCoset hδ
    heckeSlashCuspFormEnd k D hD f =
      CuspForm.trace (G.map (mapGL ℝ)) (CuspForm.translate f (φ δ)) := by
  let := finite_decompQuotient_inv_of_mem_doubleCoset hδ
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
