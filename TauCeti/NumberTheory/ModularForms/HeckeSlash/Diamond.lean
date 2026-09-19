/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.DiamondCosets
public import TauCeti.NumberTheory.HeckeRing.GL2.Gamma1.CoprimeCosets
public import TauCeti.NumberTheory.ModularForms.DiamondOperators
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.CuspRing
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Ring
public import TauCeti.NumberTheory.ModularForms.HeckeSlash.Trace
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map

/-!
# The diamond operators are the Hecke operators of the `Γ₀(N)`-cosets

`ModularForms/DiamondOperators.lean` builds `⟨d⟩` by hand, as slashing by any `Γ₀(N)` matrix
with lower-right entry `d`, and shows the result is well defined on `M_k(Γ₁(N))` and on
`S_k(Γ₁(N))`. `HeckeRing/GL2/Gamma1/DiamondCosets.lean` builds, from the same matrix, an
element of the Hecke ring `𝕋 Δ₀(N) Γ₁(N) ℤ`. This file identifies the two:

`heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N γ) = diamondOp k d`,

and the same on cusp forms, and — through the `ℤ`-linear action of the Hecke ring — the
unit-indexed form `heckeSlashGamma1RingModularFormLinearMap k (diamondHeckeElem N d) =
diamondOp k d`, again on both modular and cusp forms. So the diamond operators are not a
construction parallel to the Hecke operators: they are the Hecke operators of the double cosets
`Γ₁(N) γ Γ₁(N)` with `γ ∈ Γ₀(N)`, and the identification is a theorem rather than a
definition.

## Why it is a one-term sum

Slashing by a double coset means summing over its right cosets. A diamond coset has exactly
one, `Γ₁(N) γ` (`HeckeRing.GL2.doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets`,
which holds because `Γ₁(N)` is normal in `Γ₀(N)`), so the sum
`heckeSlashSum k (diamondCosetGamma1 N γ) f` has a single summand `f ∣[k] γ` — and that is the
defining formula of `⟨d⟩`. The only remaining step is the `ℚ`-to-`ℝ` bridge
`ModularForm.rat_slash_mapGL`, since the Hecke triples live over `ℚ` and the slash action of a
modular form over `ℝ`.

Nothing here needs the choice-freeness of `⟨d⟩` to be reproved: both sides are computed at the
same representative `γ`, and their independence of it is `DiamondOperators.lean`'s
`coe_diamondOp` on one side and `HeckeRing.GL2.diamondCosetGamma1_eq_iff` on the other.

## The adjugate double coset

For `n` prime to `N`, a Bézout identity supplies matrices `A ∈ Γ₀(N)` and `B ∈ Γ₁(N)` that
factor `diag(n, 1)` as both `A diag(1, n) B` and `B diag(1, n) A`. Reading the two
factorizations through the trace description of a Hecke operator proves that the trace of the
translate by `diag(n, 1)` is `⟨n⟩⁻¹ Tₙ`. This is the identity consumed by the Petersson-adjoint
argument. Reading both factorizations also proves that `Tₙ` commutes with `⟨n⟩⁻¹`, which is used
for the nebentypus specialization. This is the standard argument of Diamond--Shurman, §5.5.

## Main results

* `HeckeRing.GL2.heckeSlashSum_diamondCosetGamma1`: the slash sum of a diamond coset is the
  single slash `f ∣[k] γ`, for a form of any of the level-`Γ₁(N)` form classes.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diamondCosetGamma1` and
  `HeckeRing.GL2.heckeSlashGamma1CuspFormEnd_diamondCosetGamma1`: **the identification**, on
  `M_k(Γ₁(N))` and on `S_k(Γ₁(N))`.
* `HeckeRing.GL2.heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem` and
  `HeckeRing.GL2.heckeSlashGamma1CuspRingLinearMap_diamondHeckeElem`: the same statement read on
  the Hecke ring, at the unit-indexed element `⟨d⟩`.
* `HeckeRing.GL2.isFiniteRelIndex_adjugateGL_natDiagGL`: the finite-relative-index instance
  needed to trace the adjugate translate.
* `HeckeRing.GL2.trace_translate_adjugateGL_natDiagGL_eq_diamondOpCusp_heckeTCuspNat`: the
  adjugate trace is `⟨n⟩⁻¹ Tₙ` on cusp forms.
* `HeckeRing.GL2.commute_heckeTNat_diamondOp_inv` and
  `HeckeRing.GL2.commute_heckeTCuspNat_diamondOpCusp_inv`: at every index prime to the level,
  `Tₙ` commutes with the inverse diamond operator `⟨n⟩⁻¹`.
* `HeckeRing.GL2.heckeSlashGamma1ModularFormEnd_diamondCosetGamma1_apply_of_mem_modFormCharSpace`
  and its cusp-form counterpart: on a nebentypus space the diamond coset acts by the scalar
  `χ(d)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  §§5.2 and 5.5.
* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.5.4.
* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  §3.4.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] (k : ℤ) (g : ↥(Gamma0 N))

/-- **The slash sum of a diamond coset is a single slash.** The double coset `Γ₁(N) γ Γ₁(N)`
decomposes into the one right coset `Γ₁(N) γ`, so the Hecke sum attached to it has one
summand. -/
@[simp] theorem heckeSlashSum_diamondCosetGamma1 {F : Type*} [FunLike F ℍ ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    heckeSlashSum k (diamondCosetGamma1 N g) ⇑f = ⇑f ∣[k] (mapGL ℚ (g : SL(2, ℤ))) := by
  refine (heckeSlashSum_coe_eq_sum_of_rightCosets k (diamondCosetGamma1 N g)
    (fun _ : Unit ↦ mapGL ℚ (g : SL(2, ℤ)))
    (doubleCoset_out_diamondCosetGamma1_eq_iUnion_rightCosets g)
    (fun _ _ _ ↦ Subsingleton.elim _ _) f).trans ?_
  simp

/-- **The diamond operator on `M_k(Γ₁(N))` is the Hecke operator of the double coset
`Γ₁(N) γ Γ₁(N)`.** Both sides are slashing by `γ`; the left-hand side arrives as a one-term
Hecke sum over `GL₂(ℚ)`, the right-hand side as the definition of `⟨d⟩` over `GL₂(ℝ)`. -/
@[simp] theorem heckeSlashGamma1ModularFormEnd_diamondCosetGamma1 :
    heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N g) =
      diamondOp k ((Gamma0Map N).toHomUnits g) :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1ModularFormEnd, heckeSlashSum_diamondCosetGamma1,
      ModularForm.rat_slash_mapGL, coe_diamondOp k _ g rfl]

/-- **The diamond operator on `S_k(Γ₁(N))` is the Hecke operator of the double coset
`Γ₁(N) γ Γ₁(N)`.** -/
@[simp] theorem heckeSlashGamma1CuspFormEnd_diamondCosetGamma1 :
    heckeSlashGamma1CuspFormEnd k (diamondCosetGamma1 N g) =
      diamondOpCusp k ((Gamma0Map N).toHomUnits g) :=
  LinearMap.ext fun f ↦ DFunLike.ext' <| by
    rw [coe_heckeSlashGamma1CuspFormEnd, heckeSlashSum_diamondCosetGamma1,
      ModularForm.rat_slash_mapGL, coe_diamondOpCusp k _ g rfl]

/-- **On a nebentypus space the diamond coset acts by the scalar `χ(d)`.** This is the shape
the character-space action of the Hecke ring consumes: on `M_k(N, χ)` the diamond direction of
the ring contributes no new operator, only multiplication by `χ(d)`. -/
theorem heckeSlashGamma1ModularFormEnd_diamondCosetGamma1_apply_of_mem_modFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeSlashGamma1ModularFormEnd k (diamondCosetGamma1 N g) f =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := by
  rw [heckeSlashGamma1ModularFormEnd_diamondCosetGamma1]
  exact diamondOp_apply_of_mem_modFormCharSpace k χ _ hf

/-- **On a nebentypus cusp-form space the diamond coset acts by the scalar `χ(d)`.** -/
theorem heckeSlashGamma1CuspFormEnd_diamondCosetGamma1_apply_of_mem_cuspFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormCharSpace k χ) :
    heckeSlashGamma1CuspFormEnd k (diamondCosetGamma1 N g) f =
      (↑(χ ((Gamma0Map N).toHomUnits g)) : ℂ) • f := by
  rw [heckeSlashGamma1CuspFormEnd_diamondCosetGamma1]
  exact diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hf

/-- **The diamond element of the Hecke ring acts by the diamond operator.** Read through the
`ℤ`-linear action `heckeSlashGamma1RingModularFormLinearMap` of the Hecke ring on `M_k(Γ₁(N))`,
the element `⟨d⟩` of `HeckeRing/GL2/Gamma1/DiamondCosets.lean` is the operator `⟨d⟩` of
`ModularForms/DiamondOperators.lean`. -/
@[simp] theorem heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem (d : (ZMod N)ˣ) :
    heckeSlashGamma1RingModularFormLinearMap k (diamondHeckeElem N d) = diamondOp k d := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  rw [diamondHeckeElem_eq_single γ hγ, heckeSlashGamma1RingModularFormLinearMap_single,
    heckeSlashGamma1ModularFormEnd_diamondCosetGamma1, hγ, one_smul]

/-- **The diamond element of the Hecke ring acts on cusp forms by the diamond operator**: the
cusp-form counterpart of `heckeSlashGamma1RingModularFormLinearMap_diamondHeckeElem`, read
through the `ℤ`-linear action `heckeSlashGamma1CuspRingLinearMap` on `S_k(Γ₁(N))`. -/
@[simp] theorem heckeSlashGamma1CuspRingLinearMap_diamondHeckeElem (d : (ZMod N)ˣ) :
    heckeSlashGamma1CuspRingLinearMap k (diamondHeckeElem N d) = diamondOpCusp k d := by
  obtain ⟨γ, hγ⟩ := Gamma0Map_toHomUnits_surjective (N := N) d
  rw [diamondHeckeElem_eq_single γ hγ, heckeSlashGamma1CuspRingLinearMap_single,
    heckeSlashGamma1CuspFormEnd_diamondCosetGamma1, hγ, one_smul]

section Adjugate

open Matrix DoubleCoset HeckeRing.GLn
open TauCeti (adjugateGL adjugateGL_val finite_decompQuotient_inv_of_mem_doubleCoset)
open scoped Pointwise

local notation "φ" => Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℚ ℝ)

variable {n : ℕ} [NeZero n]

/-- The finite relative index required to trace the main involution of `diag(1, n)`. -/
lemma isFiniteRelIndex_adjugateGL_natDiagGL (hn : n.Coprime N) :
    (ConjAct.toConjAct (adjugateGL (φ (natDiagGL 2 ![1, n])))⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := by
  obtain ⟨A, hA, -, B, hB, hadj, -⟩ := exists_adjugateGL_natDiagGL_eq hn
  have := finite_decompQuotient_inv_of_mem_doubleCoset
    (g := natDiagGL 2 ![1, n]) (H := (Gamma1 N).map (mapGL ℚ))
    (K := (Gamma1 N).map (mapGL ℚ))
    (mem_doubleCoset.mpr
      ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, by rw [one_mul]⟩)
  rw [hadj, conjAct_mapGL_mul_smul_Gamma1 hA]
  infer_instance

/-- The modular-form double coset operator of `diag(n, 1)` is `Tₙ ⟨n⟩⁻¹`. -/
private theorem trace_translate_adjugateGL_natDiagGL_eq_heckeTNat_diamondOp
    (hn : n.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
    ModularForm.trace ((Gamma1 N).map (mapGL ℝ))
        (ModularForm.translate f (adjugateGL (φ (natDiagGL 2 ![1, n])))) =
      heckeTNat k n (diamondOp k (ZMod.unitOfCoprime n hn)⁻¹ f) := by
  let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
  obtain ⟨A, hA, hAd, B, hB, hadj, -⟩ := exists_adjugateGL_natDiagGL_eq hn
  have hδ : natDiagGL 2 ![1, n] * mapGL ℚ B ∈
      doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset.mpr
      ⟨1, one_mem _, mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, by rw [one_mul]⟩
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ
  apply DFunLike.coe_injective
  rw [coe_heckeTNat,
    TauCeti.heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ
      (TauCeti.map_map_mapGL (Gamma1 N)) (TauCeti.map_map_mapGL (Gamma1 N))]
  refine congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq
    (by rw [hadj, conjAct_mapGL_mul_smul_Gamma1 hA]) ?_)
  rw [ModularForm.coe_translate, SlashInvariantForm.coe_translate,
    coe_diamondOp k _ ⟨A, hA⟩ hAd, ← SlashAction.slash_mul, hadj]

/-- The modular-form double coset operator of `diag(n, 1)` is `⟨n⟩⁻¹ Tₙ`. -/
private theorem trace_translate_adjugateGL_natDiagGL_eq_diamondOp_heckeTNat
    (hn : n.Coprime N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
    ModularForm.trace ((Gamma1 N).map (mapGL ℝ))
        (ModularForm.translate f (adjugateGL (φ (natDiagGL 2 ![1, n])))) =
      diamondOp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTNat k n f) := by
  let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
  obtain ⟨A, hA, hAd, B, hB, -, hadj⟩ := exists_adjugateGL_natDiagGL_eq hn
  have hδ : mapGL ℚ B * natDiagGL 2 ![1, n] ∈
      doubleCoset ((diagCosetGamma1 N n).out : GL (Fin 2) ℚ)
        ((Gamma1 N).map (mapGL ℚ)) ((Gamma1 N).map (mapGL ℚ)) := by
    rw [doubleCoset_out_diagCosetGamma1_eq_doubleCoset_natDiagGL]
    exact mem_doubleCoset.mpr
      ⟨mapGL ℚ B, Subgroup.mem_map_of_mem _ hB, 1, one_mem _, by rw [mul_one]⟩
  have := finite_decompQuotient_inv_of_mem_doubleCoset hδ
  have : (ConjAct.toConjAct (φ (mapGL ℚ B * natDiagGL 2 ![1, n]) * mapGL ℝ A)⁻¹ •
      (Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex ((Gamma1 N).map (mapGL ℝ)) := hadj ▸ ‹_›
  apply DFunLike.coe_injective
  rw [coe_diamondOp k _ ⟨A, hA⟩ hAd, coe_heckeTNat,
    TauCeti.heckeSlashSum_eq_coe_trace_translate k (diagCosetGamma1 N n) hδ
      (TauCeti.map_map_mapGL (Gamma1 N)) (TauCeti.map_map_mapGL (Gamma1 N)),
    ← TauCeti.SlashInvariantForm.coe_trace_translate_mul_of_mem_normalizer _ _
      (mapGL_mem_normalizer_Gamma1_map ℝ ⟨A, hA⟩)]
  refine congrArg DFunLike.coe (TauCeti.SlashInvariantForm.trace_eq_of_eq_of_coe_eq
    (by rw [hadj]) ?_)
  rw [ModularForm.coe_translate, SlashInvariantForm.coe_translate, hadj]

/-- **`⟨n⟩⁻¹` commutes with `Tₙ` on modular forms.** For `n` coprime to `N`, the inverse
diamond operator commutes with `Tₙ` on `M_k(Γ₁(N))`. -/
theorem commute_heckeTNat_diamondOp_inv (hn : n.Coprime N) :
    Commute (heckeTNat k n) (diamondOp k (ZMod.unitOfCoprime n hn)⁻¹) := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro f
  simp only [Module.End.mul_apply]
  rw [← trace_translate_adjugateGL_natDiagGL_eq_heckeTNat_diamondOp k hn,
    trace_translate_adjugateGL_natDiagGL_eq_diamondOp_heckeTNat k hn]

/-- **The double coset operator of `diag(n, 1)` is `⟨n⟩⁻¹ Tₙ`.** For `n` coprime to `N`, the
trace of the translate by the main involution of `diag(1, n)` is `⟨n⁻¹⟩ (Tₙ f)`. -/
theorem trace_translate_adjugateGL_natDiagGL_eq_diamondOpCusp_heckeTCuspNat
    (hn : n.Coprime N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
    CuspForm.trace ((Gamma1 N).map (mapGL ℝ))
        (CuspForm.translate f (adjugateGL (φ (natDiagGL 2 ![1, n])))) =
      diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹ (heckeTCuspNat k n f) := by
  let _ := isFiniteRelIndex_adjugateGL_natDiagGL hn
  apply CuspForm.toModularFormₗ_injective
  rw [CuspForm.toModularFormₗ_eq_coe, CuspForm.toModularFormₗ_eq_coe,
    TauCeti.trace_translate_coe_cuspForm, ← diamondOp_coe_cuspForm,
    ← heckeTNat_coe_cuspForm]
  exact trace_translate_adjugateGL_natDiagGL_eq_diamondOp_heckeTNat k hn _

/-- **`⟨n⟩⁻¹` commutes with `Tₙ`.** For `n` coprime to `N`, the inverse diamond operator
commutes with `Tₙ` on `S_k(Γ₁(N))`. -/
theorem commute_heckeTCuspNat_diamondOpCusp_inv (hn : n.Coprime N) :
    Commute (heckeTCuspNat k n) (diamondOpCusp k (ZMod.unitOfCoprime n hn)⁻¹) := by
  rw [commute_iff_eq]
  apply LinearMap.ext
  intro f
  apply CuspForm.toModularFormₗ_injective
  simpa only [Module.End.mul_apply, CuspForm.toModularFormₗ_eq_coe,
    heckeTNat_coe_cuspForm, diamondOp_coe_cuspForm] using
    DFunLike.congr_fun (commute_heckeTNat_diamondOp_inv k hn).eq
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

end Adjugate

end HeckeRing.GL2

end
