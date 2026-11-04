/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LevelOne.Hecke
public import TauCeti.NumberTheory.ModularForms.LFunction.EulerProduct
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Nebentypus.CoefficientFormula

/-!
# Newforms of level one

The newforms of level one are newforms for `Γ₁(1)`, whose image in `GL(2, ℝ)` is that of
`SL(2, ℤ)`. This file transports them to cusp forms on `SL(2, ℤ)` and collects the facts about
them that the Hecke operators `Tₙ` of `TauCeti.heckeTCuspLevelOne` see. Every cusp form of level
one is new, so the newforms span `S_k(SL(2, ℤ))`; each is an eigenvector of every `Tₙ` with
eigenvalue its Fourier coefficient `aₙ`, both operators having the divisor-sum coefficient formula
with trivial nebentypus; and a newform is determined by these eigenvalues. Together these say that
a linear map out of `S_k(SL(2, ℤ))` which intertwines every `Tₙ` with an endomorphism of its target
is injective as soon as it does not kill a newform: the images of the newforms are joint
eigenvectors with distinct eigenvalue systems.

## Main definitions

* `TauCeti.cuspFormGamma1OneEquiv`: the linear isomorphism between cusp forms for `Γ₁(1)` and
  cusp forms on `SL(2, ℤ)`, which does not change the underlying function.

## Main results

* `TauCeti.subsingleton_cuspForm_levelOne`: in odd weight or below weight `12` there are no
  nonzero cusp forms on `SL(2, ℤ)`.
* `HeckeRing.GL2.Newform.heckeTCuspLevelOne_cuspFormGamma1OneEquiv`: a newform `g` of level one
  is an eigenvector of every `Tₙ` with eigenvalue `aₙ(g)`.
* `HeckeRing.GL2.Newform.span_range_cuspFormGamma1OneEquiv_toCuspForm`: the newforms of level one
  span `S_k(SL(2, ℤ))`.
* `HeckeRing.GL2.Newform.L_cuspFormGamma1OneEquiv_ne_zero`: the `L`-function of a newform of
  level one does not vanish on `Re s > k/2 + 1`.
* `TauCeti.injective_of_map_heckeTCuspLevelOne_eq`: a linear map out of `S_k(SL(2, ℤ))` that
  intertwines every `Tₙ` with an endomorphism of its target and is nonzero on every newform is
  injective.
-/

public section

open CongruenceSubgroup Matrix.SpecialLinearGroup HeckeRing.GL2 UpperHalfPlane
open scoped MatrixGroups

variable {k : ℤ}

namespace TauCeti

/-! ### Cusp forms of level one -/

/-- Cusp forms for `Γ₁(1)` are cusp forms on `SL(2, ℤ)`, the two groups having the same image in
`GL(2, ℝ)`. The isomorphism does not change the underlying function. -/
def cuspFormGamma1OneEquiv : CuspForm ((Gamma1 1).map (mapGL ℝ)) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun F := CuspForm.mcast rfl F Gamma1_one_map_eq_SL.symm
  invFun f := CuspForm.mcast rfl f Gamma1_one_map_eq_SL
  map_add' F G := CuspForm.ext fun z ↦ by simp [CuspForm.mcast_apply]
  map_smul' c F := CuspForm.ext fun z ↦ by simp [CuspForm.mcast_apply]
  left_inv F := CuspForm.ext fun z ↦ by simp [CuspForm.mcast_apply]
  right_inv f := CuspForm.ext fun z ↦ by simp [CuspForm.mcast_apply]

/-- `TauCeti.cuspFormGamma1OneEquiv` does not change the underlying function. -/
@[simp]
theorem coe_cuspFormGamma1OneEquiv (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k) :
    ⇑(cuspFormGamma1OneEquiv F) = ⇑F :=
  funext (CuspForm.mcast_apply rfl F Gamma1_one_map_eq_SL.symm)

/-- The inverse of `TauCeti.cuspFormGamma1OneEquiv` does not change the underlying function. -/
@[simp]
theorem coe_cuspFormGamma1OneEquiv_symm (f : CuspForm 𝒮ℒ k) :
    ⇑(cuspFormGamma1OneEquiv.symm f) = ⇑f :=
  funext (CuspForm.mcast_apply rfl f Gamma1_one_map_eq_SL)

/-- In odd weight or below weight `12` there are no nonzero cusp forms on `SL(2, ℤ)`. -/
theorem subsingleton_cuspForm_levelOne (h : Odd k ∨ k < 12) : Subsingleton (CuspForm 𝒮ℒ k) := by
  rcases h with hk | hk
  · refine ⟨fun f g ↦ CuspForm.toModularFormₗ_injective ?_⟩
    rw [ModularForm.levelOne_odd_weight_eq_zero hk (CuspForm.toModularFormₗ f),
      ModularForm.levelOne_odd_weight_eq_zero hk (CuspForm.toModularFormₗ g)]
  · exact rank_zero_iff.1 (CuspForm.rank_eq_zero_of_weight_lt_twelve hk)

end TauCeti

namespace HeckeRing.GL2.Newform

open TauCeti

/-! ### Newforms of level one as Hecke eigenforms on `SL(2, ℤ)` -/

/-- A newform `g` of level one is an eigenvector of every `Tₙ` on `S_k(SL(2, ℤ))`, with eigenvalue
`aₙ(g)`: both operators have the divisor-sum coefficient formula, the nebentypus being trivial. -/
theorem heckeTCuspLevelOne_cuspFormGamma1OneEquiv (g : Newform 1 k) (n : ℕ+) :
    heckeTCuspLevelOne k n (cuspFormGamma1OneEquiv g.toCuspForm) =
      (qExpansion 1 g.toCuspForm).coeff n • cuspFormGamma1OneEquiv g.toCuspForm := by
  refine CuspForm.qExpansion_injective one_pos one_mem_strictPeriods_SL
    (PowerSeries.ext fun m ↦ ?_)
  have h := congrArg (fun F : cuspFormCharSpace k g.χ ↦
      (qExpansion 1 (F : CuspForm ((Gamma1 1).map (mapGL ℝ)) k)).coeff m)
    (heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_qExpansion_coeff_smul g n)
  rw [qExpansion_coeff_heckeRingHomCuspCharSpace_heckeTCompositeGamma0 n.ne_zero] at h
  simp only [Submodule.coe_smul, FunLike.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map 1),
    PowerSeries.coeff_smul, smul_eq_mul] at h
  rw [qExpansion_coeff_heckeTCuspLevelOne]
  simp only [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL,
    PowerSeries.coeff_smul, smul_eq_mul]
  rw [coe_cuspFormGamma1OneEquiv, ← h]
  -- the character of `g` is trivial, as is every Dirichlet character modulo `1`
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [DirichletCharacter.level_one (MulChar.ofUnitHom g.χ),
    MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- The newforms of level one span `S_k(SL(2, ℤ))`, every cusp form of level one being new. -/
theorem span_range_cuspFormGamma1OneEquiv_toCuspForm :
    Submodule.span ℂ (Set.range fun g : Newform 1 k ↦ cuspFormGamma1OneEquiv g.toCuspForm) = ⊤ := by
  rw [Set.range_comp' cuspFormGamma1OneEquiv, ← LinearEquiv.coe_coe, Submodule.span_image,
    span_range_toCuspForm_eq_cuspFormsNew, cuspFormsNew_one, Submodule.map_top,
    LinearEquiv.range]

/-- The `L`-function of a newform of level one does not vanish on `Re s > k/2 + 1`. -/
theorem L_cuspFormGamma1OneEquiv_ne_zero (g : Newform 1 k) (hk : 0 < k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    ModularForm.L hk (cuspFormGamma1OneEquiv g.toCuspForm) s ≠ 0 := by
  intro hL
  have h := CuspForm.LSeries_qExpansion_coeff_eq hk (cuspFormGamma1OneEquiv g.toCuspForm) hs
  rw [hL, mul_zero, Subgroup.strictWidthInfty_SL2Z, coe_cuspFormGamma1OneEquiv] at h
  exact g.LSeries_ne_zero_of_lt_re (by linarith) h

end HeckeRing.GL2.Newform

namespace TauCeti

/-! ### Injectivity of Hecke-equivariant maps -/

/-- A linear map out of `S_k(SL(2, ℤ))` that intertwines every `Tₙ` with some endomorphism of its
target and is nonzero on every newform is injective. -/
theorem injective_of_map_heckeTCuspLevelOne_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (Φ : CuspForm 𝒮ℒ k →ₗ[ℂ] V) (A : ℕ+ → Module.End ℂ V)
    (hΦ : ∀ (n : ℕ+) (f : CuspForm 𝒮ℒ k), Φ (heckeTCuspLevelOne k n f) = A n (Φ f))
    (hne : ∀ g : Newform 1 k, Φ (cuspFormGamma1OneEquiv g.toCuspForm) ≠ 0) :
    Function.Injective Φ := by
  -- the images of the newforms are joint eigenvectors of the `A n` with distinct eigenvalues
  have hmem (g : Newform 1 k) : Φ (cuspFormGamma1OneEquiv g.toCuspForm) ∈
      ⨅ n, (A n).eigenspace ((qExpansion 1 g.toCuspForm).coeff n) :=
    Submodule.mem_iInf _ |>.2 fun n ↦ Module.End.mem_eigenspace_iff.2 <| by
      rw [← hΦ, Newform.heckeTCuspLevelOne_cuspFormGamma1OneEquiv, map_smul]
  have hli : LinearIndependent ℂ fun g : Newform 1 k ↦ Φ (cuspFormGamma1OneEquiv g.toCuspForm) :=
    ((iSupIndep_iInf_eigenspace A).comp Newform.injective_qExpansion_coeff_pnat).linearIndependent
      _ hmem hne
  -- every cusp form is a combination of newforms, on which `Φ` is injective
  have hsurj : Function.Surjective
      (Finsupp.linearCombination ℂ fun g : Newform 1 k ↦ cuspFormGamma1OneEquiv g.toCuspForm) := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination,
      Newform.span_range_cuspFormGamma1OneEquiv_toCuspForm]
  intro f f' hff'
  obtain ⟨c, rfl⟩ := hsurj f
  obtain ⟨c', rfl⟩ := hsurj f'
  rw [Finsupp.apply_linearCombination, Finsupp.apply_linearCombination] at hff'
  rw [hli hff']

end TauCeti
