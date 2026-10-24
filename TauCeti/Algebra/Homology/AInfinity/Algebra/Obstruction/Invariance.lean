/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Formal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Obstruction
import Mathlib.Tactic.LinearCombination

/-!
# Invariance of the quartic obstruction under `A∞` isomorphisms

Let `ℋ` be a graded algebra, presented as a minimal `A∞` algebra without operations above arity
two, and let `𝒜` be a minimal `A∞` structure on the same graded module with the binary operation
of `ℋ` and `m₃ = 0`.  Its first obstruction to formality is the operation `m₄`, a Hochschild
cocycle of `ℋ` (`TauCeti.AInfinityAlgebra.hochschildDifferential_obstruction`) whose class lies in
`HH^{4, -2}(H, H)`.  A gauge transformation by a Hochschild coboundary kills it
(`TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential`).  This file
proves the converse when `2` is invertible: if `𝒜` is `A∞` isomorphic to `ℋ`, then `m₄` is a
Hochschild coboundary (`IsMinimal.exists_hochschildDifferential_eq_obstruction_four_of_isIso`).
Consequently, over a field of characteristic different from two, a quartic obstruction which is
not a coboundary makes `𝒜` non-formal
(`IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four`).

The isomorphism may have a nonzero quadratic component `f₂`, so the obstruction need not be the
coboundary of the cubic component `f₃` alone.  First, the linear part of the isomorphism is a graded
algebra automorphism of `ℋ`; composing with its inverse reduces to an isomorphism with linear
part the identity.  Its Taylor map is then `letter + ψ`, and the morphism equation says that
`m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}` for the coalgebra map `F` with these Taylor components, as for a gauge
transformation.  On the words of length at most three this gives `δψ = 0`.  On the words of
length four the quadratic part of `F` contributes the term `m_ℋ{ψ, ψ}`, and the second-order
expansion of `F`
(`TauCeti.ReducedTensorWords.two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration`) together
with the pre-Lie identity of the brace shows that twice this term is the coboundary `-δ(ψ{ψ})`.
Hence `m₄ = δ(ψ - ½ ψ{ψ})` on the words of length four.  This is the classical fact that twice
the cup square of a Hochschild cocycle of odd total degree is a coboundary; the argument divides
by `2`.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.exists_hochschildDifferential_eq_obstruction_four_of_isIso`:
  when `2` is invertible, the quartic obstruction of a minimal `A∞` structure with `m₃ = 0` which
  is `A∞` isomorphic to the graded algebra `ℋ` is a Hochschild coboundary.
* `IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four`:
  over a field of characteristic different from two, a quartic obstruction which is not a
  Hochschild coboundary obstructs formality.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
* M. Gerstenhaber, *The cohomology structure of an associative ring*, Annals of Mathematics 78
  (1963), 267--288, for the pre-Lie identity and the homotopy commutativity of the cup product.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
-/

public section

universe uR uA

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 ℋ : AInfinityAlgebra R A}

/-- The pre-Lie identity behind the quadratic term: for a cochain `ψ` of degree zero,
`m{ψ}{ψ} - m{ψ{ψ}} = δψ{ψ} + ψ{δψ} - δ(ψ{ψ})`, where `δ` is the Hochschild differential of `ℋ`
and `m` its Taylor map. -/
private theorem brace_brace_sub_brace_brace_eq {ψ : ReducedTensorWords R A →ₗ[R] A}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece (ℋ.grading.shift 1))
      (ℋ.grading.shift 1).piece 0) :
    brace (ℋ.grading.shift 1) (brace (ℋ.grading.shift 1) ℋ.taylor ψ 0) ψ 0 -
        brace (ℋ.grading.shift 1) ℋ.taylor (brace (ℋ.grading.shift 1) ψ ψ 0) 0 =
      brace (ℋ.grading.shift 1) (ℋ.hochschildDifferential 0 ψ) ψ 0 +
        brace (ℋ.grading.shift 1) ψ (ℋ.hochschildDifferential 0 ψ) 1 -
        ℋ.hochschildDifferential 0 (brace (ℋ.grading.shift 1) ψ ψ 0) := by
  have e₁ := ℋ.hochschildDifferential_eq_brace_sub 0 ψ
  have e₂ := ℋ.hochschildDifferential_eq_brace_sub 0 (brace (ℋ.grading.shift 1) ψ ψ 0)
  have e₃ := brace_brace_sub_smul_brace_brace ψ
    (ℋ.taylor_isSuspension.isHomogeneous ℋ.m_degree) hψ
  rw [negOnePowCast_zero, one_smul] at e₁ e₂
  rw [mul_zero, negOnePowCast_zero, one_smul, add_zero, ← hochschildDifferential_def] at e₃
  rw [eq_sub_iff_add_eq] at e₁ e₂
  rw [sub_eq_iff_eq_add] at e₃
  rw [← e₁, brace_add_left, e₃, ← e₂]
  abel

/-- If `𝒜` agrees with the graded algebra `ℋ` on the words of length at most three, and
`m_𝒜 - m_ℋ` is the Hochschild differential of a cochain `χ` on the words of length at most four,
then the obstruction `m₄` is the Hochschild differential of `χ` restricted to the words of length
three.  Indeed, `χ` differs from this restriction by its restriction to the words of length two
and by a cochain vanishing on the words of length at most three, and neither changes the
Hochschild differential on the words of length four. -/
private theorem hochschildDifferential_comp_lengthProj_three (hℋ : ℋ.IsMinimal)
    (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) (h : ∀ z ∈ filtration R A 3, 𝒜.taylor z = ℋ.taylor z)
    {χ : ReducedTensorWords R A →ₗ[R] A} (hχ₁ : ∀ z ∈ filtration R A 1, χ z = 0)
    (hχ : ∀ z ∈ filtration R A 4, 𝒜.taylor z - ℋ.taylor z = ℋ.hochschildDifferential 0 χ z) :
    ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) =
      𝒜.obstruction ℋ ⟨4, by norm_num⟩ := by
  have hcomp₂ := hℋ.taylor_comp_lengthProj_two hm
  have hg : ∀ z ∈ filtration R A 3,
      (χ - χ ∘ₗ lengthProj R A ⟨2, two_pos⟩ - χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) z = 0 := by
    have hg₂ : ∀ z ∈ filtration R A 2, (χ - χ ∘ₗ lengthProj R A ⟨2, two_pos⟩) z = 0 :=
      fun z hz ↦ by
        rw [LinearMap.sub_apply, LinearMap.comp_apply,
          apply_lengthProj_of_mem_filtration R A (n := 1) hχ₁ hz, sub_self]
    intro z hz
    have h₃ := apply_lengthProj_of_mem_filtration R A (n := 2) hg₂ hz
    rw [LinearMap.sub_apply, LinearMap.comp_apply,
      lengthProj_lengthProj_of_ne R A (by decide), map_zero, sub_zero] at h₃
    rw [LinearMap.sub_apply, ← h₃, LinearMap.comp_apply, sub_self]
  have hδ₃ : ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) ∘ₗ
      lengthProj R A ⟨4, by norm_num⟩ =
        ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) :=
    hochschildDifferential_comp_lengthProj hcomp₂ 0 (n := 2)
      (LinearMap.ext fun z ↦ by simp only [LinearMap.comp_apply, lengthProj_lengthProj])
  have hδ₂ : ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨2, two_pos⟩) ∘ₗ
      lengthProj R A ⟨3, by norm_num⟩ =
        ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨2, two_pos⟩) :=
    hochschildDifferential_comp_lengthProj hcomp₂ 0 (n := 1)
      (LinearMap.ext fun z ↦ by simp only [LinearMap.comp_apply, lengthProj_lengthProj])
  -- Both sides are concentrated on the words of length four.
  refine LinearMap.ext fun z ↦ ?_
  rw [← hδ₃, ← obstruction_comp_lengthProj, LinearMap.comp_apply, LinearMap.comp_apply]
  have hw := lengthProj_mem_filtration R A ⟨4, by norm_num⟩ z
  have hobs : 𝒜.obstruction ℋ ⟨4, by norm_num⟩ (lengthProj R A ⟨4, by norm_num⟩ z) =
      𝒜.taylor (lengthProj R A ⟨4, by norm_num⟩ z) -
        ℋ.taylor (lengthProj R A ⟨4, by norm_num⟩ z) :=
    obstruction_apply_of_mem_filtration (n := 3) h hw
  have hsplit : χ = (χ - χ ∘ₗ lengthProj R A ⟨2, two_pos⟩ -
      χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) +
        (χ ∘ₗ lengthProj R A ⟨2, two_pos⟩ + χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩) := by
    abel
  rw [hobs, hχ _ hw]
  conv_rhs => rw [hsplit]
  rw [hochschildDifferential_add, hochschildDifferential_add,
    LinearMap.add_apply, LinearMap.add_apply,
    hℋ.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one 0 (e := 3) hg hw,
    ← hδ₂, LinearMap.comp_apply, lengthProj_lengthProj_of_ne R A (by decide), map_zero,
    zero_add, zero_add]

/-- The quartic obstruction is a coboundary for an `A∞` morphism with linear part the identity.
Here `𝒜` agrees with the graded algebra `ℋ` on the words of length at most three, and the
coboundary is that of `ψ - ½ ψ{ψ}` restricted to the words of length three, where `letter + ψ` is
the Taylor map of the morphism. -/
private theorem exists_hochschildDifferential_eq_obstruction_four_of_linearPart_eq_id
    [Invertible (2 : R)] (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0)
    (hG : 𝒜.grading = ℋ.grading) (h : ∀ z ∈ filtration R A 3, 𝒜.taylor z = ℋ.taylor z)
    (f : AInfinityHom 𝒜 ℋ) (hf : f.linearPart = LinearMap.id) :
    ∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj R A ⟨3, by norm_num⟩ = φ ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨4, by norm_num⟩ := by
  set G := ℋ.grading.shift 1 with hGdef
  set ψ := f.taylor - letter R A with hψdef
  have ht : f.taylor = letter R A + ψ := by rw [hψdef, add_sub_cancel]
  have hψ : LinearMap.IsHomogeneous ψ (gradedPiece G) G.piece 0 := by
    have hf₀ := f.isHomogeneous_taylor
    rw [hG] at hf₀
    exact hf₀.sub (isHomogeneous_letter G)
  have hψ₁ : ∀ z ∈ filtration R A 1, ψ z = 0 := apply_eq_zero_of_mem_filtration_one R A <|
    LinearMap.ext fun a ↦ by
      rw [LinearMap.comp_apply, hψdef, LinearMap.sub_apply, ← AInfinityHom.linearPart_apply, hf,
        LinearMap.id_apply, letter_ofLetter, sub_self, LinearMap.zero_apply]
  -- The morphism equation, written as for a gauge transformation: `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}`.
  have key : 𝒜.taylor = ℋ.taylor ∘ₗ coalgHom R (letter R A + ψ) - brace G ψ 𝒜.taylor 1 := by
    have h₁ := f.taylor_comp_barMap
    rw [f.barMap_eq_coalgHom, ht, LinearMap.add_comp, letter_comp_barDifferential,
      barDifferential_def, hG] at h₁
    rw [h₁, brace_def, add_sub_cancel_right]
  -- On the words of length at most four, `ψ{m_𝒜} = ψ{m_ℋ}`.
  have hb : ∀ z ∈ filtration R A 4, brace G ψ 𝒜.taylor 1 z = brace G ψ ℋ.taylor 1 z := by
    intro z hz
    have hsplit : 𝒜.taylor = ℋ.taylor + (𝒜.taylor - ℋ.taylor) := (add_sub_cancel _ _).symm
    rw [hsplit, brace_add_right, LinearMap.add_apply,
      brace_apply_eq_zero_of_mem_filtration G 1 (k := 1) (j := 3)
        (g := 𝒜.taylor - ℋ.taylor) hψ₁
        (fun w hw ↦ by rw [LinearMap.sub_apply, h w hw, sub_self]) hz, add_zero]
  -- On the words of length at most three, `δψ = 0`.
  have hδψ : ∀ z ∈ filtration R A 3, ℋ.hochschildDifferential 0 ψ z = 0 := by
    intro z hz
    have h₁ := LinearMap.congr_fun key z
    rw [LinearMap.sub_apply, LinearMap.comp_apply,
      coalgHom_letter_add_apply_of_mem_filtration (e := 1) hψ₁ hz, map_add, h z hz,
      hb z (filtration_monotone R A (by omega) hz)] at h₁
    rw [hochschildDifferential_eq_brace_sub, negOnePowCast_zero, one_smul, LinearMap.sub_apply,
      brace_def, gradedCoderiv_zero, LinearMap.comp_apply, ← hGdef]
    linear_combination (norm := module) -h₁
  -- On the words of length at most four, the quadratic part of `F` gives
  -- `2 (m_𝒜 - m_ℋ) = 2 δψ - δ(ψ{ψ})`.
  have hquad : ∀ z ∈ filtration R A 4, (2 : R) • (𝒜.taylor z - ℋ.taylor z) =
      (2 : R) • ℋ.hochschildDifferential 0 ψ z -
        ℋ.hochschildDifferential 0 (brace G ψ ψ 0) z := by
    intro z hz
    have h₁ := LinearMap.congr_fun key z
    rw [LinearMap.sub_apply, LinearMap.comp_apply, hb z hz] at h₁
    have h₂ := congrArg ℋ.taylor (two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration
      (e := 1) hψ₁ (filtration_monotone R A (by omega) hz))
    rw [map_smul, map_sub, map_sub, map_sub] at h₂
    have h₃ := LinearMap.congr_fun (brace_brace_sub_brace_brace_eq hψ) z
    rw [← hGdef] at h₃
    have e₁ : brace G (brace G ℋ.taylor ψ 0) ψ 0 z =
        ℋ.taylor (coderiv R ψ (coderiv R ψ z)) := by
      simp only [brace_def, gradedCoderiv_zero, LinearMap.comp_apply]
    have e₂ : brace G ℋ.taylor (brace G ψ ψ 0) 0 z =
        ℋ.taylor (coderiv R (ψ ∘ₗ coderiv R ψ) z) := by
      simp only [brace_def, gradedCoderiv_zero, LinearMap.comp_apply]
    rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.add_apply, e₁, e₂,
      brace_apply_eq_zero_of_mem_filtration G 0 (k := 3) (j := 1) hδψ hψ₁ hz,
      brace_apply_eq_zero_of_mem_filtration G 1 (k := 1) (j := 3) hψ₁ hδψ hz, zero_add] at h₃
    have h₄ := LinearMap.congr_fun (ℋ.hochschildDifferential_eq_brace_sub 0 ψ) z
    rw [negOnePowCast_zero, one_smul, LinearMap.sub_apply, brace_def, gradedCoderiv_zero,
      LinearMap.comp_apply, ← hGdef] at h₄
    linear_combination (norm := module) (2 : R) • h₁ + h₂ + h₃ - (2 : R) • h₄
  -- Hence `m_𝒜 - m_ℋ = δχ` there, for `χ = ψ - ½ ψ{ψ}`.
  set χ := ψ + (-⅟2 : R) • brace G ψ ψ 0 with hχdef
  have hχ : ∀ z ∈ filtration R A 4,
      𝒜.taylor z - ℋ.taylor z = ℋ.hochschildDifferential 0 χ z := by
    intro z hz
    have h₂ : (2 : R) • (𝒜.taylor z - ℋ.taylor z - ℋ.hochschildDifferential 0 χ z) = 0 := by
      rw [hχdef, hochschildDifferential_add, hochschildDifferential_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_sub, hquad z hz, smul_add, smul_smul, mul_neg,
        mul_invOf_self]
      module
    rw [← sub_eq_zero, ← one_smul R (_ - _), ← invOf_mul_self (2 : R), mul_smul, h₂, smul_zero]
  have hχ₁ : ∀ z ∈ filtration R A 1, χ z = 0 := fun z hz ↦ by
    rw [hχdef, LinearMap.add_apply, LinearMap.smul_apply, hψ₁ z hz,
      brace_apply_eq_zero_of_mem_filtration G 0 (k := 1) (j := 0) hψ₁
        (apply_eq_zero_of_mem_filtration_zero R A _) hz, smul_zero, add_zero]
  refine ⟨χ ∘ₗ lengthProj R A ⟨3, by norm_num⟩, ?_, ?_,
    hochschildDifferential_comp_lengthProj_three hℋ hm h hχ₁ hχ⟩
  · have hbr : LinearMap.IsHomogeneous (brace G ψ ψ 0) (gradedPiece G) G.piece 0 := by
      simpa only [add_zero] using isHomogeneous_brace hψ hψ
    simpa only [add_zero] using
      (hψ.add (hbr.smul _)).comp (isHomogeneous_lengthProj G ⟨3, by norm_num⟩)
  · exact LinearMap.ext fun z ↦ by simp only [LinearMap.comp_apply, lengthProj_lengthProj]

/-- **The quartic obstruction of an `A∞` structure isomorphic to a graded algebra is a Hochschild
coboundary**, when `2` is invertible.  Let `ℋ` be a graded algebra, presented as a minimal `A∞`
algebra without operations above arity two, and let `𝒜` be a minimal `A∞` structure with the
grading and the binary operation of `ℋ` and with `m₃ = 0`.  If `𝒜` is `A∞` isomorphic to `ℋ`,
then its obstruction `m₄` is the Hochschild differential of a degree-zero cochain concentrated on
the words of length three: its class in `HH^{4, -2}(H, H)` vanishes. -/
theorem IsMinimal.exists_hochschildDifferential_eq_obstruction_four_of_isIso
    [Invertible (2 : R)] (h𝒜 : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) (h₃ : 𝒜.m 3 = 0)
    {f : AInfinityHom 𝒜 ℋ} (hf : f.IsIso) :
    ∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj R A ⟨3, by norm_num⟩ = φ ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨4, by norm_num⟩ := by
  -- The linear part `θ` of `f` is a graded algebra automorphism of `ℋ`, and so is its inverse.
  let θ := LinearEquiv.ofBijective f.linearPart hf.linearPart_bijective
  have hθ : LinearMap.IsHomogeneous θ.toLinearMap ℋ.grading.piece ℋ.grading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    rw [add_zero, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply]
    exact f.linearPart_mem (by rwa [hG])
  have hθm : ∀ a b, θ (ℋ.m 2 ![a, b]) = ℋ.m 2 ![θ a, θ b] := fun a b ↦ by
    have hab := f.linearPart_m_two_sub_mem_boundaries (h𝒜.mem_cycles a) (h𝒜.mem_cycles b)
    rwa [(isMinimal_iff_boundaries_eq_bot ℋ).1 hℋ, Submodule.mem_bot, sub_eq_zero, h₂] at hab
  let s : AInfinityStrictHom ℋ ℋ :=
    { toLinearMap := θ.symm.toLinearMap
      map_mem' := fun ha ↦ by simpa only [add_zero] using hθ.linearEquiv_symm.map_mem ha
      map_m' := fun n ↦ by
        ext x
        rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
        match n with
        | 0 => simp
        | 1 => simp [hℋ.m_one]
        | 2 =>
          obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] :=
            ⟨x 0, x 1, funext fun i ↦ by fin_cases i <;> rfl⟩
          have hx : (fun i ↦ θ.symm.toLinearMap (![a, b] i)) = ![θ.symm a, θ.symm b] :=
            funext fun i ↦ by fin_cases i <;> rfl
          rw [hx]
          apply θ.injective
          rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hθm,
            LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        | n + 3 => simp [hm (n + 3) (by omega)] }
  have hid : (s.toAInfinityHom.comp f).linearPart = LinearMap.id := by
    rw [AInfinityHom.linearPart_comp, AInfinityStrictHom.linearPart_toAInfinityHom]
    exact LinearMap.ext fun a ↦ θ.symm_apply_apply a
  -- On the words of length at most three, `𝒜` agrees with `ℋ`.
  have h : ∀ z ∈ filtration R A 3, 𝒜.taylor z = ℋ.taylor z := fun z hz ↦
    taylor_apply_eq_of_forall_m_eq hG (n := 3) (fun k hk hk₃ ↦ by
      obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      · exact MultilinearMap.ext fun x ↦ by rw [h𝒜.m_one, hℋ.m_one]
      · exact h₂
      · rw [h₃, hm 3 le_rfl]) hz
  exact exists_hochschildDifferential_eq_obstruction_four_of_linearPart_eq_id hℋ hm hG h _ hid

/-- **A quartic obstruction which is not a coboundary obstructs formality.**  Over a field of
characteristic different from two, let `ℋ` be a graded algebra, presented as a minimal `A∞`
algebra without operations above arity two, and let `𝒜` be a minimal `A∞` structure with the
grading and the binary operation of `ℋ` and with `m₃ = 0`.  If the obstruction `m₄` of `𝒜` is not
the Hochschild differential of a degree-zero cochain, then `𝒜` is not formal. -/
theorem IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four
    {K : Type*} [Field K] [Module K A] {𝒜 ℋ : AInfinityAlgebra K A} (h2 : (2 : K) ≠ 0)
    (h𝒜 : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) (h₃ : 𝒜.m 3 = 0)
    (hobs : ¬∃ φ : ReducedTensorWords K A →ₗ[K] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨4, by norm_num⟩) :
    ¬𝒜.IsFormal := by
  let _ : Invertible (2 : K) := invertibleOfNonzero h2
  rw [h𝒜.isFormal_iff_exists_isIso hℋ hm hG h₂]
  rintro ⟨f, hf⟩
  obtain ⟨φ, hφ, -, hφo⟩ :=
    h𝒜.exists_hochschildDifferential_eq_obstruction_four_of_isIso hℋ hm hG h₂ h₃ hf
  exact hobs ⟨φ, hφ, hφo⟩

end AInfinityAlgebra

end TauCeti
