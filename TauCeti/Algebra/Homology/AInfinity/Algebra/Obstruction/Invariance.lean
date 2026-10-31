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
# Invariance of the first obstruction under `A∞` isomorphisms

Let `ℋ` be a graded algebra, presented as a minimal `A∞` algebra without operations above arity
two, and let `𝒜` be a minimal `A∞` structure on the same graded module with the binary operation
of `ℋ` and `m₃ = ⋯ = mₙ₊₁ = 0`.  Its first obstruction to formality is the operation `mₙ₊₂`, a
Hochschild cocycle of `ℋ` (`TauCeti.AInfinityAlgebra.hochschildDifferential_obstruction`) whose
class lies in `HH^{n+2, -n}(H, H)`.  When it is a Hochschild coboundary, the gauge transformation by
a suitable primitive kills it
(`TauCeti.AInfinityAlgebra.IsMinimal.taylor_gauge_apply_eq_of_hochschildDifferential`).  This file
proves the converse: if `𝒜` is `A∞` isomorphic to `ℋ`, then `mₙ₊₂` is a Hochschild coboundary.
For the quartic obstruction this needs only that `2` is invertible
(`IsMinimal.exists_hochschildDifferential_eq_obstruction_four_of_isIso`); in every arity it holds
over a `ℚ`-algebra (`IsMinimal.exists_hochschildDifferential_eq_obstruction_of_isIso`).
Consequently, a first obstruction which is not a coboundary makes `𝒜` non-formal.

In both cases the linear part of the isomorphism is first normalized to the identity: it is a
graded algebra automorphism of `ℋ`, and composing with its inverse is harmless
(`IsMinimal.exists_linearPart_eq_id_of_isIso`).  The Taylor map of the normalized morphism is then
`letter + ψ`, and the morphism equation says that `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}` for the coalgebra map
`F` with these Taylor components, as for a gauge transformation.

For the quartic obstruction, on the words of length at most three this gives `δψ = 0`.  On the
words of length four the quadratic part of `F` contributes the term `m_ℋ{ψ, ψ}`, and the
second-order expansion of `F`
(`TauCeti.ReducedTensorWords.two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration`) together
with the pre-Lie identity of the brace shows that twice this term is the coboundary `-δ(ψ{ψ})`.
Hence `m₄ = δ(ψ - ½ ψ{ψ})` on the words of length four.  This is the classical fact that twice
the cup square of a Hochschild cocycle of odd total degree is a coboundary; the argument divides
by `2`.

In higher arities the products of the components of `ψ` are not controlled directly.  Instead the
morphism is improved one arity at a time.  If `ψ` vanishes on the words of length at most `e`,
with `e + 1 ≤ n`, then its component `ψₑ₊₁` on the words of length `e + 1` is a Hochschild
cocycle, since there `m_𝒜 - m_ℋ = δψ` vanishes.  Over a `ℚ`-algebra a cocycle integrates to the
`A∞` automorphism `exp(-ψₑ₊₁)` of `ℋ` (`TauCeti.AInfinityAlgebra.expHom`), and composing with it
makes `ψ` vanish on the words of length at most `e + 1`.  Once `ψ` vanishes on the words of length
at most `n`, the morphism equation involves `ψ` only once on the words of length at most `n + 2`,
and gives `mₙ₊₂ = δψₙ₊₁` there.  The exponential is where division by factorials enters.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.exists_linearPart_eq_id_of_isIso`: an `A∞` isomorphism from
  `𝒜` to the graded algebra `ℋ` can be normalized to have linear part the identity.
* `TauCeti.AInfinityAlgebra.IsMinimal.exists_hochschildDifferential_eq_obstruction_four_of_isIso`:
  when `2` is invertible, the quartic obstruction of a minimal `A∞` structure with `m₃ = 0` which
  is `A∞` isomorphic to the graded algebra `ℋ` is a Hochschild coboundary.
* `IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four`:
  when `2` is invertible, a quartic obstruction which is not a Hochschild coboundary obstructs
  formality.
* `TauCeti.AInfinityAlgebra.IsMinimal.exists_hochschildDifferential_eq_obstruction_of_isIso`:
  over a `ℚ`-algebra, the first obstruction `mₙ₊₂` of a minimal `A∞` structure with
  `m₃ = ⋯ = mₙ₊₁ = 0` which is `A∞` isomorphic to the graded algebra `ℋ` is a Hochschild
  coboundary.
* `IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction`: over a
  `ℚ`-algebra, a first obstruction which is not a Hochschild coboundary obstructs formality.

## References

* T. Kadeishvili, *The structure of the `A(∞)`-algebra, and the Hochschild and Harrison
  cohomologies*, Trudy Tbiliss. Mat. Inst. 91 (1988), 19--27, for the obstruction method.
* M. Gerstenhaber, *The cohomology structure of an associative ring*, Annals of Mathematics 78
  (1963), 267--288, for the pre-Lie identity and the homotopy commutativity of the cup product.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* E. Getzler, *Lie theory for nilpotent L-infinity algebras*, Annals of Mathematics 170 (2009),
  271--301, for the exponential gauge action over a `ℚ`-algebra.
-/

public section

universe uR uA

namespace TauCeti

namespace AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]
  {𝒜 ℋ : AInfinityAlgebra R A}

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

/-- If `ψ` vanishes on the words of length at most `e` and `𝒜` agrees with `ℋ` on the words of
length at most `k`, then `ψ{m_𝒜}` agrees with `ψ{m_ℋ}` on the words of length at most `e + k`. -/
private theorem brace_taylor_apply_eq_of_mem_filtration {ψ : ReducedTensorWords R A →ₗ[R] A}
    {e k : ℕ} (hψ : ∀ z ∈ filtration R A e, ψ z = 0)
    (h : ∀ z ∈ filtration R A k, 𝒜.taylor z = ℋ.taylor z) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A (e + k)) :
    brace (ℋ.grading.shift 1) ψ 𝒜.taylor 1 z = brace (ℋ.grading.shift 1) ψ ℋ.taylor 1 z := by
  have hsplit : 𝒜.taylor = ℋ.taylor + (𝒜.taylor - ℋ.taylor) := (add_sub_cancel _ _).symm
  rw [hsplit, brace_add_right, LinearMap.add_apply,
    brace_apply_eq_zero_of_mem_filtration _ 1 (k := e) (j := k) (g := 𝒜.taylor - ℋ.taylor) hψ
      (fun w hw ↦ by rw [LinearMap.sub_apply, h w hw, sub_self]) hz, add_zero]

/-- **The morphism equation to first order.**  Let `f : 𝒜 ⟶ ℋ` be an `A∞` morphism between
structures with the same grading whose Taylor map is `letter` on the words of length at most `e`,
and let `𝒜` agree with `ℋ` on the words of length at most `j`.  Then on the words of length at most
`k`, for `k ≤ 2 e + 1` and `k ≤ e + j`, the difference `m_𝒜 - m_ℋ` is the Hochschild differential
of `ψ = f.taylor - letter`: there the morphism equation `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}` involves `ψ`
only once. -/
private theorem taylor_sub_taylor_apply_eq_hochschildDifferential (hG : 𝒜.grading = ℋ.grading)
    (f : AInfinityHom 𝒜 ℋ) {e j k : ℕ} (hk : k ≤ 2 * e + 1) (hkj : k ≤ e + j)
    (hf : ∀ z ∈ filtration R A e, f.taylor z = letter R A z)
    (h : ∀ z ∈ filtration R A j, 𝒜.taylor z = ℋ.taylor z) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A k) :
    𝒜.taylor z - ℋ.taylor z = ℋ.hochschildDifferential 0 (f.taylor - letter R A) z := by
  have hψ : ∀ w ∈ filtration R A e, (f.taylor - letter R A) w = 0 := fun w hw ↦ by
    rw [LinearMap.sub_apply, hf w hw, sub_self]
  have key := LinearMap.congr_fun
    (f.taylor_eq_taylor_comp_coalgHom_sub_brace hG (add_sub_cancel (letter R A) f.taylor).symm) z
  rw [LinearMap.sub_apply, LinearMap.comp_apply,
    coalgHom_letter_add_apply_of_mem_filtration hψ (filtration_monotone R A hk hz), map_add,
    brace_taylor_apply_eq_of_mem_filtration hψ h (filtration_monotone R A hkj hz)] at key
  rw [hochschildDifferential_zero_apply, key]
  abel

/-- Where `𝒜` agrees with `ℋ`, the Hochschild differential of `f.taylor - letter` vanishes, for an
`A∞` morphism `f : 𝒜 ⟶ ℋ` as in `taylor_sub_taylor_apply_eq_hochschildDifferential`. -/
private theorem hochschildDifferential_taylor_sub_letter_apply_eq_zero
    (hG : 𝒜.grading = ℋ.grading) (f : AInfinityHom 𝒜 ℋ) {e k : ℕ} (hk : k ≤ 2 * e + 1)
    (hf : ∀ z ∈ filtration R A e, f.taylor z = letter R A z)
    (h : ∀ z ∈ filtration R A k, 𝒜.taylor z = ℋ.taylor z) {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A k) :
    ℋ.hochschildDifferential 0 (f.taylor - letter R A) z = 0 := by
  rw [← taylor_sub_taylor_apply_eq_hochschildDifferential hG f hk (by omega) hf h hz, h z hz,
    sub_self]

/-- The Taylor map of an `A∞` morphism between structures with the same grading differs from
`letter` by a cochain of degree zero. -/
private theorem isHomogeneous_taylor_sub_letter (hG : 𝒜.grading = ℋ.grading)
    (f : AInfinityHom 𝒜 ℋ) :
    LinearMap.IsHomogeneous (f.taylor - letter R A) (gradedPiece (ℋ.grading.shift 1))
      (ℋ.grading.shift 1).piece 0 := by
  have hf₀ := f.isHomogeneous_taylor
  rw [hG] at hf₀
  exact hf₀.sub (isHomogeneous_letter _)

/-- The quadratic term of the morphism equation.  Let `ψ` be a cochain of degree zero vanishing
on letters, with `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}` for `F` the coalgebra map with Taylor components
`letter + ψ`.  If `ψ{m_𝒜}` agrees with `ψ{m_ℋ}` on the words of length at most four and `δψ`
vanishes on the words of length at most three, then `2 (m_𝒜 - m_ℋ) = 2 δψ - δ(ψ{ψ})` on the
words of length at most four. -/
private theorem two_smul_taylor_sub_taylor_apply_of_mem_filtration_four
    {ψ : ReducedTensorWords R A →ₗ[R] A}
    (hψ : LinearMap.IsHomogeneous ψ (gradedPiece (ℋ.grading.shift 1))
      (ℋ.grading.shift 1).piece 0)
    (hψ₁ : ∀ z ∈ filtration R A 1, ψ z = 0)
    (key : 𝒜.taylor = ℋ.taylor ∘ₗ coalgHom R (letter R A + ψ) -
      brace (ℋ.grading.shift 1) ψ 𝒜.taylor 1)
    (hb : ∀ z ∈ filtration R A 4,
      brace (ℋ.grading.shift 1) ψ 𝒜.taylor 1 z = brace (ℋ.grading.shift 1) ψ ℋ.taylor 1 z)
    (hδψ : ∀ z ∈ filtration R A 3, ℋ.hochschildDifferential 0 ψ z = 0)
    {z : ReducedTensorWords R A} (hz : z ∈ filtration R A 4) :
    (2 : R) • (𝒜.taylor z - ℋ.taylor z) =
      (2 : R) • ℋ.hochschildDifferential 0 ψ z -
        ℋ.hochschildDifferential 0 (brace (ℋ.grading.shift 1) ψ ψ 0) z := by
  have h₁ := LinearMap.congr_fun key z
  rw [LinearMap.sub_apply, LinearMap.comp_apply, hb z hz] at h₁
  have h₂ := congrArg ℋ.taylor (two_smul_coalgHom_letter_add_apply_sub_of_mem_filtration
    (e := 1) hψ₁ (filtration_monotone R A (by omega) hz))
  rw [map_smul, map_sub, map_sub, map_sub] at h₂
  have e : brace (ℋ.grading.shift 1) ℋ.taylor (brace (ℋ.grading.shift 1) ψ ψ 0) 0 z =
      ℋ.taylor (coderiv R (ψ ∘ₗ coderiv R ψ) z) := by
    rw [brace_zero_apply, brace_def, gradedCoderiv_zero]
  have h₃ := LinearMap.congr_fun (ℋ.brace_brace_sub_brace_brace_eq_hochschildDifferential hψ) z
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.add_apply, e,
    brace_apply_eq_zero_of_mem_filtration (ℋ.grading.shift 1) 0 (k := 3) (j := 1) hδψ hψ₁ hz,
    brace_apply_eq_zero_of_mem_filtration (ℋ.grading.shift 1) 1 (k := 1) (j := 3) hψ₁ hδψ hz,
    zero_add, brace_zero_apply, brace_zero_apply] at h₃
  linear_combination (norm := module)
    (2 : R) • h₁ + h₂ + h₃ - (2 : R) • ℋ.hochschildDifferential_zero_apply ψ z

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
  set G := ℋ.grading.shift 1
  set ψ := f.taylor - letter R A with hψdef
  have ht : f.taylor = letter R A + ψ := by rw [hψdef, add_sub_cancel]
  have hψ : LinearMap.IsHomogeneous ψ (gradedPiece G) G.piece 0 :=
    isHomogeneous_taylor_sub_letter hG f
  have hψ₁ : ∀ z ∈ filtration R A 1, ψ z = 0 := apply_eq_zero_of_mem_filtration_one R A <|
    LinearMap.ext fun a ↦ by
      rw [LinearMap.comp_apply, hψdef, LinearMap.sub_apply, ← AInfinityHom.linearPart_apply, hf,
        LinearMap.id_apply, letter_ofLetter, sub_self, LinearMap.zero_apply]
  -- The morphism equation, written as for a gauge transformation: `m_𝒜 = m_ℋ ∘ F - ψ{m_𝒜}`.
  have key : 𝒜.taylor = ℋ.taylor ∘ₗ coalgHom R (letter R A + ψ) - brace G ψ 𝒜.taylor 1 :=
    f.taylor_eq_taylor_comp_coalgHom_sub_brace hG ht
  -- On the words of length at most four, `ψ{m_𝒜} = ψ{m_ℋ}`.
  have hb : ∀ z ∈ filtration R A 4, brace G ψ 𝒜.taylor 1 z = brace G ψ ℋ.taylor 1 z :=
    fun z hz ↦ brace_taylor_apply_eq_of_mem_filtration (k := 3) hψ₁ h hz
  -- On the words of length at most three, `δψ = 0`.
  have hδψ : ∀ z ∈ filtration R A 3, ℋ.hochschildDifferential 0 ψ z = 0 := fun z hz ↦ by
    have hf₁ : ∀ w ∈ filtration R A 1, f.taylor w = letter R A w := fun w hw ↦ by
      simpa only [hψdef, LinearMap.sub_apply, sub_eq_zero] using hψ₁ w hw
    exact hochschildDifferential_taylor_sub_letter_apply_eq_zero hG f (e := 1) (by norm_num) hf₁ h
      hz
  -- On the words of length at most four, the quadratic part of `F` gives
  -- `2 (m_𝒜 - m_ℋ) = 2 δψ - δ(ψ{ψ})`.
  have hquad : ∀ z ∈ filtration R A 4, (2 : R) • (𝒜.taylor z - ℋ.taylor z) =
      (2 : R) • ℋ.hochschildDifferential 0 ψ z -
        ℋ.hochschildDifferential 0 (brace G ψ ψ 0) z := fun z hz ↦
    two_smul_taylor_sub_taylor_apply_of_mem_filtration_four hψ hψ₁ key hb hδψ hz
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

/-- **Normalizing an isomorphism to a graded algebra.**  Let `ℋ` be a graded algebra, presented as
a minimal `A∞` algebra without operations above arity two, and let `𝒜` be a minimal `A∞` structure
with the grading and the binary operation of `ℋ`.  If `𝒜` is `A∞` isomorphic to `ℋ`, then there is
an `A∞` morphism `𝒜 ⟶ ℋ` whose linear part is the identity: the linear part of an isomorphism is a
graded algebra automorphism of `ℋ`, and composing with its inverse, a strict `A∞` automorphism of
`ℋ`, normalizes it. -/
theorem IsMinimal.exists_linearPart_eq_id_of_isIso (h𝒜 : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal)
    (hm : ∀ n, 3 ≤ n → ℋ.m n = 0) (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2)
    {f : AInfinityHom 𝒜 ℋ} (hf : f.IsIso) :
    ∃ g : AInfinityHom 𝒜 ℋ, g.linearPart = LinearMap.id := by
  -- The linear part `θ` of `f` is a graded algebra automorphism of `ℋ`, and so is its inverse.
  let θ := LinearEquiv.ofBijective f.linearPart hf.linearPart_bijective
  have hθ : LinearMap.IsHomogeneous θ.toLinearMap ℋ.grading.piece ℋ.grading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro p a ha
    rw [add_zero, LinearEquiv.coe_coe, LinearEquiv.ofBijective_apply]
    exact f.linearPart_mem (by rwa [hG])
  have hθm : ∀ a b, θ (ℋ.m 2 ![a, b]) = ℋ.m 2 ![θ a, θ b] := fun a b ↦ by
    have hab := f.linearPart_m_two h𝒜 hℋ a b
    rwa [h₂] at hab
  let s : AInfinityStrictHom ℋ ℋ := .ofMapMTwo hℋ hℋ hm hm θ.symm.toLinearMap
    (by simpa only [neg_zero] using hθ.linearEquiv_symm) fun a b ↦ θ.injective <| by
      rw [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hθm, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
  refine ⟨s.toAInfinityHom.comp f, ?_⟩
  rw [AInfinityHom.linearPart_comp, AInfinityStrictHom.linearPart_toAInfinityHom]
  exact LinearMap.ext fun a ↦ by
    simp only [s, LinearMap.comp_apply, AInfinityStrictHom.coe_toLinearMap,
      AInfinityStrictHom.coe_ofMapMTwo, LinearEquiv.coe_coe, LinearMap.id_apply]
    exact θ.symm_apply_apply a

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
  obtain ⟨g, hg⟩ := h𝒜.exists_linearPart_eq_id_of_isIso hℋ hm hG h₂ hf
  -- On the words of length at most three, `𝒜` agrees with `ℋ`.
  have h : ∀ z ∈ filtration R A 3, 𝒜.taylor z = ℋ.taylor z := fun z hz ↦
    taylor_apply_eq_of_forall_m_eq hG (n := 3) (fun k hk hk₃ ↦ by
      obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      · exact MultilinearMap.ext fun x ↦ by rw [h𝒜.m_one, hℋ.m_one]
      · exact h₂
      · rw [h₃, hm 3 le_rfl]) hz
  exact exists_hochschildDifferential_eq_obstruction_four_of_linearPart_eq_id hℋ hm hG h g hg

/-- **A quartic obstruction which is not a coboundary obstructs formality.**  Assume that `2` is
invertible.  Let `ℋ` be a graded algebra, presented as a minimal `A∞` algebra without operations
above arity two, and let `𝒜` be a minimal `A∞` structure with the grading and the binary operation
of `ℋ` and with `m₃ = 0`.  If the obstruction `m₄` of `𝒜` is not the Hochschild differential of a
degree-zero cochain, then `𝒜` is not formal.  Over a field of characteristic different from two,
the instance is `invertibleOfNonzero`. -/
theorem IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction_four
    [Invertible (2 : R)] (h𝒜 : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal) (hm : ∀ n, 3 ≤ n → ℋ.m n = 0)
    (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) (h₃ : 𝒜.m 3 = 0)
    (hobs : ¬∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨4, by norm_num⟩) :
    ¬𝒜.IsFormal := by
  rw [h𝒜.isFormal_iff_exists_isIso hℋ hm hG h₂]
  rintro ⟨f, hf⟩
  obtain ⟨φ, hφ, -, hφo⟩ :=
    h𝒜.exists_hochschildDifferential_eq_obstruction_four_of_isIso hℋ hm hG h₂ h₃ hf
  exact hobs ⟨φ, hφ, hφo⟩

/-! ### The first obstruction in every arity -/

/-- Let `𝒜` agree with the graded algebra `ℋ` on the words of length at most `n + 1`, and let `χ`
be a cochain vanishing on the words of length at most `n` whose Hochschild differential is
`m_𝒜 - m_ℋ` on the words of length at most `n + 2`.  Then the obstruction `mₙ₊₂` is the
Hochschild differential of `χ` restricted to the words of length `n + 1`.  Indeed `χ` differs
from this restriction by a cochain vanishing on the words of length at most `n + 1`, whose
Hochschild differential vanishes on the words of length at most `n + 2`. -/
private theorem hochschildDifferential_comp_lengthProj_eq_obstruction (hℋ : ℋ.IsMinimal)
    (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) {n : ℕ}
    (h : ∀ z ∈ filtration R A (n + 1), 𝒜.taylor z = ℋ.taylor z)
    {χ : ReducedTensorWords R A →ₗ[R] A} (hχ₀ : ∀ z ∈ filtration R A n, χ z = 0)
    (hχ : ∀ z ∈ filtration R A (n + 2),
      𝒜.taylor z - ℋ.taylor z = ℋ.hochschildDifferential 0 χ z) :
    ℋ.hochschildDifferential 0 (χ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩) =
      𝒜.obstruction ℋ ⟨n + 2, by omega⟩ := by
  set φ := χ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩
  have hφ : φ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩ = φ :=
    LinearMap.ext fun z ↦ by simp only [φ, LinearMap.comp_apply, lengthProj_lengthProj]
  have hd : ∀ z ∈ filtration R A (n + 1), (χ - φ) z = 0 := fun z hz ↦ by
    rw [LinearMap.sub_apply, LinearMap.comp_apply, apply_lengthProj_of_mem_filtration R A hχ₀ hz,
      sub_self]
  -- Both sides are concentrated on the words of length `n + 2`.
  refine LinearMap.ext fun z ↦ ?_
  have hw := lengthProj_mem_filtration R A ⟨n + 2, by omega⟩ z
  have hobs : 𝒜.obstruction ℋ ⟨n + 2, by omega⟩ (lengthProj R A ⟨n + 2, by omega⟩ z) =
      𝒜.taylor (lengthProj R A ⟨n + 2, by omega⟩ z) -
        ℋ.taylor (lengthProj R A ⟨n + 2, by omega⟩ z) :=
    obstruction_apply_of_mem_filtration h hw
  have hsplit := hχ _ hw
  rw [← sub_add_cancel χ φ, hochschildDifferential_add, LinearMap.add_apply,
    hℋ.hochschildDifferential_apply_eq_zero_of_mem_filtration_add_one 0 hd hw, zero_add] at hsplit
  rw [← hochschildDifferential_comp_lengthProj (hℋ.taylor_comp_lengthProj_two hm) 0 hφ,
    ← obstruction_comp_lengthProj, LinearMap.comp_apply, LinearMap.comp_apply, hobs, hsplit]

section Rat

variable [Algebra ℚ R]

/-- **Raising the order of a morphism to a graded algebra.**  Over a `ℚ`-algebra, let
`f : 𝒜 ⟶ ℋ` be an `A∞` morphism to the graded algebra `ℋ` whose Taylor map is `letter` on the
words of length at most `e`, for some `e ≥ 1`, and let `𝒜` agree with `ℋ` on the words of length
at most `e + 2`.  The component `ψₑ₊₁` of `f.taylor - letter` on the words of length `e + 1` is a
Hochschild cocycle, and composing `f` with the exponential of `-ψₑ₊₁` gives an `A∞` morphism whose
Taylor map is `letter` on the words of length at most `e + 1`. -/
private theorem exists_taylor_apply_eq_letter_succ (hℋ : ℋ.IsMinimal)
    (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) (hG : 𝒜.grading = ℋ.grading) {e : ℕ} (he : 1 ≤ e)
    (h : ∀ z ∈ filtration R A (e + 2), 𝒜.taylor z = ℋ.taylor z) (f : AInfinityHom 𝒜 ℋ)
    (hf : ∀ z ∈ filtration R A e, f.taylor z = letter R A z) :
    ∃ g : AInfinityHom 𝒜 ℋ, ∀ z ∈ filtration R A (e + 1), g.taylor z = letter R A z := by
  set G := ℋ.grading.shift 1
  set ψ := f.taylor - letter R A with hψdef
  have hψ : LinearMap.IsHomogeneous ψ (gradedPiece G) G.piece 0 :=
    isHomogeneous_taylor_sub_letter hG f
  have hψe : ∀ z ∈ filtration R A e, ψ z = 0 := fun z hz ↦ by
    rw [hψdef, LinearMap.sub_apply, hf z hz, sub_self]
  -- On the words of length at most `e + 2`, `δψ = m_𝒜 - m_ℋ = 0`.
  have hδψ : ∀ z ∈ filtration R A (e + 2), ℋ.hochschildDifferential 0 ψ z = 0 := fun z hz ↦
    hochschildDifferential_taylor_sub_letter_apply_eq_zero hG f (by omega) hf h hz
  -- The component `φ₀` of `ψ` on the words of length `e + 1`.
  set φ₀ := ψ ∘ₗ lengthProj R A ⟨e + 1, e.succ_pos⟩ with hφ₀def
  have hφ₀e : ∀ z ∈ filtration R A e, φ₀ z = 0 := fun z hz ↦ by
    rw [hφ₀def, LinearMap.comp_apply,
      lengthProj_apply_eq_zero_of_mem_filtration R A (n := ⟨e + 1, e.succ_pos⟩) e.lt_succ_self hz,
      map_zero]
  have hψφ₀ : ∀ z ∈ filtration R A (e + 1), (ψ - φ₀) z = 0 := fun z hz ↦ by
    rw [LinearMap.sub_apply, hφ₀def, LinearMap.comp_apply,
      apply_lengthProj_of_mem_filtration R A hψe hz, sub_self]
  -- `φ₀` is a Hochschild cocycle: this is the obstruction lemma for `ℋ` relative to itself, whose
  -- obstruction vanishes.
  have hδφ₀ : ℋ.hochschildDifferential 0 φ₀ = 0 := by
    rw [hφ₀def, hochschildDifferential_comp_lengthProj_eq_obstruction (𝒜 := ℋ) hℋ hm
      (fun _ _ ↦ rfl) hψe fun z hz ↦ by rw [sub_self, hδψ z hz], obstruction_def, sub_self,
      LinearMap.zero_comp]
  -- The exponential of `χ = -φ₀` is an `A∞` automorphism of `ℋ`.
  set χ := (-1 : R) • φ₀ with hχdef
  have hχ : LinearMap.IsHomogeneous χ (gradedPiece G) G.piece 0 := by
    simpa only [add_zero] using (hψ.comp (isHomogeneous_lengthProj G _)).smul (-1 : R)
  have hχe : ∀ z ∈ filtration R A e, χ z = 0 := fun z hz ↦ by
    rw [hχdef, LinearMap.smul_apply, hφ₀e z hz, smul_zero]
  have hχ₁ : χ ∘ₗ ofLetter R A = 0 := LinearMap.ext fun a ↦
    hχe _ (filtration_monotone R A he (ofLetter_mem_filtration R A a))
  have hδχ : ℋ.hochschildDifferential 0 χ = 0 := by
    rw [hχdef, hochschildDifferential_smul, hδφ₀, smul_zero]
  refine ⟨(ℋ.expHom hχ hχ₁ hδχ).comp f, fun z hz ↦ ?_⟩
  -- On the words of length at most `e + 1`, `f` is `id + coderiv ψ` and the exponential is
  -- `id + coderiv χ`, so the composite has Taylor map `letter + ψ + χ = letter`.
  have hFz : f.barMap z = z + coderiv R ψ z := by
    rw [f.barMap_eq_coalgHom, (add_sub_cancel (letter R A) f.taylor).symm,
      coalgHom_letter_add_apply_of_mem_filtration hψe (filtration_monotone R A (by omega) hz)]
  have hw : z + coderiv R ψ z ∈ filtration R A (2 * e) :=
    filtration_monotone R A (by omega) (add_mem hz (coderiv_mem_filtration R ψ hz))
  have hD : coderiv R ψ z ∈ filtration R A e :=
    filtration_monotone R A he (coderiv_filtration_add_le R ψ hψe 1 ⟨z, by rwa [add_comm], rfl⟩)
  have hφz : φ₀ z = ψ z := by
    have h₀ := hψφ₀ z hz
    rwa [LinearMap.sub_apply, sub_eq_zero, eq_comm] at h₀
  simp only [AInfinityHom.taylor_def, AInfinityHom.barMap_comp, barMap_expHom,
    LinearMap.comp_apply, hFz]
  rw [expCoderiv_apply_of_mem_filtration he hχe hw]
  simp only [map_add, letter_coderiv_apply, hχdef, LinearMap.smul_apply, hφ₀e _ hD, hφz]
  module

/-- The first obstruction is a coboundary for an `A∞` morphism with linear part the identity, over
a `ℚ`-algebra.  The coboundary is that of a cochain concentrated on the words of length `n + 1`. -/
private theorem exists_hochschildDifferential_eq_obstruction_of_linearPart_eq_id
    (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) (hG : 𝒜.grading = ℋ.grading) {n : ℕ}
    (hn : 1 ≤ n) (h : ∀ z ∈ filtration R A (n + 1), 𝒜.taylor z = ℋ.taylor z)
    (f : AInfinityHom 𝒜 ℋ) (hf : f.linearPart = LinearMap.id) :
    ∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩ = φ ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨n + 2, by omega⟩ := by
  -- By induction on `k`, starting from a morphism whose Taylor map is `letter` on the words of
  -- length at most `n - k`, raised one length at a time by `exists_taylor_apply_eq_letter_succ`.
  suffices H : ∀ k e, 1 ≤ e → e + k = n → ∀ g : AInfinityHom 𝒜 ℋ,
      (∀ z ∈ filtration R A e, g.taylor z = letter R A z) →
      ∃ φ : ReducedTensorWords R A →ₗ[R] A,
        LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
          (ℋ.grading.shift 1).piece 0 ∧
        φ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩ = φ ∧
        ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨n + 2, by omega⟩ by
    have h₁ : (f.taylor - letter R A) ∘ₗ ofLetter R A = 0 := LinearMap.ext fun a ↦ by
      rw [LinearMap.comp_apply, LinearMap.sub_apply, ← AInfinityHom.linearPart_apply, hf,
        LinearMap.id_apply, letter_ofLetter, sub_self, LinearMap.zero_apply]
    refine H (n - 1) 1 le_rfl (by omega) f fun z hz ↦ ?_
    have hz₁ := apply_eq_zero_of_mem_filtration_one R A h₁ z hz
    rwa [LinearMap.sub_apply, sub_eq_zero] at hz₁
  intro k
  induction k with
  | zero =>
      -- Here `f.taylor - letter` vanishes on the words of length at most `n`, so its Hochschild
      -- differential is `m_𝒜 - m_ℋ` on the words of length at most `n + 2`.
      intro e he hek g hg
      obtain rfl : e = n := by omega
      set ψ := g.taylor - letter R A with hψdef
      have hψ : LinearMap.IsHomogeneous ψ (gradedPiece (ℋ.grading.shift 1))
          (ℋ.grading.shift 1).piece 0 := isHomogeneous_taylor_sub_letter hG g
      have hψe : ∀ z ∈ filtration R A e, ψ z = 0 := fun z hz ↦ by
        rw [hψdef, LinearMap.sub_apply, hg z hz, sub_self]
      refine ⟨ψ ∘ₗ lengthProj R A ⟨e + 1, e.succ_pos⟩, ?_, ?_,
        hochschildDifferential_comp_lengthProj_eq_obstruction hℋ hm h hψe fun z hz ↦ ?_⟩
      · simpa only [add_zero] using hψ.comp (isHomogeneous_lengthProj _ _)
      · exact LinearMap.ext fun z ↦ by simp only [LinearMap.comp_apply, lengthProj_lengthProj]
      · rw [hψdef]
        exact taylor_sub_taylor_apply_eq_hochschildDifferential hG g (by omega) (by omega) hg h hz
  | succ k ih =>
      intro e he hek g hg
      obtain ⟨g', hg'⟩ := exists_taylor_apply_eq_letter_succ hℋ hm hG he
        (fun z hz ↦ h z (filtration_monotone R A (by omega) hz)) g hg
      exact ih (e + 1) (by omega) (by omega) g' hg'

/-- **The first obstruction of an `A∞` structure isomorphic to a graded algebra is a Hochschild
coboundary**, over a `ℚ`-algebra.  Let `ℋ` be a graded algebra, presented as a minimal `A∞`
algebra without operations above arity two, and let `𝒜` be a minimal `A∞` structure with the
grading and the binary operation of `ℋ` and with `m₃ = ⋯ = mₙ₊₁ = 0`.  If `𝒜` is `A∞` isomorphic
to `ℋ`, then its obstruction `mₙ₊₂` is the Hochschild differential of a degree-zero cochain
concentrated on the words of length `n + 1`: its class in `HH^{n+2, -n}(H, H)` vanishes. -/
theorem IsMinimal.exists_hochschildDifferential_eq_obstruction_of_isIso (h𝒜 : 𝒜.IsMinimal)
    (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0) (hG : 𝒜.grading = ℋ.grading)
    (h₂ : 𝒜.m 2 = ℋ.m 2) {n : ℕ} (hlow : ∀ k, 3 ≤ k → k ≤ n + 1 → 𝒜.m k = 0)
    {f : AInfinityHom 𝒜 ℋ} (hf : f.IsIso) :
    ∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj R A ⟨n + 1, n.succ_pos⟩ = φ ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨n + 2, by omega⟩ := by
  -- On the words of length at most `n + 1`, `𝒜` agrees with `ℋ`.
  have h : ∀ z ∈ filtration R A (n + 1), 𝒜.taylor z = ℋ.taylor z := fun z hz ↦
    taylor_apply_eq_of_forall_m_eq hG (fun k hk hkn ↦ by
      obtain rfl | rfl | hk₃ : k = 1 ∨ k = 2 ∨ 3 ≤ k := by omega
      · exact MultilinearMap.ext fun x ↦ by rw [h𝒜.m_one, hℋ.m_one]
      · exact h₂
      · rw [hlow k hk₃ hkn, hm k hk₃]) hz
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- In arity two the obstruction vanishes, since `𝒜` and `ℋ` have the same product.
    refine ⟨0, LinearMap.isHomogeneous_zero _ _ _, LinearMap.zero_comp _, ?_⟩
    refine LinearMap.ext fun z ↦ ?_
    rw [hochschildDifferential_zero, LinearMap.zero_apply, obstruction_def, LinearMap.comp_apply,
      LinearMap.sub_apply, eq_comm, sub_eq_zero]
    exact taylor_apply_eq_of_forall_m_eq hG (n := 2) (fun k hk hk₂ ↦ by
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · exact MultilinearMap.ext fun x ↦ by rw [h𝒜.m_one, hℋ.m_one]
      · exact h₂) (lengthProj_mem_filtration R A ⟨0 + 2, by omega⟩ z)
  obtain ⟨g, hg⟩ := h𝒜.exists_linearPart_eq_id_of_isIso hℋ hm hG h₂ hf
  exact exists_hochschildDifferential_eq_obstruction_of_linearPart_eq_id hℋ hm hG hn h g hg

/-- **A first obstruction which is not a coboundary obstructs formality**, over a `ℚ`-algebra.
Let `ℋ` be a graded algebra, presented as a minimal `A∞` algebra without operations above arity
two, and let `𝒜` be a minimal `A∞` structure with the grading and the binary operation of `ℋ` and
with `m₃ = ⋯ = mₙ₊₁ = 0`.  If the obstruction `mₙ₊₂` of `𝒜` is not the Hochschild differential of
a degree-zero cochain, then `𝒜` is not formal. -/
theorem IsMinimal.not_isFormal_of_not_exists_hochschildDifferential_eq_obstruction
    (h𝒜 : 𝒜.IsMinimal) (hℋ : ℋ.IsMinimal) (hm : ∀ k, 3 ≤ k → ℋ.m k = 0)
    (hG : 𝒜.grading = ℋ.grading) (h₂ : 𝒜.m 2 = ℋ.m 2) {n : ℕ}
    (hlow : ∀ k, 3 ≤ k → k ≤ n + 1 → 𝒜.m k = 0)
    (hobs : ¬∃ φ : ReducedTensorWords R A →ₗ[R] A,
      LinearMap.IsHomogeneous φ (gradedPiece (ℋ.grading.shift 1))
        (ℋ.grading.shift 1).piece 0 ∧
      ℋ.hochschildDifferential 0 φ = 𝒜.obstruction ℋ ⟨n + 2, by omega⟩) :
    ¬𝒜.IsFormal := by
  rw [h𝒜.isFormal_iff_exists_isIso hℋ hm hG h₂]
  rintro ⟨f, hf⟩
  obtain ⟨φ, hφ, -, hφo⟩ :=
    h𝒜.exists_hochschildDifferential_eq_obstruction_of_isIso hℋ hm hG h₂ hlow hf
  exact hobs ⟨φ, hφ, hφo⟩

end Rat

end AInfinityAlgebra

end TauCeti
