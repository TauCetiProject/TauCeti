/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
-- Private: used only inside the proof of `AddChar.sum_dual_apply_eq_ite`.
import TauCeti.LinearAlgebra.Dual.Basis

/-!
# The finite Fourier transform on a module and its dual

Let `W` be a finite module over a commutative semiring `R`, let `Λ` be a commutative semiring and
let `φ : AddChar R Λ` be an additive character. The finite Fourier transform sends a function
`t : W → Λ` to the function on the dual module `W^∨ = Module.Dual R W` given by
`(𝔉_φ t)(w') = ∑ w, t w * φ (w' w)`,
without normalizing factor or sign. Over a finite field `k` of characteristic `p` and an additive
character `ψ` of `ZMod p`, the character `φ = ψ ∘ Tr_{k/𝔽_p}` gives the transform which is the
function-level shadow of the `ℓ`-adic Fourier–Deligne transform: the trace function of the
Fourier–Deligne transform of a complex is, up to the sign `(-1)^r`, the finite Fourier transform of
its trace function.

The identities which hold for every character are proved for a finite module over a commutative
semiring: translation, the convolution identity, compatibility with push-forward along a linear
map and the effect of inverting the character. Inversion, Plancherel and the transforms of
indicators of subspaces need orthogonality. Over a finite field `k` we assume `∑ r : k, φ r = 0`,
which is exactly what they need: applied to the indicator of `0` on `W = k`, inversion forces it.
It holds for every nontrivial character into a domain (`AddChar.sum_eq_zero_of_ne_one`), and for
`φ = ψ ∘ Tr` whenever `ψ 1 - 1` is a unit.

## Main definitions

* `AddChar.fourierTransform φ`: the `Λ`-linear map `(W → Λ) → (Module.Dual R W → Λ)`.
* `AddChar.fourierTransformEquiv`: over a finite field, the transform as a linear equivalence when
  `∑ r, φ r = 0` and `Fintype.card W` is a unit of `Λ`.

## Main results

* `AddChar.fourierTransform_comp_sub_right`: translation by `e` multiplies the transform by
  `w' ↦ φ (w' e)`.
* `AddChar.fourierTransform_convolution`: the transform of a convolution is the product of the
  transforms.
* `AddChar.fourierTransform_sum_fiberwise`: the transform of the push-forward of `t` along a linear
  map `f` is the transform of `t` composed with the dual map `f^∨`.
* `AddChar.inv_fourierTransform`: transforming with `φ⁻¹` composes the transform with `w' ↦ -w'`.
* `AddChar.sum_apply_eq_zero_of_dual_ne_zero`: orthogonality, `∑ v, φ (f v) = 0` for a nonzero
  linear form `f` on a finite vector space.
* `AddChar.sum_apply_dual_eq_ite`: orthogonality, `∑ v, φ (f v)` is `|V|` at `f = 0` and `0`
  elsewhere.
* `AddChar.sum_dual_apply_eq_ite`: orthogonality on the dual, `∑ w', φ (w' u)` is `|W|` at `u = 0`
  and `0` elsewhere.
* `AddChar.fourierTransform_fourierTransform_eval`: inversion, `𝔉 (𝔉 t) (eval w) = |W| t (-w)`.
* `AddChar.sum_fourierTransform_mul_fourierTransform`: Plancherel,
  `∑ w', 𝔉 t₁ w' * 𝔉 t₂ w' = |W| ∑ w, t₁ w * t₂ (-w)`.
* `AddChar.fourierTransform_indicator_submodule`: the transform of the indicator of a subspace `U`
  is `|U|` times the indicator of its annihilator `U^⊥`.
* `AddChar.fourierTransform_stdAddChar_mul`: for `ZMod.stdAddChar` on `ZMod N`, the transform is
  Mathlib's `ZMod.dft` up to `k ↦ -k`.

## References

* G. Laumon, *Transformation de Fourier, constantes d'équations fonctionnelles et conjecture de
  Weil*, Publ. Math. IHÉS 65 (1987), §1.2: the definition (1.2.1) of the finite transform and the
  function forms of the identities (1.2.2.1)–(1.2.2.8).
-/

public section

open Finset Module

namespace AddChar

section CommSemiring

variable {R Λ W : Type*} [CommSemiring R] [CommSemiring Λ] [AddCommMonoid W] [Module R W]
  [Fintype W] (φ : AddChar R Λ)

/-- The **finite Fourier transform** of functions on a finite `R`-module `W` with values in `Λ`,
with respect to the additive character `φ : AddChar R Λ`: the function `t : W → Λ` goes to the
function `w' ↦ ∑ w, t w * φ (w' w)` on the dual module `Module.Dual R W`. -/
def fourierTransform : (W → Λ) →ₗ[Λ] (Module.Dual R W → Λ) where
  toFun t w' := ∑ w, t w * φ (w' w)
  map_add' t₁ t₂ := by
    ext w'
    simp [add_mul, sum_add_distrib]
  map_smul' c t := by
    ext w'
    simp [mul_sum, mul_assoc]

/-- The defining formula `(𝔉_φ t)(w') = ∑ w, t w * φ (w' w)`. -/
theorem fourierTransform_apply (t : W → Λ) (w' : Module.Dual R W) :
    φ.fourierTransform t w' = ∑ w, t w * φ (w' w) :=
  (rfl)

/-- The transform of the function supported at `e` with value `c` is `w' ↦ c * φ (w' e)`. -/
@[simp]
theorem fourierTransform_single [DecidableEq W] (e : W) (c : Λ) (w' : Module.Dual R W) :
    φ.fourierTransform (Pi.single e c) w' = c * φ (w' e) := by
  simp [fourierTransform_apply, Pi.single_apply]

/-- The transform of the indicator of `0` is the constant function `1`. -/
theorem fourierTransform_single_zero [DecidableEq W] :
    φ.fourierTransform (Pi.single (0 : W) (1 : Λ)) = 1 := by
  ext w'
  simp

/-- At the zero linear form, the transform is the sum of all values. -/
@[simp]
theorem fourierTransform_apply_zero (t : W → Λ) :
    φ.fourierTransform t 0 = ∑ w, t w := by
  simp [fourierTransform_apply]

/-- **Push-forward.** For a linear map `f : W₁ → W₂`, the transform of the push-forward
`w₂ ↦ ∑_{f w₁ = w₂} t w₁` is the transform of `t` composed with the dual map `f^∨`. -/
theorem fourierTransform_sum_fiberwise {W₁ : Type*} [AddCommMonoid W₁] [Module R W₁] [Fintype W₁]
    [DecidableEq W] (f : W₁ →ₗ[R] W) (t : W₁ → Λ) (w' : Module.Dual R W) :
    φ.fourierTransform (fun w ↦ ∑ w₁ with f w₁ = w, t w₁) w' =
      φ.fourierTransform t (f.dualMap w') := by
  simp only [fourierTransform_apply, sum_mul, LinearMap.dualMap_apply]
  rw [← sum_fiberwise univ f fun w₁ ↦ t w₁ * φ (w' (f w₁))]
  refine sum_congr rfl fun w _ ↦ sum_congr rfl fun w₁ hw₁ ↦ ?_
  rw [(mem_filter.mp hw₁).2]

end CommSemiring

section AddCommGroup

variable {R Λ W : Type*} [CommSemiring R] [CommSemiring Λ] [AddCommGroup W] [Module R W]
  [Fintype W] (φ : AddChar R Λ)

/-- **Translation.** The transform of `w ↦ t (w - e)` is the transform of `t` multiplied by
`w' ↦ φ (w' e)`. -/
theorem fourierTransform_comp_sub_right (t : W → Λ) (e : W) :
    φ.fourierTransform (t ∘ fun w ↦ w - e) = fun w' ↦ φ (w' e) * φ.fourierTransform t w' := by
  ext w'
  simp only [fourierTransform_apply, Function.comp_apply, mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight e) _ _ fun w ↦ ?_
  rw [Equiv.subRight_apply, mul_left_comm, ← map_add_eq_mul, ← map_add, add_sub_cancel]

/-- **Convolution.** The transform of the convolution `w ↦ ∑ u, t₁ u * t₂ (w - u)` is the product
of the transforms. -/
theorem fourierTransform_convolution (t₁ t₂ : W → Λ) :
    φ.fourierTransform (fun w ↦ ∑ u, t₁ u * t₂ (w - u)) =
      φ.fourierTransform t₁ * φ.fourierTransform t₂ := by
  ext w'
  have h (u : W) : ∑ w, t₂ (w - u) * φ (w' w) = φ (w' u) * φ.fourierTransform t₂ w' :=
    congr_fun (φ.fourierTransform_comp_sub_right t₂ u) w'
  simp only [fourierTransform_apply, Pi.mul_apply, sum_mul] at h ⊢
  rw [sum_comm]
  refine sum_congr rfl fun u _ ↦ ?_
  simp only [mul_assoc, ← mul_sum, h]

end AddCommGroup

/-- **The inverse character.** Transforming with `φ⁻¹` is transforming with `φ` and then
composing with `w' ↦ -w'`. -/
theorem inv_fourierTransform {R Λ W : Type*} [CommRing R] [CommSemiring Λ] [AddCommMonoid W]
    [Module R W] [Fintype W] (φ : AddChar R Λ) (t : W → Λ) (w' : Module.Dual R W) :
    φ⁻¹.fourierTransform t w' = φ.fourierTransform t (-w') := by
  simp [fourierTransform_apply]

section Field

variable {k Λ V W : Type*} [Field k] [Fintype k] [CommSemiring Λ] [AddCommGroup V] [Module k V]
  [Fintype V] [AddCommGroup W] [Module k W] [Fintype W] {φ : AddChar k Λ}

/-- **Orthogonality.** If `∑ r, φ r = 0`, then `∑ v, φ (f v) = 0` for every nonzero linear form
`f` on a finite vector space. -/
theorem sum_apply_eq_zero_of_dual_ne_zero (hφ : ∑ r, φ r = 0) {f : Module.Dual k V}
    (hf : f ≠ 0) : ∑ v, φ (f v) = 0 := by
  classical
  have hsurj : Function.Surjective f := surjective_of_ne_zero_of_finrank_eq_one (finrank_self k) hf
  rw [sum_comp, image_univ_of_surjective hsurj]
  have hfib (r : k) : #{v | f v = r} = #{v | f v = 0} :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (hsurj r) (hsurj 0)
  simp only [hfib, ← smul_sum, hφ, smul_zero]

/-- Orthogonality, `∑ v, φ (f v)` is `|V|` at `f = 0` and `0` for every other linear form `f`. -/
theorem sum_apply_dual_eq_ite [DecidableEq (Module.Dual k V)] (hφ : ∑ r, φ r = 0)
    (f : Module.Dual k V) : ∑ v, φ (f v) = if f = 0 then (Fintype.card V : Λ) else 0 := by
  split_ifs with hf
  · simp [hf]
  · exact sum_apply_eq_zero_of_dual_ne_zero hφ hf

omit [Fintype W] in
/-- Orthogonality on the dual: `∑ w', φ (w' u) = 0` for every nonzero vector `u`. -/
theorem sum_dual_apply_eq_zero [Fintype (Module.Dual k W)] (hφ : ∑ r, φ r = 0) {u : W}
    (hu : u ≠ 0) : ∑ w' : Module.Dual k W, φ (w' u) = 0 := by
  simpa only [Module.Dual.eval_apply] using sum_apply_eq_zero_of_dual_ne_zero hφ
    (f := Module.Dual.eval k W u) ((Module.eval_apply_eq_zero_iff k u).not.mpr hu)

/-- `∑ w', φ (w' u)` is `|W|` at `u = 0` and `0` elsewhere. -/
theorem sum_dual_apply_eq_ite [Fintype (Module.Dual k W)] [DecidableEq W] (hφ : ∑ r, φ r = 0)
    (u : W) : ∑ w' : Module.Dual k W, φ (w' u) = if u = 0 then (Fintype.card W : Λ) else 0 := by
  split_ifs with hu
  · simp [hu, Fintype.card_eq_nat_card, TauCeti.Module.natCard_dual, -Nat.card_eq_fintype_card]
  · exact sum_dual_apply_eq_zero hφ hu

/-- **Fourier inversion.** If `∑ r, φ r = 0`, transforming twice gives `|W| · t (-w)` at the image
of `w` under the canonical map `W → W^∨∨`. -/
theorem fourierTransform_fourierTransform_eval [Fintype (Module.Dual k W)] (hφ : ∑ r, φ r = 0)
    (t : W → Λ) (w : W) :
    φ.fourierTransform (φ.fourierTransform t) (Module.Dual.eval k W w) =
      Fintype.card W * t (-w) := by
  classical
  simp only [fourierTransform_apply, Module.Dual.eval_apply, sum_mul, mul_assoc,
    ← map_add_eq_mul, ← map_add]
  rw [sum_comm]
  simp only [← mul_sum, sum_dual_apply_eq_ite hφ, mul_ite, mul_zero, add_eq_zero_iff_eq_neg,
    sum_ite_eq', mem_univ, ite_true]
  ring

/-- **Plancherel.** If `∑ r, φ r = 0`, then
`∑ w', 𝔉 t₁ w' * 𝔉 t₂ w' = |W| · ∑ w, t₁ w * t₂ (-w)`. -/
theorem sum_fourierTransform_mul_fourierTransform [Fintype (Module.Dual k W)]
    (hφ : ∑ r, φ r = 0) (t₁ t₂ : W → Λ) :
    ∑ w', φ.fourierTransform t₁ w' * φ.fourierTransform t₂ w' =
      Fintype.card W * ∑ w, t₁ w * t₂ (-w) := by
  have h (v : W) :
      ∑ w', φ.fourierTransform t₁ w' * φ (w' v) = Fintype.card W * t₁ (-v) := by
    rw [← fourierTransform_fourierTransform_eval hφ,
      fourierTransform_apply φ (φ.fourierTransform t₁)]
    simp only [Module.Dual.eval_apply]
  simp only [fourierTransform_apply φ t₂, mul_sum]
  rw [sum_comm]
  simp only [mul_left_comm _ (t₂ _), ← mul_sum, h]
  rw [← Equiv.sum_comp (Equiv.neg W)]
  simp only [Equiv.neg_apply, neg_neg, mul_sum]
  exact sum_congr rfl fun _ _ ↦ by ring

/-- The transform of the indicator of a subspace `U` is `|U|` times the indicator of its
annihilator `U^⊥ ⊆ W^∨`. -/
theorem fourierTransform_indicator_submodule (hφ : ∑ r, φ r = 0) (U : Submodule k W) :
    φ.fourierTransform ((U : Set W).indicator 1) =
      (Nat.card U : Λ) • (U.dualAnnihilator : Set (Module.Dual k W)).indicator 1 := by
  classical
  ext w'
  have hsum :
      φ.fourierTransform ((U : Set W).indicator 1) w' = ∑ u : U, φ (w'.domRestrict U u) := by
    simp only [fourierTransform_apply, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply,
      ite_mul, one_mul, zero_mul, ← sum_filter, LinearMap.domRestrict_apply]
    exact sum_subtype _ (by simp) _
  rw [hsum, Pi.smul_apply, Set.indicator_apply, smul_eq_mul]
  split_ifs with hw'
  · have h0 : w'.domRestrict U = 0 := by
      ext u
      exact (Submodule.mem_dualAnnihilator w').mp hw' u u.property
    simp [h0, Nat.card_eq_fintype_card]
  · have h0 : w'.domRestrict U ≠ 0 := fun h ↦ hw' <| (Submodule.mem_dualAnnihilator w').mpr
      fun u hu ↦ by simpa using LinearMap.congr_fun h ⟨u, hu⟩
    rw [sum_apply_eq_zero_of_dual_ne_zero hφ h0, mul_zero]

/-- The transform of the constant function `1` is `|W|` times the indicator of `0`. -/
theorem fourierTransform_one [DecidableEq (Module.Dual k W)] (hφ : ∑ r, φ r = 0) :
    φ.fourierTransform (1 : W → Λ) = Pi.single 0 (Fintype.card W : Λ) := by
  ext w'
  simpa [Pi.single_apply, Nat.card_eq_fintype_card, Set.indicator_apply] using
    congr_fun (fourierTransform_indicator_submodule hφ (⊤ : Submodule k W)) w'

variable [Fintype (Module.Dual k W)]

/-- **The finite Fourier transform as a linear equivalence.** If `∑ r, φ r = 0` and `|W|` is a
unit of `Λ`, the transform is invertible, with inverse
`t' ↦ (w ↦ |W|⁻¹ · 𝔉_{W^∨} t' (eval (-w)))`. -/
noncomputable def fourierTransformEquiv (hφ : ∑ r, φ r = 0) (hW : IsUnit (Fintype.card W : Λ)) :
    (W → Λ) ≃ₗ[Λ] (Module.Dual k W → Λ) where
  __ := φ.fourierTransform
  invFun t' w := ↑hW.unit⁻¹ * φ.fourierTransform t' (Module.Dual.eval k W (-w))
  left_inv t := by
    ext w
    simp only [LinearMap.toFun_eq_coe, fourierTransform_fourierTransform_eval hφ, neg_neg,
      ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  right_inv t' := by
    classical
    ext w'
    simp only [LinearMap.toFun_eq_coe, fourierTransform_apply, Module.Dual.eval_apply, sum_mul,
      mul_sum, mul_assoc]
    rw [sum_comm]
    have h (x : Module.Dual k W) :
        ∑ w, φ (x (-w)) * φ (w' w) = if x = w' then (Fintype.card W : Λ) else 0 := by
      simp only [map_neg, ← map_add_eq_mul, neg_add_eq_sub, ← LinearMap.sub_apply,
        sum_apply_dual_eq_ite hφ, sub_eq_zero, eq_comm]
    simp only [← mul_sum, h, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [mul_comm (t' w'), ← mul_assoc, IsUnit.val_inv_mul, one_mul]

/-- The linear equivalence `fourierTransformEquiv` is the finite Fourier transform. -/
@[simp]
theorem coe_fourierTransformEquiv (hφ : ∑ r, φ r = 0) (hW : IsUnit (Fintype.card W : Λ)) :
    ⇑(fourierTransformEquiv hφ hW) = φ.fourierTransform :=
  (rfl)

/-- The inverse of the finite Fourier transform is `t' ↦ (w ↦ |W|⁻¹ · 𝔉_{W^∨} t' (eval (-w)))`. -/
@[simp]
theorem fourierTransformEquiv_symm_apply (hφ : ∑ r, φ r = 0) (hW : IsUnit (Fintype.card W : Λ))
    (t' : Module.Dual k W → Λ) (w : W) :
    (fourierTransformEquiv hφ hW).symm t' w =
      ↑hW.unit⁻¹ * φ.fourierTransform t' (Module.Dual.eval k W (-w)) :=
  (rfl)

end Field

/-- **Comparison with `ZMod.dft`.** For the standard character of `ZMod N`, the finite Fourier
transform at the linear form `x ↦ k * x` is Mathlib's discrete Fourier transform at `-k`. -/
theorem fourierTransform_stdAddChar_mul {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ZMod N) :
    ZMod.stdAddChar.fourierTransform Φ (LinearMap.mul (ZMod N) (ZMod N) k) = ZMod.dft Φ (-k) := by
  simp [fourierTransform_apply, ZMod.dft_apply, mul_comm]

end AddChar
