/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.SignTwisted
public import TauCeti.Analysis.Complex.Wirtinger.Basic

/-!
# Twisted kernels of the normal operator of a torus on its double covers

Let `C = ℂ ⧸ Λ` be an embedded pseudoholomorphic torus in a symplectic four-manifold. In a
`Λ`-periodic unitary frame of its normal line, the normal Cauchy–Riemann operator of `C` reads
`D v = ∂bar v + ν v + μ conj v` with `Λ`-periodic coefficients `ν` and `μ`. Its real-differentiable
solutions `v : ℂ → ℂ` form the real subspace `TauCeti.cauchyRiemannKernel ν μ`. In Taubes's count of
pseudoholomorphic curves, a square-zero torus is labelled by its normal operator twisted by each of
its four real flat sign lines `χ : Λ → ZMod 2`: the operator `D` acting on the maps twisted by `χ`
(`TauCeti.signTwisted`), with `v (z + ω) = (-1) ^ χ ω v z`. Its double covers carry the multiply
covered tori.

Translations by `Λ` preserve the solutions (`TauCeti.translate_mem_cauchyRiemannKernel`), so the
splitting of twisted maps on double covers of
`TauCeti.Algebra.Module.SignTwisted` applies to them. For a nonzero sign character `ι`, defining
the double cover `ℂ ⧸ ker ι` of `C`, and every sign character `χ`:

* the solutions on the double cover twisted by the restriction of `χ` are the sums of solutions on
  `C` twisted by `χ` and by `χ + ι`
  (`TauCeti.signTwisted_domRestrict_ker_inf_cauchyRiemannKernel_eq_sup`);
  together with `TauCeti.disjoint_signTwisted_add` this sum is direct, so the kernel of the twisted
  operator of the double cover is the direct sum of the kernels of two twisted operators of `C`;
* hence the twisted operator of the double cover has no kernel exactly when the operators of `C`
  twisted by `χ` and by `χ + ι` have none
  (`TauCeti.signTwisted_domRestrict_ker_inf_cauchyRiemannKernel_eq_bot_iff`);
* the untwisted operator on the four-fold cover cut out by `ι` and a second sign character `κ` not
  vanishing on `ker ι`, which is `ℂ ⧸ 2Λ` for a lattice, has no kernel exactly when none of the four
  twisted operators of `C` has
  (`TauCeti.signTwisted_zero_domRestrict_ker_domRestrict_ker_inf_cauchyRiemannKernel_eq_bot_iff`).

So whether the twisted operators of a double cover of `C` have kernels is decided by the twisted
operators of `C`. The kernels here are those of `D` on real-differentiable maps of the plane; the
Fredholm realizations, the determinant lines and their orientations, which give the labels
themselves, are separate.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
-/

public section

open ComplexConjugate

namespace TauCeti

/-- The **solutions of the normal Cauchy–Riemann equation** `D v = ∂bar v + ν v + μ conj v = 0`:
the real-differentiable maps `v : ℂ → ℂ` on the plane with `∂bar v + ν v + μ conj v = 0`, for
arbitrary coefficients `ν` and `μ`. It is a real subspace, since `D` is real linear. For
`Λ`-periodic `ν` and `μ`, its intersection with `TauCeti.signTwisted ℝ Λ.subtype χ` is the kernel
of the normal operator of the torus `ℂ ⧸ Λ` twisted by `χ`. -/
def cauchyRiemannKernel (ν μ : ℂ → ℂ) : Submodule ℝ (ℂ → ℂ) where
  carrier := {v | Differentiable ℝ v ∧
    ∀ z, conjWirtingerDeriv v z 1 + ν z * v z + μ z * conj (v z) = 0}
  add_mem' {v w} hv hw := ⟨hv.1.add hw.1, fun z ↦ by
    rw [conjWirtingerDeriv_add (hv.1 z) (hw.1 z), add_apply, Pi.add_apply,
      map_add]
    linear_combination hv.2 z + hw.2 z⟩
  zero_mem' := ⟨differentiable_const 0, fun z ↦ by
    simp [Pi.zero_def]⟩
  smul_mem' c v hv := ⟨hv.1.const_smul c, fun z ↦ by
    have hcv : c • v = (c : ℂ) • v := funext fun _ ↦ (Complex.coe_smul _ _).symm
    rw [hcv, conjWirtingerDeriv_const_smul, smul_apply, Pi.smul_apply]
    simp only [smul_eq_mul, map_mul, Complex.conj_ofReal]
    linear_combination (c : ℂ) * hv.2 z⟩

variable {ν μ : ℂ → ℂ} {v : ℂ → ℂ}

@[simp]
theorem mem_cauchyRiemannKernel : v ∈ cauchyRiemannKernel ν μ ↔ Differentiable ℝ v ∧
    ∀ z, conjWirtingerDeriv v z 1 + ν z * v z + μ z * conj (v z) = 0 :=
  Iff.rfl

/-- **Translation invariance.** If the coefficients `ν` and `μ` are invariant under the
translation by `ω`, then so is the kernel of `D`. -/
theorem translate_mem_cauchyRiemannKernel {ω : ℂ} (hν : ∀ z, ν (z + ω) = ν z)
    (hμ : ∀ z, μ (z + ω) = μ z) (hv : v ∈ cauchyRiemannKernel ν μ) :
    (fun z ↦ v (z + ω)) ∈ cauchyRiemannKernel ν μ := by
  refine ⟨hv.1.comp (differentiable_id.add_const ω), fun z ↦ ?_⟩
  rw [conjWirtingerDeriv_comp_add_right, ← hν z, ← hμ z]
  exact hv.2 (z + ω)

variable {Λ : AddSubgroup ℂ} {ι χ κ : Λ →+ ZMod 2}

/-- **Twisted solutions on a double cover.** For `Λ`-periodic coefficients and a sign character
`ι`, the solutions of `D v = 0` twisted along `ker ι` by the restriction of `χ` are the
sums of solutions twisted by `χ` and by `χ + ι` along `Λ`. -/
theorem signTwisted_domRestrict_ker_inf_cauchyRiemannKernel_eq_sup
    (hν : ∀ ω ∈ Λ, ∀ z, ν (z + ω) = ν z) (hμ : ∀ ω ∈ Λ, ∀ z, μ (z + ω) = μ z) :
    signTwisted ℝ (Λ.subtype.domRestrict ι.ker) (χ.domRestrict ι.ker) ⊓ cauchyRiemannKernel ν μ =
      signTwisted ℝ Λ.subtype χ ⊓ cauchyRiemannKernel ν μ ⊔
        signTwisted ℝ Λ.subtype (χ + ι) ⊓ cauchyRiemannKernel ν μ :=
  signTwisted_domRestrict_ker_inf_eq_sup fun ω _ ↦
    translate_mem_cauchyRiemannKernel (hν ω ω.property) (hμ ω ω.property)

/-- **Nondegeneracy on a double cover.** For `Λ`-periodic coefficients and a sign character `ι`,
the operator `D` twisted along `ker ι` by the restriction of `χ` has no nonzero
solution exactly when `D` twisted by `χ` and `D` twisted by `χ + ι` have none. -/
theorem signTwisted_domRestrict_ker_inf_cauchyRiemannKernel_eq_bot_iff
    (hν : ∀ ω ∈ Λ, ∀ z, ν (z + ω) = ν z) (hμ : ∀ ω ∈ Λ, ∀ z, μ (z + ω) = μ z) :
    signTwisted ℝ (Λ.subtype.domRestrict ι.ker) (χ.domRestrict ι.ker) ⊓
        cauchyRiemannKernel ν μ = ⊥ ↔
      signTwisted ℝ Λ.subtype χ ⊓ cauchyRiemannKernel ν μ = ⊥ ∧
        signTwisted ℝ Λ.subtype (χ + ι) ⊓ cauchyRiemannKernel ν μ = ⊥ :=
  signTwisted_domRestrict_ker_inf_eq_bot_iff fun ω _ ↦
    translate_mem_cauchyRiemannKernel (hν ω ω.property) (hμ ω ω.property)

/-- **Nondegeneracy on the four-fold cover.** For `Λ`-periodic coefficients and sign characters
`ι` and `κ`, the operator `D` on the cover cut out by the kernel of the restriction of `κ` to
`ker ι` has no nonzero periodic solution exactly when none of the four operators of the torus
twisted by `0`, `ι`, `κ` and `κ + ι` has a nonzero solution. When `ι ≠ 0` and `κ` does not vanish
on `ker ι`, for a lattice `Λ` of rank two, these are its four sign characters and the cover is
`ℂ ⧸ 2Λ`. -/
theorem signTwisted_zero_domRestrict_ker_domRestrict_ker_inf_cauchyRiemannKernel_eq_bot_iff
    (hν : ∀ ω ∈ Λ, ∀ z, ν (z + ω) = ν z) (hμ : ∀ ω ∈ Λ, ∀ z, μ (z + ω) = μ z) :
    signTwisted ℝ ((Λ.subtype.domRestrict ι.ker).domRestrict (κ.domRestrict ι.ker).ker) 0 ⊓
        cauchyRiemannKernel ν μ = ⊥ ↔
      signTwisted ℝ Λ.subtype 0 ⊓ cauchyRiemannKernel ν μ = ⊥ ∧
        signTwisted ℝ Λ.subtype ι ⊓ cauchyRiemannKernel ν μ = ⊥ ∧
          signTwisted ℝ Λ.subtype κ ⊓ cauchyRiemannKernel ν μ = ⊥ ∧
            signTwisted ℝ Λ.subtype (κ + ι) ⊓ cauchyRiemannKernel ν μ = ⊥ :=
  signTwisted_zero_domRestrict_ker_domRestrict_ker_inf_eq_bot_iff fun ω _ ↦
    translate_mem_cauchyRiemannKernel (hν ω ω.property) (hμ ω ω.property)

end TauCeti
