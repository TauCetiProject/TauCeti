/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
import TauCeti.LinearAlgebra.Exact

/-!
# When the kernel of a linear map commutes with a base change

For a linear map `f : M →ₗ[R] N` and a module `P`, Mathlib's `LinearMap.tensorKer` is the
comparison map `P ⊗[R] ker f → ker (P ⊗ f)`. It is an isomorphism when `P` is flat
(`LinearMap.tensorKerEquiv`), but for a general `P` it is neither injective nor surjective. This
file says exactly when it is each, in terms of the factorization `M ↠ range f ↪ N` of `f`:

* it is surjective exactly when `P ⊗ range f → P ⊗ N` is injective;
* it is injective exactly when `P ⊗ ker f → P ⊗ M` is injective.

Hence it is bijective for every `P` as soon as the cokernel `N ⧸ range f` and the image
`range f` are flat. These criteria are the linear algebra behind the theorem on cohomology and
base change. For a complex `K₁ → K₂ → K₃`, let `f : K₂ ⧸ range d₁ → K₃` be the map induced by the
second differential. Then `ker f` is the homology at `K₂`, and by right exactness of the tensor
product `ker (P ⊗ f)` is the homology of the complex tensored with `P`
(`LinearMap.map_ker_lTensor_liftQ`), so `tensorKer` is the base change map on homology.

## Main results

* `LinearMap.surjective_tensorKer_iff`: `P ⊗ ker f → ker (P ⊗ f)` is surjective if and only if
  `P ⊗ range f → P ⊗ N` is injective.
* `LinearMap.injective_tensorKer_iff`: it is injective if and only if `P ⊗ ker f → P ⊗ M` is.
* `LinearMap.bijective_tensorKer_of_flat`: it is bijective when `N ⧸ range f` and `range f` are
  flat.
* `LinearMap.map_ker_lTensor_liftQ`: for a complex, the kernel of `P ⊗ f` is the homology of the
  tensored complex.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, the proof of Theorem III.12.11.
* D. Mumford, *Abelian Varieties*, Tata Institute, 1970, §5.
-/

public section

open TensorProduct

namespace LinearMap

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)

/-- **Surjectivity of the base change map on kernels.** The comparison map
`P ⊗[R] ker f → ker (P ⊗ f)` is surjective if and only if tensoring the inclusion of the image,
`P ⊗ range f → P ⊗ N`, is injective. In particular it is surjective for every `P` when the
cokernel `N ⧸ range f` is flat. -/
theorem surjective_tensorKer_iff :
    Function.Surjective (f.tensorKer S P) ↔ Function.Injective ((range f).subtype.lTensor P) := by
  have hexact : Function.Exact ((ker f).subtype.lTensor P) (f.rangeRestrict.lTensor P) :=
    lTensor_exact P (exact_subtype_rangeRestrict f) f.surjective_rangeRestrict
  -- `P ⊗ f` is `P ⊗ range f → P ⊗ N` after the surjection `P ⊗ M → P ⊗ range f`.
  have hcomp (x : P ⊗[R] M) :
      (range f).subtype.lTensor P (f.rangeRestrict.lTensor P x) = f.lTensor P x := by
    rw [← comp_apply, ← lTensor_comp, subtype_comp_rangeRestrict]
  refine ⟨fun h ↦ (injective_iff_map_eq_zero _).mpr fun y hy ↦ ?_, fun h ⟨x, hx⟩ ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := lTensor_surjective P f.surjective_rangeRestrict y
    obtain ⟨z, hz⟩ := h ⟨x, by simpa [mem_ker, ← hcomp] using hy⟩
    have hzx : (ker f).subtype.lTensor P z = x := by
      rw [← tensorKer_coe S, hz]
    rw [← hzx]
    exact hexact.apply_apply_eq_zero z
  · have hx' : f.rangeRestrict.lTensor P x = 0 :=
      h (by rw [map_zero, hcomp]; simpa [mem_ker] using hx)
    obtain ⟨z, hz⟩ := (hexact x).mp hx'
    exact ⟨z, Subtype.ext (by rw [tensorKer_coe, hz])⟩

/-- **Injectivity of the base change map on kernels.** The comparison map
`P ⊗[R] ker f → ker (P ⊗ f)` is injective if and only if tensoring the inclusion of the kernel,
`P ⊗ ker f → P ⊗ M`, is injective. -/
theorem injective_tensorKer_iff :
    Function.Injective (f.tensorKer S P) ↔ Function.Injective ((ker f).subtype.lTensor P) := by
  have h : (ker f).subtype.lTensor P = Subtype.val ∘ f.tensorKer S P := by
    ext x
    simp
  rw [h, Function.Injective.of_comp_iff Subtype.val_injective]

/-- **The base change map on kernels is bijective when the image and cokernel are flat.** If the
cokernel `N ⧸ range f` and the image `range f` of `f` are flat, then the comparison map
`P ⊗[R] ker f → ker (P ⊗ f)` is bijective for every `P`: the first hypothesis makes
`P ⊗ range f → P ⊗ N` injective and the second makes `P ⊗ ker f → P ⊗ M` injective. -/
theorem bijective_tensorKer_of_flat [Module.Flat R (N ⧸ range f)] [Module.Flat R (range f)] :
    Function.Bijective (f.tensorKer S P) :=
  ⟨(injective_tensorKer_iff S P f).mpr <| lTensor_injective_of_exact_of_flat _
      f.surjective_rangeRestrict _ (ker f).injective_subtype (exact_subtype_rangeRestrict f) P,
    (surjective_tensorKer_iff S P f).mpr <| lTensor_injective_of_exact_of_flat _
      (range f).mkQ_surjective _ (range f).injective_subtype (exact_subtype_mkQ _) P⟩

section Homology

variable {K₁ K₂ K₃ : Type*} [AddCommGroup K₁] [Module R K₁] [AddCommGroup K₂] [Module R K₂]
  [AddCommGroup K₃] [Module R K₃] {d₁ : K₁ →ₗ[R] K₂} {d₂ : K₂ →ₗ[R] K₃}

/-- Tensoring a complex `K₁ → K₂ → K₃` with `P` gives a complex. -/
theorem range_lTensor_le_ker_lTensor (h : range d₁ ≤ ker d₂) :
    range (d₁.lTensor P) ≤ ker (d₂.lTensor P) := by
  rw [range_le_ker_iff, ← lTensor_comp, range_le_ker_iff.mp h, lTensor_zero]

/-- **The kernel of `P ⊗ f` is the homology of the tensored complex.** For a complex
`K₁ → K₂ → K₃` with differentials `d₁`, `d₂`, let `f : K₂ ⧸ range d₁ → K₃` be the map induced by
`d₂`, whose kernel is the homology at `K₂`. Under the right exactness isomorphism
`(P ⊗ K₂) ⧸ range (P ⊗ d₁) ≃ P ⊗ (K₂ ⧸ range d₁)` (`LinearMap.lTensor.equiv`), the kernel of
`P ⊗ f` corresponds to the homology at `P ⊗ K₂` of the tensored complex, the kernel of the map
`(P ⊗ K₂) ⧸ range (P ⊗ d₁) → P ⊗ K₃` induced by `P ⊗ d₂`. So `LinearMap.tensorKer` for `f` is
the base change map on homology, sending `p ⊗ [x]` to `[p ⊗ x]`. -/
theorem map_ker_lTensor_liftQ (h : range d₁ ≤ ker d₂) :
    (ker (((range d₁).liftQ d₂ h).lTensor P)).map
        (lTensor.equiv P (exact_map_mkQ_range d₁) (range d₁).mkQ_surjective).symm.toLinearMap =
      ker ((range (d₁.lTensor P)).liftQ (d₂.lTensor P) (range_lTensor_le_ker_lTensor P h)) := by
  set e := lTensor.equiv P (exact_map_mkQ_range d₁) (range d₁).mkQ_surjective
  -- `e` sends the class of `y` to `(P ⊗ mkQ) y`: its inverse is `lTensor.inverse`, which sends
  -- `(P ⊗ mkQ) y` back to the class of `y`.
  have he_mk (y : P ⊗[R] K₂) : e (Submodule.Quotient.mk y) = (range d₁).mkQ.lTensor P y := by
    rw [← LinearEquiv.eq_symm_apply]
    exact (lTensor.inverse_apply P (exact_map_mkQ_range d₁) (range d₁).mkQ_surjective y).symm
  have he : ((range d₁).liftQ d₂ h).lTensor P ∘ₗ e.toLinearMap =
      (range (d₁.lTensor P)).liftQ (d₂.lTensor P) (range_lTensor_le_ker_lTensor P h) := by
    ext p x
    simp [he_mk]
  rw [Submodule.map_equiv_eq_comap_symm, LinearEquiv.symm_symm, ← ker_comp, he]

end Homology

end LinearMap
