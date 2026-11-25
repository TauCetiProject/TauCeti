/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import TauCeti.RingTheory.RingHom.FaithfullyFlat

/-!
# Finite presentation descends along smooth faithfully flat extensions

Let `R → A → B` be ring maps with `B` smooth and faithfully flat over `A`. If `B` is of finite
presentation over `R`, then so is `A`. This is the algebraic core of the fact that being locally of
finite presentation is local on the source for the smooth, hence the étale, topology.

The proof needs no limit argument for flatness. By Mathlib's `Algebra.Smooth.exists_subalgebra_fg`,
`B ≅ A ⊗[A₀] B₀` for a smooth algebra `B₀` over a finitely generated `ℤ`-subalgebra `A₀` of `A`.
The image of `Spec B₀ → Spec A₀` is open, with closed complement `V(I)`, so a base change of `B₀`
is faithfully flat exactly over the `A₀`-algebras in which `I` generates the unit ideal
(`Ideal.faithfullyFlat_baseChange_iff_map_eq_top`). Since `B` is faithfully flat over `A`, there is
an equation `∑ cᵢ kᵢ = 1` in `A` with `kᵢ ∈ I`. The `ℤ`-subalgebra `A₁ = A₀[cᵢ]` of `A` is finitely
generated, hence of finite presentation over `ℤ`, and `B₁ = A₁ ⊗[A₀] B₀` is faithfully flat over
`A₁` with `A ⊗[A₁] B₁ ≅ B`. Extending scalars to the finitely presented `R`-algebra
`A' = R ⊗[ℤ] A₁`, which maps to `A`, gives a faithfully flat, finitely presented `A'`-algebra
`T = A' ⊗[A₁] B₁` with `A ⊗[A'] T ≅ B`. As `B` is of finite presentation over `R`, it is so over
`T`, and Mathlib's faithfully flat descent of finite presentation
(`Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`) shows that
`A` is of finite presentation over `A'`, hence over `R`.

## Main results

* `Algebra.FinitePresentation.of_smooth_of_faithfullyFlat`: if `A → B` is smooth and faithfully
  flat and `B` is of finite presentation over `R`, then `A` is of finite presentation over `R`.

## References

* The Stacks Project, Descent, Section *Properties of morphisms local in the fppf topology on the
  source*, where finite presentation is shown to be fppf local on the source by a limit argument.
-/

public section

open TensorProduct

namespace Algebra.FinitePresentation

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Algebra R B] [IsScalarTower R A B]

/-- Let `B ≅ A ⊗[A₁] B₁` be the base change of a faithfully flat, finitely presented algebra `B₁`
over a ring `A₁` of finite presentation over `ℤ`. If `B` is of finite presentation over `R`, then so
is `A`. -/
private theorem of_algEquiv_tensorProduct (A₁ B₁ : Type*) [CommRing A₁] [CommRing B₁]
    [Algebra A₁ A] [Algebra A₁ B₁] [FinitePresentation ℤ A₁] [FinitePresentation A₁ B₁]
    [Module.FaithfullyFlat A₁ B₁] [FinitePresentation R B] (e : B ≃ₐ[A] A ⊗[A₁] B₁) :
    FinitePresentation R A := by
  -- The finitely presented `R`-algebra `A' = R ⊗[ℤ] A₁` maps to `A`.
  let A' := R ⊗[ℤ] A₁
  let : Algebra A₁ A' := TensorProduct.rightAlgebra
  let φ : A' →ₐ[R] A := AlgHom.liftEquiv ℤ R A₁ A (ofId A₁ A |>.restrictScalars ℤ)
  let : Algebra A' A := φ.toAlgebra
  have : IsScalarTower R A' A := .of_algHom φ
  have hφ (a : A₁) : φ (1 ⊗ₜ a) = algebraMap A₁ A a := by
    rw [AlgHom.liftEquiv_tmul, one_smul, AlgHom.restrictScalars_apply, Algebra.ofId_apply]
  -- The structure map `A₁ → A'` of the right algebra structure is `a ↦ 1 ⊗ₜ a` by definition.
  have : IsScalarTower A₁ A' A := .of_algebraMap_eq fun a ↦ (hφ a).symm
  let : Algebra A' B := ((algebraMap A B).comp (algebraMap A' A)).toAlgebra
  have : IsScalarTower A' A B := .of_algebraMap_eq' rfl
  have : IsScalarTower R A' B := .to₁₂₄ R A' A B
  have : FinitePresentation A' B := .of_restrict_scalars_finitePresentation R A' B
  -- `T = A' ⊗[A₁] B₁` is faithfully flat and finitely presented over `A'`, with `A ⊗[A'] T ≅ B`.
  -- It is introduced as an abstract algebra, so that `T ⊗[A'] A` uses the `A'`-module structure
  -- of the `A'`-algebra `T` rather than that of the tensor product `A' ⊗[A₁] B₁`.
  obtain ⟨T, _, _, _, _, ⟨eT⟩⟩ : ∃ (T : Type _) (_ : CommRing T) (_ : Algebra A' T)
      (_ : FinitePresentation A' T) (_ : Module.FaithfullyFlat A' T),
      Nonempty (B ≃ₐ[A] A ⊗[A'] T) :=
    ⟨A' ⊗[A₁] B₁, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨e.trans (TensorProduct.cancelBaseChange A₁ A' A A B₁).symm⟩⟩
  have : FinitePresentation A' (T ⊗[A'] A) :=
    .equiv ((eT.restrictScalars A').trans (TensorProduct.comm A' A T))
  have : FinitePresentation T (T ⊗[A'] A) := .of_restrict_scalars_finitePresentation A' _ _
  have : FinitePresentation A' A := .of_finitePresentation_tensorProduct_of_faithfullyFlat T
  exact .trans R A' A

/-- **Finite presentation descends along smooth faithfully flat extensions.** If `R → A → B` are
ring maps with `B` smooth and faithfully flat over `A` and of finite presentation over `R`, then `A`
is of finite presentation over `R`. -/
theorem of_smooth_of_faithfullyFlat [Smooth A B] [Module.FaithfullyFlat A B]
    [FinitePresentation R B] : FinitePresentation R A := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ := Smooth.exists_subalgebra_fg ℤ A B
  -- The image of `Spec B₀ → Spec A₀` is open, so its complement is `V(I)` for an ideal `I`. Base
  -- changes of `B₀` are faithfully flat exactly over the `A₀`-algebras in which `I` generates the
  -- unit ideal, for instance over `A`.
  have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀))) := by
    simpa using PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := A₀) (S := B₀) _ isOpen_univ
  set I := PrimeSpectrum.vanishingIdeal (Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))ᶜ
  have hIU : (Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))ᶜ =
      PrimeSpectrum.zeroLocus (I : Set A₀) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hU.isClosed_compl.closure_eq]
  have : Module.FaithfullyFlat A (A ⊗[A₀] B₀) := .of_linearEquiv _ _ e.symm.toLinearEquiv
  have hI := (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I hIU).mp this
  -- Write `1 = ∑ cₐ a` in `A` with each `a` the image of some `kₐ ∈ I`; adjoin the `cₐ` to `A₀`.
  rw [Ideal.map, Ideal.span_eq_top_iff_finite] at hI
  obtain ⟨s, hsI, hs⟩ := hI
  choose k hkI hka using hsI
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp (hs ▸ Submodule.mem_top (x := (1 : A)))
  let A₁ : Subalgebra ℤ A := A₀ ⊔ adjoin ℤ (s.image c : Set A)
  have hle : A₀ ≤ A₁ := le_sup_left
  have hcA₁ (a : A) (ha : a ∈ s) : c a ∈ A₁ :=
    le_sup_right (a := A₀) (subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha)))
  have : FinitePresentation ℤ A₁ := FinitePresentation.of_finiteType.mp
    ((Subalgebra.fg_iff_finiteType _).mp (hA₀.sup (Subalgebra.fg_adjoin_finset _)))
  -- `I` generates the unit ideal of `A₁` too, so `A₁ ⊗[A₀] B₀` is faithfully flat over `A₁`; its
  -- base change to `A` is `B`.
  let : Algebra A₀ A₁ := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A₀ A₁ A := ⟨fun k a x ↦ by
    simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_assoc]⟩
  have : Module.FaithfullyFlat A₁ (A₁ ⊗[A₀] B₀) := by
    refine (Ideal.faithfullyFlat_baseChange_iff_map_eq_top I hIU).mpr
      ((Ideal.eq_top_iff_one _).mpr ?_)
    have h1 : (1 : A₁) =
        ∑ a ∈ s.attach, ⟨c a, hcA₁ a a.property⟩ * algebraMap A₀ A₁ (k a.property) := by
      have hka' (a : A) (ha : a ∈ s) : (k ha : A) = a := hka ha
      ext
      simpa [RingHom.algebraMap_toAlgebra, hka', Finset.sum_attach s (fun a ↦ c a * a)]
        using hc.symm
    rw [h1]
    exact Ideal.sum_mem _ fun a _ ↦
      Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hkI a.property))
  exact of_algEquiv_tensorProduct A₁ (A₁ ⊗[A₀] B₀)
    (e.trans (TensorProduct.cancelBaseChange A₀ A₁ A A B₀).symm)

end Algebra.FinitePresentation
