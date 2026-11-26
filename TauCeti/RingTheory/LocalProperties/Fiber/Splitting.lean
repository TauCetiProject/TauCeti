/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalProperties.Fiber
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.LocalProperties.Projective
import TauCeti.Algebra.Exact.Split

/-!
# Fibrewise splitting into finite projective modules

A map from a finite module into a finite projective module splits as an injection if it is
injective over every residue field. Consequently a complex `M → N → P` of finite modules with
`N` and `P` projective which is exact at `M` and `N` on every fibre admits a contracting
homotopy in those two degrees. In particular,
it stays exact there after tensoring with any module, including along nonflat base changes.

The two-degree criterion is the algebraic step in splitting the constants off a perfect model
of the cohomology of the structure sheaf. See the Stacks Project, Tags
[0E62](https://stacks.math.columbia.edu/tag/0E62) and
[0E0L](https://stacks.math.columbia.edu/tag/0E0L).
-/

public section

open scoped TensorProduct

namespace LinearMap

variable {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- Passing through the localization does not change a residue-field fibre map. -/
private theorem injective_lTensor_localization_residueField (f : M →ₗ[R] N)
    (p : PrimeSpectrum R) (hf : Function.Injective (f.lTensor p.asIdeal.ResidueField)) :
    Function.Injective
      ((f.baseChange (Localization.AtPrime p.asIdeal)).lTensor p.asIdeal.ResidueField) := by
  let A := Localization.AtPrime p.asIdeal
  let k := p.asIdeal.ResidueField
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A k M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange R A A k N
  have hcomm (z : k ⊗[A] (A ⊗[R] M)) :
      f.lTensor k (eM z) = eN ((f.baseChange A).lTensor k z) :=
    LinearMap.congr_fun
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange R A A f) z
  intro x y hxy
  exact eM.injective (hf ((hcomm x).trans ((congrArg eN hxy).trans (hcomm y).symm)))

/-- A map from a finite module into a finite projective module has a left inverse if and only if
it is injective on every residue-field fibre. -/
theorem exists_leftInverse_iff_forall_injective_lTensor_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) :
    (∃ r : N →ₗ[R] M, r ∘ₗ f = .id) ↔
      ∀ p : PrimeSpectrum R, Function.Injective (f.lTensor p.asIdeal.ResidueField) := by
  refine ⟨fun ⟨r, hr⟩ p ↦ ?_, fun hf ↦ ?_⟩
  · have h : (r.lTensor p.asIdeal.ResidueField) ∘ₗ (f.lTensor p.asIdeal.ResidueField) = .id := by
      rw [← lTensor_comp, hr, lTensor_id]
    exact injective_of_comp_eq_id _ _ h
  -- The cokernel is finitely presented and is free at every maximal ideal.
  let q := (range f).mkQ
  have : Module.FinitePresentation R N := Module.finitePresentation_of_projective R N
  have : Module.FinitePresentation R (N ⧸ range f) :=
    Module.finitePresentation_of_surjective q (Submodule.mkQ_surjective _) (by
      simpa only [q, Submodule.ker_mkQ, ← range_eq_map] using
        (Module.Finite.fg_top (R := R) (M := M)).map f)
  have : Module.Projective R (N ⧸ range f) := by
    apply Module.projective_of_localization_maximal
    intro I hI
    let A := Localization.AtPrime I
    have : Module.Free A (A ⊗[R] N) := Module.free_of_flat_of_isLocalRing
    have hinj := injective_lTensor_localization_residueField f ⟨I, hI.isPrime⟩ (hf _)
    have : Module.Free A (A ⊗[R] (N ⧸ range f)) :=
      Module.free_of_lTensor_residueField_injective (f.baseChange A) (q.baseChange A)
        (lTensor_surjective A (Submodule.mkQ_surjective _))
        (_root_.lTensor_exact A f.exact_map_mkQ_range (Submodule.mkQ_surjective _)) hinj
    exact Module.Projective.of_equiv
      (IsLocalizedModule.isBaseChange I.primeCompl A
        (LocalizedModule.mkLinearMap I.primeCompl (N ⧸ range f))).equiv
  -- Splitting off the cokernel makes the range projective, so the fibrewise bijectivity
  -- criterion identifies the original source with that range.
  obtain ⟨r, hr⟩ := ((Function.Exact.split_tfae (exact_subtype_mkQ (range f))
    Subtype.val_injective (Submodule.mkQ_surjective _)).out 1 2).mp
    (Module.projective_lifting_property q LinearMap.id (Submodule.mkQ_surjective _))
  have : Module.Projective R (range f) := Module.Projective.of_split _ _ hr
  have hb : Function.Bijective f.rangeRestrict :=
    (bijective_iff_forall_bijective_lTensor_residueField _).2 fun p ↦ by
      refine ⟨?_, lTensor_surjective _ f.surjective_rangeRestrict⟩
      apply Function.Injective.of_comp (f := (range f).subtype.lTensor p.asIdeal.ResidueField)
      -- Use linear-map composition so tensor functoriality rewrites the composite.
      change Function.Injective ((range f).subtype.lTensor p.asIdeal.ResidueField ∘ₗ
        f.rangeRestrict.lTensor p.asIdeal.ResidueField)
      rw [← lTensor_comp]
      exact hf p
  let e := LinearEquiv.ofBijective f.rangeRestrict hb
  refine ⟨e.symm.toLinearMap ∘ₗ r, ?_⟩
  ext x
  -- Expose the range carrier so the retraction equation applies.
  change e.symm (r ((range f).subtype (e x))) = x
  rw [← comp_apply, hr, id_apply, e.symm_apply_apply]

/-- If `M → N → P` is a complex of finite modules with `N` and `P` projective, and its first map
is injective and its middle term exact on every residue-field fibre, it is split exact in those
two degrees. -/
theorem exists_leftInverse_and_comp_add_comp_eq_id_of_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R P] [Module.Projective R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : g ∘ₗ f = 0)
    (hf : ∀ p : PrimeSpectrum R, Function.Injective (f.lTensor p.asIdeal.ResidueField))
    (h : ∀ p : PrimeSpectrum R,
      Function.Exact (f.lTensor p.asIdeal.ResidueField) (g.lTensor p.asIdeal.ResidueField)) :
    ∃ (r : N →ₗ[R] M) (s : P →ₗ[R] N),
      r ∘ₗ f = .id ∧ f ∘ₗ r + s ∘ₗ g = .id := by
  obtain ⟨r, hr⟩ := (f.exists_leftInverse_iff_forall_injective_lTensor_residueField).2 hf
  let q := (range f).mkQ
  let d := (range f).liftQ g (by rw [range_le_ker_iff, hfg])
  have hq : q ∘ₗ f = 0 := range_mkQ_comp f
  have hd : d ∘ₗ q = g := Submodule.liftQ_mkQ _ _ _
  have hex : Function.Exact f q := f.exact_map_mkQ_range
  let e := LinearEquiv.ofBijective (r.prod q)
    (hex.bijective_prod_of_comp_eq_id (Submodule.mkQ_surjective _) hr)
  let i := e.symm.toLinearMap ∘ₗ inr R M (N ⧸ range f)
  have he (x : N) : e x = (r x, q x) := by
    simp [e]
  have hei (x : N ⧸ range f) : e (i x) = (0, x) := e.apply_symm_apply (0, x)
  obtain ⟨s, hs⟩ := (d.exists_leftInverse_iff_forall_injective_lTensor_residueField).2 (fun p ↦ by
    let k := p.asIdeal.ResidueField
    apply ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := lTensor_surjective k (Submodule.mkQ_surjective _) z
    have hx : x ∈ ker (g.lTensor k) := by
      rwa [mem_ker, ← hd, lTensor_comp, comp_apply]
    obtain ⟨y, rfl⟩ := (h p).linearMap_ker_eq ▸ hx
    -- Keep the quotient map in its named form so its composite with `f` rewrites.
    change (q.lTensor k) ((f.lTensor k) y) = 0
    rw [← comp_apply, ← lTensor_comp, hq, lTensor_zero, LinearMap.zero_apply])
  refine ⟨r, i ∘ₗ s, hr, ?_⟩
  have hsg : (i ∘ₗ s) ∘ₗ g = i ∘ₗ q := by
    rw [← hd]
    exact LinearMap.ext fun x ↦ congrArg i (LinearMap.congr_fun hs (q x))
  rw [hsg]
  refine LinearMap.ext fun x ↦ e.injective ?_
  -- Evaluate the two summands in the product coordinates of the splitting.
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply]
  rw [map_add, he (f (r x)), hei, he x]
  simpa using And.intro (LinearMap.congr_fun hr (r x)) (LinearMap.congr_fun hq (r x))

end LinearMap
