/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalProperties.Fiber
import Mathlib.LinearAlgebra.Contraction
import TauCeti.Algebra.Exact.Split
import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Fibrewise splitting of finite projective modules

A map between finite projective modules splits as an injection if it is injective over every
residue field. Consequently a complex `M → N → P` of finite projective modules which is exact
at `M` and `N` on every fibre admits a contracting homotopy in those two degrees. In particular,
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

/-- A map between finite projective modules has a left inverse if and only if it is injective
on every residue-field fibre. -/
theorem exists_leftInverse_iff_forall_injective_lTensor_residueField
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) :
    (∃ r : N →ₗ[R] M, r ∘ₗ f = .id) ↔
      ∀ p : PrimeSpectrum R, Function.Injective (f.lTensor p.asIdeal.ResidueField) := by
  refine ⟨fun ⟨r, hr⟩ p ↦ ?_, fun hf ↦ ?_⟩
  · have h : (r.lTensor p.asIdeal.ResidueField) ∘ₗ (f.lTensor p.asIdeal.ResidueField) = .id := by
      rw [← lTensor_comp, hr, lTensor_id]
    exact injective_of_comp_eq_id _ _ h
  -- A left inverse exists if precomposition by `f` surjects onto `End(M)`. The Hom spaces
  -- commute with base change because the source of each Hom is finite projective.
  have hsurj : Function.Surjective (f.lcomp R M) := by
    have : Module.Finite R (M →ₗ[R] M) :=
      Module.Finite.equiv (dualTensorHomEquiv R M M)
    apply (surjective_iff_forall_surjective_lTensor_residueField _).2
    intro p
    let k := p.asIdeal.ResidueField
    let eN := (isBaseChange_baseChangeHom R k N M).equiv
    let eM := (isBaseChange_baseChangeHom R k M M).equiv
    have hcomm (z : k ⊗[R] (N →ₗ[R] M)) :
        eM ((f.lcomp R M).lTensor k z) = eN z ∘ₗ f.baseChange k := by
      -- Precomposition commutes with scalar extension on elementary tensors.
      induction z using TensorProduct.inductionOn with
      | tmul a g =>
        simp [eN, eM, IsBaseChange.equiv_tmul, ← baseChange_comp, smul_comp, lcomp_apply']
      | add x y hx hy => simp [hx, hy, add_comp]
    intro z
    obtain ⟨r, hr⟩ := (f.baseChange k).exists_leftInverse_of_injective (ker_eq_bot.mpr (hf p))
    refine ⟨eN.symm (eM z ∘ₗ r), eM.injective ?_⟩
    rw [hcomm, eN.apply_symm_apply, comp_assoc, hr, comp_id]
  exact hsurj .id

/-- If `M → N → P` is a complex of finite projective modules and its first map is injective and
its middle term exact on every residue-field fibre, it is split exact in those two degrees. -/
theorem exists_leftInverse_and_comp_add_comp_eq_id_of_residueField
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R N] [Module.Projective R N]
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
  have he (x : N) : e x = (r x, q x) := rfl
  have hei (x : N ⧸ range f) : e (i x) = (0, x) := e.apply_symm_apply (0, x)
  have hi : q ∘ₗ i = .id := by
    exact LinearMap.ext fun x ↦ congrArg Prod.snd (hei x)
  have : Module.Projective R (N ⧸ range f) := Module.Projective.of_split i q hi
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
  change e (f (r x) + i (q x)) = e x
  rw [map_add, he (f (r x)), hei, he x]
  simpa using And.intro (LinearMap.congr_fun hr (r x)) (LinearMap.congr_fun hq (r x))

end LinearMap
