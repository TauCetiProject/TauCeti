/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalProperties.Fiber
import Mathlib.RingTheory.LocalProperties.Projective
import TauCeti.Algebra.Exact.Split
import TauCeti.LinearAlgebra.Finsupp.Supported
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Fibrewise splitting into projective modules

A map from a finite module into a projective module splits as an injection if it is injective
over the residue fields of all maximal ideals. Consequently a complex `M → N → P` with `M`
finite, `N` finite projective, and `P` projective which is exact at `M` and `N` on these fibres
admits a contracting homotopy in those two degrees. In particular, it stays exact there after
tensoring with any module, including along nonflat base changes.

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

/-- For a finite projective target, descend the splitting by checking injectivity and
cokernel projectivity at the maximal localizations. -/
private theorem exists_leftInverse_of_finite_of_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hf : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective (f.lTensor I.ResidueField)) :
    ∃ r : N →ₗ[R] M, r ∘ₗ f = .id := by
  have hlocal (I : Ideal R) [I.IsMaximal] :
      ∃ r, r ∘ₗ f.baseChange (Localization.AtPrime I) = .id := by
    let A := Localization.AtPrime I
    have : Module.Free A (A ⊗[R] N) := Module.free_of_flat_of_isLocalRing
    exact (IsLocalRing.split_injective_iff_lTensor_residueField_injective (f.baseChange A)).2
      ((f.injective_lTensor_baseChange_iff A I.ResidueField).2 (hf I))
  have hinj : Function.Injective f := by
    intro x y hxy
    refine Module.eq_of_localization_maximal
      (fun I _ ↦ Localization.AtPrime I ⊗[R] M)
      (fun I _ ↦ TensorProduct.mk R (Localization.AtPrime I) M 1) x y fun I _ ↦ ?_
    obtain ⟨r, hr⟩ := hlocal I
    apply injective_of_comp_eq_id _ _ hr
    simpa only [TensorProduct.mk_apply, baseChange_tmul] using
      congrArg (TensorProduct.mk R (Localization.AtPrime I) N 1) hxy
  -- The cokernel is finitely presented and locally a direct summand of the target.
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
    have hq := Submodule.mkQ_surjective (range f)
    have hex : Function.Exact (f.baseChange A) (q.baseChange A) :=
      _root_.lTensor_exact A f.exact_map_mkQ_range hq
    have hsplit : Function.Injective (f.baseChange A) ∧ ∃ s, q.baseChange A ∘ₗ s = .id :=
      ((hex.split_tfae').out 2 1).mp (And.intro (lTensor_surjective A hq) (hlocal I))
    obtain ⟨s, hs⟩ := hsplit.2
    have : Module.Projective A (A ⊗[R] (N ⧸ range f)) := Module.Projective.of_split _ _ hs
    exact Module.Projective.of_equiv
      (IsLocalizedModule.isBaseChange I.primeCompl A
        (LocalizedModule.mkLinearMap I.primeCompl (N ⧸ range f))).equiv
  exact ((f.exact_map_mkQ_range.split_tfae hinj (Submodule.mkQ_surjective _)).out 1 2).mp
    (Module.projective_lifting_property q LinearMap.id (Submodule.mkQ_surjective _))

/-- A map from a finite module into a projective module has a left inverse if and only if
it is injective on the residue-field fibres at all maximal ideals. -/
theorem exists_leftInverse_iff_forall_injective_lTensor_residueField
    [Module.Finite R M] [Module.Projective R N] (f : M →ₗ[R] N) :
    (∃ r : N →ₗ[R] M, r ∘ₗ f = .id) ↔
      ∀ (I : Ideal R) [I.IsMaximal], Function.Injective (f.lTensor I.ResidueField) := by
  refine ⟨fun ⟨r, hr⟩ I _ ↦ ?_, fun hf ↦ ?_⟩
  · have h : (r.lTensor I.ResidueField) ∘ₗ (f.lTensor I.ResidueField) = .id := by
      rw [← lTensor_comp, hr, lTensor_id]
    exact injective_of_comp_eq_id _ _ h
  classical
  -- Factor through the finite free summand supporting the image in the ambient free module.
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := R) (P := N)).mp inferInstance
  obtain ⟨S, hS⟩ := (i ∘ₗ f).exists_finset_support_subset
  let L := Finsupp.supported R R (S : Set N)
  let e : L ≃ₗ[R] (S →₀ R) := Finsupp.supportedEquivFinsupp (S : Set N)
  have : Module.Finite R L := Module.Finite.equiv e.symm
  have : Module.Projective R L := Module.Projective.of_equiv e.symm
  let a : L →ₗ[R] N := Finsupp.linearCombination R _root_.id ∘ₗ L.subtype
  let b : N →ₗ[R] L := Finsupp.restrictDom R R (S : Set N) ∘ₗ i
  let g : M →ₗ[R] L := (i ∘ₗ f).codRestrict L fun x ↦ (Finsupp.mem_supported R _).2 (hS x)
  have hg : L.subtype ∘ₗ g = i ∘ₗ f := subtype_comp_codRestrict _ _ _
  have hbg : b ∘ₗ f = g := by
    dsimp only [b]
    rw [comp_assoc, ← hg, ← comp_assoc, Finsupp.restrictDom_comp_subtype, id_comp]
  have hag : a ∘ₗ g = f := by
    dsimp only [a]
    rw [comp_assoc, hg, ← comp_assoc, hi, id_comp]
  obtain ⟨r, hr⟩ := exists_leftInverse_of_finite_of_residueField (N := L) g fun I _ ↦ by
    apply Function.Injective.of_comp (f := a.lTensor I.ResidueField)
    rw [← coe_comp, ← lTensor_comp, hag]
    exact hf I
  exact ⟨r ∘ₗ b, by rw [comp_assoc, hbg, hr]⟩

/-- If `M → N → P` is a complex with `M` finite, `N` finite projective and `P` projective, and
its first map is injective and its middle term exact at every maximal residue-field fibre,
it is split exact in those two degrees. -/
theorem exists_leftInverse_and_comp_add_comp_eq_id_of_residueField
    [Module.Finite R M] [Module.Finite R N] [Module.Projective R N]
    [Module.Projective R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hfg : g ∘ₗ f = 0)
    (hf : ∀ (I : Ideal R) [I.IsMaximal], Function.Injective (f.lTensor I.ResidueField))
    (h : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Exact (f.lTensor I.ResidueField) (g.lTensor I.ResidueField)) :
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
  obtain ⟨s, hs⟩ := (d.exists_leftInverse_iff_forall_injective_lTensor_residueField).2 (fun I _ ↦ by
    let k := I.ResidueField
    apply ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    obtain ⟨x, rfl⟩ := lTensor_surjective k (Submodule.mkQ_surjective _) z
    have hx : x ∈ ker (g.lTensor k) := by
      rwa [mem_ker, ← hd, lTensor_comp, comp_apply]
    obtain ⟨y, rfl⟩ := (h I).linearMap_ker_eq ▸ hx
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
