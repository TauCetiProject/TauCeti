/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Category.FilteredFrobeniusModule.Basic

/-!
# Direct sums of filtered Frobenius modules

The direct sum `M ⊕ N` of two filtered Frobenius modules is the product of the underlying
modules with the filtration `Fil^i (M ⊕ N) = Fil^i M × Fil^i N` and the divided Frobenius maps
`φ^i (x, y) = (φ^i x, φ^i y)`. It is a biproduct in the category of filtered Frobenius modules,
so that category has binary biproducts. The filtration support and generation of a direct sum
are those of its summands.

## Main definitions

* `TauCeti.FilteredFrobeniusModule.prod M N`: the direct sum of `M` and `N`.
* `TauCeti.FilteredFrobeniusModule.prodBinaryBicone M N`: the projections and inclusions of the
  direct sum, and `TauCeti.FilteredFrobeniusModule.prodIsBilimit`, which shows that it is a
  biproduct.

## Main results

* `TauCeti.FilteredFrobeniusModule.isSupportedIn_prod_iff`: `M ⊕ N` is supported in `[a, b]` iff
  both summands are.
* `TauCeti.FilteredFrobeniusModule.isGenerating_prod_iff`: `M ⊕ N` is generating iff both
  summands are.

## References

* J.-M. Fontaine and G. Laffaille, *Construction de représentations p-adiques*, Ann. Sci. École
  Norm. Sup. (4) 15 (1982), §1.
-/

public section

open CategoryTheory Limits

universe v u

namespace TauCeti.FilteredFrobeniusModule

variable {W : Type u} [CommRing W] {σ : W →+* W} {ϖ : W}

variable (M N : FilteredFrobeniusModule.{v} σ ϖ)

/-- The divided Frobenius map of a direct sum, `φ^i (x, y) = (φ^i x, φ^i y)`. -/
def prodPhi (i : ℤ) : (M.fil i).prod (N.fil i) →ₛₗ[σ] M × N where
  toFun z := (M.phi i ⟨z.val.1, z.property.1⟩, N.phi i ⟨z.val.2, z.property.2⟩)
  map_add' z z' :=
    Prod.ext (map_add (M.phi i) ⟨z.val.1, z.property.1⟩ ⟨z'.val.1, z'.property.1⟩)
      (map_add (N.phi i) ⟨z.val.2, z.property.2⟩ ⟨z'.val.2, z'.property.2⟩)
  map_smul' c z := Prod.ext (map_smulₛₗ (M.phi i) c ⟨z.val.1, z.property.1⟩)
    (map_smulₛₗ (N.phi i) c ⟨z.val.2, z.property.2⟩)

@[simp]
theorem prodPhi_apply (i : ℤ) (z : (M.fil i).prod (N.fil i)) :
    prodPhi M N i z = (M.phi i ⟨z.val.1, z.property.1⟩, N.phi i ⟨z.val.2, z.property.2⟩) := (rfl)

/-- The direct sum of two filtered Frobenius modules: `Fil^i (M ⊕ N) = Fil^i M × Fil^i N` and
`φ^i (x, y) = (φ^i x, φ^i y)`. -/
abbrev prod : FilteredFrobeniusModule.{v} σ ϖ where
  toModuleCat := ModuleCat.of W (M × N)
  fil i := (M.fil i).prod (N.fil i)
  fil_antitone _ _ h := Submodule.prod_mono (M.fil_antitone h) (N.fil_antitone h)
  iSup_fil := by
    refine top_le_iff.1 fun z _ => ?_
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ M.fil_antitone.directed_le).1
      (M.iSup_fil ▸ Submodule.mem_top : z.1 ∈ ⨆ i, M.fil i)
    obtain ⟨i', hi'⟩ := (Submodule.mem_iSup_of_directed _ N.fil_antitone.directed_le).1
      (N.iSup_fil ▸ Submodule.mem_top : z.2 ∈ ⨆ i, N.fil i)
    exact Submodule.mem_iSup_of_mem (min i i')
      ⟨M.fil_antitone (min_le_left i i') hi, N.fil_antitone (min_le_right i i') hi'⟩
  iInf_fil := by
    refine le_bot_iff.1 fun z hz => ?_
    rw [Submodule.mem_iInf] at hz
    have h1 : z.1 ∈ ⨅ i, M.fil i := Submodule.mem_iInf _ |>.2 fun i => (hz i).1
    have h2 : z.2 ∈ ⨅ i, N.fil i := Submodule.mem_iInf _ |>.2 fun i => (hz i).2
    rw [M.iInf_fil, Submodule.mem_bot] at h1
    rw [N.iInf_fil, Submodule.mem_bot] at h2
    exact (Submodule.mem_bot W).2 (Prod.ext h1 h2)
  phi := prodPhi M N
  phi_succ i z hz := Prod.ext (by simpa using M.phi_succ i z.1 hz.1)
    (by simpa using N.phi_succ i z.2 hz.2)

@[simp]
theorem prod_fil (i : ℤ) : (prod M N).fil i = (M.fil i).prod (N.fil i) := (rfl)

theorem prod_phi (i : ℤ) (z : M × N) (hz : z ∈ (prod M N).fil i) :
    (prod M N).phi i ⟨z, hz⟩ = (M.phi i ⟨z.1, hz.1⟩, N.phi i ⟨z.2, hz.2⟩) := (rfl)

/-- The projection from the direct sum onto the first summand. -/
def prodFst : prod M N ⟶ M := ⟨LinearMap.fst W M N, fun _ _ hz => hz.1, fun _ _ _ => rfl⟩

/-- The projection from the direct sum onto the second summand. -/
def prodSnd : prod M N ⟶ N := ⟨LinearMap.snd W M N, fun _ _ hz => hz.2, fun _ _ _ => rfl⟩

/-- The inclusion of the first summand into the direct sum. -/
def prodInl : M ⟶ prod M N :=
  ⟨LinearMap.inl W M N, fun _ _ hx => ⟨hx, zero_mem _⟩,
    fun i _ _ => Prod.ext rfl (map_zero (N.phi i)).symm⟩

/-- The inclusion of the second summand into the direct sum. -/
def prodInr : N ⟶ prod M N :=
  ⟨LinearMap.inr W M N, fun _ _ hy => ⟨zero_mem _, hy⟩,
    fun i _ _ => Prod.ext (map_zero (M.phi i)).symm rfl⟩

@[simp]
theorem prodFst_hom : (prodFst M N).hom = LinearMap.fst W M N := (rfl)

@[simp]
theorem prodSnd_hom : (prodSnd M N).hom = LinearMap.snd W M N := (rfl)

@[simp]
theorem prodInl_hom : (prodInl M N).hom = LinearMap.inl W M N := (rfl)

@[simp]
theorem prodInr_hom : (prodInr M N).hom = LinearMap.inr W M N := (rfl)

/-- The direct sum with its projections and inclusions, as a binary bicone. -/
@[expose, simps]
def prodBinaryBicone : BinaryBicone M N where
  pt := prod M N
  fst := prodFst M N
  snd := prodSnd M N
  inl := prodInl M N
  inr := prodInr M N
  inl_fst := hom_ext (by simp)
  inl_snd := hom_ext (by simp)
  inr_fst := hom_ext (by simp)
  inr_snd := hom_ext (by simp)

/-- The direct sum is a biproduct of its summands. -/
def prodIsBilimit : (prodBinaryBicone M N).IsBilimit :=
  isBinaryBilimitOfTotal _ (hom_ext (by
    rw [hom_add, hom_comp, hom_comp, hom_id]
    exact LinearMap.ext fun z => Prod.fst_add_snd z))

instance : HasBinaryBiproducts (FilteredFrobeniusModule.{v} σ ϖ) where
  has_binary_biproduct M N := HasBinaryBiproduct.mk ⟨_, prodIsBilimit M N⟩

/-- The direct sum is supported in `[a, b]` iff both summands are. -/
theorem isSupportedIn_prod_iff (a b : ℤ) :
    (prod M N).IsSupportedIn a b ↔ M.IsSupportedIn a b ∧ N.IsSupportedIn a b := by
  simp only [isSupportedIn_iff, Submodule.prod_eq_top_iff, Submodule.prod_eq_bot_iff]
  tauto

/-- The direct sum is generating iff both summands are. -/
theorem isGenerating_prod_iff :
    (prod M N).IsGenerating ↔ M.IsGenerating ∧ N.IsGenerating := by
  refine ⟨fun h => ⟨h.of_surjective (prodFst M N) LinearMap.fst_surjective,
    h.of_surjective (prodSnd M N) LinearMap.snd_surjective⟩, fun ⟨hM, hN⟩ => ?_⟩
  rw [isGenerating_iff] at hM hN ⊢
  refine top_le_iff.1 fun z _ => ?_
  rw [← Prod.fst_add_snd z]
  refine add_mem ((prodInl M N).map_span_range_phi_le ?_) ((prodInr M N).map_span_range_phi_le ?_)
  · exact ⟨z.1, hM ▸ Submodule.mem_top, rfl⟩
  · exact ⟨z.2, hN ▸ Submodule.mem_top, rfl⟩

end TauCeti.FilteredFrobeniusModule
