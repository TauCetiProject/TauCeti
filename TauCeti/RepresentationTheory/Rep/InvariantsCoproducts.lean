/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.Invariants
import TauCeti.RepresentationTheory.Rep.Colimits

/-!
# Invariants commute with coproducts

For a group `G` and a commutative ring `k`, Mathlib's functor `Rep.invariantsFunctor k G` of
`G`-invariants preserves coproducts: the `G`-invariants of a direct sum of representations are the
direct sum of the `G`-invariants. No hypothesis on `G` is needed.

The comparison map `⨁ j, (f j)^G → (∐ f)^G` is injective because the coproduct projections
`Sigma.π f j` are equivariant and split the inclusions. It is surjective because a vector `x` of
`∐ f` is a finite sum of vectors from the summands (`TauCeti.Rep.iSup_range_eq_top_of_isColimit`),
so `x = ∑ j ∈ s, Sigma.ι f j (Sigma.π f j x)` for a finite set `s`, and every component
`Sigma.π f j x` of an invariant vector `x` is invariant.

## Main definitions

* `Rep.sigmaInvariantsEquiv f`: the linear equivalence `⨁ j, (f j)^G ≃ₗ[k] (∐ f)^G` induced by
  the coproduct inclusions.

## Main results

* `Rep.preservesColimitsOfShape_discrete_invariantsFunctor`: `Rep.invariantsFunctor k G`
  preserves coproducts indexed by any type in the universe of the representations.
-/

public section

open CategoryTheory Limits DirectSum

universe w u v

namespace Rep

variable {k : Type u} [CommRing k] {G : Type v} [Group G] {α : Type w}

section

variable [DecidableEq α] (f : α → Rep.{w} k G)

/-- The map `⨁ j, (f j)^G → (∐ f)^G` induced by the coproduct inclusions. -/
noncomputable def sigmaInvariantsMap :
    (⨁ j, (f j).ρ.invariants) →ₗ[k] (∐ f).ρ.invariants :=
  toModule k α _ fun j ↦ ((invariantsFunctor k G).map (Sigma.ι f j)).hom

@[simp]
theorem coe_sigmaInvariantsMap_lof (j : α) (v : (f j).ρ.invariants) :
    (sigmaInvariantsMap f (lof k α (fun j ↦ (f j).ρ.invariants) j v)).val =
      (Sigma.ι f j).hom v.val := by
  rw [sigmaInvariantsMap, toModule_lof, invariantsFunctor_map_hom_apply_coe]

@[simp]
theorem coe_sigmaInvariantsMap_of (j : α) (v : (f j).ρ.invariants) :
    (sigmaInvariantsMap f (DirectSum.of (fun j ↦ (f j).ρ.invariants) j v)).val =
      (Sigma.ι f j).hom v.val := by
  rw [← lof_eq_of k, coe_sigmaInvariantsMap_lof]

/-- The coproduct projections recover the components: the `i`-th projection of the image of `d`
is the `i`-th component of `d`. -/
@[simp]
theorem sigma_π_sigmaInvariantsMap (d : ⨁ j, (f j).ρ.invariants) (i : α) :
    (Sigma.π f i).hom (sigmaInvariantsMap f d).val = (d i).val := by
  induction d using DirectSum.induction_on with
  | zero => simp
  | of j v =>
    rw [coe_sigmaInvariantsMap_of, ← Rep.comp_apply, Sigma.ι_π]
    by_cases hji : j = i
    · subst hji
      simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm hji)]
      simp [hji]
  | add d e hd he => simp [hd, he]

theorem sigmaInvariantsMap_injective : Function.Injective (sigmaInvariantsMap f) := by
  refine (injective_iff_map_eq_zero _).2 fun d hd ↦ DFinsupp.ext fun i ↦ Subtype.ext ?_
  simpa [hd] using (sigma_π_sigmaInvariantsMap f d i).symm

omit [DecidableEq α] in
/-- On the summands indexed by `t`, the endomorphism `∑ j ∈ t, π_j ≫ ι_j` of a coproduct is the
identity. -/
private theorem sigma_ι_comp_sum_π_comp_ι {C : Type*} [Category* C] [Preadditive C]
    {β : Type*} [DecidableEq β] (g : β → C) [HasCoproduct g] {t : Finset β} {i : β}
    (hi : i ∈ t) : Sigma.ι g i ≫ ∑ j ∈ t, Sigma.π g j ≫ Sigma.ι g j = Sigma.ι g i := by
  rw [Preadditive.comp_sum, Finset.sum_eq_single_of_mem i hi]
  · simp
  · intro j _ hj
    rw [Sigma.ι_π_of_ne_assoc _ (Ne.symm hj), zero_comp]

theorem sigmaInvariantsMap_surjective : Function.Surjective (sigmaInvariantsMap f) := by
  rintro ⟨x, hx⟩
  -- The components of an invariant vector are invariant, by equivariance of the projections.
  have hπ (j : α) : (Sigma.π f j).hom x ∈ (f j).ρ.invariants := fun g ↦ by
    rw [← Rep.hom_comm_apply, hx g]
  -- `x` lies in the span of finitely many summands.
  have htop : ⨆ j : Discrete α, LinearMap.range (Sigma.ι f j.as).hom.toLinearMap = ⊤ :=
    TauCeti.Rep.iSup_range_eq_top_of_isColimit (coproductIsCoproduct f)
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 <| htop.ge (Submodule.mem_top (x := x))
  set t := s.image Discrete.as
  -- On those summands, `∑ j ∈ t, π_j ≫ ι_j` is the identity.
  have hx' : x ∈ LinearMap.ker (𝟙 (∐ f) - ∑ j ∈ t, Sigma.π f j ≫ Sigma.ι f j).hom.toLinearMap := by
    refine IsConcreteLE.le_iff.1 (iSup₂_le fun i hi ↦ ?_) hs
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, Representation.IntertwiningMap.toLinearMap_apply,
      Representation.IntertwiningMap.toLinearMap_apply, ← Rep.comp_apply, Preadditive.comp_sub,
      Category.comp_id, sigma_ι_comp_sum_π_comp_ι f (Finset.mem_image_of_mem Discrete.as hi),
      sub_self]
    simp
  rw [LinearMap.mem_ker] at hx'
  simp only [sub_hom, sum_hom, hom_comp, hom_id] at hx'
  refine ⟨∑ j ∈ t, lof k α (fun j ↦ (f j).ρ.invariants) j ⟨_, hπ j⟩, Subtype.ext ?_⟩
  simp only [map_sum, Submodule.coe_sum, coe_sigmaInvariantsMap_lof]
  rw [eq_comm, ← sub_eq_zero]
  simpa [Representation.IntertwiningMap.sum_apply] using hx'

/-- **Invariants of a coproduct**: the coproduct inclusions induce a linear equivalence
`⨁ j, (f j)^G ≃ₗ[k] (∐ f)^G`. -/
noncomputable def sigmaInvariantsEquiv : (⨁ j, (f j).ρ.invariants) ≃ₗ[k] (∐ f).ρ.invariants :=
  .ofBijective (sigmaInvariantsMap f)
    ⟨sigmaInvariantsMap_injective f, sigmaInvariantsMap_surjective f⟩

@[simp]
theorem sigmaInvariantsEquiv_apply (d : ⨁ j, (f j).ρ.invariants) :
    sigmaInvariantsEquiv f d = sigmaInvariantsMap f d :=
  LinearEquiv.ofBijective_apply _ _

/-- The components of the preimage of an invariant vector `x` of `∐ f` are its images under the
coproduct projections. -/
@[simp]
theorem coe_sigmaInvariantsEquiv_symm_apply (x : (∐ f).ρ.invariants) (i : α) :
    ((sigmaInvariantsEquiv f).symm x i).val = (Sigma.π f i).hom x.val := by
  conv_rhs => rw [← (sigmaInvariantsEquiv f).apply_symm_apply x]
  rw [sigmaInvariantsEquiv_apply, sigma_π_sigmaInvariantsMap]

/-- The `G`-invariants of a coproduct form a coproduct of the `G`-invariants of the summands. -/
noncomputable def isColimitInvariantsCofan :
    IsColimit (Cofan.mk ((invariantsFunctor k G).obj (∐ f))
      fun j ↦ (invariantsFunctor k G).map (Sigma.ι f j)) :=
  IsColimit.ofIsoColimit (ModuleCat.coproductCoconeIsColimit
      fun j ↦ (invariantsFunctor k G).obj (f j))
    (Cofan.ext (sigmaInvariantsEquiv f).toModuleIso fun j ↦ by
      ext v
      simp only [ModuleCat.coproductCocone, Cofan.inj, Cofan.mk_ι_app, ModuleCat.hom_comp,
        LinearEquiv.toModuleIso_hom, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe]
      exact Subtype.ext (coe_sigmaInvariantsMap_lof f j v))

end

variable (k G α) in
/-- **Invariants preserve coproducts**: the functor of `G`-invariants preserves coproducts
indexed by any type in the universe of the representations. -/
instance preservesColimitsOfShape_discrete_invariantsFunctor :
    PreservesColimitsOfShape (Discrete α) (invariantsFunctor.{w} k G) := by
  classical
  have (f : α → Rep.{w} k G) : PreservesColimit (Discrete.functor f) (invariantsFunctor k G) :=
    preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
      ((isColimitMapCoconeCofanMkEquiv _ _ _).symm (isColimitInvariantsCofan f))
  exact preservesColimitsOfShape_of_discrete _

end Rep
