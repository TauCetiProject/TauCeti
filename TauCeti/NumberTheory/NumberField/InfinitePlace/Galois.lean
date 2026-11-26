/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Galois parametrization of infinite places

After choosing an infinite place of a Galois extension that is unramified over the base,
its fiber is in bijection with the Galois group. We use inverse Galois action so that on
embeddings the parametrization is precomposition by the automorphism, not its inverse.
When the base has only one infinite place, this parametrizes all the infinite places and
allows the group law to be transported from the Galois group.

The parametrization with a complex embedding as basepoint is used in lsernau/grh-lean,
`New/Reduction/Data/FieldsAndPlaces.lean` (`New.Parameters.galOfPlace`, at revision `72fead1`).
-/

public section

open MulAction

namespace NumberField.InfinitePlace

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The places with the same restriction as an unramified infinite place `w` are parametrized
by the Galois group via the inverse action on `w`. -/
noncomputable def galEquivPlacesOver (w : InfinitePlace L) (hw : w.IsUnramified K) :
    Gal(L/K) ≃ placesOver L (w.comap (algebraMap K L)) := by
  refine Equiv.ofBijective (fun σ ↦ ⟨σ⁻¹ • w, ?_⟩) ⟨?_, ?_⟩
  · exact liesOver_iff_comap_eq.mpr (mem_orbit_iff.mp ⟨_, rfl⟩).symm
  · intro σ τ h
    have h' : σ⁻¹ • w = τ⁻¹ • w := congrArg Subtype.val h
    have hs : τ * σ⁻¹ ∈ stabilizer Gal(L/K) w := by
      rw [mem_stabilizer_iff, mul_smul, h', smul_inv_smul]
    rwa [hw.stabilizer_eq_bot, Subgroup.mem_bot, mul_inv_eq_one, eq_comm] at hs
  · rintro ⟨v, hv⟩
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_comap_eq (liesOver_iff_comap_eq.mp hv).symm
    exact ⟨σ⁻¹, Subtype.ext (by simpa only [inv_inv] using hσ)⟩

/-- The Galois parametrization has underlying place `σ⁻¹ • w`. -/
@[simp]
theorem coe_galEquivPlacesOver_apply (w : InfinitePlace L) (hw : w.IsUnramified K)
    (σ : Gal(L/K)) :
    (w.galEquivPlacesOver hw σ : InfinitePlace L) = σ⁻¹ • w := (rfl)

/-- In the fiber of `w`, the place `σ⁻¹ • w` is labeled by `σ`. -/
@[simp]
theorem galEquivPlacesOver_symm_inv_smul (w : InfinitePlace L) (hw : w.IsUnramified K)
    (σ : Gal(L/K)) (hσ : σ⁻¹ • w ∈ placesOver L (w.comap (algebraMap K L))) :
    (w.galEquivPlacesOver hw).symm ⟨σ⁻¹ • w, hσ⟩ = σ := by
  apply (w.galEquivPlacesOver hw).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (w.coe_galEquivPlacesOver_apply hw σ).symm

/-- If the base has a unique infinite place, all infinite places of `L` are parametrized by the
Galois group, based at any unramified infinite place `w` of `L`. -/
noncomputable def galEquivOfSubsingleton [Subsingleton (InfinitePlace K)]
    (w : InfinitePlace L) (hw : w.IsUnramified K) : Gal(L/K) ≃ InfinitePlace L :=
  (w.galEquivPlacesOver hw).trans <| Equiv.subtypeUnivEquiv fun v ↦ by
    rw [placesOver, Set.mem_ofPred_eq, liesOver_iff_comap_eq]
    exact Subsingleton.elim _ _

/-- The parametrization of all places is given by the same inverse action as for a fiber. -/
@[simp]
theorem galEquivOfSubsingleton_apply [Subsingleton (InfinitePlace K)]
    (w : InfinitePlace L) (hw : w.IsUnramified K) (σ : Gal(L/K)) :
    w.galEquivOfSubsingleton hw σ = σ⁻¹ • w := by
  rw [galEquivOfSubsingleton, Equiv.trans_apply, Equiv.subtypeUnivEquiv_apply,
    coe_galEquivPlacesOver_apply]

/-- The place obtained by inverse Galois action is labeled by the acting automorphism. -/
@[simp]
theorem galEquivOfSubsingleton_symm_inv_smul [Subsingleton (InfinitePlace K)]
    (w : InfinitePlace L) (hw : w.IsUnramified K) (σ : Gal(L/K)) :
    (w.galEquivOfSubsingleton hw).symm (σ⁻¹ • w) = σ := by
  rw [← galEquivOfSubsingleton_apply w hw, Equiv.symm_apply_apply]

/-- The basepoint has Galois label `1`. -/
@[simp]
theorem galEquivOfSubsingleton_symm_self [Subsingleton (InfinitePlace K)]
    (w : InfinitePlace L) (hw : w.IsUnramified K) :
    (w.galEquivOfSubsingleton hw).symm w = 1 := by
  simpa only [inv_one, one_smul] using w.galEquivOfSubsingleton_symm_inv_smul hw 1

/-- For a parametrization based at the place of `φ`, the place indexed by `σ` is the place of
`φ ∘ σ`. -/
theorem galEquivOfSubsingleton_mk_apply [Subsingleton (InfinitePlace K)]
    (φ : L →+* ℂ) (hφ : (mk φ).IsUnramified K) (σ : Gal(L/K)) :
    (mk φ).galEquivOfSubsingleton hφ σ = mk (φ.comp σ) := by
  rw [galEquivOfSubsingleton_apply, smul_mk, AlgEquiv.aut_inv, AlgEquiv.symm_symm]

/-- The representative obtained by precomposing `φ` with the automorphism indexing `w`
induces `w`. -/
@[simp]
theorem mk_comp_galEquivOfSubsingleton_symm [Subsingleton (InfinitePlace K)]
    (φ : L →+* ℂ) (hφ : (mk φ).IsUnramified K) (w : InfinitePlace L) :
    mk (φ.comp (((mk φ).galEquivOfSubsingleton hφ).symm w : L →+* L)) = w := by
  rw [← galEquivOfSubsingleton_mk_apply φ hφ, Equiv.apply_symm_apply]

/-- An embedding extending the same restriction as `φ` is recovered by precomposing `φ`
with the automorphism indexed by its infinite place. -/
theorem eq_comp_galEquivOfSubsingleton_symm [Subsingleton (InfinitePlace K)]
    {φ ψ : L →+* ℂ} (hφ : (mk φ).IsUnramified K)
    (h : φ.comp (algebraMap K L) = ψ.comp (algebraMap K L)) :
    ψ = φ.comp (((mk φ).galEquivOfSubsingleton hφ).symm (mk ψ) : L →+* L) := by
  obtain ⟨σ, hσ⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq φ ψ h
  have hplace : (mk φ).galEquivOfSubsingleton hφ σ⁻¹ = mk ψ :=
    (galEquivOfSubsingleton_mk_apply φ hφ _).trans (congrArg mk hσ)
  rw [← hplace, Equiv.symm_apply_apply]
  exact hσ.symm

end NumberField.InfinitePlace
