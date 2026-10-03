/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
import TauCeti.FieldTheory.Normal.Embeddings
import Mathlib.GroupTheory.IndexNormal

/-!
# Fixing subgroups of conjugate embeddings

Two embeddings of a finite separable extension into a separable closure differ by an
automorphism of that closure. Their images are therefore conjugate intermediate fields, and
the Galois correspondence carries them to conjugate open subgroups of the absolute Galois
group. This is the subgroup comparison used when transporting restriction, corestriction,
and the Evens norm between different choices of embedding.

The automorphism carrying one embedding to the other comes from the transitive action on
embeddings in `TauCeti.FieldTheory.Normal.Embeddings`. Conjugacy of the fixing subgroups
follows from the corresponding stabilizer conjugacy theorem. The finer statement
`TauCeti.exists_galoisSubgroupEquiv_eq_conj` says that the two identifications of the absolute
Galois group of `L` with these subgroups differ by conjugation by a single element of `G_K`.
-/

public section

namespace TauCeti

universe u v

variable (K : Type u) [Field K] (L : Type v) [Field L] [Algebra K L]

/-- The open subgroups of `G_K` fixing two embedded copies of a finite extension `L/K`
are conjugate. The conjugating automorphism extends the natural `K`-algebra isomorphism
between the two copies of `L`. -/
theorem galoisSubgroup_conj [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) :
    ∃ g : AbsoluteGaloisGroup K,
      (galoisSubgroup K L τ).toSubgroup =
        (galoisSubgroup K L σ).toSubgroup.map (MulAut.conj g).toMonoidHom := by
  simpa only [galoisSubgroup_toSubgroup] using
    AlgHom.fixingSubgroup_fieldRange_conj σ τ

/-- **The identifications of `G_L` with the subgroups cut out by two embeddings differ by an
inner automorphism of `G_K`**: for `K`-embeddings `σ τ : L →ₐ[K] Kˢ` there is `γ : G_K` with
`galoisSubgroupEquiv K L τ x = γ * galoisSubgroupEquiv K L σ x * γ⁻¹` for every `x : G_L`. The
element `γ` is the automorphism of `Kˢ` carrying the identification of separable closures attached
to `σ` to the one attached to `τ`. -/
theorem exists_galoisSubgroupEquiv_eq_conj [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) :
    ∃ γ : AbsoluteGaloisGroup K, ∀ x : AbsoluteGaloisGroup L,
      (galoisSubgroupEquiv K L τ x : AbsoluteGaloisGroup K) =
        γ * galoisSubgroupEquiv K L σ x * γ⁻¹ := by
  let eσ := separableClosureRingEquiv K L σ
  let eτ := separableClosureRingEquiv K L τ
  -- `γ = eτ ∘ eσ⁻¹` fixes `K`, so it is an element of `G_K`.
  let γ : AbsoluteGaloisGroup K := AlgEquiv.ofRingEquiv (f := eσ.symm.trans eτ) fun c => by
    rw [RingEquiv.trans_apply, eσ.symm_apply_eq.2 (separableClosureRingEquiv_algebraMap_base
      K L σ c).symm, separableClosureRingEquiv_algebraMap_base]
  have hγ (w : SeparableClosure L) : γ (eσ w) = eτ w := by simp [γ]
  have hγ' (w : SeparableClosure L) : γ⁻¹ (eτ w) = eσ w := by
    rw [← hγ, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  refine ⟨γ, fun x => AlgEquiv.ext fun y => ?_⟩
  obtain ⟨w, rfl⟩ := eτ.surjective y
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hγ',
    galoisSubgroupEquiv_apply_separableClosureRingEquiv,
    galoisSubgroupEquiv_apply_separableClosureRingEquiv, hγ]

/-- **The subgroup cut out by a quadratic extension is independent of its embedding.**
For a quadratic extension `L/K`, any two embeddings of `L` into the separable closure have the
same fixing subgroup of `G_K`. -/
theorem galoisSubgroup_eq_of_finrank_eq_two [FiniteDimensional K L]
    (σ τ : L →ₐ[K] SeparableClosure K) (hL : Module.finrank K L = 2) :
    galoisSubgroup K L σ = galoisSubgroup K L τ := by
  -- The two fixing subgroups are conjugate, and an index-two subgroup is normal.
  apply OpenSubgroup.toSubgroup_injective
  obtain ⟨g, hg⟩ := galoisSubgroup_conj K L σ τ
  let _ : (galoisSubgroup K L σ).toSubgroup.Normal :=
    Subgroup.normal_of_index_eq_two ((galoisSubgroup_index K L σ).trans hL)
  rw [hg]
  simpa only [MulEquiv.toMonoidHom_eq_coe] using
    (Subgroup.Normal.map_conj_eq (H := (galoisSubgroup K L σ).toSubgroup) g).symm

end TauCeti
