/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Local algebras with a retraction to the base

Let `A` be an `R`-algebra with an `R`-algebra retraction `g : A →ₐ[R] R`, the algebraic form of a
section of `Spec A → Spec R` through a point. The structure map `R → A` is then local, and when
`R` and `A` are local rings the maximal ideal of `A` splits as the extension `𝔪_R A` of the
maximal ideal of `R` plus the kernel of `g`. In particular the closed fibre `k ⊗[R] A`, where `k`
is the residue field of `R`, has residue field `k`.

## Main results

* `AlgHom.isLocalHom_algebraMap`: the structure map `R → A` is local.
* `AlgHom.maximalIdeal_eq_map_sup_ker`: `𝔪_A = 𝔪_R A + ker g`, for local rings `R` and `A`.
* `AlgHom.bijective_algebraMap_residueField_tensor`: the residue field of the closed fibre
  `k ⊗[R] A` is `k`.
-/

public section

open IsLocalRing Ideal TensorProduct

namespace AlgHom

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The structure map of an algebra with a retraction is a local homomorphism. -/
theorem isLocalHom_algebraMap (g : A →ₐ[R] R) : IsLocalHom (algebraMap R A) :=
  isLocalHom_of_leftInverse g fun r ↦ by simp

variable [IsLocalRing R] [IsLocalRing A]

/-- The maximal ideal of `A` is the sum of the extension of the maximal ideal of `R` and the
kernel of the retraction. -/
theorem maximalIdeal_eq_map_sup_ker (g : A →ₐ[R] R) :
    maximalIdeal A = (maximalIdeal R).map (algebraMap R A) ⊔ RingHom.ker g := by
  have := g.isLocalHom_algebraMap
  have : IsLocalHom (g : A →+* R) :=
    .of_surjective _ fun r ↦ ⟨algebraMap R A r, by simp⟩
  refine le_antisymm (fun a ha ↦ ?_) (sup_le ?_ (le_maximalIdeal (RingHom.ker_ne_top g)))
  · rw [show a = algebraMap R A (g a) + (a - algebraMap R A (g a)) by ring]
    exact Submodule.add_mem_sup (mem_map_of_mem _ (map_nonunit (g : A →+* R) a ha))
      (by simp [RingHom.mem_ker])
  · exact map_le_iff_le_comap.mpr fun r hr ↦ map_nonunit _ r hr

/-- **The closed fibre of a local algebra with a retraction has the same residue field as the
base.** If `R` and `A` are local and `A` has an `R`-algebra retraction, then the residue field
`k` of `R` maps isomorphically onto the residue field of the closed fibre `k ⊗[R] A`. -/
theorem bijective_algebraMap_residueField_tensor (g : A →ₐ[R] R)
    [IsLocalRing (ResidueField R ⊗[R] A)] :
    Function.Bijective (algebraMap (ResidueField R) (ResidueField (ResidueField R ⊗[R] A))) := by
  refine ⟨(algebraMap (ResidueField R) _).injective, fun x ↦ ?_⟩
  let ι : A →+* ResidueField R ⊗[R] A := Algebra.TensorProduct.includeRight.toRingHom
  have hι : Function.Surjective ι := TensorProduct.mk_surjective _ _ _ residue_surjective
  obtain ⟨_, rfl⟩ := residue_surjective x
  obtain ⟨a, rfl⟩ := hι ‹_›
  refine ⟨residue R (g a), ?_⟩
  -- `a` and `g a` agree modulo `ker g ≤ 𝔪_A`, which `ι` maps into the maximal ideal
  have hmem : ι (a - algebraMap R A (g a)) ∈ maximalIdeal _ :=
    map_maximalIdeal_of_surjective ι hι ▸ mem_map_of_mem ι
      (le_maximalIdeal (RingHom.ker_ne_top g) (by simp [RingHom.mem_ker]))
  rw [← residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
  rw [hmem, IsScalarTower.algebraMap_apply _ (ResidueField R ⊗[R] A),
    ResidueField.algebraMap_eq, Algebra.TensorProduct.algebraMap_apply]
  simp [ι]

end AlgHom
