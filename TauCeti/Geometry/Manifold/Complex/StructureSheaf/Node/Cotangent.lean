/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Node.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Cotangent
import TauCeti.LinearAlgebra.Basis.Semilinear
import TauCeti.Analysis.Normed.Module.FiniteDimension
import Mathlib.RingTheory.Finiteness.Prod

/-!
# The cotangent space of an analytic node

The native cotangent space `𝔪/𝔪²` of the branch-pair node ring has one independent
cotangent direction from each branch. More generally, for two finite-dimensional complex
manifold branches, differentiation in charts identifies it with the product of their complex
dual model spaces. Scalars are compared using evaluation on the node's residue field.

The key local-algebra statement is that a node germ lies in `𝔪²` exactly when both branch
germs lie in their respective squared maximal ideals. Thus there is no first-order relation
between the branches, even though the product of their vanishing germs is zero. This gives
the two cotangent directions used in the local deformation theory of an ordinary node,
without choosing a hypersurface presentation.

The branch comparisons reuse `OpenPartialHomeomorph.holomorphicCotangentEquiv`, composed
with Mathlib's `Ideal.mapCotangent` on the branch restrictions. The squared-ideal criterion
from `Node.LocalRing` gives injectivity of their product.

## References

* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open IsLocalRing IsManifold
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf.nodeLocalRing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {X Y : Type} [TopologicalSpace X] [ChartedSpace E X]
  [TopologicalSpace Y] [ChartedSpace F Y]
  {p : X} {q : Y}

local notation "N" => nodeLocalRing 𝓘(ℂ, E) 𝓘(ℂ, F) p q
local notation "A" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, E) X)) p
local notation "B" => TopCat.Presheaf.stalk (C := CommRingCat)
  (TopCat.Sheaf.presheaf (holomorphicStructureSheaf 𝓘(ℂ, F) Y)) q
local notation "π₁" => fst 𝓘(ℂ, E) 𝓘(ℂ, F) p q
local notation "π₂" => snd 𝓘(ℂ, E) 𝓘(ℂ, F) p q

variable {e : OpenPartialHomeomorph X E} {e' : OpenPartialHomeomorph Y F}
  (hp : p ∈ e.source) (hq : q ∈ e'.source)
  (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X) (he' : e' ∈ maximalAtlas 𝓘(ℂ, F) ω Y)
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

/-- Restriction to the branches followed by their existing cotangent comparisons. -/
private def cotangentMap : CotangentSpace N →+ (StrongDual ℂ E × StrongDual ℂ F) :=
  ((e.holomorphicCotangentEquiv p hp he).toAddMonoidHom.comp
    (Ideal.mapCotangent (maximalIdeal N) (maximalIdeal A) (π₁).toIntAlgHom
      (maximalIdeal_comap π₁).ge).toAddMonoidHom).prod
    ((e'.holomorphicCotangentEquiv q hq he').toAddMonoidHom.comp
      (Ideal.mapCotangent (maximalIdeal N) (maximalIdeal B) (π₂).toIntAlgHom
        (maximalIdeal_comap π₂).ge).toAddMonoidHom)

private theorem cotangentMap_toBranchCotangent (s : maximalIdeal N) :
    cotangentMap hp hq he he' (Ideal.toCotangent _ s) =
      (e.holomorphicCotangentEquiv p hp he
        (Ideal.toCotangent _ ⟨π₁ s, (maximalIdeal_comap π₁).ge s.property⟩),
      e'.holomorphicCotangentEquiv q hq he'
        (Ideal.toCotangent _ ⟨π₂ s, (maximalIdeal_comap π₂).ge s.property⟩)) := (rfl)

@[simp]
private theorem cotangentMap_toCotangent (s : maximalIdeal N) :
    cotangentMap hp hq he he' (Ideal.toCotangent _ s) =
      (e.holomorphicStalkFDeriv p hp (π₁ s),
        e'.holomorphicStalkFDeriv q hq (π₂ s)) := by
  simp [cotangentMap_toBranchCotangent]

private theorem cotangentMap_smul (c : ResidueField N) (v : CotangentSpace N) :
    cotangentMap hp hq he he' (c • v) =
      (RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q)) c •
        cotangentMap hp hq he he' v := by
  obtain ⟨a, rfl⟩ := residue_surjective c
  rw [RingHom.coe_coe, residueFieldEquiv_residue, ← IsLocalRing.ResidueField.algebraMap_eq,
    IsScalarTower.algebraMap_smul]
  obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
  rw [← map_smul, cotangentMap_toBranchCotangent, cotangentMap_toBranchCotangent]
  have h₁ : (⟨π₁ ((a • s : maximalIdeal N) : N),
      (maximalIdeal_comap π₁).ge (a • s).property⟩ : maximalIdeal A) =
      π₁ a • ⟨π₁ s, (maximalIdeal_comap π₁).ge s.property⟩ := by
    ext
    simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
  have h₂ : (⟨π₂ ((a • s : maximalIdeal N) : N),
      (maximalIdeal_comap π₂).ge (a • s).property⟩ : maximalIdeal B) =
      π₂ a • ⟨π₂ s, (maximalIdeal_comap π₂).ge s.property⟩ := by
    ext
    simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
  rw [h₁, h₂, (Ideal.toCotangent (maximalIdeal A)).map_smul,
    (Ideal.toCotangent (maximalIdeal B)).map_smul]
  apply Prod.ext
  · rw [← IsScalarTower.algebraMap_smul (ResidueField A) (π₁ a)
      (Ideal.toCotangent _ ⟨π₁ s, (maximalIdeal_comap π₁).ge s.property⟩),
      LinearEquiv.map_smulₛₗ]
    simp [IsLocalRing.ResidueField.algebraMap_eq]
  · rw [← IsScalarTower.algebraMap_smul (ResidueField B) (π₂ a)
      (Ideal.toCotangent _ ⟨π₂ s, (maximalIdeal_comap π₂).ge s.property⟩),
      LinearEquiv.map_smulₛₗ]
    simp [IsLocalRing.ResidueField.algebraMap_eq]

/-- Differentiation identifies the cotangent space of the node ring with the two branch
cotangent model spaces, semilinearly along evaluation on the residue field. -/
def cotangentEquiv :
    CotangentSpace N ≃ₛₗ[RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q)]
      (StrongDual ℂ E × StrongDual ℂ F) :=
  LinearEquiv.ofBijective
    (σ₂₁ := RingHomClass.toRingHom (residueFieldEquiv 𝓘(ℂ, E) 𝓘(ℂ, F) p q).symm)
    { toFun := cotangentMap hp hq he he'
      map_add' := map_add _
      map_smul' := cotangentMap_smul hp hq he he' }
    ⟨by
      rw [injective_iff_map_eq_zero]
      intro v hv
      obtain ⟨s, rfl⟩ := Ideal.toCotangent_surjective _ v
      apply (Ideal.toCotangent_eq_zero _ s).2
      rw [mem_maximalIdeal_pow_iff]
      simp only [LinearMap.coe_mk, AddHom.coe_mk] at hv
      rw [cotangentMap_toBranchCotangent] at hv
      have h₁ := (e.holomorphicCotangentEquiv p hp he).map_eq_zero_iff.mp
        (congrArg Prod.fst hv)
      have h₂ := (e'.holomorphicCotangentEquiv q hq he').map_eq_zero_iff.mp
        (congrArg Prod.snd hv)
      exact ⟨(Ideal.toCotangent_eq_zero _ _).1 h₁,
        (Ideal.toCotangent_eq_zero _ _).1 h₂⟩,
      fun ℓ ↦ ⟨Ideal.toCotangent _ ⟨mk
        (e.holomorphicLinearCoordinateGerm he p ℓ.1 hp)
        (e'.holomorphicLinearCoordinateGerm he' q ℓ.2 hq) (by simp), by
          simp [maximalIdeal_eq_ker_eval, ← eval_fst]⟩, by
            simp only [LinearMap.coe_mk, AddHom.coe_mk]
            simp⟩⟩

/-- On a vanishing germ the cotangent comparison is differentiation of its branch germs. -/
@[simp]
theorem cotangentEquiv_toCotangent (s : maximalIdeal N) :
    cotangentEquiv hp hq he he' (Ideal.toCotangent _ s) =
      (e.holomorphicStalkFDeriv p hp (π₁ s),
        e'.holomorphicStalkFDeriv q hq (π₂ s)) :=
  cotangentMap_toCotangent hp hq he he' s

/-- The inverse comparison glues the two centered linear coordinate germs. -/
@[simp]
theorem cotangentEquiv_symm_apply (ℓ : StrongDual ℂ E × StrongDual ℂ F) :
    (cotangentEquiv hp hq he he').symm ℓ = Ideal.toCotangent _ ⟨mk
      (e.holomorphicLinearCoordinateGerm he p ℓ.1 hp)
      (e'.holomorphicLinearCoordinateGerm he' q ℓ.2 hq) (by simp), by
        simp [maximalIdeal_eq_ker_eval, ← eval_fst]⟩ := by
  apply (cotangentEquiv hp hq he he').injective
  simp

include hp hq he he' in
/-- Local branch charts make the node cotangent space finite-dimensional over its residue field. -/
theorem finiteDimensional_cotangentSpace_of_mem_maximalAtlas :
    FiniteDimensional (ResidueField N) (CotangentSpace N) :=
  Module.Finite.of_surjective (cotangentEquiv hp hq he he').symm.toLinearMap
    (cotangentEquiv hp hq he he').symm.surjective

include hp hq he he' in
/-- The embedding dimension of the branch-pair ring is the sum of the dimensions of the
branches. In particular, two curve branches give embedding dimension two. -/
theorem finrank_cotangentSpace_of_mem_maximalAtlas :
    Module.finrank (ResidueField N) (CotangentSpace N) =
      Module.finrank ℂ E + Module.finrank ℂ F := by
  rw [(cotangentEquiv hp hq he he').finrank_eqₛₗ, Module.finrank_prod,
    ContinuousLinearMap.dual_finrank_eq, ContinuousLinearMap.dual_finrank_eq]

section Manifolds

variable [IsManifold 𝓘(ℂ, E) 1 X] [IsManifold 𝓘(ℂ, F) 1 Y]

/-- The cotangent space at a node of finite-dimensional complex manifolds is finite-dimensional. -/
instance finiteDimensional_cotangentSpace :
    FiniteDimensional (ResidueField N) (CotangentSpace N) := by
  let : IsManifold 𝓘(ℂ, E) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let : IsManifold 𝓘(ℂ, F) ω Y := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  exact finiteDimensional_cotangentSpace_of_mem_maximalAtlas
    (mem_chart_source E p) (mem_chart_source F q)
    (chart_mem_maximalAtlas p (I := 𝓘(ℂ, E)) (n := ω))
    (chart_mem_maximalAtlas q (I := 𝓘(ℂ, F)) (n := ω))

/-- The embedding dimension at a node of complex manifolds is the sum of their dimensions. -/
@[simp]
theorem finrank_cotangentSpace :
    Module.finrank (ResidueField N) (CotangentSpace N) =
      Module.finrank ℂ E + Module.finrank ℂ F := by
  let : IsManifold 𝓘(ℂ, E) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  let : IsManifold 𝓘(ℂ, F) ω Y := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  exact finrank_cotangentSpace_of_mem_maximalAtlas (mem_chart_source E p) (mem_chart_source F q)
    (chart_mem_maximalAtlas p (I := 𝓘(ℂ, E)) (n := ω))
    (chart_mem_maximalAtlas q (I := 𝓘(ℂ, F)) (n := ω))

end Manifolds

section Curves

variable {C D : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ) 1 C]
  [TopologicalSpace D] [ChartedSpace ℂ D] [IsManifold 𝓘(ℂ) 1 D]

/-- An ordinary analytic node has two independent cotangent directions over its residue field. -/
theorem finrank_cotangentSpace_eq_two (p : C) (q : D) :
    Module.finrank (ResidueField (nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) p q))
      (CotangentSpace (nodeLocalRing 𝓘(ℂ) 𝓘(ℂ) p q)) = 2 := by
  simp

end Curves

end TauCeti.holomorphicStructureSheaf.nodeLocalRing
