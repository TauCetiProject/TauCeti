/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.ExteriorPower.MapSemilinear
public import TauCeti.RingTheory.Dagger.Omega.Map

/-!
# Exterior forms of universally finite differentials

Records degreewise vanishing and functorial pullback `formsMap` for exterior powers
`⋀[A]^q (Omega R A)` without requiring the exterior derivative or the de Rham complex: over a
complete ultrametric normed field `K`, the exterior powers of `Omega K (washnitzerAlgebra σ K)`
vanish in degrees strictly above `Nat.card σ`, and every homomorphism `f : A →ₐ[K] B` into a
`K`-dagger algebra induces `formsMap f q : ⋀[A]^q (Omega K A) →ₗ[K] ⋀[B]^q (Omega K B)`.
-/

public section

namespace TauCeti.Dagger.Omega

section Functoriality

variable {K A B C : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
  [IsDaggerAlgebra K B] [IsDaggerAlgebra K C]

/-- The `K`-linear pullback of overconvergent `q`-forms along `f : A →ₐ[K] B`. -/
noncomputable def formsMap (f : A →ₐ[K] B) (q : ℕ) :
    ⋀[A]^q (Omega K A) →ₗ[K] ⋀[B]^q (Omega K B) where
  toFun := exteriorPower.mapSemilinear q (mapSemilinear f)
  map_add' := map_add _
  map_smul' r ω := by
    have hfr : f.toRingHom (algebraMap K A r) = algebraMap K B r := f.commutes r
    rw [← algebraMap_smul A r ω, LinearMap.map_smulₛₗ, hfr, algebraMap_smul, RingHom.id_apply]

@[simp] theorem formsMap_apply (f : A →ₐ[K] B) (q : ℕ) (ω : ⋀[A]^q (Omega K A)) :
    formsMap f q ω = exteriorPower.mapSemilinear q (mapSemilinear f) ω := (rfl)

@[simp] theorem formsMap_id [IsDaggerAlgebra K A] (q : ℕ) :
    formsMap (AlgHom.id K A) q = LinearMap.id :=
  LinearMap.ext fun ω ↦ (congrArg (exteriorPower.mapSemilinear q · ω) mapSemilinear_id).trans
    (exteriorPower.mapSemilinear_id_apply q ω)

theorem formsMap_comp (g : B →ₐ[K] C) (f : A →ₐ[K] B) (q : ℕ) :
    formsMap (g.comp f) q = (formsMap g q) ∘ₗ (formsMap f q) := LinearMap.ext fun ω ↦ by
  rw [formsMap_apply, mapSemilinear_comp, exteriorPower.mapSemilinear_comp_apply,
    LinearMap.comp_apply, formsMap_apply, formsMap_apply]

end Functoriality

section Washnitzer

variable {σ K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- On `washnitzerAlgebra σ K` over a complete ultrametric normed field `K`, every exterior power
of `Omega` above `Nat.card σ` vanishes. -/
theorem subsingleton_forms_washnitzer_of_card_lt [Finite σ] {q : ℕ} (hq : Nat.card σ < q) :
    Subsingleton (⋀[washnitzerAlgebra σ K]^q (Omega K (washnitzerAlgebra σ K))) :=
  exteriorPower.subsingleton_of_span_eq_top_of_card_lt (washnitzerBasis σ K)
    (washnitzerBasis σ K).span_eq q hq

end Washnitzer

end TauCeti.Dagger.Omega
