/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal

/-!
# Formal `A∞` algebras

The cohomology `H(A)` of an `A∞` algebra `A` is a graded nonunital algebra, hence an `A∞`
algebra with zero `m₁`, the cohomology product as `m₂`, and no higher operations; this is
`AInfinityAlgebra.cohomologyAInfinityAlgebra`, and it is minimal.  The algebra `A` is *formal*
when it admits an `A∞` quasi-isomorphism to this `A∞` algebra.  Over a field every `A∞`
quasi-isomorphism has an `A∞` inverse up to homotopy, so there the direction of the
quasi-isomorphism is immaterial.
Minimal models are exactly what distinguishes the two notions: the cohomology of a minimal algebra
is the algebra itself, but formality asks in addition that the higher operations can be removed up
to quasi-isomorphism.

Formality is reflected along quasi-isomorphisms: if `A ⟶ B` is a quasi-isomorphism and `B` is
formal, then so is `A`, because a quasi-isomorphism identifies the two cohomology algebras
compatibly with their gradings.  A minimal algebra whose operations above arity two vanish is
formal, since the class map is then a strict isomorphism onto its cohomology; in particular a
graded nonunital algebra with zero differential is formal.

## Main definitions

* `TauCeti.AInfinityAlgebra.IsFormal`: existence of an `A∞` quasi-isomorphism to
  `cohomologyAInfinityAlgebra`.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.isFormal`: a minimal algebra with vanishing higher operations
  is formal, and `TauCeti.IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero` specializes this to
  graded algebras with zero differential.
* `TauCeti.AInfinityAlgebra.IsFormal.of_isQuasiIso`: formality is reflected along
  quasi-isomorphisms.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 3.4.
* T. Kadeishvili, *The algebraic structure in the homology of an `A(∞)`-algebra*.
-/

public section

namespace TauCeti

universe uR uA uB

variable {R : Type uR} {A : Type uA} {B : Type uB} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

namespace AInfinityAlgebra

/-! ### Formality -/

/-- An `A∞` algebra is **formal** when it admits an `A∞` quasi-isomorphism to its cohomology,
regarded as an `A∞` algebra whose only nonzero operation is the cohomology product `m₂`. -/
def IsFormal (𝒜 : AInfinityAlgebra R A) : Prop :=
  ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso

/-- An `A∞` algebra is formal exactly when it has a quasi-isomorphism to its cohomology `A∞`
algebra. -/
theorem isFormal_def (𝒜 : AInfinityAlgebra R A) :
    𝒜.IsFormal ↔ ∃ f : AInfinityHom 𝒜 𝒜.cohomologyAInfinityAlgebra, f.IsQuasiIso := Iff.rfl

variable {𝒜 : AInfinityAlgebra R A} {ℬ : AInfinityAlgebra R B}

/-- The map induced on cohomology by a quasi-isomorphism, as a linear equivalence. -/
private noncomputable def cohomologyLinearEquiv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    𝒜.Cohomology ≃ₗ[R] ℬ.Cohomology :=
  LinearEquiv.ofBijective (f.cohomologyMap : 𝒜.Cohomology →ₗ[R] ℬ.Cohomology)
    ((AInfinityHom.isQuasiIso_def f).1 hf)

private theorem cohomologyLinearEquiv_apply {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso)
    (c : 𝒜.Cohomology) : cohomologyLinearEquiv hf c = f.cohomologyMap c := by
  exact LinearEquiv.ofBijective_apply _ c

/-- The inverse of the map induced on cohomology by a quasi-isomorphism, as a morphism of
cohomology algebras. -/
private noncomputable def cohomologyMapInv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    ℬ.Cohomology →ₙₐ[R] 𝒜.Cohomology where
  toFun := (cohomologyLinearEquiv hf).symm
  map_smul' := (cohomologyLinearEquiv hf).symm.map_smul
  map_zero' := (cohomologyLinearEquiv hf).symm.map_zero
  map_add' := (cohomologyLinearEquiv hf).symm.map_add
  map_mul' x y := (cohomologyLinearEquiv hf).injective (by
    rw [LinearEquiv.apply_symm_apply, cohomologyLinearEquiv_apply, map_mul,
      ← cohomologyLinearEquiv_apply hf, ← cohomologyLinearEquiv_apply hf,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])

private theorem cohomologyMapInv_apply {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso)
    (c : ℬ.Cohomology) : cohomologyMapInv hf c = (cohomologyLinearEquiv hf).symm c := by
  rw [cohomologyMapInv, NonUnitalAlgHom.coe_mk]

/-- The inverse of the map induced on cohomology by a quasi-isomorphism preserves degrees. -/
private theorem cohomologyMapInv_mem {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) {p : ℤ}
    {c : ℬ.Cohomology} (hc : c ∈ ℬ.cohomologyGrading.piece p) :
    cohomologyMapInv hf c ∈ 𝒜.cohomologyGrading.piece p := by
  have he : LinearMap.IsHomogeneous (cohomologyLinearEquiv hf).toLinearMap
      𝒜.cohomologyGrading.piece ℬ.cohomologyGrading.piece 0 := by
    rw [LinearMap.isHomogeneous_def]
    intro q x hx
    rw [add_zero, LinearEquiv.coe_coe, cohomologyLinearEquiv_apply]
    exact f.cohomologyMap_mem_cohomologyGrading_piece hx
  simpa only [cohomologyMapInv_apply, add_zero, LinearEquiv.coe_coe] using
    he.linearEquiv_symm.map_mem hc

/-- A quasi-isomorphism `𝒜 ⟶ ℬ` identifies the cohomology `A∞` algebras; this is the strict
morphism in the backward direction, the inverse of the induced map on cohomology. -/
private noncomputable def cohomologyStrictHomInv {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    AInfinityStrictHom ℬ.cohomologyAInfinityAlgebra 𝒜.cohomologyAInfinityAlgebra :=
  cohomologyStrictHom (cohomologyMapInv hf) (cohomologyMapInv_mem hf)

private theorem cohomologyStrictHomInv_isQuasiIso {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) :
    (cohomologyStrictHomInv hf).toAInfinityHom.IsQuasiIso := by
  rw [AInfinityHom.isQuasiIso_iff_bijective_linearPart ℬ.isMinimal_cohomologyAInfinityAlgebra
    𝒜.isMinimal_cohomologyAInfinityAlgebra, AInfinityStrictHom.linearPart_toAInfinityHom,
    AInfinityStrictHom.coe_toLinearMap, cohomologyStrictHomInv, coe_cohomologyStrictHom,
    funext (cohomologyMapInv_apply hf)]
  exact (cohomologyLinearEquiv hf).symm.bijective

/-- Formality is reflected along quasi-isomorphisms: if `𝒜 ⟶ ℬ` is a quasi-isomorphism and `ℬ` is
formal, then `𝒜` is formal. -/
theorem IsFormal.of_isQuasiIso {f : AInfinityHom 𝒜 ℬ} (hf : f.IsQuasiIso) (hℬ : ℬ.IsFormal) :
    𝒜.IsFormal := by
  obtain ⟨g, hg⟩ := hℬ
  exact ⟨(cohomologyStrictHomInv hf).toAInfinityHom.comp (g.comp f),
    (cohomologyStrictHomInv_isQuasiIso hf).comp (hg.comp hf)⟩

namespace IsMinimal

/-- The identification of a minimal algebra with vanishing higher operations with its cohomology,
as a strict morphism to the cohomology `A∞` algebra. -/
private noncomputable def toCohomology (h : 𝒜.IsMinimal) (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) :
    AInfinityStrictHom 𝒜 𝒜.cohomologyAInfinityAlgebra where
  toLinearMap := h.cohomologyEquiv.toLinearMap
  map_mem' hx := by
    simpa only [add_zero, cohomologyAInfinityAlgebra_grading] using
      h.isHomogeneous_cohomologyEquiv.map_mem hx
  map_m' n := by
    ext x
    rw [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply]
    match n with
    | 0 => simp
    | 1 => simp [h.m_one]
    | 2 =>
      rw [cohomologyAInfinityAlgebra_m_two_apply]
      obtain ⟨a, b, rfl⟩ : ∃ a b, x = ![a, b] :=
        ⟨x 0, x 1, funext fun i ↦ by fin_cases i <;> rfl⟩
      exact h.cohomologyEquiv_m_two a b
    | n + 3 => simp [hm (n + 3) (by omega)]

/-- A minimal `A∞` algebra whose operations of arity at least three vanish is formal: the
identification with its cohomology is a strict isomorphism. -/
theorem isFormal (h : 𝒜.IsMinimal) (hm : ∀ n, 3 ≤ n → 𝒜.m n = 0) : 𝒜.IsFormal := by
  refine ⟨(h.toCohomology hm).toAInfinityHom, ?_⟩
  rw [AInfinityHom.isQuasiIso_iff_bijective_linearPart h 𝒜.isMinimal_cohomologyAInfinityAlgebra,
    AInfinityStrictHom.linearPart_toAInfinityHom]
  exact h.cohomologyEquiv.bijective

end IsMinimal

end AInfinityAlgebra

/-- The `A∞` algebra of a graded nonunital algebra with zero differential is formal. -/
theorem IsNonUnitalDGAlgebra.isFormal_toAInfinityAlgebra_zero {A : Type uA} [NonUnitalRing A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] (𝒜 : ℤ → Submodule R A)
    [SetLike.GradedMul 𝒜] [DirectSum.Decomposition 𝒜] :
    (isNonUnitalDGAlgebra_zero 𝒜 (R := R)).toAInfinityAlgebra.IsFormal :=
  ((isMinimal_toAInfinityAlgebra_iff _).2 rfl).isFormal fun _ hn ↦
    toAInfinityAlgebra_m_of_three_le _ hn

end TauCeti
