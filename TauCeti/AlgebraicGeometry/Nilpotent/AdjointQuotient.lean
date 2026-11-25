/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.NilpotentCone
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The adjoint quotient and its scheme-theoretic zero fibre

The invariant polynomial ring defines the adjoint quotient of the Lie algebra scheme from
`TauCeti.Algebra.AlgebraicGroup.Tangent.Scheme`. Its fibre over the origin is the spectrum of the
quotient by `nilpotentConeIdeal`, with its full, possibly nonreduced, scheme structure. The pullback
theorem identifies this presentation with the scheme-theoretic zero fibre, without characteristic
or reductivity assumptions.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace TauCeti

universe u

variable (k : Type u) [Field k] (H : Type u) [CommRing H] [HopfAlgebra k H]
  [Module.Finite k (Bialgebra.CotangentSpace k H)]

local notation "𝔤" => Module.Dual k (Bialgebra.CotangentSpace k H)
local notation "P" => SymmetricAlgebra k (Module.Dual k 𝔤)

/-- The adjoint quotient, whose coordinate ring is the ring of invariant polynomial functions. -/
abbrev adjointQuotient : Scheme := Spec (.of (adjointInvariantPolynomials k H))

/-- The nilpotent cone with its scheme-theoretic, possibly nonreduced, structure. -/
abbrev nilpotentCone : Scheme := Spec (.of (P ⧸ nilpotentConeIdeal k H))

/-- The adjoint quotient morphism is induced by inclusion of invariant functions. -/
def adjointQuotientMap : lieAlgebraScheme k H ⟶ adjointQuotient k H :=
  (lieAlgebraSchemeIso k H).hom ≫
    Spec.map (CommRingCat.ofHom (adjointInvariantPolynomials k H).val.toRingHom)

/-- Pullback along the adjoint quotient is the inclusion of invariant functions. -/
theorem adjointQuotientMap_eq : adjointQuotientMap k H =
    (lieAlgebraSchemeIso k H).hom ≫
      Spec.map (CommRingCat.ofHom (adjointInvariantPolynomials k H).val.toRingHom) := by
  rfl

/-- The origin of the adjoint quotient is evaluation of invariants at the zero vector. -/
def adjointQuotientOrigin : Spec (.of k) ⟶ adjointQuotient k H :=
  Spec.map (CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv.comp
    (adjointInvariantPolynomials k H).val).toRingHom)

/-- Pullback to the origin takes the constant term of an invariant polynomial. -/
theorem adjointQuotientOrigin_eq : adjointQuotientOrigin k H =
    Spec.map (CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv.comp
      (adjointInvariantPolynomials k H).val).toRingHom) := by
  rfl

/-- The closed inclusion of the nilpotent cone into the Lie algebra scheme. -/
def nilpotentConeι : nilpotentCone k H ⟶ lieAlgebraScheme k H :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H))) ≫
    (lieAlgebraSchemeIso k H).inv

/-- The nilpotent-cone inclusion is induced by the quotient homomorphism. -/
theorem nilpotentConeι_eq : nilpotentConeι k H =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H))) ≫
      (lieAlgebraSchemeIso k H).inv := by
  rfl

/-- The structural morphism of the nilpotent cone over its ground field. -/
def nilpotentConeToSpec : nilpotentCone k H ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (P ⧸ nilpotentConeIdeal k H)))

/-- The structural morphism is the spectrum of the scalar map on the quotient ring. -/
theorem nilpotentConeToSpec_eq : nilpotentConeToSpec k H =
    Spec.algebraMap k (P ⧸ nilpotentConeIdeal k H) := by
  rfl

/-- The nilpotent-cone inclusion preserves the structural morphisms to the ground field. -/
theorem nilpotentConeι_comp_toSpec :
    nilpotentConeι k H ≫ (lieAlgebraSchemeIso k H).hom ≫ Spec.algebraMap k P =
      nilpotentConeToSpec k H := by
  rw [nilpotentConeι_eq, Category.assoc, Iso.inv_hom_id_assoc,
    nilpotentConeToSpec_eq, ← Spec.map_comp]
  exact congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (Ideal.Quotient.mk_comp_algebraMap k (nilpotentConeIdeal k H))

/-- On the nilpotent cone an invariant polynomial equals its value at the origin. -/
theorem nilpotentCone_quotient_invariant (p : adjointInvariantPolynomials k H) :
    Ideal.Quotient.mk (nilpotentConeIdeal k H) (p : P) =
      algebraMap k (P ⧸ nilpotentConeIdeal k H)
        (SymmetricAlgebra.algebraMapInv (p : P)) := by
  rw [← Ideal.Quotient.mk_algebraMap]
  apply Ideal.Quotient.eq.mpr
  apply mem_nilpotentConeIdeal_of_mem_adjointInvariantPolynomials
  · exact (adjointInvariantPolynomials k H).sub_mem p.property
      ((adjointInvariantPolynomials k H).algebraMap_mem _)
  · simp

/-- The coordinate ring of the nilpotent cone is the pushout along evaluation at the origin. -/
theorem isPushout_nilpotentConeCoordinates :
    IsPushout (CommRingCat.ofHom (adjointInvariantPolynomials k H).val.toRingHom)
      (CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv.comp
        (adjointInvariantPolynomials k H).val).toRingHom)
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H)))
      (CommRingCat.ofHom (algebraMap k (P ⧸ nilpotentConeIdeal k H))) := by
  have comm :
      CommRingCat.ofHom (adjointInvariantPolynomials k H).val.toRingHom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H)) =
        CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv.comp
          (adjointInvariantPolynomials k H).val).toRingHom ≫
          CommRingCat.ofHom (algebraMap k (P ⧸ nilpotentConeIdeal k H)) := by
    ext p
    exact nilpotentCone_quotient_invariant k H p
  let desc (s : PushoutCocone
      (CommRingCat.ofHom (adjointInvariantPolynomials k H).val.toRingHom)
      (CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv.comp
        (adjointInvariantPolynomials k H).val).toRingHom)) :
      CommRingCat.of (P ⧸ nilpotentConeIdeal k H) ⟶ s.pt :=
    CommRingCat.ofHom (Ideal.Quotient.lift (nilpotentConeIdeal k H) s.inl.hom (by
      have hker : nilpotentConeIdeal k H ≤ RingHom.ker s.inl.hom :=
        nilpotentConeIdeal_le_iff.mpr fun p hp hp₀ ↦ by
          have h := ConcreteCategory.congr_hom s.condition ⟨p, hp⟩
          simpa [hp₀] using h
      exact fun p hp ↦ hker hp))
  have fac (s) : CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H)) ≫
      desc s = s.inl := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    rfl
  refine ⟨⟨comm⟩, ⟨PushoutCocone.IsColimit.mk comm desc fac ?_ ?_⟩⟩
  · intro s
    ext r
    have h := ConcreteCategory.congr_hom (fac s) (algebraMap k P r)
    have hs := ConcreteCategory.congr_hom s.condition
      (algebraMap k (adjointInvariantPolynomials k H) r)
    exact h.trans (by simpa using hs)
  · intro s m hm _
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective p
    exact (ConcreteCategory.congr_hom hm p).trans
      (ConcreteCategory.congr_hom (fac s) p).symm

/-- The nilpotent cone is the scheme-theoretic zero fibre of the adjoint quotient. -/
theorem isPullback_nilpotentCone :
    IsPullback (nilpotentConeι k H) (nilpotentConeToSpec k H)
      (adjointQuotientMap k H) (adjointQuotientOrigin k H) := by
  apply (isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_nilpotentConeCoordinates k H)).of_iso
    (Iso.refl _) (lieAlgebraSchemeIso k H).symm (Iso.refl _) (Iso.refl _)
  · simp [nilpotentConeι_eq]
  · simp [nilpotentConeToSpec_eq]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom,
      adjointQuotientMap_eq, Iso.inv_hom_id_assoc]
  · simp [adjointQuotientOrigin_eq]

/-- The scheme-theoretic nilpotent cone is closed in the Lie algebra scheme. -/
instance isClosedImmersion_nilpotentConeι : IsClosedImmersion (nilpotentConeι k H) := by
  let : IsClosedImmersion (Spec.map
      (CommRingCat.ofHom (Ideal.Quotient.mk (nilpotentConeIdeal k H)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [nilpotentConeι_eq]
  infer_instance

end TauCeti
