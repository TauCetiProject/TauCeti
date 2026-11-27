/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Endomorphism
public import TauCeti.AlgebraicGeometry.AdicSpace.NormedField
public import TauCeti.Analysis.Normed.Field.CompletedAlgClosure.Galois
public import TauCeti.RingTheory.Huber.Pair.PowerBounded

/-!
# Automorphisms of the completed algebraic closure as an adic space

For a complete nontrivially normed ultrametric field `K`, let `C` be its completed algebraic
closure. Each element of the absolute Galois group acts on `Spa(C, C°)` over `Spa(K, K°)`
through `Field.absoluteGaloisGroup.toContinuousAlgEquiv`. The affinoid morphism correspondence
`AdicSpace.ofPairHomEquiv` identifies every endomorphism over the base with one of these maps.
The resulting anti-isomorphism gives the right action on this adic space used to construct
the left action on cohomology.

## References

* A. J. de Jong and M. van der Put, *Étale cohomology of rigid analytic spaces*,
  Documenta Math. 1 (1996), §3.6.
-/

public section

noncomputable section

open CategoryTheory
open TauCeti TauCeti.AdicSpace TauCeti.Huber

universe u

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The structure map `Spa(C, C°) ⟶ Spa(K, K°)` induced by the inclusion of the base field into
its completed algebraic closure. -/
def TauCeti.CompletedAlgClosure.adicPoint (K : Type u) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] :
    ofNormedField (CompletedAlgClosure K) ⟶ ofNormedField K :=
  comapOfPair _ _ (Pair.powerBoundedHom (algebraMap K (CompletedAlgClosure K))
    (continuous_algebraMap K (CompletedAlgClosure K)))

/-- The structure map induces the inclusion `K → C` on the rings of the affinoid pairs. -/
@[simp]
theorem TauCeti.CompletedAlgClosure.ofPairHomEquiv_adicPoint :
    (ofPairHomEquiv _ _ (adicPoint K)).toRingHom = algebraMap K (CompletedAlgClosure K) := by
  simp [adicPoint]

namespace Field.absoluteGaloisGroup

/-- The map of `Spa(C, C°)` induced contravariantly by the continuous extension of a Galois
automorphism to `C`. -/
def toAdicPointHom (σ : Field.absoluteGaloisGroup K) :
    ofNormedField (CompletedAlgClosure K) ⟶ ofNormedField (CompletedAlgClosure K) :=
  comapOfPair _ _ (Pair.powerBoundedHom σ.toContinuousAlgEquiv.toAlgEquiv.toRingHom
    σ.toContinuousAlgEquiv.continuous)

/-- Recovering the ring map of `σ.toAdicPointHom` gives the continuous extension of `σ`. -/
@[simp]
theorem ofPairHomEquiv_toAdicPointHom (σ : Field.absoluteGaloisGroup K) :
    (ofPairHomEquiv _ _ σ.toAdicPointHom).toRingHom =
      σ.toContinuousAlgEquiv.toAlgEquiv.toRingHom := by
  simp [toAdicPointHom]

/-- The adic map of a Galois element lies over the base field. -/
@[reassoc (attr := simp)]
theorem toAdicPointHom_comp_adicPoint (σ : Field.absoluteGaloisGroup K) :
    σ.toAdicPointHom ≫ CompletedAlgClosure.adicPoint K = CompletedAlgClosure.adicPoint K := by
  apply (ofPairHomEquiv _ _).injective
  apply Pair.Hom.ext
  exact RingHom.ext fun x ↦ by
    simpa only [ofPairHomEquiv_comp, Pair.Hom.toRingHom_comp, ofPairHomEquiv_toAdicPointHom,
      CompletedAlgClosure.ofPairHomEquiv_adicPoint, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      ContinuousAlgEquiv.coe_toAlgEquiv] using
      σ.toContinuousAlgEquiv.toAlgEquiv.commutes x

/-- The identity Galois automorphism induces the identity adic map. -/
@[simp]
theorem toAdicPointHom_one :
    (1 : Field.absoluteGaloisGroup K).toAdicPointHom = 𝟙 _ := by
  apply (ofPairHomEquiv _ _).injective
  apply Pair.Hom.ext
  simp [ContinuousAlgEquiv.refl]

/-- Passage to the adic spectrum reverses composition. -/
theorem toAdicPointHom_mul (σ τ : Field.absoluteGaloisGroup K) :
    (σ * τ).toAdicPointHom = σ.toAdicPointHom ≫ τ.toAdicPointHom := by
  apply (ofPairHomEquiv _ _).injective
  exact Pair.Hom.ext (RingHom.ext fun x ↦ by simp)

/-- A Galois automorphism induces an isomorphism of the adic geometric point. -/
instance isIso_toAdicPointHom (σ : Field.absoluteGaloisGroup K) : IsIso σ.toAdicPointHom :=
  ⟨⟨σ⁻¹.toAdicPointHom,
    by rw [← toAdicPointHom_mul, mul_inv_cancel, toAdicPointHom_one],
    by rw [← toAdicPointHom_mul, inv_mul_cancel, toAdicPointHom_one]⟩⟩

/-- Distinct Galois elements induce distinct maps of the adic geometric point. -/
theorem toAdicPointHom_injective :
    Function.Injective (toAdicPointHom (K := K)) := by
  intro σ τ h
  apply toContinuousAlgEquiv_injective
  apply ContinuousAlgEquiv.ext
  have hh := congrArg (fun f ↦ (ofPairHomEquiv _ _ f).toRingHom) h
  simpa using congrArg DFunLike.coe hh

end Field.absoluteGaloisGroup

namespace TauCeti.CompletedAlgClosure

open Field.absoluteGaloisGroup

/-- Every endomorphism of `Spa(C, C°)` over `Spa(K, K°)` comes from a unique element of the
absolute Galois group of `K`. -/
theorem existsUnique_toAdicPointHom
    (f : ofNormedField (CompletedAlgClosure K) ⟶ ofNormedField (CompletedAlgClosure K))
    (hf : f ≫ adicPoint K = adicPoint K) :
    ∃! σ : Field.absoluteGaloisGroup K, σ.toAdicPointHom = f := by
  let φ := ofPairHomEquiv _ _ f
  have hφ (x : K) : φ.toRingHom (algebraMap K (CompletedAlgClosure K) x) =
      algebraMap K (CompletedAlgClosure K) x := by
    have h := congrArg (fun g ↦ (ofPairHomEquiv _ _ g).toRingHom) hf
    simpa [φ] using RingHom.congr_fun h x
  let g : CompletedAlgClosure K →A[K] CompletedAlgClosure K :=
    { toAlgHom := { φ.toRingHom with commutes' := hφ }
      cont := φ.continuous_toRingHom }
  obtain ⟨σ, hσ⟩ := g.exists_eq_absoluteGaloisGroup_toContinuousAlgEquiv
  have heq : σ.toAdicPointHom = f := by
    apply (ofPairHomEquiv _ _).injective
    exact Pair.Hom.ext (RingHom.ext fun x ↦ by
      rw [ofPairHomEquiv_toAdicPointHom]
      exact (congrFun hσ x).symm)
  exact ⟨σ, heq, fun τ hτ ↦ toAdicPointHom_injective (hτ.trans heq.symm)⟩

/-- The absolute Galois group is anti-isomorphic to the group of automorphisms of the adic
geometric point over `Spa(K, K°)`. Its elements act through their continuous extensions. -/
def adicPointAutMulEquiv (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Field.absoluteGaloisGroup K ≃* (Aut (Over.mk (adicPoint K)))ᵐᵒᵖ := by
  let act : Field.absoluteGaloisGroup K →* (Aut (Over.mk (adicPoint K)))ᵐᵒᵖ :=
    { toFun := fun σ ↦ MulOpposite.op <| Aut.of <| Over.isoMk
        (asIso σ.toAdicPointHom)
        (toAdicPointHom_comp_adicPoint σ)
      map_one' := by
        apply MulOpposite.unop_injective
        apply Aut.ext
        apply Iso.ext
        exact Over.OverMorphism.ext toAdicPointHom_one
      map_mul' := fun σ τ ↦ by
        apply MulOpposite.unop_injective
        apply Aut.ext
        apply Iso.ext
        exact Over.OverMorphism.ext (toAdicPointHom_mul σ τ) }
  exact MulEquiv.ofBijective act
    ⟨fun σ τ h ↦ toAdicPointHom_injective
        (congrArg (fun a ↦ (MulOpposite.unop a).asIso.hom.left) h),
      fun a ↦ by
        obtain ⟨σ, hσ, _⟩ := existsUnique_toAdicPointHom a.unop.asIso.hom.left
          (Over.w a.unop.asIso.hom)
        refine ⟨σ, ?_⟩
        apply MulOpposite.unop_injective
        apply Aut.ext
        apply Iso.ext
        exact Over.OverMorphism.ext hσ⟩

/-- The anti-isomorphism sends a Galois element to the adic map of its continuous extension. -/
@[simp]
theorem adicPointAutMulEquiv_apply_hom_left (σ : Field.absoluteGaloisGroup K) :
    (adicPointAutMulEquiv K σ).unop.asIso.hom.left = σ.toAdicPointHom :=
  (rfl)

end TauCeti.CompletedAlgClosure
