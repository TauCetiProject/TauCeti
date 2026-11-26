/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.RingTheory.Etale.Field
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.QcEtale

/-!
# Checks for the quasi-compact small Nisnevich site

The identity of `X` and the empty étale `X`-scheme are objects of `X.QcEtale`, the empty sieve
covers the empty object, and for a quadratic étale field extension `k → K` the morphism
`Spec K ⟶ Spec k` is an object of `(Spec k).QcEtale` whose generated sieve does not cover the
final object, since `k → K` is not an isomorphism on residue fields. This applies to `ℝ → ℂ`.
-/

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme Module

public section

universe u

namespace TauCeti.Examples.QcEtale

variable (X : Scheme.{u}) [QuasiSeparatedSpace X]

/-- The identity of `X`, as an object of `X.QcEtale`. -/
noncomputable def idObj : X.QcEtale :=
  @Scheme.QcEtale.mk X (MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance)
    (inferInstanceAs (QuasiCompact (𝟙 X)))

/-- The empty étale `X`-scheme, as an object of `X.QcEtale`. -/
noncomputable def emptyObj : X.QcEtale :=
  @Scheme.QcEtale.mk X (MorphismProperty.Over.mk ⊤ (Scheme.emptyTo X) inferInstance)
    (quasiCompact_of_compactSpace (Scheme.emptyTo X))

-- The empty sieve covers the empty object.
example : (⊥ : Sieve (emptyObj X)) ∈ X.qcNisnevichTopology (emptyObj X) := by
  refine GrothendieckTopology.superset_covering _ ?_
    ((Scheme.ofArrows_mem_qcNisnevichTopology_iff (U := emptyObj X)
      (V := fun i : PEmpty.{1} ↦ i.elim) (fun i ↦ i.elim)).2
      ⟨fun i ↦ i.elim, fun s ↦ (IsEmpty.false (α := (∅ : Scheme.{u})) s).elim⟩)
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun i ↦ i.elim

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.Etale k K]

/-- `Spec K ⟶ Spec k` for an étale field extension, as an object of `(Spec k).QcEtale`. -/
noncomputable def specObj : (Spec (.of k)).QcEtale :=
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  @Scheme.QcEtale.mk _ (MorphismProperty.Over.mk ⊤ (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    inferInstance) (quasiCompact_of_compactSpace (Spec.map (CommRingCat.ofHom (algebraMap k K))))

/-- The structure morphism of `specObj k K`, as a morphism of `(Spec k).QcEtale` to the final
object. -/
noncomputable def specHom : specObj k K ⟶ idObj (Spec (.of k)) :=
  Scheme.QcEtale.homMk (MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (Category.comp_id _) trivial)

-- For a quadratic étale extension `k → K`, `{Spec K ⟶ Spec k}` does not cover the final object of
-- `(Spec k).QcEtale`.
example (h : finrank k K = 2) :
    Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ specObj k K) (fun _ ↦ specHom k K) ∉
      (Spec (.of k)).qcNisnevichTopology (idObj (Spec (.of k))) := by
  rw [Scheme.ofArrows_mem_qcNisnevichTopology_iff]
  intro hc
  replace hc : IsNisnevichCovering
      (fun _ : PUnit.{u + 1} ↦ Spec.map (CommRingCat.ofHom (algebraMap k K))) := hc
  obtain ⟨-, x, -, hx⟩ := hc.exists_isIso (IsLocalRing.closedPoint k)
  have := x.isPrime
  rw [RingHom.isIso_SpecMap_residueFieldMap_iff _ x _ rfl] at hx
  -- The residue field of the field `k` at its prime is `k`, so `k → K` is onto.
  have hb : Function.Bijective (algebraMap k K) := by
    refine ⟨(algebraMap k K).injective, fun y ↦ ?_⟩
    obtain ⟨w, hw⟩ := hx.2 (algebraMap K x.asIdeal.ResidueField y)
    obtain ⟨r, rfl⟩ :=
      (Ideal.algEquivResidueFieldOfField (x.asIdeal.comap (algebraMap k K))).surjective w
    refine ⟨r, (algebraMap K x.asIdeal.ResidueField).injective ?_⟩
    rw [← hw, Ideal.algEquivResidueFieldOfField_apply, Ideal.ResidueField.map_algebraMap]
  have := (LinearEquiv.ofBijective (Algebra.linearMap k K) hb).finrank_eq
  rw [Module.finrank_self] at this
  omega

-- `ℝ → ℂ` is a quadratic étale extension.
example : Algebra.Etale ℝ ℂ :=
  have : Algebra.FormallyEtale ℝ ℂ := Algebra.FormallyEtale.of_isSeparable ℝ ℂ
  have : Algebra.FinitePresentation ℝ ℂ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  ⟨inferInstance, inferInstance⟩

example : finrank ℝ ℂ = 2 := Complex.finrank_real_complex

end TauCeti.Examples.QcEtale
