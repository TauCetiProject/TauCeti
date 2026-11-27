/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.AlgebraicGeometry.Sites.Nisnevich.QcEtale
public import TauCeti.RingTheory.Etale.Field

/-!
# Checks for the quasi-compact small Nisnevich site

The identity of `X` and the empty étale `X`-scheme are objects of `X.QcEtale`, and the empty sieve
covers the empty object. For an étale field extension `k → K` of degree other than `1` the
morphism `Spec K ⟶ Spec k` is an object of `(Spec k).QcEtale` whose generated sieve does not cover
the final object, since `k → K` is not an isomorphism on residue fields; in particular this holds
for `Spec ℂ ⟶ Spec ℝ`.
-/

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme Module

public section

universe u

namespace TauCeti.Examples.QcEtale

variable (X : Scheme.{u})

/-- The identity of `X`, as an object of `X.QcEtale`. -/
noncomputable def idObj : X.QcEtale :=
  Scheme.QcEtale.mk (𝟙 X)

/-- The empty étale `X`-scheme, as an object of `X.QcEtale`. -/
noncomputable def emptyObj : X.QcEtale :=
  have : QuasiCompact (Scheme.emptyTo X) := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  Scheme.QcEtale.mk (Scheme.emptyTo X)

variable [QuasiSeparatedSpace X]

-- The empty sieve covers the empty object.
example : (⊥ : Sieve (emptyObj X)) ∈ X.qcNisnevichTopology (emptyObj X) := by
  refine GrothendieckTopology.superset_covering _ ?_
    ((Scheme.ofArrows_mem_qcNisnevichTopology_iff (U := emptyObj X)
      (V := fun i : PEmpty.{1} ↦ i.elim) (fun i ↦ i.elim)).2
      -- The underlying scheme of `emptyObj X` is `∅` by definition of `emptyObj`, `QcEtale.mk` and
      -- `Over.mk`, so a point of it is a point of `∅`.
      ⟨fun i ↦ i.elim, fun s ↦ (IsEmpty.false (α := (∅ : Scheme.{u})) s).elim⟩)
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun i ↦ i.elim

variable (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.Etale k K]

/-- `Spec K ⟶ Spec k` for an étale field extension, as an object of `(Spec k).QcEtale`. -/
noncomputable def specObj : (Spec (.of k)).QcEtale :=
  have := quasiCompact_of_compactSpace (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  Scheme.QcEtale.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The structure morphism of `specObj k K`, as a morphism of `(Spec k).QcEtale` to the final
object. -/
noncomputable def specHom : specObj k K ⟶ idObj (Spec (.of k)) :=
  Scheme.QcEtale.homMk (MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (Category.comp_id _) trivial)

-- For an étale extension `k → K` of degree other than `1`, `{Spec K ⟶ Spec k}` does not cover the
-- final object of `(Spec k).QcEtale`.
example (h : finrank k K ≠ 1) :
    Sieve.ofArrows (fun _ : PUnit.{u + 1} ↦ specObj k K) (fun _ ↦ specHom k K) ∉
      (Spec (.of k)).qcNisnevichTopology (idObj (Spec (.of k))) := by
  rw [Scheme.ofArrows_mem_qcNisnevichTopology_iff]
  -- The underlying morphism of `specHom k K` is `Spec K ⟶ Spec k` by definition of `specHom`,
  -- `QcEtale.homMk` and `Over.homMk`; the sources of the family are `Spec K` only by definition
  -- too, so this step is definitional rather than a rewrite.
  exact not_isNisnevichCovering_specMap_algebraMap_of_finrank_ne_one k K h

attribute [local instance] Algebra.Etale.of_isSeparable

-- `Spec ℂ ⟶ Spec ℝ` is the structure morphism of the object `specObj ℝ ℂ` of `(Spec ℝ).QcEtale`.
example : ((Scheme.QcEtale.ι _).obj (specObj ℝ ℂ)).hom =
    Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)) :=
  rfl

-- `Spec ℂ ⟶ Spec ℝ` lies in the basis `(Spec ℝ).QcEtale`, but the sieve it generates does not
-- cover the final object.
example :
    Sieve.ofArrows (fun _ : PUnit.{1} ↦ specObj ℝ ℂ) (fun _ ↦ specHom ℝ ℂ) ∉
      (Spec (.of ℝ)).qcNisnevichTopology (idObj (Spec (.of ℝ))) := by
  rw [Scheme.ofArrows_mem_qcNisnevichTopology_iff]
  -- As above, the underlying morphism of `specHom ℝ ℂ` is `Spec ℂ ⟶ Spec ℝ` by definition.
  exact not_isNisnevichCovering_specMap_algebraMap_of_finrank_ne_one ℝ ℂ
    (by simp [Complex.finrank_real_complex])

end TauCeti.Examples.QcEtale
