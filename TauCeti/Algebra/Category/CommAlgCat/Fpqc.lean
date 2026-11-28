/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import TauCeti.Algebra.Category.CommAlgCat.Fppf

/-!
# The affine fpqc site

The topology on opposite commutative `R`-algebras is induced by the big fpqc topology over
`Spec R` along relative spectrum. In particular it uses all commutative `R`-algebras,
including nonreduced ones. The subcanonical big fpqc topology induces a subcanonical
topology along the fully faithful relative spectrum functor, which is continuous for the
induced topology. Thus affine schemes define sheaves on it.
The construction follows `TauCeti.CommAlgCat.fppfTopology` for the fpqc topology.

## References

* The Stacks Project, Tag 022A, the fpqc topology.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.CommAlgCat

universe u

/-- The fpqc topology on affine schemes over `Spec R`, presented on opposite `R`-algebras. -/
noncomputable def fpqcTopology (R : Type u) [CommRing R] :
    GrothendieckTopology (CommAlgCat.{u} R)ᵒᵖ :=
  (algSpec (CommRingCat.of R)).inducedTopology
    (Scheme.fpqcTopology.over (Spec (CommRingCat.of R)))

/-- The affine fpqc topology is induced from the big fpqc topology over the base scheme. -/
theorem fpqcTopology_def (R : Type u) [CommRing R] :
    fpqcTopology R = (algSpec (CommRingCat.of R)).inducedTopology
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) := (rfl)

/-- Affine representable presheaves are fpqc sheaves. -/
noncomputable instance fpqcTopology_subcanonical (R : Type u) [CommRing R] :
    (fpqcTopology R).Subcanonical := by
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  rw [fpqcTopology_def]
  exact GrothendieckTopology.subcanonical_of_full_of_faithful
    (algSpec (CommRingCat.of R)) _ (Scheme.fpqcTopology.over (Spec (CommRingCat.of R)))

/-- Restricting an fpqc sheaf over `Spec R` to affine schemes gives an affine fpqc sheaf. -/
instance isContinuous_algSpec_fpqc (R : Type u) [CommRing R] :
    (algSpec (CommRingCat.of R)).IsContinuous (fpqcTopology R)
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) := by
  rw [fpqcTopology_def]
  infer_instance

/-- Relative spectra are cover-dense for the big fpqc topology over the base scheme. -/
instance isCoverDense_algSpec_fpqc (R : Type u) [CommRing R] :
    (algSpec (CommRingCat.of R)).IsCoverDense
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) where
  is_cover U := by
    rw [GrothendieckTopology.mem_over_iff]
    apply Scheme.fppfTopology_le_fpqcTopology
    exact (GrothendieckTopology.mem_over_iff _ _).mp
      (Functor.is_cover_of_isCoverDense (algSpec (CommRingCat.of R))
        (Scheme.fppfTopology.over (Spec (CommRingCat.of R))) U)

/-- An affine sieve covers exactly when its image under relative spectrum covers. -/
theorem mem_fpqcTopology_iff (R : Type u) [CommRing R]
    {A : (CommAlgCat.{u} R)ᵒᵖ} (S : Sieve A) :
    S ∈ fpqcTopology R A ↔ S.functorPushforward (algSpec (CommRingCat.of R)) ∈
      (Scheme.fpqcTopology.over (Spec (CommRingCat.of R))) _ := by
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).full
  let _ := (algSpec.fullyFaithful (R := CommRingCat.of R)).faithful
  exact Functor.mem_inducedTopology_iff_of_isCoverDense _ _ _

/-- A faithfully flat algebra map gives a singleton cover of the affine fpqc site. -/
theorem _root_.CommAlgCat.Hom.generate_singleton_op_mem_fpqcTopology {R : Type u} [CommRing R]
    {A B : CommAlgCat.{u} R} (φ : A ⟶ B) (hflat : φ.hom.toRingHom.FaithfullyFlat) :
    Sieve.generate (Presieve.singleton φ.op) ∈ fpqcTopology R (Opposite.op A) := by
  let ψ := ((algSpec (CommRingCat.of R)).map φ.op).left
  have hψ : Flat ψ ∧ Surjective ψ := (flat_and_surjective_SpecMap_iff _).2 hflat
  have : Flat ψ := hψ.1
  have : Surjective ψ := hψ.2
  have : QuasiCompact ψ :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)))
  rw [mem_fpqcTopology_iff, ← Presieve.ofArrows_pUnit.{0}]
  -- The generated presieve is the ofArrows sieve used by the pushforward API.
  change Sieve.functorPushforward _ (Sieve.ofArrows _ _) ∈ _
  rw [Sieve.functorPushforward_ofArrows, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  exact Precoverage.generate_mem_toGrothendieck (by
    rw [Presieve.ofArrows_pUnit]
    exact ψ.singleton_mem_fpqcPrecoverage)

end TauCeti.CommAlgCat
