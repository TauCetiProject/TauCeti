/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.AlgebraicGeometry.Morphisms.FiniteType.Over

/-!
# Zariski refinements by finite-type schemes

Over a quasi-separated base, a Zariski covering family of a finite-type scheme admits an
affine refinement whose members remain finite type over the base. The refinement is stated in
`Over S` and does not depend on any larger topology.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Every Zariski covering presieve of a finite-type scheme over a quasi-separated base admits
a refining Zariski covering family of affine finite-type schemes over the same base. -/
lemma exists_finiteType_zariski_refinement (S : Scheme.{u}) [QuasiSeparatedSpace S]
    {X : S.FiniteType}
    {R : Presieve ((MorphismProperty.Over.forget _ ⊤ S).obj X)}
    (hR : R ∈ (zariskiPrecoverage.over S) ((MorphismProperty.Over.forget _ ⊤ S).obj X)) :
    ∃ r : Presieve X,
      (∀ ⦃Y : S.FiniteType⦄ ⦃f : Y ⟶ X⦄, r f → IsAffine Y.left) ∧
      r.map (MorphismProperty.Over.forget (@LocallyOfFiniteType ⊓ @QuasiCompact) ⊤ S) ∈
      (zariskiPrecoverage.over S) ((MorphismProperty.Over.forget _ ⊤ S).obj X) ∧
        r.map (MorphismProperty.Over.forget (@LocallyOfFiniteType ⊓ @QuasiCompact) ⊤ S) ≤
          (Sieve.generate R).arrows := by
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows, ofArrows_mem_precoverage_iff] at hR
  let 𝒰 : OpenCover.{u + 1} X.left :=
    Cover.mkOfCovers ι (fun i ↦ (Y i).left) (fun i ↦ (f i).left) hR.1 hR.2
  let 𝒜 := OpenCover.affineRefinement.{u, u + 1} 𝒰
  let ρ := OpenCover.fromAffineRefinement.{u, u + 1} 𝒰
  let Z (j : 𝒜.openCover.I₀) : S.FiniteType :=
    letI : IsAffine (𝒜.openCover.X j) := isAffine_affineOpenCover X.left 𝒜 j
    FiniteType.mk (𝒜.openCover.f j ≫ X.hom)
  let g (j : 𝒜.openCover.I₀) : Z j ⟶ X :=
    MorphismProperty.Over.homMk (𝒜.openCover.f j) rfl
  refine ⟨Presieve.ofArrows Z g, ?_, ?_, ?_⟩
  · rintro _ _ ⟨j⟩
    exact isAffine_affineOpenCover X.left 𝒜 j
  · rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows, Presieve.map_ofArrows]
    exact 𝒜.openCover.mem₀
  · have haffine : Sieve.overEquiv _
        (Sieve.ofArrows
          (fun j ↦ (MorphismProperty.Over.forget _ ⊤ S).obj (Z j))
          (fun j ↦ (MorphismProperty.Over.forget _ ⊤ S).map (g j))) =
        𝒜.openCover.sieve₀ := by
      rw [Sieve.overEquiv_ofArrows]
      -- Forgetting preserves the object and arrow projections definitionally. Reduce the
      -- dependent sources `Z j` and the affine arrows `g j` together.
      rfl
    rw [Presieve.map_ofArrows, ← Sieve.generate_le_iff]
    apply (Sieve.overEquiv _).le_iff_le.mp
    rw [haffine, Sieve.overEquiv_ofArrows]
    exact ρ.sieve₀_le_sieve₀

end AlgebraicGeometry.Scheme
