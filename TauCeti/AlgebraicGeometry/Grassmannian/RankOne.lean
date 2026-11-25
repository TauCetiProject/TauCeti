/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra
public import TauCeti.RingTheory.Grassmannian.Chart.RankOne

/-!
# The charts of the rank-one Grassmannian as standard opens of `Proj (Sym M)`

Let `M` be a module over a commutative ring `R`. The rank-one Grassmannian `G(1, M)` over `Spec R`
(`Module.Grassmannian.scheme R M 1`) is glued from the charts `Spec C_x`, `x ∈ M`, where
`C_x = ChartAlgebra R (fun _ : Fin 1 ↦ x)`, and the projective spectrum `Proj (Sym M)` of the
symmetric algebra is covered by the standard opens `D₊(x)` of the linear forms `x ∈ M`
(`TauCeti.SymmetricAlgebra.iSup_basicOpen_ι_eq_top`). This file identifies the two covers chart by
chart, over `Spec R`: the open immersion

`Module.Grassmannian.chartToProj R x : Spec C_x ⟶ Proj (Sym M)`

is `Spec` of the inverse of the ring isomorphism
`Module.Grassmannian.ChartAlgebra.awayEquiv R x : C_x ≃ₐ[R] Sym(M)_(x)` followed by
the standard chart `Proj.awayι` of `D₊(x)`. Its image is `D₊(x)`
(`Module.Grassmannian.opensRange_chartToProj`), it lies over `Spec R`
(`Module.Grassmannian.chartToProj_projToSpec`), and the images of the charts cover
`Proj (Sym M)` (`Module.Grassmannian.iSup_opensRange_chartToProj`).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TauCeti.SymmetricAlgebra

namespace Module.Grassmannian

variable (R : Type u) [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The chart of the rank-one Grassmannian `G(1, M)` at `x ∈ M`, as the standard open `D₊(x)` of
`Proj (Sym M)`: `Spec` of the inverse of `ChartAlgebra.awayEquiv R x` followed by the standard
chart `Proj.awayι`. -/
noncomputable def chartToProj (x : M) :
    Spec (.of (ChartAlgebra R (fun _ : Fin 1 ↦ x))) ⟶ Proj (homogeneousSubmodule R M) :=
  Spec.map (ChartAlgebra.awayEquiv R x).toRingEquiv.toCommRingCatIso.inv ≫
    Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
      (ι_mem_homogeneousSubmodule R M x) one_pos

theorem chartToProj_def (x : M) :
    chartToProj R x = Spec.map (ChartAlgebra.awayEquiv R x).toRingEquiv.toCommRingCatIso.inv ≫
      Proj.awayι (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x)
        (ι_mem_homogeneousSubmodule R M x) one_pos :=
  (rfl)

instance (x : M) : IsOpenImmersion (chartToProj R x) := by
  rw [chartToProj_def]
  infer_instance

/-- The image of the chart of `G(1, M)` at `x` in `Proj (Sym M)` is the standard open `D₊(x)`. -/
theorem opensRange_chartToProj (x : M) :
    (chartToProj R x).opensRange =
      Proj.basicOpen (homogeneousSubmodule R M) (SymmetricAlgebra.ι R M x) := by
  simp only [chartToProj_def, Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

/-- The chart of `G(1, M)` at `x`, mapped to `Proj (Sym M)`, lies over `Spec R`: followed by the
structure morphism of `Proj (Sym M)` it is the structure morphism of the chart. -/
@[reassoc (attr := simp)]
theorem chartToProj_projToSpec (x : M) :
    chartToProj R x ≫ projToSpec R M =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartAlgebra R (fun _ : Fin 1 ↦ x)))) := by
  rw [chartToProj_def, Category.assoc, awayι_projToSpec, ← Spec.map_comp]
  congr 1
  ext r
  exact (ChartAlgebra.awayEquiv R x).symm.commutes r

/-- The images of the charts of `G(1, M)` cover `Proj (Sym M)`. -/
theorem iSup_opensRange_chartToProj :
    ⨆ x : M, (chartToProj R x).opensRange = ⊤ := by
  simp_rw [opensRange_chartToProj]
  exact iSup_basicOpen_ι_eq_top R M id (by simp)

end Module.Grassmannian
