/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.DisjointGlue

/-!
# Higher direct images of modules prescribed on a disjoint cover

Let `f : X ⟶ S` be quasi-compact and quasi-separated, and `V j` a cover of `S` by pairwise disjoint
affine opens, indexed by a possibly infinite type. A quasicoherent module `F j` on each preimage
`f⁻¹(V j)` defines the module `disjointGlue (f⁻¹ V) F` on `X`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue`). Its higher direct image `Rⁿ f_*` has,
over `V j`, the sections `Hⁿ(f⁻¹(V j), F j)`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.higherDirectImageSectionsDisjointGlueAddEquiv`), so
`Rⁿ f_*` is nonzero as soon as one of these cohomology groups is
(`TauCeti.AlgebraicGeometry.Scheme.Modules.nontrivial_higherDirectImage_disjointGlue`).

For `S = ⨿ₖ Spec k`, `X = ⨿ₖ ℙᵏ` and `F k = O(-k-1)`, this makes `Rᵏ f_*` nonzero for every `k`:
a qcqs morphism to a base that is not quasi-compact can have nonzero higher direct images in
infinitely many degrees.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped Function

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) {J : Type u} {V : J → S.Opens}

/-- Preimages of pairwise disjoint opens are pairwise disjoint. -/
private theorem pairwise_disjoint_preimage (hdisj : Pairwise (Disjoint on V)) :
    Pairwise (Disjoint on fun j ↦ f ⁻¹ᵁ V j) := fun i j hij ↦ by
  rw [Function.onFun, disjoint_iff, ← Scheme.Hom.preimage_inf, disjoint_iff.mp (hdisj hij),
    Scheme.Hom.preimage_bot]

/-- **Higher direct images of a module prescribed on a disjoint cover.** For a quasi-compact
quasi-separated `f : X ⟶ S`, a cover of `S` by pairwise disjoint affine opens `V j` and a
quasicoherent module `F j` on each `f⁻¹(V j)`, the sections over `V j` of the higher direct image
`Rⁿ f_*` of `disjointGlue (f⁻¹ V) F` are `Hⁿ(f⁻¹(V j), F j)`. -/
def higherDirectImageSectionsDisjointGlueAddEquiv [QuasiCompact f] [QuasiSeparated f]
    (hV : ∀ j, IsAffineOpen (V j)) (hdisj : Pairwise (Disjoint on V)) (hcover : ⨆ j, V j = ⊤)
    (F : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules) [∀ j, (F j).IsQuasicoherent] (n : ℕ) (j : J) :
    Γ((f.higherDirectImage n).obj (disjointGlue (fun j ↦ f ⁻¹ᵁ V j) F), V j) ≃+
      Scheme.Modules.Cohomology (F j) n :=
  haveI := isQuasicoherent_disjointGlue F (pairwise_disjoint_preimage f hdisj)
    (f.iSup_preimage_eq_top hcover)
  (f.higherDirectImageSectionsAddEquiv _ n (hV j)).symm.trans
    (cohomologyOnDisjointGlueIso F (pairwise_disjoint_preimage f hdisj) j
      n).addCommGroupIsoToAddEquiv

/-- In the situation of `higherDirectImageSectionsDisjointGlueAddEquiv`, the higher direct image
`Rⁿ f_*` of `disjointGlue (f⁻¹ V) F` has a nonzero section over `V j` as soon as
`Hⁿ(f⁻¹(V j), F j)` is nonzero. -/
theorem nontrivial_higherDirectImage_disjointGlue [QuasiCompact f] [QuasiSeparated f]
    (hV : ∀ j, IsAffineOpen (V j)) (hdisj : Pairwise (Disjoint on V)) (hcover : ⨆ j, V j = ⊤)
    (F : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules) [∀ j, (F j).IsQuasicoherent] (n : ℕ) (j : J)
    [Nontrivial (Scheme.Modules.Cohomology (F j) n)] :
    Nontrivial Γ((f.higherDirectImage n).obj (disjointGlue (fun j ↦ f ⁻¹ᵁ V j) F), V j) :=
  (higherDirectImageSectionsDisjointGlueAddEquiv f hV hdisj hcover F n j).toEquiv.nontrivial

end TauCeti.AlgebraicGeometry.Scheme.Modules
