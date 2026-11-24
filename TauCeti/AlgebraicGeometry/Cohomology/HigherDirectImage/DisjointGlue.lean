/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.DisjointGlue
import TauCeti.AlgebraicGeometry.Scheme.Opens

/-!
# Higher direct images of modules prescribed on a disjoint cover

For pairwise disjoint opens `U j` of `X` and a module `F j` on each `U j`, the cohomology of
`disjointGlue U F` on `U j` is the cohomology of `F j`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyOnDisjointGlueIso`).

Let `f : X ⟶ S` be quasi-compact and quasi-separated, and `V j` a cover of `S` by pairwise disjoint
opens, indexed by a possibly infinite type. A quasicoherent module `F j` on each preimage
`f⁻¹(V j)` defines the module `disjointGlue (f⁻¹ V) F` on `X`
(`TauCeti.AlgebraicGeometry.Scheme.Modules.disjointGlue`). Over an affine `V j`, its higher direct
image `Rⁿ f_*` has the sections `Hⁿ(f⁻¹(V j), F j)`
(`AlgebraicGeometry.Scheme.Hom.higherDirectImageSectionsDisjointGlueAddEquiv`), so `Rⁿ f_*` is
nonzero as soon as one of these cohomology groups is
(`AlgebraicGeometry.Scheme.Hom.nontrivial_higherDirectImage_disjointGlue`).

This is the setting of the standard example of a qcqs morphism to a base that is not
quasi-compact whose higher direct images are nonzero in infinitely many degrees: for
`S = ⨿ₙ Spec k`, `X = ⨿ₙ ℙⁿ` and `F n = O(-n-1)`, `Rⁿ f_*` is nonzero for every `n`.
-/

public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open scoped Function

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {J : Type u} {U : J → X.Opens} (F : ∀ j, (U j).toScheme.Modules)

/-- The cohomology of `disjointGlue U F` on `U j` is the cohomology of `F j`. -/
def cohomologyOnDisjointGlueIso (hdisj : Pairwise (Disjoint on U)) (j : J) (n : ℕ) :
    cohomologyOn (disjointGlue U F) n (U j) ≅ (cohomologyFunctor (U j).toScheme n).obj (F j) :=
  eqToIso (by rw [Scheme.Opens.opensRange_ι]) ≪≫
    cohomologyOnOpensRangeIso (U j).ι (disjointGlue U F) n ≪≫
      (cohomologyFunctor (U j).toScheme n).mapIso (restrictDisjointGlueIso F hdisj j)

end TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) {J : Type u} {V : J → S.Opens}

/-- **Higher direct images of a module prescribed on a disjoint cover.** For a quasi-compact
quasi-separated `f : X ⟶ S`, a cover of `S` by pairwise disjoint opens `V j` and a
quasicoherent module `F j` on each `f⁻¹(V j)`, the sections over an affine `V j` of the higher
direct image `Rⁿ f_*` of `disjointGlue (f⁻¹ V) F` are `Hⁿ(f⁻¹(V j), F j)`. -/
def higherDirectImageSectionsDisjointGlueAddEquiv [QuasiCompact f] [QuasiSeparated f]
    (hdisj : Pairwise (Disjoint on V)) (hcover : ⨆ j, V j = ⊤)
    (F : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules) [∀ j, (F j).IsQuasicoherent] (n : ℕ) (j : J)
    (hV : IsAffineOpen (V j)) :
    Γ((f.higherDirectImage n).obj (disjointGlue (fun j ↦ f ⁻¹ᵁ V j) F), V j) ≃+
      Cohomology (F j) n :=
  haveI := isQuasicoherent_disjointGlue F (f.pairwise_disjoint_preimage hdisj)
    (f.iSup_preimage_eq_top hcover)
  (f.higherDirectImageSectionsAddEquiv _ n hV).symm.trans
    (cohomologyOnDisjointGlueIso F (f.pairwise_disjoint_preimage hdisj) j
      n).addCommGroupIsoToAddEquiv

/-- In the situation of `higherDirectImageSectionsDisjointGlueAddEquiv`, the higher direct image
`Rⁿ f_*` of `disjointGlue (f⁻¹ V) F` has a nonzero section over an affine `V j` as soon as
`Hⁿ(f⁻¹(V j), F j)` is nonzero. -/
theorem nontrivial_higherDirectImage_disjointGlue [QuasiCompact f] [QuasiSeparated f]
    (hdisj : Pairwise (Disjoint on V)) (hcover : ⨆ j, V j = ⊤)
    (F : ∀ j, (f ⁻¹ᵁ V j).toScheme.Modules) [∀ j, (F j).IsQuasicoherent] (n : ℕ) (j : J)
    (hV : IsAffineOpen (V j)) [Nontrivial (Cohomology (F j) n)] :
    Nontrivial Γ((f.higherDirectImage n).obj (disjointGlue (fun j ↦ f ⁻¹ᵁ V j) F), V j) :=
  (f.higherDirectImageSectionsDisjointGlueAddEquiv hdisj hcover F n j hV).toEquiv.nontrivial

end AlgebraicGeometry.Scheme.Hom
