/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.DisjointGlue
public import TauCeti.AlgebraicGeometry.Cohomology.ProjectiveSpace.TopDual
public import TauCeti.AlgebraicGeometry.Limits.Sigma
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Quasicoherent

/-!
# Higher direct images along `⨿ₙ ℙⁿ ⟶ ⨿ₙ Spec R` in every degree

Let `R` be a nonzero commutative ring, `S = ⨿_{n ≥ 0} Spec R` and `f : ⨿_{n ≥ 0} ℙⁿ_R ⟶ S` the
coproduct of the structure morphisms of the projective spaces `ℙⁿ_R = Proj (Sym (R^{n+1}))`. Then
`f` is quasi-compact and quasi-separated, since both properties are local on the target
(`AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap_iff`), but the base `S` is not quasi-compact.
The module `F` on `⨿ₙ ℙⁿ_R` that is `𝒪(-n-1)` on the component `ℙⁿ_R` has `Rⁿ f_* F ≠ 0` for every
`n`: over the component `Spec R` of index `n`, the sections of `Rⁿ f_* F` are
`Hⁿ(ℙⁿ_R, 𝒪(-n-1))` (`AlgebraicGeometry.Scheme.Hom.nontrivial_higherDirectImage_disjointGlue`),
which is nonzero, by the top cohomology of projective space for `n ≥ 1` and by the sections of
`𝒪(-1)` on `ℙ⁰_R = Spec R` for `n = 0`. This shows that no uniform vanishing bound holds for qcqs
morphisms to a base that is not quasi-compact.

* `TauCeti.AlgebraicGeometry.DisjointProjectiveSpacesExample.toSigma`: the morphism `f`.
* `TauCeti.AlgebraicGeometry.DisjointProjectiveSpacesExample.twist`: the module `F`.
* `TauCeti.AlgebraicGeometry.DisjointProjectiveSpacesExample.nontrivial_higherDirectImage_twist`:
  for every `n`, `Rⁿ f_* F` has a nonzero section over the `n`-th component of `S`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open TauCeti.AlgebraicGeometry.Scheme.Modules
open scoped Function

universe u

namespace TauCeti.AlgebraicGeometry.DisjointProjectiveSpacesExample

variable (R : Type u) [CommRing R]

/-- The projective space `ℙⁿ_R = Proj (Sym (R^{n+1}))`. -/
abbrev projSpace (n : ℕ) : Scheme.{u} :=
  Proj (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n + 1) → R))

/-- The structure morphism `ℙⁿ_R ⟶ Spec R`. -/
abbrev projSpaceToSpec (n : ℕ) : projSpace R n ⟶ Spec (.of R) :=
  Proj.toSpecCoeff (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n + 1) → R))

/-- The coproduct `⨿_{n ≥ 0} ℙⁿ_R ⟶ ⨿_{n ≥ 0} Spec R` of the structure morphisms. -/
abbrev toSigma : ∐ projSpace R ⟶ ∐ fun _ : ℕ ↦ Spec (.of R) :=
  Limits.Sigma.map (projSpaceToSpec R)

/-- The `n`-th component of `⨿_{n ≥ 0} Spec R`, indexed by `ULift ℕ` since modules prescribed on a
disjoint cover are indexed by a type in the universe of the schemes. -/
abbrev component (n : ULift.{u} ℕ) : (∐ fun _ : ℕ ↦ Spec (.of R)).Opens :=
  (Sigma.ι (fun _ : ℕ ↦ Spec (.of R)) n.down).opensRange

/-- The components of `⨿ₙ Spec R` are pairwise disjoint. -/
lemma pairwise_disjoint_component : Pairwise (Disjoint on (component R)) :=
  fun i j h ↦ disjoint_opensRange_sigmaι (fun _ : ℕ ↦ Spec (.of R)) i.down j.down
    fun e ↦ h (ULift.ext e)

/-- The components of `⨿ₙ Spec R` cover it. -/
lemma iSup_component : ⨆ n, component R n = ⊤ :=
  (ULift.down_surjective.iSup_comp fun n ↦
    (Sigma.ι (fun _ : ℕ ↦ Spec (.of R)) n).opensRange).trans
    (sigmaOpenCover fun _ : ℕ ↦ Spec (.of R)).iSup_opensRange

/-- The components of `⨿ₙ Spec R` are affine. -/
lemma isAffineOpen_component (n : ULift.{u} ℕ) : IsAffineOpen (component R n) :=
  isAffineOpen_opensRange _

/- At the pinned Mathlib, instance search does not find `IsZariskiLocalAtTarget @QuasiCompact` and
`IsZariskiLocalAtTarget @QuasiSeparated` from Mathlib's `HasAffineProperty` instances, so these are
passed explicitly below. -/

/-- The morphism `⨿ₙ ℙⁿ_R ⟶ ⨿ₙ Spec R` is quasi-compact, since each `ℙⁿ_R` is. -/
instance instQuasiCompactToSigma : QuasiCompact (toSigma R) :=
  have := @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat
  (IsZariskiLocalAtTarget.sigmaMap_iff (projSpaceToSpec R) @QuasiCompact).mpr fun _ ↦ inferInstance

/-- The morphism `⨿ₙ ℙⁿ_R ⟶ ⨿ₙ Spec R` is quasi-separated, since each `ℙⁿ_R` is separated. -/
instance instQuasiSeparatedToSigma : QuasiSeparated (toSigma R) :=
  have := @HasAffineProperty.instIsZariskiLocalAtTarget _ _
    instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat
  (IsZariskiLocalAtTarget.sigmaMap_iff (projSpaceToSpec R) @QuasiSeparated).mpr fun _ ↦ by
    rw [projSpaceToSpec, Proj.toSpecCoeff_def]
    infer_instance

/-- The preimage of the `n`-th component of the base is identified with `ℙⁿ_R`. -/
def preimageComponentIso (n : ULift.{u} ℕ) :
    (toSigma R ⁻¹ᵁ component R n).toScheme ≅ projSpace R n.down :=
  Scheme.isoOfEq _ (sigmaMap_preimage_opensRange_sigmaι (projSpaceToSpec R) n.down) ≪≫
    (Scheme.Hom.isoOpensRange (Sigma.ι (projSpace R) n.down)).symm

/-- The module on the preimage of the `n`-th component that corresponds to `𝒪(-n-1)` on `ℙⁿ_R`. -/
abbrev twistOn (n : ULift.{u} ℕ) : (toSigma R ⁻¹ᵁ component R n).toScheme.Modules :=
  (Proj.twistingSheaf (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n.down + 1) → R))
    (-((n.down + 1 : ℕ) : ℤ))).restrict (preimageComponentIso R n).hom

/-- The module on `⨿_{n ≥ 0} ℙⁿ_R` that is `𝒪(-n-1)` on the component `ℙⁿ_R`. -/
abbrev twist : (∐ projSpace R).Modules :=
  disjointGlue _ (twistOn R)

/-- Over a nonzero ring, `Hⁿ` of `twistOn R n` is nonzero, as `Hⁿ(ℙⁿ_R, 𝒪(-n-1))` is. -/
lemma nontrivial_cohomology_twistOn [Nontrivial R] (n : ULift.{u} ℕ) :
    Nontrivial (Cohomology (twistOn R n) n.down) := by
  have := (Pi.basisFun R (Fin (n.down + 1))).nontrivial_cohomology_top_twistingSheaf_of_le_neg_card
    (Fintype.card_fin _) le_rfl
  let ψ := (preimageComponentIso R n).hom
  let M := Proj.twistingSheaf
    (TauCeti.SymmetricAlgebra.homogeneousSubmodule R (Fin (n.down + 1) → R))
    (-((n.down + 1 : ℕ) : ℤ))
  have e := (Scheme.Modules.cohomologyOnOpensRangeIso ψ M n.down).symm ≪≫
    eqToIso (congrArg (cohomologyOn M n.down) (Scheme.Hom.opensRange_of_isIso ψ)) ≪≫
      cohomologyOnTopIso M n.down
  exact e.addCommGroupIsoToAddEquiv.toEquiv.nontrivial

/-- **Nonzero higher direct images in every degree.** For a nonzero ring `R` and every `n`, the
higher direct image `Rⁿ f_* F` along `f : ⨿ₙ ℙⁿ_R ⟶ ⨿ₙ Spec R` of the module `F` that is
`𝒪(-n-1)` on `ℙⁿ_R` has a nonzero section over the `n`-th component of the base. -/
theorem nontrivial_higherDirectImage_twist [Nontrivial R] (n : ℕ) :
    Nontrivial Γ(((toSigma R).higherDirectImage n).obj (twist R), component R ⟨n⟩) :=
  have := nontrivial_cohomology_twistOn R ⟨n⟩
  (toSigma R).nontrivial_higherDirectImage_disjointGlue (pairwise_disjoint_component R)
    (iSup_component R) (twistOn R) n ⟨n⟩ (isAffineOpen_component R ⟨n⟩)

end TauCeti.AlgebraicGeometry.DisjointProjectiveSpacesExample
