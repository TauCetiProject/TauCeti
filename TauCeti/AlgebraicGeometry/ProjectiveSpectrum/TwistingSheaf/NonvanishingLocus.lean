/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Nonvanishing loci of twisting-sheaf sections on `Proj`

When degree-one standard opens cover `Proj A`, the nonvanishing locus of the section of
`𝒪(n)` associated to a homogeneous element `r ∈ Aₙ` is the standard open `D₊(r)`
(`AlgebraicGeometry.Proj.twistingSheaf.nonvanishingLocus_toTwistingSheaf`).

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Sections 5 and 7.
* The Stacks Project, Tags 01MM and 01PS.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]
  {ι : Type u} (f : ι → A) (hf : ∀ i, f i ∈ 𝒜 1)
  (hcover : ⨆ i, basicOpen 𝒜 (f i) = ⊤)

namespace twistingSheaf

/-- A standard basis section of a twisting sheaf vanishes nowhere on its chart. -/
@[simp]
theorem nonvanishingLocus_chartGenerator (n : ℤ)
    [TauCeti.SheafOfModules.IsInvertible (R := (Proj 𝒜).ringCatSheaf) (twistingSheaf 𝒜 n)]
    {g : A} (hg : g ∈ 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ basicOpen 𝒜 g) :
    (twistingSheaf 𝒜 n).nonvanishingLocus (chartGenerator n g hg U hU) = U := by
  apply le_antisymm (Scheme.Modules.nonvanishingLocus_le _)
  rw [Scheme.Modules.le_nonvanishingLocus_iff _ (𝟙 U)]
  intro W j
  simpa only [Category.comp_id, res_chartGenerator, ← chartSectionsLinearEquiv_apply] using
    (chartSectionsLinearEquiv n g hg W (j.le.trans hU)).bijective

include hcover hf in
/-- A homogeneous section of `𝒪(n)` is nonvanishing exactly on the corresponding standard
open `D₊(r)`, including for degree zero. The covering family is an explicit argument,
so this lemma is intended for rewriting rather than the simp set. -/
theorem nonvanishingLocus_toTwistingSheaf (n : ℕ) (r : 𝒜 n) :
    haveI := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover (n : ℤ)
    (twistingSheaf 𝒜 (n : ℤ)).nonvanishingLocus (toTwistingSheaf 𝒜 rfl ⊤ r) =
      basicOpen 𝒜 (r : A) := by
  have := isInvertible_twistingSheaf_of_iSup_eq_top f hf hcover (n : ℤ)
  have hlocal (i : ι) :
      basicOpen 𝒜 (f i) ⊓
          (twistingSheaf 𝒜 (n : ℤ)).nonvanishingLocus (toTwistingSheaf 𝒜 rfl ⊤ r) =
        basicOpen 𝒜 (f i) ⊓ basicOpen 𝒜 (r : A) := by
    rw [← Scheme.Modules.nonvanishingLocus_map (basicOpen 𝒜 (f i)).leTop,
      res_toTwistingSheaf, toTwistingSheaf_eq_smul_chartGenerator n r (hf i)]
    rw [Scheme.Modules.nonvanishingLocus_smul, nonvanishingLocus_chartGenerator,
      basicOpen_awayToSection_mk, basicOpen_mul]
    exact inf_eq_left.mpr inf_le_left
  ext x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover.symm ▸ Opens.mem_top x)
  have hi' : x ∈ (basicOpen 𝒜 (f i) : Set (Proj 𝒜)) := hi
  have h := congrArg (fun U : (Proj 𝒜).Opens ↦ x ∈ (U : Set (Proj 𝒜))) (hlocal i)
  simpa only [Opens.coe_inf, Set.mem_inter_iff, hi', true_and] using (iff_of_eq h)

end twistingSheaf

end AlgebraicGeometry.Proj
