/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
import TauCeti.Algebra.Module.Torsion.Finite
import TauCeti.AlgebraicGeometry.Cohomology.Localization

/-!
# Torsion in finite cohomology

`AlgebraicGeometry.Scheme.Modules.exists_pow_le_annihilator_cohomology` turns vanishing on the
inverse images of principal opens `D(r)` for `r ∈ I` into a uniform torsion bound. For a
quasi-coherent sheaf on a quasi-compact, quasi-separated scheme over `R`, if its degree-`n`
cohomology is finite over `R` and `I` is finitely generated, one power of `I` annihilates the
entire degree-`n` cohomology module. This gives, for example, an ideal-of-definition torsion
bound on higher coherent cohomology of submodule blowups.

The criterion combines cohomology localization on principal opens with
`Module.IsTorsion'.exists_isTorsionBy_of_finite` and `Ideal.exists_pow_le_of_le_radical_of_fg`.
-/

public section

open CategoryTheory
open TauCeti.AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- If the degree-`n` cohomology of a quasi-coherent sheaf on a qcqs scheme over `R` is finite
over `R` and vanishes on the inverse images of the basic opens of a finitely generated ideal
`I`, a power of `I` annihilates that cohomology. -/
theorem exists_pow_le_annihilator_cohomology {R : Type u} [CommRing R] {X : Scheme.{u}}
    [X.Over (Spec (.of R))] [CompactSpace X] [QuasiSeparatedSpace X] (M : X.Modules)
    [M.IsQuasicoherent] (n : ℕ) [Module.Finite R (Cohomology M n)] {I : Ideal R} (hI : I.FG)
    (hvanish : ∀ r ∈ I,
      Subsingleton (cohomologyOn M n ((X ↘ Spec (.of R)) ⁻¹ᵁ PrimeSpectrum.basicOpen r))) :
    ∃ k : ℕ, I ^ k ≤ Module.annihilator R (Cohomology M n) := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg (fun r hr ↦ ?_) hI
  have hopen : X.basicOpen (baseRingToGlobalSections R X r) =
      (X ↘ Spec (.of R)) ⁻¹ᵁ PrimeSpectrum.basicOpen r := by
    rw [baseRingToGlobalSections_apply, ← Scheme.Hom.preimage_basicOpen_top, basicOpen_eq_of_affine]
  let g := baseRingToGlobalSections R X r
  let res := cohomologyOnResLinear M n (le_top : X.basicOpen g ≤ ⊤) ∘ₗ
    (cohomologyOnTopLinearEquiv M n).symm.toLinearMap
  have : IsLocalizedModule (Submonoid.powers g) res :=
    isLocalizedModule_cohomologyOnResLinear_comp_cohomologyOnTopLinearEquiv_symm M g n
  have htorsion : Module.IsTorsion' (Cohomology M n) (Submonoid.powers r) := by
    intro x
    have hvanish' : Subsingleton (cohomologyOn M n
        (X.basicOpen (baseRingToGlobalSections R X r))) := hopen.symm ▸ hvanish r hr
    obtain ⟨_, ⟨j, rfl⟩, hj⟩ :=
      (IsLocalizedModule.subsingleton_iff (Submonoid.powers g) res).mp hvanish' x
    refine ⟨⟨r ^ j, (Submonoid.mem_powers_iff _ _).mpr ⟨j, rfl⟩⟩, ?_⟩
    simpa only [Submonoid.smul_def, base_smul_cohomology, map_pow] using hj
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := htorsion.exists_isTorsionBy_of_finite
  exact Ideal.mem_radical_iff.mpr ⟨k, Module.mem_annihilator.mpr hk⟩

end AlgebraicGeometry.Scheme.Modules
