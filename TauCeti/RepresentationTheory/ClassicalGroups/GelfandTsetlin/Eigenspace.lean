/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Eigenvector
import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Eigenvalue

/-!
# The Gelfand–Tsetlin lines are the joint eigenspaces of the Gelfand–Tsetlin generators

The rational Weyl module `V_λ` of `GL n ℂ` is the internal direct sum of its Gelfand–Tsetlin
lines `TauCeti.gtLine λ P`, one for each Gelfand–Tsetlin pattern `P` with top weight `λ`
(`TauCeti.isInternal_gtLine`). This file characterizes the lines intrinsically.

The Gelfand–Tsetlin generators, the images in `U(𝔤𝔩ₙ)` of the Gelfand invariants of the
upper-left corners `𝔤𝔩₁ ⊂ ⋯ ⊂ 𝔤𝔩ₙ`, act on the line of `P` by scalars read off the rows of `P`,
and these scalars determine `P`. Hence the line of `P` is *exactly* the joint eigenspace of the
generators for the eigenvalues of `P`, and every nonzero joint eigenspace of the generators is
one of the lines. So the Gelfand–Tsetlin decomposition is the joint eigenspace decomposition of
the generators.

## Main results

* `TauCeti.iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine`: the Gelfand–Tsetlin line of `P` is
  the joint eigenspace of the Gelfand–Tsetlin generators for the eigenvalues of `P`.
* `TauCeti.exists_iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine`: every nonzero joint
  eigenspace of the Gelfand–Tsetlin generators is a Gelfand–Tsetlin line.

## References

* I. M. Gelfand and M. L. Tsetlin, *Finite-dimensional representations of the group of unimodular
  matrices*, Doklady Akad. Nauk SSSR **71** (1950), 825–828.
* A. Molev, *Gelfand-Tsetlin bases for classical Lie algebras*, in Handbook of Algebra, Vol. 4
  (2006), 109–170, §2.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §15.3.
-/

public section

open Module Representation

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

variable {n : ℕ}

/-- The joint eigenspace of the Gelfand–Tsetlin generators of `V_λ`, indexed by the level `k ≤ n`
and the degree `r`, is the joint eigenspace of the same family indexed by the pairs `(k, r)`, the
form to which `TauCeti.iInf_eigenspace_eq_of_iSup_eq_top` applies. -/
private theorem iInf_eigenspace_gelfandTsetlinGenerator_eq_iInf_subtype (l : DominantWeight n)
    (χ : ℕ → ℕ → ℂ) :
    ⨅ (k : ℕ) (hk : k ≤ n) (r : ℕ),
      Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ hk r)) (χ k r) =
    ⨅ x : {kr : ℕ × ℕ // kr.1 ≤ n},
      Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ x.2 x.1.2)) (χ x.1.1 x.1.2) := by
  ext v
  simp only [Submodule.mem_iInf, Subtype.forall, Prod.forall]
  exact ⟨fun h k r hk ↦ h k hk r, fun h k hk r ↦ h k r hk⟩

/-- The Gelfand–Tsetlin line of `P` lies in the joint eigenspace of the Gelfand–Tsetlin generators
for the eigenvalues of `P`, the family being indexed by the pairs `(k, r)`. -/
private theorem gtLine_le_iInf_eigenspace_gelfandTsetlinGenerator (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l}) :
    gtLine l P ≤ ⨅ x : {kr : ℕ × ℕ // kr.1 ≤ n},
      Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ x.2 x.1.2))
        (gelfandEigenvalue (fun i : Fin x.1.1 ↦ (P.1 i x.1.1 : ℂ)) x.1.2) :=
  le_iInf fun x _ hv ↦ Module.End.mem_eigenspace_iff.mpr
    (lift_differential_gelfandTsetlinGenerator_apply_of_mem_gtLine l P x.2 x.1.2 hv)

/-- Distinct patterns with top weight `λ` have distinct systems of Gelfand–Tsetlin eigenvalues,
the family being indexed by the pairs `(k, r)`. -/
private theorem injective_gelfandEigenvalue_gtPattern (l : DominantWeight n) :
    Function.Injective fun (P : {P : GTPattern n // P.topWeight = l})
      (x : {kr : ℕ × ℕ // kr.1 ≤ n}) ↦
        gelfandEigenvalue (fun i : Fin x.1.1 ↦ (P.1 i x.1.1 : ℂ)) x.1.2 :=
  fun _ _ h ↦ Subtype.ext (GTPattern.eq_of_forall_gelfandEigenvalue_eq (K := ℂ)
    fun j hj r _ ↦ congrFun h ⟨(j, r), hj⟩)

/-- **The Gelfand–Tsetlin line of a pattern is a joint eigenspace.** Inside the rational Weyl
module `V_λ` of `GL n ℂ`, the Gelfand–Tsetlin line of a pattern `P` with top weight `λ` is exactly
the space of vectors on which, for every level `k ≤ n` and every degree `r`, the Gelfand–Tsetlin
generator of degree `r` at level `k` acts by the scalar `gelfandEigenvalue` of the row
`(P 0 k, …, P (k - 1) k)` of `P`. -/
theorem iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine (l : DominantWeight n)
    (P : {P : GTPattern n // P.topWeight = l}) :
    ⨅ (k : ℕ) (hk : k ≤ n) (r : ℕ),
      Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ hk r))
        (gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r) =
      gtLine l P := by
  classical
  rw [iInf_eigenspace_gelfandTsetlinGenerator_eq_iInf_subtype l
    fun k r ↦ gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r]
  exact iInf_eigenspace_eq_of_iSup_eq_top _ (gtLine_le_iInf_eigenspace_gelfandTsetlinGenerator l)
    (isInternal_gtLine l).submodule_iSup_eq_top (injective_gelfandEigenvalue_gtPattern l) P

/-- **Membership in a Gelfand–Tsetlin line.** A vector of the rational Weyl module `V_λ` of
`GL n ℂ` lies in the Gelfand–Tsetlin line of a pattern `P` with top weight `λ` exactly when, for
every level `k ≤ n` and every degree `r`, the Gelfand–Tsetlin generator of degree `r` at level `k`
acts on it by the scalar `gelfandEigenvalue` of the row `(P 0 k, …, P (k - 1) k)` of `P`. -/
theorem mem_gtLine_iff (l : DominantWeight n) (P : {P : GTPattern n // P.topWeight = l})
    {v : (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule} :
    v ∈ gtLine l P ↔ ∀ (k : ℕ) (hk : k ≤ n) (r : ℕ),
      UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ hk r) v =
        gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r • v := by
  rw [← iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine]
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- **Every nonzero joint eigenspace of the Gelfand–Tsetlin generators is a Gelfand–Tsetlin
line.** If the vectors of `V_λ` on which, for every level `k ≤ n` and every degree `r`, the
Gelfand–Tsetlin generator of degree `r` at level `k` acts by a prescribed scalar `χ k r` do not
reduce to zero, then they form the Gelfand–Tsetlin line of some pattern with top weight `λ`. -/
theorem exists_iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine (l : DominantWeight n)
    (χ : ℕ → ℕ → ℂ)
    (hχ : ⨅ (k : ℕ) (hk : k ≤ n) (r : ℕ),
      Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
        (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
          (gelfandTsetlinGenerator ℂ hk r)) (χ k r) ≠ ⊥) :
    ∃ P : {P : GTPattern n // P.topWeight = l},
      ⨅ (k : ℕ) (hk : k ≤ n) (r : ℕ),
        Module.End.eigenspace (M := (weylModuleOfShape ℂ n l.detShiftShape).toSubmodule)
          (UniversalEnvelopingAlgebra.lift ℂ (isRationalRep_rationalWeylRep n l).differential
            (gelfandTsetlinGenerator ℂ hk r)) (χ k r) = gtLine l P := by
  classical
  rw [iInf_eigenspace_gelfandTsetlinGenerator_eq_iInf_subtype] at hχ ⊢
  by_contra! h
  refine hχ (iInf_eigenspace_eq_bot_of_iSup_eq_top _
    (gtLine_le_iInf_eigenspace_gelfandTsetlinGenerator l)
    (isInternal_gtLine l).submodule_iSup_eq_top ?_)
  rintro ⟨P, hP⟩
  simp only [funext_iff] at hP
  refine h P ?_
  simp only [← hP]
  exact (iInf_eigenspace_gelfandTsetlinGenerator_eq_iInf_subtype l
    fun k r ↦ gelfandEigenvalue (fun i : Fin k ↦ (P.1 i k : ℂ)) r).symm.trans
      (iInf_eigenspace_gelfandTsetlinGenerator_eq_gtLine l P)

end TauCeti
