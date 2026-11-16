/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Acyclic
public import TauCeti.Algebra.Homology.Curved.Module.Right.ZeroCurvature
public import TauCeti.Algebra.Homology.DG.Module.Right.Cohomology

/-!
# Ordinary cohomology of totalizations at zero curvature

The totalization of a short exact sequence of curved right modules has zero ordinary
cohomology when the algebra curvature is zero. More precisely, its differential has image
equal to kernel, and the cohomology of the corresponding DG right module is a zero module.
This identifies the generators of the acyclic classes of the second kind as ordinary acyclic
objects in the uncurved case. No boundedness or homological-dimension hypothesis is needed for
this direction of the comparison.

No homology is assigned to modules of nonzero curvature. The square-zero equation used below
comes specifically from the curvature-zero specialization.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Bull. Lond.
  Math. Soc. **55** (2023), 1553–1640, Section 7.6 and Theorem 7.8(b).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- The closed category retains the original curved module objects.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {h : IsCurvedDGAlgebra 𝒜 d 0}
  (S : ShortComplex
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)))

/-- At curvature zero, the differential of a short-exact totalization has image equal to
kernel. This is ordinary acyclicity, not a claim that the totalization is contractible. -/
theorem totalization_differential_exact (hS : S.ShortExact) :
    Function.Exact (totalization S).differential (totalization S).differential := by
  rw [totalization_eq]
  let T := S.map (forgetDifferential (h := h))
  have hT : T.ShortExact := hS.map_of_exact _
  have hf : Function.Injective (closedHom S.f) :=
    (GradedModuleCat.mono_iff_injective T.f).1 hT.mono_f
  have hg : Function.Surjective (closedHom S.g) :=
    (GradedModuleCat.epi_iff_surjective T.g).1 hT.epi_g
  have hfg : Function.Exact (closedHom S.f) (closedHom S.g) :=
    GradedModuleCat.exact_iff.mp hT.exact
  rintro ⟨⟨x, y⟩, z⟩
  refine ⟨fun hc ↦ ?_, ?_⟩
  · rw [cone_coneDesc_differential_apply] at hc
    have hy : -closedHom S.f x - S.X₂.differential y = 0 :=
      congrArg (fun t ↦ t.1.2) hc
    have hz : closedHom S.g y + S.X₃.differential z = 0 :=
      congrArg Prod.snd hc
    -- Lift the last component, then correct the middle component by its differential.
    obtain ⟨b, hb⟩ := hg z
    have hclosed : closedHom S.g (y + S.X₂.differential b) = 0 := by
      rw [map_add, ← differential_closedHom, hb]
      exact hz
    obtain ⟨a, ha⟩ := (hfg _).1 hclosed
    have hda : S.X₁.differential a = -x := by
      apply hf
      have hd := congrArg S.X₂.differential ha
      rw [differential_closedHom, map_add,
        S.X₂.toDG.isDGRightModule.sq_zero, add_zero] at hd
      rw [map_neg, hd]
      exact (sub_eq_zero.mp hy).symm
    refine ⟨((-a, b), 0), ?_⟩
    rw [cone_coneDesc_differential_apply]
    simp only [map_neg, hda, neg_neg, ha, map_zero, add_zero, hb, add_sub_cancel_right]
  · rintro ⟨v, hv⟩
    rw [← hv]
    exact (cone (coneDesc S.f S.g S.zero)).toDG.isDGRightModule.sq_zero v

/-- The ordinary DG-module cohomology of a short-exact totalization at curvature zero is
zero. Since cohomology is internally graded, this also makes every cohomological degree zero. -/
theorem subsingleton_cohomology_totalization (hS : S.ShortExact) :
    Subsingleton (totalization S).toDG.isDGRightModule.Cohomology := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  rw [IsDGRightModule.mem_boundaries]
  exact (totalization_differential_exact S hS z).1
    (((totalization S).toDG.isDGRightModule.mem_cycles).mp z.2)

end TauCeti.CurvedDGRightModuleCat
