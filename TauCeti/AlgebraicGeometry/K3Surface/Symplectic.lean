/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.K3Surface.Basic
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Forms.Pullback
import TauCeti.AlgebraicGeometry.Cohomology.Genus
import TauCeti.AlgebraicGeometry.Geometrically.GlobalSections

/-!
# Symplectic automorphisms of K3 surfaces

An automorphism `g` of a K3 surface `X` over a field `k` is **symplectic** when its pullback acts
as the identity on the global two-forms `H⁰(X, Ω²_{X/k})`. Since automorphisms compose as maps and
pullback reverses composition, the automorphism group acts on the left on global two-forms by
inverse pullback, and the symplectic automorphisms form its kernel, the subgroup
`symplecticAut k X`. Pullback and inverse pullback fix the same forms, so membership is the
condition `g^* σ = σ` for every global two-form `σ`.

The subgroup is defined for any scheme over a commutative ring. For a K3 surface the canonical
sheaf `Ω²_{X/k}` is trivial and `X` is proper and geometrically integral, so its global two-forms
form a one-dimensional `k`-vector space (`IsK3.finrank_globalSections_differentialForms_two`).
Consequently a single nonzero two-form `σ` (a volume form) detects symplecticity:
`g` is symplectic if and only if `g^* σ = σ` (`IsK3.mem_symplecticAut_iff_of_ne_zero`). This
condition does not depend on the choice of `σ`.

## Main declarations

* `TauCeti.AlgebraicGeometry.symplecticAut R X`: the subgroup of automorphisms of `X` over
  `Spec R` acting trivially on global two-forms;
* `TauCeti.AlgebraicGeometry.mem_symplecticAut_iff`: `g` is symplectic if and only if its
  pullback fixes every global two-form;
* `TauCeti.AlgebraicGeometry.IsK3.finrank_globalSections_differentialForms_two`: a K3 surface has
  a one-dimensional space of global two-forms;
* `TauCeti.AlgebraicGeometry.IsK3.mem_symplecticAut_iff_of_ne_zero`: on a K3 surface, `g` is
  symplectic if and only if it fixes one nonzero global two-form.

## References

* D. Huybrechts, *Lectures on K3 Surfaces*, Chapter 15, Definition 1.1 and Remark 1.3.
-/

public section

open CategoryTheory AlgebraicGeometry Module

namespace TauCeti.AlgebraicGeometry

universe u

section Ring

variable (R : Type u) [CommRing R] (X : Scheme.{u}) [X.Over (Spec (.of R))]

/-- The **symplectic automorphisms** of a scheme `X` over `Spec R`: the automorphisms of `X` over
`Spec R` acting trivially on the global two-forms `Γ(X, Ω²_{X/R})`, the kernel of the inverse
pullback representation on global two-forms. On a K3 surface these are the automorphisms preserving
a volume form. -/
noncomputable def symplecticAut : Subgroup (Aut (Over.mk (X ↘ Spec (.of R)))) :=
  (differentialFormsRepresentation R X 2).ker

variable {R X}

/-- An automorphism is symplectic exactly when its pullback fixes every global two-form. -/
theorem mem_symplecticAut_iff {g : Aut (Over.mk (X ↘ Spec (.of R)))} :
    g ∈ symplecticAut R X ↔
      ∀ σ, differentialFormsPullback R (X := X) (Y := X) g.asIso.hom.left 2 σ = σ :=
  mem_ker_differentialFormsRepresentation_iff R X 2 g

/-- An automorphism is symplectic exactly when its inverse pullback, the action of the
representation on global two-forms, fixes every global two-form. -/
theorem mem_symplecticAut_iff_inv {g : Aut (Over.mk (X ↘ Spec (.of R)))} :
    g ∈ symplecticAut R X ↔
      ∀ σ, differentialFormsPullback R (X := X) (Y := X) g.asIso.inv.left 2 σ = σ := by
  simp only [symplecticAut, MonoidHom.mem_ker, LinearMap.ext_iff,
    differentialFormsRepresentation_apply, one_apply_eq_self]

end Ring

namespace IsK3

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A K3 surface over `k` has a one-dimensional space of global two-forms: its canonical sheaf
`Ω²_{X/k}` is trivial, and a proper geometrically integral scheme has only constant global
functions. -/
theorem finrank_globalSections_differentialForms_two (hX : IsK3 k (X ↘ Spec (.of k))) :
    finrank k Γ(differentialForms k (X ↘ Spec (.of k)) 2, ⊤) = 1 := by
  have := hX.isIntegral
  have := hX.isProper
  have := hX.geometricallyIntegral
  obtain ⟨e⟩ := hX.nonempty_differentialFormsIso
  rw [← Scheme.Modules.finrank_cohomology_zero_eq_finrank_globalSections,
    Scheme.Modules.finrank_cohomology_congr k e,
    ← Scheme.Modules.finrank_cohomology_congr k (SheafOfModules.freePUnitIsoUnit _),
    ← InvertibleSheaf.trivial_obj]
  exact finrank_cohomology_zero_trivial_eq_one_of_surjective k
    (X.baseRingToGlobalSections_bijective_of_geometricallyIntegral k).surjective

/-- On a K3 surface, an automorphism is symplectic if and only if its pullback fixes a single
nonzero global two-form: the global two-forms are one-dimensional and pullback is `k`-linear. -/
theorem mem_symplecticAut_iff_of_ne_zero (hX : IsK3 k (X ↘ Spec (.of k)))
    {g : Aut (Over.mk (X ↘ Spec (.of k)))} {σ : Γ(differentialForms k (X ↘ Spec (.of k)) 2, ⊤)}
    (hσ : σ ≠ 0) :
    g ∈ symplecticAut k X ↔
      differentialFormsPullback k (X := X) (Y := X) g.asIso.hom.left 2 σ = σ := by
  refine ⟨fun hg ↦ mem_symplecticAut_iff.1 hg σ, fun hgσ ↦ mem_symplecticAut_iff.2 fun τ ↦ ?_⟩
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' σ hσ).1
    (hX.finrank_globalSections_differentialForms_two) τ
  rw [map_smul, hgσ]

end IsK3

end TauCeti.AlgebraicGeometry
