/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Diffeomorphisms of products

If a diffeomorphism between nonempty products has underlying map `Prod.map f g`, then
both `f` and `g` are diffeomorphisms. No smoothness of the factor maps or their inverses
is assumed: each is recovered as a slice of the product diffeomorphism or its inverse.
This lets one promote separation of a smooth map into separation by bundled equivalences.

`Diffeomorph.prodAssocOfModels` reassociates three manifold factors with independent model
vector spaces, generalizing Mathlib's `Diffeomorph.prodAssoc`, where the last two coincide.
`Diffeomorph.prodAssocSymmSelf` regroups a triple product of normed spaces `E × F × E'`, carrying
its own model, as the product manifold `(E × F) × E'`.

The four-way exchange `((a, b), (c, d)) ↦ ((a, c), (b, d))` of a product of two products is
the diffeomorphism `Diffeomorph.prodProdProdComm`, the smooth counterpart of
`Equiv.prodProdProdComm`. It regroups a product of relations `M₁ ⇝ N₁` and `M₂ ⇝ N₂` as a
relation `M₁ × M₂ ⇝ N₁ × N₂`.

The homeomorphism underlying Mathlib's factor swap `Diffeomorph.prodComm` is
`Homeomorph.prodComm` (`Diffeomorph.toHomeomorph_prodComm`).
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

/-- The factors of a diffeomorphism whose underlying map separates are themselves
`C^n` diffeomorphisms. Nonemptiness excludes an empty product hiding an arbitrary factor. -/
theorem exists_factors_of_eq_prodMap
    (Q : (M × N) ≃ₘ^n⟮I.prod J, I'.prod J'⟯ (M' × N'))
    [Nonempty M] [Nonempty N] (f : M → M') (g : N → N')
    (hQ : ⇑Q = Prod.map f g) :
    ∃ (φ : M ≃ₘ^n⟮I, I'⟯ M') (ψ : N ≃ₘ^n⟮J, J'⟯ N'), ⇑φ = f ∧ ⇑ψ = g := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  obtain ⟨y₀⟩ := ‹Nonempty N›
  have hQ' (p : M × N) : Q p = (f p.1, g p.2) := by rw [hQ, Prod.map_apply']
  -- The inverse factors are the slices of `Q.symm` through `(·, g y₀)` and `(f x₀, ·)`.
  refine ⟨⟨⟨f, fun u ↦ (Q.symm (u, g y₀)).1, fun x ↦ ?_, fun u ↦ ?_⟩, ?_,
      (Q.symm.contMDiff.comp (contMDiff_id.prodMk contMDiff_const)).fst⟩,
    ⟨⟨g, fun v ↦ (Q.symm (f x₀, v)).2, fun y ↦ ?_, fun v ↦ ?_⟩, ?_,
      (Q.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id)).snd⟩, rfl, rfl⟩
  · simpa [hQ'] using congrArg Prod.fst (Q.symm_apply_apply (x, y₀))
  · simpa [hQ'] using congrArg Prod.fst (Q.apply_symm_apply (u, g y₀))
  · simpa [hQ'] using
      (Q.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := y₀)))).fst
  · simpa [hQ'] using congrArg Prod.snd (Q.symm_apply_apply (x₀, y))
  · simpa [hQ'] using congrArg Prod.snd (Q.apply_symm_apply (f x₀, v))
  · simpa [hQ'] using
      (Q.contMDiff.comp ((contMDiff_const (c := x₀)).prodMk contMDiff_id)).snd

section prodAssocOfModels

variable (I J I' M N M' n)

/-- Reassociation of three manifold factors with independent model vector spaces. -/
def prodAssocOfModels :
    ((M × N) × M') ≃ₘ^n⟮(I.prod J).prod I', I.prod (J.prod I')⟯ M × (N × M') where
  toEquiv := Equiv.prodAssoc M N M'
  contMDiff_toFun := contMDiff_prod_assoc
  contMDiff_invFun := (contMDiff_fst.prodMk contMDiff_snd.fst).prodMk contMDiff_snd.snd

/-- Reassociation sends `((x, y), z)` to `(x, (y, z))`. -/
@[simp]
theorem prodAssocOfModels_apply (p : (M × N) × M') :
    prodAssocOfModels I J I' M N M' n p = (p.1.1, (p.1.2, p.2)) := (rfl)

/-- Inverse reassociation sends `(x, (y, z))` to `((x, y), z)`. -/
@[simp]
theorem prodAssocOfModels_symm_apply (p : M × (N × M')) :
    (prodAssocOfModels I J I' M N M' n).symm p = ((p.1, p.2.1), p.2.2) := (rfl)

end prodAssocOfModels

section prodAssocSymmSelf

variable (𝕜 E F E' n)

/-- The regrouping `(x, y, z) ↦ ((x, y), z)` from the normed space `E × F × E'`, with its own model,
to the product manifold `(E × F) × E'`. -/
def prodAssocSymmSelf :
    (E × F × E') ≃ₘ^n⟮𝓘(𝕜, E × F × E'), 𝓘(𝕜, E × F).prod 𝓘(𝕜, E')⟯ ((E × F) × E') where
  toEquiv := (Equiv.prodAssoc E F E').symm
  contMDiff_toFun := (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contMDiff.prodMk
    (contDiff_snd.comp contDiff_snd).contMDiff
  contMDiff_invFun := (contDiff_fst.contMDiff.comp contMDiff_fst).prodMk_space
    ((contDiff_snd.contMDiff.comp contMDiff_fst).prodMk_space contMDiff_snd)

/-- The regrouping sends `(x, y, z)` to `((x, y), z)`. -/
@[simp]
theorem prodAssocSymmSelf_apply (p : E × F × E') :
    prodAssocSymmSelf 𝕜 E F E' n p = ((p.1, p.2.1), p.2.2) := (rfl)

/-- The inverse regrouping sends `((x, y), z)` to `(x, y, z)`. -/
@[simp]
theorem prodAssocSymmSelf_symm_apply (p : (E × F) × E') :
    (prodAssocSymmSelf 𝕜 E F E' n).symm p = (p.1.1, p.1.2, p.2) := (rfl)

end prodAssocSymmSelf

section prodProdProdComm

variable (I J I' J' M N M' N' n)

/-- `(M × N) × (M' × N')` is diffeomorphic to `(M × M') × (N × N')`, by exchanging the two
middle factors. -/
def prodProdProdComm :
    ((M × N) × (M' × N')) ≃ₘ^n⟮(I.prod J).prod (I'.prod J'), (I.prod I').prod (J.prod J')⟯
      ((M × M') × (N × N')) where
  contMDiff_toFun := (contMDiff_fst.fst.prodMk contMDiff_snd.fst).prodMk
    (contMDiff_fst.snd.prodMk contMDiff_snd.snd)
  contMDiff_invFun := (contMDiff_fst.fst.prodMk contMDiff_snd.fst).prodMk
    (contMDiff_fst.snd.prodMk contMDiff_snd.snd)
  toEquiv := Equiv.prodProdProdComm M N M' N'

/-- The inverse of the four-way exchange is the four-way exchange of the regrouped factors. -/
@[simp]
theorem prodProdProdComm_symm :
    (prodProdProdComm I J I' J' M N M' N' n).symm = prodProdProdComm I I' J J' M M' N N' n :=
  (rfl)

/-- The underlying map of the four-way exchange is `Equiv.prodProdProdComm`. -/
@[simp]
theorem coe_prodProdProdComm :
    ⇑(prodProdProdComm I J I' J' M N M' N' n) = Equiv.prodProdProdComm M N M' N' :=
  (rfl)

end prodProdProdComm

/-- The homeomorphism underlying the factor swap `M × N ≃ N × M` is the factor swap. -/
@[simp]
theorem toHomeomorph_prodComm :
    (Diffeomorph.prodComm I J M N n).toHomeomorph = Homeomorph.prodComm M N :=
  Homeomorph.ext fun _ ↦ rfl

end Diffeomorph
