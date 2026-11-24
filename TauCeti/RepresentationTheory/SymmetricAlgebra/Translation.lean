/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Translation
public import TauCeti.RepresentationTheory.SymmetricAlgebra.Basic

/-!
# Translation automorphisms of symmetric-algebra invariants

For a representation `ρ` of a monoid `G` on an `R`-module `M`, translating `SymmetricAlgebra R M`
along `f : M →ₗ[R] R` (`SymmetricAlgebra.translation f`) intertwines `ρ.symmetricAlgebra g` with
translation by `f ∘ₗ ρ g`. When `f` is `G`-invariant, `SymmetricAlgebra.translation f` restricts to
`Representation.translationSymmetricAlgebraInvariantsEquiv` on `ρ.symmetricAlgebraInvariants`,
carrying `(RingHom.ker (SymmetricAlgebra.lift f)).under _` onto the contraction of the homogeneous
irrelevant ideal.

## Main definitions and results

* `Representation.translation_symmetricAlgebra`: equivariance of `SymmetricAlgebra.translation`.
* `Representation.translationSymmetricAlgebraInvariantsEquiv`: `R`-algebra automorphism of
  `ρ.symmetricAlgebraInvariants` induced by a `G`-invariant linear form `f`.
* `Representation.map_translationSymmetricAlgebraInvariantsEquiv_under_ker_lift`: image of
  `(ker (lift f)) ∩ Sym(M)^G` under translation by `f`.

## References

* L. Smith, *Polynomial Invariants of Finite Groups*, A K Peters (1995), § 7.5.
* R. Kane, *Reflection Groups and Invariant Theory*, CMS Books in Mathematics, Springer (2001),
  § 22.
-/

public section

open TauCeti.SymmetricAlgebra

namespace Representation

variable {R G M : Type*} [CommRing R] [Monoid G] [AddCommMonoid M] [Module R M]
  (ρ : Representation R G M)

/-- Translating `SymmetricAlgebra R M` by `f` after `ρ.symmetricAlgebra g` equals applying
`ρ.symmetricAlgebra g` after translating by `f ∘ₗ ρ g`. -/
theorem translation_symmetricAlgebra (f : M →ₗ[R] R) (g : G) (p : SymmetricAlgebra R M) :
    SymmetricAlgebra.translation f (ρ.symmetricAlgebra g p) =
      ρ.symmetricAlgebra g (SymmetricAlgebra.translation (f ∘ₗ ρ g) p) := by
  have h : (SymmetricAlgebra.translation f).toAlgHom.comp (SymmetricAlgebra.map R (ρ g)) =
      (SymmetricAlgebra.map R (ρ g)).comp (SymmetricAlgebra.translation (f ∘ₗ ρ g)).toAlgHom :=
    SymmetricAlgebra.algHom_ext <| LinearMap.ext fun _ ↦ by simp
  simpa only [symmetricAlgebra_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] using
    DFunLike.congr_fun h p

private noncomputable def translationInvariantsAlgHom (f : M →ₗ[R] R)
    (hf : ∀ g : G, f ∘ₗ ρ g = f) :
    ρ.symmetricAlgebraInvariants →ₐ[R] ρ.symmetricAlgebraInvariants :=
  ((SymmetricAlgebra.translation f).toAlgHom.comp ρ.symmetricAlgebraInvariants.val).codRestrict
    ρ.symmetricAlgebraInvariants fun x ↦ (ρ.mem_symmetricAlgebraInvariants _).mpr fun g ↦ by
      simpa [hf g, (ρ.mem_symmetricAlgebraInvariants x.val).mp x.property g] using
        (ρ.translation_symmetricAlgebra f g x.val).symm

/-- When `f : M →ₗ[R] R` is `G`-invariant (`∀ g, f ∘ₗ ρ g = f`), translation by `f` restricts to an
`R`-algebra automorphism of `ρ.symmetricAlgebraInvariants`. -/
noncomputable def translationSymmetricAlgebraInvariantsEquiv (f : M →ₗ[R] R)
    (hf : ∀ g : G, f ∘ₗ ρ g = f) :
    ρ.symmetricAlgebraInvariants ≃ₐ[R] ρ.symmetricAlgebraInvariants :=
  AlgEquiv.ofAlgHom (ρ.translationInvariantsAlgHom f hf)
    (ρ.translationInvariantsAlgHom (-f) fun g ↦ by rw [LinearMap.neg_comp, hf g])
    (by ext; simp [translationInvariantsAlgHom]) (by ext; simp [translationInvariantsAlgHom])

/-- Within `SymmetricAlgebra R M`, `translationSymmetricAlgebraInvariantsEquiv f hf` acts as
`SymmetricAlgebra.translation f`. -/
@[simp] theorem coe_translationSymmetricAlgebraInvariantsEquiv_apply (f : M →ₗ[R] R)
    (hf : ∀ g : G, f ∘ₗ ρ g = f) (x : ρ.symmetricAlgebraInvariants) :
    (ρ.translationSymmetricAlgebraInvariantsEquiv f hf x : SymmetricAlgebra R M) =
      SymmetricAlgebra.translation f x := by
  rw [translationSymmetricAlgebraInvariantsEquiv, AlgEquiv.ofAlgHom_apply,
    translationInvariantsAlgHom]; rfl

/-- Within `SymmetricAlgebra R M`, `(translationSymmetricAlgebraInvariantsEquiv f hf).symm` acts as
`SymmetricAlgebra.translation (-f)`. -/
@[simp] theorem coe_translationSymmetricAlgebraInvariantsEquiv_symm_apply (f : M →ₗ[R] R)
    (hf : ∀ g : G, f ∘ₗ ρ g = f) (x : ρ.symmetricAlgebraInvariants) :
    ((ρ.translationSymmetricAlgebraInvariantsEquiv f hf).symm x : SymmetricAlgebra R M) =
      SymmetricAlgebra.translation (-f) x := by
  rw [translationSymmetricAlgebraInvariantsEquiv, AlgEquiv.ofAlgHom_symm_apply,
    translationInvariantsAlgHom]; rfl

/-- Translation by a `G`-invariant linear form `f` carries the contraction of `ker (lift f)` to
`ρ.symmetricAlgebraInvariants` onto the contraction of the homogeneous irrelevant ideal. -/
theorem map_translationSymmetricAlgebraInvariantsEquiv_under_ker_lift
    (f : M →ₗ[R] R) (hf : ∀ g : G, f ∘ₗ ρ g = f) :
    Ideal.map (ρ.translationSymmetricAlgebraInvariantsEquiv f hf)
      ((RingHom.ker (SymmetricAlgebra.lift f)).under ρ.symmetricAlgebraInvariants) =
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule R M)).toIdeal.under
        ρ.symmetricAlgebraInvariants := by
  let e := ρ.translationSymmetricAlgebraInvariantsEquiv f hf
  have hf0 : (0 : M →ₗ[R] R) + Algebra.linearMap R R ∘ₗ f = f := by ext; simp
  have hfn : f + Algebra.linearMap R R ∘ₗ (-f) = 0 := by ext; simp
  rw [toIdeal_irrelevant_eq_ker_algebraMapInv]; unfold SymmetricAlgebra.algebraMapInv
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun _ hx ↦ ?_) fun y hy ↦ ?_
  · simpa [Ideal.mem_under, SymmetricAlgebra.lift_translation, hf0] using hx
  · exact e.apply_symm_apply y ▸ Ideal.mem_map_of_mem e
      (by simpa [e, Ideal.mem_under, SymmetricAlgebra.lift_translation, hfn] using hy)

end Representation
