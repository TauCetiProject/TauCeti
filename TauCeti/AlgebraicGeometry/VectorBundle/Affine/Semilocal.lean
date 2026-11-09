/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.AlgebraicGeometry.Morphisms.Finite.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.FixedRank

/-!
# Vector bundles on semilocal affine schemes are free

A finitely generated flat module over a semilocal ring which has the same rank `n` at every
maximal ideal is free of rank `n` (Mathlib's `Module.free_of_flat_of_finrank_eq`, Stacks 02M9).
Through the equivalence `FiniteLocallyFreeSheaf.finiteProjectiveEquiv` between finitely generated
projective modules and finite locally free sheaves on an affine scheme, a finite locally free sheaf
of constant rank `n` on an affine scheme whose ring of global functions has finitely many maximal
ideals is the free sheaf on `n` generators.

This applies to every scheme finite over a field `k`: its ring of global functions is a
finite-dimensional `k`-algebra, hence Artinian, hence semilocal. So on such a scheme, for instance
on the closed subscheme cut out by an effective Cartier divisor on a curve, every vector bundle of
constant rank is trivial. For schemes finite over a field this is the higher-rank analogue of the
triviality of line bundles on discrete schemes
(`TauCeti.AlgebraicGeometry.LineBundleClass.subsingleton_of_discreteTopology`).

## Main declarations

* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.nonempty_iso_free_of_finite_maximalSpectrum`:
  over a semilocal ring `R`, a finite locally free sheaf of constant rank `n` on `Spec R` is free on
  `n` generators;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isAffine`: the
  same on an affine scheme with semilocal ring of global functions;
* `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isFinite`: on a
  scheme finite over a field, every vector bundle of constant rank `r` is `𝒪^r`.

## References

* [The Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
-/

public section

open CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

namespace FiniteLocallyFreeSheaf

/-- **Vector bundles over a semilocal ring are free.** If `R` has finitely many maximal ideals,
a finite locally free sheaf `E` on `Spec R` of rank `n` at every point is isomorphic to the free
sheaf on `n` generators. -/
theorem nonempty_iso_free_of_finite_maximalSpectrum {R : CommRingCat.{u}}
    [Finite (MaximalSpectrum R)] (E : FiniteLocallyFreeSheaf (Spec R)) {n : ℕ}
    (hn : ∀ x, E.rank x = n) : Nonempty (E ≅ free (Spec R) (ULift.{u} (Fin n))) := by
  obtain ⟨_, _⟩ := finite_projective_moduleSpecΓ E
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq R (moduleSpecΓFunctor.obj E.obj) n
    fun P ↦ by
      let _ := Ideal.Quotient.field P.1
      -- The rank of `R ⧸ P ⊗ Γ E` over the field `R ⧸ P` is its rank at the zero ideal, which
      -- is the rank of `Γ E` at the preimage `P` of the zero ideal.
      have h := Module.rankAtStalk_baseChange (R := R) (S := R ⧸ P.1)
        (M := moduleSpecΓFunctor.obj E.obj) ⟨⊥, Ideal.isPrime_bot⟩
      have hP : PrimeSpectrum.comap (algebraMap R (R ⧸ P.1)) ⟨⊥, Ideal.isPrime_bot⟩ =
          ⟨P.1, P.2.isPrime⟩ :=
        PrimeSpectrum.ext (by
          simp [Ideal.Quotient.algebraMap_eq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker])
      rw [Module.rankAtStalk_eq_finrank_of_free, hP] at h
      exact h.trans ((rank_apply_eq_rankAtStalk E ⟨P.1, P.2.isPrime⟩).symm.trans (hn _))
  exact ⟨isoFreeOfBasis E (b.reindex Equiv.ulift.symm)⟩

namespace FixedRank

variable {X : Scheme.{u}} {r : ℕ}

/-- **Vector bundles on a semilocal affine scheme are free.** On an affine scheme `X` whose ring
of global functions has finitely many maximal ideals, every finite locally free sheaf of constant
rank `r` is isomorphic to the free sheaf `𝒪_X^r`. -/
theorem nonempty_iso_free_of_isAffine [IsAffine X] [Finite (MaximalSpectrum Γ(X, ⊤))]
    (E : FixedRank X r) : Nonempty (E ≅ free X r) := by
  let φ := X.isoSpec
  obtain ⟨e⟩ := nonempty_iso_free_of_finite_maximalSpectrum
    ((FiniteLocallyFreeSheaf.pullback φ.inv).obj E.obj)
    fun x ↦ by rw [← pullback_obj_obj]; exact rank_apply _ x
  -- Pulling the trivialisation on `Spec Γ(X, ⊤)` back along `X ≅ Spec Γ(X, ⊤)` trivialises `E`.
  exact ⟨ObjectProperty.isoMk _ (((FiniteLocallyFreeSheaf.pullbackId X).app E.obj).symm ≪≫
    eqToIso (congrArg (fun f ↦ (FiniteLocallyFreeSheaf.pullback f).obj E.obj)
      φ.hom_inv_id.symm) ≪≫
    ((FiniteLocallyFreeSheaf.pullbackComp φ.hom φ.inv).app E.obj).symm ≪≫
    (FiniteLocallyFreeSheaf.pullback φ.hom).mapIso e ≪≫
    FiniteLocallyFreeSheaf.pullbackFreeIso φ.hom _ ≪≫ eqToIso (free_obj X r).symm)⟩

/-- **Vector bundles on a scheme finite over a field are free.** If `X` is finite over a field
`k`, every finite locally free sheaf of constant rank `r` on `X` is isomorphic to `𝒪_X^r`: the
ring of global functions of `X` is a finite-dimensional `k`-algebra, hence semilocal. -/
theorem nonempty_iso_free_of_isFinite (k : Type u) [Field k] [X.Over (Spec (.of k))]
    [IsFinite (X ↘ Spec (.of k))] (E : FixedRank X r) : Nonempty (E ≅ free X r) := by
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of k))
  let _ : Algebra k Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
  have : Module.Finite k Γ(X, ⊤) := (X ↘ Spec (.of k)).moduleFinite_appTop rfl
  have : IsArtinianRing Γ(X, ⊤) := .of_finite k Γ(X, ⊤)
  exact nonempty_iso_free_of_isAffine E

end FixedRank

end FiniteLocallyFreeSheaf

end

end AlgebraicGeometry

end TauCeti
