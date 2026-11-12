/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Semilocal
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula
import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
import TauCeti.AlgebraicGeometry.Modules.SchemeTheoreticSupport

/-!
# Twisting a sheaf supported on a semilocal scheme by a vector bundle

Let `f : Z ⟶ X` be a morphism from an affine scheme `Z` whose ring of global functions has
finitely many maximal ideals, for instance a scheme finite over a field, and let `E` be a finite
locally free sheaf of constant rank `r` on `X`. For every sheaf of modules `G` on `Z`,

`E ⊗ f_* G ≅ f_* (f^* E ⊗ G) ≅ f_* (G^r) ≅ (f_* G)^r`,

by the projection formula and because the vector bundle `f^* E` on the semilocal scheme `Z` is
trivial. Consequently the truncated Euler characteristic over a field `k` is multiplied by the
rank: `χ(X, E ⊗ f_* G) = r · χ(X, f_* G)`.

Applied to the inclusion of a closed subscheme finite over `k`, this computes the Euler
characteristic of a sheaf with finite support twisted by a vector bundle. Indeed, if `X` is
locally of finite type over `k`, a quasi-coherent sheaf `M` of finite type with finite support is
the pushforward of a module on its scheme-theoretic support `V(Ann M)`, which is finite over `k`
(`AlgebraicGeometry.Scheme.Modules.isFinite_subschemeι_annihilator_comp`), so
`χ(X, E ⊗ M) = r · χ(X, M)`. On a curve this is the input showing that a modification of a vector
bundle `E` with finitely supported cokernel changes the degree of `V ⊗ E` by `rank V` times the
change in the degree of `E`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.eulerCharBelow_tensor_pushforward`:
  `χ(X, E ⊗ f_* G) = r · χ(X, f_* G)` for every truncation degree, with no finiteness hypothesis.
* `AlgebraicGeometry.Scheme.Modules.eulerCharBelow_tensor_of_finite_support`:
  `χ(X, E ⊗ M) = r · χ(X, M)` for a coherent sheaf `M` with finite support on a scheme locally of
  finite type over `k`.

## References

* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYQ),
  where `χ(X, E ⊗ F) = r · χ(X, F)` is shown for a coherent sheaf `F` with finite support.
-/

public section

open CategoryTheory Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Z : Scheme.{u}} (f : Z ⟶ X) [IsAffine Z] [Finite (MaximalSpectrum Γ(Z, ⊤))]

/-- **Twisting by a vector bundle multiplies the Euler characteristic by the rank.** Let `Z` be
an affine scheme with finitely many closed points, `f : Z ⟶ X` a morphism and `E` a vector bundle
of constant rank `r` on `X`. For every sheaf of modules `G` on `Z`, the truncated Euler
characteristic over `k` satisfies `χ(X, E ⊗ f_* G) = r · χ(X, f_* G)`: the pullback of `E` to the
semilocal scheme `Z` is trivial, so `E ⊗ f_* G ≅ (f_* G)^r` by the projection formula. -/
theorem eulerCharBelow_tensor_pushforward (k : Type u) [Field k] [X.Over (Spec (.of k))] {r : ℕ}
    (E : FiniteLocallyFreeSheaf.FixedRank X r) (G : Z.Modules) (n : ℕ) :
    eulerCharBelow k X (E.obj.obj ⊗ (pushforward f).obj G) n =
      r * eulerCharBelow k X ((pushforward f).obj G) n := by
  -- Instance search finds neither finite biproducts in the abelian categories `Z.Modules` and
  -- `X.Modules` nor the additivity of `⊗` on `Z.Modules`, which is stated for sheaves of modules.
  have : HasFiniteBiproducts Z.Modules := Abelian.hasFiniteBiproducts
  have : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  have : MonoidalPreadditive Z.Modules := TauCeti.SheafOfModules.monoidalPreadditive Z.sheaf
  -- `f^* E ≅ 𝒪_Z^r`, written as a biproduct of copies of `𝒪_Z` indexed by `Fin r`.
  obtain ⟨e⟩ := FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isAffine
    ((FiniteLocallyFreeSheaf.FixedRank.pullback f).obj E)
  let e₁ : ((FiniteLocallyFreeSheaf.pullback f).obj E.obj).obj ≅
      ⨁ fun _ : ULift.{u} (Fin r) ↦ 𝟙_ Z.Modules :=
    eqToIso (congrArg (·.obj) (FiniteLocallyFreeSheaf.FixedRank.pullback_obj_obj f E).symm) ≪≫
      (isFiniteLocallyFree Z).ι.mapIso
        ((FiniteLocallyFreeSheaf.isConstantRank Z r).ι.mapIso e) ≪≫
      eqToIso (by
        rw [ObjectProperty.ι_obj, ObjectProperty.ι_obj, FiniteLocallyFreeSheaf.FixedRank.free_obj,
          FiniteLocallyFreeSheaf.free_obj]) ≪≫
      (TauCeti.SheafOfModules.biproductIsoFree (R := Z.sheaf) _).symm
  let e₂ : ((FiniteLocallyFreeSheaf.pullback f).obj E.obj).obj ≅
      ⨁ fun _ : Fin r ↦ 𝟙_ Z.Modules :=
    e₁ ≪≫ biproduct.whiskerEquiv (f := fun _ : ULift.{u} (Fin r) ↦ 𝟙_ Z.Modules)
      (g := fun _ : Fin r ↦ 𝟙_ Z.Modules) Equiv.ulift fun _ ↦ Iso.refl _
  -- The projection formula, then distributivity of `⊗` and of `f_*` over the biproduct.
  let e₃ : E.obj.obj ⊗ (pushforward f).obj G ≅ ⨁ fun _ : Fin r ↦ (pushforward f).obj G :=
    (FiniteLocallyFreeSheaf.pushforwardTensorLeftIso f E.obj).app G ≪≫
      (pushforward f).mapIso
        (whiskerRightIso e₂ G ≪≫ rightDistributor _ G ≪≫ biproduct.mapIso fun _ ↦ λ_ G) ≪≫
      (pushforward f).mapBiproduct _
  rw [eulerCharBelow_congr k e₃, eulerCharBelow_biproduct_const, Fintype.card_fin]

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Twisting a finitely supported sheaf by a vector bundle multiplies the Euler characteristic
by the rank.** Let `X` be a scheme locally of finite type over a field `k`, `E` a vector bundle of
constant rank `r` on `X` and `M` a quasi-coherent sheaf of finite type whose support
`{x | M_x ≠ 0}` is finite. Then `χ(X, E ⊗ M) = r · χ(X, M)` for every truncation degree. -/
theorem eulerCharBelow_tensor_of_finite_support (k : Type u) [Field k] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank X r)
    (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (hM : {x : X | Nontrivial (M.presheaf.stalk x)}.Finite) (n : ℕ) :
    eulerCharBelow k X (E.obj.obj ⊗ M) n = r * eulerCharBelow k X M n := by
  have hM' (U : X.affineOpens) : Module.Finite Γ(X, U) Γ(M, U) :=
    finite_sections_of_isAffineOpen M U U.2
  -- `M` is the pushforward of a module on its scheme-theoretic support `Z = V(Ann M)`, which is
  -- finite over `k`, hence affine with Artinian ring of global functions.
  obtain ⟨G, ⟨e⟩⟩ := exists_iso_pushforward_subschemeι_annihilator M hM'
  have : IsLocallyArtinian (Spec (.of k)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have := isFinite_subschemeι_annihilator_comp M hM' (X ↘ Spec (.of k)) hM
  have : IsLocallyArtinian (M.annihilator hM').subscheme :=
    .of_locallyQuasiFinite ((M.annihilator hM').subschemeι ≫ X ↘ Spec (.of k))
  have : IsAffine (M.annihilator hM').subscheme :=
    isAffine_of_isAffineHom ((M.annihilator hM').subschemeι ≫ X ↘ Spec (.of k))
  rw [eulerCharBelow_congr k (whiskerLeftIso E.obj.obj e), eulerCharBelow_congr k e,
    Scheme.Hom.eulerCharBelow_tensor_pushforward]

end AlgebraicGeometry.Scheme.Modules
