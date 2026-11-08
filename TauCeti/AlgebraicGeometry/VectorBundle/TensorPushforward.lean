/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Biproduct
public import TauCeti.AlgebraicGeometry.VectorBundle.Affine.Semilocal
public import TauCeti.AlgebraicGeometry.VectorBundle.ProjectionFormula

/-!
# Tensoring a vector bundle with a direct image from a semilocal affine scheme

Let `f : Z ⟶ X` be a morphism from an affine scheme whose ring of global functions has finitely
many maximal ideals, for instance a closed subscheme finite over a field, or the spectrum of a
residue field. Every vector bundle of constant rank `r` on `Z` is trivial
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank.nonempty_iso_free_of_isAffine`), so
by the projection formula `E ⊗ f_* M ≅ f_* (f^* E ⊗ M)` a vector bundle `E` of constant rank `r`
on `X` satisfies

`E ⊗ f_* M ≅ (f_* M)^{⊕ r}`

for every sheaf of modules `M` on `Z`. Consequently `χ(X, E ⊗ f_* M) = r · χ(X, f_* M)` for the
truncated Euler characteristic, with no finiteness hypothesis, and in a short exact sequence
`0 ⟶ V₁ ⟶ V₂ ⟶ f_* M ⟶ 0` of sheaves of modules on `X`,

`χ(X, E ⊗ V₂) = χ(X, E ⊗ V₁) + r · χ(X, f_* M)`.

For instance, a quasi-coherent sheaf of finite type annihilated by the ideal sheaf of a closed
subscheme `Z` is a direct image from `Z`
(`AlgebraicGeometry.Scheme.Modules.exists_iso_pushforward_iff_ker_le_annihilator`), and `Z` is
affine and semilocal when it is finite over a field. Combined with the additivity of `χ` in the
original sequence, the last formula says that `χ(X, E ⊗ V) - r · χ(X, V)` does not change when `V`
is modified along such a `Z`. This is the dévissage step in computing the Euler characteristic of
a tensor product `E ⊗ V`, or of a pullback, of vector bundles on a curve.

## Main declarations

In the namespace `TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank`:

* `nonempty_tensor_pushforward_iso_biproduct`: `E ⊗ f_* M ≅ (f_* M)^{⊕ r}`;
* `eulerCharBelow_tensor_pushforward`: `χ(X, E ⊗ f_* M) = r · χ(X, f_* M)`;
* `eulerCharBelow_tensor_eq_add_of_shortExact`: for a short exact sequence
  `0 ⟶ V₁ ⟶ V₂ ⟶ f_* M ⟶ 0`, `χ(X, E ⊗ V₂) = χ(X, E ⊗ V₁) + r · χ(X, f_* M)`.

## References

* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYQ).
* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.1(d) (the projection formula).
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Scheme.Modules

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FiniteLocallyFreeSheaf.FixedRank

variable {X Z : Scheme.{u}} {r : ℕ} (f : Z ⟶ X) [IsAffine Z] [Finite (MaximalSpectrum Γ(Z, ⊤))]
  (E : FixedRank X r) (M : Z.Modules)

/-- **Tensoring a direct image from a semilocal affine scheme.** If `f : Z ⟶ X` is a morphism from
an affine scheme whose ring of global functions has finitely many maximal ideals, then for every
vector bundle `E` of constant rank `r` on `X` and every sheaf of modules `M` on `Z`,
`E ⊗ f_* M ≅ (f_* M)^{⊕ r}`. -/
theorem nonempty_tensor_pushforward_iso_biproduct :
    Nonempty (E.obj.obj ⊗ (Scheme.Modules.pushforward f).obj M ≅
      ⨁ fun _ : Fin r ↦ (Scheme.Modules.pushforward f).obj M) := by
  obtain ⟨e⟩ := nonempty_iso_free_of_isAffine ((pullback f).obj E)
  let : MonoidalPreadditive Z.Modules := SheafOfModules.monoidalPreadditive Z.sheaf
  -- The pullback `f^* E` is the free sheaf `𝒪_Z^r`, a biproduct of `r` copies of the unit.
  let e' : ((FiniteLocallyFreeSheaf.pullback f).obj E.obj).obj ≅ ⨁ fun _ : Fin r ↦ 𝟙_ Z.Modules :=
    eqToIso (by rw [ObjectProperty.ι_obj, ObjectProperty.ι_obj, pullback_obj_obj]) ≪≫
      (Scheme.Modules.isFiniteLocallyFree Z).ι.mapIso ((isConstantRank Z r).ι.mapIso e) ≪≫
      eqToIso (by rw [ObjectProperty.ι_obj, ObjectProperty.ι_obj, free_obj,
        FiniteLocallyFreeSheaf.free_obj]) ≪≫
      (SheafOfModules.biproductIsoFree (R := Z.sheaf) _).symm ≪≫
      biproduct.whiskerEquiv (f := fun _ : ULift.{u} (Fin r) ↦ 𝟙_ Z.Modules)
        (g := fun _ : Fin r ↦ 𝟙_ Z.Modules) Equiv.ulift fun _ ↦ Iso.refl _
  -- `E ⊗ f_* M ≅ f_* (f^* E ⊗ M) ≅ f_* (M^{⊕ r}) ≅ (f_* M)^{⊕ r}`.
  exact ⟨(FiniteLocallyFreeSheaf.pushforwardTensorLeftIso f E.obj).app M ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (whiskerRightIso e' M ≪≫ rightDistributor _ M ≪≫ biproduct.mapIso fun _ ↦ λ_ M) ≪≫
    (Scheme.Modules.pushforward f).mapBiproduct _⟩

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The Euler characteristic of a twisted direct image from a semilocal affine scheme.** For
`f : Z ⟶ X` with `Z` affine and semilocal, a vector bundle `E` of constant rank `r` on `X` and a
sheaf of modules `M` on `Z`, `χ(X, E ⊗ f_* M) = r · χ(X, f_* M)`. No finiteness hypothesis is
needed, the truncated Euler characteristic taking junk values on both sides alike. -/
theorem eulerCharBelow_tensor_pushforward (n : ℕ) :
    eulerCharBelow k X (E.obj.obj ⊗ (Scheme.Modules.pushforward f).obj M) n =
      r * eulerCharBelow k X ((Scheme.Modules.pushforward f).obj M) n := by
  obtain ⟨e⟩ := nonempty_tensor_pushforward_iso_biproduct f E M
  rw [eulerCharBelow_congr k e n, eulerCharBelow_biproduct_const, Fintype.card_fin]

variable {f M} {S : ShortComplex X.Modules}

/-- **Modifying a sheaf along a semilocal affine scheme.** Let `0 ⟶ V₁ ⟶ V₂ ⟶ f_* M ⟶ 0` be a
short exact sequence of sheaves of modules on `X`, whose cokernel is a direct image from an affine
semilocal scheme, and let `E` be a vector bundle of constant rank `r`. If `E ⊗ V₁` and `E ⊗ V₂`
have finite-dimensional cohomology in the degrees `< n` that the truncation reads, and `E ⊗ V₁`
has none in degree `n`, then `χ(X, E ⊗ V₂) = χ(X, E ⊗ V₁) + r · χ(X, f_* M)`. -/
theorem eulerCharBelow_tensor_eq_add_of_shortExact (hS : S.ShortExact)
    (e : S.X₃ ≅ (Scheme.Modules.pushforward f).obj M) (n : ℕ)
    (h₁ : ∀ i < n, 0 < i →
      FiniteDimensional k (Scheme.Modules.Cohomology (E.obj.obj ⊗ S.X₁) i))
    (h₂ : ∀ i < n, FiniteDimensional k (Scheme.Modules.Cohomology (E.obj.obj ⊗ S.X₂) i))
    (hvan : Subsingleton (Scheme.Modules.Cohomology (E.obj.obj ⊗ S.X₁) n)) :
    eulerCharBelow k X (E.obj.obj ⊗ S.X₂) n =
      eulerCharBelow k X (E.obj.obj ⊗ S.X₁) n + r * eulerCharBelow k X S.X₃ n := by
  -- Tensoring with `E` keeps the sequence exact, and its third term is `E ⊗ f_* M`.
  have h := eulerCharBelow_eq_add k (shortExact_map_tensorLeft E.obj.obj hS) n h₁ h₂ hvan
  simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃,
    curriedTensor_obj_obj] at h
  rw [h, eulerCharBelow_congr k (whiskerLeftIso E.obj.obj e),
    eulerCharBelow_tensor_pushforward f E M k, eulerCharBelow_congr k e]

end FiniteLocallyFreeSheaf.FixedRank

end

end AlgebraicGeometry

end TauCeti
