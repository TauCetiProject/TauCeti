/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.BaseChange
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.BaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import TauCeti.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.QuasiSeparated
import TauCeti.AlgebraicGeometry.Modules.Sheaf
import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Flat base change for the pushforward of quasi-coherent sheaves

Consider a commutative square of schemes `g' ≫ f = f' ≫ g`, with `g' : X' ⟶ X`, `f : X ⟶ S`,
`f' : X' ⟶ S'` and `g : S' ⟶ S`, and the base change morphism `g^* f_* M ⟶ f'_* g'^* M` of sheaves
of modules (`Scheme.Modules.pushforwardBaseChange`).

When the square is cartesian, `f` is quasi-compact and quasi-separated, `g` is flat and `M` is
quasi-coherent, the base change morphism is an isomorphism
(`Scheme.Modules.isIso_pushforwardBaseChange_app`). This is flat base change for the direct image
in degree zero. It suffices to check bijectivity on sections over the affine opens `W'` of `S'`
lying over affine opens `W` of `S`, since these form a basis
(`Scheme.Hom.isBasis_range_affineOpens_le_preimage`). There both sides are base changes of
`Γ(f⁻¹ W, M)` from `Γ(S, W)` to `Γ(S', W')`: the source because `f_* M` is quasi-coherent and
`W`, `W'` are affine (`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear` for the
identity square on `g`), and the target by flat base change of sections over the quasi-compact
quasi-separated open `f⁻¹ W`
(`Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated`). The base change
morphism is compatible with both identifications, so it is bijective
(`IsBaseChange.bijective_of_comp_eq`).

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bijective_pushforwardBaseChange_app_app`: flat base change on
  the sections over an affine open lying over an affine open;
* `AlgebraicGeometry.Scheme.Modules.isIso_pushforwardBaseChange_app`: **flat base change**, the
  base change morphism `g^* f_* M ⟶ f'_* g'^* M` is an isomorphism for quasi-compact
  quasi-separated `f`, flat `g` and quasi-coherent `M`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition III.9.3.
* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH).
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- **Flat base change on sections over affine opens.** For a cartesian square
`g' ≫ f = f' ≫ g` with `f` quasi-compact and quasi-separated and `g` flat, a quasi-coherent sheaf
`M` on `X`, and affine opens `W` of `S` and `W' ⊆ g⁻¹ W` of `S'`, the base change morphism is
bijective on the sections over `W'`. -/
theorem bijective_pushforwardBaseChange_app_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] {W : S.Opens}
    (hW : IsAffineOpen W) {W' : S'.Opens} (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W) :
    Function.Bijective (((pushforwardBaseChange H.toCommSq).app M).app W') := by
  -- Both sides are base changes of `Γ(f⁻¹ W, M) = Γ(W, f_* M)` from `Γ(S, W)` to `Γ(S', W')`,
  -- and the base change morphism is compatible with the two base-change maps. First the
  -- source, through the identity square on `g`, whose rings act through identities.
  let N := (pushforward f).obj M
  let : Algebra Γ(S, W) Γ(S', W') := (g.appLE W W' h).hom.toAlgebra
  let : Module Γ(S, W) Γ((pullback g).obj N, W') := Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g).obj N, W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let alg₁ : Algebra Γ(S, W) Γ(S, W) := (Scheme.Hom.appLE (𝟙 S) W W le_rfl).hom.toAlgebra
  have hid (Y : Scheme.{u}) (V : Y.Opens) : Scheme.Hom.appLE (𝟙 Y) V V le_rfl = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 Y)).trans (Scheme.Hom.id_app V)
  have t₁ : @IsScalarTower Γ(S, W) Γ(S, W) Γ(N, W) alg₁.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₁ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  let alg₂ : Algebra Γ(S', W') Γ(S', W') := (Scheme.Hom.appLE (𝟙 S') W' W' le_rfl).hom.toAlgebra
  have t₂ : @IsScalarTower Γ(S', W') Γ(S', W') Γ((pullback g).obj N, W') alg₂.toSMul _ _ :=
    @IsScalarTower.of_algebraMap_smul _ _ _ _ _ alg₂ _ _ fun r n ↦ by
      rw [RingHom.algebraMap_toAlgebra, hid]
      rfl
  have hα := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear g N
    (IsPullback.id_vert g) hW hW' h (UX := W) le_rfl hW (UY := W') (by simpa using h)
  -- Then the target, the sections of `f'_* g'^* M` over `W'`, by flat base change over
  -- `W' ⟶ W`.
  have hUY : f' ⁻¹ᵁ W' = g' ⁻¹ᵁ (f ⁻¹ᵁ W) ⊓ f' ⁻¹ᵁ W' := by
    refine (inf_eq_right.mpr ?_).symm
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
    exact f'.preimage_mono h
  let : Module Γ(S, W) Γ(M, f ⁻¹ᵁ W) := (inferInstance : Module Γ(S, W) Γ(N, W))
  let : Algebra Γ(S, W) Γ(X, f ⁻¹ᵁ W) := (f.appLE W (f ⁻¹ᵁ W) le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S, W) Γ(X, f ⁻¹ᵁ W) Γ(M, f ⁻¹ᵁ W) := .of_algebraMap_smul fun r m ↦ by
    rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
    rfl
  let : Module Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    (inferInstance : Module Γ(S', W') Γ((pushforward f').obj ((pullback g').obj M), W'))
  let : Algebra Γ(S', W') Γ(X', f' ⁻¹ᵁ W') := (f'.appLE W' (f' ⁻¹ᵁ W') le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(S', W') Γ(X', f' ⁻¹ᵁ W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun r m ↦ by
      rw [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE_eq_app]
      rfl
  let : Module Γ(S, W) Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    Module.compHom _ (algebraMap Γ(S, W) Γ(S', W'))
  have : IsScalarTower Γ(S, W) Γ(S', W') Γ((pullback g').obj M, f' ⁻¹ᵁ W') :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have hβ := Scheme.Hom.isBaseChange_pullbackSectionsLEBaseLinear_of_isQuasiSeparated g' M H
    hW hW' h (UX := f ⁻¹ᵁ W) le_rfl (f.isCompact_preimage hW.isCompact)
    (f.isQuasiSeparated_preimage hW.isQuasiSeparated) hUY
  -- The base change map on sections over `W'` is linear over `Γ(S', W')` and compatible with
  -- the two pullbacks of sections.
  let φ : Γ((pullback g).obj N, W') →ₗ[Γ(S', W')]
      Γ((pushforward f').obj ((pullback g').obj M), W') :=
    { toFun := ((pushforwardBaseChange H.toCommSq).app M).app W'
      map_add' := map_add _
      map_smul' := Hom.app_smul _ }
  exact IsBaseChange.bijective_of_comp_eq hα hβ φ fun s ↦
    (congrArg φ (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g N _ h _ _ _ s)).trans
      ((pushforwardBaseChange_app_app_pullbackSectionsLE H.toCommSq M W W' h s).trans
        (Scheme.Hom.pullbackSectionsLEBaseLinear_apply g' M _ h _ _ _ s).symm)


/-- **Flat base change for the direct image of a quasi-coherent sheaf.** For a cartesian square
of schemes `g' ≫ f = f' ≫ g`, with `f : X ⟶ S` quasi-compact and quasi-separated and `g : S' ⟶ S`
flat, and a quasi-coherent sheaf `M` on `X`, the base change morphism
`g^* f_* M ⟶ f'_* g'^* M` is an isomorphism. -/
theorem isIso_pushforwardBaseChange_app (H : IsPullback g' f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Flat g] (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((pushforwardBaseChange H.toCommSq).app M) :=
  Hom.isIso_of_isBasis _ g.isBasis_range_affineOpens_le_preimage fun i ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (bijective_pushforwardBaseChange_app_app H M i.1.2.2 i.1.1.2 i.2)

end AlgebraicGeometry.Scheme.Modules
