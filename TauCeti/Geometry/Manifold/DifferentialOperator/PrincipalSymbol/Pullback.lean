/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Elliptic

import TauCeti.Geometry.Manifold.MFDeriv.Localized
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Naturality of the principal symbol under pullback of sections

Let `V` and `W` be smooth real vector bundles over a finite-dimensional Hausdorff manifold `M`,
with `V` of finite rank, and let `P : Γ(V) → Γ(W)` be a differential operator of order at most
`m`. Let `g : N → M` be a smooth map, and let `P' : Γ(g*V) → Γ(g*W)` be a differential operator of
order at most `m` between the sections of the pullback bundles which is intertwined with `P` by
the pullback of sections:

`P' (s ∘ g) = (P s) ∘ g` for every smooth section `s` of `V`.

Since `(f s) ∘ g = (f ∘ g) (s ∘ g)`, the iterated commutators of `P'` with the pulled back functions
`f ∘ g` are the pullbacks of the iterated commutators of `P` with the functions `f`
(`TauCeti.commutatorSymbol_apply_of_intertwining`). As `d(f ∘ g)_y = df_{g y} ∘ dg_y`, this says
that at an interior point `y` of `N` whose image `g y` is interior, the commutator symbols satisfy

`σ(P')_y(η₁ ∘ dg_y, …, ηₘ ∘ dg_y) = σ(P)_{g y}(η₁, …, ηₘ) : V_{g y} → W_{g y}`

for all covectors `ηᵢ` at `g y`, the fibres of `g*V` and `g*W` at `y` being those of `V` and `W`
at `g y` (`TauCeti.sectionCommutatorSymbol_comp_mfderiv_of_intertwining`), and likewise for the
principal symbols (`TauCeti.sectionPrincipalSymbol_comp_mfderiv_of_intertwining`). No condition
on `g` is needed. When `g` is a local diffeomorphism at `y`, for instance a diffeomorphism, an
open embedding or a covering map, every covector at `y` is of the form `η ∘ dg_y`, so the
principal symbol of `P'` at `y` is determined:

`σ(P')_y(ξ) = σ(P)_{g y}(ξ ∘ (dg_y)⁻¹)`

(`TauCeti.sectionPrincipalSymbol_eq_comp_symm_of_intertwining`). In particular `P'` is elliptic at
`y` exactly when `P` is elliptic at `g y`
(`TauCeti.isSectionEllipticAt_iff_of_intertwining`).

Typical instances of `P'` are the transport `s' ↦ (P (s' ∘ g⁻¹)) ∘ g` of `P` along a
diffeomorphism `g`, the restriction of `P` to an open subset, and the lift of `P` along a covering
map. The intertwining relation is all that the statements use. The scalar analogue for functions,
with conjugation by a diffeomorphism, is `TauCeti.smoothPrincipalSymbol_conjDifferentialOperators`.

## Main results

* `TauCeti.sectionCommutatorSymbol_comp_mfderiv_of_intertwining`,
  `TauCeti.sectionPrincipalSymbol_comp_mfderiv_of_intertwining`: naturality of the commutator and
  principal symbols under pullback along a smooth map.
* `TauCeti.sectionPrincipalSymbol_eq_comp_symm_of_intertwining`: for a local diffeomorphism, the
  principal symbol of the pulled back operator at every covector.
* `TauCeti.isSectionEllipticAt_iff_of_intertwining`: ellipticity is preserved and reflected by
  pullback along a local diffeomorphism.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (linear differential operators between vector bundles and their symbols).
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (the symbol of a differential operator).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W]

/-- The pullback of the smooth bundle `V` along a smooth map is smooth. Sections are pulled back
into the bundle `(g : C(N, M)) *ᵖ V`, whose base map is not syntactically the one of Mathlib's
instance `ContMDiffVectorBundle.pullback`. -/
local instance instContMDiffVectorBundlePullback (g : C^∞⟮J, N; I, M⟯) :
    ContMDiffVectorBundle ∞ F ((g : C(N, M)) *ᵖ V) J :=
  Bundle.Pullback.contMDiffVectorBundle (f := (g : C(N, M))) g.contMDiff

variable (g : C^∞⟮J, N; I, M⟯) {m : ℕ}
  {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
  {P' : differentialOperators ℝ C^∞⟮J, N; ℝ⟯ Cₛ^∞⟮J; F, (g : C(N, M)) *ᵖ V⟯
    Cₛ^∞⟮J; F', (g : C(N, M)) *ᵖ W⟯ m}

/-- **Naturality of the commutator symbol under pullback.** Let `g : N → M` be a smooth map and
let `P'` be an operator between the sections of the pullback bundles with
`P' (s ∘ g) = (P s) ∘ g` for every smooth section `s`. At an interior point `y` with `g y`
interior, the commutator symbol of `P'` on the pullbacks `ηᵢ ∘ dg_y` of covectors at `g y` is the
commutator symbol of `P` on the covectors `ηᵢ`. -/
theorem sectionCommutatorSymbol_comp_mfderiv_of_intertwining {y : N} (hy : J.IsInteriorPoint y)
    (hx : I.IsInteriorPoint (g y))
    (h : ∀ s, (P' : Cₛ^∞⟮J; F, (g : C(N, M)) *ᵖ V⟯ →ₗ[ℝ] _) (s.pullback g) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s).pullback g)
    (η : Fin m → TangentSpace I (g y) →L[ℝ] ℝ) :
    sectionCommutatorSymbol J hy P' (fun i ↦ (η i).comp (mfderiv J I g y)) =
      sectionCommutatorSymbol I hx P η := by
  ext v
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) (g y) (0 : ℝ) (η i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) (g y)) = η := funext hf
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := F) ∞ (g y) v
  have hd (i : Fin m) : (mvfderiv I (f i) (g y)).comp (mfderiv J I g y) =
      mvfderiv J (ContMDiffMap.compRightAlgHom ℝ ℝ g (f i)) y := by
    rw [ContMDiffMap.compRightAlgHom_apply]
    exact (mvfderiv_comp y ((f i).contMDiff.mdifferentiable (by simp) _)
      (g.contMDiff.mdifferentiable (by simp) y)).symm
  have key := commutatorSymbol_apply_of_intertwining
    (ContMDiffSection.pullbackSemilinearMap I F ∞ V g)
    (ContMDiffSection.pullbackSemilinearMap I F' ∞ W g) (D := P) (D' := P')
    (fun s ↦ by
      simpa only [ContinuousMap.coe_ofClass, ContMDiffSection.pullbackSemilinearMap_apply]
        using h s) f s
  simp only [ContinuousMap.coe_ofClass, ContMDiffSection.pullbackSemilinearMap_apply] at key
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at key
  have h1 := sectionCommutatorSymbol_mvfderiv hy P'
    (fun i ↦ ContMDiffMap.compRightAlgHom ℝ ℝ g (f i)) (s.pullback g)
  simp only [ContinuousMap.coe_ofClass] at h1
  rw [key, ContMDiffSection.pullback_apply, ContMDiffSection.pullback_apply] at h1
  simp only [hd]
  rw [ContMDiffSection.evalLinearMap_apply]
  exact h1.trans (sectionCommutatorSymbol_mvfderiv hx P f s).symm

/-- **Naturality of the principal symbol under pullback.** If `P' (s ∘ g) = (P s) ∘ g` for every
smooth section `s`, then `σ(P')_y(η ∘ dg_y) = σ(P)_{g y}(η)` for every covector `η` at `g y`, at
an interior point `y` with `g y` interior. -/
theorem sectionPrincipalSymbol_comp_mfderiv_of_intertwining {y : N} (hy : J.IsInteriorPoint y)
    (hx : I.IsInteriorPoint (g y))
    (h : ∀ s, (P' : Cₛ^∞⟮J; F, (g : C(N, M)) *ᵖ V⟯ →ₗ[ℝ] _) (s.pullback g) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s).pullback g)
    (η : TangentSpace I (g y) →L[ℝ] ℝ) :
    sectionPrincipalSymbol J hy P' (η.comp (mfderiv J I g y)) =
      sectionPrincipalSymbol I hx P η := by
  rw [sectionPrincipalSymbol_def, sectionPrincipalSymbol_def,
    sectionCommutatorSymbol_comp_mfderiv_of_intertwining g hy hx h fun _ ↦ η]
  -- The two sides agree up to the instances on the fibres of the pullback bundles.
  rfl

/-- **The principal symbol of a pullback along a local diffeomorphism.** If `g` is a local
diffeomorphism at `y` and `P' (s ∘ g) = (P s) ∘ g` for every smooth section `s`, then
`σ(P')_y(ξ) = σ(P)_{g y}(ξ ∘ (dg_y)⁻¹)` for every covector `ξ` at `y`. -/
theorem sectionPrincipalSymbol_eq_comp_symm_of_intertwining {y : N}
    (hg : IsLocalDiffeomorphAt J I ∞ g y) (hy : J.IsInteriorPoint y)
    (hx : I.IsInteriorPoint (g y))
    (h : ∀ s, (P' : Cₛ^∞⟮J; F, (g : C(N, M)) *ᵖ V⟯ →ₗ[ℝ] _) (s.pullback g) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s).pullback g)
    (ξ : TangentSpace J y →L[ℝ] ℝ) :
    sectionPrincipalSymbol J hy P' ξ =
      sectionPrincipalSymbol I hx P
        (ξ.comp (hg.mfderivToContinuousLinearEquiv (by simp)).symm.toContinuousLinearMap) := by
  rw [← sectionPrincipalSymbol_comp_mfderiv_of_intertwining g hy hx h]
  congr 1
  ext v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← hg.mfderivToContinuousLinearEquiv_coe (by simp), ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- **Ellipticity under pullback along a local diffeomorphism.** If `g` is a local diffeomorphism
at `y` and `P' (s ∘ g) = (P s) ∘ g` for every smooth section `s`, then `P'` is elliptic at `y`
exactly when `P` is elliptic at `g y`, provided `y` and `g y` are both interior or both boundary
points. -/
theorem isSectionEllipticAt_iff_of_intertwining {y : N} (hg : IsLocalDiffeomorphAt J I ∞ g y)
    (hint : J.IsInteriorPoint y ↔ I.IsInteriorPoint (g y))
    (h : ∀ s, (P' : Cₛ^∞⟮J; F, (g : C(N, M)) *ᵖ V⟯ →ₗ[ℝ] _) (s.pullback g) =
      ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) s).pullback g) :
    IsSectionEllipticAt P' y ↔ IsSectionEllipticAt P (g y) := by
  have he : (hg.mfderivToContinuousLinearEquiv (by simp) :
      TangentSpace J y →L[ℝ] TangentSpace I (g y)) = mfderiv J I g y :=
    hg.mfderivToContinuousLinearEquiv_coe (by simp)
  rw [isSectionEllipticAt_iff, isSectionEllipticAt_iff]
  constructor
  · intro hP hx η hη
    have hy := hint.2 hx
    rw [← sectionPrincipalSymbol_comp_mfderiv_of_intertwining g hy hx h]
    refine hP hy _ fun h0 ↦ hη ?_
    ext v
    have h0v := congr($h0 ((hg.mfderivToContinuousLinearEquiv (by simp)).symm v))
    rwa [ContinuousLinearMap.comp_apply, ← he, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] at h0v
  · intro hP hy ξ hξ
    have hx := hint.1 hy
    rw [sectionPrincipalSymbol_eq_comp_symm_of_intertwining g hg hy hx h]
    refine hP hx _ fun h0 ↦ hξ ?_
    ext v
    simpa using congr($h0 (hg.mfderivToContinuousLinearEquiv (by simp) v))

end TauCeti
