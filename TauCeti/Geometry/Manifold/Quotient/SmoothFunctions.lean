/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import TauCeti.Geometry.Manifold.GroupAction.SmoothFunctions
public import TauCeti.Geometry.Manifold.Quotient.Descent
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Smooth functions on the orbit space of a group action

Let a group `G` act freely and properly discontinuously on a manifold `M` by `C^n` maps. Then the
orbit space `M ⧸ G` is a `C^n` manifold and the orbit projection `π : M → M ⧸ G` is a surjective
`C^n` local diffeomorphism (`TauCeti.isLocalDiffeomorph_quotientMk`). Pullback along `π`
identifies the `C^n` maps `M ⧸ G → F` with the invariant vectors of the representation
`TauCeti.smoothFunctionRep` of `G` on the `C^n` maps `M → F`
(`TauCeti.smoothQuotientEquivInvariants`): a `G`-invariant `C^n` map descends to a map on the
orbit space (`ContMDiffMap.orbitRelQuotientLift`), which is again `C^n` because `π` is a local
diffeomorphism.

This is how spectral problems on a quotient are lifted to its cover. If an operator `T` on the
functions on `M` and an operator `S` on the functions on `M ⧸ G` are intertwined by pullback,
`T (f ∘ π) = S f ∘ π`, then pullback identifies each eigenspace of `S` with the `G`-invariant
vectors of the corresponding eigenspace of `T`
(`TauCeti.eigenspaceEquivInvariantsInfEigenspace`). Sunada's theorem, which combines this with the
representation theory of almost-conjugate subgroups, is in
`TauCeti.Geometry.Manifold.Quotient.Sunada`.

## Main definitions and results

* `TauCeti.smoothQuotientEquivInvariants`: pullback along the orbit projection is a linear
  equivalence from the `C^n` maps on `M ⧸ G` onto the `G`-invariant `C^n` maps on `M`.
* `TauCeti.eigenspaceEquivInvariantsInfEigenspace`: for operators intertwined by pullback, each
  eigenspace on the orbit space is the space of invariant eigenvectors on `M`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 21 (quotients by discrete group actions).
-/

public section

noncomputable section

open Module
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I n G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
  [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]

variable (𝕜 I M F n G) in
/-- **Smooth functions on an orbit space are invariant smooth functions.** For a free, properly
discontinuous action by `C^n` maps, pullback `f ↦ f ∘ π` along the orbit projection
`π : M → M ⧸ G` is a linear equivalence from the `C^n` maps `M ⧸ G → F` onto the `G`-invariant
`C^n` maps `M → F`. -/
def smoothQuotientEquivInvariants :
    C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯ ≃ₗ[𝕜]
      (smoothFunctionRep 𝕜 I M F n G).invariants where
  toFun u := ⟨u.comp (smoothQuotientMk I M n G),
    mem_invariants_smoothFunctionRep_iff.2 fun _ _ ↦ by simp⟩
  invFun f :=
    (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯).orbitRelQuotientLift (mem_invariants_smoothFunctionRep_iff.1 f.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := ((u.comp (smoothQuotientMk I M n G)).eq_orbitRelQuotientLift_iff _).2 rfl |>.symm
  right_inv f := Subtype.ext (ContMDiffMap.orbitRelQuotientLift_comp_smoothQuotientMk _ _)

@[simp]
theorem coe_smoothQuotientEquivInvariants_apply
    (u : C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯) :
    (smoothQuotientEquivInvariants 𝕜 I M F n G u : C^n⟮I, M; 𝓘(𝕜, F), F⟯) =
      u.comp (smoothQuotientMk I M n G) :=
  (rfl)

@[simp]
theorem smoothQuotientEquivInvariants_symm_apply
    (f : (smoothFunctionRep 𝕜 I M F n G).invariants) :
    (smoothQuotientEquivInvariants 𝕜 I M F n G).symm f =
      (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯).orbitRelQuotientLift
        (mem_invariants_smoothFunctionRep_iff.1 f.2) :=
  (rfl)

/-- **Eigenfunctions on an orbit space are invariant eigenfunctions.** If an operator `T` on the
`C^n` maps `M → F` and an operator `S` on the `C^n` maps `M ⧸ G → F` are intertwined by pullback
along the orbit projection, `T (u ∘ π) = S u ∘ π`, then pullback is a linear equivalence from each
eigenspace of `S` onto the `G`-invariant vectors of the eigenspace of `T` for the same
eigenvalue. -/
def eigenspaceEquivInvariantsInfEigenspace {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {S : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯}
    (hTS : ∀ u, T (u.comp (smoothQuotientMk I M n G)) = (S u).comp (smoothQuotientMk I M n G))
    (μ : 𝕜) :
    S.eigenspace μ ≃ₗ[𝕜] ↥((smoothFunctionRep 𝕜 I M F n G).invariants ⊓ T.eigenspace μ) :=
  let π := (smoothFunctionRep 𝕜 I M F n G).invariants.subtype ∘ₗ
    (smoothQuotientEquivInvariants 𝕜 I M F n G).toLinearMap
  have hπ : Function.Injective π :=
    Subtype.val_injective.comp (smoothQuotientEquivInvariants 𝕜 I M F n G).injective
  (S.eigenspace μ).equivMapOfInjective π hπ ≪≫ₗ LinearEquiv.ofEq _ _ (by
    rw [map_genEigenspace_eq_of_intertwine hπ (fun u ↦ by simpa [π] using (hTS u).symm) μ 1]
    simp [π])

@[simp]
theorem coe_eigenspaceEquivInvariantsInfEigenspace_apply {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {S : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯}
    (hTS : ∀ u, T (u.comp (smoothQuotientMk I M n G)) = (S u).comp (smoothQuotientMk I M n G))
    (μ : 𝕜) (u : S.eigenspace μ) :
    (eigenspaceEquivInvariantsInfEigenspace hTS μ u : C^n⟮I, M; 𝓘(𝕜, F), F⟯) =
      (u : C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯).comp (smoothQuotientMk I M n G) :=
  by
  simp only [eigenspaceEquivInvariantsInfEigenspace, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply]
  exact (Submodule.coe_equivMapOfInjective_apply _ _ _ u).trans (by simp)

@[simp]
theorem coe_eigenspaceEquivInvariantsInfEigenspace_symm_apply
    {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {S : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯}
    (hTS : ∀ u, T (u.comp (smoothQuotientMk I M n G)) = (S u).comp (smoothQuotientMk I M n G))
    (μ : 𝕜) (f : ↥((smoothFunctionRep 𝕜 I M F n G).invariants ⊓ T.eigenspace μ)) :
    ((eigenspaceEquivInvariantsInfEigenspace hTS μ).symm f :
        C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯) =
      (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯).orbitRelQuotientLift
        (mem_invariants_smoothFunctionRep_iff.1 f.2.1) :=
  (ContMDiffMap.eq_orbitRelQuotientLift_iff _ _).2 <| by
    rw [← coe_eigenspaceEquivInvariantsInfEigenspace_apply hTS, LinearEquiv.apply_symm_apply]

end TauCeti
