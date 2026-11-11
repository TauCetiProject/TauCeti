/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import TauCeti.Geometry.Manifold.Algebra.SMul
public import TauCeti.Geometry.Manifold.Quotient.Descent
public import TauCeti.RepresentationTheory.FunLeft
public import TauCeti.RepresentationTheory.Induction.AlmostConjugate
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Smooth functions on the orbit space of a group action

Let a group `G` act on a manifold `M` by `C^n` maps. Then `G` acts linearly on the `C^n` maps
`f : M → F` into a normed space by translating the argument, `(g • f) x = f (g⁻¹ • x)`; this is
the representation `TauCeti.smoothFunctionRep`, the restriction to `C^n` maps of the translation
representation `Representation.funLeft` on all functions. Its invariant vectors are the `C^n` maps
constant on orbits.

If the action is moreover free and properly discontinuous, the orbit space `M ⧸ G` is a `C^n`
manifold and the orbit projection `π : M → M ⧸ G` is a surjective `C^n` local diffeomorphism
(`TauCeti.isLocalDiffeomorph_quotientMk`). Pullback along `π` then identifies the `C^n` maps on
`M ⧸ G` with the `G`-invariant `C^n` maps on `M` (`TauCeti.smoothQuotientEquivInvariants`): a
`G`-invariant `C^n` map descends to a map on the orbit space (`ContMDiffMap.descend`), which is
again `C^n` because `π` is a local diffeomorphism.

This is how spectral problems on a quotient are lifted to its cover. If an operator `T` on the
functions on `M` and an operator `S` on the functions on `M ⧸ G` are intertwined by pullback,
`T (f ∘ π) = S f ∘ π`, then pullback identifies each eigenspace of `S` with the `G`-invariant
vectors of the corresponding eigenspace of `T`
(`TauCeti.eigenspaceEquivInvariantsInfEigenspace`). For a finite group `Q` acting freely and two
almost-conjugate subgroups `K₁`, `K₂` (subgroups meeting every conjugacy class of `Q` in the same
number of elements), Sunada's argument then shows that operators on `M ⧸ K₁` and on `M ⧸ K₂`
intertwined by pullback with one operator `T` commuting with `Q` have eigenspaces of the same
dimension (`Subgroup.AlmostConjugate.finrank_eigenspace_eq_of_intertwine`). The representation
theory, through Frobenius reciprocity, is
`Subgroup.AlmostConjugate.finrank_invariants_inf_eigenspace_eq`. In Sunada's construction of
isospectral manifolds, `T` and `S₁`, `S₂` are the Laplacians of a `Q`-invariant Riemannian metric on
`M` and of the quotient metrics; neither those operators nor their intertwining is constructed
here.

## Main definitions and results

* `TauCeti.smoothFunctionRep`: the representation `(g • f) x = f (g⁻¹ • x)` of `G` on the `C^n`
  maps `M → F`.
* `TauCeti.mem_invariants_smoothFunctionRep_iff`: its invariant vectors are the maps with
  `f (g • x) = f x`.
* `TauCeti.smoothQuotientEquivInvariants`: pullback along the orbit projection is a linear
  equivalence from the `C^n` maps on `M ⧸ G` onto the `G`-invariant `C^n` maps on `M`.
* `TauCeti.eigenspaceEquivInvariantsInfEigenspace`: for operators intertwined by pullback, each
  eigenspace on the orbit space is the space of invariant eigenvectors on `M`.
* `Subgroup.AlmostConjugate.finrank_eigenspace_eq_of_intertwine`: **Sunada's theorem** for
  operators on smooth functions intertwined by pullback.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Theorem 17, p. 159.
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

/-! ### The representation on smooth functions -/

variable (𝕜 I M F n G) in
/-- The representation of `G` on the `C^n` maps `f : M → F` by translation of the argument,
`(g • f) x = f (g⁻¹ • x)`. -/
def smoothFunctionRep : Representation 𝕜 G C^n⟮I, M; 𝓘(𝕜, F), F⟯ where
  toFun g :=
    { toFun f := ⟨fun x ↦ f (g⁻¹ • x), f.contMDiff.comp (contMDiff_const_smul g⁻¹)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦ congrArg f (by rw [inv_one, one_smul])
  map_mul' g h := LinearMap.ext fun f ↦ ContMDiffMap.ext fun x ↦
    congrArg f (by rw [mul_inv_rev, mul_smul])

@[simp]
theorem smoothFunctionRep_apply_apply (g : G) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) (x : M) :
    smoothFunctionRep 𝕜 I M F n G g f x = f (g⁻¹ • x) :=
  (rfl)

/-- On underlying functions, `TauCeti.smoothFunctionRep` is the translation representation
`Representation.funLeft` of `G` on all functions `M → F`, for the trivial action on `F`. -/
theorem coe_smoothFunctionRep_apply (g : G) (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯) :
    ⇑(smoothFunctionRep 𝕜 I M F n G g f) = (Representation.trivial 𝕜 G F).funLeft M g f := by
  ext x
  simp

/-- The invariant vectors of `TauCeti.smoothFunctionRep` are the `C^n` maps that are constant on
the orbits of `G`. It has `high` priority so that `simp` prefers it to the generic
`Representation.mem_invariants`. -/
@[simp high]
theorem mem_invariants_smoothFunctionRep_iff {f : C^n⟮I, M; 𝓘(𝕜, F), F⟯} :
    f ∈ (smoothFunctionRep 𝕜 I M F n G).invariants ↔ ∀ (g : G) (x : M), f (g • x) = f x := by
  rw [Representation.mem_invariants]
  refine ⟨fun h g x ↦ ?_, fun h g ↦ ContMDiffMap.ext fun x ↦ ?_⟩
  · simpa using DFunLike.congr_fun (h g⁻¹) x
  · simpa using h g⁻¹ x

/-- Restricting `TauCeti.smoothFunctionRep` to a subgroup `K` has the same invariant vectors as
the representation of `K` acting on `M` by restriction. -/
theorem invariants_smoothFunctionRep_comp_subtype (K : Subgroup G) :
    Representation.invariants ((smoothFunctionRep 𝕜 I M F n G).comp K.subtype) =
      (smoothFunctionRep 𝕜 I M F n K).invariants := by
  ext f
  rw [mem_invariants_smoothFunctionRep_iff, Representation.mem_invariants]
  refine ⟨fun h k x ↦ ?_, fun h k ↦ ContMDiffMap.ext fun x ↦ ?_⟩
  · simpa [Subgroup.smul_def] using DFunLike.congr_fun (h k⁻¹) x
  · simpa [Subgroup.smul_def] using h k⁻¹ x

/-! ### Functions on the orbit space -/

variable [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M] [IsCancelSMul G M]
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
    mem_invariants_smoothFunctionRep_iff.2 fun g _ ↦ congrArg u (Quotient.sound ⟨g, rfl⟩)⟩
  invFun f := (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯).descend (mem_invariants_smoothFunctionRep_iff.1 f.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv u := ((u.comp (smoothQuotientMk I M n G)).eq_descend_iff _).2 rfl |>.symm
  right_inv _ := rfl

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
      (f : C^n⟮I, M; 𝓘(𝕜, F), F⟯).descend (mem_invariants_smoothFunctionRep_iff.1 f.2) :=
  (rfl)

/-- Pullback along the orbit projection, as a linear map into the `C^n` maps on `M`, has range the
`G`-invariant maps. -/
private theorem range_subtype_comp_smoothQuotientEquivInvariants :
    LinearMap.range ((smoothFunctionRep 𝕜 I M F n G).invariants.subtype ∘ₗ
        (smoothQuotientEquivInvariants 𝕜 I M F n G).toLinearMap) =
      (smoothFunctionRep 𝕜 I M F n G).invariants := by
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

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
    rw [map_eigenspace_eq_of_intertwine hπ (fun u ↦ (hTS u).symm) μ,
      range_subtype_comp_smoothQuotientEquivInvariants])

@[simp]
theorem coe_eigenspaceEquivInvariantsInfEigenspace_apply {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯}
    {S : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯}
    (hTS : ∀ u, T (u.comp (smoothQuotientMk I M n G)) = (S u).comp (smoothQuotientMk I M n G))
    (μ : 𝕜) (u : S.eigenspace μ) :
    (eigenspaceEquivInvariantsInfEigenspace hTS μ u : C^n⟮I, M; 𝓘(𝕜, F), F⟯) =
      (u : C^n⟮I, MulAction.orbitRel.Quotient G M; 𝓘(𝕜, F), F⟯).comp (smoothQuotientMk I M n G) :=
  (rfl)

end TauCeti

/-! ### Sunada's theorem -/

namespace Subgroup.AlmostConjugate

open TauCeti

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {Q : Type u} [Group Q] [Finite Q] [MulAction Q M] [ContMDiffConstSMul I n Q M]
  [ContinuousConstSMul Q M] [IsCancelSMul Q M] [T2Space M] [LocallyCompactSpace M]
  [IsManifold I n M] {K₁ K₂ : Subgroup Q}

/-- **Sunada's theorem for smooth functions.** Let a finite group `Q` act freely on `M` by `C^n`
maps, and let `K₁`, `K₂` be almost-conjugate subgroups of `Q`. Let `T` be an operator on the
`C^n` maps `M → F` commuting with the action of `Q`, and `S₁`, `S₂` operators on the `C^n` maps
on `M ⧸ K₁` and `M ⧸ K₂` intertwined with `T` by pullback along the orbit projections. Then for
every `μ`, the `μ`-eigenspaces of `S₁` and `S₂` have the same dimension. -/
theorem finrank_eigenspace_eq_of_intertwine (h : K₁.AlmostConjugate K₂)
    {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hT : ∀ q, Commute T (smoothFunctionRep 𝕜 I M F n Q q))
    {S₁ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₁ M; 𝓘(𝕜, F), F⟯}
    {S₂ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₂ M; 𝓘(𝕜, F), F⟯}
    (hS₁ : ∀ u, T (u.comp (smoothQuotientMk I M n K₁)) = (S₁ u).comp (smoothQuotientMk I M n K₁))
    (hS₂ : ∀ u, T (u.comp (smoothQuotientMk I M n K₂)) = (S₂ u).comp (smoothQuotientMk I M n K₂))
    (μ : 𝕜) : finrank 𝕜 (S₁.eigenspace μ) = finrank 𝕜 (S₂.eigenspace μ) := by
  rw [(eigenspaceEquivInvariantsInfEigenspace hS₁ μ).finrank_eq,
    (eigenspaceEquivInvariantsInfEigenspace hS₂ μ).finrank_eq,
    ← invariants_smoothFunctionRep_comp_subtype, ← invariants_smoothFunctionRep_comp_subtype]
  exact h.finrank_invariants_inf_eigenspace_eq _ hT μ

end Subgroup.AlmostConjugate
