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
# The principal symbol under bundle maps

Let `P : Γ(V) → Γ(W)` be a differential operator of order at most `m` between the smooth sections
of vector bundles over a finite-dimensional Hausdorff manifold `M`, in Grothendieck's sense
(`TauCeti.differentialOperators`), and let `L : Γ(V') → Γ(V)` and `R : Γ(W) → Γ(W')` be linear over
the smooth functions, that is, bundle maps `L_x : V'_x → V_x` and `R_x : W_x → W'_x`
(`TauCeti.smoothSectionFiberMap`). Since `L` and `R` commute with multiplication by smooth
functions, the iterated commutators of `R ∘ P ∘ L` with multiplication operators are those of `P`
sandwiched between `R` and `L` (`TauCeti.commutatorSymbol_apply_of_eq_comp_comp`), so

`σ(R ∘ P ∘ L)_x(ξ) = R_x ∘ σ(P)_x(ξ) ∘ L_x`

for the commutator symbols and the principal symbols
(`TauCeti.sectionPrincipalSymbol_of_eq_comp_comp`). Here `L` and `R` are global bundle maps, so
for global bundle isomorphisms this is the transformation of the principal symbol under a global
change of trivialization. Changes of local frames follow by first restricting to an open set
(`TauCeti.sectionPrincipalSymbol_restrictSectionDifferentialOperators`). The same holds when `L`
and `R` are given as smooth families of fibre maps
(`TauCeti.sectionPrincipalSymbol_of_eq_mapLinearMap_comp_comp`).

Consequently the notions defined through the principal symbol are preserved by global bundle maps
of the following kinds:

* ellipticity at `x` is preserved when `L_x` and `R_x` are bijective, and ellipticity is preserved
  by function-linear isomorphisms of the section modules;
* the Laplace-type condition `σ(P)(ξ) = -(c ‖ξ‖²) Id` is preserved by `P ↦ R ∘ P ∘ L` whenever
  `R ∘ L = Id`, for instance by conjugation `P ↦ Φ⁻¹ ∘ P ∘ Φ` with a bundle isomorphism `Φ`, and by
  compression to a direct summand;
* the Dirac-type condition `σ(D)(ξ)* σ(D)(ξ) = ‖ξ‖² Id` is preserved by sandwiching between
  global bundle maps that are fibrewise isometries.

## Main results

* `TauCeti.sectionCommutatorSymbol_of_eq_comp_comp`,
  `TauCeti.sectionPrincipalSymbol_of_eq_comp_comp`: the symbols of `R ∘ P ∘ L` are those of `P`
  sandwiched between the fibre maps of `R` and `L`.
* `TauCeti.sectionPrincipalSymbol_of_eq_mapLinearMap_comp_comp`: the same for smooth families of
  fibre maps acting on sections.
* `TauCeti.isSectionEllipticAt_iff_of_eq_comp_comp`,
  `TauCeti.isSectionElliptic_iff_of_eq_comp_comp`: ellipticity does not change under bundle
  isomorphisms.
* `TauCeti.IsSectionLaplaceType.of_eq_comp_comp`: operators of Laplace type stay of Laplace type,
  with the same constant.
* `TauCeti.IsDiracType.of_eq_comp_comp`: operators of Dirac type stay of Dirac type under fibrewise
  isometries.

## References

* A. Grothendieck, *Éléments de géométrie algébrique IV*, Quatrième partie, §16.8.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (linear differential operators between vector bundles).
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

section Symbol

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V' : M → Type*} [TopologicalSpace (TotalSpace G V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module ℝ (V' x)] [∀ x, TopologicalSpace (V' x)]
  [FiberBundle G V'] [VectorBundle ℝ G V'] [ContMDiffVectorBundle ∞ G V' I]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
  {W' : M → Type*} [TopologicalSpace (TotalSpace G' W')]
  [∀ x, AddCommGroup (W' x)] [∀ x, Module ℝ (W' x)] [∀ x, TopologicalSpace (W' x)]
  [FiberBundle G' W'] [VectorBundle ℝ G' W']
  {m : ℕ} {x : M}
  {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
  {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; G, V'⟯ Cₛ^∞⟮I; G', W'⟯ m}
  {L : Cₛ^∞⟮I; G, V'⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯}
  {R : Cₛ^∞⟮I; F', W⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; G', W'⟯}

/-- **The commutator symbol under bundle maps.** If `Q = R ∘ P ∘ L` for maps `L` and `R` of
sections that are linear over the smooth functions, then at an interior point `x` the commutator
symbol of `Q` is that of `P` composed with the fibre maps `L_x` and `R_x`. -/
theorem sectionCommutatorSymbol_of_eq_comp_comp (hx : I.IsInteriorPoint x)
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      R ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (L s)))
    (ξ : Fin m → TangentSpace I x →L[ℝ] ℝ) :
    sectionCommutatorSymbol I hx Q ξ =
      smoothSectionFiberMap x R ∘ₗ sectionCommutatorSymbol I hx P ξ ∘ₗ
        smoothSectionFiberMap x L := by
  ext v
  choose f _ hf using fun i ↦ exists_contMDiffMap_mvfderiv_eq (I := I) x (0 : ℝ) (ξ i)
  obtain rfl : (fun i ↦ mvfderiv I (f i) x) = ξ := funext hf
  obtain ⟨s, rfl⟩ := ContMDiffSection.evalLinearMap_surjective (I := I) (F := G) ∞ x v
  simp only [ContMDiffSection.evalLinearMap_apply, LinearMap.comp_apply,
    smoothSectionFiberMap_apply, sectionCommutatorSymbol_mvfderiv hx,
    commutatorSymbol_apply_of_eq_comp_comp L R h]

/-- **The principal symbol under bundle maps.** If `Q = R ∘ P ∘ L` for maps `L` and `R` of sections
that are linear over the smooth functions, then at an interior point `x` the principal symbol of `Q`
is `σ(Q)(ξ) = R_x ∘ σ(P)(ξ) ∘ L_x`, where `L_x` and `R_x` are the fibre maps of `L` and `R`. For
global bundle isomorphisms this is the change of the principal symbol under a global change of
trivialization. -/
theorem sectionPrincipalSymbol_of_eq_comp_comp (hx : I.IsInteriorPoint x)
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      R ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (L s)))
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx Q ξ =
      smoothSectionFiberMap x R ∘ₗ sectionPrincipalSymbol I hx P ξ ∘ₗ
        smoothSectionFiberMap x L := by
  rw [sectionPrincipalSymbol_def, sectionPrincipalSymbol_def,
    sectionCommutatorSymbol_of_eq_comp_comp hx h, LinearMap.smul_comp, LinearMap.comp_smul]

/-- **The principal symbol under smooth bundle maps.** If `Q = ψ ∘ P ∘ ϕ` for smooth families of
linear fibre maps `ϕ x : V'_x → V_x` and `ψ x : W_x → W'_x` acting on sections, then at an interior
point `x` the principal symbol of `Q` is `σ(Q)(ξ) = ψ x ∘ σ(P)(ξ) ∘ ϕ x`. -/
theorem sectionPrincipalSymbol_of_eq_mapLinearMap_comp_comp (hx : I.IsInteriorPoint x)
    (ϕ : ∀ x, V' x →ₗ[ℝ] V x)
    (hϕ : ContMDiff (I.prod 𝓘(ℝ, G)) (I.prod 𝓘(ℝ, F)) ∞
      (fun p : TotalSpace G V' ↦ (⟨p.proj, ϕ p.proj p.snd⟩ : TotalSpace F V)))
    (ψ : ∀ x, W x →ₗ[ℝ] W' x)
    (hψ : ContMDiff (I.prod 𝓘(ℝ, F')) (I.prod 𝓘(ℝ, G')) ∞
      (fun p : TotalSpace F' W ↦ (⟨p.proj, ψ p.proj p.snd⟩ : TotalSpace G' W')))
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      ContMDiffSection.mapLinearMap ψ hψ
        ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (ContMDiffSection.mapLinearMap ϕ hϕ s)))
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    sectionPrincipalSymbol I hx Q ξ = ψ x ∘ₗ sectionPrincipalSymbol I hx P ξ ∘ₗ ϕ x := by
  rw [← ContMDiffSection.restrictScalars_mapFunctionLinearMap ϕ hϕ,
    ← ContMDiffSection.restrictScalars_mapFunctionLinearMap ψ hψ] at h
  rw [sectionPrincipalSymbol_of_eq_comp_comp hx h, smoothSectionFiberMap_mapFunctionLinearMap,
    smoothSectionFiberMap_mapFunctionLinearMap]

/-- **Ellipticity under bundle maps.** If `Q = R ∘ P ∘ L` for maps `L` and `R` of sections that are
linear over the smooth functions and whose fibre maps at `x` are bijective, then `Q` is elliptic at
`x` exactly when `P` is. -/
theorem isSectionEllipticAt_iff_of_eq_comp_comp
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      R ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (L s)))
    (hL : Function.Bijective (smoothSectionFiberMap x L))
    (hR : Function.Bijective (smoothSectionFiberMap x R)) :
    IsSectionEllipticAt Q x ↔ IsSectionEllipticAt P x := by
  rw [isSectionEllipticAt_iff, isSectionEllipticAt_iff]
  refine forall_congr' fun hx ↦ forall₂_congr fun ξ _ ↦ ?_
  rw [sectionPrincipalSymbol_of_eq_comp_comp hx h, LinearMap.coe_comp, LinearMap.coe_comp,
    Function.Bijective.of_comp_iff' hR, Function.Bijective.of_comp_iff _ hL]

/-- **Ellipticity under bundle isomorphisms.** If `Q = R ∘ P ∘ L` for isomorphisms `L` and `R` of
the modules of sections over the smooth functions, that is, bundle isomorphisms `V' ≅ V` and
`W ≅ W'`, then `Q` is elliptic exactly when `P` is. -/
theorem isSectionElliptic_iff_of_eq_comp_comp [FiniteDimensional ℝ G']
    [ContMDiffVectorBundle ∞ G' W' I]
    (eL : Cₛ^∞⟮I; G, V'⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯)
    (eR : Cₛ^∞⟮I; F', W⟯ ≃ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; G', W'⟯)
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      eR ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (eL s))) :
    IsSectionElliptic Q ↔ IsSectionElliptic P := by
  rw [isSectionElliptic_iff, isSectionElliptic_iff]
  exact forall_congr' fun x ↦ isSectionEllipticAt_iff_of_eq_comp_comp
    (L := eL.toLinearMap) (R := eR.toLinearMap) h (smoothSectionFiberMap_bijective x eL)
    (smoothSectionFiberMap_bijective x eR)

/-- **Operators of Laplace type under bundle maps.** Let `P` be of Laplace type with constant `c`
on the sections of `V`. If `Q = R ∘ P ∘ L` for maps `L : Γ(V') → Γ(V)` and `R : Γ(V) → Γ(V')`
linear over the smooth functions with `R ∘ L = Id`, then `Q` is of Laplace type with constant `c`:
its principal symbol is `R_x ∘ (-(c ‖ξ‖²) Id) ∘ L_x = -(c ‖ξ‖²) Id`. This applies to the conjugate
`Φ⁻¹ ∘ P ∘ Φ` by a bundle isomorphism `Φ`, and to the compression of `P` to a direct summand of
`V`. -/
theorem IsSectionLaplaceType.of_eq_comp_comp [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F, V⟯ 2}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; G, V'⟯ Cₛ^∞⟮I; G, V'⟯ 2} {c : ℝ}
    (hP : IsSectionLaplaceType P c) {L : Cₛ^∞⟮I; G, V'⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯}
    {R : Cₛ^∞⟮I; F, V⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; G, V'⟯} (hRL : R ∘ₗ L = LinearMap.id)
    (h : ∀ s, (Q : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G, V'⟯) s =
      R ((P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯) (L s))) :
    IsSectionLaplaceType Q c := by
  refine isSectionLaplaceType_iff.2 ⟨hP.pos, fun x hx ξ ↦ ?_⟩
  simp [sectionPrincipalSymbol_of_eq_comp_comp hx h, hP.sectionPrincipalSymbol_eq hx ξ,
    LinearMap.smul_comp, LinearMap.comp_smul, ← smoothSectionFiberMap_comp, hRL]

end Symbol

section Dirac

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V' : M → Type*} [TopologicalSpace (TotalSpace G V')]
  [∀ x, NormedAddCommGroup (V' x)] [∀ x, InnerProductSpace ℝ (V' x)]
  [FiberBundle G V'] [VectorBundle ℝ G V'] [ContMDiffVectorBundle ∞ G V' I]
  {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
  {W' : M → Type*} [TopologicalSpace (TotalSpace G' W')]
  [∀ x, NormedAddCommGroup (W' x)] [∀ x, InnerProductSpace ℝ (W' x)]
  [FiberBundle G' W'] [VectorBundle ℝ G' W']

/-- **Operators of Dirac type under fibrewise isometries.** Let `D` be of Dirac type. If
`D' = R ∘ D ∘ L` for maps `L` and `R` of sections that are linear over the smooth functions and
whose fibre maps preserve the fibre metrics, then `D'` is of Dirac type:
`⟪R σ(D)(ξ) L v, R σ(D)(ξ) L w⟫ = ⟪σ(D)(ξ) L v, σ(D)(ξ) L w⟫ = ‖ξ‖² ⟪L v, L w⟫ = ‖ξ‖² ⟪v, w⟫`.
This applies to global bundle isometries, such as a change between global orthonormal
trivializations. -/
theorem IsDiracType.of_eq_comp_comp
    {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ 1}
    {D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; G, V'⟯ Cₛ^∞⟮I; G', W'⟯ 1}
    (hD : IsDiracType D) {L : Cₛ^∞⟮I; G, V'⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; F, V⟯}
    {R : Cₛ^∞⟮I; F', W⟯ →ₗ[C^∞⟮I, M; ℝ⟯] Cₛ^∞⟮I; G', W'⟯}
    (hL : ∀ (x : M) (v w : V' x),
      ⟪smoothSectionFiberMap x L v, smoothSectionFiberMap x L w⟫ = ⟪v, w⟫)
    (hR : ∀ (x : M) (v w : W x),
      ⟪smoothSectionFiberMap x R v, smoothSectionFiberMap x R w⟫ = ⟪v, w⟫)
    (h : ∀ s, (D' : Cₛ^∞⟮I; G, V'⟯ →ₗ[ℝ] Cₛ^∞⟮I; G', W'⟯) s =
      R ((D : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯) (L s))) :
    IsDiracType D' := by
  refine isDiracType_iff.2 fun x hx ξ v w ↦ ?_
  simp only [sectionPrincipalSymbol_of_eq_comp_comp hx h, LinearMap.comp_apply, hR,
    hD.inner_sectionPrincipalSymbol, hL]

end Dirac

end TauCeti
